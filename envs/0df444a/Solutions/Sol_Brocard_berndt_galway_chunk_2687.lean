-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2687
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:26:19.623298+00:00
-- url     : https://prove2.me/submissions/96d146b5-45bf-4efc-bf29-d86b43b3e4cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 483093525 ≤ n < 483273381 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 483094775 1250 483093525 483093557
    0x3021b19090c0905010219060b030307060515010f0c0f1205070b04080903060916030b060f12071401030b011b0c0b030109050916080c01110304090f1d0c0112020a 71
    0x405503041003035a00c0d80d0710a0310b01d50076080f440c0ba6000d08002d000170554040031f4407124501510760712009081c117495031410701c8261420002d5408450744500188110715204112211564181d0100c0340065896040b043d030706130050340c010a03956046210010240340640b100c0090080e5100c201040110402c05540898000c50700305000d244a43d05066035450031208241c1382c00405000000036412841c801c0b100003402082410480364031401d00340c07596407007000007048105890319858002d04907204c0c00448160114101c001e650000d8880c5100e07211110045080307600024a003404510302d0b4405900d10980d01c01c240150074451417000c0d031040c0d02ca40f03118010703410a0b80820b90880c2c035141402084607040c08a0071219184140b000300b8149414032080d0f80340629540035040c040e4542c4d001c008160305000701c0e00a403000d5002404103484040460004210561060300a00c08000d0301e0a9602004200d2081e8400140c2daa900c0c01c0320b0402d41c0308000d503c503071820000e020b4a1350b900c601074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 483096025 1250 483094775 483094819
    0x26190b060d0f0911060c030307120f06030302010c0f03050c040e130f030f08090a0b010b0327031b010b0a06050c1006030809030d031103070f2303010510030903021b 72
    0x210032410b0340800c000e000d500c0d125401e5682c000c100780c82250240700a80365504000141c0ea80301c0c05515100020b02a00c0b07400d03a0007881c5038213a900c826810a2404814150150801511240a41e542c42c030103a20380442241190010b88504140000c1040104103050f500102c0c00d4008010310340c0c414005185070b0726104c0c0459010300c00c6001c01e404014409885403c6410701d0f074425299005032030842c5481c0d13a415140c840502074113405050200103e8008001c402e0080710304e14650000841c4220b400f03124070340d0303604082c20300c01e0740381d5040c026074640c21018001d038006460090802512541040c034181d0701900b00d4800102035124401140a5080e000d004a000850260300066034980c080001d041c10f040510850205050601005211084401044035031000041ca41600390420300241101c40003c92026241d6140032842541361010307281d001181201d40407220559507001c102c409a064403425640078001d80c020100500c0084402d07080d031002048014a60360140b150501c07440c1d88 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 483097275 1250 483096025 483096041
    0xf0906160507080303151507050f010f2012070c1205070605060904030e09190615260c090607061e05010f030f02040c05040b0a26190b060d 61
    0x21200380d00c95a01070041c00d0104401410802029514525001070b0f1480f02200860030240501070b00b1540c0e103003240310441600c014590100a460601c55000005800b034005c11ba802805540f90104644000c00010070703c0c02e011056204c89403e0814411003140304175001000c0300c0901004107045000140d0f48a900183c00c4d4468991513140c0c9010308052049420083c00d40340030380b60300f50610010a070082c5001c80c5424007155403103003503602c10450221389040c00c1a90003402d0300340300740071400d614102c10210990341d180c0e4800b18000c140d40703c80200750303c0340056035090b6a890070201c2c450451201c0180140000981114500304031941c606003141c001c2a81e10301408100e0b5800e01e500d0211380165401456006145500142143c443e103c01065050009220359603c01049603070030701644c10389000748004480e464540c3d075010b4000d002e4a030400a501900c0030b1608115562004080301140554801441c50841c42c510781e503a0b10003880da40c0c0b0440d621400c14070510704070078024010000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 483098525 1250 483097275 483097297
    0x5060a050a240e060405010b091e030f01050405250e0720010902011205061c020420070506010b0a0503180115090608010b03030306030c1e031912030608120f0906 71
    0x2e11074540f01d140114450082c281d2841213040600420034015560309031803101d001212110700504030281440402c000e03d0290507003600603641618024081940f100303108500542c2a2449003191401c2850030407405007075011400c241304c105000c0d006d8210780059000c491418404114103a8034441e8207140b010840d0000180c1d110b000405c00c559108107861184c0d040300310140300d1820000005840c60f1182e0f00a1119048480c1e914025507495030005075060768400003903059011010310141803540701c1c240903200340c8500000000c6000e1403034110b5100c403040c3d540f842d04503203030007400304c16010702c200342c103081f80d03494030480d0500c1c03109a40700700010400204000341310340c0740c4880f250a450f88445035911a0304180104020707520049500fa510100c1151403071030f04104998841c0407041d040544d25014403500489052501902c000941034074000c6400d41e4040700b5061040701500c21a01421707109800c0400440c0003003010034040d09107445030703405490802460201152168203ca00148 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 483099775 1250 483098525 483098591
    0x15090b0d0605100e130207020d0803040602040e13020f011202120108061b1e03040f0f0602030403123809090109420204050303070f110a0305060a050a 66
    0x25603e8803010000000f0094100815101100c00018000d02610340b240000e4580004001c411035641c8455642d015034000401d070349074141400c0010083d08540210442140024080341000754092903180c020759005002e412054070440c011518249044400c403501c45d0248035503a6035002c2c910005010b40070f180002c00091411109080c546074900302000c040140c10030210122000c404d1103240f8034407a401070707103a480e00c551401c3e450010100d88064102ca0f190302d0140c04124850700114000c50103030356080003000030704603110308540140c00c40b074070214000700c074404001d401d050102140201c088080c089010040c0041740011310b04668103616655660b041c40304020004134141040c088110340d50070318843d0001e501410b000c0c000185a07440034449141c5402c445690111800b40038040c081da40c440641c2c0c03419480101440c001104c8418040c201d600c40c9040c0071918000b180c0c3c1050043c941601d0340e40c40302c801071001800d20702c1d825444691034140d9040c0074001d92141d800c01001c10b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 483101025 1250 483099775 483099779
    0x14010507110c0604060e06070c080f010b19061707180b0903151003110301180311011b020d08370b030703021302131a07020a080c06030115090b0d06 65
    0x100e080c000c01c203204a00c10351040c80180841d903400b03483c80341c201c041a07c030181e0f110018200411040190740c054040c8e0305c0b030801c0f10a890748064110314541c840a071908281c20f0b00c0e05450fa07440c10940d0080c06c00007060740038000301014084c12003903040051070400021307590b80005000076164850300001c03000c4000040c03661183c1810030001c000c1c2d0409401c1ca1059060000031401c07669907600c009011301c043c0c003180078219942940440d100000001420b00c03541c0d19440d001c0c0c81480740344030800042d482c000c2540c0c4040025148410303102c0107607001c1e01e010704a00a0985501030040c100d10b015106040a01695016940002c1da001c58082c03001c00680c044602900700790745101d0036050080c2c128110400042c1c43d24000e0040e40d11a2001c09138075030706050300c5180c070840c0e41e84c4501d65510034405496902c40384640202a12402555605501500c0e164101c2c6e9030302c9000c0c0c6681c2c02281c1000100315000c014050003600c8103192400c5850f10740d0321810860550011a0035010303c958410007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 483102275 1250 483101025 483101057
    0x30a0509030c09150d0302010608060f2202010e120c06030a0e07080109080301030212010e0d3b040b030a080a020c011d0109030303020d0b0a0906090501120f020d14010507 75
    0x1c1c00400b240c101c0d801c040c1454041d0446180080e03208080d405000c103072440c101018001e4120300c02400c081011145c0c1840c010000c868034030816640b03601c07003012005000d030300362032085100400700303406843e1510440c0e95201031100c19030441481c000755002c0d21080e1121582c45000071401008611008211154008030042c00c06442e80d0000000c0d0385444000000076000f4402e481c1100c0e01220402c407452403050b941d03409040340150000381802403c018503c02501702501e0340c42c109440740c0d55244640354070461000700021480000c0c0030340341d1040030002450a07401c051398001024003034a0850105035507080c1c0d541c0040f002703880507030880b030000c49040d40d011060140c41c7c1d100701c401c0102c8054a03000a001007125002c050201500050800300491361a0000038841d5000b0701043c0100381c4e914000390042c072090103001032442c04c1100002d84c04100e02c4c01c4a40e181c0d0402c24160346140180d081141c0aa1004400c131200550340145011442c001e10443e44541d440b511102016411403003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 483103525 1250 483102275 483102283
    0x30f06060e010f150e040e1e0d0f0203160201020a0507060c02040c0801150c0204240810060b04060c020d150e060a0507051e0909071215050609041a03030a050903 71
    0x200c480f41107052010048000e014032075440c00d1045007021002c85401c00082009081100d541c0c0d540c510506c501b140207800030107180120b0186540c1070340c0a507105d4880c1211040946048040181d00610034220900140705c0c014810310700c1401115420002c03070792600d0400c4070310f03030080300800d010101c0320055003403034020710040806034071b0800a25814104001c2680031810284020814029910001c40d11070b6401220a00d1150040c03200341007151040110841c2c040c0241149405000c0e00e4100b000c0342405844150350f4411440d500700350500303000310790020b003189040c1e0344500d59404003400301e50041507068186114ad0f802081003a00100c0f01c41c90984040c010120300d518040802c80c5040c0c0c08015500b0031080c040d13481b41c09903e0400080681d008034060703e64031400c10000c0c0441c00390405491054050740703001c148803800c2e0151031150034107540d1040f0b035000b400800102c105450640c0c4140184c40c41d000b4a03203024021000030a1039500304107002e030042540041e00805510b0300b00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 483104775 1250 483103525 483103529
    0x301020405031f23070f030207230a0b0c360d060213091b18120614150306151003052502030d0b060304050d030209130f06061b0525030f06060e01 64
    0x820203600e42221035480d41d01484071036013440200081500030762001d070ad080c00220f03083ca40040c030312001e50410b000c2c81d0b28290310040c100790f001c100c41c1081a00c0c21814032900b810a81240d400c105a00c5c420301d0a01c060040c40d01011180303140d0800051501440801c02c14025202201d8000f8844442001040c4078035030a00450081c050440c06240c24036000d41c440c24103a400c42020062580081d184c04070190401c02c00038403961910b070040109140030315912003019201141241c4658444149880100c890342101681094410031380c9506035002c0d0f003055070007145107203e10520b524203440c0c07580c1d040c070481515030040c1c02c009400506c100080c0241c07441d001d02141c2c0c0b140740d414160350b0655a0910048034cc01415004a02c42600303a8a03211020001c5c1c1c0910420700a80701c0845103100140440e0003039101151410b0880010040551002d001103640320001300712042c05000340004418044910a071071201c01c040c003200062491400010643c480e080204a8a05040500070304850503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 483106025 1250 483104775 483104777
    0x204060e0f18031204080322050c0f01090506070510050901021c0b040207080c1c080403081b091201051501050c0d0302130902040303120b0301020405031f23070f 71
    0x3030040c08001e0564031904800900742915003180ea8640060075402125070080100e10308a08210030b2015810095100c0c0b83c002d0480f0b10351a10f4a81701034130101e4140b01c050842c0d4400d100c41c035400e007000c50801c003c1c0281410100f0000d5a07030000240a64003040080703032603801480800c42c507403006005003600300d04078500941c1489201640710440c00015982c42544540b2150040b400361142c3d4105c54030130b9048195141c0c0c0d0418030120740c1d0340d0070302d082900b10b061004460001c40c0501c00c10a160180c0d9040e940c1c80000d46480a982c00900380c0144c0e49619601c080000420f69940d200d6207032011550440040343c81e18100da080c600c8034041d10201810302c1810019814140780c003180503c42c0c90041e003030050b103c004554411104442d5070300300b03000440c4000fa010082c15006002c051603c1403041d414080b408003401450309071b0040b4458150594045000308420508800c4125625000020002411003070b001c2410010718015286e1040304221406200c119a80002185952402 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 483107275 1250 483106025 483106049
    0x50a0201020105181908040e04030c0b0702010c050f0901030e01050a0c0915050403150f18020325050409020f1f08010602070e0628060203030a060504150905191107020406 75
    0x444e814080d00e031007042010b078500340609900703101003000381c3c0c00b41c40113040788191405d054900f40c1750140030070442003030130788070048a01c0001d6481c1c3d205025281103042c40f13039a002d0514101250040ca1900b010f0510b9040c107840c4d103034104080000348107541c441d1345d0001000c81c1001c00c13140c001d04641e075150480000c0341e04000c10203220079085012a401c496015500034101e1104285200003088095910540542000e00c40c01044070011074212450f07000702c0c2903074100900300600c0b0300d06203151146140d5802218108000619280e8130160141d07001429000c400400040012801403a9010743c0c401c041d00d01c511201340310744c0300c094103014090500050880c50300304000d4070110140201601c0c8a02e5540fa024880442c85800c9404407600d960108010300da15200081d403a034204444240b641c5140100c0001e00d4507080c007559454514030042641070380e0500b62080090b000c000c1003050001a80140c01a04006034410705000000c044081500c0c1d0714984104000d84007035500a044482d9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 483108525 1250 483107275 483107311
    0x180c1209110f060c0a0807020109123c06021806070c03050d0219110a0909031d0604033f030204050103050606120f061906021015080304062109050a0201020105 70
    0x100140e81c64580d40c110079215214030b404c0c23004030f4200c00140c1100070089004400d1500300424000d069100c2c2c05100c2040c010b0141c0303400c141103501c10801c40d034214210007642039008568240e00404100c850f81c091026854040300101d00f081d07014400c11103880480c5c480820074440c007400f03000c10314540340c400342070307c01401d0300c50090280c4a1100505403912060b181c203800c0d9200e40220300100840f2100340302c1c00d02d4a040181015556400d046080c03402d0280080191030b0010494065990012081d40000c0d450700f09004003d10300b503a2400d415885800301c640d810000211002686556a40941da0358108000101550f01c050f20440c05402c061041e40001e0b010700ca0f9041d88000c034114008501e69404001a02144510485516070250741e41c0200c1c91607070104d4032015041c4046414007907007510700f0640d000c0248d00e100e840c1c010340007030101b480401e1242d1b213445800590f151004800790261004501194103a01084074203500030310103001156028016940d102c1c85e84442410560 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 483109775 1250 483108525 483108547
    0x50601051201030b062202220f0b0d09050312070e0a050906090402030a1b0311100203030705130f0e0a0b030105060319150e0a03140301180c1209110f06 67
    0x3041804004c0c59442c400000608648441c81070240203081205c5020300031910598503402584490600b500580100701c0b01000240c08030f14020440d0306010000803614600000b1652541010180c0005580c5074040175010034400c2002c0c145168295903c91018100380b2406048401c04001e2f0501448a4103000c12690307071460305d40c0383d001c1001c4d030380111550381d035100080c01e002c1c101e980240044440701e000c01c2c103146842002800e591152403100001503003682080ba103003800c03150303c1d40117034000c2000a44961041020701040d0940c4807902d034559444000d101e145040c2904078101e081c0d40d080c20049110483c1c090180340d100150b008018604280c00803e403640c2d081c600100c26030b002c42404004100e9800c40310a600a00300e841041810342406681e40c6908280c2c10680c0080c020341542090310580c4001c490488110700c660f07106020100840c1c1e0003a0105010440c00d00084d12100703551340f1154010002401e1150081d07418101c0e1200c01c00014400695200e4020101031085050134 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 483111025 1250 483109775 483109807
    0x1140112150b030a02040516020c01140a2703030f0e0f1f0507050a0623160c03030e0d03060503010c14030103060203040602071403030f070f02030909070909020c0c030105060105 78
    0x3501d00d0081403116007070010a18011090700c00941003407a081c10481c00301d42e88201d41030b5442480d801c1d160252913220044a1003051040f8501540e2410001e8903803483c01082c51800881c424201c030002c00044028503c01002d0540c07044d80481c20640100c512290b002c05030312810303141256140503540d84140441c00800700c0040d6a601c00441040c1c81c4401c90242095070000c5622204036402c40740c6926051005d0310341c00f002c1001c00d10100d154a42e5059825100700d00c54038900d401070280044013981100c010042c04420380505680b21f4000c0c0030041c09200001000645e41c42c04a40c1c1480c01c0141030031524604860010855035171244942413041c041280d0460b40c11030005a140c2e02d45082160091107616402071414000e40e180219285d40800658819034210200c10425966000c05860701d81041d103801005800800c0020018503100917044d81186062508041140c0c6036481c0760101ea101040481035a0302180c49e0342001d01d024050203034050381c01e180003400c02511241080c1c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 483112275 1250 483111025 483111053
    0x171003051506120a1104060e090607081e04030206040302071e09090206090303070c030b0f07090504050a4a0c12030702030601030c0905090c0609010f03090f0501140112 74
    0x4410901c0011841d540d80e10304020307035030400040030b49800913607a1074442803919184d0344a5005605103170f0000b41c2080c02d11040b030301c030700982d401821859554120458640328020f002d41c06562540c3c0340042c000044001c00c9201d144a5002460300c0c0c105800c001c2c0c90301c1c10950018507414002215104c1091184c0000e8088a96100300801c84d0b04444c400901d041c01070303800d801d030103110114030302c4140305410350404203c0380246204000e94070f42c03001c0f0040c40107040b41c4042c00f1030072050302085103040c1130340403030340c080c0600038001000700b0b094150700c80780e5003610741541c03144083d241110384894000b140780d107405c0d40c070360b0303514400c5580c001503262100c2518816070320581c020306050300070396400e0040fa2546903008064400c04d684a00d405001c8040a000e80d0140d036240a0006140d20300010b421280e100d00105407070b092003c0341d801183c42a0182d58a8020561681c82c5080041e00314106582c51a1080001081d0321f502c40310440303c090030580c441c00100742e40c00c0d55040824082100100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 483113525 1250 483112275 483112303
    0xb04051b03090115170f010c0e300c10020102090a0e0705070b0403050d1104080c10091502030301091b08040209060f04090803040b160c060c030e0d1d01030605010509040c021c17100305 81
    0x3100d02b00040c84e030040340d0098040d65503091105041c880030340798040391610709404102c031b0700c001088000c1d00407800c0b8010400405c1e00011981c00a00840140c0442c0d0b03a480011407908920b40440341d5556030088005036001c401040012030041900c52550092108403483c100702242080d02e00b0903641d41e03070348100c0c50f03441c0110300002c1030b00d912621421340c66003c0d00300c1c1c412000b40300d08045002941c0303520034468101c12170f02c0c01603541110222503144070f102d40010f54814034541c8540d020000c810744050300c0179a010600140b0b0041a0703c80f8000c5c1c260060144030040e4403440c050401843e4520014590356000c0f280c092041103003a00700d4040100703150085000184000781c13038070581c01030180807000b050a22450450784125035000600300c00d01d8590b13003400c5520521240064040d2031140c0204c90200d00c09000030000b50070260702040072058688100c48070815034160750710b0107800300000ea05c005200c1b54030030708004401d022801e40000d140c00d850480c1900e16190315032109501c0300e0b440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 483114775 1250 483113525 483113539
    0x60f060d0518070303230a050d2d200403080d020705011401120201270b0f040f0609031b05060306091005060408100b04051b03090115170f010c0e 64
    0x11142c0011403404860000e400085807502078503814090610400c140408144d0707240c100c1054500e555110580303603c5419a1940c43c02c180d000d88030700c8040d00018180700b41400000d0400ca41c04d20340703000b41c004a50185400021001c8070014200c1c50b10440d0302021428000c100010800145424216122036003059401600c6140c5850f12501404e0310240e0800e56044040c00828190842041218040d2007602c80c000059415504600740c3c6082600d0ba90b107040c40d1a200300045814030000741418410001d800b403030b080d1507240302d02c24200c2e203422240004201c00c42c1841008145030000701c6c40c0c5508110003503140d24190020784207200c02881c15001d205060f004c581011a940d41c1900900340003012035842c0e44e10f80d030f5a6543c2d502c0907074410a0190074000e659540b41400d04c200c90050340318224000c94450281e540005582c0b0240040b192590303a1602210000d500e4201107000c0c02d00c00a24403550072106002c24a00446607010503602d901d4104c0d83c2d0485034120f041c1a9145805403414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 483116025 1250 483114775 483114781
    0x1b1204030c061b0b07080106020c030a0b060f120d0c021311030103030c0204020909151008040b0c031e0a0f0b06091e0f13050f0108030715020d02190201060e060f060d05 74
    0x580150744040f40000e001076110001d01c00304035048100181a02d04550840381c0c41c88500701010b680c1d401e00400a4071510004011420031706000c0400440020090302d45646001801c85035840e11254410303a800085641d22a070f0110710f030846003080203200c01442807200c0d2116071644d05083c401880000c7c00e014900381400f04540703a50301030302c9055000501c000f40358540340d03500d0303524840402c0d2814400d043d2400c0b40306186009401c2c6a01894001c0064210380c2c1e2404100003c542c0302030071001c4074200030740c480460940b42c5141241b24116000300855105030008000d000d9440700007515103d4030091147c641d55466642010491002c408040514a1001c1c0b0100301412081100650030011052511f0503c800320740140d40200781003102049141e9990300070680300d00403100000c0c407030350081102401c0504ea58028241079607504000501c0c01e01c6810811103c0c5201e14007010260b51202010091564004080380e8031600a41b80100c01441c0381002030031a12030f18100341d1a00da0341e0404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 483117275 1250 483116025 483116057
    0x3060a05060d06060306120b150307050916020714060d0b01140711031c120c031d060a0e190b09070906030b10050105070b06010e030c04021b1204030c06 67
    0x1400020a00a410755039036465003003000016000600607030b40440e04107840041c0a0300f01d50030841303050307402c1a42c0030700725103c2035405220694002081139043c800e40030081400c0e80c1c0e0340407880c001c000b456980032920b01a540c01a05100d420fa02c0007803103079603021180c401a02c0c0c0000722045d541d41d01e000081d4400c6003200603251110380d801c201b00d03061404289a0100030a00380c505c03c40701c030102c0840f01c0082e0140f071480c4281440d40940000a1110400c0c203024130710b50b4010010181807420b000c0f5422810f02e4445034100100c2c44034a61a0b40075905000301e020052080c50310806003031026100380c0408010704481c5404040d4002c0024850304001280c0c02d20511004018148a8106210f1140d0300d06104540c60410750703103080d40c1c0c3c0240130001102d41c000e00031030b09495070101c0d01d0000c40d40d07408019519003c0c0c4a01c4260180200c13001012179960340e200505100c442c088401146844a0501c2072500000d900e4503441041708000c1400404c0c10355000758111422407a00c2005860354181c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 483118525 1250 483117275 483117289
    0x1608070c110f031e1b03010603031b060e1f2003011214010e1e0c0d06020706090b09030c010617060c0906070804060c152a11070e04110a060e060306 65
    0x4144d01d5030601503485000700003004140d5201c20090000000080543c05042508952141c407005001c20301d5141c44e18034490400000c00400d07401340c88005400030480e44454188030081d4074203040c18008054100006040d48206141014030f000e41402d18690650414294030040c0900d601d811690b11501d0204141e1030007801c80400481c3c002e02ca0501d4042c0801c1c0d403800c0d40305502d42041d07000c01000420080c00540c02680d0f120003040903041000503102d44009510041040c1c0d1950307115403000d004600114012405a913102c8011a40e40b9072481c1e40c5401c50f4000d030088100030809a0740c010381c2060026103160020072815a45603140c50401c00a4043e100703000006104000105000070203c0c0c10159005256028800000400601e0740701760049404528030310100e40c0540f8403450361200306c5015038446403080d0401c1b00c841d40c41c1d00600c5280c2160784e840039582c60145002c0000304542125803c02c155030544807629440d09140740506100d95903582c1501a038008000036840b071b076070368cc = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 483119775 1250 483118525 483118543
    0xe03030c0718051608130204060e270708150718090c02010605102001270203070b030f0a1e020d020c12040803040b09040b0301051608070c110f03 64
    0x3040741c0c1c160359181942000541d54607084036280e4a0b00c4002000090301c0703142035a002d1031030f685203040c0b6510f840282180a04028050360040d0380d0301e00101c1c0c41d8000c0300005000b0000e04840e1403815015000c40b1505101504c141030494114500400851000091840c0d40418100d0f0782402d6030b50700081150901084018040402c0e0041400561711070b8a9019400b00140d0f98001d0118a41ba441400a0100150384440019681d4240c103001c44c2d502d205042203120303079a03001040c4042c80513000291007003c44480c3d0542003501d05c0c0201107150030042c080c010107007403502c54218030f0704245800c3e050318000c001ca0503050700c0c0c60942c07244041100e203e11140300c10b04e00440d111205040d00000030b4103c0e01c848801c0317100700703440311120070041030940342202c42801c025440c2c6401e20700d0341c0c40c2d540c1045034010340144d12012483d289640038042c5511450980c07160b80e824400b410001021014080c0c1510b05000d42c060340100810031602c002d0030b12a40664806000041c0600071030701c0c000e486 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 483121025 1250 483119775 483119797
    0x90b040f05070c0c051507030c140d030b0301050a050c07240504030804020f0a0b030c090a080102180a09020702030c010507030e0904321e0a080c2a030d0e0303 70
    0x310040200c4540c200b42d05a03201405541350380c11098840e010b1107003484074031000c4408650306114907000a88140350b2292500c0c461a000b0110044022400d890b203540f840c2000e0100e034803500c0121260409204440e84495405001e01590a040100021900c01d02c44050300c002103285e107003081c1c03032050290202014004a4100980c2c906814005c1001e1000c0d1001c920030120b444403a2501e1034480c4014064a200340c26203461500c64100072807140d0b0102d40506c0e0418800c000c00126003c2c00c0c0f020f40f10303004803100200d50340c403183e20412075416004d40000c0081ca106220100c00368030001000c200c4a0021300307015554000c5401c041d98000e4218442e283d02520b543d00704000c1003034007038601e00e000e03d030b025144440c00700992544d6030181e01a9000f1045034481c00083c549000c001950100c25241d01e003d031808000d254444900c9075000c92015001075010013504d988181c0000d2001956541c52245600c0d0050300c00f0019442d403820348503c40030000c1403001c5404590b014011a2040404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 483122275 1250 483121025 483121031
    0x30219080703060506040e0606031e0c060408030703020c0901060e01050f0906070c031203020a0e0f01090e0114090a0b180c0d0606020f06070e0d0b1e0108160816090b040f 75
    0x82ca01d041d01c080c0c2000c541044c0520700348000036002e02c600044084c040c0704001c01802c0c3c09031903c54682001c078850780d11078200b4407801007200d085864580080014284c1c1d0700240d5980d0320b081c10042d15048030381d815280121001c40041101035440680705030400003d2800d0382e40d80981511444040c0692440d040e4490380c001050007c001ca0b12400350100c07071103031080c414100c602c1d03c802e5040f4016540c25101140a20140391000d150090b40b400c1040414104245020303142e00c14403070b402400341c10140109a1803400c1d02020b1808910b0140d0100701c04100703120b10594000414002c5203205249081202030001180078040000240e038002600000100003296880c40020364905202e41132042070700900021407076807413081c040c5182c00c02c0c0c0078105c682da0071318076071b00c40301c0c184c00c010403600c0500d900201d013541403c5110f240034001c21060f0014916241c0e036041c54110f0501d40e6000046651100040d41606002c120480b012180e03400300000d281b00c0d000e00401c01034000c16200d1034105103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 483123525 1250 483122275 483122279
    0x90a080102070318140609040608120a02010b03030901120b0a0510030b18010e0708040303090b073c05090325030b0c0901080a0b0316062003040b040302190807 70
    0x220550140c94502d02035515228410304142c1d405500c007809020b514000e0202e05d2064446042090042c41040c0000d00002541a60364440d6418008441526a4081c1002402c03411140d4240500d149409049005c2d51030520402e00203040281900004142c603500c0300d03209203041d0f48410404000306000791103a01c4005100b60003c008040c10340b02031f0311404402c80644440d0a850024906070340c8003144c0d81e030850308d980310161000d00005008904141d1144d810400142e6a079403114002c01d1292505403000c8171400c0900030401c901100f0b5032080703d00c0360a04542c0907003200f02c180341114034100103965204004c0401d003030140c0204030346400d81d55000100d0401144614100480c4e00895130500c443e21105800401442003203105d60000389640c01041c56804103a204030014540101103d840d5841c006a400c12035140303a0008000c998003d040402139101c100c1a0003480321024082e501d01403c02039142042c2c040c40c000a0700806418001048111241201201500c0c0d004100c0711015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 483124775 1250 483123525 483123539
    0x1b01021c050a020d030510030f0507030804030803010e07050304020307170a080705030c06010f0e0601050306010905030a03030f0b0d0b0c0f1c05090c0409021c050c06040b0d0506150d050408090a 85
    0xe4840c01011006104d41900008014440d125060103000754121081c0410301c7d40e1039030a8140340000c019203107030158440c0040010385c90801131005601c10380d40c0030b440b58900060282402001060001841020030800c801aa400708410f010340710360040c0260380780d4032070034901c1c500008014000c01c2c00e400002c50341c0c00d0010000c050200f008403c03044a1960b80ca070555180303048468031600700650040e5012410075802000519409a81031504415051f9140c3c0068503111240c1425008250b03100c140d0b55144006000380d0751001005d40d4000890160b41c2d8404074000d0b0028110740b403154022540004021214003107610300c24400041c141e2110b00420002c0007020182e80e010031030b10402049814908143c0149080150010000c5400e4107490300c80c9910f490f81448111564040c25181c0d800c0c40c1d1702d101c05400a01200c8404c00c1d151521509508200d40029089501c204046034460702015000360883d03804106446000c1407507200c4e854401c00fa4014200c400b0b0b4001c80100e000308400c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 483126025 1250 483124775 483124777
    0xf061f05041e030606050111030a080702030f040e0402090c13060c06094806080907150e09090a0f02150c011803031401080c06180d030e1003020406021b01021c05 71
    0x10341d014110800445d542c440054490451141c50008260018040901800d02607121a5409082801541e1414810100415055215410000320140003d052209504055820680c0f01141d068007500c0c024005082d03044e5030b416840380c4d00070812a1802c02c4204101c640013102141c0d4442204060011120761900b0284400002d0031007410414101c030030300c2621041c0c848039030240c48008039011400e0000448400300c00401d41165403080c042c0014035010300c04019002d9100584d900d0034810b17222020440030603400b501c0e14500e0b80c41002820301040d028030025440d1a4101c0d2404020040c1e01040b04c03140c000c9004803010741d46031914103070000302c0c5200140b01c0305100c3c0da003c00950020100100c124802070003610541c0e40100c00b100c2c0c80e81001c2c801002e042095500781043c145071440041c002401914044000650102171a0340508000e0741c400068012401d0543c105400c00c04002d68420507070b07822000000c200d4040c80c145900134460780ca03c1104500050096150080d0042d020b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 483127275 1250 483126025 483126029
    0x17090304150f0e0d0f0c03060b0a0504090206030c130e01090c08090303040c18020706050c040303020c150d0906021c0c0f03060b0318070e010f0e0f061f05041e 70
    0x2045154802404864070a1100d1030982c41252110048415030005000c5011036206044400d074444441443c04203503807004040085100350b0010454070809400c0c40314405180e40b156003d50308003400c01d00107a80749416030b54841c0c90300b01042c2c0c0700c880c8460407072000d0801d94801c021550b103078000441d049900d60411a031a20080d10740e2200b98541564440c0e980c48200d502400314807010304180680e500204584070440c1d0459005402c041c1c040d1113031400c80d43c0640e0084204000000c0400070550103006108038003204440503544843e03a101501d105d0720800c2c2000403800e07919141031003044030701c0d0b055405100c5c03001c0d01c4860f0100240c20010081c4104c00d00701011402d182d0020b030b1254424003400c8241c0e0480344015003107494280f031001c1030081e041806803a500403e040800c2080088400170f0007041c0d5054a021107511340000f03c05407810180c0402c52038001e990400003103403504001404400741c85001da4405c3e0b292148200c5240c01503402504101100c014002072080c655410282 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 483128525 1250 483127275 483127289
    0x20d320f0a020c030d050705030d0c03110c0f0c03060106091503061206140f01120314120702061008060c070201320d0b030d0c151b09061701060509060a17090304 71
    0x104c0d170040d0a60903606801890001031040c0e00411076555140210b8001c0c5850110354200400c0c0308503a030710f40e1010b030f41122500c60382e254005078007211031240400c000ba03135403403081e400fa045e15410840c000742240c80303900958401008400030701c00a28030a0348600014081d803001400711b01c42e0791030f01c0300c0640b065501225500c007620340030031012600004031504954841401d404d02c0045a94203440250001160345500c12060003020700c0300784041d6889114400c55400f500251a1510718103122404640059145902038002c00c520150100211345445809082202e4400c41c104074031800c2010713010452146850024400170031100240c0500118170311b020003442040703c000103160390389500e6640f84000842c0066500c000c1410407122880c002c805000105800300d2508a00c100040c2003016940029034000080000319408081415141c5136041208204d514044004201c0c0c0102030f00107200b0a00007540c1d0100714040d5480380740e0308480c1c0d00300000901d08145110384030b8000384203440c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 483129775 1250 483128525 483128533
    0x2205010e100206070e01030608010504030306030b100f1a0c0d0f1403040f0b0402030f030a021501081f0507020f01060b07030f020601060c0b1806041101020d320f0a020c03 75
    0xc025180040d04004400469802488103655800c812101003914800007418541d9588000c58102e900307000f0340c0c0c8214002c0c0c4000c107080d07203503180c6030007640802049266181c030124418400c203e43c4a000508860074505100c0c2d00c0366402d600911144100900c68046104034440c14000c035400248407018106640c40350b010004603200e214100c0d01c01140c001307100c0d2549018580016104051343c0da041800035040354490034917040b409180d0740c8110500320140c0d11421403210080a504285070141155202411310382e170b030316100c40380700090365817242940c04c0d01c1e00b0000b407002d4800c11000c400c170780d1100000d102e19642c1c1c8469070340a41c0002c0040e000551006021080c07176000107600c0d8100e402c40d81d42d20070035207255111184d180c03201514140c10541d94407104540028104030f414000c034000c00c460000300041c1d0b4000792604801c4580b45042c49403103101b0300c283d5007061444803204196451507448140c06107074040424070a107101c0b100b01402c00308642c040c2c04d80c00510881d10542c10b400b22 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 483131025 1250 483129775 483129797
    0x10e0c0102011a0607050a08041d06181801150b12090303010608070323010b19090b0d090f0b0c0c07140619020111030c13211205220501 60
    0x1203083c1c8030360407102c01c5654030340314007040c0c43d00b014402031131181d001c1c0c2c0c00e452403e01d9903a034444055111741e21a450490810000d0101c04100c21310303039604070804a0340c3c00d000f008a51180d158075403000741100042d01c05030b010045070000039000f0b01c0185140d04641800d140d01c0e0050703094280c000343da0202462641e100041c10311702c00002140c1c182d52840e103030060559030b01a0120050f002044030524007468818291003000d45d1140d059019090308508a80c0340d2180f1025030310400d00349603405007000403190040103019081400c882500c00c0d0359001190003c010b0800d200080c00c40e90340141405019401c001180600e80007030b100c0340417a6425100d0441c1c0d64880b06043c0e0392848100f5512040070002e2501041c1c50220b181d00c1d103200c0340004a42d11000c0f40c2480b40c160811030310568104800100050108060380800f80a403260201c1070a492082451580001003140c0009001846451021101d2401482540c500c2d08180424480c40140c003041040d60170b0461007440e0102d480c5040c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 483132275 1250 483131025 483131027
    0x204170703051f09060c080702010c0e06180d08070b09160b030105060a0318380105060a09030803041109090303131e0503040b090108060a0b031302120d02010e0c01 72
    0x4600e04032038000d0010202140d104481d1030365111560544a01c040e0782c1d00350100054094007944500c07511742c1e101c082035407802c007401909443c0301034514402c0001009140c0e00c55070b105002d40d56001207003800f103070691091030007064401402f4070307000d00880c40c04245481003220720b034801032060611005483c3c88103400240c640791000e83d4042d0380d1517000f003440103011504050000d48a98112440d000c91b0580251b049900010040c0d0000c0d038106500c0090340d1801e81d251071001c40074142201064190b4100a003103140070804c10300074981f00e220005200381c41c251203030300080061500010a6903980c05c0518121400b0154140780178010842c600010700c0703c940c0442542d1090440228075085001c581d41c60000e42c15030361840700b14142d040e00340200400c030100007503c0940844020b86540d01c0e0401c2c005015110018086441440d070042e062003201071900a8a410500089121070b4074440303480001e440221541c0ba06149104650a42440b641e05401a101286003003090326008020040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 483133525 1250 483132275 483132283
    0x9040b06130e0a06120c05040e030c1009032304260a0b06010212040b040f0e0907061119081c0b100c020d1209060909021305280801020417 61
    0x1c00d50525100040081040004070800e20781c0c0004501d01c00500d0a49443e0100b0806030100420b607250700c0d2840050203d03041c41d01c5009580c221820065050141410315103507189045c00b01060a01d4a8040306020140108038080e81000c140c0105a00c034031008501c2d08041d04988030b008110350207003141d2000c907080e0714181841310901d41d000d00407840641c0ca40c2e84d4013400240c203a90440c880d280202141e102d512019001805c0c80302da10903030301e500d410710791a4142e0282d04030106072245181400b600c284001503103400c60702c190a1620343d1031100c092250608501e844400045203440306401d080100c1540103014480401c4c0d050b085001c284d01d90102281d61000d60203410644808656041c1401041244000740c40180200d040d80c00c250b441c14460054180c8250200300204000d016403500042110060400c441045041c040400c44c1030041320b40500c04c40c2d008130380c0184418090f0040040411114076200c120b02441542c030740f2141d000754403502c40c0c030070706060145011100d42c0c0301003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 483134775 1250 483133525 483133537
    0x203011203020709050606160c0503100f0b0f0a0612320f0403050906130b070629030615040917130e090c01080c21011809051b0607021509040b06 64
    0x31f41600d00f44220799668034682020346034161000c034044080050b01d581d04000541c52507546103c00b080d00c01040030311800f601d6011040714030401040075120165240c0900400840708036203840c402049203681c3c3c0034000d196400041c40454901c1e0f00025030509079034200e0307003400e207000340c103402c1e954807408425035104c01543c00500080301044002c1d450b244c04405450700000c14401722038680c1e41c6405c0007101e030340049000c1741c403d502ca8018149050710004480c01079130b410310402ca019103003540000e4445070002c00b03400864107120144450303500c4a0b80240c0c1c413241c1c0034420108008407211840f140f40c0003da400f40c4005503400020446420303c404050180b0002c42c01071040060348001510401001040030802c0030051002c20b58162110520017045101e00c0c111403215410021040d5003082070960424142d4100b040c1034000031000125940305c035528000785003140544030005511171040d00f402a5020501d5903861070644010300c01803055090440f000c0000000c55018403240d80100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 483136025 1250 483134775 483134779
    0x3030708010303030b010e04050117161802210f01090b01030915050705220302030607170708100f0e09070f03051b0406030c0e160207050d02130f02030112030207090506 74
    0xa40040001134082c1e002485101c00504007501020044404142103640983c00b0411034032441d280526100000c3c003101001d40403915840846a040c55004010528203a0050550f90f5000480104c4840b0349000c1d240d140010314280d290b641020041070301a14420b00880c0c1540d450101c070440598081d100310144142c0c42840d290380c0076030992441000300801405041070250400010b00c0303811806615089092240e0f0400c1d0501d82540185440c05c100200200203114144008406140305000f03501d038003140514210342541d5981149501e00001c035407009068200001010440c1d143d1240c4542c40f03100c404003141c0d0f910390758083e4505800305a00c4054400d41015804032002c078621800d0515200000d072012076426965500c5cad41440c04241e01c24645814800c043c8a8034104440011542100380c4c8005c000302420304001400d11103a0303c800a00c42c0325072034010801c000c0281c00840152000c5c610440d01c0350307502c000420383c800300b404044005020320b010115600505104040c091100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 483137275 1250 483136025 483136037
    0xd0b01020105061f030504050c090403050a08070f1707020c130c0e15270d0b01050f09010308042c01030c06080702031c09020f030d180503030909040618062408030307 73
    0x21140054004000c0a0019655801271140c400d41940780c03103075180d00131446640c0c1c00ba41d07960041342c014440740021b0940010480c141000c00c0b411540310000301280120300800328919120044140d1070a401d8800b50b5070030040074514800d0114040d400408001410744421855152040400501c0c01000002580c5520140418001541c209a030405012603403510450650342c04c10008078960f036020400c48641803191300600081c10000b124010940c819030f5043d4055046035100c0c02540200c1c001c00d020f0341e50000d03402140c1c5000a03184030050034010308140040d40c481c00c191141d03070068003c020200e40c02e2000f24000394800002c4490100752440c040944080483d620409058005001c1c0c3c0d00500240a411a0b0303a424004014540070030b45a03403d4441040c0e20030304070017004e580154400c0e007040c170602090341c582942069005911140004400c4110085102c14804000001d40591b1810706001c034056100040c284c0400c01c10711040c46041ea440e03110780e41d40d10040710300c1000208 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 483138525 1250 483137275 483137329
    0x140d0306050d292701020c0703021e12061005061206100c050114060f0f01050304020f01180b030613050919142a010905061c0207080d0b0102010506 65
    0x41c82e100c0420a51000c60340484100c803881010b2040644141d8919820203040d480e1011613a10a103464800250904029030900b01c6c83e140168a50380d062002a0003680140c0f0062800104541140c4102c08010600e0524202400b89159100b904a96140c03140c2482180410203207800c00031390340c80d005404850f051590300c0c002401081482c2e502c2ca8010f1021092003c00051400c0c02001c6100042e407144041c3c91030a04c04220b4220303600844c00e0302810070604500f0841e42d01c5411a684250107980c0303540d001502100407070b181c150048202d000d401800302e0201e0044041002540105811186980260081c0c00c503101226025210140d10703900400e030403500020084c60a41d4041c0c05100300420402d0f4400000f0305203011041c07050742c1ca201101e280d031444a8040510402c9450a2803c1c81003e8240008107a8071301c50308010380340103081c04c0d00300b0440d1407040c1c044950240e40140c8aa85460000e000700000c0c0c040c0641e017502550920b40000d0440c1040011203c000045062100d1a04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 483139775 1250 483138525 483138533
    0xc031b2301020418290310020d0b0117090a030509060d0903020d080a0506060301030b1306061d1f061404091407120c09050103090302010b0d081c0e0a0303110d050103140d0306050d 79
    0x6141d03410046e058042e4060000c03070800765102a04a00c00b0142001c11f450800d4800103100503400c0010b020585038402c00e00000e88800910543c8441d0b00d414425524544000090410b010348442805014103061300203040590201d00011403990701c0c0c45001d550784419150380155030007262040c1c0c00c100b0520041011583d0035403481d80020401d00c41e00c42030761440d1942c509941054202894014940d80103495881d030f5052415131040d1340d1000e86080c0794005000c6429288075124178401c02c950442d00c141150a001c04071401403e201c8010401c00514074a1302e551400105e8054004c40c8102d40d010841c880ca5004d640003003606540e4083d09181804010b40060003019415003c640d601c00c0c81ea02d4944409158043c181d0040d20300b01d46405844242c0303c004050314200a41003810541d0301503140c2c2002450500042d45410041100d00c20046100c0c6203014141303c489150f8108000081484410760070b03130f80b001e4a20360607602d804c409150300381c0655405202d655040414048900081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 483141025 1250 483139775 483139841
    0x7080316030804111f0f0513120213020703020c0103050601030b090a02131205060906180a02060d11120901060b070302120f0f21070c031b2301020418 66
    0x414130034005284072130400804a01e4255914041e0441041c0a6200395041c68100d650b0000807842494407a1a01a1921070202060001d10440c0b01c440e01c0c2e035007070b0000c55841241e0340f104160a41d208540314170741401c009540c1c40340060032038003092910001c2503840d4440e005c7c4200000c000380905941c3d0b202c00c44118001c1d8032410441c4140f00d64000081084207500021004003401600180035606103003041d81d040000140c10044905a03045030b00102c89004036411101940440e02580c0b41c0320b00d035040d103020b4452071070010308a05000940c0c4048002080102c0c0c081d071400c1008000071511442d05940300e10480c10040c0260340401406040200e4602c02032000e0000f0700004c80c28105a902086125080400c0c180c0500f04403010300041610792032803540e8003c0c82da1802c1d83d0910072588014001c0401d003c040a4611188041601409902112060703901c0001414210580b08a141036000350890300424410054002406807040924001d94203c1c0307480b03406202042c004541100c0351 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 483142275 1250 483141025 483141031
    0x906100f03060f0602030c0111280e040e0a030f0f050d020702061608040303030b03010c0522080729040627080610030210030c082d0a06030302070803160308 69
    0x81540700c100101d5100148480a002130106400640d1035101e003031035513800d42e01d000300c0307020702c00320107110314981c40307030510141c003054021100c452003842e242400407140050088400f50700075042055007807240c0c00000711902e0141c043d648115400481180440320b60804192100000302c0501001090003e541d004004540c40180254641000000e4000900001c0744043e52101808a010000d00d5054040c3c0d120440c0203c0c002c001c040352115000d40305000340d0f00445110040041140e00320031038080e00801a000c44011140070541d900305400c50031800b9030001000340c201803c600c588003100d206403015682e40d07444001003001d451072184e43d0720f0203200b0940c2414106110014200308144a01c5008e100c8584c40c5007c00c07421401404590111a01000f00305403030040780700384080d48280b845402c1464043c4054004103150920300e107050381c00e03016454040c80c0300b0901981001d517074010400c49204e90251803c595480d00001c1d2240501c0360341c0c140c01a002007031107000034030461a480d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 483143525 1250 483142275 483142277
    0x506090405100c18031a0109140a02030604020c011a010f0201020403050c01050f07140318031606050903030405091303180f06200105070903141609050c12090109020a050906100f 78
    0x103907008208103c604c01000c903500664480402d40101c5000074540030742980504070054041c0030588403069041742e01100288240e079056404800303c1d040d561681c044440b41d800c000000e1201030441d8400d070038951920b01201e4080383c461200581014018026203045a4210001e00001307505c0800540e000d0b4005621800c50110801a0310006281d01b2980e401050b0444002d5403200d104503243c020000d0b002d1038041c8039600c4906029540c00802c0381c40402d880c214642180c0b21130707281d00468614015038212a81c40140d0b82c04110b010f4400b1540d204a40b030003599500ca080b012050000d0007070031036000d94243c1c1e200207034080c824103008598002c0c4025101d240014009003a80e840c500711101904e43c540000c00c1e5040070410702c505030580e0110714040402404040c100215040302c10042c6103c2c9000d0581ca450004403001a8801503c3c03059816001c00140ca142c10600d090003450020700c201d10600360400c0c0401c0e02d050a8007400d1107510040c0c00b80703d01c0103c0780c0c000d9840f2820000810 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 483144775 1250 483143525 483143537
    0xb01030902030625030603120e04111204020a0b0c070e0408191e020102040f03060e03070506190614010c0305070507030c15140c0307021e1c060506090405100c 70
    0x480161400c1245500c6034004040440610f0304c182c198510001030400c8582c109800d094041c408a02582c4442e2001003080c00c0c403180101542000c1406000d41c1c0321803182c440c1000c51100460704d4030008a42c4980e10032140c025003203403100c00509242c080e00a04644980c000740041c4030782c0110b801e04a400500031080ba07810070142240d000040304880200d0000a008102609407503081c0000c00b00c2406920700081d42014100300b64841c50b04868030018186544606403c00c203482c040c4126112250003006980861a0141881294a59600718090400d18080c80040d00d0341006c03002500500d0140d6640d407200c50580c904555030b4102034400e8800e8044d03c800007000487d071084410081042c030301a207212042c95200601400564031190401200c01c20641c041544027100b202c0e000d0b81d04442c103280c0b48140652041c46068121001c50700711110001024500109501701032429104803014802580c2d040140b1181c1c207400c0d0340084c5a0b5010703964403100101650030228440e05145000c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 483146025 1250 483144775 483144791
    0x170a0905031903090204021c0b09040b07140706050106110d0f050403020609300114040c050405180601030f060e0a0c170f01021201080d020d08040308060d080d0c180e06040b0103 78
    0x4080780d2010341c1014001503c3c0c50320840103123490180c00e03c2001e0455a0306034903c5d043c1c9400c804000020200c208000032981c210320310303020150989248603044101000fa0b580c542202800c000f0101c1c1411169104904110400a110b0182c09000d50b183d03643d024101403550342070150f1034201c00f101030b0384124448940071644076101070b101009016031101207502540c1340d0038103003183c0225906603281819003040002080700b042604048800c150303030000e400d94980482d00864a010301c4222071600450000200f4400007400d40d50086002d0081000304201d02c4650665424808d04001c1400d40301650800c4110b8403000c1d0000405501400d541280c51502c090500f2a030140f0940800d4100750401030140003010042004500e01c50300041c0666107440c40c01a1007a08001c00c001c08000c006000691592124009600425401810b00d900c8104000d0000090704800c0d5500c0000307942c0340404a034141002c0c46c15801c0ba0300784141029161142d200303000107465450811414580c0b22110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 483147275 1250 483146025 483146029
    0x50d0c0509090606190e180c0d08090343050d06060e0901060b07060203060307030c06111006060c110f09040f060e1506011815170a09050319030902 65
    0x1e81c1d10485004024041d180b03002c50421140d03405003195420040c0440c0790500078130700c40f0310fa40b03038001c808100c0012510040c004050311380043c04c10b22503080070102d200c41c0e04205002d809070100c080100e09880e54201140000c40811003000c0d02040309218100c0d4020144880300303001e214070346800080303000c059191408202c5469003004200e6401d540c0707000070000342d0705021241d0b07000341074a802444003c0c40d050311500103014000c4068600c0d580080400c0e0690750170805c810003194003120395a0016601c09014000042c454001800d034001d0f403031241106080f40c030822045e10301903221504d50702c2564071a06404c2e8207074850a82c004215410300716855441c1210103104510131484010302c0e80080c64482e094402120000700117034040300c0e04080078003140a00c150b010b502860400c0b5145a9006d00f681100c106501180c82400d90b8401515007a03803102501d4150403002010074416140d42d80340340c00711540110040c0c81604180400101d500003000c02c40c0e0751f00840e29002ca41c2d0300702600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 483148525 1250 483147275 483147289
    0x30402151b061005130b01051b030712110c0f01091503020408030708070210050f161e0c0609211704080f150a02070b0c030a090f111804030504050d0c05 67
    0x189404101c0f4080b83c040005140104410720015054041808142ca40070000707081ca000b907118241000c020603074000e04180040054405081d0041500f107035050502d1400741101d1091400e43c0000d00521030104805c0c20420058481c41c40183d581c03001191030080c0d01d240b21185145818201502013100240b04d52080024240c007030300602855070f0300c0d1040c0c410000c04000d1241c480b424004140031000e01c00c42135400f0b41d41400804030706030401508501d1308415001b901c408003034000910481d04018003000b03050300e40983e1640d071208400c141c0c0ba103c6003040d00503040c02a00683d422084035000042003082d002650b0195480000d040c04c0e00c1e54911410310b001c103140c2240d260300c843e0341100280341c04483c854024101801c118a00a0151241040c8490041150302c18031400000700e03045080552150409a8108011615001c05840c00c1c40200408002e00d40c42613450b80b204094449000102c40e00076940364540c503142500c0c01061000901603240180c4d650403026200003155160f005c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 483149775 1250 483148525 483148531
    0x30a020306040204020a0c21081e010506070f08030a0614040605030c060d06050d060e0111040b07020d110a030602070605071412040206070803040305191d19170703110105030402151b06 81
    0x884a8402340c4c905500280207060080c026414400a510f540010442207020941959000c2d51600d980304114240108030680c6040300404000c00041008885c0045900890030f558a1141171070514a2050410059030441c1c040d071540350f000781501102c50300d0150f00038030715412088000700b026561140007844002c407404040d100d441e124412005000028456150903c0b0344400c51810702d403e2203e0b8018901406500900401b0390149900a200d40d81c900c00c0480c0030010600c0d1401510f9141010107901705070b4048036250306142c0441c0d0302d54068641800c00030b05005241d030401e20070038048402039002603c1aa0010001c1000740040b905050013140f046009844060742c961700001d2000003a103441120030100410072000c0d2504106528428034003040440b840b0084400103043d9020a000e50b030710402d01006690898142e0601c08140607080744d02840b0012898050140155413510041314020350203c160302801d0105035a10340078118507901813001c0e28400c80d031140d02925041c429 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 483151025 1250 483149775 483149813
    0xb0418030c060b090c070210020c0406090e0c030601030f080d020d020d02040e06490b0105090a090c0b0c0309100e100306080c09090a060c030c0806030a020306040204020a0c 76
    0x41014009104160142085843c030030b54682080b842d00c1d00365060b040c059904000d104550785120400807038400c000007404513400500030040320350740d034004000414415030301848078010550808601d1a010441a0407a47c01500000091600e0b99a44503154019400d0f09040341d401e110030304844484c2e2000c6c0c8040d03001400c2c016902d0303080c29010070403e2801000705200e120b8440d1040042031440c40e030744041c001c0704c0c070509902c00e503540007401c000504503140111a5030760305588001e200d01200d40c40c0c1280d41c161000081038680000c00000d4404481307000e07105040310a002c0014503112070080000342500800d980c288020f80000643d8960364011800019200c130909039a1403034032960510600810782010030509103840006520354064100151003440c60800160070030500b880180c524550010082100c0b10341900080c2c02415554421000100000d0008400342000900c2450a5030014010a400c0e615079080202a6203d54004010003081001890004103a074101a61523248 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 483152275 1250 483151025 483151037
    0xf0f0c10150e16020d0806043801081012030528020f01150909020f180702010501092a050904020a031e0b010c080304020a180b12011a040b041803 64
    0x2d404800002c1c0c0a01925100401d442d01440d58507a03900051035a0304518181400e001e10b9840c040080e00608450f140580341c1e0466181c0581180d002100b0305401d400c100320035a5031500c0c0c0c3c00044030704490880300c85868107008001485081c1c005d03008155203d100e8503105e0b141c0310000d001600d00741c1000c1c07071401c1400091400080c2c102c1d01402560140c0c200203008003c0d0250121060b19000c0f0140f05100d2403554444c18041035480386c410740801c2801c0902460300c5800803020060b41040100c0d42c040055280000105800700c050081d0b200100030ad00c0d0000503181c00f02444a2224804400f9600b400000c01800140351074900141030011101d0318005140c0c03503c1d009901100402c030203d1034419243c000d161103141e8021440000c202e402110302c44d203035951403000c0b6426a40c3e070b400604014200844191044601e600020200c2109544041c4401e24502d4464266004a512503002c03c0d035940311517000d0b00300b1358400926440010700128007902100302902d0b190446080540000721 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 483153525 1250 483152275 483152279
    0x7080f07060b03010f020f04030b09430f03110d02120304080714060406050c010e010f05180d021218120307021806010c060c031407080105030d02030f0f0c1015 70
    0x43c00780320b02e80089000c040d040d468490414100241c0d4443c80c040100700091074404610505010040b09915485941800701c00404034501907100072101005c4060051100054009000300040c0031421148003a01d406041c90440d61030355040801e030ba19003900881c4908440d005a902c04003514524003180c00034596031070a02d806181000c0c03d54004561a5002940186050315401c003180c0071a0302610300151103075030f00c0c07050301d0140c0310b0346100010a600704904208003c0791584458005c5210904103203c0d04411002070340c039940c0640e5440d0140e0000914200f10300445c00062000d40300c100c041d004507014100010300d4a00310809a0001035001142c0c0310110309080842141d07090007050b0b041040e2400da00000c009a103840030082007162640e0106505500035044103005800382940ca40803880d14210061030454244200e034440e114158900d072502d8004822948021090700751039260000314201c4112590080c0150010703845150030001e0400306d28815612480c0c0201401a2828 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 483154775 1250 483153525 483153529
    0xb0906071439120d030e070b0d0f0e060411210f0319091404020f0f07050d020c0414010b0f07140604030f03050c030a0b1908151806070507080f07060b 66
    0x26040341990300031404681ca528520b90006050130150805150114800946a00003030600815500ca1001d6140100d410041a403e540180c814004151001c0119110260704a40d841c042030720040c201170020580d0b848141807030040801514503a012040200710301007402407526011301d000c2102d6400110300783c1e0a0080180001000403c1498117044190915400300b01121007070310a5840380e80e000401380281c2a83e442900c0f40d00d044400e115072524050704001d92254800030001c8018060031100342d030240703018880c80c03111803000728801c00541c0c01c0c804200300540c00500a00500b8a083c01620000740d040048030261000c200c015000034101442c000c1c003402041c04043c0145030910f401c22940417010000d49a2098403000c0c003140300300ca0b1001107040100c1420548554103500000468400d2000801071408860104141020740d10042d0140d100c2d180c05150760001d800c40d07404100d2140c46000540f18060103040914a0540b4140c02d4114585c08032400303d0f074103511208000154 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 483156025 1250 483154775 483154873
    0x30f0c0d080c04091509020f03040203010b060c0a110301020d0504120f05030712020a031b021510030c030320150105010206150306010b0708070b04030302070c0b09060714 75
    0xd254a040400441c188144200745500030b41c0038100040d079440700fa0300503101680882c0402008544000c658945016054400b41e42c000c1710141d009608119040f00d0a0501c5011140b0407240203000d85440daa690355080b41010102503070710343c90340d024084a40c00c020240b0805005500ca40300e520b006013900b00f405005d0fa004441d10006200b07051003000166a00801d2141210342c002d00b00503a1142a0708094005000360650712120401980b042c0d1407040d0001a58605002c600246614079664160060f04203a1036020040c2000a01d000c20000a03000fa10071071640301500070700315a170700384003c405441c0840300e441c501c0303d11000c20010409941c040c40590f0304840451030503140402814080b81c0c3e11181803061602c020030025440007400950030654168591014400301542441d00b8020042d4002d48410707540b001d003815000075113205150032200146c038060911070a01c3c603191541079920380340340c846c04000c2c042c525002404a848000322040481c048000fa403403064210401c1d507074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 483157275 1250 483156025 483156043
    0x50409061502150708040314071a09010b1c02010818030304050a12020f0703030e0301060308030a090501291521090106080f0703081b030d02120a06180c030e030f0c 72
    0xf05503d240c0034003401d540e02c01d01d0b00d80d0194150070501c414054000f042d014a1007402000707041c2c600c3d41c03080d89410740c206d041c485014904190080c40360041010030401c0e900b00104015001c60410208540154020300c2165444400080c0102e10b140c07040b40742078295801101c0807070700d5410004104040002d05a03118000d00c0d0705e4401414050901c3c4000c0b5600d846900028040c803039000521403045d0341c00d401040155500103405c85d101d0500607200005041080000c50300b035420078004038002032114000c210b03100522170303603411180304000500c188903d4400014600000400000455a0542c000160741100e000d213611f203645003140c5958211941504103c0c840d410034080b000030721000007541320540750080c90b51503960700804540038074075151104029a03804082280000380246c2e60180241c03040d5400c2802180d0b640b0030000017103480368050b464202c0c00320001000010300300c0d4410101151682000282c11246480d80c03407940d001201c08190807040081c03500c0790010240100c1e80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 483158525 1250 483157275 483157303
    0x6040b030d050a021608030d0509030f04060e0901050d0302151506120402010905060f0d0b1f0203130609120f02030a06360f0b04030c02060a0306080f0a030f0e01050409061502 77
    0x20b0b00f015501c6c1c0c2c4078880c034215405100d0b01d6030042960410b081c000c0352240d07103961000135079840e500c00300507001c40d00c8107240e2803107400c4000000a00307041294280c84040d07030590181c00b48080c00e104091148030b020f0072a403401008034036500c0003511884002c0020b90f84111004001d46030920004003035884981020b4000c070014024041c418140c070080d9a076114083c1c002095030340348207002c21040e58800c002c900c05040440e8607605405c0e0044014048900d84044240113540c5600d42a00d005005200300c04004081001c0c0d0408a8800c0c41c03110b014a100805643c0c410119031191000c0e914110007140025090000405102601c00301c03d01d0344d071960b00034034a50074220b41c9842c0d40088070b07224084e241d40c2907000003038109889400d45410196008203525101d6903a00d80c014024819030055446601c14020380f02a54500020741e1054240e1558030820303000c0342040102c4204400464142c1804028000440c42c510a401080045c10b09141c0740b54039040440740007460003603a907590310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 483159775 1250 483158525 483158563
    0x506030606030723040b1305010303120e060708042901180603020d031809020712030c0c0c0528091b17040605060109080d0905030d02031303060506040b030d050a02 72
    0x8510301200100d00b48076400c4d0320440505483d59800305014040d00100c455110010f0840900c1c0c9410701c2c1d001038143d90007683c40d040c60302c10743c01c410001c9403940c0e02c5440c0c3c5903000720005a1221301c074402c1254898030401d5400b0408842c180b28000200d1414a846481c049441c0113101d4060f0001d120808480300d0f100a01c0301e60b140d5004a011340342c4402001e01000900e1307501003008554802a8401040c500408668401d00781c1040e900c00c50140038503400207424000a030041c0c911800072143c04d00e400c080208005481e00c402c02065050003d01c08851040111000240540c81110500101404c6001140c0b03100640495401c60109034907400502c15145442109154819035403a440b03544000000b4140e11640010fa030360120343d900c14210f0340304a00104950750b81c04007008044032010307002c480c2003c81c00c95080e600d9006481702c1c1d44551002c0441003000c295650405500107002030000500400e810001c01c0c00c206240700008045080007031209401941000042c44e080d1200c881e807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 483161025 1250 483159775 483159779
    0xf0c03050d09081b010618050702030a031a040c08100b1c020c07090207030513090c1704020d020d05060f06040b010c020103201908090604020603180f010f05060306060307 75
    0x10340903000d80001251110b40c0c444129040203031102c1100c94102e030150741d03c0c1094000d404214007034100c074010820f44898400c0c200030910403a01440b4001c42140d00610b0401d9002e82040b402040c10000c003812184521518078802d48540c03103846002100f50383c0d103508a1600d031014240100d410791001280359070400000035020050303c0c1250b03071580020030150b91140c0b050482c2d4948845070300080c5181d0700c000356003010035400000034540340b844011664006a900c0d90108201c881d5580700c40040307a07a01c1d051110343c4100490f10741d40944020180c591001907030700800d0580c1c82582e001c603240d034020410301070020b00b5480880c1c0c0c000000c8070180800f41202c0d00003811141c01c940700030706140e201c42201c42d403080d0000210080c030000f911940d4031055444602c0c100c11008005100200d022403010802c0c100c0c0c0450b82c0da11840e0041c1c0307250300e191201640145030700c1091075503226600a4024149a40b035082c01002c120021100c0007140c282004e40400d418040c000c0e002c0e52082d0311410003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 483162275 1250 483161025 483161027
    0x271b0305120c03120c0403020f0906030d030e0a05030a0809100b030a06022b33150203040b07030507200d03050c160e011d01030b1b1605010c0f0c03 65
    0x11800e28003010104042d01c4160381d400c40391071800307036464680001c00003074104400d1410010207401140e000721080f001c02c41c00c240500c090400261039007905604071880b03060709c0c14041d42114000c0100030044400e00e804036202c09003550004960070000459413020320105503c00c0103a040300611620301001011082c03000255500c07040e00004280c03a4011420740d52524003d00b454070490140503c1000c150303409010200100f00d4030200c001c03059000344030600e80031102ca1020705507a4224240055071400c1c140c4400f00030b04a03000d00c00c1188001c20020408150344000307000910f111b0b4490640700c01c83c500d80013085508011115035a80b401c90380f044440c0d81c545d140072242c5505400c0c02c95842e1200506141400d030191020040740500e0800001d400d0968441203049030312400c40b00914541c2c031400d40010305420b100143c16042594003143c5080a1030242c003000c1d41100b43e10514002e200e41152000e515625010b0700c09940d030305000040141c00c012081090b13480c5283c99074541001e076074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 483163525 1250 483162275 483162283
    0x30c010c0306082e090b0f070f02010e060a0207060626010b01031b0309110307180b032407020102040302040501140909010b061b0c060301080d030e010603200103271b0305 75
    0x244400d80d144840c2c16034100440507501c456015030300302c0248940c62414828109101c88251010230000e40c08191850520b0300c10b10590301554000c0010300580d0b00d0700307100d07000690030425060711495aa6600007900f40c101c4440034581c58a81e0400e07030b040e40e06640310709003140d620507502414503040c004600d01240c0c80701140a00d0140c941000102800c03941880f11000240d84c18040d01885000400b0540d5040f903001c13001c0c40464400c09008002929040c1521840003001c104401900c0c0404041c0814025502e60351003030302e5100040c1050740c0d9400140a5032000c1e8400404078240c034034950340506210140507446a45240203108440364480403420500c80c40100c0c00c9502041ca1406408003c01d014900700c014006150782c0d02c030b5848043d03140d100c0f038059841310042403501d1241d40351010706000e0702d41165000345000280504403000c1c00700c00d07002c801c5007a040590700c0780340d007810440140c41c0d072072180e01090800c081c04080e03141200441d00209013040d11140d082e1010400104005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 483164775 1250 483163525 483163573
    0x90f0b04060e01030f092a17070302120f010515040e0714040e010207021008250f030c051c0b010207090b0306010311010507140c18070e061b030c010c030608 69
    0x841c0004040710085c80701d0005040c0307848010910520505080340c09400d1031082d000d400105114880520380e15986101c09007001d401365003054200403004c001502d02499801d140500d07027029103415035841400a421500116581c1c0103282001000804d1402c252107440d04031800c540041210905020440454003003a6600b584115290015200008829019255a1b41c0d0103015071560410010025009900c00c0310b00c01d8440400b000743c81a159103489405c09410b01a440340f114880b00150704502504c0354084900c00d1040030088544241020108512900109480040c4640503140024101780c0325621032145c41d420000851116a408a0303000d045943c0324161010418540c8016107445c001c10002410a0040c940400903201c804102c58a19203000c0b0b92102900140030155400b4100540d40e2000156506000103c41d041490007020f2945c4003a11403d591440344540500c0c0d0752003044001100c1e511201348244d45600b40c0503900140c61540c01030301c0c020304103007841c414a030703c80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 483166025 1250 483164775 483164777
    0x709140915030708060a02090907081302040f0605120f010c03020f18040b0904050105010f050105160b0c0433020d120c090b0307020307030e01020309010c1113020a090f0b04060e01 79
    0x110301c00d5490303581c104801d10003001960180c13a2249400072000c0000e4200100141c040c0c85078200254889108800b01407081c08a4200c03039140d4500e40d02800000c1c50384211074485259070b800049416a10710000000c18034161008004800340e60070118250b400a00846040c27500501c401ca0781d0046050aa03000740d00e0302c40f40303250302e00074820010303015150300c080107600240c0c41d005010074030006401c020f06803800341c89120f06c0715980d040115114800c5c1000c0d5540464010092000144c0484546820000b01c1007603030306054961001103074442c1c2d01c6e44106141120310f1101c0013180b903088201c502c081401c0c0041d2003404880c110191100800b0191301602a5545100c2c00a45004080d5a40948100c04409407a8505600040e54a5200c040c0550100b201c0c84404546984000100c0d131820340103a5030391003000442d07030f1000342c5490a540d801d6400401d42a00055040d018405003000024982d0303100b050502d8012454856862508006844502040148502a00908402c01c01842 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 483167275 1250 483166025 483166051
    0x702030f0c01110c161224091e0b09030f0418060f0b040323070603020d1107032003040806060d1b0f05040f020705060105010c2907091409 61
    0x30707101580e00400030f10352440031030540400c91810b0b08100080307041c071502d2031851844610341c503600c42a0921501c002c000f80340011001d02110100c407405044084040da410002c1800e445583e5556603800d00d00002200c44080c1c180c0c840b09000c0b407544500d401110708000741d85007100b45411101c81d80f1460054020811001c008200d8440460b403008c401003020f00c20200810b52640200f90307c1364070030b10003610019089403d048121b01c181c2e482d8041c50080c400284100d0b443c264080d0b002e500700080703100c0910344c0d9418070240d6000e4100104151840b0f503851080c480050201010f101e442c901450905034030a12040c40080300015000350400c1d0102e802007846800d5180880c004c0203004c1d04090f80c55100c83c80060030304003801800c020358504860a000d01c20300400c14800306d00401d44041c080d9480080100855402100000e032003900600c40700390040000510020b079081c140600d550701300d441d01c081028456001e00101c0140810341040c0d4547d400c10800aa42c14101070205058254 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 483168525 1250 483167275 483167287
    0x60403080c2d1e1c1b03020307150c1205070c0c0b1207080f07080414100e0606010c0312150b0705071e05100f050c10060302030c1c0609080409020408030910080702030f 74
    0x10044182c0b0030005494010701110484502d0000d4407600044821981040500c140c1c2107a4036203405002101c2a8963300e046058a083c2c0c5010b01801024200c80140605200d60b0400b00701c101c01c42d4400340603e2460940e40303c440c01005021254010040e000f08124007007403118800000f003200d5008003840c038007081c8603195410840300300312901684103002d00c070b40c152011903c0b0054004881d501c5841c0180c0781c0503940e050041d28251616900100000c083c01d001401200d421742c407004600100308040521551aa92005020390003080d080c1d4456210010070820060b42402c41212201d0071007007103c54504d854040343c070132041a4229024440200d03d0349002c079202d0300a90300300d448000d08440e040d1101c02d8414004101034001640640203032459039103681448a9111080307039036444803a080e21013580f2181e00030060007804442420081000140d60f40550024001510220015595808e00c035002c00c06005010032105080c400014108040a038012081c1c550582c001c040081d40d81c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 483169775 1250 483168525 483168527
    0x3040e09060f19060b030a0f050f16140412080301090b0a030c05010305090a0b15010e0402040e0c0318030a0f0e03060f010b070203030909010f150905060403080c2d1e1c 74
    0x440713290410b07890001c0100c1000080d8240f0b400c401c0461080342d204001ca6194039038100e080100865407200800514455040710512481d01e65443d680801301c480d08081d220307145007410258001c0705880e415004001030000c1096441900c140c207200711a03c200c414a1980d803094240780e24820036040c1561400081c0c59460140074103850f25504c6071584004c0c2c60600c5110024820b0030421a0008100030f07284002410144211420346a0340f131102072035a0f40c0c00300c072007a4651001300002c0107240d040c048080c10340b0b0200050700c0f00c01040c0d00c5607a04045501c00091074910828100c03482075104006104211071a1440c0d10b041d03a9010711070903039a814900100749507115000c50250020107840000400e0f100d840081d5040d5010800da0b694001d12000b01156006040e010711a03010174100420000140701ca0000c3c0b440f5005182134070000c1203100b18040c0c05940f0381041207510310601207100e00701001840070210042076101c954008601030304845640d040e900325030102440c1c411001c00e0003d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 483171025 1250 483169775 483169781
    0x4061512170a050706060b0c0706030203060a090b0a090504030527010e01121404050a170307080112030c1a0106030c03090305040509040609050304030312060f181d0f03040e09060f19 80
    0x1082d0448010f000301d03a56441f035030001e82d2010208505501442c2c00c0820036603c24000c41c0d0041b01e00501041010342000c0440004200d82103c082e4403022560340010350b1200382c000d031031040b4029114680c40d4070000700704802030034000c0160030f0b65124500b9000842c6c0c2e00003903140590391080c0703080803542d01038100e6580103008080c1314041842d8414100410041700140f2584200c0c4140032200c0070b48460418107191740070946100000c03c0d08240140104440c0b0440420410300903c0c003900890000d48900900141d0b10781d15a403c550294014040243c0600900c004da24480c6010402110740d03440042840c0143d00901d4890031113100407505001d099002500b40507040001d8035959580c0346070140001c0e07000010b0040841c2045000652000d050a44070220b400c8511150f160343c50100c4940000c0c82c00e0f000c3c00719100c880e44a03917103d02c2400c1108006101c2c5200c000c0d90780d54201020000622001003a10b20170743d0090b0100900f4030301d003202c4990071604050201b510f00030b40d910f1b0310000d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 483172275 1250 483171025 483171037
    0x5031f02040807171203040b01090b060904060914101511120c0601090b04050c0403060b012705010206090309060702150702060708091306030203030901110f0604061512170a05 77
    0x11510940f07501044201d800c800c0c04108261074400c807038007003510b0540001903001c01c4401030103011030100100310f0320005810542d00c296004220518040c00c1100007011144a500b1a0300d40b071b60340c3c02443c000d007404503140a400c5500207030b040d0541450682900c2390700000d0502d250410200025140303d48404114840020000c006543d442d007120629590b0740b000b09115121074642003084010300c5090911401740160740800d80c5614141c21501c5500140404090650400c805650065200c00c0c2201075980b1a9041c05981e0300030b1741c41c001c0024900040540080e9554204000040b100d9986208946c8003581c141d07600164050a181d05a803140203100c4013a42120f800240c084c00c200c05034000306100a01151840c0100075454911400c5034100c1c08020b40607401004603140da0360151724405059140241215499040c0003225800c044d015542112216100c0d500d4041e400a0350010201034003084000144480480e194074410f41c00b480c04900103200c0018580510500c00d0781240c075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 483173525 1250 483172275 483172289
    0x20d0b0109151406190c0203060907090c030506090103021203190201091a0402030d030209040e0f030d0b09220c05060c0723091f030f0c0501140405031f0204 69
    0x8500d607900e1400402921854110300704404611502140b00140201c42c008850400f9080506100c12100c1224003032841e000c01005000a005024005035400c00c03d4901c981c42c01c0000c0c1100d24580043d840c181c42c84d41f0301602c280741c146401c002241d00c480400c181141d070119102c4000000c02040281103200310003600e501030355200d01c0045196015040b07070500e1803103145070038070141e00760a1103100b1080944000350305410210203400d519201e5005002d803030500400000b040d01c4003800080c900858904051744542000c144a418034040388101030074400c05a400c0103152408144c0c141041401040014010940048103020700c100000300303401405000d442156a01e114540b040c3ea24100c1d4401e05202089401d00420304103400c2e03404c4e401001d0040c0c000d0241d601c4070810281004101da85045086075441310000224003120b02600c14607010741c1281c2032450412000515001d41e0000d0459002c00400080200341c800140365500c0e41e10000b0510000040440c41c81c0c00791003a030340010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 483174775 1250 483173525 483173543
    0x60f020c0303250801060f08061201091a0105040c08011a12070503190605010c14190305070c0b0301210317010906380f090a03080702030136020d 64
    0x400c1d100c0805440101900c203640120003c0300c4035510854200409004a400060314003005a8040d4000d404994020340300409503448441d071400e249003114a411820385a00045015511310071800e81c00c0e40e8050103090701c1c140a61901d003400a040d200062140184541c9141d0841c50110b0301d40007940c9000001c0741000e0042e0502d186c004181e5001540c1004c21a103a2a00d1311558107424481c0804640068640115000c0140c45803200c400c1c940100c0c01d01c0c1d005000395094100d003010200c0b044544a86c03907094560840741001d04e225019500500e0891034204010310401d41040b54031180000d0044914001c2da800d8071302110a286270b44403805501d41594001709010300160400800d4901c1d43e10340710b10980789040c60400e4800b0a00c0784003909825000034206210302d9038000c09626140c2e070245440d00c48100c0c041461401103034030a403804480402c0090842c50203016081caa5140b0130070720704485c4c1100c0309090f000c00860108211394040d0850080854840c0d10a01085c0d030780100081e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 483176025 1250 483174775 483174781
    0x105010b04030b070306030c121401020a020105010602070b040f120203030c010f02251203200715060e040c091503061407021204030308010e06040b040912030b010302070807060f020c0303 82
    0x248026070000e0100b00c038200740800010740c0152203031151100b01d0303400900d49215a0b14009042840f080c0f110001c2e140c1000d0ba41d65881d03840002d0000307102080e0341da8000a25585040e500034200182071700101c2c0c40e010100000c000b0382c4a62801841524100345880040341d07903d05c0000d03c1e5104d14024400c913942004450310b410503280d0701501c40030303812100810a034001391428140400d103500e001403041119824450000e44250701002104a80b5285041d41411010620305d040d005250f080300c6140e00351900208811581c010000104200f0442141f14200369540e04050304050061001c40b42e600c64407a145002411400001550084410003c100340b41c54240241001218448054440c4044822038000c0610848080325010b96441f400b99003400c07a82e030411000a00b05552058440804900a9881c5c1c801e00c60003602c035401c404142c0d400008081c09407070b00d0454107814940f05000342d01c0401d06c0502210a0150320041c0040e200301401c06050089c086d00d01e548903184070200070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 483177275 1250 483176025 483176039
    0xa020c0d09030b0a2d0209030f10060b090105090103090204060b0d020705010b0111250302090705030901061a0706200408030a0e030d05180d141006140a0e18010501 72
    0x1050007602c0c02202c0303c00090355070600c2401034561291404100c81140d81a200b03c1e00749859020f0307941d1a0411016141c01c0840c0c001910f0010200f00603805a041342841c0d0140c2c000300d224903002400811070540c01e002d001c3c1c002800c2800340d41d0344c441c1455101c0c4058000c558803079100ca009807a12001e8603864001c11f400081c0250440f04044905d0340c038040c0380c03030060b42c001e006101140e00010010440003040c1c04804012030701d021007510207030922850200c0140d81d103403072041c45004d50f9500e8984034607009181d41d094500701c0d4031010040c0c0da1011171081f460b400004032501e060304204007003404040b502007240c80c5001000e050308800300c080380110704144040010300c82056182d99846244111500300f503115200c250b0450003065040003914205080c2c4c04182d51180340041294601150984482d02110035000394005503800000c2140d8044459200b000d003c1c3c081d10060142150b01d0b4400b181800d079640c000c200f82541e862001840742404600c0e0500305190a0000348599651a05 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 483178525 1250 483177275 483177287
    0x207060216030f140307050303010b1903111905090604060c0213230c07022206080a02060a2f03210f0c030714030906010314030307090902030a020c0d 66
    0x401005004160074809402800c20041040e80c1d048a07007428401819030710102c04201001c20072419010071701c1103a004ca03605001560088c0741d1a0b6100340d940501004030500d00d500421544181407a00440080902d0303414180c1c1c0c0b29585020502d00003038504d2000f50781d54029034403440d90140c00050085000340d440b0540141061007540c3ca1071906030441c0419058445260101400c990842d0f00c1a403400540368a2681214240c1c482c103203402559004104940c40c01c010280300400380e0308044c11854180d2040400500401003c1c00154a04e60300140b0345201e0490004100860300c11b03102c01d450130b942000c401000156601303c010702c01c1c420700d0544a400407a010124000701410740388a0b80345c10700407030f40324852180082d45540c0c0ca0818031040f07130f040a04040c0030051030100800d03084050b60025409100d01c280203213140d41c590324204581a803035108002041e0070620034402c903241c201c100b4805581c01d00031701517165a615401300000340902c2e0010705c0ca51042e80070010409800070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 483179775 1250 483178525 483178529
    0x160905030601181d190204020d02030a050f06010309031b02120706030c200a0209041e0507031e121d04060e090601050312070f0c120305180306060f0f04090c060207 72
    0x22028862100b50018440594000b40200d413000d401003500c030054608402140c2440034030041005007018030389001d900072070300101c4500364a141d84205000100f1811040c0303d61180e07003460300740001c840310b030340040c111a8203807446000a90114850021580e401d070f943e2031a41000030881c0d40c3c5a40d60304000300644448034035000450000280e4507090000760305241c0703411030040d00134140041140e080c0b000c160301c0203109841c0c00c0000340707400030350f0581c15070720fa030705070307006500a1180780d00f142441d6102c40d100c8038070341540314201728400c000039004140c0b80018406600345200e0081d01c1d110b4203018030b4044178510350700600d040400b00d82c8403040601c150064001d24200c4550f0385e2030f03a0500d41d5444510b442002c1d1440d050040b14006031413900507480140c81120404601035407065980c0b0707a81c0911004501241000c07421114000c0198055180a0021002050182040c001080b07004102c0301c0c0080c01061000c039619020749403a08600360a03a88400f485112030350340c0c040292201d02074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 483181025 1250 483179775 483179819
    0xa180221040311060408030705180312180f1c0507030f061a0109030818030102070512040602060a060b09040507110d0f02070b1828030303060303080901050708160905030601 76
    0x80c000f6940e5010002511510407540500e0031803968440030400d95440c1c120740f0300000c480511100307400b07981d09d0a011a907800610012269245c1000d400d18040c1000ca50300904d00846c10300c1d0314103200356603140b00c00c80c4802e40c10702c0d441170019103810054181300964001030149a10841800100710099200003c0c1130107401e500110004488011a808010b910000d04080018844041c012501c14450003a40900a00041c0b030648156119401d1205807072040b00c0801000c2001c00186030140310b456030150815104014003420301c4540c8090340520310401e030099a0343c000190b607041c051074040080c0760840084030046039261a000303000702c013004400c500601495038002403c0000e10292030303410b5512401800013050140520038849082070407003c803495036620100742c0306c6440340007802540c025a40801c56909504001d00103920140c140c10150f89000c0400c035400f9400104071b41c1124003040f0941c1e00c456000e00450300545240c0095915000d0003000040c0c6117249030305012031001c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 483182275 1250 483181025 483181037
    0x70506151002010203040b07260115020f0a0c03030806010c1505091e1c05070c06030e06060105040303020d0f050405060d0e0f0a03020d270909030e0402090a1802210403 74
    0x74440124240c0c0000d0702c00800c418214000310b44c8082c00340c101d94100b11442d0031144400244409410140030082e803103a543c80805d000c028010580c10710180907030513002001021040300c0341d5110464540c66108c0a0100401200407492582c4241048a00243c0100c41c6a250403000306044009101c20798a008042c407400080d85c0251480c42030128817420310202501980c00c042904140c90512842d07074504010b000c0140e580014034403c400070184c0101e5800003140880056101e10303200c00a030030141480004c0c0320800c00a40e000035031100600c03143c0751600d002c03002e9030801d690602564100a5000c20b0114000e902c00002c0d901045043c16072000b161020041d551441da01d42c0b0710090b0140c0160005684100300c140180700307501342065041c0050314a02019510b5010402c00c80e00082c0e1071a850f00071040505030321141350694a07038212421890a079990700028043c0ea00382c132584080c00100c1503002c107002e01c1903064071003c2030101d0f0101002c007071480003014064411901100841c407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 483183525 1250 483182275 483182299
    0x120d02100506011d06040b070302060a05090c13020901030902040615021002090a0e04030e0a0e04120906120b010c0c0303051e0406090905130203010c020309130227030307050615 78
    0x40d40540d900820701a141c1c0c001122002c88540600e0607168a49908803408000c00181241c11400400301d0600903405000d42c0d0424103c0c210030f6400103000420385070b002c030b222400141e482071000d00d12941500401a9543c1e90400107034081d012201c000fa602510380200000d20300e04e1150140c02d07540503542039481088060001104038080e07081c0d99070704006030303500a1110980301520990094068100001c040d1410b40015074a01642e4004001540d840300c188400c100c2c00c100715012000940c02c015407c40d0400c0001080000f128042c0c0034016103c0580322680e03406954002412908105c1e4005500e44904000d03007039602c01084c8035407041100c0240c000280c80070701a41d0659203150348803000c2c10310301000e00003d071401500800b01c0a000309000c00040c1c2d400d202c2c8a00c51442030f0007954603a5400d0382001000c60549411510481c010031000c122140c19641c481c40072209a0740440480700004080381c5980525140240544038000600501c51000080074540c40c004551241100c0c2e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 483184775 1250 483183525 483183553
    0x10110a030302030a0e2a011403090c0a12050606042301260706141b0307050c10030c0c1506030c090e0706030c02031b1009030c02090a0b09040f050c120d02 68
    0x12102c107071b029400d0f40c81c622040320a445800405c0b122124145040e43c1090080003205940da401984c042a85034018913543c80241405071540005100303181107001600705603200d0a07244c1c203006140314484c61795101c110180c2c40d41c101d5100386680c0b8a220311001c0750386032040d00d9580004400c1e00b00c20780a82c03102c90521138a0004000f010b80c0c4941d07503030000d50005240204515048076021200040242e9101d0b1a00c21007000135089c40e40c052030040c070f03102e40d41c042800440600e426801003014204400c0e100b04e41d070462043c0d040f15070300940300000c048450b00c4c07000041c00c844d000103110141981340043c22004541040f1405044841030b10303056a5585000c4d000c8480855900d80503030400e0001d284005848001c5040c1514010b00f030b1401d202d1009500d904603003514000b1000701c2c0000440c1e800398200820291307801611404c0411803551a00e0010b0788008008100800c8507041224210400400f07022030610020090050f0286c03102c4d0f000102d0300e88002c901944010300c1580300440c460 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 483186025 1250 483184775 483184783
    0x70b121806091b0a05150a0f03180b0606090a0608090c180c1315180f08030f0c0a050a141c0509190b2101170c10110a030302030a0e 58
    0x1200404014040d08a035012201801040f0401490b40b145a80d0400a00d545617a00d4501503a220745800e40e50390f507103103e00504510b6020050780201450300c0316200502035441ca8410080d60010151390032a070302c42e400201203109240c1304503080381b46070900040d6142c005c10002e00450150040d2140503141a082c440e02488049040603d102d200d004078900100800c005d000440001c1c0c4502240b80d100d5410307410a00340d10502a0010714034561601901c400000c0700006040b058155101862171b00c1d110b00d0b52801160190038010800241546545c6002c000d003000303c590010585050140c1400c0ca05907007046072810860074000c08603604075140d41c01ca0203890582198403900e01b8094800103000c044640c2c061a00540d00c950300740818103100340c40c0034003854502e0245c84030788002418854540905c0c183c0c400b110301c1c40c00344540500c5103008144c1c280060410380e03440a8608000400b19509401c00c00780740c1042c002e40000c0700916515800440c030408040100707001000804540e203a031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 483187275 1250 483186025 483186031
    0x705090f1302010c030c0b01080c0f0a080d050f1c0902040509010506010804080903030d0f15050d0f29090a020a0602071809110a0612060e061f02070b121806 69
    0x44001c058829001907005082d5000203c2c040e01d441240e00b185561003450500080e000402c26a12100c0c00012a00d40140300402c032143c02e0b102d01d00d009191010082d52010008800000d0180100d142003802180406981d590702c2920b0036060401020102c0100070200024107900030342c10140010804a4140a12402483c0c1a9150702c032503035554507554815080145403590502081003010035402d02e034018262a0040841d00090b08001802c00708440011030b40000c1c0558030034880e03880420300601c0c09048181e04190211504070740b515204c50317803190780b444280c44040180d0034071000480c00076111503c2403081d940404440d44a030070990703a0310f1841c4200c0000900c1440d86280314505070f0000c0c0e03550b41c816585020303085005ca0000d1642c1c900d07508128009011048400b100000f81d000f4a0f005101d8240e83e0021401c101c80400d10713210710000e81c0001c08007112400d9150510070002e85000384126400a5100d62503d00c0d0b0030700008058a9140c0115120311403000103050204210740 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 483188525 1250 483187275 483187291
    0x1081b090f06010201110a110d110712020d0c03050331091505041d12040608070e030c0301020d2004080303040f110612010303030e0c010f140f07050705090f 69
    0x441030380ea812000780c1040e00248894119501c900c0b201542440c01e03005010b40e110507440e008012801070070050324110481d42c424080001d0102d40000905c1d0100e81c074030556101c45c0040c956401e0038000715904141c070300b900901e1155641e2000050200c04005003a40e80c5040e071729480d508406509102ea542da5030302007280015000542001004540d51044641c10503da64200880e0750b03035800241100c0040150b02d444500b803800f840b9071801c00f4041d21410f0030017a202e6a050608001d8020000540140800e0a00000c8151502c0d030b0b83c3c08000c09a10101c0c000c00966440300d2100c4460701811100d5480c804103015034403040d50701c0011405076410755240000450665889031110036080c00c5218007900d0f081c51280c524011a1901401802d4a030f141030441c42031540740d45001000c6071401c0f15000000d40260701c41d0456030380d101d1003085651520385070144046024140e20300581c81956039500c51000b000a00a0400c540801c1260807181c04561019240e03545124001103030314110742d01c1d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 483189775 1250 483188525 483188539
    0x30a0209060409020d021f11030a080f18060c25172803050403080a0b010207030201080a06120c0305060601020a0b01030807060603060c11010605011404090209030a02060f0301081b 79
    0x2507181e08050340b10341c00f618002012890100c001d0303000309824010142d051909038030344450045001e500a10100b414460f540020343c81c4c84880a8020a00301018014081c0e40b54100041080c01d50840c1d0341c2d031000c80c03045094803114180080c46054a41c400702c0f40c80e138041c40741007049000c89201d0001d41000364004815035403450703c80041c0c4030316901048041d0044603501c4402c040845a400100380d4802d0b403901c00048a0a090401170940000201032103010340c14401d041c145070740d0215000003180d9082c2402c2e2702d2929000400c0b00a82215002250174007003480c500310900c02d505e46100c00300c134012001e0f10042d460301b0004980300c260170540640a02110f03401040060020001821100d01403d0300061090312a0b948400fa030740c031003c02400145210280006800c0b0a104900c001c01090034902d85110300c10100801c6402980b05041001707a01040c5401962018007140f19200d5005240c00e039a002d104c04010320701d41007801107142d45e10900e07212030500d0409080b00b11074000020300038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 483191025 1250 483189775 483189781
    0x20705071206021e07021912230111071b06050a110307081b010c030c0c061808030c030f0601050a0e040e0c1201091a0621031e0414030a0209 62
    0x50454001c05a0100c9102e542004503103211200300e0300c40d0100c0c00c4a1034080e50303280041d00421010800c40000c54510804149081205040825a0107441a4007440e2002054460381845e284a035104240d00d0640d402e0046059503a0380420080484d20b1045040741c0c005041000c00e84006001406003102048081014002080c000d440c2c0504540c3d0440c21030740340203d50390b50034150b60020109044d010403407030703a260101c800070b01642c1407020051804000b4040c00c810010030380c010a10b00a00710b10f45d94604240c0811a030344001c0b0705103420142d0390755213040c80d400340803180d40201c0b186508544140003007019503108070104c1c0d0f0740c0001c55503140c030105602d4080000400305d00b01d2480d003030303c20158103c100d41c0310388580349028281c400000451500b20f06100e40d408244d42d0540894410360810030070241c0e1900d10140281280710b01d01b100a507100c600d05440c1d8401d201407000c400401d48103d0480c404100c0050046d01d030101e90281002d16480c041c5076683e0002440258485d40c06800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 483192275 1250 483191025 483191039
    0xf04080304050a052b08100626010b0703110601060909020315040f0605040b03010b06030c07080c03030408071703160e040f020c01060302091b09010c02060f0c0604031202070507 78
    0x15681142c0100151050000b9698500f13180c1503031883e4100c0040003a2201c1465903405c68680d008451060902d19800d2130241010b0102000a000d420103000103c200990320040384884030745104408580c0b1189561620803841030780d00200d000f240092019126081150b00129805041340c44680b501100b040c2031101050194000411500580e0300e60321a0100365511405aa09013805001d80082d131141040140003e0b5030303101e0062406031307042c4212492103441d0713281141d5100b645c01c800c145d2101c09a18001d1301d14800c0c040e8804062001000748824040350000800509201d01d61000075040125001100d0380022901d00f09000c003124620200d181c0103c4e4910903010004000040c110314102024040382c11519880380c00760341d1840c090045040c0f101d891a04a0300381807401c213032160b440b2401d0300d4610030706000c0d50400c040e40b6801001c41d01c44c1415140c0e040c2c081c04110707444038a041d80280d1ba40b48202d405400282d07800c0b0b01c0301050079041c0708a80240b0f4010018083d00c40c102130b9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 483193525 1250 483192275 483192277
    0x302060f070c120c0203070902040605040302100c08041404050615270d0302010608210406030b0d0c03050307060f0c0504210501020a0f0f090e060f0a080111210f0408 73
    0x3000c0244a884101c0b400041c00a40810100e00000c0d00d41041c0066240141841c01d0030a8100c04021807041009001440e0050151400c0300e60403140361803540d2900da401c4815030700c00c0c900142084000b0401207485400c0d01141681c2c1309081d20104200d03070343c1d641040f10b042103403a9010100d00003005103100041c40c41300b1044120740c10400118913002110003091000e1401c000607001030f551000c2c00c0c0004082805852140105544628031942c0b00c002d5015591044d44202001d2554070b120120035074668042c0b159911b80c0200f101103040d550390074503035240d51021a003114043d03d4101091103003d07481c4600b4207440007560754a8117190410103600140300c0d2601c2c11003109010428064000b8030240010411b540c25541c0d0500140c1d00c00d440500000020132074001800580d40701030000754035109840b58040011a0003026040045010039481c01075904405c5013075091030500c034800490180107010260241002030728035240c051161303000710410340321082001c4000000c1004252110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 483194775 1250 483193525 483193531
    0x601030f060b040617030c0708012d1404140606030a080301091a10030212011505030703020a110a0308010f12080d0b03031201140a05010305070e011101110c07210302060f 75
    0x54000100300b51200703101c001c00c010171402001c00750710000d9203060b40075051103444000c0008078001d0240a4a00381c8084014690048818112100c100c200391124a1900240002c19601600189900b454240441800b80d0403511803054403805000c80c0711803e0008032a9000b5400a48103411030f420070400c9006000842911800c08000d1451601213030f44180500359009141c0e100180d507501c81044201500764164041c130500025804080e45260b0810102c0e50b11040c6441c0040c1d80e85151003044c1d403011445044013005104d1031442400f01500700050078143e402005500294954582440480401c01040100002411302c40d10807422103903000300b109408020b00392820056080c00000e40c2c1c2d4400d900c641040c09200924140508065004e00040d000a203000d0100d0b1414410140c05000c109168504000d0362020900c1a82d401b0740c009520450b82c820b04542c2c1e266501c521a9942245018a84510142c500d400d840507041c6650b50010551580150505030785148503221403c03002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 483196025 1250 483194775 483194779
    0x108071704201c020f06030c0a030203070c1a0106180f051201060b070f0b0601050a32040303051905040503060a020a090506190311180909031e0d0c020601030f060b 72
    0x407040004142c0d0f110304000c4540b0040701d1040500c0f24031401041420250515040c0c0555820400e0150f810b44c5c2e8411203107a42d02c00d08015070750303440b400d000711846040381030094180f84004042a1a0700e50030110036040303030010b03521b142c13840b0440c00c1d8042c25802e040c8901182d000ea80380f010072143c100000c42c844c409000c4400000e000d60b81307941e02501030740301c0c210468140030350b40c0098003000050400c0a80121081c40c059081104000000d400000b4050906060400090b500b03107900100103189103042c4100010b00b80c035582d403032401500d940c004034800c3c80026540b100c1d0940c01403007001030b0303000c40d42c0c000d0040000f80c4030300b000c0500a501c00402d5100300711107203401080e1610b4540080442084405011240780e56a0340014101d0b843d0350071095141d4003c00c01012101507814911403035078022121903006448800c84a4514401c01031817000c00c100d4031200c091803c0c020720140c03280030440b0b4000d0107000480941240c0794003003400018849080070f80d10101003815903000d503a501c000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 483197275 1250 483196025 483196073
    0x705030312190501030f0303141302040b0f03010f0e0105010e07140a1b0809010f11100b01022d061612050c22060e0a0302031213030615050108071704 66
    0x1400082c44143d035400d81094504980310032440d01019458071948004444400c01c0007801e090003008845941103c801c080e00c629211510719000ea134500b4511040500020300802c000c00442d002078001d807501c01080c0015529000001950716001d41c409842030041c0e82c1c4560580403200b02e9142d00d6001210100100410b0340800031590400c1100a0311090141e544c158840041c10b00050803000340c100060100314843c41c807004940307000120748161400c3d030703100400c0508500340101d2500d0b600f00600901c1c1452080c1880030395504941e6000d030021847c090381c00d50365910700407c0840071101410000580e038410041c190341714550105822111022109242c0440040400899031456100c82c0801c603001008012a582180c0c200420910a49020395001d1954000a03202c0c203d0349984000301100241c0c1ca13600c1101c0913040006158800c0d82085540c14141407a19060807a003d001c1c041503000002c03034640c500a0308400c1d0403250ba420040d0803981d41d5626851a5405130004444500f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 483198525 1250 483197275 483197311
    0x503162009060904290a02040f060201020913110d02040b1b030c07030b150d03020105070f0c0206090402070614070c2904030f05042d0501110a030804020d06050403200705030312 78
    0x181190b0b561b0251314040000350300d072401c0004001c40700380e0342c6d4001e80075a81b040010030074a032078a200601202c801064005a00202e03a040030545100d000013a03039481d4400140803680f0243e1300c010f40500140790302001c18546c01c00305004c0e0f80c0d11542c01074040702d0744809010000070f040044201d501401c3c0b52025031100c20840f012906400c2c81e80382c1203000d03075120010041c07035507405803500d030a001c40c51610400007841600400e000c0e00c20b8001c0c1600464002a2420a000e40360b0003c40c048031052800c2e520500d01068000c10344080d82d80100d500d0300b1074a000d02240c0a0b091809407c4141c103207520300301c54407159000e80f41488640ca00f80c040c40f500f0b0100140801d0708501550340081100340a1000b0040040c03040c8026000790440d6050062100c504080b0240000d4042d0740d0381c0c3d02d420004200e8913103000190500d074041100501c0f29051404004c1059400796003880080c184000c155150710490301e0f02c548134041800f480360035070701c203100b24a070f03054180701105c1d04486d030006030a81e642 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 483199775 1250 483198525 483198593
    0x501080103110a0e09031b0607090b0c1e071418060607020d020901080d081021060b0303030a0b0108181f0f060305030304050d0315060c0503162009060904 68
    0x304c000c490381d10b60b5400101c1c40f6181c000ca09480351a04070060009403019140c48880070784020124003a8580700040411044150202007090301c000d1000ca03010120011424a401030303441ea0b240c001c0d40001c07042855101205d0421140c00700c0c17607480b600d40303c017400d603255070900c400343d00180030aa9000c0700d002e0707942c000741c0c44c4c07501784901074a4a0009007490144d550400342c10000e003e0500303c0560041e103000c20a00701c4580d081c040b40c01e00244003d9030744256080c148081c0140c6503000c0e906000000030f1156801256005550000d02a21920629620302d8900a9592982d41c160b039070359000510503a0b0b410fa5a043c00549140c108800000c0201959002da011509543c00c110b0341d603031000003030009208082050386040341c0b00d0700e81400f40345030204030310f1050f400610420003880a00280041082824415904002500168003071322000a0411301d040c48806450031050201401c0102c001d401c3c521045481a070000c2c3c440f40c02900e803580c0c0d0400050004c96501c1070000086901c41e210 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 483201025 1250 483199775 483199799
    0x103020a02030d060e0a0b0111030901200105010603050a0e19060b0d0813051503040c030308070921030f03060b030c070c050a0303030f1b021005040804090903110111040501080103110a 81
    0x2d00622017044031103140c41c00e50751044590307820703100f414800c8030000d070480b2042c00021102a1002885c1c01848100704030f500188861000c540c12a595007801c001040040d45a40100d00c6030078603000c18001030803400c20140c0c403034042100e0301038091008000f540c042030040c1c204c0a444040940840110855030b07d44010300d070444c0c5906440300b2602c003806c001c58903201c500550b41c03004800302c0e24610305041e035400034000702500c0010301b4040c03100002141c060041c100840142003054064042066119110a070001014000c5001c04e07004070251a00078030070322440d4240d9400f0b1004a107941c0f18a03131044c44582141c441200c0407611040041110f440d0103c1d42001103110783c401085141d6400c0c1c1c0719003601d40c076504002c10303186c003c058014075950024400d044a5003000d0001803a80b0389003040103403131186421003190141800204402c143d4424880400050000c000700044010003440d0030840c03060303102d000c1c0002d400c08011302c00b084210311858030410008042884042e43c560741c032818 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 483202275 1250 483201025 483201029
    0x1403030a0f2c090a060806040f030e090a09021201060b040b16021f080a090803130203010f11070312020f0403080c1009030306050f03060702031918080618030702030c0103020a02030d06 81
    0x280c09109001c00c02030400c0d4040f69046140340b071060013400e007004035541d69014002c002500f1401c00316407100515016562021100c880a400c1c500240781c20340c00038001d0101e500e4120f0141c4208801906c5030311040c86800d0aa80e040f00c2004d26141c90601c45201c1038020100740c51605402121800050341d80305104200c00300700611f403210a400701c060280400d03e004201c0c0c08a1030504126000207080740c01181d6120b0740280041505840314000b00340140480e19031004144c0c0780c449402c40c0340700020f02521242e0f219503207070740384106000303941402c0e03014203902c034a03d1200c140300a000191040014211a2507076200301d500340d0701c100c1e0003503094404646054010a0741d81c00f051107a0b0818241201140c0350030f400a242c941001000203540348101a0659040c25058068000c0f0030305c21203a0007508087d40080c50301154941c0381003629070b07600f51110020414801e1007001600400300a48102c0d07900100600303402e904120042d0040e42c800340780c04045001c10041c0400d030201c036100c0c6c100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 483203525 1250 483202275 483202337
    0x40e150103031e030c0e0603331011070b0a0c150504120c0b1f05040e062a070b0a18140d0905130f270c1403030a0f 51
    0x110550f001ea2003008900605044109801c2110412085030440191104030740140d803826921364860080031030340741e042c00e141d01514040500f1800e03481850420030310888002c42d402410000328110039554014041c0b00780c81c0340d0300000020450031902c84041c1071580001d0a0902210b22581d41d1010101c401e09101c0001c543d44d10240001d000c17440756840c079044921b042c0552940c046888030512440001c00e048040c4890601c0c651020340c0b450313018002801c000d0000e00c05110100d40301516100308407041448110385000402c4000700141c0c06022030901c040013603207400010380300c06d01915001048100b034592641c03d5012200310210519142038080c0d0a048200e001d005426418001103c40c0c15007009600041409140e89041143c01d8005612100003090005000107038054002c1e0b100014601040c0a503080c203800040c80b4030400c1c10b00c2952407140150300c8038001c100d01c5414200f400c1c6c00d0f0340240001c42c40e090046214965a65103400d2054004030340b00079001c00c084d01014401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 483204775 1250 483203525 483203537
    0x71a010609210206090303191248030204031109061503060a121a07090503072306040b030a0b03010501031a151003060e060a120305300105090609090309040e15010303 73
    0xd19644105d0608030300100391002e00090720003a0070442c0d4094002c03c013a448070b055194240442d2224103810a5102400d12801c40e6000690ac0103402900644020b80d03001c0001c00740b0344411714000d1001c510440d001082c940200c24407025190076900004c00864002034802c078085802d03003001840041841c0b1503290120b618000212402081401506240901594090a1225950115040040e01d400d82141168074a80d82c00501550f1801f080c4140c01101c00200407400c650303001d00035031103051f01d10002e0040c004a070013410700f01d0340c0074030002d0415494429014181d6148200c040d4002003012180254690301400145032010344103a0b0002003540c540040004155864840c0c0c0d00c120b0072140001c20a00e00141500c01c1c0c0000c010003002c100c2c00140c403c60010342415855403030924400d59803140c0c84210441c82031000700380a0648105030050009842d440c003007010754403402d00b8101440c10310000c602400050705905d609403016005002c03d082ca4215001c140d01d0007180a03583d16 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 483206025 1250 483204775 483204817
    0x10315150e1504050103050c060715020a020d0912020102030a030b0409021810050301110301060c0302100c17010503190b13020306040c03021c080f090105070206071a010609210206090303 82
    0x2ca07140c0c6000d82e0680c0514103203001040401c0001c02e40600901c4280c0d405a5101c900340f4120384000c05140079161514408101c261507158000b0728841c1640d41d546075100c115448444c07119910410100080c01a881000305400c0301c0d00c42d400c013000818010300003152644503540080c01550805000d00c103015030103c01c01001000c0c406075000201429002004107126807810a80c441c4014001c0701d00b0b03c06481e01c00002c05108000440500d01464810002805070030380090041c9141240d12048100a000125851901080240c07c0f030059440d80300a03054159a40340000380010a00c140004000d5040f501680707041c00900d06c280d11449a400c1c080d42588108004980c12404554010180c2504000003c0442048480003940820001d03180d140c0d040048400c1d01c52040f00a40002c0c0200b500010480003140401e050743d440c102c2d180150f030301c404084400034028441d19150010341c2c07102c4442c0718540483d086000340041d100c18034041281c00841c0c51a8020765502e054104200b4034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 483207275 1250 483206025 483206041
    0x10150c021c020103152603090a0f0509011d0a0c050d061707060f050f1608040308071101030519050c130b120c0a050304020918010c1205060a0608010315150e 69
    0x5070b0711510100d1041511514105070400c5059002d60b86146e8213001e60110f0b03c0b0705d090f01002a2161284000c0c125040103880310000700030959280f20f981d00a40700e000011030840c80812900300c0040070980712203d56581c181d018000340c45001401024880c0401c209181101a4001e25000d40740034000100d100352840c80413498081c550740040d0410011030b0500c00d016502c081240d41c10055103801580316180c10307001b2a11010303940c000400c03480d000074000080201c1c0e54007500c80d0038001d51042080d4151070f0019030030340c1e900701c40c8000201700030484c010040050b98032a60f00030441c1c1841c0740c1440d00c04801050301580c2070b040b0822003032012501c90031070300e88174540c154059481c020341e50504050b0140503116000150000384240d2344a800900100b0304003140068100700c202c0244140640c540e030117803080e601400070001590400d400240942015001d8034103c03044e90b40c401c030b0580c1ca10703145c211800314900c015041c1c0540301c04146c81600c00426a4401074034840300c00c040181400d041d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 483208525 1250 483207275 483207281
    0x3060f050a0e13050f0303040b090d030c0207090c03060b2101080c130207031115010939020f011a090f1302010509030c030304080a02100810150c021c020103 69
    0x200280c840c0c10009070500c00b9500c0c88481070b41159861034030480e481074a00e0110b04041c0400342d4a0803511020003007006100300c1b551080e0003030b42103a040e620b00c400c5070403088065400f0b40c900500544d0000d0703800c1000789684d81c40b0510078009450001646030725415003c616a10a00641c42d044984100e4404100d24601c2d04d1401016007000400e0060002e40100b44010341c41402d1400b500d5012912005050082c9606072003000550141c4403030392a01440341174174040a010380404189090404040144991400e1841522030621000090990b11440000400c5c0d204503100714010703a0341e0151140001d001ea1002e4031906180c140a0040e06400c0c040c11140c02481c0d462565a80030521a080d81e040d603404420039020b1800c1c03559003010f0030109140690401c22103805200000e400034110300003281c10fa440c18400c89060303580c0011a4002c480b40c0700181c6280280c02c034191030030880031150110030185440d050030700032460b000c00c4c1c0005103c00041c403110800d103407070b01c00c4146c05c640e4584 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 483209775 1250 483208525 483208529
    0x2120303100608091213050607060e1903080c0d060803070506011a03060f01030e1e0c0909030a0818071a0307020106150c0f0204021207051b01020414010807030e01020a03060f 77
    0x103d0100e0041c0340c82101c1ca035032660b031040c03c0d400d00710f0700140f454920780b1040c4540300584000b4003050f694001714a02040100000c0800320b100340184406c8564020340c03421000c0b074042d0503584442c100c2d12034030200342449d8016041401040d0342c6100010381200c00340080c00b01707a40101c0151007075600d08460079850445000c03000e90100e80030410003810b503031109075012403400e0030700c1d0000e05c02c0010344a0320f00d4600050a460b40d14001c0d100034130b03080c00d00014015000c600c103072119280382e203d0400b1190b83e4041c10040320049800300002131b00c0300300059038010400e42400300711840b959403903044401c1d448030b80c1004039000030004100500182c09015403001808100c2d410018103004c10710083c130014000000401030001442e15001350340d55074042d12450103188130f02080508240001402551203000c040458000350000d0b0300d5008418429102102c20540400d00f408005000469800600501c80310038103980760021260401c003403014040b47c2d4156180050414201242028850044c2d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 483211025 1250 483209775 483209777
    0x50d05030c070504140f0720010905010f060f030b19020a0f08090f060a0e033a110403030e1c0c050f0409111c1401050123030c10020703021203031006 66
    0x141401907402d400b003450f10362201c0c0000b42905692522a006c0ba142c40c3d08d1340e0038030000e0b180380c1001c4540042c19401481000e10505c020400c1101512005080ea00365105449180350040070401c0890901c1d940385038841c030780025108070f1802580e0100100e810196459000810450b036403820540c05c80e0491f40c0104010008000c40034a03c04955a601001010f4240f00c41d116007001c0c20078a420000d403000b03c19506c074030710b070800d1704994408041d850780800d41c20500b9070108540c4e6100d034984184040f540a5540e503a00e040c1c19901c054501c01c0580001c02e4001684000c228035200141306040305141c451034010b40d04c28a440c0401048141c40036942c0d119500c2c29080e0000030f03041c0100140c0c520000e032500e40801503200c0c0138a0021191040c05050b010301d2803a0100484019440b05041e2a480003500e080120404103941e481021918502d405a2200c0c0d8040903621b400b070250103078060a4030449214a071281d001c40c1246918441b44d40d5241c0c40403013400203401002c07400802514071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 483212275 1250 483211025 483211031
    0xd090f0b030f0c09040612080a0e010807170717100303020106052704050a0c09141003050a0f1e050606030105060d0b070c06151205070803090f0f0307050d05030c070504 74
    0xc2808060803100010302004150b4030001001c03082902c0e1038005d13600421003504040347c0d0150320b08080045600c103c01d40b80003c1c040c0c0d035202c1800e45c010345c0307114007800b081d650b400c41e4046c0070900012400c0b4040c1c00381092019510307580044510894441e4891a410003060300294518034001e030954110f500b002e84140f40c0404410300302070098001c24092012203854603101d44035820940e042c04c0c3c00f0400601000c1d103100011445c010142c10050100e1050300503990142d035150021402181c0740d000003020768108060140100381808080c0008074080c40c00e68440e0421009000d138001040303003041b1111b400000c01c1140301d14080c82110790040c4180c0d600c40341503020f0703510300c0100c0f10014020000c1c008211800001d02c10291f001400100380c3d10301007846103490b500402054000c09408880c40c0c480c00c40003164454000c03040d501010b0000d8501c5070a00b00f218104165a92080c0c41d90f41c151092280000e15540d6118200c05098010000307160342d41c114040050500e283c1d07800807030003142 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 483213525 1250 483212275 483212281
    0x7060503070c08130306021b0708160b0919060e18040506060d0533061e0123030a02041e0b0a1d181017030301120f050d090f0b03 57
    0x24001044080c003d51003000300d5500c88100000d1509880681c0018001e14408a8802e01d00c4d84031995500c00320001104a40050366100709181c1c4d2107a842c4024000c08a106804014510900c80a803071000030003041c610a150a101c1e1401903a941d540c80b5400203001c0400030500c5040a0640b8041034441c01428200c0b03203815102c160303541c3e00242c2510300a100e841c0d400d1042c03080a112100000c10041511400c7c4048401141c000c09001410100c0c0c203c440c00c04603501c0c0c503001818900d00e4242e4039100a11075a0780d801541c61281c1d040b00d451907a1842010040d21102000c0103600c512940780b001a01e903410081c100c10740ca010342a1102c0080074800e0706004600a040c00d5485441e190b150003816a085a14103011007038012000d20b4004400d4030f81c6811400c0300c144080d21800e03001d032041c042c169541003c0489100202c00054180d003003000140600030715180141591030013241c6d07543c810441c40e641c0900d0101801e1900000030400700007801207208005036403005203850b4004500750301f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 483214775 1250 483213525 483213527
    0x6050703180c050f03030d2405062a0a0b01090204080105091504111804060516030b01170c040b040902071b0e0a150b0406050309060a0e1207060b12010209030706050307 74
    0x50398003d080c411003001030000090f907020003c031354111400000a0107000402041808088080000c01d0125503c602c404030f840d04101c8251550a041c2003140e0151940c1199a030818905003907148900e4090340100e0b50210b9000070501d40241040d54005036118540402036003150320160142c5400e8012401c00d080f5014100c0b01c40e0703041500030000d5004812200d002407403c1c01d80c903c00c00800c02c5410200b00910441e940f209210300144244140c0b451080032088084404c10740c05580864024910030440d41c1c2d400a189038405101815245007a0b11940d40c0c041a410650109a402d60002070202c1088481d030400d54803940169100b0b20742c40c0c00c01c40810000403000f024015201c0d9650068203601d494507034898020030740c4121030340e078607a1680d030020400e5004072400102842680d012230450b00403031260380c41a4402801904001001c1400280e466001d82002d4916684400d24442c0070350b20400a040000304540006940d819140c0c103060400800da4050000e010091042100031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 483216025 1250 483214775 483214793
    0xf01051608040605070c0f061a011b03050903120c1e01020f160303060b180103050c1204120e0a0b0903100c0f051c091a01140f10020a0f0605070318 65
    0x10b940990046819645c0d100200c031001300014020b06164004a882410b00c04164040c0c0740302c0072800a040380c8150740b8001990269100d142195805801c0071111001ca44180090901c0340001000c0e070b49218000c0500c20030b84c0d0015902c1001c00c0d00104131034603031166502c078649030a11030300f4001c0d820410b82101c8816140182000002c521301605010703420544a90701c60720142a10a50481e120b030140d0307620010014448084a01107480c3c000482c4072943c41005880b040352004c0c0038204690f42e90356600040c40b11540051003400b000408482440d900c0403140d402810120755825210841013040628008900504000c43c92400102103001944103d442820a01ea428100d6549510015540c584d15400500c00765030b515011244041010000207041d80d15080c040e07003185641c82d0f2900003201c02603405841e601c982e2003135a4071418180b80d031b52302e114031030f160059038031a49980d2641c4c0030484003820226582a9500b00304850a41c15200b84040b080d0040746c002c00d83c486517030300c1c0215 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 483217275 1250 483216025 483216031
    0x60a050c04030b0717040b090d05190e010c080a03050a0b0603090c0f010c1b03110603070801210506090a03031a06031f0b0c070e0a020a0c020f04021b0f01051608 71
    0x221a800a000440344e900449218204802d02d214040f00c9160609141084c1101030310421201d00803130320f200d1101e074030440c161075883c48a00c441402c004d6003000d00341d5022a41480d041d050020482040d400f0618190142141c1d42c056140460302c5d2800c0501c150883e0b100e03100c0303103200b04030607c144a980880010401d460000544003010003d8030440140c4404c412020001d00d5950031005000007429403000d50340c00c82c0e204408001c40c4002a104008560204071510000100714000401008107611007800081f8500d481100e80880c0d282c40783c5003007102c200d40710500c0da80b1580003801019454032407403c1c214540c4211401c0000f100001640611000d419069503606903860120101039031b0040704014907400030150b5031084007249041d111321903407150507443d01d08040043ca403005180222400c100f059611100c0c8507449608200032070403400d41c0650006da00f07100c800d200c044004118080d038030100b0000e1100810b441181c90944074020031410395170b11114010701049070029022a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 483218525 1250 483217275 483217283
    0x10060e1e0a090204240f05030105070512040809130b09010509070f0c0c12050f1b06090d050a020901090f0f0e1e0a080403030f080907140d050a061d060a050c0403 71
    0x40c0750302041c00010041c00f01750042d4502121060240140c0301001000e00040310400c41503401d50903580c0c02054201c600840e00340010032800c0200e100e0925000700025030051007248082e05203690741008c00c0114660441c90303001d255403486140c01d28906105214014070b0300301e810302000d00d04030a000300780c03400c070100c1c2c0818040d083c850f60040040c00103200002d0125404520000d0301282066680d940084085940078015500021008100c542c2c0d400d14000c400381c40c4910f04800e10041c03080b100c0c50b1440a403805c0c05100c400100582e194040d00d8002c01c8288004100d4944450180c0b04841181d01c903400040d14141403070000140115009030f11407012540f2040c0c00301c20140b03090500c2d40028005005081c000b801004060700000916021b80103692a0a00796407622041a5034400d540607c2e410f0110b40702070105c803480c000d020280224810350640365100701940e02e19003036a000540011011030000ca915180100401002c0d07072042400c1000c2c0300340d042400c0381540c10701c11804098 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 483219775 1250 483218525 483218531
    0xd030f050f04030614191406010e030f2a090907140d0c030614010e0712020307030b060424021f0216050d0c050106082a0102070810060e1e0a 62
    0x41c00807104070301914015a0051070510030a001504036200303894088602c00340300b9200511240c510a094072400c030300d80907071520701c12250b100c40c001034a040b0050140158980b0801d1030444c025501030040c1044160315a2003070043c01810002036000102c1071504134000c00f0400104507003c100040c0d09011211500811101001c0d481e000c601110441000a03048a0300002d0000402410794480500c21044041c4110035076280d4910000c886019110f040c001825001c11a00300340341f5600850304a4003d05002450034680400b1512a0700903511550180090740c3e50702440da062280d5080d04490f5030701c00344c14060711000395402000203404401140301c0d404550440801c0701d00e1980c05456422000b00c1d050000e00c0e0304010100000360400304c0b0382d5400c12030001045000041c21800c1174480e0b01003900c10b810445d01c04440449145c0e07202c0e04602c0380c0340c0000ba4844050100c585030700c0d20583d0105800742004602c0002e40c0000e0a04400001d03145007480346001c07107007850b0307410460000c004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 483221025 1250 483219775 483219787
    0x50705060d1107030c0605010b1812010f0c2006061c0302012705070e0c090904020a1d010f0b0f040e040303090204150504140f070c03140d0204140d030f05 68
    0x1d402014001a900c1011400150b401c0a05810111132005a8800c0c10140030507a210761041120340900a2045241d420800540c8003600d8402c4200500c40f04520000401c43c1c0040b072880b055035003070070500020a070480101e000c51205011a0800c2e001d800b00108514204000803492002400f2242045a9001c4816008041c0b003900070303021101d0005404418080311022012550903c4031040350b851040200008504200f20070b080e21607000240c9841c00c05603200240400b80704020400c90b80811040780200e50409064800b81c10048400031504696050183e0340f02c80b031206400c65800c3e88028401d00300c0c104088411070702650a0300710801d0840d180c5103070540290100c0d840095001d81404465006442c01c18a190103c0fa422203050000d80405c15034480d10710000d44030304940c0c0c8a5040082d070001d0007060704090303480c07080c41c01107881302660300b80a1481d0040300e400c0d000d1a400003404c100100a84400e000d4040f4100c038500310383c0889135009407043c010607514005001c8081030b4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 483222275 1250 483221025 483221047
    0x31003030807050d020a03050612070806070507050111030f06010810050d2003100b0a1d16021504080301170d0801062709050f070c0c09020306060d020a0207180905070506 75
    0x1655009076130340300255115000c528006c1d02500003190680c0c0100080c0b00548550b0310300044200490f14414050207094581c10022a000d80c80080c0c162000e640b42c0d02c05114244112008521038100b0030658906030030a04001400b4000180c1038403c800c80201e010300060382ea038400a00381d241d10248904652a117940340140103401e00547c03540c14010b43c1400410b4840e250050200312104843c40e19411340ca4404030141c80d1031595103070520f003002034002207064000542840d4801300c80c0c0100c4072823880100600d80d2504044508a4a410002c00100000c0242444001d460880b000c040d000300802d810004095038414860a0108402c288001e00b19804c42c4052440468800f441000c103240c6034140750700a89000c1e1703082d84d1007011610014500521031240c0d007148560000d002040286800070100294101070803060348158200b14440c0030319545d00c01805600fa50b40c0103019500c2c5011241b09038030031000441003041c2d007020040e2002500100d400c00686000315680d41c1c5461510071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 483223525 1250 483222275 483222277
    0x10f0905030604110a080d050d0209061218100908070209060a081006030507090b03070e09100519060503190b1803040303110601060201020f07031b021e01030e0303100303080705 78
    0x4426070701401103005020030b0012528010000c0e0506407011640e650b992111389986e03070030b1014400e0015105200549640c43c0980092044c40c900030728050814441000e007110161050352904150000070840b0074051505001070500340c020f2444c20080d891240d110b040051160b454001d1081c1c1b1400c00041d81030b51060603900c0585450030494580044c02c4900c4002041d90b4041501c40b03105842000444003200c0c02413001c05000980035003802490181781140712100035121414a0264450010303404000c2e10034148190030110b0342c1c1c105640790304020001c80d109034011078000d07000f90040e0b0110300c03c04002c070300c50b080d13000e401c1c601c90390344502c000d90002003031511858813800001400010f0542c401a00a900880001a039030f099a039154240c2c200d01c261301006040700424401d0340d001ca80183c229000020942c03070301e0441402c580c0c1c0020443c0b41d03080031070342d0001d0030001d200341c0369680351058215503241d8074000c51440c1015220300307039010355070b1000808002e5414001042d41b4803580c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 483224775 1250 483223525 483223529
    0x510030606230f030703080d110a0c15090c14010201020706020307020f070e090a080c1c021c030b0d020d1704060e0f090708070503070c020603010b0901030501080604050309010f09 79
    0x180007041000d850301070444504201034080b10070a500444a14880d141030a03580c80100002002461003a01d0340c7c0d81c00310142c002100c0a605269900c02c8030714105004070040c4a440740ca03a44400c1031001e289820324281c20b1044e4515902442c01c030840300080c191540050540300740c00000900e1001040040b806403080f003200608060001c014070680540001d608a90b00d80c003041914429901d80c0300d00e41c104c5c80304480c00d00561340138100200c046001c1e9001848a2207060080c1c42002002a0710300328070915601902c1c1c0142c1c0030503043d02c58041545501580d2a0300d0b85401d1011210040000d0744024050801070300c50600c04480c1c404000d081d504034546000154a60340c2c8855982c2c0024000c07650780c100075409405c00f24180c400320300c0c3c0180c10520a1200b9110301100b91240e01c0c003114a900700520090620010a04071000359540d10080c44c001c00c0003a14182c0d03541c0fa8400010140e074010790100c1da0320341c0050b040c04001400482501c0d807080c820b103000c1c85242c0403c1c1c82211429965 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 483226025 1250 483224775 483224783
    0x1103090d0b060405060108090a02010309060b100206180f0a140a0b01030b091c0c2004020d06050f030d050d020a0e090f0f06060310030213110c0703050d0903030909051003 75
    0x416191801c1101100c00180b140c1c00458040005590300f00055801781d0048565007a1134210954440056000e03500c480c0085000d80c00c0029804003100111300461500401840960700810810044d0080150010000c0051a0140c8409403c80f02c085550742040c4100610603051885540c550020800440e4403040d0840098041e5581da800d041121290965820f00c441c003411402d0403450200080c0a40074040365601c200f040041e688800d90007281026080d248110907003403488132681c1741d001410004021507030000d10540f03080300b041650300c0e030b461200d0b000340c020344a8118080c1c1c1142c140d0b441c0301150440565260304194040f1001440d480020b41e10500000500285580e00c602c1c031481146036122002c03090300d842040120b50b00003224009400c4150b140c040c030050901d62241c10b00d2030304810000c1015031700f03124180e0481e0032503440441240d00c808420414848104443c184a11090400111085c21520010a82c49a03406000c0c01c061312100466018064210044011500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 483227275 1250 483226025 483226039
    0xc051b012f190b010902090904080a0201060302091f1202220207170c06330609090a050405071d07110a020307080102091206130b0606220501090602010c0f110309 71
    0x140c210124200c10448140c036500da0250000c05d0819081c42256102d03840184110031581d91036442851a62140340715000319501d03041c00100507218400160300428945080304590f80740a444070510348042d41c05a881c1e43c1d2081c0c4101e01503120712450100c900c08001da44100c07110400360b48030183c403502c1d0008200702c7c41c507002c03081c4000002c8007030b0035055200e4065407940d031a444c55001d950b0100c20814466200c0440ca041841c0341090039407880c00501600c0c3c5400c0c05008000140900e4088615007519911801044100202440090b001d84600c0c0d4113a43c9041a25280e410580340c02846c5005110102c1801c0c4420841003100d001c0f85a401130840f03001540311041d01d0f0103074220044603401501c07025007041d601300e00072824a2003010b8221404080b8a626110b40c109035001810a58010104120090780c1c510200d0401c010030304401ca40d100c80a142c00300040104c030301d540c00501164500381c96007146503030007094581c0c010103e103000039910b40c2c20004181503220349030100d5407040d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 483228525 1250 483227275 483227293
    0x141e090a023001090b0618190e0103050601060f110601140f0613090b10020a02090406060513020421120e01142209050408030c0f1303030c051b012f 65
    0x1c410b504141a900182e1003881648804028040903000f140800e81401d03244519802060602c07611280000c0002c05d4401040d40d6980350142400000381c05c25a01908035a0040c0aa01c2d0032209011040141d03242084607084000300341a29000d043c001c40c20b450201910700360b019034403801000050a001030141c1d0b03640c00034102c01d5002c0d00e00d6110b01d941c00d80c06d00e45408041d01c2d0410124800d08050740280144012039801c11008a900400440b07070560703208400300e06600c0d401c0c1403484040d169000141d5417414a0301c00400400b04444070704074681c2e103466180001d0ba001001101c07200740f81c00c0107001c0c1080e034001030754080b07840c20026010034130203e0400c0c4a2421104d4104480c2800c00450002c60b031200e003090b0680704102c50140480400700081450310090b84028940400c0122019007001d00003180d00080d685190b01c01e5002400c0009904148175040c0940060505d4a50703101c104211500d001800c040391800d07c4e100b07040c4142c04a006502d0345140341800d0001421b0a68240b08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 483229775 1250 483228525 483228607
    0x123061c0c0305060102060603030a1b0c06080a110304081b0111180a1212140c060412180302090105061308240f09070308071a01141e090a02 62
    0x46162003090340003d0a00010600ea54000301760a1700400e0080d000d1885c0210001042c0c0b8101106898401d09651030044800402e900d6041c40e40601745a507503070a080c1c10106805403c1c0c40c034400211945100c200705000000711401d048600645000d85145944c0c401443d0a0340100400d402c646985a8001a801200d0081c0403460300c4001088400f01d000795240d42403558403442c0d041c00180415203a481105001e4002d9114410901084204918000581c80c07410b080820988045998140007e0f0494409800c82d08002426807a40c0310110164135640010f00c00c0c1313106226480c0180720001e40c0307959040c0d26250754006012000d007210a003103034014010f04a402c01c50701e2106561031840c0070032804e001e411107c42c0a00c3d5020b0080891508588606030181e11441c1e0845026108003022134402c4d40303144c210742c001c080300c0b00d40541d603101080a010200240380b64003c0f004104020000c665940c1124154116407003c900603150081c110f524206007003050701c1419445c10510054200c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 483231025 1250 483229775 483229781
    0x2270d020a0b040f090207120804050f07180b0d02011719110301142409060d0f0f0e0a02060d0906090209040f030f0801121202190510060503060123061c 67
    0xc604c2c82966900480d0303a89007103000c80c0960741c070080407907030400e034130b144500e03c40c026171074205000d101640c0b140110040d403140703442c1c102e520410304003007800d450340b001c82180e11075919030b44020b498903061007410f0390008190103078074050400c0511222001c1340703005641d4076281007030640c60700b01004a094100f04401d00c44d0024407130406890900030b00d040d040d043c4503160801d54080f200310702030b00d102d20442c0507620340c204491054200e6002d100800f483c04540c014064070801034000020311a03401d82104055a41c68954440360394071140c0c02e5001621204216402c190002c0d40c001154519490301038058840840d021f540458143c082c00140100301414000d02e0f88291280b003410400220141c4144200340702c0c480d20080c403862000302084c2c14150001d0640c0d054070507a074050805030400440c22221400507030b01c95220340020380202d015441810041c0100301c0092200c0c0d0300d44183d0706c2c164000d8000c800d4803480c10001e008016141c1d001603d20129003480384c1036010300085044401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 483232275 1250 483231025 483231029
    0x90c0504050a06052409040903200f120c0a050d080f09010c0f03020c0c10020c0306010e01080a03050a0201020409090b16110c0d0f14010504050d0302270d020a0b04 72
    0x400c900d007001180000c03040388034880485002501e000d005040c0d80000024000d0411441032846504200c20101c90792a840740700c409a11a0305c0d04102d503081070300703030255807080c05c14109099401481c0c19500180c0001d00b0307040c607010300c910b10360307481d40c0c0a610f80d800c22496800040c400e2149000100300c0d180c001480c50301c07420781042c0c0c18803965200e0b8000c03400d0f074a002d20b0329800300700075130700002584d4401c0d0000d01071007004800311408001d038000480c03a038086d4803d058005800442500407107242c00d000a500400d413a6800d440c1c1541401c01e0240c540803182001014444c0004060400c64000c0d0162401060740d0a010409400d02e41411441c03004219900400f03511700302030001c40103014040c5400d08017820001413804036036000c1400411040140c041d140e4544014440c0c0008003030017030705c04040c0079a9001140c01d04180ca0302c44e117082d0000140e1030916005100b0080f5824000c0710300c40903425000840030a4043c5100030640c2ca0a9105019400002800010070002d0100004000b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 483233525 1250 483232275 483232279
    0x131e030212030705280f05160c080c030c043b03030f0103110402031b090a0807150201150e06040218090a0b01110102121305070b070b010501170c1b030d090c05 70
    0x7203141014030321100007080212003180421044842c650040e445000a003150748e051040045001070503031134143c05401980c0c0480c4003907000d504c0048040c00c082c070510310b92480954050242415504000700c024101c3e14110300c07400a001c54000b1516819001d003400c1c10000401d5a5030f81c1428160a10007038800d000558110b0891340100c003281c02d241c07084034416514000ea10105041c0f94005c0c200d258428a10280e00051200000c0b410308070a11001d801020312401b80c02c203010301c1550103400d642e00302d80001c08407045004100080c0004030901a40a80105d40c01a5200c0d01c000e8182c202c00320794003940707800a40d1a800c2040c40d0b02d03c2d40c004110703a242600e0f48141103000e0341d4600c0c20303482150001c0c2c03580039100307021801c9602c0030400659450f2240080c0d407501603e49003103800c59004040c0c2a01ca04500358010031040d60440042c41c1107040009231001c00e464100141011486100101110b112698111440c1000188140c41413459844814882468282803505203810f0390301a0034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 483234775 1250 483233525 483233557
    0x603190b06030705100e040b04110a030207200a0e0a0213060e04050a050114040f02070203060c04030b060d02091306110a1d030a110118030b0c030f131e030212030705 73
    0x4201442c040aa9020300c88159a82c86c4842c01000144006040492007558000d0746896207048450b503580050506403009590043c0c403040281030036021294000d03100044c3e0804d0104c25403190711109500703c182e64402007a00495207030484010024410082c181c900690040404138109a111440b00a00d0300119400c0c23015803203890f00501116402e11400c0200a149256800142010740000300405400c0c000141004810780110741440c01c101c9200c0c200181c005003d0080116503a6001c2e0001c03020b50b90b01c00505207c0d40818a019405045250464500e0300003804000c01a004000c07260040c0380400d03107984400101901c0d030011686101a07451b08903903c0a001d0a0004010f5403560f0000d5440040c03412480054803929100800006404180074010001c185002102402071544120303883e0703645450b502e034a401e04400f81100c1d030080401c4994801147d098400ca0140070050a0318540070001ea180c00d9280008480d180c00c03058001000f0040c12a40110240040d1210200f0b50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 483236025 1250 483234775 483234779
    0x3050109051f141810061d090c03090c0a03060c030f1a1002030c0d050a120902010e0402030606070501052d040b0f15030a12030c03060b030f0603190b060307 69
    0x4082c04100041010140080040081142c0c0058400303002c1c5100707020341100002ca00400d248020714008031024000701e25400d004003c003517481000183c10300f01000702e81c4446440744001840303001d8082c0500300002808000702d025400103102040c2404002010039594039500e00c0c1a00160141085140102e80703050340c1c1c2c014030100c5002d40b275190211a10000380003652441000410a4900e5980085200034818641000003c0082d00b0b83d0040e162103081c0c540311405c000504064109400001c0c003030604a40c2c9005036082250803440c1c00d42120301588a0741c0d0003000c1003003030280c0b40c0e01610560070f11040c0160b401c0029100002000080104074001c405440d50343c4844100f1b82c1c00a10200c1144000380b481d0146200d00e5401403a40b42d0710f10311180c05000000c0c5866103078041602e0b0201c04502920070990035104038018528141070a02049207492600c100500008091043c0c06210a00044a95030140304190fa403880303412070401c7d80042800c0200055100300c0d40c0c41c0c0244524540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 483237275 1250 483236025 483236041
    0x70c1502090f0907050c0703030207030203010f0b030307061121090c18070503070309230c1c0b04020a0b0318061f060318060c050c19080304080a0c020406060305010905 74
    0x7110007020002d0300907100680c0c1c9030107000c02d024004100004110044c03004d040510070070701000c1f0040d03000368014030290b41540101821100c0d0503d150800c030b468460340d042d50717407404000c0d00d12a940150380080c40803117504103100340d0700c102e00f1844265118071081c254080310884540b4055261700c02100c4a4041031418020b060b0304101001b021560384e00c0004421034410300042d40e000341a441c000c80c500030139540f040c10040b800466414002e0010341d40c800000002c220980907144200c4012429000140c1070000100700181c02a0449049000017030941d1110702a0000500301d041c0150307660f05d4090f4065056482e590301e14003281c024480032400355104840d0318160071403059060b100c1c1132f25003c2c00303400410540f50302c010070b0a0b9003100600402d802c1d110b045000007154681030f90300e000780e614140c20180000489030452820054030408114000b0507a43c1c0164001c1c02d55655050050040e030b82c94030409002540703c0e08194012030640d034941c0005040700e50b0980280015190051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 483238525 1250 483237275 483237277
    0x1a010804260a050c1b0f12010f060306020c0105070e0604090c0e060a0207051002060106080f04060b1008060a0501090308071e051b0103061220010c080d0905060c0a02030a0807090e070c1502 83
    0x41c180303500c0001c031b5108444503d4200b44080e148140c0c1c400008003da2804100015a4505e41c0f00761109036020981ca8050325084c040d8075881409880d00c24a60070000001075440d000300e001d041e00e203d55400d585a040c178003582c2e00105400d401407880e6140d00c11450000c1d601c6c1110300640b0b005900d000c0d2040c03c401c2c00001c216040c0e0707203075448405042c4c0e03404541115090005200781d8990313480310000035a40d120100c10708807111031540c0b0104146008000c1c0310390780c0e8003035200ca1704010220f074080000c101c184003680c0d1b01c1070744802c4615120146800350302c00311003021070203070250041074640100039024004030a00070000f03880c1440155030361404c507411a046280d01800e4840502d00301d40d40d5040c0160100b11b050814103102900c00c1080e152541036412000a89a00715540c2003841e0501c9801c02c00f8070742c40340440c0140e0385021003c0c00020b4032401004028414094040c02160f81076009041c484040c18041040c055149000c040080c440d0141d2401a2000d9080104088100d91a80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 483239775 1250 483238525 483238573
    0xa0806160c211701080d08060609030c100914010305070f0309020406090e060a0e010207150e07090f0b19080c090402040b04090b09011a010804260a050c 67
    0x4441844140c4031200507a400804441c08403500600b85004501400d0388500c1c416015010360381d000c451007011411054240b8041c2c1080c08198000403001c81d100e980512429030103241136170b50f03648403400700c00030030301c1c0150300441140d001d091011039640b0b0f1a80660b0306012500070840b0100301d82d40c05c400643c11038106179400000900641e8031842c1041c0240c00c9080740d41e00c0500006011076480050408640075059022910f0300240c0921611130003e0140c0840740380800002c40c9002c10a980d01021801c00311440038095407569220701044005020403402080f200b0000c1c03240d0100255000010021048018840c0c4010600c8140a8030b01d000d003107054641e410300600500c1c10501c208591940010300403640300741c50700e01226494481c2d02413070081d6840783c05a510b06003446141d003800e40321071005a8007041091243c0c4142680d012003820740143d0441c4881c5018010500c411081d440c8121041d44030840000708500107651001c01040708441e2001a101d601007060702d9106050307000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 483241025 1250 483239775 483239791
    0x4151b080d050403020f030309100501080c0603160306090f0c020d1103040b161a010501080106080c0a0302031f0f1706010308040504110c120a090e04050706030e01020c0613020a0806 80
    0x1d0250001039812644402e4006001e03004448039040805515407540d171080311400f103160024004031007200d5450081d02c1c050300300940900000d410100114205000c001c00700e02e1680c0d100040e48241502960141000c4c0c49515418003244950b0110f65000d08000c15040340140305a040c6d1508280c0319120351101d801010b800303945000d1a09482c00c506410400e0348419087c500304216000909101205202c01c07800507001009600d40340c005403444030705a1084040c030080e081003154203806402242c0948030541801070f1240c68140ca4502180d0560780018050a0030140101e107994094840400721100c8801c00d07400d0080318100b2907198142848000c00f00c00b4140010b01a03807030107400c14407204024022480c00d04020340702103840e140306280d07281c101c000c0024115138003d512103410700141000c840b10340e8a034202951250340c0c3d4200781c8280020076594001d03010002c0000e4040783e82d03040d58075080761802e091a01c00d84c0115403a803001203100c0c1d10000d90002e101c00c404944280308040e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 483242275 1250 483241025 483241027
    0x302040f0b0712120b060c0706180305031c060314010905011802090f1e01090203011e0312031109150c0c0301090f03050309150a02031609050a1a0702030304151b08 72
    0x100704029034a0b011300b14009031034aa03c0b61480391182d205c04002e000084400300007000d203580f070702c0005440c140e2040041c00810f40d50b490280041440082214813a100510010005101203203c40004015540004000403030030204030402c41c20540001c0740481c06080208000030908044400080d10010000d401144000c00150502003003494030340e1045003580d5140d1000e030b003402c03402c414040903001440c41d941e020006015000c2e45a62058a0490707841c40710046034150385070f00c0c0030514400110300030503413109921a90341c411a070a0320f0402c0c1d00038000701c2864054240c4c5030610342102010354401d100380d0899030442d260500442c081c2542112020640b00b0050b2400c4500e40d10040c514000303445941802254884448a207510407440d8150043c0ca9080c4a009443c2410581072401e0400c43e4030710702800556500a4104219030321089200ca2403480c21090301c0d0301d07004501002c5d505001c00f0500007440c02e4150a5080f1180203541e0720201c00d41c0d00d6031625070a540d094006000004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 483243525 1250 483242275 483242303
    0x2120d05070807051218040621060e120a120e0a0f060b0d020a06020a030210050f040f08070f0f0506091c0c021306060305061201020a1e02030d09030e10030524130c0302040f0b07 78
    0x102e03604c1401052f00800940d001c69000303050003040369020484607000504941000c06120740288904030504a845c400707030850308540e031100d1b40007024021026014a5486074401959034503d00c40240f455400390046100343e681e09c0010707459080001c1f065000d8040c68002c1c441d000558809c5c0c038400c0302250280403c5403110f4944141c0540c140c0c03000c84245904010190100302500d0104018901c114400301c40c2c1081c91401504002c4090155603003540840503090b4202d80c0f0003010007186003d4500501021800c5c00007509828607002c20b01c2d43d56252000210380c045d0700d44c200b01d1090100382ca40350748688142c0e08079400c0748030340d04244001551451a65245c80c0039a0b03003050300c286d22031040b02d00303003001c483c042da08442d100d202c110301003201001e55181d58203280000c20100311660404100c10703d4544000c400c1011010003807108240e030100340340310940ea401448501c1042c1207504010082140398050000c0d07006002e050143c41c84554005042000313001100d03003541d030010301035064007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 483244775 1250 483243525 483243533
    0x314010e100b070c1208070b0a020a1d0a06030c12020708040806220209060a1e05040c03060e010e06010207030c0603050109110315090603010b0d060902120d05070807051218040621 79
    0x212544504031b48040d010051040031690421085010780aa44001a90340713070010406403801030750030418950f0300304a140c2c0301c14540e26248090100c0e4428100840c1010b080641144d018034490303101c118143c030102c0c14070240403854001e00709880b036041c200e23209030700d0b4090412030965554021075215600c158a040042c107000d1907241e000100130b0404112203407218084100d01c28440501441d007034441d001005a85030501800d45030020a040800c00c25090400d00001700805006400b00f09101380045002640300b0002d240c0115001a9500c0d006a00c0e40c000030050b02003803181a610a090481d16084004d50304221707030069540c203d010300780241440078491502c2000b442c40c0d616550320040d00e003050302ca4600e0407019910070840051000b520f0f10421078030310100c0c0c1600c0a10350244441a54450f00a03085a1180f90400090f60719040949402c80c07a00c20b49001d100c4441c030b0081211022000e0700718030807210180884081c0401c540f1400c1c0d0303804010b0800c1030350094500400800c4045 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 483246025 1250 483244775 483244799
    0x3310f0509071b120203070606050121020f0d050f33010f090e01060203070c0e0c0f030a06033206250302041d04050d08070507120314010e100b070c 65
    0x710385968911052032140c0d141d4130301002c83c080d410b03000350b04005440010010284100030290500742001132075010401c1d0341c0c0000300c50f00d0758442486540003800100c40c010000517109004412042888245000402d1403144642990000100d82480840d612040c13031409401d205400303002d00e04500e190743ea2004451104050908406000000f0000b007406405854a54041c0003140c004554414662810400e204460b600154130a142d0f00e09002d002481e4108850114000404042d1280c60b4103252400500b0140d0004004d250280e000c001d1040349888007a2030480451f406d0300f810650104020344030401252084078454505103c03d00907100700b07101240806803441c0041c189602c646410300c0111254840c462400204410442000b200704404100e40315145043c070a00d0a01c028040c00d00d0041c003400506d50300c141180d42004500c03ea1011300001c0009101024a596450f03507449000707403c0c3e038505e090341c100010101e81103a4a03411a0310250303128030381d1201c09140808203402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 483247275 1250 483246025 483246047
    0x50d0612050d0f02191406040c0f0602030438040e0a1b080601110f10050a0c0207061b02060c010c030b031b0112050406140903130906230303310f050907 67
    0x1429002e0f11001e1086d400800619201e68801c20f0703803908031070074100034058280e81136000d501103500402050010b0901c4501e2005208a40d44034075522450707038241c43c021b818144c6000b01d41544041400201400d04401003030007100203401c03c0040d402120019029070b503210310320001080500001c149294800c0020b100419269411b031061090529201400e0030441d44a1f03c0503503440300e0900040c3c1481344500c00b2010034078002040070314600078001d0b10008030303120581682c50200006800799100c18046440b4811000d00070096441c00d148094000d007202050a8080c0c800e00503890704806050040101c5002c0503100e0305183c00038400454007a100040040f90929105d058007003071103109460312402040c1d84005151181c4110852050442c09a4028010141800410071003070041e9240f062a040c03400841151400c0c0000201c0c0c51813040c80215a20f076500600084004041180c9010359642c480f038a00c0c3c62039595890120b5001031501071180d000e5008004298018015115008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 483248525 1250 483247275 483247283
    0xc010f0201110c0c0f010f090605070c0e011d06060301050105040e0903070f05030a021005010f09020d09120c05010f060509130c0f032012100c050d0612050d0f0219 72
    0x1c022907440d1803808240c1140311800443d50010204c08918a804a0740e01080c0034286070080030030b0403d441c0148107000521496080c00f0000036904140314200c0e40178400b5042c5045401d400d543e59038900c01001d4240c00c05800500c0e803d2001c580d0503c0c0c90021a0304840c0140d54060030a404c0011000c1901c0e070151a203801884104036030b03000900c1c0b401d642030100303004201860b11000300043c06414600c4201c406040c240c50a00144420040340c4544020f0f61144280142c64140c02c01202c4010217042d00c0261003030220901c15052030744c1c040c1c40244d04a116000900603011410160410b8400c280141d651208180c2d0010301d01049036000017001310302401882c01c141d556249200380001c00c64000fa00d842030b48111410020305565514900c00d0816107840c3c40d17500c0c5000e040b941b9400c801c15400c0c03617562600302c81907c05110324240e50620a5084080140d165a828111050107101ca001c03241c5010f05484428600d02401c0320840403065034000d02544007400001c0101600c03d100100c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 483249775 1250 483248525 483248531
    0x12c190204030c08030919031e0501020d060b04050a0f0b0702010503040215030c0d1a0f120106050915090c07030e04090c120c0609050d020105041502030903030a230c0c010f0201 78
    0x4042034581c3d44203401001188003465a0302000c1c401d004000740051964601049440e504000040585620030441144640d840c602910a4076115000e81314001d910f41003613007407850100c2d01c0074015000300122442110f45104c2c40e81e8403c2c60080303d5403603100311044108180311200c0554007841c000c550042c03005158003000ea40104090f0301a8005441101540d00003261520b581002031060000344c1192080b1400b003640c031280001d40250403030581c00e01480403000721030400300742500b1a0700130308070007803490742c440c174158500384010007409036018452543d002c082210f2005c00001ca070301d030720f0f010303a10401041150700521000e44031002d0110f90801e0740d01400140004814041c240c814072581144041500c2c00324006d1030030382680c01c0244109143d418190042c0c2e04141150100d451710b820081440034104010f90031401880e012540500000541c2c000c4103500000000c100e00c071215401c0b4804640c020200c07a2070240302d10f40307080c80d802800703400141e60241c010a07444902c144004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 483251025 1250 483249775 483249779
    0x9030a03020c0907031e020a1103030a090b060d050c040905100903050903061608071d13021b010623030c060705070e3322090303050901090b040f0507031703012c190204 74
    0x50ac1ca5640112240301920f1b9660b401c034020082c0742a8000c0d0460821507040019000989800761101a00203106200d1903442c9420301c01c0110070b0103018010b030030345d28080010b92041e08001c0c1840e1710000003140300307029000010701e07a8010080f42c290361324141c0c0d841c0855a900c4010685000496550600841e400c00380ca11040c0c1e6582100060310580b50316001d600c0f80801120036500d0303040e0707d140d1606641480d00520910045026081e0402d06e00c2185000e0098141c0109041c1442142c40742d80003080010343c9030601c0b00001e03a40048603480080d104103691008800a0b502c4800c90b06008020781a102150071004600c0c1e0824012900404641c507200c020000c00b070145a000c0b03180b011503912130307240c50241a010300c81e4a6000c540d0800071702107001d03503035102a456040280010010034004d0b01400a01c50204114800345034040c41c2003412410101d0900b8950304248280f214800b808260800750707d210004442100c0da00d26210540c0d030301c0751182090f4001c60420981a200e80c24840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 483252275 1250 483251025 483251057
    0xb03040c0b13180501050306060d06022110080606010801090905100c0908010b06030f011203051207020c09150a0b22090c230304060c0509030a03020c0907031e020a 72
    0x244401100b014042c0080ca1806204401c00c005409070310103c54540001001546c03008170700d072903000310102c0760710707003614868a1310720003c0c0681c1c2d5070100038482c0e100c46440c4401240b50102d00910442038409842c2d1340da1101a95242001c446050010304444010090411541c111010040c032030000e8541000c40c00c00c21138200d614124900c0d000400c0c1e943d040010074400e119812331480107450301e926501e002e41d080c1e881e10030188542d8107040f00707a01c6000e09040c4650305446019441c0184404a4101044000d41e1911404035070b0344107803010070210b903450f140550041d14254010302913040c01890300003a00d42d00d400140038054251000c3c0c44c002e0540130001180c0020744501c0714001424070000d05c0040c0010105050440d40851640b0343c0d0755429920019603900c40d911039404030b00040e001e081100c6602403a804140c051003181e100c0c1c4105600450781c8001c400b01075a024410340d07141c0408405403111403605a02c00304101c08000780002c01a0010250707482c1c903003004410090000381c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 483253525 1250 483252275 483252277
    0x2d04020f1012060b1812190c081009032106080a03030504050c0105030705040e07030f06080d1409062a07030b07030f06050105180a0503030d270c0b03040c0b 69
    0x29a201c001081d441407900c0001c05481020301a0a4049082e400d02140e1500043c4c00320b8206107080c8503072000d40c3c002800340800c2110030b8952682d00b00c512a803a100341b03072580c0c0003002800f40c00250701484401c0c10004110b07204041c40c15030141d4540004003002c240300480d1141e8103154840c220f841303041c040364142c1c0410003001154840e83d40000c81345014242035080030701d80840c03941000b2041043c0034180e0f500006031400e039046410601401e840354602030740100a0a28240c48160a110002a881c6004140d01a00720802c3d1141c1c2611141840214054498240040e5003c5000d10a290584545c00714126a5641c40d07501142002503926074540350000030780c400c5074070710341810400031155030502460083c034140b4142030240d18141000607241c1d000b250140404c030102440c0740e01041c1c0d5030352102070080201505807640d0b00d10707042640c0302625a0141c04501d440c42000c4400e24036100081045c0321a41200c00e0b01405130810864003026030014000f541c41e00703251203000c980c24450764 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 483254775 1250 483253525 483253549
    0x402040b0306012c160809030d150302010e01080c04090b0604120f1704121719080105010e0d0209010302010311070804091b02030c06060402130306050a090b2d04020f 73
    0x220100b030444800c80522140451890035210100003603c007400207401715218507401d56142c0c0d00700303181c02e6036640d80c415140d800f0708030b01704940720b0400341c52045c1c0c1241440c052042d28000c0e622105203100f07240055030901d600b91980380020104100c10407208000340d0184a68100051815280965078400c4100306001d1207001c0c0d07105010343e2003080c100302071000444490900030b0000c0d030038585481c01002c4031054010001e082803100116031920715a00d442203680044003a03410fa02209101040103080d05030900819011600391321801d13910340342504040210381c1d8010403110f038503800c1d41d0044000d00312001c990100303500240283c2c40020b50610142c4090211340b10001400650b81c02d4003070101030f42820f59020740d002001000100400800c00b1640404117a40150751002d000c414500200a0344d403001e001c0e5403030304c000c2c4001001c0c6900312126050056000b143c40fa15040880c12001ca10164000e07d400d0706010364240900680b0340c0da84c0d00a00040160289086a0000c118060180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 483256025 1250 483254775 483254789
    0x1d0a11010e0604142e030203040f0209071706060708071202030403140a02010915050306040b010e062a0c0306040b07030204090504030e010210061203080c0408011d0f011407080402040b030601 84
    0x310144289900308445c422400b2412412100303110b0078160104105800e07801c800c101059000400036045c01107001c01000c2482c4e02a001a11514181200424803010281060350b0100b104003c500a4900b40080d11074258112200510740140d585c0c3d0710315000000b80030b010650106100000c0440d00700c80c20500c4d6060480d01904a0540c0d600c001400e4041540040c0c000401c069000c0c1140c590110a484e4015010313140042c42e020b00c000140c0e20100e0019005621082c00522909007044002c15034001008841d41b43c3c9109850918a0351120030310f48140c0d805a1001c5d00281c0400d00c00328045811540c0741c20b00500e0300d500ca161910665104940680102d148102007032030369641009094a190010300041040c942009540c9001a140d100040d0401070800049a02281c6200881d40103042071b200030040081081c1084030302484890420125005500340d1828241060040e0b0480805a030b40c584010340c0c030000c0035075241101600c10f981083d80d800c1c00001586003000107a028000d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 483257275 1250 483256025 483256049
    0xc1e03010905150601030c2a080309010903080c0403020603070f1101020703110c1f0c0302150f0108160602070b07031106150a0906080a02010c02120106030809041d0a11010e0604 78
    0x50a003243c1c40d1450060301e080e04052400b101c7c082003941c0404105100c1001000380880d010740d682c0c8015180a40480c051700b114400024810100d41c15805022914420b0b1100c525503036604601d00031500a520020303400460400004042c9481880c000e6100e91243c2080301408002c10041c5003283c01c00c88084021513a08015030008410800c068a080d40b011142c03482150300d51460a41071142090303100c0180040e0701641c10030140207004002e482031500c40d40d100c80780303820069210442c0003841482d10034018080e444901013648421501a00d18540041c81c0703a6181601c6030281741d02a8100750200030500340b8008070000207006003806502404065042600d240e000c0001c0d0a02c4c580c02103556518104041044007408102c010302d03242c090a001050403403500100340b81038066078450b4081d51900c5d0000c010003040750054840c10b601034800308124400c103040f00d820b4415141c00405650300680321f49000400c0368404440c42c500600d04050105448404030b0a0b60f0003035007101d411004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 483258525 1250 483257275 483257293
    0x3130c2d050603062206030b041208090604120806010e09041109060f0f06070618051c0c240e010c051810050a0e0406050a030303020a0905040e0c1e03010905 69
    0x2112101040580001c4807158618100320000901c88400c1003200080365030400307056170003003016034400c000658001c03811060900c0e1520340032a15540c882c0000700866000d0000c03c01045c40010b0480c442c507030005c80844c002540d4172098031780140080040e4108a003111812000344c070345501e0070380a20320900e010348500d01110304214003180700230a8240540140e041060807503984032800c568200c401d0303c400d90303244168101440a05501c2003904e005018008600c020000005901d004031344400040819601810030f00b11010544450003800500901c402c0c1c000c0c04411344910040500c0814001511800404106017981e10102c1900c003c240081050304490100344000c84058208a840444c0200104d2014020b8018100c00000300a115800141c03140c680d80d2045000e058010319030f1040c59602d190090295103c200b07800001000044005081e0602e80105002c0d00d0b1208041c04030407094900340050807000090381054076806211018840e202807007190401c2d1301030009006889 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 483259775 1250 483258525 483258599
    0x50306010207080d090e0c07050f100b0d1203020c101802090105270c04080307150f0506130b0303130b07050d1416060f050c0315041103130c 62
    0x1c2c0080e409003443d90031a40300c048280794000360700815104400c059009a0f126560160740c98050301d04020a03520034918000c02c0040000351100c0500e500d10b4041c4000d03d0910280718400710718100050030b209110b0358206130903003c1d4000d411802d40150446500c0701d0126004010b9402950400d41002003480150342542400400103001d4882500e23080c101010758120745400c502c207507402d07212018204001c10b403030080080c00c407001000c03c1011130362030301a1802c0c104280e8407074020030340c0c80310315003586d640403841c4a00903244112401819411400d400702042005002c2c03140205500d800304100945908100e59480030103001601065901da48440c0340c0a1702e00243c850b01c240601000620803c0d111540f00c0131108a402c0012212444a450740743c000003900c030858859410f00d0505041007007800303500000d113129603000d40416429031088000d00040740c0c17402480c003107032000400000302c0b0790903480c1c030204225104da6207003a110b99451041002c00e4070807261036118110360b030702400c1301e070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 483261025 1250 483259775 483259783
    0x30606080c03030f04031103150702060a1802101409061201140102030412030e04110c06042109300302150f0f0412121a03010606020309090c03060d120503060102 71
    0x700380560082d0310b4101c0e24000a000f60060b403000400410000304a4180c544040c0044244195600104a51800e29000282d2941ea00301c601c070941e01d18000190a203c54605024024140c02408008c4580395002d41122803003c0c0c0300890400c1c50341080941c155448890003401c4000094a1100079541420701d42d031281d142e0b4504060456000b0303c811f0040c1e0340c5811707140700b100350b040c00d01c03003422110440414050004103291011611b000300c0c4603214060080b5015100e14441c2c24080915105640c00c1d00e83c1c0400c034860440000c24030001446003190800162018822004c801c490310700e98203400307190400480f102140103070802060a0f80604414035541d41203070b5144040042440c210503c1c8210110007400546008002803240a0003401031880030840364100b8018031180d0345040008c00341c085980c2000d03000390328101000840610203c15550407400044c07680c2c207c1d8031152010695a04040c250030b90111119250381c00082050320b4111400d40d040c2c80b500d440b494444006420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 483262275 1250 483261025 483261043
    0x903030f0801030213050c1e091503010837030c021005040b040e100e040302070f09050c03042424080105090a03051c090c090507020604120c110a09020c0f03040b3103060608 76
    0x80ac0520040c000e41001154001e40c800210703901030281b51442000395289008024014244046084020145a40100c00b5100300d8025078007080c5c84d00010008031402d108a10a50040c0d103410301043c003058a815038420340001d10103c0c425061521900c0c1e01300c1c1400251022405640140000c10050241d01e40c40c100400340700030704119a10b08040c051820b1311000b44018034130707050f00302d9902842c1c4180e2a0400400401003040140c04102c02010300004542038a2a02c000b06114000441460500a0621400c3c054000e0f00d83c5410640e170503038490700890800140383c426002211222060340c400c0003001c600901c0c04a01c100d1402d0700c03007011100040c0564003150071440400003c00e041118060f0307a0308191a0cd0007100b521400c0c0051060880701c1100c0d8420200c0100054988481e00904007400c181000c7e40c3c10f040c081d1400039582e00c503506c281800b020041c06030703401c41c4500394034401c652040c0d5205080040101e0002080031005508100e030b9990741c4001c2813010510400902c82 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 483263525 1250 483262275 483262309
    0x11d0310060e07081f05210a030203180f03120a0507060c030902040c0c0201091e12050615010f080c03040317090a060c030903050315011403070903030f0801030213050c1e09 76
    0x200c03800000880c0c2850005c1030103000d000c0c0a1012010f881d04464000340e5060308022015603000700d480340350094899210048507045450810f01a9140b86040000c160210000030000d011071b81d22602400b200390132142c660401d1100034012000070804601890300400c2e400ea80c002007101c540e20421048810103680c040c00c003c140c00c03039200141d801140503400d80b103544c800c181b01c110911180c078210f41c405801003940340c1414242e01c4100000020554081c2c0341e203400075204015080011101503494030380510016030048049203c900c9400000c41d009030207842e10039501e0381e0808440d20120815a48004990710000d42042840264802e5036008030030380c03078217115052150b10010940d0002501400072800505407110480e8052101e20265030364840c0d2150b2030345414400070f05030b58103070b200960101e800342c0881c20b9564851030446060342e6008224000c40e500105400000303141c000c00241c0121400c00180703110300c64981c03c01f8220241c262046544040180900c007c0d0f07a81e4100700a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 483264775 1250 483263525 483263551
    0x40b0604080604052a040e03221a120a090c05042a1d01030e031207050d050601051611030106080f1e0a120503090102040e010e090d0e011d0310060e0708 67
    0xc5d80c039400303d41c4001e903642c00316030100c4c2200503a2034080c11441031101300041040d54040c0030a44c081c041c41c1900407078001081400c40c1004400d01c5100358440c85501c04041d03001200090200707035490b071019a03507034000c68881c4184d0303442c0c001080449643d50604c0352816203445903041500c550075408442c1c2c1b4004e280100d124010741036039080d80f6542001040c185901d0f000303a030041c51020001c0c3c420030990958901000d08018202615030350205c0c1d08402d0f81401d1000181301540078604940800c91902a0504201007684955108174100e02c07038151f055480300000140d810041140c1c482e035246500180c0300c000000c02c0108107000e40c5405560b0a600201d40d42c8002c80d00c0603440001109072400c02550f80e6442510031402031142d5007006644951480c00400c48074508650300307100c0c9003140101e4083d868466010340d41c070950300030005d000a520704806110281c1003044408030ba903014003226040202c400700c6100f600c07055000403500100420800c0b00c007950009280760002c035175076042 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 483266025 1250 483264775 483264823
    0xb100303021e011103070507030f091206050c07050105071808071a0f190f030509150114120111090f0121020a12140a0c09081b040b060408060405 64
    0x182d2111241c0d40c1c0c002ca000034228240c4040d010a4212595100800b08519034030b150810000d0055000000c0640009174080304102d42c1c503014940072015540a4424540c1c0e005460361604040c01005003410442d140901465000031000d000f914019140c9490b01890350b6212854212845056401010183d1042004000c0c00480d5004a203094000c040e2455407148a00422411481002c00e091800015000c211318181e9100701481c0a11001d0364040c801e54807a080c00a81c2c42850700e40f01c01c0d50602d040700402c00403410814038142110090082d01c0c081c034901071040c0c2140c5003605907490316070000462151510f01051a14910300342400c1c050a800c1c00b038004503440340741240380b428005a000a044400034043d51400b010082c01e4502070003c4c0e002407030760390300015041d64564a0340f4200345214105c28000c00200050342c000c5402011380400d03103181404d91540d88207003030381c000d41e459006103601d032920310080024201100081480f810289405850075030b00140301d015528007a01c003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 483267275 1250 483266025 483266027
    0xa02070c03020d0606030c0b03061509010206160212120f0705073f030f0c03060b0f130b071a06030c0906010815121005010503012a11070b03040b100303 67
    0xc003020303290151007182d41c0c4403903407903c030004240c00d4001a20038417a8140c002039001c44c2030b00a5105141c1580c4404a6540c20141280e240c05000d440a0160704a68005503e12203428290f043c00001417046840c141d480800c45101075112461031000c00940c40100911540006440c0d0341242142c64024a4800d954440390070001030750240112114071070020400022012400316010005428441800b03c0e4941026000f002c00c1d450041955007002130800d2a41c4c020720480040342c2006c07000e6880e045003100140382941c806e0400d900e080a40d1103021640190303030b8010b00542e9114000c0e030103a84c031390507401032504100207000ba8407962158020321296115280d250380c00c95001e080803040398a0305510860520038020410b60031140000c440d240c0d01800090b4980b00c0204203908000507600e41c0c081c14240c0710300f40c1c846030b5143c4060180c41194281060100080d5190749841c0d141c8614004d4801e0804160b580002101d80b4080706110901001c50381450700b003164103c20451061950750 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 483268525 1250 483267275 483267293
    0x3060b030f061c1205030601080a06051507052d060907182a080a0b0a1a130b180f0103090c0e13060204031406010e09030306060d180c0e0a0207 63
    0x961070090486140e252403000c0720542c502242a813140c6600e607545201e840c024469003045030314500290340c40004c141d1b14420f034817840054a001600000c00c40c0181c2d000d00d256036219140840384d510074410424119204201f10040c6036034142c0c03078280040c03024500d044c42d0480107408a181500f002d94104587c69544480f00100301c59480c2c04201412070700c00d0043e0004d2002124032003001c100141044055000d55117520071550042c08000d04420001840104411402034002101010b02070720902e841c0240644442509801001c0310142c4448181d0a20303084000682807245180390151a03919094000c581407010a18082003854801d4840480a9681d481811410000100420880506800311001864218405541c3c56543386071107268111006881c03025070044600100703015100320511402002040000c2d42152038036810000964840715400b84010f5072011a4512100c0c8840b140000900a03403914207802d10300403012845801c014a0840e070284100070341c0c000904000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 483269775 1250 483268525 483268531
    0xc01090b0c031608250b01090c1d0d080a0305041505090c010c170705030d05070201020910030c02031204050606090c09060706050c070b010b04090e06011a0a0201060e1603060b030f 79
    0x21080d2000552030410991622407820709051025022100101d0f003024030f005e2280642c402c00c881c0c449680d03203030b100c6000c41d00250035040c005088510107045903c04510f01400c2c514004000c0c280901007542d64030416800a2159400300342c41d40d0800003400501c08101e0351301d2820761024002032401141071910b07511403180e0603042c045203001e0701080c009042018019004044002550b070707246030825940d2074115940c0c03e480d150528001480f42c030320600030b598010342e02910740340d049185014103070058541c2d00f0301e6604510041c0306590a809090604034000c03070140c0003a08a0341006030a01032400300040442203020800c02404a6980303071030b030031034203641c0d0403840019250315209034201041c445c00b400a080c0d0211400045038078200071004100302e9089010030013200d85114121600c0320b009104550138410146181e840c1c1391003200042c43e08500b01e01c0001141a19004030160a001c1540c41c2101000d00042014040b40c00d4800c05019181d400c1d1018111700d404210113140310001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 483271025 1250 483269775 483269797
    0x160b0a050a02010f230109060b0415030207050615040e0607050406050c0f01090308060901230d080c010501030309050109050909030313031119060b0609150307051b0c01090b0c03 78
    0x5411000340b4400c1d80058444620007a092004142c8408540c1c9040119550034a0314031404000180c203200c02d11888040f80d628141c550b050a03e4a0061703c0344840c00c05003001455020054080011010302071584180300c0d5501510300c02c070308001408112075100b82c0e001469071110060000725504801641d08954070703844c1c81035403240003400f27850820a600104152a600700803c0380d00f01900800340500c00c45007a01c03403083d56030340c1c0c2481c1c0c0000180340011103039420070000000d0f030383d0600c001020b41090042d1304403171400c44082105421514241e00a0b400a04070390b800340310940c1e100901d00c0040a0407601c1201c8c601301140603940346c1c0b00c090925031066110041c2d52080500901079207240006283c20740b40b504600c0c0b0050102c10348030307050444050b07182c1007000009181180030f9802c11480500160841119030b4111700103584090100c10600105011a601802d903000c01d5040d02c002e04400340403000c0300e10b07002600710740c0a41c005070b103e12070078031102e0791140000054132030a92070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 483272275 1250 483271025 483271027
    0x120415021c0c02012d051006090b03040f230c0301291c0b060a0b040819030509040603111908061308130b0a020c030f0a0602030c2a160b0a05 62
    0xb441ca06a0045c1040a400704a5988019803440d911280180a41444000840501c083c4d0760b080030085092505008000c013040301c7c14020710007040c1b680e02840d4003510070048c2c102c1c62042d0752600c032403a03c1c04904243c1c0840e4a214000400f600a100402000c02c06400074880003814611102d902240b44449100c0014018841240b0b507880c544980c10040c25a80300c0b41c0048240d04142a8200085600a014036609040000c40f0411141114200c40e0f040300035011507020480229640e038030315882541044800d2010030030b5030352940304e8440210300c18003010305024181c206105e02900b00310240c580d4860001010488044040b8803ea4170025031070189460005901c0c1c0888203008103001100e039a4032040020030f00c1070b4040020003268000d90210b40b00f02d03400c03200301582e0b21440c604074020b40e04a0750f500e10020301c0faa0051034101c041c42d0000c070706005103000380c8071541d0025804241c5c004444a007031720210f9000e0103880440c10340061660240ca0a000c0030040b148210301d20b030010800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 483273381 1106 483272275 483272291
    0xf08070303081f0504060803071a13030f03090f0b0619031707020402093c0105030f06060705060702060726010302190902120415021c 59
    0x1506580b0007071265100d50309884459803c03034060964000e1090041026641c174002d20b03000c0e2010000464680045040040e213411904012a00d100002014001050040b00c823801d2620f4140c106410344490f15041100102603205003e0080c86c0d80c680790004210b15a103406025107011101655120001c164144035030605200040c5001e0a02d02c0d002c0940c24105c01806910340024001070401601001007000d081c1c113101c0011441042d004001c210b03604906011911610302c500c03894840000c0000600b40b80300251420f4112214140000c0c603a5035030800b114041c51b0300070169001402c1440020b07541f1001954458086004507004c26602104402284d181002c03110340e080140c0d1a42e020300800641958a8200c058400c0304085262000d03030000700a1a800c0c003004c0c00c4079107000c3c2804580c0300d11410313241c100e040c0100000c18541500016a2001d00400100021064 = true := by decide +kernel

theorem cover : BRFrame.Cov 483093525 483273381 := by
  have h0 := BRFrame.cov_init 483093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 483093525 ≤ n) (h2 : n < 483273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
