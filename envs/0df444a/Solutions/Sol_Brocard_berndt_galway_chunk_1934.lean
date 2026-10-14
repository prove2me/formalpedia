-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1934
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:12:43.626428+00:00
-- url     : https://prove2.me/submissions/3c4b180c-b2ea-4541-8ca0-e1231df6e6fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 347661870 ≤ n < 347841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 347663120 1250 347661870 347661887
    0x10e0c0304150c03290a060302072a0e04050a03111f36031101140703090f020a140f03060402010f0c1b030807060507020607020c040c170408090a0b0a 66
    0x3a000595100c3c074648a041c025040000b0808200c21040702040150541c542d5a2401314800c5224259519001c5401400fa10940b4081c0b80c00410a000f1306040b5252981c07005207030943c030054000f03a40c00029031410424030303040c0304600c180c0281c22800d4291a01034095a10305c070000320b01e0b405c42c10800d0302c03024071790850402c2c0c1041c01d0300200d03817241001c0d00d503030160b0300e0070203004119484c000760300a680101c0e142ca84603244c4240d651419094040740c1c99402c0300c24203010032051906040216450512035008450b00300d000f1001d601e41c0f07118944c00074000714441ea100182c40c0144002a0605c3e103003808000b808218203902401081c42c1640c00281f800403208a80c1d02803007008403c01090001e036080f0b40a08018102c0002260b80d01c0e130500c030344140c000038001c54056041000040b4800d1000c01d5942c00307185a41c004100a58010007000007030004c642c056003c005034680071690658242e40114000d50040301c0107550f0b0b84284003800b0180c40103801540034200d013003080343c0010380d00c40c0d402e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 347664370 1250 347663120 347663153
    0xc0a0e1311090901020c24060607031e20010203010503060c130909050615040c080612010e0109080a030b030a03080c13030f060507090807080307120201110f03010e0c0304 75
    0x448218260710701030900c11601c1c00c229800c00020020080ca8000540c010240e50340400c0c1180c030070308034000440307007003845440c42c042100129402042c09406c0403005404a035103e81000300403c80b10125081c1072410501d0b004002034814030110318000440721801200c10503090003540f640d030424011030340e03e507000741003011a20360028105500761080792500c0080e01845809208010746424801d0392030009071a9200000503c0c04000600d18240c4108a021400d507142c20a05503151800c2184083d90340b42961059503d40c040c41030f17941c000f80314560415210306511a110041e400001301240c03405c510310740c001d90000301b064000c44d81041c81c455021185592266440035030800c240c00e801280d03400100b4044031900110308000311600302038440c0700c1a0f907a5000055803064103070759420b4503109050460300104406004600c80d1040d0301c07001825400007140c5032091500030221a44881d9400104a00110041c003268030407140c4145c100da07000c4010390030b41c10310341c44004115a42442 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 347665620 1250 347664370 347664391
    0xb0d1a090a23030f040f030303060f050d020906040609061206060e070519020307020405150405060913030509030111070b04150903050901030b0a1707170604050303130c0b040b0c0c0a0e 81
    0x542c820740601c01c100b02c2ea00304225401c81503c4540c0d50740e590b12020001c5c0001c81c0420b082c405c0224940884440590032070368000e00101010346e180d000d03c100c000014084603089030715243c02192903c02e80c020a00105038000100c41d0744032540c00c0c40804c4820541180d0030030000074092021056001d016124410254100703860940b0076594213a15611501400a40050401c001c2041104500226507100503094505202d5980d03008100003048008039205500b640d43e030341c90600030902c00c03400ba020582010740000f851285002c004403060304032080498000700c0020800c4104009409202046030f41d1400034020984d26550180080c0601404103040680c2c404005410340e03280c9440a005003049592a001c180001c020207071509114041c100c1e00b40f2004140c3c0072540c1d80025114419500000510b045841d010201d0900c400355200548000040140100d0080020070061004002c10203461746d0325090071883ca4200252901141d20501c20f1200030805500d500703041c0c6030302c1054803d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 347666870 1250 347665620 347665673
    0xf0b010e060f0c0616030b0301090b1504060e13050709270302010b040501090c020c01051309050408220e06010203070b040b06060d1802150708070b0a0b0d1a090a 71
    0x4207007240c0521000040980300307250a0100e4503141009005c07030365050380d03030510203100740c0800e041c00c2e00d80d100002070120b1100300020390000c0100d9560644080024404201d40365030300c20012055405648998071151230b07146200c204502000340e5001069000c0007844821100314409030185840758403500c10403846000401003600c01c1d03002c20101c100c000d10400043d40c447d14604c0c000c0100b041070401500c141440c4c221198058400d41780b105241c00c2c1041422030405403090090074000c0d0044507055014419101d51140e0b540d4081c49102800301c203140303c545088060b10301001c0152505056410070403032100817602a0f42c0c500d82c0305030460700440791a1a19008903151340700e44081c030140710b443c007241034020042c1188000031150085070f5014142d0300c10313030342d14801e4030400304c00401440040121900245003003060350340c0b05440140c00a440b80301e03c00450594194140102c505c6c0c043d02030580b20410701e6680c4903801000030b00042001510607038420b407202d40f40044c02e00d04c0c0c14050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 347668120 1250 347666870 347666887
    0x90f1d0601120504050c131104050f0105040515030f1509070e0f030a060e011b0c1b030b0906070909052a0f0403050f06010902190503060d06110d0f0b010e06 69
    0x650440303082c02c0d91040708102d14503090925a4a4000501e40c642c810400030042010541060044c2240780b54807402031403406150204011800d100c40d2034850600100380301c001030559800d0203240b220103842040d56500e14201d0b400350001c0764024501801d2074004960030501d51140103542e503002d521810070110021000d80011039581c0d155200540c54800c40e00c18404000031034220040040407003000b4403803070380d070611200308404042c500100021001d40c40c100106101d0390317021580302d8000c803164104940320b032141401aa001c9405040641c0010284502c1d658021f0144e002040d00a1013008541081d803c0c404682c0050301240005600800c4100d45000314502154801d04441d000f050741e80b50380380381007909d035000301240701c0160180500005049126000329030400301c203410180100031006a058803e6040540b10582013000301c403004002411a110f07100b80d040f07039510300c0c0da15240300c40c3c0d403401640c0c400e1075080342182c00c149010700d00341d802510900c0c40d804100e90b007076243c1a51 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 347669370 1250 347668120 347668127
    0x5070e010315090606020a0308100e040f1106040b0403020f09010303140d1d0c090903030f040803070519020601140f0f01050903030d0f0c0e0402180907030e100507090f1d0601 77
    0x168200360000f618203000000d080b50000f449848040c442e440d02d09880e910b100229040d808148150841a0800c000141c0040ca00c0300340c12050505c2610180b0311007001b50085148c036007181e080385046160000e418025813609000020828404a502c26815815594000c000580e040031060725403c0104411400750401d8025400160020988807801300001c2195079a41007500f0000d40150401008551000804000c503445000d184c0d0903500b140e01c4603541c480305684028068020848203000f04102c183d0350540c205041c0700641d0080c16603504050b1a500b0094410001034440c40c1d8525982240c0e859000326608190001d0800c0c50711002200c011904501c141015403036503602c4c01c5000c401000349079001c542c050380c6594510752540b5481d030a1004920803030540305580640b00d0380c0c100c42c0b46003132030361185d100e1028507000c1030b46419031040e00c0c81d0440324080c07500c200d03480304100b042455210403504000d00080350031003045841c05507003040301e1000452400c007040c661000a91280d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 347670620 1250 347669370 347669411
    0xd120c0f1407051f0c09030308060136030512090109030213110c1b060327101122050a030308040c0f09140f100b0309010e060705030103030207050405070e0103 70
    0x200801500c03914009084040c4ca02e044031500039031010b00d440b0360319060b03521a000300410750b5450f840c1c200d0b40ba2101001560094106a820a0341e042c030007513143c04c000281d15280074280a01c1100210b8142546041401e202c0a02c054030b1900c074061140d01d43c40d81c2d00081180889405071204044c2400c02c1c1200380180400507071821240400103510300321558001080c040405243e009138061428903420400315200c152180d000c00644e0741d2900309042600003061007072503142c3d4200e982d10211000c040c1d00b030701d185201c61520900040784100300501103662041044044040011074241000c0018070101001d000280400170160001030030803088a2100024000140080c10801c0c1d0310903045002e07200c00f000064042982001040d00c100c045004680505208010341911070704160b61104150802020012203640b610041c04100780c091142c5030084006554055981d81141800b80ca490707501d61000340120310380810094541d17032045502c083d8000920b004078001060068400302c100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 347671870 1250 347670620 347670623
    0x61020011812080106180b1810030b0a05060304050601210c0f06022103130204110406020a0b090f030909040204020c0708010506010909060e01050909030c0703050d120c0f1407 77
    0xc441e00582401440041c07158240810fa6a0a4050f0f0700d5841c2103030315400017039040250707600174030040c0034101c0303d58081d03e00c1c400350617206014001c0303040006030f4a0105080c0100800da941c00c3c1090705041406c500006898207450403860750601d80d03201960780b40140320700d4818142c0c8280c8106803d030040e040c20701852b080b80160221a445014030f402448142c1716410240c07103800e5000913031815094400c90031031480c4e82c440b405d5503a0784005400040020100f01d0b4416030310031031114034009500142000d03218a074000d0184910b58170b007540301c46102520307000d00b982c807600a4600700c0b00f001080300e155540c2501e00380c0c0700da210f91010501a00554410004038001c0c5500400d40030015440307584995400d983e80200c007562201c044049603014010f6041c0c220900c0014400c5007032010407590042c080d4070403246802c0c1c0006407203041000c02d070021101600100301540c80030798088141154601044020032607400d0855010309000041032443e814001c1800034907201c483c4480075658002d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 347673120 1250 347671870 347671901
    0x12031003320c0a0e1e0406050103060b010507050a02101b0b0a0b0609010c0206090d021905040b01110d080711010c02030408010f020705030d2a050309010506102001 72
    0x200c040980d01c05a90004444111a407140c0d0310515003038880010341c0a0b04950251280e40600d003012070642400c14010103034140842c10500c0b03c0142604249500e10a43c041c1702c0000b15035055150007001d590060090740d04201e42803041c2004202c005c01d101030aa0350443d804031100c801038005403440d2402b0751040171503030210388822040c0000044114031138016003508200c5403045100300012070042c19646030005100005101c01800c005000f000a458028080c0c0d41c882c11907030005d101e04400b2503a110a00c6d900366006c00550800d4000c3c150500c10908050103a042214061a580c0b40b812156a0030844004085504d06016020500c0400d011070001d008042003248003964a50140c46852055880c041e18504e001c205071007540c4403154440c0242d490800d8516071840500030b01188045414201b00094480c40511001c428a581e40d544800d500c03072510a120f44d0850303000801d15806540307041d0010f40b901d68440c091110001843c92003009500e200215a40100ba40c44100c8060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 347674370 1250 347673120 347673143
    0xa0207030f142b080a0905071d0601080f04020d2a0608090d020705091e0403031a0901210804081b030d090608070c0f0c0e011a0c12031003 61
    0x340310200c0b002c484841d95401c110f5000d4001240100c0c0784821140a41101c507220340c4500c25614418040c590b00001c0c031107008160900c0320b44515081c13290b207a10803844440c0710303520415400304000c0b1b071711b42c862002d007000c1d09107280100d8007a00a81d40200000e00c100c3d402c8900e5420010100c607180c0310100c920941003494190302030081d400e00128011440400c1d000030018000742000200c9260841050b4042d00b681c51604041c042d16060241503000240c0e0564a00315070744403000030b0244502d00070f950105040c1c040040d041881111010340d10f010303207000401401810822001c9003450010310404003815003240c10314240301e0159402c503540d130740119000201c40001840c445030340060304a003038450780b415040003503489803500c2c072a100220f01c0c000f0014049030300815848080501880f0249040452559261058012070308010b1b04c2c004910014041400c034059000704d03900e420280c2a01d4901c5a00010750f950781514445c1802c20b20002c0055000c4541a01c42c9004617402a08802c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 347675620 1250 347674370 347674373
    0x10914060d0f020c0721170705030c03180f0d02100e04020301030b04121b080901050d021207020d05040303080c031e09030306091006120911030703110f0402030103170a0207030f 78
    0x3c0e5111240c09039551251a601044140c008043d40d0310141404100460b0820a51b4030031500c180c240307184d65800c100601840d804503500744000c10074400c490002d1566514046800040c110800c010a4061100340344464201d442c5d9002c4406250740403584995040e440c10012100e01722440142ca41041c00440000304100315814602d014603ca20088840321601150455050645607240200411180c2100b004206050001d010019040c50140c5c9000003040b40e5100343da1180160010094500d403c00c441c01e40e06000500800b01c1a107800382c60310b89161402480e0440281c0702c03020400c000400309070404800d86209103000b900000050b21450580f00854491b04100d6046021300a00b50000702c40d084056400021b0300d10316100c50124080180b1500000e041c44e0400710b41440d4040990780c059681000b002004520426504030404150024001c4c0b240c1d100042c02c0c0120300500042c0300040a940d0a800e0450740242e40c56101c0c800d40c3c41c00c92500140d980f01070b21207100c860780c82c030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 347676870 1250 347675620 347675651
    0x606040f030b06090a02071707050a0b01030f030e031b060d020912100b0f0d03051c180c0e01050d02120a060603030806040b01090612020a1e0201052202010914060d 72
    0x1e03c10141180d4000c1307190303101000030040c2d11800c2001424002c4a500c0c60718207031005c1025214a80c011421070746021001c5d51103020748003081e0029100540c90300002c2c010550b00505000a4200541c00360a107040342a01440740800c1701c21015100700004220701007411000d40c1500c00b64900100050f494400c86030155881c0d147c549403c4d0812401e04040000d2414500308442c0c4041c405004a60000c2040d1400c59141c4c00c00190a01d050408031404685441a40030700c800c024012100b441c8940110300d4100e90f00244d5501408110801900421450ba980f5070251180c1e078065521040d00481c0704805410b0030401d4000400c0d40d407404502005040d0f20003805845180290f82c100102440403005442c100c00600c505400211940e882a030b01c4011900649000500381c18181c1b060800003030140c81d04604600d030340780181c1d583c00070001240b86541c10841d01194580000c00b00d06a03940008140b5426406003038074a0303407a01000034058540c44212140c82c00c20700001c025001e200480340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 347678120 1250 347676870 347676893
    0x4050705130602030c060703090305092d0409020d0f0c1a04152f0708060109020a0306050109080606010c150f0b011103043b0c0c0105070801050d0b0606040f03 70
    0x800c0c60400c000000c42c115000100b15000c0308a840002d1010b541e501c036044024200e00d903004c80c200941803049801c16190f00e000c404a01424121440d00d858034002d078041011403c00404d4481c9080c40201005600c0e0100781c440065001040d070072940d101d0b820010003a417119030042c0d11109404907400c10380340000001d001555105500c001c2e001300415000c484580c0c01a2482c1084805140b200100c107515580d10600654440c00361441140d03914202800d00000340d000f5110f0036000544082c0b099890b105a001401c000d0904405490420f0081652400e006000d5410301401c0100103080c081109007208086000c3c100600030f00e041600c1c44005000c014140c0d9011942c201490814440080140c500356010700c224621440001401c14800c0d0301c200010403000c0400c0c00c0518560034012022a00c03804111005076580e200c038960a03400c40704000d02c054100902d085c018441a40c0d501c0011113100d4002407000c20f59101c1d200041c500c0d200e2603000101c1c011034001d00000708110300320b11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 347679370 1250 347678120 347678137
    0x616030e010806040905030a120615050310120803151f0f090602060112031b0209130506060609010e0108070201140117010e0105060d0206180604120212010b06041a070204050705 78
    0x95106540f1000306200554144920041a680082c041c00e840a84a506c4591659181540214045594000f131420200e070390344410001403800010454044c0d40b0208c080c1c0100b05c1a0802c000306503c83e103c0000c540400352420111040b000d440b642c4966411200b005e6480c0b00c58900610344000d0500500341380109421100070600c0e03a200002c040e4000f1408034100c0704001001890121203590403214500d0002110400c200c5a81003003000d0317103e51080622901d0807910044a80885080c41440d0000040025100300410043c440259034010104080030303c0038200380c1859201d90b40240d014200750542008420517807000020302031017400c02d00850180b0319000300b001c810544289403d071102102c4880c0c01038001e02414006003012001400203400400203180f40c03414041c0090b0503a40a84e1102e42f9401c001108002980b41190304081e102e000c10b0000c01c00d440d030711000f05000340961703c180425481c92440d81d40d00c0c2019501181d08081c1d000300200316602e4121030160054108041c0d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 347680620 1250 347679370 347679377
    0x30a0b03120a0f08060a122d03021e0316021305041b050a350102040810060605090f06030702010b061b010b030304061706061911100908070b04020616030e01 69
    0x61244418051804e85000f940041d146008850416080501588106000b21040284580d036000c11444400c100c0b00408454040c2030b03150f1000c1d080007468104e222102800e010300c500a04079a40000100303e40c0441d45840603610070101c58000140140c003104480105c142c104001c0000700440482c8036801503a041c91040107e94503101441309522140c0610900380900b0440d200950340741d038075114140000c2c82503440c01441c203000020300b660843c0c1d00160311030340310351a070a07085a1280030f481c0c0600740b640380c4507040031f0b42c200c00a064041c1c03400d83d080c0214400008901460310130341160b400c404015012554442480b17004410b1a4606240050a94a006000c000614010041324211001d6a642c03000268102d02c0082c1201406409136500420070449203e49021461280310928265100d05001d08840078005040c007030400349121a640c50045220000345007102034440b8990007080c2400a075a8a10202e900e521815024035100c00d00780c04c105c820503500c030481c0301c8400420783c4d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 347681870 1250 347680620 347680637
    0x806040921030e070315111b0309010f030506030d0c030e060a0c05010608010c080406050718030803150303030c0708070219120c0b030c0d0507090e0a060e090705030c06030a0b03120a 80
    0x180f40a0300c41d6603501000308400448000c03003d0740c0b480d5420444003040865282481c1140764004075820200006001c4003c1c0c2000c14960450368102e5604032488016041c2402a0301d000c0300000d803104002e0400c18184071040940300d06240c4501440743c91500c02400d41951124140d201400d0081002e008644a42c203288000c40c0e8030f0010301402c050003a203500c034143e054070307140d450b4000707004001c0508080001c203014103815844c99064510045002d003880075540d0500751008841c001e003103110749003e0750003003090010700e0301d10504549289070032004c81601c07a0040d1000450b100a5525102c14211940c0c0e40402c40500b0a00040c558601c03d0741c100c012581c0d507000c28402804100c5903004451028015480d4045140d0002c6601400500c1c1408141e40c4544a04445580c196100e9803507941d2448140003084c03d840489400a000c1801001c0d07003454003000a685040314400c46004180200110b50502c0c1e10350860250395400070b082e22a0320000600c0c094564010301c800d1b40001e401c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 347683120 1250 347681870 347681891
    0x11030c0703060e0f0c150903100219020c061e130b220501090b0a02030715050603190f03050a0903050d080402100302031e0c0c010213050a170607080604092103 70
    0x650304e01d00112a03010b040c0c401ca442d01008524686440100520502000110400e0303070107005119104030104001600d50038400c4000301003d00003040340080d58044030a10983d99514000d0711101160185c000301c0041681c213a00b521400b88840350042c8040800c401f08030030300604083c241011140101c05180d01310030700c400300e10034001c0c0704071404070340a108288940f0030b801000b0004103500740105c0c0d01c0d00d0803940c0e528401075040c0a0b015440341e910310501c01c030b034a0309201c6c1000b4400c45c1144e02e004004140c4410081104802e8014140003001420300280c0f40900003540040da003200c1034513144003000b007000e02070400c1141c00300c0c81602c200c280c05070001e010f8800d89010704c004007143c0b41d04120940c01b0401901c0044d24200e0084001d1090f8070300000d00340010903c85c0764240c480c03000c0ca45401c3c207111416405801aa80d426404191b5950300f0000040f4654001c1d0703a03150508a50701c404012030010002c8a4003c1d115821000404075042c0d22250308000d58a81c0d65000c00c404480d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 347684370 1250 347683120 347683123
    0x41503021e0114030c040506070f080a110c1215130804060207060e01110a0b070504050415091406031c142703071206020913061701050a0218010c0311030c0703060e 72
    0x4070740c0e03011245c03014002480241842800b410300071f4821020340301100202c1c0c5903400a504050780d0880000c07070117046e800c2d544009205141100605861044a43d0082c20f4520b46540480b426004050084000540620018007520410a40003c602690340c2d4a4140003500c80d00d40380140700104e10b28100d0008254891440e501512904d44058030038900d04c0d0b620441c5d03000e0054298405c0150a0101080c107075164800c1809140503070100b150b6041c41e0052010656078868504034941c0300101c00c1003143d4401140ba40120700c08050180f4400105100a58031946000c0200e042c901011590003000c01c040c14820807060b036014080c03001001c000f81010340d151043d0203042c0110f2954040d92001940700d4000d0120944001c0180c01a07080750514501142c1c1c003a4071103000d500b400b60010414030404e21500360045e61514065107081b0203407031030040c201c000b07100d80d504014080e80b07140281403207800303920041080034050700d43e01c5860042032030340c03070f02c450205403034031840d10480c81481d450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 347685620 1250 347684370 347684377
    0xc06070c020603010e04060b0402031305100605330d06090e07300602220e040203120c031210051801030521070602040801330302041503021e0114 64
    0x307004200914680c20305942103150807002d80112042502d40750104582ea42d40d001440c894000554900e001092a0801c030780340000d00070708228680d140030300501480c0c44584a10b48840210350038094160b080da0089504101031071449100840e01207000c0b0741b00e00181e0004030450b0001c0d081405404101d10b8030640700c40c09881807140030091849140c0c86168000c0745240c2c90b542405075a80c0304100c54503441c0030b07a8031001c4011101c010394001c000003014041c507000301404032440803016a14155010a40d998010040c25080c51004648a16010000c108841c0503074070345036880705207050183c6840c3c00e121140c001e00d407003130903015114050148010030180c100e980200c0100345624080d042c03c2ca00312000540a95215802c0005a02080160001300010501d050000612104180410a100c510948019824140d00001882d50110420903c007034940444000400b2460030030b54950003861584003c0d00001d814401c0044103124a03c0803803041d00a0b250002060701d4035076091110311 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 347686870 1250 347685620 347685623
    0x50604050a140a0509011d030c0118030516150905060406050705070201170c041203020304050f060406050703030f020415020a0b060405060108070804020310020c0c0406150c2a0b0c06070c 82
    0x38076490010703100fa551a0000d0340c00058180000440503445800c0c80001c440b4143e9041880d4000200d0080d840c400344503841040ca5250380c041383d80c003066070b0010030b01d00c201e100352401a84031028903014844d0881d00c08080b00e49020042210341b0240c0b41c00c80e1954011103050b9400c0d8070b00000a0309031401001214850b682c140d6444843c08444840c1e0844000060030360748201000303000200d0a000b28006c079403d803d01903002151543d14080030009000002d0488900440b0188000c0007134940041c2614080c0d6132600703010035408001702070f980c001c0c0560303485441020320000d852640307240c01190405416004402c4010107a4803d01400191030f011780d0410700150386400010005403054901d141c21510080075107590764030715906c0c401a0b801c611124403c3d600441e200320090b1800f44510301c010081d0740120a1540580b481c050710083c010b000141c90b00095240f8590300303420509d010480d04080040242281d51541541c055640000420b0491841510007051040d80108200020369 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 347688120 1250 347686870 347686901
    0x90905070504032319140309180603120a030212010f050904030804050109020a03381501091503051b091c02120a050609010c05090a06031d060a050604050a 68
    0x180c0f56030390740d45103203c0d040324201482d542040705102d0b40b581070003019400101c58002000500d51804c0025843e202c0c0079a41201d94400c01000001e07417200440c1080e000c900d0070b0030301c8107965070401280c05c001c1506000b0780301c3c2000040700e40d040790f0107a018181500d40c180c102c605580e218100d601c08807030f0a01400b13900c8404040000c0c0005d2044012641c094410000442c40c45c0d800e901140c1a1045904104d44455072013040300c9684009024018101c0030781c2c6841c46a031070320321070201a000d00184c14035040000820014500d44d001d0700d0707990000c24040d51444041041c0490003001002d0549802400781d401d484404061109501503a1382000e0060219084805000b004508140c56450072a003092080c6584283d2079000c0c4140000c0c640148090802d600d400c0c44054210b42c642601c41082c418140702800a540b41c2d185000b05440a17800c0001e00044421640c1d02c08558030105243c551081600308514a01c441d000903000721801d64007448103480e98050441a14095000d0f000103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 347689370 1250 347688120 347688127
    0x50d090c351c181d0915040209060307080a080315030a030e090604060e070c060f02040303090b030a0e07061e141602210105040c081c0f1218030909050705 68
    0x10034109a0b00c2110b040020700305030205041d02090814500081d62003503030442800603505040300344400541d50b000400d02c0c003402c40b034288005010101c41d00170303001034060468840019400d81b01002098054109001242c0f4840c03040d00d803441c603641c011150401788001c0089800b803a070800240001d030041c0d0586403030312866010350603c8001e0b176001782120b43c000e448050006181801c801c0d40b40c040c101e241e68400e440540707030424109403116121b000301640d104000410202c0e07440320299080d51f14060701c1d1030380c0351030b451044030291001d00d180031100d0090786030001303d150304000703000079603442c3c4003003400150000030041c0c401910810f05007001c00c0d0b04101b007a0380003c4010b440a0a148018082d40c2e1708072080b14410040c0c400325078000341c03980d915014081804001d600d050014000d0400801d5240540e00034113640502c00d403c040140840c0034143c50049006007401206101020010084840e0050322038219040f808400c0d00411003003900400e004686000303042c49040d003621510315 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 347690620 1250 347689370 347689393
    0x60b0a0e010b0a021905010b01140306060409020711040221010803070c0b03090a1502040315020a020a03141e1902010b010e100201020c06010e010509010906050f01050d090c35 77
    0x442d41d000031000301c00c600840c035018842428442c40001c940c0c5c0540700007d42c8411a10001d000c95401c1850f5659140c414410842265034000c1214240d9081c00c60140c1c07100706a141c50b40b809015400250380c0280041010b05031656140081e00000d2091114107a1507641c03a1040c54881c490814007415034414100c1c18030060320030710001c5403c181c5d45000c60301501c0d019100c00c0d004400d003804001800c2d800103402c105110308007840000660700c0310f80461030a04000d5020f90f540103000f00007024806c2000003401c18070003490039614030740f2490284241d184403001051100e903000340d0321600880c0724035034054500380c814861140b40c90410703111005600c040d038041001642c10503480804641d02001001325007241030140702d00030320400410100a505000030000c048034140c11050009291901c20481c030f695030181e000004c002800c04035035905803002801c0190400300320182122618100000707804142c1110b0f41080e2402e0101032032012100798a18504e02d00103a2701c840560b0004034100c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 347691870 1250 347690620 347690639
    0x160203071211101a01020c0a09110d050a0b1503090d05030c07060e030c15101e120b0601030c0c020901091d19030909050103020d14010209060c0109060b0a0e01 70
    0x1000100c0c2490750300e00001c1c10340c9518101c403158254034151346403c1401c000200e000c1c031040341c00d40240041d10087d02d9032404540c00ba50648169104207840d10101d0256420820480d1500c5401c00000d1040307140c03880014019281d503443e50390090500308000d1048500c1e6034241c0303000302200005800404600c010464054201502c1014200401c00c103200014405115030980401e4190255807114541c075255420001140140b5600b440e00204000600ca4008140400e581d40e2120301d0454250f1480c001011283eaa00f0584020003403148030014040d8040110f407050909a81c00d00c000c4218400403103844560110007504a08003c0050100f03801d00e8006010705021040d40f401007580c800c11091520200e101c4000000c0420000c1005141d40019000090f11000c4001e1045514560124200919241010703041035085450040910020b40444a002800030511034443c55071030006070003042e4071542140c3e018a482904000d40c100a85c8071300031030b0054809500710340c0ca05038000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 347693120 1250 347691870 347691893
    0x20f070623160806031c0305010806010f06020d05030703020f0a0e190501020717011b05120915220804090e1e0c01080a1b0503010e0601030506030d0509150301140916020307 76
    0x2298540101b404039201d14601e0b464100038100741307940c0490345514001c14107044c12810f810460300d20500b00e400740804d41e00000e55003114007803441c5c110741d00d81e41c4020490003401541100a01240001150544603a0060b10040c1400c0115141c0440f041000d03139048070075026110705405600300b00003c08c0360720002c4002070440351140c0004030b4805050001c050f1001142040d1401103000850b1800400d0301d07919940350b0040740b82c00103207465050003502d00b00d002001080d040401c6502003400031680b00c150b900c1b0004580c4041865111a11aa548405481c2c00001003025200d8131814541211100706481e0051803014040d042a98120004640d1500c0080045000d5502d400d16240950540342080d40c100942d5074580d80c884d41041480c03c0244030113487c6504050400081c058240d07000b26003641120f44508081e682c0d540b031030012840301c099912701c2d903450310008000000c0410303040504107041e11040f14100000c1d40e0f42c0c5c00107446401c2004100f40140c0c010300040c00002c0451180 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 347694370 1250 347693120 347693131
    0x1b110d020604050a030b07081e06060306120105010b0c010f05040804030b0903070c080a0b070305090c0105030709080f0106030212070b0304021309021306170c011e03020f0706231608 80
    0x740d80c505900c8030f01042c40811075900c11100902494108261580d0102e946a04454400c5101c101e0a151400142d012000134066501c50f040c0080400c0c180e56501c1082c425041030350000340900c2d0303540c42a2500e540c1042082a0065081c0011181d8802c480d1160070702c50f80d4445049420281940c0382d41d402160000c2c1170750840d100402c415008550030501035802088200d00030000c180f100c0c45d00400104000e8007540500d400d080600c00344000200702443e50300820302e0b0154403543c4042084610040740e502c2030009004200c5241d1842e1419000441901e000755404814000407040c016038074141031040043c3e0003c14000b1400602d04402d031142910580701c030120702c0a110b50009003a40180200800030b02d40c0c0d446042050441400551501d84490380181031038a40e0940040c2401c0d079081c0945011640a00ca020354443c041d5054566440007110317103039118590703803900750020880c0d009082d0300703011114a150401c60035049640e00c100030b00d03a0201c40d5030122107029134003030402821 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 347695620 1250 347694370 347694379
    0x330807180b030705030a08041d06061e04090e030c430e0705181512040204090b10030302011109010f05090a03020619030f09050d11031215011b110d02 66
    0x100003a01e9a4100b095180040c083c180a990708c41c603000045140c9210180c04030b5920411030200000d99660005a0717003001001c5004100300c00e40040100c0e514422030b00010301d075603e042160450b401001000e04000c0320b00004a442e10b02c10b55414640a00d460141d040b0381c0200d43c80c400101d51074a0703821160b8802c03050b000c00c25403502d44c0f003a20382d200e81c00c0710340c200014808112000791005c1450300051544043d10305041c0c094040c03c2030700c3d407032240307101a01806103283c002c1001c5442d5940002c48040d00700346031203168289466200042c01c134a01c015001076003825040160070b4600c00032680b10348016101c1c0c22917440c00941c1078400e90020f0300d14035030041c40c41c9000005a143d050081910500c403182d410142400020080c04651a9016869000c0d18041259000030400192000340d0310590503c00142d0f507000007280d20310b00c0b4481070100c044419906102180c0036220340c1c1007802500362900d04a050b04492100705869002d4409000305590b204840d101d4242400d103848014000361 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 347696870 1250 347695620 347695633
    0xf0203040306020d0b270105060c07080706022a0108010603050903120405010c020d020705060403230d0201021e030708010b1b0703080712081513330807180b03 70
    0x212a02d040340c1007400e074018403a46903840b414442c9050600207a8903c8240f01900002032003503500c1040d000c0500915024040000700d0100040c010892900200051007c56142c544c5505000f901c801410041c601010706200001c4a1149242d9001c07002400694039a07602e0703864040102c0140c203000c1c3c030258103800104100c80100c40c6401078079110301e00a80c00422602d135100c23030007803502005205e00821504801010301407662002c00700c400301c9400c501500000c044000b640c02c420100b0340c01e240410310130701200c080141c0c0c041d0050082c20804041c4902402e2100c1103001c41480300300c540741c0000d0031600041c4a40c10144d000b032f1080b03083c9540841d9040c1282100d1502c0d081d295002138441070000b190585c20080c1c0740c42d48100c420606c0c0350010990800c13031441410000522161486100314882c011000d000a40c00400344070803900310400342d181102c040c42421600381d542081c1100020300081030b840c6000400d84212a01020b031011340d0041c0000f81340040c00c4c450183d6a0500515 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 347698120 1250 347696870 347696873
    0x42d08030a0c02061b01051006020715020304051302090d03121404052a061606060909150e0a1505090f1209010c020303070f0309080f0111030103030804110907210b030d0f02030403 79
    0x344034a48c41440c1c481e1288a809040020183c40c0c075407598070548000c0b01150b01d111001d42e001c000c0c1c0301103940c2070310003d2802c4003800d25600a0f004e00e80e03610f6007100080b0680c5c0705159014541c4440340d06c20307080802440f0001007000d6154102214041c00551280350082902038011018154415001060380340050046000645c3c03a440640c515100c009044c40c00c2052044500c070b50130007428100740411800d00b07155100d4140c50588a0000181661351109002c80300081c4131154029074007a035003c030351103080e1100c00010b1800f610b041849100c4d000454110401c0013413075030441c400020030380742000325220046071001e111302e03802c03a0580410f1219800060b1240d0389208001c0c46504c6500b1018101100c151411010a48881c880d030704200d01040c9440104003100c2c1980c0c0c0518210200351ba482c102428203a00c101e10482d00201c41004000ca000d5222003440702004c8490410348050001c0d42d242c20035100040b10040c3c1c107030400105e09104601803855603640c08071a0040e6407c00d80d8a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 347699370 1250 347698120 347698123
    0x20a0e0423030a0908150c0f0904110d0e150606280306030308070f0503041101020a150e0c0a050f0103230103030c1203230705042d08030a0c02061b 65
    0x22058407005680c0085910821560800d24100240c280f940080105416245405500c1100a400784908140004c0c02d00200e0065200301c40741c5a0000c0c00900040a1404c0f41700742c0c550049074240701e007618103245001d00340f501240b07007004401c800c0050001c944070030341000b410740c0c410340302c4251900000078100060340c0103014050303600115850014001c0e00d107007800b0740000b070003d00900402058102e01d2081c20340080642c0d8115401c40c40c01000d145001d00180c1c9003108650001c3c0206803250201e2205080704c0c4c0041c0e410030000401d54059a20b09014020451082c0c081c1d10b0380940b072001d00c40c4865100e54005840346440c02c0c0100c003040f10b414100601c9103420b03013080d40010000d19000c000d11001038502c500021781407900b001116040d02c05143e0021001004041c0311801c28042035407903105006683c0a883d500d1801e403484170300d0300038a60780400c0315140d00740c009032801c0340040d111a010060700c0d00e00d41d00d80c9988a04010b264200512940150030366040c40e07210402042c01d5280 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 347700620 1250 347699370 347699423
    0x7060318061104080f07060c030810030f0525140d050c1503040b010e0405030316111203010503010c020d051c060b04150e10020c090a11030f01030c05040504020a0e04 73
    0x2009007080e0f5664104030000d420078035100030a0f91203a01200040290a510400c004c25103600341c40c140c0c0c1c1544803141c0d014030b4022203a0000d0903c101ca2103402c024400046902a068032071340010104040c5400d03400d03020740b00c2c40d00c02c5014a60402d0015491070600c2d200d800e044a205e0307015210800c41400c005121403084996614903c4400700c05c0000f00414125860301601400c201c9e120300d850565511036981c40000d01701d14984460010300b171901401103074814911001e01c410f4405443c5003d034140c079140c100f407051078400d43c28039600b1110a40007180d0b95043c4095540c40c0c0d032400d4601d103400c01d040d0503d01000504280e0302c03680052160440c901800c003800b0100180c50070801442c90041a04a8140c4000d00c100015091607203072980028442080850680d03400700da9075a44c015500080203860301803d40d010f400000c000c00e56101184542c1603034803840440701720580f0390050208980d8202e4000350403030307080d003018007120700c2d18410140c0c0544a17500c10b42583d600d84040b6241c000c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 347701870 1250 347700620 347700641
    0x180e1207033f0207030306051c02010201050c030103020d0311030f0a090501021b091303020a0b0906072d0c050102070213050a0e061608180a0507150503090706031806 73
    0x720000250281111480c11151068116504001d818000e4048015a42a4040000510381e500013036003401c01d8040d4020f040145802003258204040507600c0d1040908400812801540381c6030010308806040000d0342d041e40c0e00603002c8002d100c22603405840610384c03661408050301c401c2c08414802c0e00400e000303003400881942e54040d20341c0741c00c001a181200320b459190841c1c100061300c616988410f0360181d4070800c20403030041d81042d035080a9003032800d105000b8100780060f030304004168900081b528007c4aa40c2d44404c0180908510245010031800d0aa440e510b013038103076182014400c191004a06008100051601d520b0f80d00180c010491580d40442d1282c480013004191103187c4104050a012040504254a0001510700515102400076814822894081543c5003404400a183c46035400c003110240440c6082c190f980e8900362080c0d68842035100c120915007481101641e00034000710004102c4103013030110607030160400100120116486402204c041081405455400c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 347703120 1250 347701870 347701877
    0x402090a0806071206060503060102120f0906030f060909030f03061011010e070f050105070305040b0a030902030d0206090d1b03081b13031e080f09031906020901020610180e120703 79
    0x400f005084c4d000d40d40f4980c030440034400c0900411107103980100301026448190005241e8410400c1002071aa004e03401841d44c02440100401c2000a80110a980140e10803651203030316a46500d07106640780700f201010b980519090004c100b5030f041140905102e1100c0e814000b0300c142d08603030001c1c215441042c0092007a070009000304504a90b00100c10040c1c1428a0908d02c0c0440d0768a02415501c506d2003105034001d07000801840443c401d034000b81001e0fa00400b0b803a004000903000039a204403c7d01c900105e4003803031414010882c00f6244519804c005818001c12404040d2010780364038000a20010701e18070803441c0684141e10140040c14000900700381d88541508600b070039400d41c03001d4a080c00d94846444e244001242e14071059900ca030104000c103030340d145041c0000c2070920780f0004001c215840d000440c4010414a5006000b000c3d600b85d00700c611655400d425a021103000344034121604400b01c1c03400612408941142d00000860022100308010141461603554407800060340013 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 347704370 1250 347703120 347703137
    0x63312090c12070501142d12060402120105060c0a050601120302060105090106080f040804050d0c090b040b0a0b090103091b0501080c03060907050703021f0f0e07140402090a080607 79
    0x30b1520340c100400324007101d40145681070130301d400605040001c0c201d8107940c4401182c0b05404803441049164681c114440403401c082c040d0058156079000508043c052079660380c0010380c607040920a4036900445040703041000e0346806d007480040e03031206194043c103004529001303000c00c0c41000014028560300300c2034404480b02d420000e0600106070402c0d07200d0352001c801003003841e40c40312250350002441c2a00841c4d603100d42ca0320490602c01c60340102d03004403125890605006003a0072020481d6011581804001351440801080390a802140703640214000c01c2841642400c03000f81214840604000504004031707100d4046c400313807810295010010512051205517031001000da00a0b2801c0e0125040d41045400181e86c03c1001f0609001c0050103d11001458420031205201c40f848100e030611581c04200c0c039102030141605412551400d0009010440400003107800448000400109072a0b441e0301c208800fa43c4020a50341d80304038148404210b410003072140314040d14654466168 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 347705620 1250 347704370 347704393
    0xd0f09021905010f360f0905240d060f061a0301080c1c02011419020a020a121a06040b03071202010318150c03020c01020d020d0506331209 61
    0x20822902019002c101000d06541e0200601c0180780b002d24101002800d40003445d00244103908405500a22254a180304006080c07980f83e070000740a0301405080680040b400d20028000009584503c1c1d00100001540380110702140c5c0003110b882d080610104081d6554603015440c1c44900c08a91100000040104509030040010440e101c41c291181052552a00b171400c804220b41d840c0a41070080b203400c170310800f001d450308503607180e03100e044071407a00140c1c080029919078074104103d01802c12010041081c07000c07143e4007400ca07030740642503500d070500180a20b2004c0e01c01906454000745c0b51000c20b11256028003205004c0c2c0342124241002d115140001001e4681c9150340c042d08004004110012520910240062001c0b1078004241100850803c600034441c14000790560b510100d084062001e40390000d01d03654003a21030a210544400301000100000c5505c03031103040d064005043e2280717030140d420540040800c0e41d80f41c04c0c0080d40041c504081001c8401101903040034010b001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 347706870 1250 347705620 347705627
    0x1d0d0305090a0e13060b040b0603090109052b0302160b04050d0909060e07050a020c03060c040f1a03220204050705071e03050315030c1c0c090b060d0f0902190501 71
    0x20b004240c601800d8400381044004814400c092440160155849500f11802529240c01c500281e03040502500d0343c0c0d2810ba0b0801d4020501c001040b1064052200303110703c3c9107801501c100d6001c2c0c04c80b003080b6441e001c03800150000c0d40040c9001c04050f000c1c00c10007000c14408400c06215501550113012861100c4400900c3c0e800c0c0e9422402c3c0d203900d818802d1120b03151300314a0755400350050500c240d07035180180b4207078036111850b10302552600c01c10b010821980e08400103481141c110b000e8007000c2607250304c042c254201c11282d141c944c00d070080c00000c404601c42c404000c000c1110101c50340300140160045001c0e40c10449520003ca1030028480e420002c5807085283e1498000c040c407415400103130340c010001d1002419408030518441006c82d901c0c2d5050005c100e0f844002008081c0310740c81d098143e100300c920401c0035201c1106400000030a0701140c00380c1107551800a02051a00101041d2640244442030045036444ea4400d580c40050311045e5031051001450014888114940740005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 347708120 1250 347706870 347706889
    0x103151805011e0b191e020c120303011a13170d1b0c030201140f07140d111c0e060c07030213140406020d1103040606051c02030303071d0d030509 64
    0x6a06007240d000c01006441302c40c0003640c944d0f9180281008000d46038810440300354103148070b014810150241a000c6030b98000640318609601564400d201c402280402501e9000911a410313854003a1010f184002e080c00000b00003e909920494180d26110031000340ea00800e1144500030b5408042c0b014100ba40080c5000720001c6403950300c45012103560b94042c8545140c1c8002810f01803002c0c0400366031081e0130f040c1c0c0e499043c4006134a407a0705107418003803100030a00701a5140c0d80a60084801c010707200d0500400c20348400c00040401001540e600d46403039a42c01e44010400850100a0b2075540c2c130440240358520301c620007880c0c86810750040001050201035108481850954030203d00c080050b8150343c891303088103005031600d424284081c050a2103812804100070000f04000401c461540088240e130030644036480b0307451038034100c8841080e110300080c0d455841031001480180c40703040102001c003802e52810082c8142000030034010050310004801117000440c024495040c80c0b03908 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 347709370 1250 347708120 347708159
    0x20705031608100509010204051009050405010b25020102012c060106050c070504021606020304032705010c060c0314011805060f10110102070209040623070806010315180501 76
    0x500c0742003403415841503540e00441e80890300c1e0719110400a00495001c0d419500103000c050440582900040c8000b8400030150207414419481c04e400820100c1d03054040d0b900d0400d5041c05e42d46654080b41c2c10420324030350180101d04642d283c040300c2e080018a1514400600b8200c04a24441203100b6551802c0c828160041d1041060500c0800b50390701d00010507804846054400598910704503059807102c8a10120140c0102c0c000400c1c0410103a014008000c0a44802a40349810f1040060440b081e00144285800110742403c200c02040c0d40b5403001031405000c0c100050384040000380c00c1d01405c1c09900c00c040180c0b070002c0741d229801c1039004065014108a501c4480603003040c000507020f000104a0b0410800300025441b60340100754100c503c03071750300246548968070741807904502920540094a960300e255038a440d00300b600c440c030902c1c000c44868580c6201941e418004500a181410540b03d003003002010015402034400c07030782e500c0c03517880fa000801c00d0340c1802200418038025044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 347710620 1250 347709370 347709403
    0x12061309050601061803140609070b07021302251112013c050c09040c1b1e17030f06030303010312180b0a11010501060e09040f0201050c030a02070503 66
    0x44000c0000e20100307840c0c1c10340e0024100f0042001501d41d00c007004c5840d83d00000e0010520905641103070b500026420304c11568041150f050b5030715050380400d41d01030050001c1d0000d8041d10540080e08881d0050720f80f00a80c100901c070030b00d2451000390b01040884c00203032000ea400440103200e0342409286411000e001c18024041e06104003600c11458882a48161002c84aa042d009860140004151501e9010102800340e400e0210000c1f15513403148480d10700c640e1030700340034a40031405100000e072445100d030449150103060340c680030740d82015142094007913541c924032440003a00d4240c103012240c0000305125140c1c6490144082148000780c1840d01c60b03441031004200141100404004c40e80c0b451401c040e40c0d880c04010b92021480b190000c580992003c0340500d130103503029005807800c002ca50001e1100740d80e204000e503a58100c00404581084c036590004e404900640c021111627403040c90258a0107410200e02030460f00082c0540c401a080f1020801491600b00004010403018a4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 347711870 1250 347710620 347710631
    0x3090b07030801092c03120f190b0a050d080304050d0804021c021c03030906050606090303070201140f0412050c10050a030b0f03010c09050a1401020c2103120613 71
    0x1c07405094003105225150b103060700c80c403500068203070044a070f64440c9050303900c1c040c04c090614545070306c035002050b1a030480c0301c0120004040860301c0900c50b002d040030385e1581e900080465066000b0304005d0308201e40140c20254005501d450709a2142038060003010000e84900b0f2600c0e129050036002e400d21000c2203200004e1102580e2103014170687c81c107003240442e071100c0c0c682c8045040e0400e24000d0405001d120b0500038145a0140c120300c080304d2240500700007030740c2c0c0e003c1004400d000b510b09803609503005000c1d210065001c1d900700444040c031002941d06101c0d004510964070340c004d8005004900b4008410000c200e800c1013071705442a0101d984886083d01200010918064200f1940416480320040350ba00d868202200c0b43ca07043c00b030002c0c040310255800141c12000d440c49030304c0c0515112040001e1404201107400f0131250168050002001c240c820030070080e4a0740000310780b81c5400200700003200d008100400080044004072140d62900d20100300404d640c00200510481c02c02c1c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 347713120 1250 347711870 347711873
    0x110303040804051e04050f0a05061f0513050303070515070918020d020c0604050d020c0603040c0b0a0203040f06122f0a020118060905070501050a0e09040602121303090b07 75
    0x194142c4080d00c2090b44c0c488280d081040301c2004130004c0c1e010241e00203242800307000f4000c0840c90f1300c51003258202d40500080d2216400d0041c204046690200c0d6184803141181c6110300c100000c2035085154461a007140761184e000a00f1070740210b00c11111544200019a00d80d0075500d881640484a0b05000c07105503d007071403019540c0c1098242612080d0b0000c0d080c8025400d6505488851101038100c405500e051b20b4544e42c2c2d81902c00d01c0c100540f0680111a081c0e1800f43c088904c51540140c4819203d0b2810255040301c0e0072400304a010b6020611011500202d44185140200403540c1c841d140501d6215074a011100c01d00b10390403580305140c4824003801110085000000c4d101020203950b91090b80d0101e0040c16088882105000000c5562091100d181c2007004003030b010740142d5400c0307a038a6005580034417400c1c4050021800d401c280e4203591500e20034681d03005000d56009442d200c0c06184540b400780c02160032131020300340c8140f02c0080c0b41d0320003511009031024041070751810790a03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 347714370 1250 347713120 347713133
    0x70302330307050d02070c230a080109020303090609030717030d060e01140d1104060e04110108100909081308060a05090123040c0b040b0a0e030106030b040f020d120f11030304 77
    0x2c2c070001d5142e1360340016580080142901c2d03244010452030600441204000103800100c4803036560451081506c5413000c03494200611403c2c01050b03004004503e4808004c0038004a9040319559542c1030244c050001007158100704007545000030103000d196190340b659094411550359800c000a8800c0750b00040c019000c194045030015501119007011680962405155103110a84c41d180c00c13605000001541e440c9803441d42d0f0285200e9039600c40450404401107620440446a2404040640038101301c1c1c100b10340e2118000b2806000150f14104d0343d40d40d60a100101d80d8440720f1b0300e81c0003c0c00c0092486491280a4118902e04001d120550001c0b81c842010255041544003140003000402e0130009030b0108980140390620b16280c0f0396540362400101508800f103604040780005a000010f0314041c41840c082d03c2c1d0101c80801240c8440d1620221401d4111040f40c01400812003a40855030540c205030304007210707680d01482c0000000b001130103404000c030248660f51051080c400040d41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 347715620 1250 347714370 347714377
    0x4060f2d030e0120040306060806130b09030f070f05010516050318070906060302070302061e1b0d1b0f030615050901020304090f0902120c01080f06010207030233030705 74
    0x80c1d240109142c1031801006004102a400003100c8852090711500703000401d802401c100ca000789030402400d503565440c9a20b41d00d040300d4012100210f41c0351040003504413990039402541d00c004a17800d1071301144040d0010340c071410b0f00f135803020403514207101008402d00600340d0101c01c8010f45110032004407000b4003180400780c000500c040000c45114149541001108020018010b060201c1603032418094001d5021020580050140c40c00003014480c03009041c1d04d04900c201a045029607a604480c60b40041403e500302071610100024444401c8601910f40c0e6088101c0c6803c4620400d41c80c00382007420189046c006040c1130403003c2144114004404400d6811401c0180d501d49001c00102d0440c401c80e0454103000d07113401208101e04060b40e100680f454400e031034181c2a00c3c14088816501ca40e1400381a001651440008190441b80024940c10400c10b004507001340c1d4480d0b000804803021240b490724485c0d2040e14208246000c0c40394400c0c00380c003200d40300c0d00c0c60501d04801002d610 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 347716870 1250 347715620 347715707
    0x21906050420031c020c0a0f0e1602031603050d05090d020c1503040f260a0311040506031303110f010e06070e03070e0415050c070615050a030605180304060f 69
    0x82e4040d2550004a001b0301001100c40c40007031659590f21344401c0320103a90320180c01003018000011002818074480d070346810014008a4004505200c40401c50b5002001c03030b54401c41c2041828000f011044c002030040307a024030785400141c8409404c0c4c1400901e4400e225844c1803003003c03d6580200b11041e00d5044036000b940011054000031b030181007006401c941d0842c00100065030300200c1c01d207030304d1540142150034a16038042c4101a54101074134664051402185c2e403142040001c2400400c1400100b5405c0b8464101440644418141305080030710400d00d4074440d9444500c08038100506024036540036039281001d00d488400f0a01080e641d00a0303000f2028803009407000309091082051506c13490143d4000188a586044085038100d9041003608644250420450b40030500d040403d100665001510520740f091441c3c03105409000007074100f81400c401e981d0400c003800781c03d00080000d0102a210704030f411030100b000501e190f60f06800100d0b1051100251880340800c0203004d030008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 347718120 1250 347716870 347716903
    0x1a011202060f25110604030b37020919030c0e040f0b040f0209070c050c27010b0a18030209060402030a2405040c0206151002190605042003 61
    0x120700340b02a8400a1007490b10780b80c0111a0790407507080004003200070809440c82282032102844a600922105000c1c50200902e880c8101000940f1030071101d10342c1e07111045002030700c1504000354a007002c0103002d8040f10300059400140001701c0c6c4c24911109401c024250071560803480c51600c50301040140e078022400e4510301c840c045020310481044100e0a00c0d0011040c0d50f540c1070078038050150084c0c164089004c3c0d201900020a1280160405400036820038058503011f1200c50408c50300315140e100c0d1002c0740e2060013182c055a0008941c0c0f030301038070802d50f41d6560340f450380501800c42c030001d442110407040303048400d00058072084445600103000380e0300540c9031380383c62414030050000c010092281e06802240c0010182446038030718200c480c152010860001d401000300d844140846940c5102040c6890780c01071801e0451841b5540031903407058175030582e203403121950442e100c0c00d000e80300b161707e40081c80b082c0041c450200403025010200e400713506251038040f81e01c9500c2c42e03a002007003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 347719370 1250 347718120 347718127
    0x100e010f0614120c0a0306082a03030c0703080909011a04050d080706090303050703050907030b01030803060a0e0123060a12050603071d041509020a030822121a01120206 74
    0xc005424041e0f0348002955805640646080c00f2403000c0790b0000884140040c1c10710317800040c6000d0128000801c0c5038450704940076800320b10050307981c098400300c946400d884204480e003010300c03040c010100a0351150000a5443d90100b003006800d8030184c01c02074540503424100050398184c02c0403101212001d070ba01400002e0f15090905d41d502036401c002c0e1015090244030030030150305030710a520410464804200c0341c3c40e443c04c2d942d92112a400b0003001030111100620101c0d451101070341c0e200f4030040081c00b15584401c0c0310804503e0a0b400803082e15501c0401c0404200d68030b180a180384c0d0195122420000c1a4000034460784a09101d0812255550b0103d245624140041e03400707040d0088a041078031840420a00c001e5900703d07000d640415000501948055460040085007500103140c2060f01c0e0035600e401c121603000d82c3c02e50100001c6100d0b66400080c65001980040c0b417050b80c203031600e104600700362981420743d21980100340705040040c0642c05948003001403040c0c040e20030644 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 347720620 1250 347719370 347719397
    0xc091b0712030b180403031103061005160602040608071103030f011205010f0509370210050409061502160522060f09290f010509010e100503100e010f06 67
    0x10041c041a0a4118000180130504180c5401c0d800340034504c203a4040000040d00400411203010680301103900c00d08401001c052248510003030700c01c0d404840111070700701405945010891780a03a103c1000f080c07202c403c00c6405500041d4080c141c41c5020003031851454004d40000c0c50000c14002c0e00720390b0307a503d080c82050200950060851540905e0b082081e828141e01d00b903507c400b540001c11707224082c00101405a081c5c0f10300d960000710700d019010f00074040f035401c01c26220200380c400c00400909102c002681c034481d0051030018041d100003031840514051000f800c0003007040810549a002900c104450703290b00b89040c68143da000ba6038404440700400200c040c0c00d603036004444220b40514081403903072107a8048a02001c8040c820352040704124541c0d07845d540c0d4550030690200ca0980e0070b60080d40914020040d400c81403401e004070f0007c000024a580c402c010448000903808001c00a00c801074040c130030090850721050501543c90705100c0341080300540950010030103440349002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 347721870 1250 347720620 347720627
    0x14070311070b04061d0f06040201140c0d08010317031311040905070e0601020f07081203060a0e0a094d060406120c050711190503030c0c091b0712 64
    0x60708030b40c0c07080184081d8203042c20041c018002c020503003210701e08a0b9450052200300000c0000c0120802c801400448d40d6030380041d11010303802050401c100d181040303c400e0954044c0126003000140c0c1d1625012035046050030408180c82404000c804170080080c0110854450741c11440c065006503651068035107140810b000e016030060040462090705030100e4070040e8582c81c584100020f9084549000e110304545070f5070700c181e00c00d0304a150032114a4203603c40c2104019940400050f03d0012a5660f9902c000c3c81041d040314080104c0c0d07035403500001013080c108101c0d802c5940d0103094050300c0b9080c138450944414007028003070300c442101c801c0707420b0040404d044428185000f0300352600e4540d91580603041c065500b060003aa07502c0d0096440c40c1900807403c2d19403143d00310742c103c0c9100356070006010031000d0020100100c040070700c0e40000c05a90030402059010b1982018100a84401e8184251445d010f0110600031141602c00c0e505403070303048113441e00c003508041c62030700400c00c495066 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 347723120 1250 347721870 347721877
    0x6031707050c132c06060316090903261b0c0c0f0415080d080c190507020d0c0b0d150614161a0708100b0a140906040807030308010914070311 62
    0x20b0100540c1c82142404ca83c0302d031403041c031141c901e00649400d990740b00f08240d25070b441c140f070383c10340b444146109201131010342d80b1201c451446801d0944079030725076400c00d9184840303100315441e260088000b0410341c49540012a119100751002076414141c042030b40303e8603a0301c50403059015885040c14011135550340e400034030041c51514000080e580e200ca4610f40c4906202000c44003040400e001b140382004c8900465880a8403100440e5a9550303042c2e00301e800d94424082664480701910700c1e60301081d2003000c2d05004210f0b1030403003a9182c0308a4802c206542c40c0b07012450b1080007014041001c6d079000050440e804482030b00c2d207583c503100b2642c204100504284068003403050800e02c261078143c00000d007405503070b20f62144440c0c0d6176a000101c0c44c0040303501516641c0d05d003d01840142a00030023003d400c0d007160307607042c906040f040001303e24640c201d540074040c90307840107a00300309240c3c00100e1315024003000c2105201c1d0424120126641902c06401c5000b007607950240a01908001e0081cbc = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 347724370 1250 347723120 347723141
    0x1150c06020f09010233040302010f11040f050f0d02040b060c0f0d080a0c0e09090309191a072105090316030b0622020906090d0606031707050c13 64
    0x210b46608242403041116003089410a000d8850b00c18001c1d24250b9403492980141085030385000c210402421000c03101d58054021010f6649460514481c3c011a000d14062802e00c50452a100da02e00041c015002c00281c1c81180181c20300e100e0941341d0b40b01c80010701021501910041800500e00c00450040c1c4070700801d1000c24010f08074100c0c03000d030380803c0682c8880ea01e40c1d80d46005880e103e5000b8210b8149008000209841c0600700c41c41c1c2c20f000300040c0d031160003c01924105000300c004030340101240c24842c0c41d0803a501200b806403c6511250040c0184004111406d1001643d03030104120070148980071a000010250031505100300111260706401070207030350601c0b20013801c00000420700e0008461542c4440d001a40504228100d150f480c0b41d030102c04c51310068000701840003540300102c801c1c0c10820805c42c840281d140c01c041500c1c21841940006002e6145041c1000600e0401483d2003050703404105040108100082031190004e046416042103800b45d000710b0004d25131440c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 347725620 1250 347724370 347724383
    0x90703090302190f020d03020703060b0406080307030e0604080d02060108060702010509121c0f0e210a0e0a050a081c0804021e0307091a09060d08250204021c0b03120301150c 76
    0x1b10f6004040c2c1c00f1510100726403155605002103800c4c08100410f5071154052941e565000b80000400719104010b0300c4054200500a00d28040e1920300325400d20030356540318409a4840070041101100c03c003c82544100288020802e909048004985805106001d540418404120351005031860b40e050303c071200d5842410002d1408082407007016100d0781100e90014020840d0481c40911074804000c000b2441042040c640141c0e90f0060751074a41c40985e481d04040b2501003c5540d49400d400007010b071070642c00402c1c0d002ca002c190602c034a62520307000001c2240643c24000140c4815600300030414600840c0e10b005140b00c80402d2912181d80d000018203802c01e05070066410108164440011003914101100e503160400d104c0c2c0c9492000e8001e000c0282001200340180e00340c40320340e13516042141c0c190103c0240340c00007010781c0c1100e80700000b50503002c1144448004180308240d001c0b0b0301a00030381078001145604101070b0105204036542c51030720720ba204150a01c03400300420120360005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 347726870 1250 347725620 347725639
    0x90321040b180111010e0d030914070308030906090a020303040b07031e050a090503070f0b09011b0308010e01050f01091809061107030e0a14100e090a0b090703090302190f02 76
    0x1031041100024440b0841c04900c044109601610703060043c107110020b02002400341e540072070400c600500d5504030a86d051041e16545c0c003440801404040019406603150725103d0410525040c103045000d0140142035211506010040c1c8006c010f0710100e80c0b07071080086e116030050500351185c400030028041000c541400c0ba0030810b41110203000c81841e0b958507030100503212411726943d140c45000b500e01c1e49540003001c100140420000b4010344406150140500c540c00741100e0841900d20003c50200702c0d04801072143e15003004116004041c101d82e107002194000b00068420f82e09130181d440780b1001c400ca00700d00c050440e0022200e00ea4002d2082003000401c0c80c11800c10380201c44103c0001e0710120746860a460106141000d96804210400cbe1100050081002000709180703082c051203080d4070b5195096490428680c414501d50700d01048004c0c01c10300300400400014034201c14945410300c8035000c42d82c00140381703000300061f4404c0b82080b940743c24845030142c08070000942c05141708 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 347728120 1250 347726870 347726887
    0x1208070c0e1f090e0709020c0f031b0105070f0804060e1e032101030510020a2a030201050108010c1d03030708340f0201120f0c0507020312090321040b 66
    0x554290503405001400c401d5025103400d150821350b6082022440141d200308000d001d40700082d03000303000303040d0b01c00211920408101205030a5030002c140030b40034584c1c07800751303100c0602007801180d50209551512521200b0f61900140c0f24441c0a40090080c5684003009103513030401300050a82ea030400554500908001080a82d43c2e07440803000340348000c48210203c400c4088113100f503040c0d03642300019040000d00401c1810094105203a841e0801c0301008640380368841617643c20802c2c220500d02d52440100904001c1e00b5941e040c0e0000c5410385c540600208035660210081c0c0e0100c1c449000c520030003c00200085c95401500300c003410407140021445001844c01c040340c5c100d0080b00e40780080f13101d0104001204109200d001806100c41e0300d51100041d8810200122218496840000c5404060a40c18101d400302e00ca100081240011940e065140810441c203540c2041044d0614207181000070907100d40c008107101c1d4080d424204501c00e000e406109980103048000a0280c590940 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 347729370 1250 347728120 347728141
    0x40b150a090e0c09010506072009270d0e10020f061510111c0c140105090c0f030d03110f0a020717150f0a0605030613030314011208070c0e 61
    0xc0080d0340c2c009100d54034030150f8a050008143c0d0490b117000f0001814a102610b409440a00441e0750b54190925511085c12503928100080d0240059945500c49907914411030300c0b001001c004801065400b41600da5007650f448014042c078000c1c00d60745039946035002041079203404000c04001d2043d0003031008000d05495400201c2800311030443e00218181c1e003c082c00e59482091841c040019003040904a508203c002d9140c0480c3c511490700070301a200326100c00758160001d11a508690351603100380300f80d148042041c4800c0603400c48002c13003500510000a40e864001c070072140241904e6269040760f0036103040a45440507901307201d1959803005264029103c8030300340194842c60000c00c41d2583c000c8000280d000c00380030350880c2d0480588a0700f540c039580040040c0301204594840320003040f191014002c0f41e000e0820499092000342651030013400703560144040c2003220003c0e4004111003503040c41007000036070700031212640e00e440c1030910740002580d907008002042028020300150508 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 347730620 1250 347729370 347729381
    0x60c03041e0f06080a0209010c0b0403020d0807031a040b0301090215070c090209011209023f0d1706010309021c210e060c1c18120b040b150a09 63
    0x10041c400784600d61a1042000e080400380140d10006201c100000c0003a00554010000700074141852031800b00e56a65495008108840850043e0072262003010b02542188009030032801505040c000340d00d003688103000501c283d03954903120341c0e10380c40c201d042500c088d4450407416030003800944822041d5100340440c1c0e4030440341122101c0400300c00090381e4440e032080c0c5018810503502c150500204001c0800600001c141c2070f0ba21000c4c03641c45108500c0002c4010a440c800c80c1510a203040d18502105920318070a04c07100c83c55004031031900f40039075100440d041c102e090340818031015196180100c00a08200100a40207010300c0d1840b00c442880d60500d50b584d03803044513400010301c0380e80910703c410001900c4420106c0d84690303020040b45064006465810102d50171544410008a010b0310800c1e00040800080750340480105d4210b192210b101002e0b1109044580900109964161415130001c0020b408109070340e000c5070720b5a0140120030310301c2d40e0080110040341d480f0b035111001880c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 347731870 1250 347730620 347730659
    0x160f0503041407030311070608070c110a0816060e0603040b0c0c0705060708030f1008030a0c0807061a0a080d121112190f05040c09090f1406010302041d1b060c0304 72
    0x305400703000600c948201c02d100e11400c0107039901044242c207a650408804c04cc141801e0f4000b618050100301e00c0800c20144812010160007585140d20303043c030281c1070340c0c1e00142040c007440c0b08004000200c2c1c1c080160540103004424040d9481d50202a1641420466040285d0100b000181da8092201c810060b44c011035941c1c3d80b14803652101021a40880f100d4407a86040d60414000c025906001d21405002240240e05917850041c0954400084603204125090031840e03c501c41640c6041c00f10f00b80c1d0151014500034245075822480150420840400d6030310f0007a294500d5030348a415181c10788031050214071000e041402c2c0000750003221403051800c0d02ca254a4000c05900c80c186601860380115085046400901d042015400142c40107003820f56007040c01c0b40301080040e10319490103880c0d4100d04040c0c0102c5d4114030400c003e4900e00c4200300d0310700c115084020b08112011405240907140b109a90b0800070107107021a905000b02c030101c0e1024080443c001035011950803800c00c00342c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 347733120 1250 347731870 347731873
    0x70305030f06040e070e0c1201030f050d0212220315060603110a14090a030f0309081b0f0f12030d02040302040c050307080403030203042f0405160f0503041407030311 73
    0x2951040140f10448805110309801075000940400c20300310042c146540140701d60344103070720b02009003c41c0900d0542c280d0045400341d4050354204180a820b0210840b080c095101070710003011648d034001a240640200c1d406844514440d6480c607003051031030347c00156404a88004400c1780c241450300200301a100b400d000c241030403007040b0400030749000c0b60801062a20b9585500b10001084829070700280c040540000300745101002180245c1100ca00d01131280d07580351402c034200420941025580d0841c0c0d00d00c0a480312608109a48140c032031030f0f04940030fa0700018141c00c15000201030090030090341c8a01e000004030320042d030106400505c2641d000350303401d100b1400e082508903618030023200d400d00060068404100007a11030b800860700180030300401c1c489000300310481e076a070304070301c4404040c80e90a0107491a868140b5004d80d40d0310100c40c4243e44c14540741c2200140044038660508000c200d00000054100030040150342842d4800070200c4848a03281d15000c1d001c1e403903032884034605 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 347734370 1250 347733120 347733151
    0xf0411030c060403060b06130b07030905041b0305060d0b011d060328031e080114040515040f0e070f060216140d0206091810050a150c0302070b07030503 67
    0x908000a0042400384054016481c0074510f4807150000c010106e0190303445003041003042204122041c07604054680b50f20080e540da6407510b40640000c8440c5c2c881800349041900e080c04001001c0391710f0003802c29909010a1a548180001d0b140d048440c1004158030716803000400c1c80140014682e8038000b5513241d01c5590303100c560030559501d001d2207400c10082d800a440d107034501107001128017a94482e040c00e5111102178152075440c1000268640d00060000f40100070241c0e8542030400c10107400e440801090a0112a0600c01501400c609020395150000c052228015601060b0038041c448251803d6076260280c3c8036a402c024854040180710344045148040980e0013404121005202110170042d544801d00010104164042e64406024440020300b6121444824070880c45400074102c685410003140704800c5840d00484e00454010301c0c04c1c0104e10b0501c05a01400805040100d4911198a412458001143c20202106002080e41c20403d0742050246004080c00540d2000303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 347735620 1250 347734370 347734403
    0x1909060503070b030928050106150905010302070528060e0609011416120e01050906011a1c0203100315151421030904150801050105010c0b0a0c05120f04 67
    0x880d02080d03990f0040e81c1c001000c0441103006c045541c00f0319240d0b8420800c2c2040303003602d8203821a10194880c10303503d2001d110940a00d5803100403003002d05804d0a0460805425444603680c81041640c0f410031040e040c1103032980150300c55005559968801c0f4103000d901c1300a1030041d16500142c910007010741c240a130003056500c00d0700e1418440d06149081005040c0c601d00100e4404510020a042140d51031a8089554800307015142c40340c90b04500400040d4502414002c00b0018030130b111141000c14004040c0c409060700302801001c8a002c00580c680d1035400d030580c0941e0003075200416501b080c820b40040001035030005008810510030404c1c0203943c580c05090103c1c24a00015480300c06500c3e88444840c840940d001d0310701c41c0c1004c50b418440c203600801d08640c41d070303a82020309400c00b4808200701306090203014003600b42841c00c000402e01d260341e6162407810103400c40414a449040c0d541d0b43c248980c0940c0c40007010040071400301d08200222640c501da0a84e4261044220543c1485 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 347736870 1250 347735620 347735639
    0xb0d1802060f0313021206180f1b061b0d08130f0308101a0903212b050f090c10050904021b070305060907090513060506190906050307 59
    0x40526802414880c607000c2680e41c103000301d0744010030700360402c501503088034056219217410050030201800144483d040c4091100c0b290300c0802c10f40f81e09940601d000307001561020501791401109014041504100c403000035105001e41d0f10300203035100d5290b68802c21004c000860301d01c07050132b544401240d0f841e5900c0c502e50641580c05d001d450441d524840100103880380802a0384000303010704c0401e00300d403181007141c685812002c00c1e201400021030217401600d404d10400d2031080d0a00d0f14555030718691002d0b01500d0144c51100e0302d48290222844a00301703603038003042e83d070450214810801c030f242203200348040c076102355015203452090510b266150700304444c001d941c6201c0d03500c800c2d04100031882000045e5100c0d808668000b50906c56500103800304010b03038405548500040d00091814881c250f20700041580140132180c103080034081c44607090141c08010b1500301c000400d15a40d10404902c00007042075200d103183c80781c2080000c812016a100c001a500c0483c243c880c0c40d582e42e030141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 347738120 1250 347736870 347736911
    0xe030c060a3902010804080c060c090f0118030f17030c1306030506130513020604140315101802040b1c0506011d2b050a1217040b0603030f040b0d 64
    0x2140480c203002c2c1908055070141e416194000d20408807e072920700345010341c506140043e50b4922903048080703080311040c541030390111140102071800ba5500800740d0002c2d1950643c0f031102601c7c03828a40f404d80284041c0042100d02122801c941d20754034104803400e00956402a80c0503211600021408901e5900c81c3c0507180c00348070000d0050b110054003c54480c01800301420304400e80001401da4401600c500c1d000d0001044c213141000100d010000525003001e00401e080c0742c020202e441004011480d0f0061003099a8554420103030310052166024020310030743d00b000306c41c801c0224402c2024030500524240d10680d8400512440d02c0f810010f42c2d0340d81c001c2020101140101c84542d08504107500044c07181d003102c605000c8050320b0504080001044104161364030b400c420703500c200340b107113211404000ca103403031600510f14400082d4926620a002e080201036510540c04501c3e140e804100b0b87e00180320600d603841daa2035850284102950100c00303003c0b401c60030700921140348810004803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 347739370 1250 347738120 347738207
    0x1903020901122a051909050c0f0a18091d0f010209030703020d0812010609032105030c0c07080319030605100212070501090609080a0e040c0504060e030c060a 69
    0x3c41002850315039140303036801004050424046902c400901e507510300804003616411801007507104e50038040e064068030301c001c002d2000d8581c10000685d00d4503140f021a101141a46889581d444a050381000e0306220b55204014490030a110310b84090500314144000a0656044840c400c914281807400d07401400f241d41c2e03058202080810160a083c044a2820303449000d1951501c0d0303001060111650080e0040070000c0c00d119000d00c200321524500c21201c040d07141c04007440d18042a80141281f20007801041f810300041842095120100500405006280c082e070383c0f42d000c00340c02d0507010042890244000307814800c000030f8504020400e08071080447d400792030f4a1b80c0d400c1103100680d00102007203500d9907840c00e2003000b20f042849135640c507e10030038120b90340700b0b000240105022912040184294609a2446481900714045408440b11800c252003024480c000290070700085200241d000f220000d68400a50303030000c1100740c00c1032000085101012140301d480f5110010001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 347740620 1250 347739370 347739383
    0x90e0717180312010905070912320a0302010506270a0c11010504050102090f040506090604050a0f0219140f0301140a03050f010b0109051c110609190302090112 70
    0x12070425010411850a01458202164580180c109411408480c260301408a49944d80103101c5030643c030100e020000c0c41c1189540e001c004440c1c4582140d0000c440f03442c440480d008290102d22040d40082031701140c000820354091000b2403c0107406018103c0c1caa604c20038803010404d440c562002c81c11034144078100800c5043ea078940e280e60005002c02001a014000c1c0c5006038511030409004071803007144100e0001da11509080b01b8080a21a5551401e10a41c1131204002c03440d2101044c1d181d100008860129140d220305e200c007402031550000d151038050002541c3c031070000c01c2c2e41e000c1d0071009884d51802c451110201420300782c0e000700707040c09a03418001c000412001c0886500c05d1000c0f0b1004001200c1d6966136030356203141404030401d0340096511802c4049180d80c004a191009140940352185444298003480c520500a454001c00d4110402d00b1050252200d80649100460142003c81c10004a00f008002c10004d880120700c114074080000c42ea04110000c0801c1c03580e40504c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 347741870 1250 347740620 347740667
    0x5030c150a02040b03011203170106020d12050f1308041208070b010608060607061505090a14060a08030a1d090118060605070305040e0601020c0306013002030a03050d0e060106090e07 80
    0x103c461000000350105404014003280395034100300707032aa03105008bc501d540041c180400c405d1000b508859200d4442c4100910388030421948092b000056a44055030101080c6081070500d030464280c0a90341000c00c00191030300c0600200300a00c801006964014034145186a0340c442c0c0880784070608652080e00a0803d008403000a90940c10010394110296074554256131568040349a88804035030740350b00c090b218901c84071078500070210b90350451030a9948070341090030320119960301e00c5a054484100404d800c1d4440011807807040541104400130304829095039900344250517400507500c10442c81d450301c000060003038044c0086a0005505440b601d0030685401c00282441d032004101e42c0c15405182032640295909214890107008800c03d1103e403c00702e80d00d1654070040f0000d4482d208400e2502e8000540d40004842551550514090782d83e000511444400352100140008551149078004600d0740c3d00501c201040c0d42d10200622100d5454290483e840d00d4000858244058901f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 347743120 1250 347741870 347741879
    0x9120601050a03021207090911040f09021f0306090c02010e060705030f0609090a060504060c020d0507320a120e0118060f020c0303040e0103050705030a11010c0f05030c150a02040b0301 81
    0x6003160642c00b105002074960040d902c0ea4070000350382380200211440401c0203065142840c1600c144a8032201c0103c00700620105540841c074012040c2c1ca902403c03507901c40c000030015100f170300400003500d00f6810500c812030031650060302810010f020003140d401110006021144100d0642c2e100b1415003141c621252140800d000300345c9006040c5d01028000d804c1c500340858003602446018601c100d90000304541d0401d40242810b01080489040000804c440c9021620518500803240c20b0b440102c403540c0d024901e081049400401d0509090080c174443c1014420f1490a00d01203a040d9280c50610144000c01103d000311494041090303c05a007500f13205c80e0348141d0818282ca403560048a03900802900082c0c41c0d40c000f80c2c44003800261140051003040301c1400f0711170080c18103900a00d41d2542c140e5034151210f10221000c0c0c104070710f0800c001d00781700c1e20340940866140c204e020f5a9440c000500e83d680c880c02d181c3c0c4c0100810755482d002c200441654400c460880e100c0c46045c90642e400c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 347744370 1250 347743120 347743129
    0x30d090c060807050a2111070b09010b01020d0e10270906050f06120a15030809040b0907020304091e0e0607020d1d040b04060504110705010e0a020a140a0305030a0509120601050a0302 80
    0x81e039035a1000d83e2842100c15914507071f00101001c502a101c221401e140c108211303400d6403100d1004604642219803200c8540d508100791a40d100c404413000c02d100c5000702c500312181e6246031041c890039103901c99a10000704bc0070030300000780c071410a42408150345800c1408045a4043e0400e50804401c0042c1c000d418958140036400050401001c16400101c084854824903c0d40007541c41003400514141d02d071400b88030b1407a050364266002c0410386054803000c0e4072400f507032007100d6a0070707121041c501304903100404000e014641c1385070400050150350240c50741e5036001c4420130094402c103505055001d00501040e026101d4480828554100101c24403001d00342d4001c489070410b494180c0801d0300e035528000d01d1040503260403c81d0b00c0d110b032820101c0c2510740c8142e0007903450300420300007000750b103907242c003070f4281d40064070304100d1401c010300441c0240513103a101030440d00020405900c55540600108001c000c01c81e000c41c902d0552185540d00c6100a1148541c8a1450b40c002c0006062 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 347745620 1250 347744370 347744417
    0x7120621080717030a14090604080301030f0510110409050702060412030b03030403020d0f03090909050c2101060303110d02011e0c020a05100617060423030d090c060807050a 76
    0x7150302d049000c0e10700d0f5000c446960300300350350b44480580c8481c40b92405041480b03c4e43d52041e20100245140c1c245910b5241c613911042c0005860202d40c8051441071000410914401100c403003420001c001070300c1e07070001d2203411a000c1c2c40c03c403c1c100004aa084d91002900c103028640240e40082c40064040f01034004103101c400d0745405000511002003d6a50b001420340c2084c0074640d218024181454001c00f08a12504102d16483c41c11051001207000020404008902070f900800303403125620343c0b40390004955170840d11725828868017208040d4400708100000c3c1c3d19504031070b12a1304d102c030141e00340c4202e80e10858030700079038007a10207904006410071054500785006903144046c058460300d00300b6240903050221035444500c00c2007006261003180c030599483d02c01070f00c6103080560315807007803a035005030307107401c18001e448030b01d9035088240120340d100265000c0800280055241511141c0070510a18001ca10364500140100d401441124021a800d558110b18491040e411402109 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 347746870 1250 347745620 347745623
    0x1807030b15040306020c160803040506030c0912010605030106140319031704060b01090b090108070f030b0307061d03060103020102061f0e09010b1003020f0d09150203071206210807 79
    0x440110a085007a0258000303001843c020748000d0f0ba50705800d09514502418418207610700c900c5440100500c2c0e00110581341034600c11140d59070b982e10344041840007030007044890303a03100000c1d04000c0440c00c3e0540c081e07c100c80044d00203001c20b603521700c0c40104195507180b506805400100303c103030380140314031806a1510f01c40d040c50002031850005145400008a60132141c0c2ca40d0707954403024541c1c000450f10028803420424600c0c200c88040000c1100602504140c140600702c2040d4400600070342100d050284060f080364030090303880e00b0081000121000103035003540918091074050802060b254140e80c0c06070000c00490302c0e01c089840d08882070084041701e885900381c02144018100c141c850040362210b00104010304e90303504000000c0d0140441034103241c4100180000081807200303540d43c251000318002918001810400500c0c100e444000402d944000100445030b40c000b094800030390324060040201d0fa8442c5e985407000d25034440d0b102001001103800e5000540740c14024100203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 347748120 1250 347746870 347746879
    0x20a270b120702150c07030f0909180b0c130b03040f050d091d040309140a03020a062003040f030b06030c090c03091203010f031118071d1807030b 64
    0x499440380810059088000c1110900c0244000d20800a41c10801c84400c0200e52050301503505288a500710f40c3e03c240348006082c040c007902d1320702c01c10303004084500082000800900c088406242c00d0301c8011800c00c1c00300d03075015100e004103814410000c140e501042020b4104242c450502511030041e810043c811106d01303203402e4444c0b001690a20900590f907140d615517038842420400e50090108801050b40d448019000c20080840c2d40440c0440c21138044000900c481c0040401185070740031240c10103900001c0040002aa02ea40180d0780721000c0301c00903400c004080d54003406074480c4185d00c01c3e0010340d559094240042810140c00c1508650000d040380c0005000501040c11010111414601c0141c0441000750201040c4007185220b81c40d0749641c6d245604080f40200c0313100203404050112101007412001684032041a52210080521350138114500300c0c40060404100c040803408404400c1220700aa081480c080c114943d28620240c405075200902107004004003014191700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 347749370 1250 347748120 347748197
    0xc05030f0c071e090506100c02040c05040b03040b010f05010908120d020d140f130f1b03080d0c020c0103090210080a200705010501060212030712060b0a0c03090603020a 74
    0x7190b08040129020050602e040600f03a150580103c00c690004203124060000402d81852580d8031401c006070541e030403240020000e00003001120b1078082c07500928a040000010300040c4023110202d103040324481490f00d00742540324801140c050807640b04001095201c4841c805010201002400baa03001c0c41c1e40041c02c04040d588268250b980541c0b1a00e41c80550800740950b03e12094240c40c1d2000c48500880d1500b045541c60403452011036201400b5042583e0f00e460824640055200046800903601620b030030b5201c0074800144032981802c0c01510802c1114030807035004c1c1c05900c91042e00148403080c030030303004042a60701b1200148000324666645180c0a90350b07446a0700c00900101d13018003a03440b82c81c40d1506a0840b1010b0704400f0540d0300211a14400d22024021254403600e50b103000e00f12407280c0c5a00601400580e04204501c040c0490070203004ea41c0040b00a00e86402a903d0040701661500c0c00e400301d220b030041050005068505031014442c0400310250607285d0b6034003a044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 347750620 1250 347749370 347749379
    0xe07050121230708250809100507080f13030e010c0f06051f14060906130515120f010509011712030a1407030b0913061409060702010c0c05030f0c07 65
    0x10b410b10440203501c181080d079030034080501c3c0e1040707419a00c451080e0107050310b00b50801c01240c4100c0d1032480082000f06007000202000800e00208000d901e6646003804a801c1504e405056940c00700d440c0610701405c400011a03040216409200668051b100c0e405a8101304c3c0c011201c09202a80c20b03110141c10600d41c0000803038501c2100e100e03003050249034040d4044100401c0c06000940e2103044052480089030300749a407420100d661001084461640e42c5141c00c1078035801800729401542c1c03000401d01c000c4510040c00c0000d101d101c048489052581e80c41d100030464180d801c0c09100c1d00040c0c00401440b600d54114800c0e0001031401d400c6800e1042c2101401809510480e0300d000e010791035a04216039030700302001032a0858001e007070074455851414041880202c0041c00c80a110820315201014031500c1e41c001602d840d10300d184007003d89000040c0a036559002d0310106c0040d031800e03408610030351203013402804107640304000d1480c1c0840c0c1641d48181d41c01c0054060348900a00e500040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 347751870 1250 347750620 347750651
    0x80c06160306051806091909030801180216081309020d090203010c09031e1e050c0f030a0209010504021b1b03012d05072102040305010e07050121 64
    0x14418800c00c0c022100ca05280c0304010242e40c250b6000d64000d02448840304440040090001d50119042ea0040c9003507540e50000012042280c0004600c5860701c03841f0801e0503840815035058620031008400d022540c20130b5402240706945100700c6803801000280c4c000340780d41c0020030300240381c41381c0640083c0d1591500030880c1d1000074070b100e8240d038410044045060030301880a94036282d0504042541c82c1d5158125070800c40c801142d501c0007100c40000400640341010954640340060300441d13280b041c0b03082513841440c0041c042c4224080c0420a5140c035000504141c40b550140c2a50b501e0f900e00418803000e900700500f6400f00c038074200310802320200d00700b0544051200140d44020003c009a062508580b44803a00c0104c41c0454a076039030f2420555001074442582403040000c0300c1e5902c40c03044900200c41385174071101214821444288a003e900a4019203015200801c125224110310701e42d00d1503c0e2240f2030115491514410601d05080b000d0800380400e040c020404491940144 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 347753120 1250 347751870 347751883
    0x140c07110f1009140a06050316020a0b010605070b0907080307020909030d050f0a050a0203060105071e020603133807090b0d0e0f012013090207050102091305070503070309080c 77
    0xa80c0090300c01c140c10013420a402400d50409141a28212145400c040d0018400d01c0000d02c0c042c2010007441900c030805200b0040c5500301a00400800c0e9196142c4000501643c81701b4029608051106c010410b00302c00030503c141114826402186884440d40c01d0107103218000704401744501040c80803a00c410010300401d44140480e090038410f03072900003014012140090603014101d071040c000c111540c0d81000c22140e41030781092102d80c82c9a1542c0f074558080300803500c000d4010742d02101f84007040170304110f24140c141c0b00360303141d4a04044d030ba5a032041c040c1440080c40305907815070044018640e284903015070811b446107040c00300141c89821aa83c180d01c002c80c01c000c02603445184000005007400b06011000070f032002403006008490070420410b982a28100f13007104002481d04a501d540344114004281e000ca0540d00e4907640d0a00c00d000f9000901028028448110400c0242c0750ad8880c0c0c81c81805180c45a50541e11403d1044006212a1204403110842049280c3c45175000b0850f4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 347754370 1250 347753120 347753149
    0xc02180a0c0215010e0403050706020d0f05010f0b0c1e190305071e0309050103050901020c1b0406121e0309080a0507090e070b040b09010905100305040501140c07110f 73
    0x40784075110790798002e15018445000020101c2010010300c401c40200d102030ba0442d816140550b1140c03500c0c1404002482400608030045141c00780010840443d600320504070f5103529610b03041a43e44070084240381c8240e80503138005402c80700360720b440c15201c41c9005009050110494441541a0003484103525021740250003003440450200f04001c02090407402290944080c10107803442030380d0140200c0e03050300410703042c103840d480003a032046c50950540701030740c9105d0300701c1d01d00b41000d400c1541191150b141c1301c1d000e00e00b08000030032208031601c4c46207005070b44803c940021a00b641d01240000ca00c07403500b2410800786980018a04008200c840d040c0782c054005050018500381414080b1940100c1c1d0107625040b0f80810006042c081065030b04981d002c2002719501c2d0040401201c031000c040e044541c1c811070054032400702681c1540309c40d1007140b03e04000c02c0001d10b0855040703c1c1402c00c403030701811a0350401c1480f0028150905040a100c4064905200c00694000094914000715407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 347755620 1250 347754370 347754391
    0x306060a0c0c0308092b1205160b0103200312090f061219051302010e1c05030c0c06070f1119081f05071b0804030203072615070c0218 59
    0x10412170328134040c6204140c1c2080300c0360340a0348400e01416051074181c04900074009145217100a505a4001c000303d4510307110260315a45545001c2c86c081500e24428081510303a103115242c0ba2910711160721064140b1100240107019a140305400301d075072640810a015002070801900106e10303100c1d007025111091034030720ba9503000c0c900b000021045030422010581020700700818403c02e45960100703d804c540e02803800e1401500c00b040407a075100307030030540c081e0543c0c1c0d04881c0c081032242c08805001c141848606941080c40807004000c15802454409031403817405117411800035402c8801840140c0b0040c1090369a040504a05114003400d680600060b4010034038400403041940010244d20a031458100954241100d008101c8011080301520400c49008004103201c1024140e5004607401001c640d88152201340c540381190000c02201c947d580600881c00b0309800100c1c1081c2c5503403800032009459990300c03208031070064001c40213a070440c9031081c42000c106600a40d5501c0fa8800d0703803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 347756870 1250 347755620 347755627
    0x4030317100911071103010b0a2907050606030d14030c030711010501060f2a02060c0304080307060b012a260c1c050408060402130f0c0801080f01060b0306060a0c0c0308 74
    0x400380392151403010054887e9140c80c40b120250303a5000c1065059032541e0040c081041030b14501115450202205014983d1010495504000c07000601600c144002d80c01d45042e050b99803001d60b02c00c4ac1c0c0044000110030184005011104000050f41c0e0107c1d19244c0000d40c09654074442e421104d080c5c01000001d00555030301c16070903801440142c1d84046c8070034000700c2030342c2840d08507400707082d421002440f4840004440f150603600300241d501508101d402c0c1d03581c6e4030035864a00000c01078403071007502250349081020344242c0ba020b000a030182a46480c0e10003c1c04d290f0343c4a9403800c83c8010380c8018007501446a0b224000e0034080d0000d4400b03c00140514110550750309604034403103001108201e020001400400782c0030882541184d410750f10511000da003485610f010302003a5030140039143c94883d20400325940200442d040311040c20030344403d080c02610075802c1c2c0e01580512075840c071040000c14400e04180c0300500e000c584030710704441c2c01080c5036034050704042c003584140c41510300130 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 347758120 1250 347756870 347756873
    0x20904060f1a010f050a0c1407050a0611161413110406020109140f030a050a0203070803040b060901091104050108270f010c09052b020a0602030c01050c0403031710091107 75
    0x84d03580441c800c0e07107061860808050381c0e80240540440d1000030300450443c0c0b005e0012440400904025107401818508150b40742c12004007600d0034402d42c0007041c1314001c034520404000001c0041940c040700705013081d660031981030151900d0741c1d0305145921a0b4a51802000c0ca90b058060006880203500115100042d81896400c01440c0c41100c00c10380c1040e0000700007040c0c00802c5503640d1015040003a2a503004900580c03c41c0540300c00a0200c0a00004100c1004580ac500380e1207040b0445d10515142d0f202c2c0c1000c000c079610750010000e21403042205101542c000e40d10b10760300c41c150307001c1450103c000e80700d0410360200b042040b01d00e60740001c1104031904000c0c041d68004161500d462403100d0718101c0002c25069100320030b640441d10020000842050046d1918121a0041c0000e002c0a0340c6170b0f402540c9501c01c9103401074551801c000314101d035041500700c8044070342554034500c84107595003071079540d6a4080c0c041d0104c000c00202c0014504c04502071900e58140345190642c40708041d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 347759370 1250 347758120 347758127
    0xc02120303180115080a0f171602090a0b0a090e1f150605280c0c030b090115030510022a01050105010905030d12020901020c0301060305010213051804020904060f1a01 73
    0x10003407a081c4140041360b081c042102e000859150158200142190003440d900701048240d81710900644440e0000600e03c401304000040e0014452003070303448004550b205180c110481e282c480545a0118424804100121990300701c0d0b20301c082c001d410b44009805010382c054080c5103a0340e01168442d102e00c1e240d181070103021031840c000c01c031609000c2e00d002840c61104100b00041405410303e03400c141d4500c43c01a102d4802c045015a02c001e05020003910307420440c25468046680c20080d41c01c2840342200d003030301c0301c1e0048102ca038003100900c05400c04030703c0031020b03400150441c0131020500798028032301c180303a11034030b40440841c0c0b000040d00d50402000401400b40ca410a074080c0d40303c009000e0400c2d40c004081207145070b4140300180c48540040040b0705046d24262281e5166084c030300d02205000041d40180030381c0d9030304045c0d0701c4101c1d030b94018459801c000f125003600760391041d0000741c0542005110164424410300000444001404c107032422140341c004450000b10540500034050f581 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 347760620 1250 347759370 347759381
    0x10b031e15090303070f09031401090c0503030f0706090303090c0909330c020715020705030c04140f0606040b0c061501111b1311210f06010c021203031801 68
    0x1e801d4042142454050000c0c0c1c3e03030b40701c0500700b4820043e2805504221b14420052a006107500070b040c1d0115441142590b8084d01d00c040c4145ca1000d00e000340081d00d4076000040b60140c0c41502911800c108a58440c10010442c01d00c042c0c0c1415103404180c4001500c29013014042c054a240000b032402c10b6007007140f00c0040e048800d001344846120b140f01c3c0c1c40d03100d98008801082d42c040104e40303069104030890428601ea0301c4541030681004181e14800d03004203506041d80d00950850703010340d81020420080d104000c0703003626140c00b100301003411340c1004030380e0760307481000900034601c0c0a40d90744002403154071400c1071000f150008002d20145942c240100c03002d20400b40f030f00c20350081000719840e807611a0700001c2c48202402100c180c019403500c0d0040c081d41d0b62031000410285101213061308880d805281c0300c42d210740211503003000e03041c1c081120a0107103400c03014008035030756000c006541c1d0100b4001d040c0d85c013400d91150805031250800065200e00603017041c01500d071030200300140c207640c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 347761870 1250 347760620 347760643
    0xc0c06041b05060405010806040507140a0207030201170709031407031b151715040f050708040c060309051509010212010602031c1107020907111603021f12020903010b031e 75
    0x3e000c00c402c01003030387e21441080c1c010350101d4001401e0b840e401e2096900700182040e102c2c000c0d0001c2000035000390007192000483c1d0003030300c500d48030100007802d0648001040700e91a0104160700400d0010460010240300001c0003007040b02d103000c1d12078032155012480b40c4841c0c50040141c40307083c442440e17800402c8000407100d0504400c4006500516842504014034100c000e403245505140c583c3e54540244100355180e05c01001130707080c0403900030301211040368180c802201c5203c0000b100d601c68442d03900c059802c4000317003802c06212000007040382405840460a503400707222a48111a0307064800b402402190000c6660b021a0600c0703514211280c07403a9003e0600d00a92200c20810f01c10031a443e6981c102e03a40f0206544c1c800c0140d03044000c605420001b40b0484448201c1000060540c00c2074034000c41d80d41810004c080b080e86643d0500900741f0780007a00700446008000d501e0340203400713086802400450074540000c0803034035244008003513644804c2d54251707000c1147c006012010020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 347763120 1250 347761870 347761879
    0x812010f090504120e0a0e040c05040606020a050a12050c030a030b090903040806040b1003080d0507350403020f013303030c0b0406020906030703020307080106020c180c0c06041b05 79
    0x503d0643c50304001003008100e54400d10040726400c0e80c250350360340a4580a096080c01486c0c10382445d003000b0003c48051700481c0c1c0104c3c50705001140700c1c0d000040030003207194440000d045a04207a0b840c002d0b28900c4401c99401e00205010202c0a0013003800074281d4800e01c0da40014512040c07908010103000040c0407556039810030403003401410008200f10394802d400c1702903020355448000c2031074031100403540090580b003404190788000c04002e41249000300104d9941a03841c90b020f94070310075582d20303640c3d108211619400034004002c6034452450340c0b060181c01039036000341c00161003c0c2036451000d04504a0800f01c01580c80c3c5454800b4420460301c92a040c1d82a86421030741d01030020342030600060700c4443c08400080170413500d501192450b120240003180c5a0a0844001d4061740041e02d1050201d414000049950391000480078514031004064030504031562144064604003e0010036200608006040707052204000207800785d8415102110384035114071620800c2c4081d90400d500c03d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 347764370 1250 347763120 347763131
    0x21306090803070605060f0409150606080f06120c04020307020a0b0c04030b010e10030804060815040b0f130b030f0303070909061401030e03120a021306141b0a0812010f09 75
    0x1d450001050ba0101ca510040000d03090f10b4400026699400341e07085190f1203814496110100000f03102a8810100701c244140203c0d41c40d1442070710b003408101c0e04002000e9890700007600d81d15005417a441e00c80010410741d600e245100002c281681c0c021214040568003404d91a4200408210f405030312407064400c0508040c215a0751080204e418440d20380707030b1402a40030481a00d00180d03118000c607071040265640e0f542ea0b0002501c1e203c02101c1410b044501c0b080003201505107402034144c1a0300040ca4221820100030070021641e00300c000c0341007441d9854005c0c02150720304000240748429000003e41c0c407440c00d8100140a40c41c0b54110408081c01c0900400c4140d031109a081225907003400c01040c50100c185000745117000792030b510745d41c04079404c040c0308150189500914a8940c951207041050b0740302d02e010345083d640c4400f90700d585076003084184090321180c8611400c1c5580740060300c24030f1540f52180217160704010907001c3e48101171001008003103402c0ca1a14024070140405010b03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 347765620 1250 347764370 347764379
    0x120e0d09050306040f06091e0b10050d0f0305160203151602070e06010f05120a09120201090c030f05010b1003020d050a090305070228080f160f1802070b090102130609 73
    0x2a4840c08006c02d01c0d40c07200c2c20b540800a01600400140b107805007030791040030301030804a220b01010b4544038032228010340c012845051040121140030742200e0f4040307000030b0301d40e0116081d42c4041c544546854042e400b803801aa804e22242083c190360421605040c28001d440c0780e078010082c2e509a00b5580111010001c8403100c00b0b40f0342d8400000d09180d00e403a0303000d00d130030b8425210b1031460390440e0001d0010089100307401e40c04480c0722405412503440c00302402c1c0d426400c80700100d2019060213003c000c00c10000b0302c0c0034150320400740f01da0004500403068001203041e080300062401c01194010030344244c00b150703d1050795484051503d05200418103034402500700e2084440180c002c040c1e6207400900340c4441443c20000402d06490408040c1d40d4a007101e4a441d9504406100d82c000c0d0b044240340310a802410400f03030354180d100144030740e281c05119a26000c80c0700101c51307815001e1044402240c48800302e01c0c42010340e41c0000d1798a401001902e800040e95030840d90030f00204a40030711 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 347766870 1250 347765620 347765633
    0x40b040b031009170301120b1b04120206040b1306260f06030a0b0112020a0915060c050705030624010804080a0c020d02061303051002090619120e0d0905030604 70
    0x50840c00309041c00503c00d151400c2c1441045440207000301485400800012042d0180e0048599213025680d01086c3e0344403034003180000c1d004a50654030740302d0184410700000c494107014642451006104928041d66400c86800b03603040002191410044100108089600403465515441104d500c0780c80b07000c11414440c0e88200e01030009141e080c0f1000020703805d0703103007001380340000c0d030300441244e1549d80e50724002031501030714cc00120301915143d940000c440d2118094999441200360303086a49505200c811103030800341517802d54040c810064002040e403030600c800c0d40940c0d9000903000c3e082002d18050001c014032500120b04110320b0000700004900c4420940341c02100074940742c10403603824000129100c281e0b010195002d1000079850441b421540c108408030f0348908145d80b400350702c3c0f1070341e40101d000e0300d00040e4110104000340d40500b501d540901001020b41d081182d00089400d40d103100700d5024044241196020101200025811204890061100b2070080005103015920710 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 347768120 1250 347766870 347766883
    0x1f0b0111012003040f02030f0c0f0d02030705220c0810080a023f03030f0618040f0c1e030201020c06091c0804030b10030303110304080304240218040b040b03 69
    0x20700b440701012011030100800b000c2200300c410707002411a00030111141e00a501c45e205003000034860b080310300840755039040010702c3d6550300340c00030080c3c100507240109000079261040c00f0008843d2020300391355902c00d0355200b824045846a0794a085502d881e01552452000326040200329503c0901c1e070100598514140000784071802e0748102175102400740078405140400c0c41840822001c0105c8035819070008003552140071000c40d000300d2510780c1024440000d00c400003500d15410000c0009001c20b200c41c06a08195100d00740910f40300c0c1d600c4056150b00481c00d139039004100710006040043d5a4100300618850303c084034010b02c0c0282e101c00054010b4580391503024943c800b10f003480240310a11041c1d07001590040c01c440528a0304113207041600059000880200f0302d018611034000305014141d03841150301c0140303189980c4407038440042e100307807001814040551002124510040034006030095450181c21310003445034000c1080240c1d1505003041d0700440c84d2541a0b5029907002400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 347769370 1250 347768120 347768171
    0x70c110d05010b03010e010b1804050604030c0812041101480f03050714031602300708010b030105040c0605030c041e06020c0f01080105040e1f0b011101 67
    0x4541429034501c1d0880c0904049020503515510705562400110010b40000c03441203811070b040350008481150280b9540800d48024045030300903000140000d00a400c01e01c5400c0c000d501580c01e241e1500e000c007000d01000c0f00c003115000b4940f0310204480d42c000c42c1e000400b21521041d000081d40304c5c99040c0314524500e2502006260b00d580e01904040c000444101290304804080c007004034030b080c050040e40c00910221a02c59428112092a070004030503141000151014600c1c50a030350703000c1010284104050314205180250000650a4803054041f50480118084c00c1c4035490554102e0031180582c800900a904000811000680300421482a5403550500c552a516100500a96401203800c604121800340c41044c040c5000706072031204403040707542200c030051600f40622a01c19a05500b007400708504000521280c64103420111030b0208410403105460751040c3e4100c0204400c6841c4803109590718000c4405592244010112046541c000d00c9036980b9888030756060700b00c4c980e4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 347770620 1250 347769370 347769379
    0x30f06040521130f050a080d090501050904021207111005150d1722142b08070f0308010506040f0303080c0903030a030501050103050615070206030703091509020108070c11 75
    0x8a5000c440c18803d0318084021075943e440d080340c44134030622400505001c0c01d13100c0c0c1c1c1c144e14005000b9034005201c180034034066941e9001146030400644903078000b00f140651240e000c1c002c6148081f40340006910601c801d0741c0302850201c01c1c002d12070800c05070300d180d40d0440e07003000b007003000c20f040210340d008009100341c0c0c081c00890524201140d02c500b1400841c21145400102c40c2803964107802d20f5042d440031003501035840d0f6580d030a030000e02411071550f584c12410300240ca0303000c40ca080c40c0803900d4003102078200c54000020b17076541440780c0c0030702401c46a030200d603941241070540c07021309507001d8101940c40900c0d050810319070300b40358121884014204840000010007108000c0c0039164003030405011a0340f103240001001e80a0302e03090103450b00081c60640000c2ea10b182004a50b00940c202503100ca00e0001540c007403007501c1d4002040b5230203054484030400c0004070001c1c2c40501d20040b0303041c0054600c00900c0010001ca034003928040811141320559000b051654480051510003201c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 347771870 1250 347770620 347770663
    0x1c0b06040207023a030e0a0f0806160201021905030f0f091b04110a0f02061609061d1c060605040c0504120c0510180503011a0d0629030f060405 63
    0xe01522104c4c01008001a0000b03c0c0a02e00d0304250700304141b0034185500300c441004403911a052013140e15014810300c162a840382c40452100c6080c403180351180001032001614103069a0014512014010b01d2040003400020800542900c1c0b100d16a4101800340c0e110056410800a069628050240b10010300680c4400c2450741c2d5555034403000c080441007001949882d04034401900021034a04080050300172480010f141c0306401c1042800d40c001d546034003000030b0030204122401d00d8541c49403054805520b031034005560380d03100d20794181842e64821a241c3c80a6240010648a2907402140141c4c18100030926003900181601c0a54515481d000d410103080e042030100c45000da4420303900b20a045418100745680f0554800d200c0140c2d50742c1202079541c0743d041c5800c85034050b2a05460346d280c03180008a6140030301c0d5098185009076030105074036506c54244965003004280003081d40a4600d1684051f040030b110062005028070f0242c041454591601070b211042800c2080f030040050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 347773120 1250 347771870 347771929
    0x506060f0313020a0303051801090b1605070503060a0e0d020d090e0702101407180b0f090310060e0a0c110c0609030f011404030e061e07060603021c0b0604020702 71
    0x16003180551034008104c1040940c1d07905029081d0b40c001d2a5032045c241442c00035248c44c0d4000c4400c142110f03071007100149800c865500e108200c0036038000840302801900300014150b50700b00507043c02071301ca1400001e501c8074440c401c2e500d84400420a2001d54103c0c040c6020080c3d0011402c03011144400f40340200d942d01e82e40d08034242603240c481441a14a0120001406144555154418100354460030805c038007002c600701c41c10500d8400e01240070410400e81d104403000f10702400050070060229043d0450340d0744144250340f00d0381c105842c0d40c8544010170402030071340e01819155420605002c03038a1482407840c41d84960300001503d024020000305240700352410000b490b0024004002040005038520103544150819070302640015881e00b642c2c0b60618006c01260b22580b081c00c880d0b010070101c1c60390f08509401c14141aa1300b103640d05400405a00e5420306103a0128000400c0144080c880c03410300000080940105d014a20501281c030058503941c0803181c840760703119001c082030140c0c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 347774370 1250 347773120 347773141
    0x90c12070803030c0d180f0b100e1302030106050901030803040c0603090809150405210d020f03041202062107030f0b0a030b10030503072612070c06060305070f030c090506060f03 78
    0x155440c141d03518113446c400001d000c83c1c0144145120300c1029030010315186d484a90141c0c440d44e020306581d1138000404a1f00d481a1540c40748242c41c8080c0000c070314142d0340c8002a00d0301074240d20075603540c0d40000400003007047d480085005420241810000c50b0b615454a0700303203014809840303010310745802103186000d494400340c40084c24018103041e0f01420081440040c00b0f40c4007a441490b00c6151040c0d240700b80045000750550b12524029401c1ca4030788900c80002d5101c0310016078110400708a010507044000c0e0103a245543d040c401d1580ca820544001011141c81d8030340e400080b440c120703003807541340d50f50300e841c8040b250400d101200a440ea0b0f104507404602c1b590009065100000d0300310204001d0300c00003c08194092480151102e007004040c2c220b12945c140500e804450200046080703000c6c03240d0310310550083e01c0010b10b164482e6105407070041190001414800450010010855071012400c041c015024051006d814540e000c01c40c54041d00541c807807141030200c000742c8403000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 347775620 1250 347774370 347774381
    0x3050d0f090b0f0c0c040e010c0305010801090308040b0c0d020703030b0906030a0213151d0f1b03010909061811210c010804141b1c031202031905090c12070803030c0d 73
    0x6008107c90858080158008c11507800c2d9100428140703000040d08113410703c1100c0c0c2c60781d09601d6110103507540d03513160100981e00600c40b8426010510005440a51602c080c0039000d200c0d8500003141108c010402040780c9008101710b00c260300ca02d8164005845810290100000c501c81c003144138014460b0340403901d0210740100302c000b4492280c6585803404240c3d51400344640e018881e5081c0c5803162007100c41d4440c4120050b00c6a0100010030a840103513000c2d902c1c180c01290005414034040406a140707502040b426a88030000c1420600540742030402460320b400c80e410310040f40300100c010203481d0000800f460741070025030000034061084101307080c5c040324001000e480a20a58040c18682034400c3d0700c1031030154441c040701508911103215003085e8a501903e52481d07904c7c030400348070041d600c000c0405503070341001410301c130003000c05028007801041240094080c0c0160305060001030020301406102551040d001000311000100840e42c21407011086541d81d14940301700705d0060134 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 347776870 1250 347775620 347775643
    0x1911040e03032a030c0f0307030b0603150108070302090d0209070e060a0203040602160602150a0f0906240e01063e010c03020f12091603050d0f090b0f0c 67
    0xc10400b803003c0c0941d42d2400e1041d0325080a295901c882e10940c0c40d800110f82000350044208640c0305200340c44800b459000301c4610f40072802414482c042442e0b40c2055901e452100d58002d5041c003190b8024601c03540c000380f6860b0071402e1a1120000a40341d00a0101c0640503040240c00325a40f24851460444c0400e005020240da42c80c00040082d56030b88584100c2c0014050740e60340c440b414045400c4d0300119849a070042c15010708071301012241501c00741840700381643d501200d40c0506024000d04008500400700010080100b10480362100e0b100781081840507040b40c400c1c454103180e004440d054402c0e618017000754462868407400c03405c12224402d13140c80d2051110448054410f0540b0b101808140000e10090301c80501c02d4050340640e0703c600715a00c505101912403d0242101d03942c0c0140c0074011102c02031040a07110702031442c140c0058030740d5000044180401d54100e00c440707010500e1031038007428007440c040e044034150150800b1110321000000d140b0b00071010800078a0f40c402e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 347778120 1250 347776870 347776873
    0x613020f0409181b0f091a030708160e090604031b0606090603020f0a0b19020304051009170303060904060c02100e0d020f0c130b03100903030b040e1911040e 69
    0x3c00303401481090203c0a11000c44944005060301592036030752035101c0c0d00b15410700d4015441241404824006012120380c0c02100d1907a0205519860760104890001000401d020340b040c0b01050400140a54440e0000d84055a4000500c400c01c180050500d5001c0c0e01407911a007103800e14400c0c00381c2c20815040280260b814820089895165540310300100d80c0b0841d914403403220f1100c10b0081c4030159120300c51100209120114606140c8052000c8204003441581e1905031581d0000301643c0000198100140c0f07401d005009800052081e50540d4101c10021810b42c949070700000d00d41100100000c004544400410140500030440301a1189041d2410f022420a800050756035510986950006102e00210252518030102d06568000800352444030516100080280604006400c0c5a0940302d41c20707004000d80701a00c107070105e692082c3e40c041307000c50300801040142c6080031a184600d40041012150b003003128076030b040f450750780203240c84180f0403060001030090400084100e0305 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 347779370 1250 347778120 347778131
    0x302040203130b0c030a05070305070c0308060a170706200c04020d06090f0c020606180f131b0f0b0a0c0b0604110f031609030314221211010201050613020f0409 70
    0x76000c5a13010707520416100b00104002e0783c5000048041d2003055841001003111040301d030010030300c2a907485034461000b52816452541c4c1d1801c844011082d60103045481d04101c10500401d940403070303051a840c6070403025555400150102a84840c81460054421640019070407104821030b0008401015044000c00c0490529904940074003c05a507990040c007030390b4000f484c103191120310101e4405c0150408603440c1e407200c4178500700e000090800c00079080e40307001880004503102e000194802802d0038400c2080d180000880c0c0001e55034203d42d488803000c2c0000e0f5103903a4031070032100308070740c11040c042c4080e111880030400428010300001c05a0500080d07000c48a02483d0045010b0701044000440c08040c11078200d41820560000034001814115510310342d44401000d400050b50714800107904000041452143e801c1541c030900030910b43e5620202806820718030749000e0a000e0000380903920381b52000400420b4684054050b640c0c0c0412144242000745050318040e00b69020100721 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 347780620 1250 347779370 347779381
    0x5030d18050a090c0f081b0903030906070c060924120e011a010e0301020c0309060715090b04030807080907150314070801170d0c0f0519390302040203130b 68
    0x4d45000804030700440c0502c100c41c641548210310040c450001481040001110507400d840c1961020f4236013503140c0b1051103800300e10340d0b03440001c00c0a20303c11080b40031110b02c1c0c102c1c00742c13403d00d40e90300134880306004043ca42500302071812010700c040503916041603003080440200d80208a90749070b104696180841c525050080c2045401c00040b00341c8403480a20f41e5001018282c1c4902100c204640d041444003414604001000d0000030344a08001850081000f00b142c0846011000954414800b075061101381900801102d400400d145884603441c030b01011030681c1c170307940ca00c207400703145041c2642c404000d4400e40c845050b902240141c1005410244401840c840c4280280f00051612002d0416202c0340016a0913440d1001d40b2034583c6458181c5407044071000d0045d040d82c290080715032080b000d207031503903441100300c0c8a21203416140c1c0d451000e100000c085071541c1000302001018a01c01d03118184107a42c21240d04680c05030b5030360307184180001d680506020050407050341d5001d010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 347781870 1250 347780620 347780639
    0x3002010209040e0102040b07020d0201120c020606011e02060613020c1501030201030605030318150403390305060c0a03110c0a06150e0f040203030c0a080c010b030705030d18050a 78
    0x80201d03080320180040c3c14045281400c030b00c51842140d40d00c07002080714100505003170018950450050502810042050a400003038650040ca04c40040e0814030400c4031941e001401c4100308010001c50078194880724201035503d5801078841403007944040c680030107020b450b804031848078042406940c42808042d043e25503c21003800100d0101f4200074020030f0509001003921510b410008405510ba0704034004d0050f03000c944010030315401d8042101001050000d2070050368514a464411206201e6100b41032001e418a5180080800006000c00120f2000a14030b43c00c00100f003c415079400403158250020245100340116192000c03882c09144600440d01004c194040c0005200d00c2c081400b080d0310300301590041794411030305007002c2002c0c03000d00d00c85c46a20600c090b0071a8a1b10a1042c060b41c034000b80220100da005000040006268100307000d181000c1006500410b1154207000c0000e8a031240074645008109000702040c0b200f150004881004010141c440428181c4070000c96 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 347783120 1250 347781870 347781877
    0x31d010617060109020a0207060e0f1210050604020a0903060f150b040e0915040305090a08030f0702030f0c060913060e0a050406150501090506070507091401080607020f060430020102 80
    0x1d0201d800340c040002840440340c001c451400c5440d601070400c1e181810825281c10180c422201d03040040460400240d45030b603c12044ca80c0d840d240245502d00100e00c040e015584e000b02268020343c018024040b500b9040322a030025a5440103000c1140c03440c00c0d003c0302c014a400c108141b0001107140c1e001595880300e400400c159800302283e00010717586c140400e5590305a8480703551900c0380c1180018007003846480502a491002040031400585da514018510340201001000c2c00b6400544202145410840c0b0240042414003611030741d100303880001c1d207074040c02003000d001e18076980e281944071140342d0190002e0028250329151500b0302e040420000c2504a90884446151a0000c0c000741c01d20100740085800596a01c6841c134202800d1050300c1d0813004044599104800020030740041500903d0b58803890803092078001c0d0325080005d880c2c104c01600c23030015034000b1800d12000d0341c40810502d80c0641c01c20b40503aa42025185207000380c010150030f8880c400340c03813a00d8021701a07042d00207 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 347784370 1250 347783120 347783159
    0x504030311060103050c01051605010c1d0405090a0b061503040302060a06061706061e0403260711090c0f0a0306060807050a1d03030c0714040f05040b07031d0106 71
    0x144070308108a400c100e50750341d40a001c00b504a500a4624032860340c40b079402004502410002e4034028502503482c0360035a2401c11382480800c41903101003807811005101004241422101030000382481c07801d254907071144c0c3d84007409078400c950010f816501c40b070400d581101c030645840c6a40c1d04c0c160400944450050303522007111410001c0c00542c140c80f41e424141814032116020003991190420004140d000030440c22051003c2000d0388511584040980015401a9103000c0301707e030048224080c8014003008030305030000610500d804201c0c41b0712200000d01c42944d1383c1c4c801d0340340d5095045541c0180907566801c018000740244c00c1541c5500030904591f095101e52680382c45089041d42d0a004000c6e10000194117411307052001061a8500c2000e1007018080d0f070b103040d260314102810a071480d005102c1c156050004102c00381045e01c514010f03021070321b03400c1001c4d0910740e1364440440009040007040603158448155150002c1c441c201e003940901000b0489981d442c0780801c04911800c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 347785620 1250 347784370 347784377
    0x908190b2212211a010f091203110d08090307060c0507060216210f030906060518040b0601030207120c020f0a08071802030408091507080d050108010c140d0b0105091005040303 77
    0xa00001c0c000c650003148000410100034003c01e0903450011507542008200450030401502c03c0005d81058070030b081c0340704501903520784601805900ac0180750541c4d616001040007407682c100b001440003c81038075036180d80700070040b42086a0b100102c400c3e02a075403024064902c009a00368010403d6400701c208503126595100c0c13100d5401c0300003194400c04400510100300d50414100d2611301c203a201c41c003175038490540042d9442c1c4a03008608020b00303402031103103000651814042480049101140e000c1000d280542c50008169203250a90300041504c0e0244015110000b00715504c051144480d02c42c00780903003ca4664403080300ea0ba40400b489990304911b1651428000c800590080341d02c180e402000745882c0c000c1c02c100340084264008900c034200d010030b0041c1d0000624440090004003130001001c40c3e02d50610085908540c0010b691034180014160075403007504460041d124000d18101000448d0803010005860500c28100d01075488603009283c0714156811074003500c180c038040d94 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 347786870 1250 347785620 347785667
    0x1a0d02030a0f0e060402060904090f1416120c050904030e090c1b0109082b050a02090a08030910030203090106030c0803071101080c0904110702040504030908190b2212 73
    0x34079141c442c5130a480c00303034100104208029141c10039802c0852500d216a140350184447c035169604d812150402c148101d0f041040c200c1420100700d401c441c0641809580020205200c1d42c41000308455481014003d4090400140605001c1c25a118003a00003030308012003442c11500141c0c46512000e42c100810144400c01c05080300305224065202d540140303254074002c291801410040c01c00218141152408a00d40707603803030b0b02e500034140124506d000140e100c00c1d040c1c1c10807000c01c03402d4000d61003e60052001b50740079038410056007128000341c2001130b529100c11038070740c0c09090103400182846c0004e200000d41c81000200411000e401584441c41070007040c0011104a5803d84000c04104010f000304031007450548c0c0180314141203c90b4640c5002000e0340490245c5100301c038160040703030501004012610007030000303424065442040b510b1091003a551041801400340ca001d04a091500d680340b04006481c01070102a0b41114003507012000040300140340201032914400440c0c0c281 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 347788120 1250 347786870 347786891
    0xb19092004050d0f0807080c0601050d0f030e120a200a06090e060102010b1e130b0a03030e12031201060914061801140f0a0e06030f011a0d02030a0f 65
    0x40300580c0030009019481c01d898007040007580700180d14252203900030642400c2c00602c04400400c0e0161040032032544400c55103014034280342059010318003441070360841000055001030010610f9a140c100b400e1301403654030201c0e0518680a040000601c07600c00e0306402c1c01400b5800e0200340040c400c15600704c41c10601030214100c1584111404241260b0342801810030044255a00c41010b00c00010807003040b10000b00d04c051201049032149415122521160504030302c24042841c441e40207004801d20140814074218443c480681001398125000620740c1c0c55444104184440710120303519000d64403409141c0702420712440d00410843c090014802c0c00c908000c2c082100001c002908145d49100682c008134642e101c924100305c0e1881020007110303005030141c029841c03982e0b03009846410380d2002a200700140d480e020300c9041d0900c00c20900d640300500441c151040101c03440d00101e407a040d940c0040c014661454801030010040068080e80ba500c80c0c0d00e4201c81010500410088 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 347789370 1250 347788120 347788151
    0x60e010e0f0f0c120a080a120510050103051308030c0a120504080a1119080906090a060207090606030504121b0f0f030e060705150c040308040f0e06030613150b1909 72
    0x44c0f0403600360a4100d503c605010495460107003a21408505000441e89130030f000490454808480e4018414070401c0309208a50380342c403800307500040e181ca26044295490711100314900000300f0400b40000001103403681644120b291070304901750002c040c03001e800d1628041c01d598208003034100020b0014600000038a80018400c50200b013400140c0c4051591781e243d0941ca903204041050b040302313007001000c3c1603450b200e2003400144807a40c0070700030032402c00444409840c441d40c41001010305140900000c40e41c0b00c0204400980f0b2410070060b12100e00e014000000804500507101c05039010f01002880707002222041c1d40b611a43d42d04000d2820b20381000b1040c0640f040c060003030740c4601034030070210403e00300c1a9045500e1741c1d0f2040c102a5a6078a520155000d5049000844c203424002c2124480d440309050304844101c01403d5249803411600c0141501c3c124060b00e4034804441810984415a00c42d2605900c0070300901c040301d0880b144507014042d80d108803909113140c40f8a232103010340c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 347790620 1250 347789370 347789389
    0x50f01030b041211031207080a06050f1e1512060603041e0312060b0c12040303020d050f0f0d0e0606010207080c2107080619050402010903060e010e0f0f0c 68
    0x1d100d01e00440544581d201c800003030f084040c0740310a0013443e802610541c04e080014010b1003036941c80200840c030309a0001011001d02500043c506400c000d028409a51181400890050282c804c03000d01004403a05050b00d00d90726422a8020380a251901d18201b00e2100801403860642c007440c0e850b4032090300380210b5100c01c9802030030407112000340143e110010701d602048280a413810245500c58140c2000c115103403a40081c0320000700107000500c081e814003030030a070300d131080120758141459520702035282c42d01002c506c0c040020002e806c3c0b6000c42000b0545994038141687d00340c954001d84644002440e015415900074420706001070f5407036200141030390a448100b0041c18944040c242401400542c0d001d2503044140c80c8850004000000c01c90b8070b004040c0000204420304114440b001200e400c1660505603505001c10400136036008044141200e03800103001a030b420070700800342d005141c0c5c40c4040e0b58a0243c4284500700c2c0000242c15510101020265407024280800b003048003203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 347791870 1250 347790620 347790623
    0x4060306050117041203060314030c010b180117121207080a0516030f0e0d0e0918030a0e01020a050f06010f0b0306090106030b010203040905070c1a0709230a0b0301030501050f0103 79
    0x29200000500041c5d070312a621040d4422800c0100b101503d0b6500c051610011591401841c2d00124425800c18024001e00f119840c1c02e0f652019180704140344c0320142141401100703511450b04e011048540001c2002d400c0408a5181c0700352070315200c07a1212101a015640580010060800700e03101a1071403007002d01030645503464034a901e0300407200313802914089580e03c00075075642c01074070080c5100740000d004d000e0495482c42c85010b280c804110650070040c203082840403071282d840001a00000441e140100309040c09600100010b00407454100320880c01425400349280381c0e40c10043c00100c00c1e0580c0c810300e0445000300d455001d0b16019010440f50355602010800040200900079400000c1b00344042c41a03914207910342d4802800c0d150b0a0700d201001a0304801c0500520a42c00e030380e442c80e490303100c080303505604108c140185101c441c1d001e80113400c06682004040d0016102c8008e603010005029009155683c6a01215980091106035029400c003000680c07124040101035042c0d030b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 347793120 1250 347791870 347791907
    0x90628021b040c0e10051b0606090c030c12130501021b010606020a03091806050d050c0f10080f0c19020f010b090106090e1033022805010b04050408040603060501 71
    0x310000304c100b00d550b04610000c20140501004a0111300c072904000c6070202219100400c0c203410000140403240d000100b85a000ca08240288454a49610202d50b8591002c40c03103d1503075110300c0807408802400c0fa8009005610006541c84007109840220885400c008020088680d407040c080c0c0c1c46481c903841c000e00140f0201018402c01007040004001e0006041000071510b072114041080c0c110399a000750b5299000d60105003182c40c0016440a100c10f081d02d04818400b50b2500141082c038025103001c10303080c42c2a000415840d900b0064881c038135645041f0f44540d01c8240c5020392124190010303c0c0065003003058040f65428400030b0a03040310101c3c0d0364031881c907107401002002031501401c0c0040454900303100050300e140804079500340317044680c80c2d83d00c2d4015801001d0030400d02048198199000403c0c00d60312550b0440d0b001003220244051805107914900c0d099006044448446500a00d01014841800035100141c1b0580d85a03890402c10291a040103690b01001e10300c410468 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 347794370 1250 347793120 347793137
    0x120f0504030e060c150903430b01030206071b06030614190e0406090206041409092a030c0405010602060403200a1403160b060f0a0803090628021b040c 66
    0x1e02d0b005c2a000b03980100c0700300580781880340c0c2c0d0300d95040c6002030a0380a68408440044c034800c0384402e504000032045881620000c030172007952019110441448064498a404503041d81071099114034171507064070307a06440075440c1e11a207003d0000d100074000d0140c8480301110f081000d090202d41000c03049090003ca000d5213150626501c1e50020007802180da464544881c000140c45400242c00940307040314030040101c0002c000d1089841000380640240d078800461050101c040c4402000b04001d1240c400483c0c50540c1c0109140c80c08200ca51b41e00246440e0002400e40d901144040c0214820350f144184451030110302a0a114100c0080307078950003480510f8000340500140980c0e902d01c800c10360f41450f60024501c2c480004003042515011054810000603150410020091090440b4aa0201030420803055500c0c05a83c3c000c0d4081d004c0040e2800850300315044440060b02c000400c0d411444100b1002510b8011824014604540044480001d450703d8001c201e2203c8541d42d46980 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 347795620 1250 347794370 347794393
    0x2a120b0d0b1801020403050102040e0901021c020a051201090203040308060307031220060a05061c0803041407080d050c012307080a0b060a090503070b0f070f03120f0504030e060c 78
    0x91410340503280b40c196640101c01c2400c0d400081c0094801913020390001030300ea928000d05495480001032074164181d10401480c00c0328400c001c0d18410908a1603001604d84510721415107840c41014000500e044000300000740e0b14002e6001148140e100703949142554440105069641c521400001c01904034800c0e03091500c0c3c41110358084403804910005904260303c100715040000a407070b0181125195410080d003401c0140032500c40d81000e114401c4040300f40d494140c024080500014003964849501000c500010499003002c1c01540054842c1180e48400281c529400440084607550030019103500450300d040d82124071f40b103011041201950f03022400c9130041001003034190540c0e503401d0b080c00c107516550060041e0300d1a60f10313480c0c41c1c0e44c141020546861180c3d8040404c0000810402c5190400e00c804d613042654070590707042c0304001e145002c3c0d91000340580c003184100d20f48801030700801c40030f800c0a03029500a0700c488121030301c4501440190f21508840074400d6000c1c0100c00e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 347796870 1250 347795620 347795633
    0x40e0103111f0e2d0907020f031e0409020c150a022106040608010c02030408120f2b021602040b01020705010503060d02040e0d0503091903020d050c012a120b0d 70
    0x1000f00000d00062101682500d449200134850308a0040da08865103480b500d41030a1031003a400500500003800c5c4402d4000b1115039038031a04952070101c04407410f00082c242e6440080e90090841c0f0a8199140e401100055a58009000103607007000304171400705070500e40030702c200c1c1c1409110348c48089001c007000200700d45425002d0105600140c3d030f51400075103078100384030303004c02004140d01540c2d0b40c0d485c0000e075a26069000441c410480780410107080d10b180100d04685104858803030061030031103a000820a80e40104180d90901400001c02d41c2e140c280e000b40358002540300311004c015440244004a03612541030003601e0204404202140451901d480c00da009144000c001103050a400c40d10b1364101448206042c02040001c41400740000050012442c00414442803090000054600a55941c52401003000340300340080c1c00c107034990081d00100182ea40c402508620611220782e0028080c05222500001a0400580e00e1002e2040e005400c0100802000d14071004860784400c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 347798120 1250 347796870 347796887
    0xa0e25120b0d02210d1d0904021203040b0d11030402010c060b03120c030304140a0b040201120e0a03020a0204110403081803070e0901020409050709080d08060301060902040e0103111f 80
    0x140d8482c1200740641c0041e5103030245142c03100c90074244072030f6400c0d01c42d400d103140050484120050110380b042181c804809844802d5828004035540e190584450020551441803101d410446000001d0f0100e00394100200404080c5011117042000310352101f408074040c04103907402400a020300d0105e00104000380c0010801c07400090a89070704425454a011040c0e100f0261030441c0d410200410091000c04051540a40200c402500460409568a41007240001d0000307046c84582056801010070320303804030703202c1034801040358444017070750802a40e03654810400300c1c410350420740014400958181a01c1c216079200a40c20f0034040d100806060840d1209500c41c0c140c841c414000070a111030301072440c050803110000580d44d90810900304140c0f20001c000206028039408100150300c0002010303d0901c0782850800e00c1070b180c0303d0006e409031a4a6000d015902e00100b808250b6644240440341228400c02100084200400c00d105102e956620b04140d0748403101e9030100340f24040c40300c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 347799370 1250 347798120 347798141
    0xc08040e15180a1e1a0f150717070209090c04050c090a03030c052805010501050d08071b030203060c041e030503071e081308010509010b1e0109050a0e2512 68
    0x4440728480004c58403011140d21104017820700088104615180c01d11300d6100c10701c400240d84401c00341c1c041006104092244190081c00140c8513075030711200352004016180c10b164003c10404080c00c0000d106540c40e408005164803861074400420020a502c40c2143e01480307000c2c000002c045d286860075114404940c00549660080d070b40e240001e0305034074440b1441c010b2081007a04e100282d80c1031403421650305070041c90140060385030380070114001e442903c0c04a0341c0032054010426442100101c00c04c0a07a00c000e40611410041c06446101c040107801070b1400b0050100c605c234500d84c0d0642d0b0900d89c500c800703016904104a8a4042505d4111841240d40e14101c000001038280d40d0f002c1c40ba03030024600705413003001c08105129166081c050203070010440d1000307100390540b14000030220301c9561801041c0c2d22811001c0703a0b40c1c0e40075020788401007100411130340143d9038490041c5c0c40d040301190144078400c40c0d090340c0c26003101d00c500c080c1041c0300f581e0341e00e8841c0002d00d003a0350010f0869000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 347800620 1250 347799370 347799401
    0x3070f180906020a02011e0b0303030c0313120f17010e06060309070b0a0507150209090109020d0603060f0203060103051e1f03140c040518030711010c08040e15180a 72
    0x41c4280401e032940000c0c007604206070700020f62981e4014680f541010394045e10f8100d10305043c8480c0c107680d0000241ca800110024959980c3d4684a01110780d003094814020110190003002072200c0d80c0003414007000030701e0754895160031440a41c00000d460340074051880e4110164000c0741c118100721015641c040c40c41401c84003003d4485280d108a50054036500000401c005054404c010040d6501442c07000362103010350a2000000c00214841814052150030315400300b003410380d0180c5500f10100841d0400e4042180321010246140030758011552203011a0a1601003044004518001203682058020712f18080d07e484401144080c0394a0f043c10410710394203008070105000d621045549007040d401040d4030807101090105880c401008020303071407101618050a0407020003102c02055000440c1d02000d50b00c2d0005840d00c080342d9401400c003580204011500140002d030309070041304025540611070305d0701c00400140321900040480d48403110004039503900e1883d00008602c955001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 347801870 1250 347800620 347800631
    0x2040605030411400506010503070c08090418110604030203030a050c07151d03070f0513150807060201050105030111160f0219060801080f07031b180501090b03070f18 73
    0x1444004024898040142d003e18480074900c5820a44c0031155003040400e10103000302c1c5812800642180002000341c02070000c0c0d041c002c0208243c20382100d0500700028020050307041404507415a0014001046940141000c07058680d03190503416242201d40c001d00442c034003c9811800c4525411640301c510945c458220040742030b03c40c540c120005001c0c40d690380c40340d4502c004903151200008101690081c1c100c64000c1c4a440752400c43c0e4800e03100c0544445480004884004004001100d0210000c0314290701c0490141c2c0045031080c01c4481d203030700038003850f42c85804040c221000241d00089602c030410134040042d0154184010340780c0985162884048982c01040091005440109001d04040410300159070400c40080c017504501c1d00400340f14044200255441c00b107030101904100021200340c8204007036090300000b40c03406903480070701808100d1005014110070300a6041d194188403124046080000303080b0115041045031180c3e05140ca03031002c00b0031a882c0d100c485000d46a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 347803120 1250 347801870 347801899
    0x81f0810150909050a170d0f05060117010501080c0a050c0708071508070e0f010509031209010f08090a110d15050f180d030c020c1206060f0102150a0c090306150e010902040605030411 80
    0x140300710f0388e030003d440704089028904000010041c2c2c01060301e51814002840041c842640e1140304141d110140c85401a5510703917152042c1c8007802009880e5a40e0320402d02c0c081000ca00120b0020100d134141780501c080d60107000300984140c070041718410300082d801c2040301600d160018480c1882d1b40c041c10618500411000441d0405100900c1c21200e410009046046d551313119480c01011300c082e00c0c011143c0e05007552071644808200001820101d0714404a01c4141e03107456414222951203214640420381140d074a4000c1c00c400c403501000030320139100084480f4002d01520400964000107416010340340f1405400421309c4420b82011442816052000d07a01c41d4450304240340c0d0048024605803408400f004049040784503002c1c119008400072840000141850940020800c200400d07450b020700011100da1030240c0c009040346040c91440002e204503444403105440b03850040d95041c0c1e8039000884280c0c8214812100011010000103010a1040c3d08248904000400d4038500e142e04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 347804370 1250 347803120 347803147
    0x309040c0e03240601050705060402060702031c0c1b052809110301030c1203020303010608040203030d020a080a06050103020a0c0b0a090206040b1b0706081f0810150909050a17 77
    0x3104600041828070f2640b0700c01110300780345080e0b210b0400d2801c1d600c5d03c61269035040d00e90401400003030194202151640456600b8004407083c102001c2040b5101304202a00a20841c0c0c400c0c2c056844d003403001152060307901207001e01c0307082c2c2d40050409080324401c4400c00318000707480c241280451000b442c01240800c82c50151004075120841c40544a5065003080e87c501c6030a41d1141004810b481180400640c011082d01c3c115074290070320451943d01d40c00072a00314894070361a130b144a840002d2a003903658002448500401988901b04030b40342c4c95100640492103107014000114922100c04000207041020141c0d002d0000140811101803560100c0c81d145c100e0303000040c100202040c0300308075159504c0240b08104001000300300c11403074588007400e0071102801c980b000e83e122240c0500d401440302c034400020072011040700e0303042c242c01c0c051400800744084e859042a145c0074002900051a02400d2215a0400080c0203da03030720740e4070581140800c507080d5008000c1403002100b02c1d402c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 347805620 1250 347804370 347804383
    0x71d04030215150405010b040e0c030405070b03161106190c050c0d0305010501180b0f07060212090c01021e150414120304020405010519060305060a1212080709080309040c0e03 77
    0x1c104203543c010714610810401a03880581050102d904140410084c034016030031200d411000d8040499901c0e183c0d0300700346082040a4000c080d8038603002061000b11030740303c0a00c01c03c8804540d18141d584032010790080e11054240c900c400e440403205c0d040003010020b80e00c0862560300c00c5c00d0072894161001c0010b41041c1d11903185201003030359200100490358009d00c20341c208008130a40a540c0300d08250022605005201090008181c085110000c2000d258110341c2d40e07422140c81c640c0e81d807400821050ba107100c002c0f481030050203809088507990580007140d030718224904024005000d070a121003243e04070300070016184522001c420314800d40090043d8581082c03200b04c0306540c0d29050040c8015203106030b11880c00b07000b5040010380324112407088181651003034600400c0329101c010004502e07500b25002240c5802d0a40304807020000041113101310114103481c0c02e200d66403090400c3d0703001803842c4103007031094104000d181151b16050303000781d800300310b40e04104240b075000202281c5040d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 347806870 1250 347805620 347805631
    0x117010b01140d14040f061803170402010905040207050d1b0506010e07090b03011d010605070210141c0b1201060312050a020a0c1e051504050918010e031b071d04030215 74
    0x618070506d1105212280c024110700100407058260081251360700206822044d0110724810380382c400204045a1142141200a1100400030b544900c07090030440d03200e2110140703040c0401d68080c01100895007421400100e2a0004090400c0fa0320300840609800c500611020070021761103808140e50061502460203004422138494034409108014052030383c044c0c111505118081c40801c005030703541880c020950540745800d1160480150780c082c028003c05e040c80b240301000480e0200e070f00d030540c2d00806031104221004c001401c1182c000600b00ca035240005000d004c40c4032a20010280568010110100399204541c001d02c0d03561610000c0340225004500100302c443d42d802d40d0010800c8141c8040c020445620340c8140c2c41e84807820740b070701c29845054001c5012400081001050203070384030800e40b4102c000c0c446c4440030100d0035202e40c401c01341c80140356030094640b503119030000340300d80c04d855107200701d4220005111801145003400400440440c401c420300070820010b0f44c00c2032401807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 347808120 1250 347806870 347806883
    0x10090b010f050109152f0a02011d06042903160807030c23041205010c1205010608010b0d0e07030305091305100b0919030b0117010b01140d1404 63
    0x55051115519a841da190b010340d0400640f40e2090090030f01d00b04c00d8955001c03183c1811010088144204e5107203060902092048619405d030400c01010041072409001e4800d07691a24001c03910090403041c0742c8440d8030540c01070306c24002881007031003480c0d4402e1052480641c1400a0030400941c805941c4100d60044500e003040c04031804103900320500c3c60f00045541002d0100b140780c82002400c1644241046801c120300b40048012181c182c0100e6003e80149030750317041303116030350304105020f01240003141c0c4c00550000007510060b0b941d4801e041c1071360303290f40c4c4564450740303002c84000c1720740c200e0300031200095610051800c0304002040304030001d5102e510359645801c000800c103d0a00940c004010029081c102000903804407968400244c841d2580718a4490554601043c2c6940982c0c81c1512603070120003010081c030014820450498840c0342040d407600b000303c09901d0a036242000b1403030100d948002c44000816500024008202000034001441c50034688008504142540d003501e16 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 347809370 1250 347808120 347808143
    0x150204050f1e011b02040203090304080f0d0f081512060109240b0703020f03040b040503010b0d08180402130603050a0c021f1a09160305010e07050403080306031009 72
    0x11401c1c0031250001402048501c0b894240705078040c001d48940d110b9005040004102d107030440340c840300c1511000f494000d4011500d0b840c1109035580d496006004040c5a88140c10040d100d03580000356079040d00f210f0b503407a68400408120150784800340648080c0700840803003902c41d455250803000103001c0030030350018200d035403415000c042140c04030319500b2102014407407030198100d00418030b40304403005005625030303030b02560a00305c0c1804213030f18407545a400001000031700c1000100280050700c80440c02004145c4441c003c0056001443e500205400410321008407039502043e480e454088000d400945040801c3c0a501c86142a075000540030039600c90074445000359602c0755070034115850006003204520103d0480c03141c603880c0040c1080c2c0e034440e46441004501442075012560b4040c1c04040315003444440103c141c00c00c4208000042c0c03038040000352000180040f28023681302d64986626090841c1c50302880b0b50b2000b8101c1d42c05102c3e20200d481100100e10071410540e001d074049020b07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 347810620 1250 347809370 347809379
    0x619020c0103060f0f06050711090103051e0109150209040f0f090309140109170c090c09011205160c06020906040906180c08240306010f1406030408070605090a150204 73
    0x488243d07801c0720585006048050012801c01114072060b00c083d810559141d00341d07031405c1356101c2c002440260f0011101c0780000308100e800a00307000b518014011903040e10b0100c00c006822141a0240070304a100c01040e660040c4040c1d0340140101e503800b40000c01c01c210304c80b14040564003642c0006444a075291088000d0680c40a0003101400b0f0451521940d46403120008061021034098100300c04411240d40c0580b241c100040c1e011600c02403d0450285041e44100c0ea90742c04c05075165021030f04010742542c25900b10300c580f512461718007202d5455045506001c6505a180e00701c100ea1003a420000030202e95580c0010704000d200100000c00c1d801d080200034598444400080400b00303040c03e090490349600621001d81c0401e481e0410701c1300c1c0e820320511300b024801002a45801d03000383c400220b45d0440442c80d400540c0d21016940050380e20000600c40305210482d00030b0101e070401c7c401c040004031a270700156009aa50f40455148141c5600c98501c00b800301d60701c14640b941e00040801c0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 347811870 1250 347810620 347810627
    0x1e070603060504060f090b13060609051203031e060102100614012c040b0a0e040f0201110706051e120a06030c050406061b0314180a14010f030b0619020c01 68
    0x102a002c00d44080c0400d41c600000040080864040c40c010503440d81002407044d11007a82052281d00031000502600781c2e90103020f884081140500c6010306440641c4a40200000081302c4c0944600c0340e002d903455180c8130f05005020340c050400c0d4118002c038003010444040034011b000203005c4051004103400180c10000d86141c4042c0c1d0052140f170440400503450741a107d00d1441c26005c140c6011803400c0850000a2402c1c809130400011007400c0710034801440440c1c203009803c0307031003a04c901c440c03500740000b0f0a680d104248200000178208000004a0300e10f105468503000191701c561030b0400340484190b9140c1032045621280d026903d000400502101d04843d000901e400d032400c1107224100701e40280440003132655040c0010b072014105040510900310a0034101000d0301722519000420b80d88480310301d401c0c0946116a0b0122030108420b0100c2241c4000c20405031180c044c00200e6001c241d02908282d60102c5d44104180306054401c104030310500076158041e8082c09040c4a404c0014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 347813120 1250 347811870 347811881
    0x41b0216061e081302090403050a0908031305060903010906051306050106090506040b0a020a121106060f031e011509091e021302070602041d040525171e070603 70
    0x404100c1c41c40c000c0521154a00e40e928840c14441c80c3c80120f40e92100707010314040801200080d084003507103007003000340341c2d1180182403145c4585e99441e00c1b041d41d0f15081075690041c800350901c83c82c800d031030030030041c40c1000042503400070207030020920481549130113003280c1e811280c00070b800424022607001c0001030300c12540503010908007124214200f81c04135525004500950000d810002aa400d0441c001c02522840039070040d4903005100108800420007a02c01d00c0905483c0b0500003c0389492403c28500140d2031000380c01040d80001c00400b10881c2511111120300a558031814480010882c10344035015050720303e808925914545009010354492070320340743d0b860311a00000750050780c0b8003054410319556000e000d0b031100d0480c2002c5000784103580c0401a09403c1904072100580f072401140c0c8103074040c00594202052940c601c03045035042d011a541c05854007031081c0842c4000c440711000026417074003112149110010704990302e081b280007203420b03035014050404c542641030288 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 347814370 1250 347813120 347813129
    0x70306060e1006020d0c030201021b010f1103012d08060c090a06020d02060a0f02090303070c15020706120c0c050105070e0f064b090a05040504051b041b0216 69
    0x1c81c0b1000d2901d14001d455000c040e60a508000000740f02c0750a052007501596060190800403030081c03210700e0744ea54000d2098480921901e820401012a54074000c03050301d049410b820318540c0411112a101d10450208046500e180c5218503408203104004020440c1300d13554502c000c0755981000300c00c0043c0e0b040584e0200045600c0f250450411310303400b28220380c211219500c04200d44807140c01c4400a4090303400c00c550140300c0031843e8020312502c04018030403034034441d07581c0c4200c02c0042c0d412030f201e200c2070040390082410b00e620709041c50001c0e8084407082c110351801e05003140c50f41e5112800e4850580d05800060f00342c01201d921803504960003807100104940462414444110b4880101c1c00300d003090b403c01c5e031110754000d440030001d03001c03050041c021402c03000f1141c00740f403400d151034002e500380b98082c4644683c0460141058071a460141750480000e00c64490001b105a4108400f030b08200d400c42d0f11034010881c00c0120710017041d4006000d402404001d07140c0880303054604841d500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 347815620 1250 347814370 347814391
    0x4031b02011d0102030c01230f060d030e04090f06021206010918020310050909030301060315031e1727030c24070f2a080c01120905070306060e 63
    0x26154010703030300001640d5000c103024a851481c081e0000060307040d801031b0f01d0b600c42154203158101c806c00c8151030b041d0503000d4281001e1401c0b5103c0d4201d030b81448400700e50080d0040f03c600c0ca60000f0902600350b0f0100d951f0014008580c4004950314125590350025044132220340201c0c00d011b088000c40c0303401d54445428a014400725103070482060525200d81140040107900001040842d0f40181c14070700030f0080540500d11701d0170a01c007156038a5000340f0500000070703e800c07401d1500640c604001c1c41107035001030310390100c00102154a13100075110403045038841c0c0c1e244420401d50b1003400281860814080000b9440042030407591804c44041300800e1103900986004050b80c0d0f900c00c0343d000541c10702081da02d4181e000700407404040c800c0d000058110f4520384028010094450300c900b82054804c0520401742c1d20102c1194800280c9004001c1d0b03981101103088802e51147c0c8011180341c8400340301241c00001034584506150464005a8680d921490300f4005480c1000d41a50083d00c60785 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 347816870 1250 347815620 347815667
    0x403170702030405060c01020706020a05220605040e07120e010c03180b041103030c010509010912080609010e060301020f0c070303031410090b0d1509110103020a050d111201030b0403 80
    0x100300a40b80c0c403031030084074403134800403500607000300b42541910b1041c0e602071411550341c002228050541d17040010a040f4541d40b108031845040030295541d0200c4511307444d03c900341030800c031101c9205080204039604100080000b0680d03045940900428030b03001100004510098203802415195082428158091100e0f24200020340d401c040903400380e006100a003014440d040004d04501c40d07403124107003560912080c130030310340e1040d4001900c5038801c050203ca0700b04a40c0c0705440100d01200c4156000c1c0100c801080b1500800c404bc2c3e80c8040002c00051409660680c5008203400c514100c003600d600c10300d000d200301034043c821001078a03d007520f03801e510b240107030800c1115a01401100c68090303d0f41c0a001c0c1607126a513000c602d02c1e034444000c0c0d0140f03441541c540014242c058041d12030101c0c00c0102c1c9615402071007259038903501d9665103440c01120b10031031400b41c04a030f444507a21510402c81040000c001089150107144201010300707060a19060040581442c40030f104038129182 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 347818120 1250 347816870 347816881
    0x709060b07060b15030c1818070e12071e0806060a03120c0b0103120e010e030c0d0c05180a0b0105090f0d0f0501111c18020105030c1e03040317 63
    0x82907034500c9510040100740c103820314010030898207003500503400c0c2ca1008404c0c81401145c1601808101001c8803584c40400318610810502841c030000101d5070101807408160581d2040c0418446203d01038882c64001d0000c450146c42d15581c2da10510404a103e41040414842a00413100924100340109454101000050500c440e42e103c02084080c50300c0c40e41545c40d001d055002035643e000b1650501c19070352820210034600c45443d56000090001010781c2441d030141c4040443c951000e4000d00038080b034041441504075000506031908804000001400e41d2001c801300d03a8070480d81030b07401280c1401200e4009603000c0480b0241400020b102007400743d240d003910014400800c440480c00b0b07003401e0600e10461192030102034615420110203415a20a00005001ca0b50f40201000c0c2c1c48417685030004100c40346042c03044401100010310901540c03240010350303004800e0703c1c440761820744c14002100150700104201c406222003c41000245a00280701081c101e01c00c190004241c40d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 347819370 1250 347818120 347818139
    0xc0e0306040c06180e0c09031917090f09151c0807031409040e01061a03040c03080f0d0c0903021305042f0411040906080f0606150c0d0809070906 64
    0x4a0190300104248034071003c040141c0c42d81040014505c14540b1801818824829032840e440038941d5802803080390700b0250b07007400c03003990b846c4100e8000d1007410800115902084481d80700d118400d6120714012814006982c51400c401c0c0285010303184911126040800e00c29540940c40d101c80741c03c4482141d0402084400e0202d4044d1541482c2c000617415a07445070340414020300c850150006e2404040c460304d204154407031416504008691045081c7c4454142c0343d034070007120000c012404035a0300b00001002d0f90041c05851915420701400d1184108442c400c442a04190000260040d082003081d4106a000704000c91007a4100b4890762402e900c7e40c240c00446a0100c0c81c82c0c40501815200c0b1f02c4181e082c110300d14800405c1444005160f040c0c3d0806500903020303041900b0f10349500007400400015684c819114107202501c1580e43c2c2d0f00c00c0000c039407002c141c0c00008100c02c000c42980504180700f50310040600e81c41780c40c00360810b50116444c04805802c40d0100e80d290040a0008052 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 347820620 1250 347819370 347819393
    0x9080307030302032e0e13020d06111e070c0b0a080f0601140c0106080f0c09040f1a040602071703240406170609010b060304081606060305030406030c0e030604 70
    0x4142c2400340e500c0d16101070010044600c4645600f0700300d0035501c1448080e0145800da403c568207001c0c0e9000d541c840800800d01030381c00000007544403107290f58980c000341d040d4019046030225408200e090103002d011000c0506503408413403411400005948080000c4c001045018001c0e10800744e0400c0c2c0102405401c004003d04510340011000d40051443ea205010750213102030800d501c2502c60001080c094041d00d164080c4100c1800b82d6002c4490b2081d00042c03400400d4001010040f03107854588821000c0800c000b02030f62a0030381041c0d050400203141c48021701035440f6541c01a60340e11581003000740d01481151b915114039040090201903010380d08104124804540810144030704c02000a004082c554005a4112941d00e8110f07413031a4081a42449088540f00031700000b01d4607001c00440b8401140c004000c282d080c852a00d840c898800108206481690002000b6407aa16010700d5a08190300c00c0b03000076117034985550115440411518120303815002030480d4201a95880d0010b170 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 347821870 1250 347820620 347820623
    0x3140403020604091d0d0201020702010e0d0218180312010504050a0b300708011b03150b0c0a02040e010527030d02071e0c0312020d090b0a050d14060301060609080307 73
    0x60700c0b265000100012056202c0041e4400d40446d00040c07803000c000b80c083c1d0071000c0d041e808503007540580c0d0703810f040680205000c0d5600404903409014044420b8103245405424119903202c81c0414165103402040103110315500c045a810056150604000c1610b0008008401c200e0501c103004140d41c54080f000006004d440b004000201e00782c00b640442a903910207000c2d51403280d8400010090030642c400c00c044001c00484440021207001c0690507503510698015500c1c020000400c0004030200c0504003020010f0306640d81e9049940002e025540d000b14110080d964810034072031220250038401c12441d5a610610030140080c02002d41c5a01031011008411500000c0f10402c01c503030b04880413200104198941c01e414440c1c03c103445090591300044524600c07000301200c0c2580002450707542540340703903101e07003103141481e1801c2c1c0f1540000c0800d00a100060010403110009401001e0300c1c0d001c204900c0da80e5203041010542595100d52110080c000c0410301031000480100880d50001e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 347823120 1250 347821870 347821889
    0x3060515030a11061201090506041404030c0615050603070f08070c021c030507021003021224010e13110c0106050d031704081201140f090c040e0c09060a0c03140403020604 75
    0x400300f890100300d131407181444aa241092543c00401c0b8101240d2080380142c13019181000152102003c0001da01002d88015020503807503070800002030781c5500701242c0c109030020a21003880e580e03400714246801c15103410b00420000d400355030300c1a5008144643c040403503d0000e040d601107801255403400100d01440600115000060516014804480d01564054101d00d06040c49940040c02500b02e02131107c9400e2124010445e2104002c0682903140007480800a030b1944000040d00c00480c1c0b440140c1d042408402648902c0010344180811a01c000101680d5044c0d8814024210b9241c2d42105218407440d00c90200420ba00c800080300400d100500d200c62a20345d428411058042d080c01407101c10481e8001080010051025079220201520804181d03c101c2d030811444000440d5403040c15682407108100440c51282e005810181d9a9a200d240c2601c10011032a141d0040c0200c101207411111014100355010b1410040a11000305590070242590f000074030602c52072041e407441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 347824370 1250 347823120 347823143
    0x30c060421050a030f0315030b06010302070f080d3305010c050705031002120f01030506130206070b07020a0c060806090a0b0118091e0e0a08070c08030406080103060515030a 76
    0x15401c80c0e40034114603030004100c0348900620300d40207003a0b03190041060f0009040185600301c1c03041c00d8501c002075961100d211181030380d07034500440c002d4010140c29614280000755a401103103030880240101407400b40e0204044084103e401c40b554071080c01002624901009001c0011013405114150780c1c00340392280b80c10343ca50510713505c0c14150ba0450341d40741c0200101d800410b0041d600805403c0c00442d002d4065558440c400440c003c400d20002d40141c00c1100001e0140341c0c034010044080344010308070b5041444ea51284480044d040f581803026a1000c0d0034401440454107421009120b10f2418000602d08078000c506200c0c00984020340840d1200c40152560380681070140100e44510003407040d0903130f201102400341c94403c040f800314018007411040c581d03503180180f1a000d90641b008007034014442e5600020342e80300c4802034035070800711040070520324014130081c80180b00a075503d030707010750460402d10100e6101805000803403110103050301480e18003054407a50344e500302c50740401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 347825620 1250 347824370 347824409
    0x204090e06061e2101020306040f02090a060f182d0f14040905060702010516030b011d180f06010f030501150f020c0409050a17090d170d0c0c050c030c0604 68
    0x10801c10100498614005121684c404132056000d503104240454060220008401030b580807445007101b49904000280001e020040c0203552110b284190383c64000801d0210b4042d07640c20540a4216240340c2e249500e0a40745407183c642100345d00700040840782030311482c04d404d0110900e407910070300c55015a5420400c09a65407a4171064000d600b201c1500c803140340c03030300c0024000c1c10f04491608150020380030469940c0d11900c07581054000607192446000a00542c0d1715450040303500c21a400305100c05d210056031012080036001d8480d100e802101802c0080025002c0e1007200e100d801051f2074100100407100001030119120782260a10003051070541000300d06000c448402190005d0400513500104071000070a03982c0c0c603004503090700c01403510031440c212910030a0764180d4001e11503298500400d0240300d8079000c041840660600e003203080c0d04c14400740c1d0502e0800001244925846105000040c4480c40417139400310060140707510440000740d00c40c00349014148054009008422 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 347826870 1250 347825620 347825629
    0x40303030f0b06070b070f020f0c0409060609152108040306020306031e0309121506060d0b090c0d0b0321070203010e070b070309060c050304171905010204090e06061e 73
    0x64882c42c00741030240c2d95016410889980101550008001101d40301c41c8a09030b8404034001c101c070114072000e446407102d101c04000241901c15003d941c429690300d400180f034101031107400d243c440032462151000b486c017000400c841003a4a03080c4203c5d00c1030700151000881348012035094a40c4800300580300d44807800424035000c0d0010009101e0489240c25445d081c0c0000302030408848100c032000c01c102203440015441e4242080d44018819a01c40422528030302031010b4114507c00c48000a14642c01200080d10b03c54290b0345443d00d002c0018900d03e2001d00b40c010140c5010003680140840450010350840c041055081910221404140d41e000c40d03500b0341000b1701a580c841e00311070b00c0d01c0d01d40492130b1050744060b0046001c1000004000386480c02050780302a2960050081c60500380350078600c12184c510207a81007245d0043d0040401c91110301440b00c0e80c82409a00016101ca08000d850300403a450983d40079025030212003041010790710071440c041c008506c1d00d07035003d04040701d00114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 347828120 1250 347826870 347826881
    0x114090a021c09061b230a14030709051318060b040905071503050702060702100f020903010e0d080a060311040e03042c0f1608100b040801020c01051b040303030f 71
    0x9400b00c0c1464028001e000468009012040610b072110868006000d01a40c1065034401083d120065012099800c40b40031005001c04840b86e042501c024401720829135041d44c401c844140114038076000500482c00c00b01101d90314801d03541010807440300c1030240105040c035940d40040c1000d03141e0000004580b140d4103c1d070075040d0711900312382c5100c0d1542d05800d401c0da001c00d203803030000c0d14040014210703a10008400e4040c08094000e400b072105e00496850143ca860b0401c4180c05800b00712840954509200b1445150300c0d900107041e551003940e80040c010710000d48030068241c1400c3d4203101091482c1000103828508a9000071091902c501c003508501a40d40240c05000342074114003510540010020484141e900c88582c0b541da50724044580c0d010185d54086840598045c0c24176a240101c05071504400076a0203800e0282c0d98091540d900d91091f08210b5960b500400c22504d01002406080d4000e900d8200200e1020f200003004013160145120240801d0f443e45017000d88010f00b903104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 347829370 1250 347828120 347828167
    0x5152a09150c1b0f030a08030a0f0b0909030904050709180b1807090e010504290a030b1024050901120b040911010f03500f0114090a02 59
    0x50700c60021060409480f0115080c40184c050600c440c40d031501e504c0c01103031550713419601400700c40c1162035a1b00c7c00b070003d02c0d108040b83c0d1540d0790741e03084505955483d001d46104845c40402560b0310609902800280c4402070900c005000300c890b000d014460380c3e0051800c0410070a03a0001c0d1801e01c040c0015410203030034004080f01100e42c001e100396140c3c401d0200341a00d0800715030003e03a998403800c0c0401c80b00c01c1c6601840f0318080c84080f450505000140074150a07006002502068a0b81c86050911106607850358595401a81c100580b584200405029450032400c0e09a5000350311405041e610805200d00c0c1004513074400301854680755408041e4000d40503108000da21550301e08060003800840030b042c0424905c410b05044a44240191400030b0120102c0c1c0d0302d031000321f01000801c940380c40c80c00781001c1d0008800500c0040015040c0040f4200031141c051182000c074612300740d101c0181c01615010207019141d4015407605244240c016401d91001070b130764010301c2841400038001c80a0f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 347830620 1250 347829370 347829373
    0x10506160602180a0806060a060305062205070219080a0f02030d050c0a0809010221071101090606030b06060301080a0b180313050a0b18090703020705152a09150c 71
    0x501500c0d2216411941c46a6501501c18007116500c40174100e0b03881d60100c400581c0310f40c08401c14014140f298002e039400a10181007852004250120304d19003400d0002500d0403140c2d2042000b07031441d8108010490b008184ca100c4a000d181625a040300e445144155818060710416000469100b0400c0324000c004e010010055424064108100d03603200400600000d641d040108000c81d0061080301d03040400e104442c240c412640101d00600c00e030003012807040c005c400c42c19011464082c0036849095201d0310000881c1421881c09408000010300201d000f100280014800c170200011603040ea00e170001c070508066500c5004256141c007011249c01d21a02000c01d1a00d152004010110706450007100c207510895150002911140078005800081000320b0003010000d0900ba100300e9003140041c81c0c0585880059100c031840c0c09610350003464100030f102c0030044034003840c5c0d89510718014200c40307036461000c440070400041c0c0500814103200d854a103c018107a4403e120464550b600314a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 347831870 1250 347830620 347830627
    0x170f06070804020102100c08150103110a11190201050d05100308070b10060e01020c01080a14040803071e0804240509160906060203190e0d110103180209010506160602 73
    0x64001e01c5810156002c9015104400a0404811050250f11401d842a41e1607030095030340c032003003454640c920342c506905150340c80350300d001140301c10001414440c2c800c2d16109810501401c4052038890150304071400c1d02203e20720800140e074080c0c100c03180804422000b04094407004041072181d282d80d03100805920002604004001400110b14450b0005a00700c41c2c5480e0340300d100707440301d25089200c6c03401600007000850b92507010f65440c0c1e402010440d00042c0071422140001c034842001c3d44c0c140da181c203010040258861344040c040345003002802c040c0c400b1040c64103003d882c558018200420440300701c801a42820000d40c041c14000d0001d030824030080c07c2ca01c850039110410340c100103040b4400d203900403030b0224281c0a0001112042e5005500c2c00858103d05801e40840300121b004106807507030310300c5040d0340301c043c44940b40e402202d90305a6080000005002c9401a207440030704d56454010b000c0150307031890842d9044800a94404c1e50f28010344d40b003841d103240d80000040c1060b2020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 347833120 1250 347831870 347831881
    0x250b06060f09041a0f010c03020303070309051e011e1116020f040c1116030c1e0f03200909070e072f06010509010f0902090d0f12090f050307170f06 65
    0x3104d180c2d202c40416140c10202c2000f52004540d9611081d50140c00b592041000c0740703c0a200758030905110f4040c1040e100800603074a6000400d200340c030190304290b034450100c4e11039201000880e61058400380c004000310728038034010800a0060715110001603400800d04019034441c03204443d03140e00300034020031031590000b1018142025211003403500703204040c417071060b4140710003c0d6020b50381c2041824201e40d01d05004014a00130940104200b2030f205040080c3c0140340303269110255118621441c560f810f401c042400349107071501c00f9031144007841c050004140300801c9034400d0f0b403003600e8003060559031720b0704c19a14030300881c8424550013440307591400d0b03e1580c02d08204003d5400d006444903641d94004000c0481e8003802a01070288008100b0050516144d0051585103009070402074500d42039215680e010b5110740f000d81e0310b0740c5809000b0507503e90021500c0c000d040c1c000b1200c250541002c01181c1d543d02d85016502c0f14032420600111089003c000c5046884021001caa501d841c06 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 347834370 1250 347833120 347833151
    0x2a030312040b0a090b0c090307211208250315080a140102190e0315010b0a02010f06120b0a0e01090812060612040210030e03040803250b06060f0904 65
    0x80303030151480c00459000ca0074003810307405071360301c0079400c414003804035207501400301d01c15801610243c0c0e051043c400d0015245001100085078491012560100c1c4041c41c2440c40055442002d102d04101c41c0f1020040681c40e4885a030990614040c1036000e807119481055000303110000ca41c1c480038070391450004102a00140340d50b46142b284800607140c40c1080052400c2c0d000350449180c0d2407500c9030300b41911134810740404e03c40710070041c102d4036900d0700b1543d407400d140c2007a081040ea04d0742c0043d041807515024000c6031114000301004014403842d00ba4101c410154008000b071807103001001084203585660040038420a101c8020003041d1402d00d8501d2403a03010b41800d41d0007242c0e000006607146410b070240c2d440320600b4580322100756102c0d420030440c0b9004604860a060352001800114038041002d403025001c07990085941d1941060594001d0950340603c92443c003448040304006681c11a14540181082c1c94254590300c51100d103840500514801c1030300180f810040c01c840021 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 347835620 1250 347834370 347834407
    0x3020d0f11090315060f190b0f0c01180c1e0803040e070f030209130504051e0615030303090d2012030105040513020306011a0c0f0f0d0f022a0303 64
    0x103c04549a1101e03881c2075112a800c2110841d901c0000e0508203210707818202000c51090700300204050541d80c86003c0e98600e50030004220040c450041810142103078244607421540d500c1c41e0403c5d80360308035640d810207841114011003c201c101201040c0300036060b141858050b0808000b034036115511040f511505a90403034072400024401004110750728002d2080390b40c0d014002c0c0030900d54207004413084c07000d044043c208440ac0d220318840740c1c0c0241604c0107400401040480a49404d003080c43e900010300c000c030903125100760001c10500038459000140071107803084508205268090316554800b01050742c42c0e0720111405890840d901101c00c100c02503050303d20885007004aa00c640700409109220010001e41542c0090300512001104131620788039002c0f9000c072640741c440d80b01241d5007044a0090040e03401e034800000304048100600c030b824002921407802c0c0c42a0440b004000b5500c1c1c401e4010481d541800d901d01441d0f28207008810700304800d000d03013281d50358064403104100040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 347836870 1250 347835620 347835637
    0x80c060405210a140906160b06032b0207080601030614070f0f0c021c1a0711150601020a0c06050705070501080106140306030f06040f050c010305060604030303020d0f11 74
    0x550301801c1c030351008140d440102e5501a2880c5040400c030f003101303a074642403c4400062a080c140000302a076a2001c0061146450000340072289080520b072000d01b40c8400f5000610135003224051000d0b8850040c1c1b031500e5a200407504006041041c0d03001d900b0050303e9003210b032042c040e06c000401409003a4000241441d00c0c0140b00849039a840c404607030303100040c0d0604000940341d2180d5000d045c0705901c001c0c4014001003051600301d03444100c0070001e05108030200e88a40d58045411660496540303c5580f00740c560802c4c00500748000f42580e141e12030404510111052000800c040c0d0344200031580e0305540c00005560001d84032000501250800042100d040c8280100031495510541c1001d040350581e886d01d440e01da074540000001c50700001d08190301442201020300c04071008008250090b030107403036002d002d0082814075a06010745015001d043c941084184034058441c4011582100e800d490010780303847d184001000900303400c1100c07940550800c6000c001e0440548010b02260 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 347838120 1250 347836870 347836873
    0xb012307230318060301053f0a0b13120804080d050103030e131416021c0f080a050c0a0c08090907090501030e0705060409020c07090204061e0c020d11010c080c060405 73
    0x98034980804c0800d200034010180c010b032512041602c10340c0e002e00d18884000742c120344442c1500d0a4018402d0003907146442c81e1040d845071145005010101c0308040c0c00860b004000e40c80211680c680d000f0390b01500c240c0c00c04200300d4400203010302c81c164003034403d80f2a203040103101650b568100144150100400c0910840090340b0f040d0f140314240c460300c00180ca10521080840d07aa00c0d10700d4045181480e4041d095020300004050b07a003143c00e40d0000c0c406000c2e180c66448550141d8000c0c01030000400a80d0703d00d18000904c542c01c0500360035200d60007a03620f80024004120b20b88520329000d0009225041042c000030f1220b100c0c1c00c00e1005e001d9a0003aa01086440300e40c0781c00743c4d90780109215098108808101c14001d0120b190010400d011011040b03c0046030f0b00c0440380202e9010b035100400042c088403005034000109200901d41c1c02030b074508400d1041d0150002244003071100e00040481a0716144644964041e042140481c2e800c0050b640c2c4580c0300307030f560585a040407902140c0c50f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 347839370 1250 347838120 347838157
    0x1a12070f090f1103090717030904050406052a120414010c0309060b0612061003060e01120201230901031a030a15051006050a080a020d0608100b0123072303 68
    0x850310002c0139a0700c103100e0000201081450102c10501861030f0710115100c2c0d000401c000c2110351103074007940780541e07c14200002d4903d03010380070203072540b0801881c0d2204a10300c004904511810015200c20351840f480812194403540380c55181699286a040565400d21043c0620550503602800348940680340500004200c142009103a100d0700c2c018003050300702000443c41606103a900d1140e031041034203000070203944035090008509026803120a044481044140855901129120311440e040400722030070050509010090b0180048440c1095691a05500c140010710403410204001800b6113000e0694ae04014100540304c0c600f5100e041d0030040440c0d5107030545081501100c1490b90740b40c0c1007954034a41100d845502030002400c0540901070300d2240c0080c0d11507403004042640003415001ca4000c107290070b90300031004440c140300b807640080c12540c18012080180f07031a0002d900d6559200c030314211025031440100a01410b54944446400030000030051025035140e180d032200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 347840620 1250 347839370 347839391
    0x40c020f070e0105030d05090d02030715180b0406050a09031203060905061009050603151f1707140702150708040e01120f030f0309050a1b08011a12070f090f 69
    0x40036821310410f50150710820700d80d041244644040c246036000100070003101807d41d00028588400b90b04000f0321588410806c3e42c00c650000c5030300c0d003018007428550740700918124000c01103000700c0c443e800510800169800d1041d00ca547c03494055030703204486011640707061800500402042c02900c04603454a0f01151851600d8540034420704510360b10803107900e00f010180400ea07000070f072408080454000351401ea540d07403000c0d48003102c241c0308504603003103c6281c002030405201c5a14141c0300c0c8400e0052020603039008c0c000100d408120000356a4407880e610110b0411340c80c0704100c0c2702e010f20101d030460404c40300c0e8000f80200c46201626010380c0e40c8505204803a0104910700410035802e0400c1880042d00581e884900b0000ba4140010390148940301c1c0c40c203006040c9011100c901005061816500840c03450030702902c0d612000700b2000004010507541324414540b03c07803043c074187c054a04240c00400ca40340150654203030425503070369100081805071007800c0b6882800c0c5c1c1480a00d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 347841726 1106 347840620 347840639
    0x1112d010c050703030513120e01170c04141909090f0506040f020a060e060d0e070f090b10030903120c1211030406050c030c07080d0605040c020f07 65
    0x1a035541844c80c008044030001415400d0700c0500071040408078100b0165141d6840190609811070a078010042e10803964030840750b584800500e08201032060010007a0080f212412400c1c8030740c002d94402c1001c40c0780010034801103610100700400000b18550000750751389009030f02c0b0401520319034546504041c0101e40c245d0b21500c45084100842c100041e981c8001d01440c41c0104025581800086141c8140651a040e41c2e4548800d1002d09501340500c00007886c2d25400100820342d600f0b25a030203441c1000fa0300d0b1149070395684d107000d094045e0007006840c0d9410b0382c480c01010000000390f0010a24840d245040009483d800b0030a00d00c1845904000c040c180c000350340380e00d81443c0072020388030010144a03513050240144a003400340304041e50340300c41e031190700e19449000da0004031001380b0540c0d0115500c1402c00003107650036a00030603140741c210840300c00e0f2081d2903201e03145c28 = true := by decide +kernel

theorem cover : BRFrame.Cov 347661870 347841726 := by
  have h0 := BRFrame.cov_init 347661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 347661870 ≤ n) (h2 : n < 347841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
