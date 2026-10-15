-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4911
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:08:14.757417+00:00
-- url     : https://prove2.me/submissions/f530b457-4089-4547-b67b-b55a6d58dc47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 883093525 ≤ n < 883273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 883094775 1250 883093525 883093553
    0x106140a210c0e10032915030c0613260d030207020102012408070b13050603130605092107030806150706060305030405120a050a0b0c19030b012007030816 68
    0x4004219402e2550800741c05030100700c0d00586c00e03d5000c2165600c4d0319401456603800101c540880c02407407101e0340200c2d1800314485031059000c2070224411842e2900940706005480c01e00d4060f000080b6031040c022890381d11051400095003020325500c07912403190380078203403481c014800071807610700d035400d191480c01c0c421546101e0b40c105034000744008001040403500400b54203c240d45407a00c0700c0c6d0025102011070040c42c4c820b00c3c001000c02d040101d06076090750b101d50001c1c020801c7c2e0801d814100d544031503069514440010041e403400e0060202015142120341585502034603a0b00c0900f00070703c0d031050700401c4007205810702030703600494a94840c03800a54890070040d0b640b14208820040440e02c801c6031143c1c00d40c0041200c0e80000c001040c03101200d03510901c500242e07143c00c415a00a80161948048060b01c1c4032200403009606030003000b50b1900a8a070303910041200303000d144c01c026214840e1400e9900a0a042001448200c000c02c080c0030381c185490b8010040ea5030b20040034500ca = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 883096025 1250 883094775 883094791
    0x2030c06130807020d05250308120703150605070c0b120604050a110d020d0501080609100e01020409020c010f06090608070e09010b0d03021b03011e1a120106140a210c0e 74
    0x300382c1e00080319281403c3c694900344425662110b60b8910758a0412920038440700840ae11005030100f40000c1c002e1308404150700f0b10398a641d104035265403000300180c001c40c400355101640030794001800c80c107200460781d04440343c00003400d04d03640b141d003480b000d40000f611000c182950350b07440c189407020440c060300042c0031245c0050703901c0c0c0c2005c200006485c03040e0008181604540e050043e00d0b54000b441c03030b0004613000400b24030300364650803090080c02140e02c0055980e00014601340b0031081940110340c00308142d03104204c202e854030710817011959140602d06e00741c2c0c0446c4042c070a010b4071405403640480c0708800454480407240100c0d00d0340e00450030840145e4407400403003065211301c072448000702400b58020050824080c803c7c00c0b40f01542a400300200c1d907204a600c5980d8a001081e8220311009000c5805c260080c5082034005c05462080410030882d118440506180c0b00d00841c04a0340521090014051401d130880000504030204440104034030000042402e000300b0218031a10403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 883097275 1250 883096025 883096033
    0x902031513050c040506063007030c08070c0507090e070906030803070801142407022814060730051b030c0d050c150a09020f0102030c06130807020d05 66
    0x1aa10b0201d10700604220854425810803080000580307441064030040c00100030100c0a550440da1104600c681906182802c5540c0b04200706880f82c06401103c1041d05654801200e0b03541c58004482020005a0003040c0390800d40d03081042060700d420250a84900e1010b517040345603900466800c94401d64011a8040c50102c100310394980c10a43c0700d801080c82d004622046c410343c03c0000e001c0c00c102403c5c0c0d42000306000e040e692121f1114265094251701030000c42c101640580f01100c80500000c060340b40710f1884001180036030341101420111103001d07000c0f0381042c43d40c0d07660007103c0400805c084561881d07513804000815440a1001e02c5081c1601ca00b0f9507420902c50514070000030700041740f50f9030300810982e01414800107402d9511201d40c40c11076216048121000e042510f822030b5541c15803e91024060300b0319083d48a2070701180300b2900c1c2c00e03c4903020b03401039889000b40260032200c2d0304401e001480e10074002952002007403058803014070380161940080e050700b42c00c0c0341c165100d501c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 883098525 1250 883097275 883097311
    0x30c05011106011805280501090606181505070804030c050405060108090c1e03030403031e210506010e06030f0a06081c1b050a1a010e130609020315 65
    0x1800050150094959801034950341d07042103c3c00000c0362404401d0340301103a42e0400991b5886d60300944440c60010030702011400b48000e102e64001d480203020b20030505280034400141d040c01a282015003050b07008040c03501902d0280001181614130041e0b20900000704020b0000032003140082c0099403107640701030380c6c4034200303000d100465100410741410f200e000c006029801c40005540c02e80c11004550600608001205c0817681c0080460f4103500b61002140220402d50011a5510b00c8406103101181c0307005111f5003222142440d0080e00d00c2c00d100d00844000082094004992012040c18414690f40201c000301d241c680c0201c503a150250500f505114412103e8090180102007040c0200f00b12414502e6240c11440c0d01100c01080c0560034452110101c4a0094242c2564001042c0c804810007030034081054801c0081c0c1c004012481d0300003107900c110108045000321004101c00c1d0001c44150782d503400030a0405c0c0c060740c3c14800c04405485003950b40486501c40c000303e14201900031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 883099775 1250 883098525 883098527
    0x140313080a120e0a08040308032e090f0921090527061005030601050706060306153201051b0706030f0b030105011202010c0c09021210050d17180a030c0501 68
    0x90307856103c0c03074054000c0a06000815a4602560706036a00500742503a640c44a55041010b103490100149403808842c029031110022292044110b9056010505c03100e4068080a02150104000104421541642102203001101e0030050216260900b0048592108002845040c40c40f09038211000a4052210684450050706802201c00d49240030651141074016065000041c034890410001091140901c130b50f9030440001141c00c40800c00001040003020072846000b03020b0300d90f03440301d000070380120848101200410803226071000100b001d076074401103034940d018001032000c0c07144150a90706545828420007005014503100001c000c806c64501c18191840590507a10036450800100a0358503800f5007040c09036070901e041d2680d18114600f0089101e8242c10010809101060a14100085070301c1d050050b032900107001800c41d44c400c01c1010714200114010199402c525007031070f0200c41040501070720540740c10358a0400d041c100c0492703d54456544240c132000c1040c00100015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 883101025 1250 883099775 883099781
    0x8150a151e1715071103091305060405071e121b0c05100c0503010b031314070f09110a1812111810030f1502030c0d0e0d140313080a12 59
    0x2060b031001401071070072507004041540780001c05950074840884148885403000380119000400300810220317290354044458001004100c80c414061850a40400c2410b806550350081e00c2d0010769025107035401c003d84c120b07403543c034a1300040c404544540300c4e0b0741d003124032210350f08404685a4880d4510011424203d00c0e15450028100109150400d80125541e200003200d054a20758081a540d80d02ca1000c03105c1540c0b610303031001e00007402a8078a2030890b0030204103c404c69044203108101c40c1c0d00c0e440e03218101c1c0c00c1000b200d80c0e981410050b001040d409180e4100324940d60011075100340e645d07103624148001c1c0140d81100c0181c0c4500300741c4d0032490202100305c086018441801407603d400c4070304c0c0c02e07101d4903400084d14440c0790001200c00c000b2601c0750203c1035050010300359141e00307145001002c0c03034000300f401d603606c42d0030602400307070014000a82c00d121003000d40d60407400d054131000d0010a58006000d400a1450307800d00765004c224a6402003c4640050380c0700e000317030031f610300c40c107811 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 883102275 1250 883101025 883101059
    0x71406060603060609010c050703050106030309080106060509060d0f0e2d0d0804020105031008070909050d0c0302071a04150206091c0206010302130b101808150a151e 73
    0x101d0542881071080c04d464520640c0d0000d13200303080c131580540b0f13503060080c5445101e0740010100c0d07090001c08000c01d544030400100b01c85201000f031100039107621703050700c460044000290f04440c0130b00c01507003444815084071040841d95400051640400b5001901744800504100944030030304140440d0b50503166900060110400c018220401101a00401d100300c05400641000000b1002c103400300c03019075020000342518000c48101558031140380e0090229110180c81e42d0003551100001c0741d00a00380070004e650b0650240132003c0c1003540305080e20310b011503651360480d4140004594040318034030651080c0c0309900140901e240240000e071910100341034810300c1c8800c0e0504031084980000740301f41034aa04682180c0d04507003150b0340c140202030580c01140d0000c0c14000310141207030000e0741c0510307841c142ca00414949444808a950f207548040d504101855104c0024904807200d80c81000c1107907480d450311004070b40d40d002101c030896404050301c001e14422041003100c40c18010305510 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 883103525 1250 883102275 883102279
    0x3030105010f141803122208150615040801060902370311070b07080403021606081603090804031a06010e010e0f04150b031b0306100e0102011107140606 67
    0xa4142d6403410120440c010086400a0302e22035002040d4141d8041c03100c10382c2c2c0c200e0b0700e0680f522030b1f5440792403008904d40241400940030100c04003040c020f0300802c4100c032100200f10032103226110b0300140b066a200120102080301c4051101191200b828011100104a031b8000542c565590543d0348422044611121034a22000c4840e041203061081c011101c101c01d60900007812003451600c280b4902c6010070091801881500f04009a0303008500f4900642c0039a08a4010b81c40d0303851785d800821524085c80380890740076400200d5240010b402000105803030b140c0031078104825610b24a941c0c0080d08215807900410f800c01d403805103651005507210000f46020805070080e100043c10038024045032500945a0b2a02c01009071a96000540071000b40600c884542e541c8800c4020b1a800c1501e40aa10b050210022240c030103404003900e001e000020020b081486011605a0f0122000c500d1607044d95264000e50203114002c2000c0c00b0f12a00540e002d280e05d241209001303041000090040d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 883104775 1250 883103525 883103537
    0x80c011a0406140109090c030f0903021e0601060905151201060507050d050306092e090207140708031c140a020403030e03010510090c020a050a03020a050610031a0a0b030f03030105010f 81
    0x720303c0c2da03800903020049075411400050884403610040303010701903500c09000d090b410401400c0405034005030310700441a092044198043d40d00103030303940b118401c0c803078000040e5000340140701c1c0385040500719804441e1035480e940760600c1d1942c0181000d40036400070f00070800201d0000e06124040c45428260340941c5403040c0343d89464800188a510050900ca00d107a034042d6540340e0380c290340b00460065201500c03010a0b071503903480c40c0601941c864181181d143e200d02603121421071000550307406031182074015604000305c88070056122496010032601c820f03240c0184600030300d03a451256014043c80080507071b43d10700754280500441c2004007810f0080c5e1600301045640b41850302294203448100c0c00c003042040750300304220302d0100d00cbc03140682a0702130011410109034002491840d2640306009072003483d500d503185034000c0000c80c40050909402086c0390f89504000d0250240d00080c05040002c21800f0807005c645031000a4020401d6130340f00200501096070040e804c1c401c1200546014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 883106025 1250 883104775 883104809
    0x415020a181d090a080d0b030a050129040203060307060c020d0f11010f02160306110f1317060403020307020d061103130501113c070b01050a060c0b040f080c011a0406 73
    0x5059072190015131940142d0350089044596001e000060427250883c0c001c2c00050860541440640303800c00800769164800141e261032400c0074000c2e00d102d680c0007006498a2490035500780c43c5c0c4603020b04104c3e401669009a800001c081401c0c0c8020a4014240e07400319510020003d008800e6113801082994041c40b032040c8003091028101040e680d01140c0444c5800020030f0a80c0c040c00307903070701c13a00c82e8040c04140364010600881800f41111842121200d14510b070322007080d2501c60583e0080c3c01601304100351009810300d030702101c1515100d000001203203421150540942e800070389080840c44140d885900a1160901404201c11601e40c42d4a20b01031081406081070703da01c0f1803101d10010138018000c000004a8440c8403146001e455213139840700319150403a00030009014840c8603407421000443c40a01c650700e41d41a0036030003850703000c042d1550380b07400c00740030b45c6904102c0d034102c810003a07032144030f1302030103843c412203010304042051841c481e003008195103280d0440081d5915542d40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 883107275 1250 883106025 883106033
    0x1502030a0b0402160f03021c02010b1005090d0b1308070b0610110c130f0509102009120c0301150609080f0a08030901061e031203050415020a181d090a 66
    0x71310b1640c50b840502c11400c4086803030b007a4113000c000c0b0301006914403070141d0512042d80641100700c19001c1214154800c050603001640d0728068094200d40040c40304a0541c00140384400301c40e08510100d0102c02e43c3d00030f513036030558030354080ca2048460203040000c3c0300190402e01500f510301c404504101404950703003088140e8520380341c6d03d090b2003003140600d84803036101a0ba00c540c5500000100501107443c154440c1541d0b880712003030041303880e031a00341000b8803810701c135202c1c100d00c1c00c210403d070f890003d800c41080b80e10380708603c1184482c00384140040d0282d8092090700640f01600c822004042d14180001d000d9210075448005160440e00b21081900c1c400f00b800c07011181d00400c4241c41342c90b1a0013660040040d83c000c203d04124617404407405400c101c1640c0c0c11170788034544180785038410a504400b81d0f1020340700182052202440903031035503419005824030303058610307086803c24a81070220500c2051039010b10003078400c03080075004151a500210764884a014014110b81c2455a1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 883108525 1250 883107275 883107307
    0x10b03070b1b3c01090b040302060109060501051c18060608070504020309030904230f0f060d030c1e08040b0a0221040509190c0e012a060506010c1502030a0b0402 71
    0x10003094070301c40d40030f40740b0008100c1620440c52907600d50080211904911341645001c100741c17070031b5000d4441c0310000109901140a00c605441041c1e45040c2002a405040300d4209000a04070f140c03039031200070241000605c60003011000d4001c41d00400d03420f1601c060302d4107010a81d044540294010001c00545210000071255081c1d4103503800901041604031501400f880e648000c544036100c5030070300c031540131030907a035074001d00c2034500c2000c4646540003002034201c070400c2d00030041000c1c00741c0d07040410040301c20400c0540c0c2580e88181c02c0302c0a561030030a50351181d041140320302400b2a80040aa42c100401d10030422101024080035411510429080c0158843d10b4410381a8030000350f03850a010030b4101140c203c18200f4015000c2c04000a80f003604d5041c3d9841c0001c1040d0103180d01e0f1045410b06040724141e5100031900d055245e1100c101a10008164505000241d510754000440a180c2030b000704210f001c0041e107a00700701d090801560068445180710360f00501c044495440c01d0301d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 883109775 1250 883108525 883108573
    0x32b0c091a07021003050703050604051e1009021b0c040921090b030c0a020607021207080f07051906140402091501020109020916080a0e1e010b03070b1b 67
    0x45071460380c1d141070740c034200014030030b1403802900010101d001ea41c2e0550103400082c020142a2001c0c0000d0741e0343e00c00c0c4000c58004441400a4854040541c2e000d80c180c80c050541210468500c48070031625088190281e03032211a8900c0760b09002d18442c840c0d110b0a000c101c003c1d681c00c58061018080607150701d0151401c0f44951300d00225402000b82807140078612040c0140200e07500d040d144c1c1342020440340c0300d030841d00e0640054040c94000403000c5101051101100b44c40d0381c0c9160600c8282d44400d58642c0100c80300700c04001080020300045502003008281101c070b41c044d4000d03141c15501d0b00005170345650001a00a11160742031000694500e61007036403200154034680352044003440103d025102c114000b81d00071a0200c01d0001900710025181100c4119417202c2c0b82c5519214842c408403910b07004035200d1500300c11550705082d45202000c035201c3d4010000807032149800c00002e410140c0c9507003c040400000030f5440c01c1100c820400080210003817020306055582a844800946008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 883111025 1250 883109775 883109789
    0x1080d050a270909110a0e0c09030705060f1b06010506071419080903010e24040f06050f070f0f08010501080c07053c2508032b0c09 58
    0x41e016016003070b44070901c41d0400e000340380b4407034040d966000c128010030b124074083d112042c00c031140340d1755804d090340c2c06003c880da0700038120070980d5000f007141040c0d04280001585402200000502a642c1e00003910000300003180c0c0310783e9011480f00760f00302000c0030798800c0c1142d00181d004200d681d80700030030307108030a4100041c10480c00d20700442130b04161140e505a110070000494000520050b0700251903042800d03002040341e141290b0b00c503960b8120301581d50fa0502c01800325035003299500382005401c0b80c421180751074091103603a52001036074030460f9500383d01103010b020400f0090340421225529941410001521840d0714001030a40d6014010103041c080b051002ca648054040100d500c190f03000350a4500002d840c801d044c0b44800161200c0c01e02c9111005001e0f129409803601d41800a0000020903014601c545041c0402460103900d00642c0124100050b14020500041070740c00b240c844240000f01007a40e00035044041c0d40c0000407500e02e802c140c20700c265040100ca40580c0e0203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 883112275 1250 883111025 883111037
    0xf0501030906020405030f1b030309130c0c02130f0506060909040b09070b0f090a050a18090305070b070f0f09140d02040204051207060801050d080f031003060606051201080d050a 78
    0x1070390034610080d104039403000343c043c031130b130145c4d40745054001c5440d0610b41c0a5403024001c910403c2c0805680740901e82945502c0210408020381140c001d910010b885aa1820f01052010003070300040e0b08a0328488a80c44070640301d51562560745403522556a02c04402c4490900b84a101e0001c03c1994000a0001300101807601c00706c0c02c44c020401c034050080040868040da01d001504002405401500400b4018100349601080e1460000700702001e82e0090351080e181104400060070242c4201001501845400c1140801150b154206284111034a4482c2c03000710b10000c50041200406030075000c01c00082c050b003408003060f02c84003040140c800311041311203c041400001d000f88601c0e880740e54441c0d40c02107600c4030b860000c60144111103540d00d4078001c583c5e0304c0f010300440b144050b400a04076882040645901e201403009190090a0503044110981d125511a400c40c0c1c3c00e03400003000b0410214031186c8415066207031901600e00b9034090075010310f903904060710743d00030b06003c0b8041c000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 883113525 1250 883112275 883112291
    0x180303050720032214011d1503160c080414010e06030406060503210316030902090a0b132304240b0a1d01050405100807140a0503070f050103 62
    0x8031451031032007500b4500c001c10740d51002001c00641c1d240d104140080500c8645074822241e0300c400404001203c00141406030640d2030240111100040940901d50b20780c8180a12005a201c0b0303181a862610307400c0c0c0c4103550b42004484082c444c4203280c40001000a008040f90000e02032605035030486400e0003000c400b5000d1030300181c60500d80c01c0c00382074001d8804001c10061040350380001c01143d009509682c041d031340a44406400c03600c4c0c2118580f40301c0040022078542102590901410b901914000a4640080e400078410f1031050728031600316612132980107543d140048885804800c071880c10010b485081160400540400003284521241a00041c00340028140d440b80509400004000140e10b4099080003c11030340300a035000301400180440c0320040c0301281c0304110980404c01c038040c1c0c0303060b0070880039140040c82962445111400040d58040402040002c3c01200d804001481c103500240001030045a0200c0e20a500c80142080104c6008084400741c0f9801c3c600410f80407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 883114775 1250 883113525 883113527
    0xb1903080a0306080a05070f0806040305070831030c05061e0307020c030d081605070503030f0a060f0b2106011b260a0f02010501060905060d3c1803030507 68
    0x40f0a9074008215805002c1c103c10400901003066015039180400000c005500c0d07034042d5580c0c01084400401103001080300002180b0000e0103420004149030b403d141d280c4121540c0f6a600c010201c00042c4c0b400124000d00800415032000c031301605d0259105400d144411024040c0200b00c1004100410030020100711100c3c030a0200c0000c807000a01183c41b003c8811900a0100380d0440720b600c0304034240304640150310710440456a249400030300030748c250780780c103507400c00c40650140c40505190f6071030800041842048210800402d10b12043c141c0340e812006060b00d41d90444110048010506403c02080e6030304003201c040c481c2014000c1c1d0300802010f107840035003544001e0b44245940201c9103030b0300d44804040b00510b25074410350740d0203000e1045882d059007655400c0c000e000201b110700c0000d21030707800d21002516241151140100342e42820320700011071004009150b40117a545015100603000c0340d00d0098030500c0c24410204140118a0030b200054581da000050415444502095800f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 883116025 1250 883114775 883114781
    0x60806031203010b19030b13150e07020d08150a06050d0207150f0f05010e0601050c0106030804060206040311030a08013b16020105130201031509020c0705040b1903080a03 75
    0x1001c030604071540d030b540c6907194910250840c0c2007082c1c000038034140109600e8400e01030703d103808201400904505074640f400f44041c08160159050a4400040c006000e80321440320901401c4150041c01000042d000009c282c0e0800508084c1c5200038845441c10361344a04c0900e00807a4850b1408a440e06841d511900291282040103000340c1c0006020643c18812070303200c1c00c05410505010004420000080c5056400900c6880c4034441c1d840009245940140000c2c402d90191200014459440f661030007a560090781101005a000700308010400da0001c0480003500b480400944c10034045420003044403905006003046800c0c1ea840d07141580ba9842018407043c0884010115100b10410b0281001d200032130b0040207804038407074002050350040c0316243c050203403400030b4406161705070010b6014080f2403602c40550b4542c0b0390000b030307402c0c0c40d48080c21503881c207a400390010301d00d014200700c01d40350950112441400c0300e030780001c080d403000d21804003180d40c0a181d01e40c980c45944002d40003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 883117275 1250 883116025 883116043
    0x2012307242a1404091a0a170607120f0501090b0907170a020702040608060a05040303050a090213091a0c030f010f051f02010608100b030709050105010c1b15020109031e0906080603 79
    0x5d904e0411118468009198580209005040d541c03200307070543d01e513240402d00b201028028080e03000305010a407803510480e1a0204101402008585c4d020748503104400c4a07000d138020901e9503030320b10754402c0500e480c0c8107440c2c001100d0300e403060301c00c1203604000c0ca0008001d0840e5495950003c1c090341103445681280b0002c20114060703c0e91890f1404054014000440741140024a0040001d03040c034454441c2c440495005040c8200c400800d40640c1c0082c9800c00003910010034480003020707030801c4903104a2041e00c080c031510342c80e030401c00c0100703100c000d0603000602c000700c1a07242441180c40d0306008544541c0110304403039a848070300b03209038018141500000d40c94066944c900c200302c602600162401e040039000c8801d01c039a00c0c0000b800325902801554001200f06d180d80000c681c54001a49945800090405c00c99a8410905a003202c9000140c00580d454148003000d254210340c0851003d80c072910034500521421000030081601c0e03024840600410001041c0b150301c080140d296 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 883118525 1250 883117275 883117289
    0x3050411040c03021e0406020309011b05010e0d0e0d020919060b04290901020601170f100e0d030603030f1206260d050702012307242a1404 61
    0x82e03040d903410020041e40c80001290040c0b4141003040d024008040200c400301d0300c4c02d034091070510000c80011540e000d00b5030003005101072207071004404142c0038492840c514400200810401d00c0e00384000e000b2415090200d4400c101d0740c003280000d80c4840500a610003011600e08141355400244000105001d03041a00d07901c2000c5030210312041142100203410407003a6040300b13455030340301e02c25031144100303d040d03801a004000104a030f4070f14000e00360280ea40b400c0940d07400c280f0b0b131003001c2d11707100d11205074014503610b078080d000342c3c0c4009001040b01c408492400b404003505546028004400900f2040b08100125078034002d03410f100e07404580900a10a140101d19004202c1d0741c46a50510301088000d0107100140b51030107000d00c0c00c580402d41e06840741c0006d0740d031000d64550403502c508100e80300040104210000030350101010021030801c541072502000000d18410200c400e4500c1c60500c0840b14110b60b681c03118050010800d0441614002062407025132100d4914010b6903c200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 883119775 1250 883118525 883118531
    0x1020c0726120a03181b030317041106090a0f080c0301140f01150c02062d040b1206190e0708072a05210705010b06030609070305041104 60
    0x10500c40c01c90041500d10701495840c040c00c04824003960303034844103000c548118000c81049841d01950003500030b00034002801280c90b030103202e26211420f07510f500707244101c50107150201c188105034101e0510448005403440104181c581039984c203c110102e05da42a100b900d000c1101c81c06940c074002061f0241401e010b662013540d40e510f81d5595980803446981e482542031441d481610b038030501e00d5030700c100640d0345101c50716464841094081e90080b1707900300402003d4580e20000d0b0321000010840e240d880500700044075000f1032223908020a460010013482010002003000d000b6030030654000f03010070002d18406494281c00694030040c41c0403490b41e90240715a002900e0000c800300c0c180300c3c2d0300079200d0410750b0b603c3e110220346042e004980707003020304440301c00d0402c00c002060711003401d039200e082180c81142c0001c0c5254581107030b51002c0000242c0c0091088100042070064a00042c400d0b0b550030b0840c203003107000908509004069008160740c8800140911000140359185800064020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 883121025 1250 883119775 883119779
    0x409020f03010617010f0b0109171617010b03010c050d05180a051608061603090501060504050901060f0e040206120405070b1b0d020a080a030b1212120f0613050901020c07 75
    0x140e40e0b030300013201e040607294030308403100b0115149801b800c01681016550100640d0818034004c10502c15840360315014817420790300d200c042c03a07095014000780c00b004a094144c2031140e84030340d0a46e29401c03100c03406031f41002041c10784650000151400c03500328010100d4981d440c80c0c5081c40c0141c00708941240361103007526040034408d011411850b03101a10940a1072147c4400060340d0703e440503500c4072002e580c041481403110307200381e00c541c3c1c0003442034001150750303a80c40c000141615401d640101c1d50781d54503181000011032080100004094035a20499103291a40018010340a211080f039252690f140c002420407005000f244081c12141066503162074800740c418007500c1c0c41c840214524854200360400ca1400041c4414000b0f611040075407a00030480340c00c030090000791070015045903410781c40941540c1d0034040c8540700d03443c507581d0544540b00c643c0d0381e008400001e401d55281e42c042d401881280e44851980c41000c040000d808102510380488083c028443c43c104815140902e101c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 883122275 1250 883121025 883121039
    0xa020d0b041b0b070314120f06193c0902030118180201050903010603020612090c10050409020f0f0c06090f030a0813110a0305060601081608060409020f030106 70
    0x40300c0d0040e0b001d82c007820707070101c1c00d104408100c0009005101407400c05000c9440068032071030f460812400c52400d21810303c40205000024208183d41e000407202242d01080540d0410600c03800d580d20b002d4402080d014030f0286c118003d2031848100d0b140b081e00c0854480261001c1807001c240c1140f4004803d28850358480760480290820b0040c401500d15116410480700a140200e03010480c1c00403850300216900ea00650f01980010302158055403078441c0003001d40d030b0303940c0a001154103075900d00c00240303011080c640c10310704820310140c803410304000349290456004040e030b015a4040e100059451010901344034403401460465403071810300150b02248100d000c00e15500440031328086800d030740c0c09076582580300d0050a032844c000811000000d06030902c40c03048180090b000c0d015140d1904640e901056040241703400640741c2c1e83c07000081c070009580c0030101d40c1c1d100280c0c002422500700d0a8100614802c4080d02d0f6500c91600c038402c1300d00390340d04d5078890040c514008001700140c60350340764 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 883123525 1250 883122275 883122293
    0x31b0a0201020d0905090a050a0b0d0302060610030912080c2713020423270103050f03030f0a020a140a0f030605091b0a030f09140c040608030904020c0a020d 69
    0x10003240140200143d10251500071001281503c038018040e140e150307a610701100045c080140120846a1202c202c0c0e411604c903024101071990007940640107514048050021110343c03080c0301420545480003072400310303902012901c0100d0252a040704240c681e0107402c445801075081030020020b0409400081d00c1000d200c0451000c400e661803160134014000c4801207000303621803010f501a4014881d040b11040071000700711640002c12039880b0710f404c40740340d82c2010a05051108090300d03440040c001d00c0400c2000c0045d074285000150315502e0074030740e2a0065034002e404154680d40201e0021086070140c640740c0020b007008401d0b60b80b0703a4440c001c010004803200c030f105400f2030700e0b241020400342080c0240901c00d2800c44d19041c029601c0491b000b030321ba800908603004159403190300043c65450ba00418401c1401035121184520700d12150740d042000310b581d603501c51840e0200410803031f038001c41510181c3d0b104a80058031502c00c8040142024080c040082d4400d242490b03001c10801000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 883124775 1250 883123525 883123543
    0x10f1109040f060f090221070c0c121104091109160e0307030206070807080d091101030f050601020606210f1c0c080304060c0306150905100c021503040203031b 70
    0x89051203810300010b40841140c01c80d000c2d120300c981c0004800d020b4455960018009a6019407005440c010440c0b03004214510668282000070070410140c2d080c00086041000a0300e0a19444903175000c0d41e81d01d040e60a20072105850041e07840300c44030000d000150405411842d00a801c2d54040e2521207422041c83c4010305041020420001f0b40d1003003801c0029003101a81c2d03014244602d0407440352101c00c3d840c1c20141040360f50400c1000b5410301c601650040c3c80b0303c0c511070f0b1145100103070007400141c160b620600060401e90b00e0b22003003240c240c0e80006c003542c01880c155040c04030f0301c40945d2200e050710060708040c10b00780f0600c1c00824400c03000040841005a00d14102144040f250000300d655989801028050321010f1010501158159125011070100c3d414009665a990414000007442c0c2170034181c080764440b6400c1143c0e0030051140349289405107003290064038160700140303842020f000c0303000440c4000310000d008c64400300111509034089070520340e8000240da0403103036604461 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 883126025 1250 883124775 883124779
    0x160203010c03060b030609090f160501021005060108181002070305030f0c0a02031b0a0c0806060108011403030403030509190e0114100e090406060513021e0403020d02060c010f1109 79
    0x94419402031191261400756440c00c074080d0f2440d114030003001509a4040c00641d01e5010350741009522712020800d1007801032001000314485460030002a00340600b040c08019024145000c110b01d580c0d00215450784041804840c02841c54a500d18030b2070114201c0f040c0750458030000e100420b054101011318440c4518149401350342d500c0d01c120042c5030040c030500c5400760f4401c2c0060003008034a034502d1300d0b0300c041d103404031740c55242c4c40c0c3c46182d02d003003496021840b03039085101484000d59005c030816025280c10000d001a82440c240400d607070b03220724840541000340200b400542c694032085040d8055002d101c00b40406602c52080c0030500f0350a203c1c0c81022498111719000e541011596040b410700a40c42d035441406a0350103001420200070720860f0f42c180d0318040800c00781c2d201000020441149640181c0b40e40100c848103902d11404940780d10444424002040160345144042c8003250703040e590b0700d480d80070f0b420001e40544003a2652411301824030304c44601c10300040c005021b00580c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 883127275 1250 883126025 883126031
    0x18150f02160501110c0a080307030b09010f0305100c0f050a0513090e0d02060c030411131509060501020c0303090402070201050f03010b090117130332030403090f0b0406210216020301 80
    0x46160316510911a41410400c0b50b00401b025802040d918009103030b122045040c0450f807580200000354055109802c6a900914203035014014020204410701f00f04ac101c510410000c400c03141702401d030400d2003114400300040026681038840c171520035142c82ca40381c86803140c1040e031101d494101510380e010712502d1b5481154080401d052000507420302901403075154510319112074981481c00d540001115401c03100840c41a51050b0003442681c10b0007185074410440f142c00c0052050a50305260301040c11540b2000c042c40342580c02108540002074100e030300503a075106520050b100d07400b54850820031010048000030700c0582d40030045c8a85c1101741c0c0d0307400648001c449681024142600c00d90a00200c50144000082c002c031159800c051480044812000ca1000f920203402100c0070381c0c0281010101c00e010815400c288030740040c00800b00880f1007541803200b68145c0c0c1c041d0388074800c100082c3c41c4013003400c40c003022401c482d444007904d070a40d6550581d02d81c1110208080340100d0203986 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 883128525 1250 883127275 883127291
    0x703050d021225030309150b0906150d180203030c01060807090504150e01112d07170f0f040e15040e0d050d06050a0f0f0918150f02160501 61
    0x2e8404540110b00040203212200c4004000d910324041e00d154200e042c140d480d41c0e400003003802030800c1900c807492071201040305501170091000301100540010b00030a403a4040c0c540e001014010354541c400c5540300041c3e48105a05001035520145002135014000015004141d1f5019000442950301c064121480641e0341c801c40310445801302d034003501d41c1c07807820340380c851403151a0841c00381d2115000001c240c05a9121588035554801000c40400c040e00c11100184261001d841d04500210301d42d1480c20041340f03072200021910300d07204843d1015400901001d410b072440c4195101011580b22141c1c44a8803440e650040304400d440c00c0c070100e401c100c403201083c0307814050f07442e0b44000c0c640030385041d544102080e0f849400000c42212040d4940c0c1c0c0100d844e40f560030002c80140010315408c80054a0310800800000d056040f40b08001d080021007000c9000c03400e400d002c41c681c000d039903000480c00701070244002c10628011014076400050341401c8001d00340c52901185024000800c42a6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 883129775 1250 883128525 883128553
    0x1d03060112080901020c0a090b03010518060f07090f03031d030c010e150d0203280b01021c1707020105071812110625060c1d100306080703050d02 64
    0x1110074828901070180030350580c0c0c0011240406403002040c180115000054100001406207085400c48155607a0301d108260070380c502401116004014012582d991148020410382c4501000300000000882d80340800e2000f84a407420710700400c600f50301d03120341030b44a14008000d0580e11400e1171003003111030354990040c5030201b0418181c03d4141c4480c3d0b420280f01e400d0002030b81d1140c006244140c0c0512040c000030340e00c0d0000354424000780c140344010080712100f18806980b45007240c0501d43c5000388103113540c2d800281140840c00c0c49121000034444080c401c0791540303800400c4000d14003030081482181074054011340e0107118a5152012880d5000d11013083c800d90350b00c40c042d140101d03a0000d4004c07494012111200040c0542280e15001555000000c40d11210000c1e0804000142212050081c0391042e01ca6650652410407440880542c004911480c407000c424404d030040410403e019004e544494002c1120000303442c50260b8905103030307440c1c00d6808100d03000f501441084060394 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 883131025 1250 883129775 883129783
    0x30b10031119090b01030e0102130e180601030605060d140708070815150103020c160f0504020c0a0b09071505131a0a122304020f010e0d0809030a0f031d03 68
    0x4044080841c060303483c602070320007010304010340344a4140741c0e131400314140846082c0000c0082c5101c2103a407210203460944030b0002d0301e80c0141010810511602c40454010005c20100d044075045040403400361580c2d80050014a503c01e4018488194201541d21381032010515004596a010940304256501c200203078450b03c0851244200782441c3c2c0002da0341308082d1410024910b8180b4005080c0f2590101051911040c0c001942d08141d2455080040d514003100c1d0340d004c2c2400360b8095040805095045a44a0618a0082407580c420300010707041c4508002001c010103000201d84d903a00615203024140b40e20000b4a00c072003143c0c101c008039492052404240140d0000702070030b407420740700d100f080761000f503c8081c1c030300000d17140d018914858030f2003821413000d941c9039402042c240c2080d104014900316070400250520403903544054465a81c0e62941645940000384142d0700c1110300d00082c200125048020202111529a10141584014000007400c2e80c0c420254801c40e5841c1003640c0c0d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 883132275 1250 883131025 883131049
    0x30f3c051003021e2809060e0103020d140105160e0d05070e04082b0e07050906060d06030209011d07110c0607081201091a01140919030b100311 63
    0x81100c00c4000300010b0a060003078444000d4207203441501ca030440d0b0b0004402d102141c0c81001039405c0c0d1a0030308001140310484000a100070041000b00030304d813404400f004001440702074031a5500d48154401c2c8048140b9040200304104020803c1d890031500c1d80104c4038030700c150365000503403a0149038201d0501075072058007150450003d0900518111400041c2600100110303000307141840328402d00104200b00c8800d0030402c202d012254910010300000300c5080118590071980b209500b00155183c0422258009000356440c540da10046403000001d0b00c12a8402900318450b000000b900c006807080103003402d220b450880c142e544680c2e1080300c1b4121710f222700c0085a00a401c1d140084d03c0c141c80106010b5100361001070801406505456940c2e074240d1021082c2a2100401da0fa0341c1108a401180202c0909000c0000005507050440a0040b4002c0d6030054039812440c1c0c0d44180400d60000c0115070040342d81007640f80002a00550285c3c0d40300445110041683e9a0407901c2d0010803009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 883133525 1250 883132275 883132291
    0x2a09060509220e12120103080a11031801080618160315080610170c0f0f030d020703031211030103021c0f060204030209061e0f04150306091b06050a030f3c05 69
    0x88642d01f551a0701c2c1c80b40d40509804000c1c0300309014a820000000d00142024030741a200700041200c203640050000080180031a2007440b1000c00301d4003a52140551642040007018000556900d103407091f802019144a900040d5440f80800182100300040c0b40d442000c403424840c01c069038513003220704554840d030b1200069402485000c50035050405503619218801031651064040850110307091410759009040103801068080c024160440c038210340e00040001c00708002c2d64400003068250006001c0240701d440d281080a10300c6140b40000504141c02c8914010703001c003181341100080d8813911080307014545100010fa03d03450300b00115114000741d81c00c0e4401c1047c2010070002e407803050388001503100d65100c601200300b07140401c20201851003910000781601d810706001f501d44070501d07840710081c1c2c9801d0041c02419403220035541501b440e800d0100e82d00e06444256000341001e50008076100c0502955101402d001802c0124182d80c800020681011022005003d841e0200e945038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 883134775 1250 883133525 883133557
    0x24211503150a02130b0c010e0615100c0f051e010b01020118030507060617030901020709060b070b04080f07200409080412020604030807062a09060509220e12 69
    0x1c840942d260001c0c4031210b14800605000c43d1614440c11301a0860601c45825a5503031100b901e00d0802048156000341040745500717054809400000d003050740702c1c0300403006c00a90340301c0c6400308410132241121503603108094a440b401e80c07a80c07281403800301024180041d0708000d80d4680700d50040c80741008a1412481302c0c8032800e01c0751802e84081c0d0000341d080324240e91b40c140008080b400144000840046400034503a503400e15800240303085000c0c0c014a460506d400020060307040b050302120300c40c1d0b07440040b008031503481d8205080580107020404800480001e43e0204000c40032015000302c0f094585071000449040c007c1c0802c84601c6500180200d408200910480340030069100c82c69100a1040b85400e480e0303646d1000c680c104100c200c85060300c0d4400450200c0b212050301c40d18811600c18120000042d030300052012881344140c0041c010002204034840d12860455104c03124491070605082520f00c040c1c2c001045031603a03802c498010300003419558210f80d0101d0b45440103041d03140c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 883136025 1250 883134775 883134781
    0xd090608071b02012601090609020f12091501060207090606080615160503040b0c010606020607080606070606170a0525150201061e0305070902092421150315 69
    0xc0c100502c12003a030500042d1821000036508154171240355920100320108507501d841d1031041620081e401c0008c0c6540144140200003102206440c9c001c1040301e01c001c81078a403002a13030300305001c00c0d10800704500381900103c0e1075900002d2803011500b0400f81001031310b6541408407030710242510075990021007081d0402c202c6000d1405002c40c84012017244d0040c8402c1c0d60f1b8103103181d006030722802c0c0044012901030071a0800380b1410004011900181c011444c120000820b140401000b85110b10070104010381031012035030160014100c0590500a503100810981796103ca0b0391008991510406507540c000c06840300f08280c03080303101182d545401e820643d2a4020303006480d9204110340d0303078040000c1c1404030192010b00201c0100a0b422815003141001070a210301600032402a500402403080682c032002c3e5004200703880c426940c020034005c401100c51034407032110b8a684183c40c80d000031443e9641034415500032018250f2104c0302d54059014187c81c0c1d100e0145807040303200c000c400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 883137275 1250 883136025 883136057
    0xe0a1a1011013603300606030f1a0a05091503070308040602010b0613090207021f0201141302180907030204110a0e041130090d09060807 60
    0x8400140c00389828031511607514208100d00312440000d04040001c8042c04800204620f00c1c81e00001c1c1c41d01961070f0741a07000320707207000d81107414140d010840060208841c4420000e040c110804144090340c0c00c0c000d0aa440d44028060500c3c00d0b100010a89007043e134080c42d00e0359a0500200020240c540d40c0c004d4644000c100e0181001803036401c80042d428206461660705009080107144544081a102d606103800242120100c8400c42e006d06e2080245440501c04810f0000440d00c1480025136510344600c0072422145003000000710703214005100c041d00704d4064000000480080d8024691030b680c160084007444202c840194010b1101855840d042000441c2d60703520880d00c0c0b0803200d0465032a0b01080c100d510b50091004411030210f8005200766001d03c000031845400c45040c03112000c0300304e0303102c0e4900c14040d01040c60800e5042400d58082c6c0d40314985041c00f0000d0001070b4900c3c000c02e48a495070308003042180020101c0c000401c0090281802601512440c4d4500c2c0c0c0600c6024a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 883138525 1250 883137275 883137289
    0x40308091507110118050604030f0e0609040209040905150a151d040309080a0503030a0b010302032710020f090406060224040c05131b0e01170c040506070c0e0a1a 71
    0xf5000a01d5490301207407032101c1116440a42c01c2407044000b00110714117420005d084041102060041000c4c1c42c4051842c0c2d9640001e8415144049a00594440d9200f00290040601c1c80c801050340c090034002c1d14601c103441114030f00c50305624406000314400c0923280302c1d1503046409000c1180480000d01100c0002100346254818802d0502060303031502e516a05203040c0104501311001e910000401010b00c070580030708403140c00700307080960550030080300e224102c1c80001d8821325280c4d922240c80c0c00f4003008104610900001d1320045581300c85004031000c461b40620301c010b024509000000604905c00190500c14480b4158410348003e198034000540507002340c0b00f0795401a2140f07010031155640d42c180d0603081e40c0090001402a00c91607401580c580c5500e46506004003801074215907600141600380d55904d58409500d1075583c5210124640a280c0125030450300210f034210400581c00f850100780c0340750902800c50f90b42c64141e0300094070581e04124452601030f0f51062400d0034401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 883139775 1250 883138525 883138547
    0x80a1b0c030e151e070506040602070507050414060d030311130302043c09020907020d090f0f2601020403030c15050c090f040902060c010c110d052a0d0503040308091507 74
    0x4e00c00c2c5080d030192101c900d0042c06075025900c1c240d00080c5202040002c01802004040c1a00c0c18400303244030350401141680c00602e900d0240450b00c8000080510a5104d158803d01c01c110705600d81003100d03e2542900c0e030f5400100e0240e440d000e80002e000d0307940f9100d4140420f50000d075000340c3d441c400e1540d1320300000400103a51241c8840700c00005a60344081c040c0300d480c03a40c1c014208401c0c2104000d228540d1944800741c4421584c90600001d0a0365050100340e84951031044001009600c0d21070750b04411841081c1c1c40c0d48007141c08005c069111b100012914000c0c58101c0198082e11400021614281d80404c071494041056503010700304100f25807101c0e0401000024540000c0d00419140d9101c901c084070340303954690a004246400001c09200004010002d1030450082100681107110350007500c99552407411444480c0300740031350442c040d03458a0341650f040e031841981c044c10542068a086001c5401c00000038102c1e240041c0c04180d100e502da01d00c904989441005440c0c4207480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 883141025 1250 883139775 883139827
    0x1050a0203130f0816060f050a06030201050f2d28023318191e020a1208040501120c08010303051b1b04050603030703020706080a1b0c030e15 62
    0x18821212040917541c1c102510502074400810304d11855480d08080b00da005103541003552400d803050000d0303680319050b18501140414000e41e00c40d035200c81002e1045043c031110024100d180c3c00380b0808601d8402518101601c1c1810720809510a5002071034640079120030b0005900405403011021130140e410342d916455a01c070031105040042d5210405802110400000c1801160812910f0360070420303188010141c100340f0b054040595504031242c030420f02c010314884070803034040d030070356681341d23408401000114900000c0d103c41d8070700b10003640c01500c100c0740810203460041e1021082800f9218030750310342d5a6110b100b6801c584c4e0603246504420304d00d11000e21001035020124008100c2300120001010b00f90360385844900400040d544010040c90094205000c5000041d070000f07070742425100f040c2040320090380d924103400010540014200c2244104024a10f1080d0300003041440c4a13000c0d17030742c58040c0c03039081c01448651030222117014000d030820410022500a0320115040d0342c080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 883142275 1250 883141025 883141027
    0x1506040218040234030e12030f0c16060e031c120c02010f0606090807090c170a0e0c03011104290a17090c060301061d030601080c0301050a0203130f08 66
    0x81e0400b00e030490b004446440e0940140c030003030110f442011031400a039401c50252550562826503130040054090b01b42c40ea01940c60201461114002031099840c1408035510054031440c20b030000300d95401009004000300c0703c41030390104080e0b2050100c1d0742d402c50b003d8014007412000720300b45410940d80400c0a010088080003529002015008000d20b0a5040e4008954011090404421204941d22480c18070940202c104011000810381c80110b508115002849219501c0107031601c3c3c2a1500d41c04113101e0389002c1042c6242c46070300c000030b040621811514075505135000d250882d4403801d1b522454001c10700040124868030b00c412601c8640116103c010a040d2000707850743c0d5082141d01c40701040c802040c030700c0741c215a1802903a000b0944402040010a0140440e100b84810b001d00010021070050b64000c00e003181850516a88001d030807a8030b95a581d9020a443e07021482c0410f00c42e50a00e0302165100c2603d0003983d010b40b0443c6d0300542c6a601540e50410006001c40f401c4800e0b030f034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 883143525 1250 883142275 883142317
    0x207030209070c0c0b0a051209071a030703021e07050c032b18030309081b13050a021207020c030d020c030601120f0605010902210912090f0a091b0215060402 69
    0x145e40c8094030302c25015403245d648440840d0283d10014900800e000c00d80c1c1d1114508120102050146500c8120307012008d9590b40c80b8a0000c4010348074070610501040d0f1401029443d0540f020f0040a083d0b02401c19207100419410402d40c8980e4001031203440815810045c00d41114030784040e00149009043c07074031480c1a03c111100c800c43d8680c0c810f0740441d10340402000500024040111215440b4416165121484000818204038030b2900c64100e40d68000203003490906a0480b0a02e100c45001c60a0300d15003a41e0080d60b4a61203242c2d54007a008088911046030b0000400911103d0020080c0c002d5a082c40c0072400c190618840030380d5800700320200140410000c0c4500d45c06806220340169441d0070042c00444505140b00003003c8140d55081085840080400d60101d9000c0c0d000d00c07141e45038800c500103000d40340d0031200a076005034090702c0080c44c42034545c040c1150500c01c003844049544594001d9840d08480c8000740042803518000a409140640c000d00c00f44400307940301c04802e6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 883144775 1250 883143525 883143539
    0x230901020c160918150b0a050d1428200a0e0402210d0c02030c1302070215040302090f0a200706270303093305070207030209070c0c 58
    0x720911004004800100c41c081c0074010b03070f074004d540d100781100442403840d070300655418014452000c841d60040e662100ba20341956030380c81e40140140002400d91030145045d003080c0300540e11542d4041c1e0588a80d407030014001f0714078100307074400f0408201900010421515601b460322061688d6800f2030044038486603003540c0340340095000d400360b070300002205c1c941071040c0200e0408003011034800d421012500760040c43c00055415104c4080c1c82c081d0041c01e01031000c81c8c507054003428000e90144080c1440c10700410345a0181402d40c0c021600000c0d4020f04100440241c4543e00001c3d4005803000d000515003a00950126001030035a0701c00100030100002d010b40e2043e8009040c0102c401c00500801400000d009441040d25003521101842c03000f8040d001c581e05d040c4d20002c05040c1c41b4002070f4184001464900b075540810f41e01a103083d100301c2011f01e940d000c0300b8001c405491506010036801c038400030300bc4042c4c1c0e50290030099503445581058070540d040e13101c100d0740800c0d5500c0100d050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 883146025 1250 883144775 883144783
    0x3060b0a0e0103211422170d020615030d1d040911130c0816050706050106230903060402040b040e0d080720070303050319020a02070315230901020c 65
    0x1d40c040c9074401c40704070414400044e18902d081c0d8034001c1111030000320318044810700c200c45481800c2e0345003d12040398008110900320341030f400006240e072140c0600350602001700da4014191a84e9003a640d40740d40f0141d000003006a9007154581503444503140914440c003032119901e8500c0021030101010302c203000010196041d00504036585017803212140d01c0f03401c2ca580030040c4c22040481c01e22050580302c200403c1c418009082514000d410b1496001d124002c2044602da0b0740c002c1c1040c001581c41d4503000d050000540e00c008031518404908841101c10f81e4140d9075108001405840380361038503000c000181c00f460035959405a0b5501445c1d50416003040070901294607500d03140c0940c034158034060720320401460543c110203d003001070003102070045840002d50760305040c41505ca85a0400a20b2040000e40e12100a5880003502380840707900000c86400700c0c0d1041011004907012428403800b0f4400c4820605122941581182800c00c11a5921039010030884001030070306031340580840c94 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 883147275 1250 883146025 883146029
    0x30d052707030308060d0506040206180402040e0f01060f1e170907170c06070209040501060f0f03051c02030a140c031305040f05160e010c080c03030f070801050102030403060b0a0e01 80
    0xa41c4101c03420401c1580002420340c0c020811078116130081d109885e50303070f11400000d200038072410740060035403240040c20101000b0207901410444d204d5480300c000c89840078040d180c80040007000000095024441d003040d24030640642d0f6807411201a454541c03160032001851102807254560554004481b10041240700780c076020000c0c1082490202504000d8040f08248406034002c0000e46400b519101d0460352240c0e8159032000255440c0d0400c0c6004010f00c1d00f10720f440d00300f0140001000702c070aa10640650740a4002d40b100c1400401c0e402940341d1107000e8046c00b581003400120603990007401c40112542d60141c03a140340c0303081c1c40b11041c216400b035104408107010011041c1301900b802d1041e01010440081d08115608100d0142204070000c1007180b0204420511809480e9202d0703084401e03120707480704200ea210540c3c1e080c40c6407290030440b402c0d1049440c8000040c1444c0c4a46a800c3c121041a00030b18601400c540b50200940304d211800c50b04044810f4001840340d0840c404640 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 883148525 1250 883147275 883147351
    0xa090504110411041d130210093f050f06071101060b03010305071715151903020f0607141207051204030206030a022d0a110a05030d05 59
    0x4441035104108800c4072028002e6805041007131005004440303c04480e0f409191582502803103075030b25603c01144c8032840e810300035042a81c1c1c1603140301043e044080201694411503d015281c0c8075000d4081c01895241c0d8124201070039454044010004642c2800c2c81c2401070003a20320f0550f89540315842d105003a42c000d400a0100c00005156440a10070b54000c0c025504140746194511344600303a0f40c1004d40a03a00341d0103110100d99205070350030070510794941c2000302c0150241c606100b5850b505290b8500c0b86004c0e600780c00c102070707103161125488000c2e29030050440746050860024006680c00c0340c10101e901f941d8031032094110101c1000300a0446851a10b1a6610300b000e20380319081450b0320241c000340480034402440180d0310203056035030146020500503164200070340703034480100c501800f1080141c00c11008000241001004200e0300000703880e60b035202600040c440c3c1d41c420b00090060b0550f0024440c00e21014025001340340c0045061994003007103003240415049080c2c0e026001a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 883149775 1250 883148525 883148543
    0x607060e1c02070503030c0627120322030906110a02150309071d0a09061e0b0a06050a020a150b0a080f19030e040b1512062115060a090504 61
    0x1c01a5030410005000d04020703405903040038140c8450760380c0d41c500903089042010340c0c001c040308185416410b0b104000c060030201e0b00490758a00c1d108a65030720030385000580039070849284c140c90075481c000e0740e0301541c1581d80c2440c192910310100c1304440380440602c1c144c001c076601c040c0580d840c1203540c01881c0d000300e081d40c0d480c01c2070b5119910308003141d840f40d840303a01a8441c48504940d0b031400f43e0f6200c02500d50109055506150120061580349550303a149940000800c412114550100b0083c00b01910303598100c0d52240380c00e4580e40200c03126140103922010324000007e42440d903080403a1003046000c102c129880c0001255403201e90084046035100b0700c4842041001040101d12a11004080660004190320014020f0120401050007180c032080751480302d49524009084441440380c015450f009030080c000055041611820300c1030117810074010007100d801c0007642c1400c240d100101000c40802420404568004080301c0d8003d501200004101800d4010780741300d181314100b64 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 883151025 1250 883149775 883149823
    0x18130f02370f02030403240f022a07030f140714130c1107090b19050108010314122808010b0301090e01061505030115080c04050607060e 60
    0xd812003000d09001084800e00c10401c4110003100d0540500360303505407800300e02d901107211003680f0b148110f900041a40c2440800000300d424414403440c03107582d8940d0f051007042c449080b01c100b40d01031104065403954461701c66503500c41075140320101c0c408a0a00b03071094a80c1d2515403854080b0b50101c03d440c00c242e01e40449000313150034406440076055020050302002c26940104038042a4030300c015100e2555140c40d585070720302841270b42c5884071010b81100c0d48a9180c0510740090072825000714003030301090248018203556000180103464040c0d441c15030300e0707203952130f1840c1c8c001408036184454010745013a40c65010b0307500d00a2907420100008500c100500061000d080c80b049442a010001c2c0e40b0b005200e500340030ba003201e045410018020a4441100d203a060041055921115180e440858103020702030708a409141202d2006001695060a220080d0340740310007101d00c0c00c1b0100d000c00c82801a4130303100024040580c0903000c00a0490349000000340790000f8001c020728521181951 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 883152275 1250 883151025 883151047
    0x303040b1008060114041d0a03050a09060311180105070b0103030305061002010e2a0306010f1a04150c110612060306130506160212070305030702160b18130f02 70
    0x74080100950700041c40c0b950f24025165600000d1240020320494440c040d08211780d49030300000d15048242c0b0155000042c0394607000c4d0041d0b01550700c0e00042404c907000020980d009110b20062128490246460040341003032020012422090280c1400820710007140480c0c050784015000e180b007924001481d05010080000030120003240c1811a0305000c010341958401040c0c0c1d014030302460340074400040302d42c1038211400340444440d9401d8800d803400003035035464103c2c181c070442c1c2da030500440070074400c05180c80d060b02c80c80c0158802c800303104000200c158070410400c80780c5030141142c0c0c02003090207000520329900c0f5001d404070221840c030030701c146450144031054100014980b2150500140da4601380c8440000745110002c2c4040303120101c40074024440303071340341d10310300d81a2a0340c65070303107240180a98006840b240010711452058031480d444200341141aa6810001a0304241803820300548000c030350720f070260b004600c0d041c0850500d40940217884d5070f079106280c05a104c10030480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 883153525 1250 883152275 883152301
    0x305061807121211190602280507080703090f030f031e120207140f10060e010518062b02091f0612090b0f0708160f18080303040b 57
    0x1140e030460414280c800180008051421115003410145483c1025000e12420698107172180074040b4180700e090401c00801c1d5000b04031070340700ca2440b0041d403840042c160445800e140341c09401f00c2c804011000104004001400000b0311a1804280381500e82041000d21000744d4011101080600c0aa0702015004001c08200c12075011217011840e1030306134000d188684986004120550001d4280180150018104105d075a01c00440320b0f0f054084901a03695400804c041d002c080c50b21a000c2071080051450504845004200b80e90091b844910184029000b030440c0f40c0c44000b1411419600b0150500b0760b030111040303e0301d00c41c1d080490044c00b918513001444040b13640082801142210900c3d1010020b4850301e15281c01030b8a24010100001e000d001809420b00182d1001c0144505160811a1180c0180d80c0d030342d4a903032250341081c042104410002004519510340c81044c441c07056842602c580d082412035414941d90f11a400e0859006031025500302103000c0c00c0002901c0a46 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 883154775 1250 883153525 883153529
    0xe090a050609070c0f020303071412040b0d0203060d021002010204081203091203041509050706090b070f020f060409051501020d02070f1512020c06150123130305061807 74
    0x45028003107803a08200248480e00010414014010311403c1682801040c01504440f1a805002c40781c0c1c031041410316541000700100c0300700551003141d000d035803810801410303070381180d02e09000036042651080050029400040106420000c013055403000760762480303140d40354a00550001695241850011410a0245002c406d4031760001c005000508000041c00c40403024200981c1d610380d100c41c60b1209040a00d031550311346040c10005a801030040114100b0120b505684540d07030142c1e503481a00308203005081c0d002e08142d007022001805070034880241c1106035002440180340036125030b45401201c1007903500d03007110540d84413602d16558040081d603025a0450008002240c54081c140d41282500e0260054503401c2282201c60140200c21000621010070820f6444941c2110815a81d5404543c0494a541144120001540114002020311041d07400000e1840640f41d10f1445e5075208c6048030b004000b40e280c0000126006100c85400780c86c03109a00c42c0b00e04406031801d482c1c180e4035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 883156025 1250 883154775 883154791
    0x11e0506010e03150702010e0f01151a090907200715021603030e01020304150c0b0601030b0f0111030d1d0f010c05040e0702100e03070c0f0317030a0f0603030e09 71
    0x7407048000681c0d0004488800801c00d00b110071540c0d417129022070251804001e141e40f1480b6880300034221410640040100036401c09a0b0001c542e0b9442c0000165500290700700240701e41000324034005d007821342596501c030703892f800c012000d0810b41c1c0305a01da1f89012428200250011391040c0410036003641491035642c914401084c6c07071018001c103070000850707610006003803150502044000b85d000388252001089081618003000102120103440e806140500301c41c96804440003542560182c4100c07000b0440140030450400400d1005584a00c0540c82070400c0b4441801145550082405843c24a6207400c81d80008445411800c40c03510035800f0380e051003039052a039900d04030350348007007903504981044020100c0f684a0074400d03070400b004049000c8400742001d45041c4015400002020424805d03140300b0241036589a80d9001e1084c1800000c04943c0c143c4801d03200300d000e0f48091500075103490302c0000c507804a90b000008440031503108a010614036082400c0d40d1816801603640407402c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 883157275 1250 883156025 883156037
    0x30403051303020a1205010b150919150519030504050d120b0607080c19200d0506040c080c010e0a0515040905090d11011a090a200403110607050703020103110903011e050601 76
    0x109d1041400746000380300309580181d407050501d049001c00b03100100300404c14100445003856580000501d554002c010203041d81c84002c41c0d14082c1486481030510480d0488003402003e60300142c111190b03101e030b041c44039000c2e4948105080f02da481030300501d0054070a012141d501e0101e04034141c106020030300040c0c1030391301c1030b0960000305240c0007000c00502c0710365074441c9180342000c0024209100304c41003c2c0c0325100d4002040704001e100d04100050322400c030116038507500d5800046034a05100c0c140a9000180c00404101e00d003170414000f01c20b14041301031039040076160550901110310131284150b0340d82c080400040090340220100c48005c0c012402480880c1145100d07a065000f00c581030f40c0130f0940380000518058065005540d40160100301030034a0303045d101007540c0d50f08180015149245159000c092074035007401151400c03940200a015600d28580040d801084401c0c10018000d00030010b00b801c556082c0300d40c8240c51109494000d1a035003031085481252402840c203410300030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 883158525 1250 883157275 883157299
    0xc150f01140616060506040e0712060513020d050c0a0e090d0c031b0b060f030a05060a02180604031a06030316020402030c0408060115021b06030403051303020a1205010b 74
    0x6901528141598030003000d03507601900e5031020880a01c590460b88500c41100e0b2549003c101440e00103500407441200d0070700113502d018480c0d030f45030403e0b4030507030110410001e5140000740081e048640d00c20007103082003045024a1300400e411101c0590116069004078096415034075041c02c0d1a0050245c07005804100e1402c440c40c15921034a00c03600c0001e0102d8a0003c20400d440354144d8402e5480c550720b510001d00241c50851503681b8107590340c611400e8004541445410700081d1782e81c000d5080340051086445072400074001754088403c5c000307151250314000c042a1140002000114800c0706a1000c244401c03243c2080d6100c0903080074800c1c0c0040000e0a40d000541c030444000980441e00142d1380e44500d9166030380c1c0d12030b81c0d100754081d00841c000040c08140301014411440f900ea002d485c2541c001c480203e2103117a180319256400a170910104002c244580301070060300040c441040301040e1603400040c52052030760700074440c0850981342d203401c104080c05031091540302511a030841030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 883159775 1250 883158525 883158541
    0x308070203040605160c0f08010f060b07050601170a080f030108060a06230109230310021e0a1115010503011103090a03140d050703090209130210030c02030d060b0c15 73
    0x202c02d5509105c8100a20045081070054a00c03140f001081c2110083d42d000f030707950342020b01a0069448507c1460f103011000250b50605030300315100d0b280e108006c0c0c40140e0904c0d1661500080001070404203104110345103000458140003000b001222088140d141c0d0715202c8030031310700200184030a40090800c081000210003003055102c050110a5480343d4040c8030200481c0c0e1503400c0d50201c0b140c0544403607092014140c5900b03c80c204603041e0148c680b0003484071f08070800e070300c5181c840c2d05180e142c1c03045080c02142520b0162448548030715100361500484901245884e445090010141800303400420030ba01e0248100c900c2003281b8040e890561410300c00b225202e4541c41c10107018011402c4040e042e50b82103c1c100c4080401c05001005203003050403008000341288001240540388800224000684000283e505607a00a25490341c1c01d42903601280640111307012107041d4072043c4015841c149580c050300740640184a03c4a46511428041e1480e0011030f209a0f0501c19a0000b840841 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 883161025 1250 883159775 883159777
    0x22505060f0a1832150601030f0510051309030e0d0507051c1a01030f1b0f0303081009060609170304090603080705010b0109140d110d050304030308070203040605 71
    0x7000c40001101c03075907124258000035081051054034416400f5440c84104041055420207a00826045070168446903076110b110300607035200c3c680703d58044060f01c200401c100c129950b0000040c5004605201c06100754810340b501607510801c9400102c0d024441810024420202c0000c0c0b403c1c02d015038a00c50b240604000816a44107008800c0318045c9801d000d01040760100400001d03000e0501440c0d00e002102c088d254040c412900d0408c584001115a5a1518000d0603a03400c0400840c1d100003590b07480302d4844102214650300c140d2001c0008050728403041e08801180242c84004061400802c0c1c1f280a6100d1381014248920740501408030300c1e03001901500351550b0911100c03686603110700003880c500540d4030401055061940200c02c114600300582405440b440c024000e041c1094015038400440b07008400c400c1202088412240c5000d54007051114050b01643c601402218042009204208800d4405610004042007056403054207641d0007070192014500306800d110f802491 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 883162275 1250 883161025 883161031
    0x2041a0a11061512120c030a080709210311030406050a030506091521010c2d080a2d050403020d020c09070305041b06021e0102040e0105060c071802250506 68
    0x501454609054054400c00c031080174541d524000c02d0311090105401070ba43d0f17100481a10000d9059004901c0d1240100c4400c42543c1001811b00024011a04100c00503400a03500b5000c002c0303400c4800300085030170b10052014045030365400f943c500021101038266140941201d0068400b04c0810120281c0358540c1203070182d01303c5012224038548082c145854130003c51003005546890614041203400c000414680054005c04003001d40c0c600d0b0144011012000d02c01011800b81d2001808109207a07100041181d0516410403c601030b90040040890511b10800400b0b903503102440103154042064821002c441d00c000d080c20303072408011840d6044050500b0042c951140045020044c1c90600054101d0020202d000c200d5560300c00250b07110220420b0100940c44041400f04001c41070085805965074034050042c03c0c0d10341410f10501e644006041086c60140d424045003a41620b00c541107140d40258002d41c4503102d290101c81da854244001c9001c130380750b040140f400104040740c0558 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 883163525 1250 883162275 883162279
    0x30c010503040f06051305071d090a230a06110d05010b0315190503010e1e03280302040807060c1a0105010c110f0a030615080c03100504020402041a0a110615 69
    0x4154560751b110188030140701308000c0076400f81c0c40d4040340d000383c0b4035071151010000d0411015942c40b813040e5a600c80d10004005000a6450306095061416400c182001d141000086030025065925103000322880c400040d00e00131000906800001c11a005060152407451f10b414614145000c180e07072a0b461000e0141d000384500406034a0b410000d0a07080c000340750113002802079010511841e17031903400e41034410307244600d50348660004c02c3d4000150360340d860004101d50302c44504810300c0741113200194214020190200804203040030309002d000c0050000303848050110301640790a0800400141c5401e43c01d160100c0100b0080e81d00409a0001d140c0141c0c407448140f42c413a01050b5484803607068590811a22017002042115135880058060b41103108102241d4030340030500d8440b004e409660b03900d07034083d00400c070390072115601c000c2d0007502c010070042c9810b65800c0c484c0b0072981d10214074401c2090200740c1441060f00080342c0340359030316010080c2605191507030020990401d64a903142c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 883164775 1250 883163525 883163531
    0x40f050f1b1e041a070b091b13020c0706120f0908040b070f0804062a080307080a0b0307060e01030b012a1a04050606011e09060f0302091905030c010503040f06 70
    0x341800d02d4001101c0141c02c9109200c00b00481d0301d000c10704603900c184400c403400c5d6035140000741c004402250840c0c101d441c200314200500301d035004001c030a0545464502c445070b401c00c040015298100683d4004201030740720448144080076001c4120350200c41048003440c1031205a1001a42c3c24080728241c880e40940142c40e03854504080d8104200d4200c020506c2c000050702081c130681000890701a003020702c0e0041a502c500035210042081d000c50014000c201c00d0010544040c002c200260b404001e10800023650454030000902d480e07036641c001008941c070a510144036581c540202c1004003400c2c202600c10b007029030540d80c106001400c0e44054111501842d03020000c01062942c8080b054140792150340c10315040c40340c0c4071013040e150f081c049000d80d0048600c80c900160080003121b4161119a0f07690b01d000c0303082c1c41d4402005500300030550300b003001c18181e40e2104090303100f07141d11049510304182048140340c94000000001ca052040038010440042c1c0b07504855000c90307910034004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 883166025 1250 883164775 883164817
    0xb07050304080c0d0e0a0b04030f02040207020102030c0706180b161e05070f0e090a15091106071406010504180204090828120b01020d080c09040f050f1b 67
    0x401e02c68050081149441d0150108031040b40354004901107030848210f456a030300d2a078990b0405100d2085210007420100076080f5400585443e0b8041c001060060040c2c1e032420317181d4110141030510075000034011852001b081c0000c07021140c0a0800342102c50101498401d10780281c4050341c8090000801030000b550040d448002016188040c2d903504c60100c82c02aa1a110399100c0d2942034040d507403480e81c00c180002c009100000394100107d421024088034907503a88000d8000e070038401e90a40e1443c0814030381c141c0d10b450310b000401c8200e0094400004a0691010039030401d03006a00c218800c90801140e07900d414001d55070b10b21155412200003075410518640481503000d50000d02078100c80c0036020104035510041c2c0c90482e001903594481081c03490000440883d400f2050542c0141d00c0f1500c080c0342b15004021070750300036442d00840f6040011400005054410844144032610303203940c00e2100c501c810705049a0001c5040030100200b100c602154080d600503203107060805505039a40c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 883167275 1250 883166025 883166033
    0x90f110a031e05091519150504110a050a0e0d0b0c070c05041104170c040c0207060e100801050405130501020c0a0c0e090d0810050303040906080d0822022b020117040b07050304 77
    0x206e000000001e4105212141e020b8140144810040c131400c1e0103182000102038030100d140040740c001d02902e407207990520445281c00c4507074500300100c06400000004900b4085407003034800503c02d0542c0400303165520343c1440d00800d01c5c500d550100740103038240300c8620039219141003980c00f0740c0ea8001c0c0f1a800d000046185900c3c21000c0c0c02600c0c0c01c42d24101c0340300714895000c00c0070800e44440d0b4545643e200019030601030312404646e1483d000500040050290b0b00d1300e6000181c0000d804110138400035810b0300c1e15422a88907143d41c400c07a0307200030004001c101c1c540c001074000740340c5006200003602c1c103610855202c1400d264031400b00210100010414852095180007920014045946842e210201c0c10002c10380f038001c07481c961082c2c0310740701100c52107070307042d207202d0100ea00340d407205000101d1104900d08150401240e00c49541983e000e21415802c0c070f2a0780600100d2442010901c0728000580044041c1c3c28442814142c10100004140208096a04084545040d0307569a955083c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 883168525 1250 883167275 883167301
    0x3031506090907020c15040b04210c06050301150912060e1203010306090c050607050c120c0409050c091e01210206030f070e19090f110a031e050915 65
    0x5195030740300c1c04002c00d02002c69400a8411048407051302c5078407030441d95420221584c01540714010707060500b04014010030700c1c090427400702003800200d4418540c015a07104075000d0301079082400050008401009040710151201854081909041c0300483c1081c040320000448030001030b06090315180590746003041001510008405940340e030703449585078030b0054080c0a001d5420fa42d1905e0140001c1101c1ca0b0800440c1c0c2c0d0581e109c8024466141300300c0a201390a58079050074103d6004004000c0c0150300c036400b40302401c0d8866400b07005031051400c00c0201d04400540700000415442d0446000c48492403d44c60640340441d0301c49114a0b50368000e03604020340880000d402440101c144455407600c3c4028170300a8265403118882d074034100701400000c20400c3c1210401d4100201c0070802e00010350301081e4022110900800c034070161080c0c0d01500d902c8220380000007550ba6900501c2e4651700401c2c6001414650410700c0780d42030000c0519038400009440d9112101240f001c11741100d5010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 883169775 1250 883168525 883168537
    0x2031302210601150e1e030d0c060608060c041a190e09060f010f03020f1308030421020603040209070e03010c030c0809070b0f0304080c1c030f090503031506 69
    0x50080d0350303060690368240c440c241807501050542c4112800481c248062040e01c038041425544e035042c06104c81004c0000c21103c60148115030b40c91408021810340f02807214200c030800d5038a0301340c40292545010340c1228242c3e4003140103074000c14103200004613407008480031210605d4a040c40820b18403a0a07880707104074807100c4403415a101989401035000074000358040da0484075148680d8814090181600c0e0b01d440c2c107400190b01c0c00104d1010307402a0301070051884146070359070409034078005610310f42282d0b800c015503c0d4000b0400700009032140004a050503821103200030315010545c0800d01a002c0030707200030b108840c00400142c01c14480e000b600681c200c0240240b010304003506c0c000d0001c0c0b8400086000090041d0005039412800061600440f1442081c0c1841d101c11780010703c40940005d071007102c1c0004108160308000d041006031107a88818903038021481401c5100c068100c69040d0010208142081c501102007480803050303030b9024a12202841206828000040441c03140f6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 883171025 1250 883169775 883169779
    0x62814150313121b030e041508032d0c1c030e03070b040f0c0b0d0b03030306030304031410110409060602010e06190b0603130b070c05060c0f250312020a020601030602031302 76
    0x528441380906034080c6401c1540141035504002c0c50502c443d00b5186034045000b40702150b441000b400c01b050118114620700f0302401010407003a030303076041405802176120700074100059101c4035181070301c401c000c1d42040c0318004500b0104040c20210202d9900c03402908030240111a5503400a400e0288500d82840d1840c3d00c83c088600d0319407100035040305900a4001e14550130b00e001c0b03100d002402e000003264000d0344010700460905286540303001003506c92411000107070090b0060260701c25814040ca85c00340e1b41201c2c48513107907400c040b401b008031a400c1c1e02038011a81880c0503016001d01c08035032660800002c11a050341c600e9080b14100c0642000c4400680010000081141e0304081400180c83c00e07109030040c4a00d500c8a02c8219268404241c010700607400001c0450102032181008188128018100d50f00746400161030000001d01c07090b1000020058022503010958040702600525816220444c189160074000960724401400024038041d030000204101d429044103188500d940 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 883172275 1250 883171025 883171067
    0xf0c04090f09170708070b040602091c050d052a031c1401060c15020d110a030902130204181e060b0406030e06010e06281415031312 58
    0x124500000030905110251146494103903d0000d10030580101d910070b50304204002e00f411240c4e1200600200c0242c070495016508000c10310154682071040d410211b0740440b4107566400350b050042c142481c0c100c02070301f00710301044208035900e07104200200d0100d0500c0030800440e0351411440c074501c0b440b120011220075144540c0e4420740d680e006401c001d801400b0004999a031000c082c0d480a81d4800000d01e110501140e4012140b00b43e405040d02400c041404a0400c01d060b000042540c4004003040009486e84035000c20750a1421104101410078102145400e25000b0020f0510f000300340c00c00b011a44a90000d144146014904000d04034207510401049036101c2d034685082c0d100d8419040441c0c2414505500c8030004120349040310113605230341382075903580401c0020a03d4100e961080840e41068143c0a07040411048400f90451b5143c410003026500c04100d6505d6100340401000f88007001045640f400452102c2c03500350b40003003220080b8003420015140d901d88160245089a8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 883173525 1250 883172275 883172291
    0x14010b130e070f051c050c1e18042a0803130e0109090240020417210901111f0e0c010e01050d0204050307030f0201090501020a0b0f0c0409 61
    0x40c0341e804403540c2502107080b82d40b1a50365045400c12010ba5100346540f1824040c580b03800c550966140003002803103901517138541c0c50400c00242000c0702d4403465400809001c448040b00e810a940a84842c842c010025580e5103001d41c0c0e000c01000c0f458403990140e24800000b80801e055244071038000e0411a0180d903119000c503641c2000800e81031240c19086640d00000146401641c810000c5050700982154500020207050071403c2d580002c000c041100441030040d40203c0b4801c00c082441030308980940c0d114a010303c500e00040000c2244c00f4940c10213000a409000032407a00300079140c4401020b03444402400058032000310038076880d0301d2070040e508054001c60310380c3d09001348180990b20070400340ca10050758540e240d0070798503000d010403070085604540d0340c0180041c0603110318007200985010f80b1000403904080460b803088880c42c0c91194404110344c0c000d10350754007600084c40203015102680c0c0fa031080710140502404c02204120000c035030300c007295500301c1d4040d00000e072090000007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 883174775 1250 883173525 883173559
    0x1090503190201020618031e0409021207140c0c040f09051e0d03020a020c01030b040f111305090402010f050d0f050c03040b36010b2d0d0b0414010b 65
    0x10790440224014011040001d6624074940c4a0002d4070000e00011411f118801900c04100e0101d91600e000f007100a2100203546806400109116a400219100303941044400a801c03078565120b40d4000142c140507442c5c105000241981e80c140040b1000700b44003507031280c404018408040043d080c0e004400d01a03040011010f445040302d0103da080304d03548080f01000301d00300d02518000c60010b070440c101641d2550b10a40242c02c000c04010300006401a035050f401e0121255014046041c05010910744010b0085002043c01400300f0b2310002c14601e050703070000f0410b4168001040502002162612920825600505100001c0c4000300700c24140400403450700e820031503086034034456040c0051035000c0d44032035518180402c1501f80400c1070354180440c500034807c10409040b5940c0c0c0108a03a107035540f0f00340c50001d05541c1c56030b213035200c841403504010300301c90700700f81e8040e541b200b00c40300002d69041d85640e48190840e03002e000540310034401c3c1e405011742c66203141d8402c8011004203000d07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 883176025 1250 883174775 883174813
    0x130b060c1506011b060e0f010614041a030a0b1e0106031b170105060a02120301060804141c141e030a0606080906011a0f220608150f01090503 62
    0x3056401d00e0740a03a41e035844011101011440460f04090b404131425100003185c9401c5105000c1d20f140a99400000c9841081c1c21a00103521070051810800d0101040e410075120750740d800c000040c03a46081c09680c80c08039550300710b10b441c010841d41c2000e0004196070400741c0f203000c01550100004280f56500d02000b13003d0260f540768680d170300d90b02076280204e45006605544401e0701d443d80c2e03101168a4807003000019003140f2440019401003481d03041c1914034401c01140a00102e4079200c03024281400d2012007000c5c002003810899005589a2406000014007140c442580780f50440f01401030a040c05814052701250800c0301003240c10f80c02c41d501c05403010f188140745120040051903902c000450701c841c01aaa03a46898002100500c480344120f41040210200032203000d103400c83c01102180e5551203880d480e030709540c2e80d000c1c4452030034400182e80000d010038078120480381417145500850300e45114450f03106000654404e52107034021582c0d2001410b000303007642c009600c1031048030740c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 883177275 1250 883176025 883176043
    0x10501030b09131202032206081b040e1b4b0c0106053d02250f120203010c020d170a0902060c0f06010b0f09130b060c 52
    0x10905100c0a01c0d46401e100003154420007210602c0040540356446141400c1e625502c28011400b0402280c0001000300726080643c403409801c600d0458030307009008025041c0036000e115031802850040f51144000d800359019502c501300c40d508940c42c1c1409550301c803000e82d91710014858011500301c0040a4443c031040c0c2640749034042850310b20380745083c0c5005c1c0f0095405c82e051307022500040d00078801d449000d4001c0024580002a60039210360000c0d00b4062032400d074414800146a0305104027100d070228107580200d141c0501c410b00c4a1003006500c58000210031016001e070130351044860000140d212000f8445d1000040349181c9038104103e03c01c40d400b074103a01030341c00d1070800c1d00741500c00500400c0c001566542c03400405580007000d10385100181880c901c00d92031b50130070380140c1c8d074190052004104500080183c48078005450303090041c141e100e044600703c24004030146003180c0701100d482034412581d412040c06c00c40380344001480307507140403500101c2c085150020f8240024611507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 883178525 1250 883177275 883177277
    0x1090b1908210a0c0f060f06150f02160308032802040f0b07030806240406050304120914040f062c150d020411070614010f0803030f010e07022103010501 67
    0x8180d002e8a4040b91580c45001c0d806800501c0786039410010440c00d00031110200c1c071900d40464a5646010303524161009034000206101080f003c1034152a0014038401400c3d8840c005440c01a4141059500d05c03101032102824205000001801112320f0303814440c041965000b80c03075030540c00400014001c0d042070041066041d082d03c000316802c1511400d5512031581550750041558076002400a010240d2481112040348409158454402c54010b0009003629545090716480c10b400c1440340d480e2000d0031501403000120051182c40502a0605001101902c0102d407088034158404000c15040d88101c0b6103040e084100359000d0200b0340034210340c0c11600380450306911400190b00f041110110301c2680300b0003160600005081503040103492110f8940303141e0801b601511804141d40002c00c41150300b142000c0140103c5900b11600c03400303031104400450841c901101280c9400f030040c014003e0360507041000411191080101801c01700203159403620342680c801400c2c02a800a0041038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 883179775 1250 883178525 883178563
    0xf0c0d061401111c05071b0602010c080105041505061308010e0c031c120902060d02030403030b030f030c15060a1205031213080d0b041107140d0509010801090b1908 72
    0x5891001d001940c41d411a030000c400c01d0503034034131000035141c5074010b00c0101c0341c40b20328411040300b41051900020061005400101d00a0b1440c0340007094800e058000500ca540b51154080c0781c0100a03048006442064520301d564207020b800d500c00301527441d844241c2660a00505400a80010907c112421802d90403108000c42d0004038150b520407024480c00000c0440c4102d00c00b100003a00700d125601d0000d00010b1a103003071a81100141c0c0c0c0101e070160301082d06d480c288009801c04102d48074445400785d01039810071042d01180e0780ca031b2000361592650405440045000781c1d0303418401c1c00041c20070000c454807070360b443d10b03000d916070b0046e41c800d030351450002d00003407880d2007005550700074664001056071038004010900e200504d041540b880d0010340c3c507081034107000324040080112a024450f120314501001325050701d44038180000d01d00300101841410301c81c0c3d070854042d0381540c41e0b1520100e00340c1c001501107903006482e81031055500c8841e001c00140c2d410041034040c10202111281 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 883181025 1250 883179775 883179797
    0xe19121716030c02060f0c1f062702040503011b080604150b0705012c060a090305040506030a09020405040609050d0801081209040204081e240f0c0d061401 68
    0xc960500030304051518480c40484450000391007840062669403005050b40d040150f00800384d02c09800c900303d01416640722428124141e03031648130340c0e22010400003050040b10300300b212034444000104007070003281d800701104190003843c030f40545018040280c001c210340d5410034800c04079100c043c4480382c089480c02d004030b00d083c103080c050749041c5401c405507012042c1c0b4141c44124980d00000301503403103540ea00701c40c10002010602d1500b83c910803030307901c0a0024648540b541002c41c080e00c2c010085240118460000e0b0300708040d10100d4000b150910388950300c80444001400d41d940d0000d41c003514010030441040103552040c0011070103181280c0c03107507003c0314098800160a0017500010390200350b00303401c1400c01800070100544098800b5060580d02c014880c64440344504c68184403400184003141c8920030003039030b142d1001c922081c00400c0810300c00c0b40305000e005445440c00d26115000030350010041c1c01121001040c0c5e60341000003607540e03804c0c3c4203141007802405000900f49844 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 883182275 1250 883181025 883181063
    0x110307092603090f0f040e0c03100513031b060203070513050f030c040c11030c011a0108040c0e1003020d120206010b091323090607030b0d0809010e1912 67
    0x480d1010440c0507009603d4250034000300081425819080380d4810415601d40c6119180c0d40961400c190841d0010454104441c01701820b04c01c25a029040484c50070003000189c161b1030b01300c8094a601030619100c0da00e04070f81402d0002141c040c014101500001c28480d87d50b9202c00145801c03020036445e80d640740e45070020001030f45000c45642c0e6140d84500c090300014a025030141c2815820303414803049140145118500759000034902400701d96503a626179100014441c1101c900403c2440c3c030089502d890313030700c0311144441400b9452a00e00d40ba8001611014030820090280d43c005022404d494a90700d0101500c034441c03d55a001030284000005001c1c00d81001e07500e40f100000e1090180a44182ca914010504045c4030583e84100d0460b44410142c0040c00b6406200b100780644038a20313041c5030180a03218003000035801043c1c00340e0090085502c00056604149091070110711845200c07001524514000c40507038203121050074002901005203610b02800d500c0380b5080c91050302d00b006 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 883183525 1250 883182275 883182329
    0x6030b060306030c2214061f050703140f0d0b1207140603091005040b01090c020703020a030305090307180f0b0414010e0c0f0301060f0216080705060c0111030709 71
    0x1812a01680308081049083c030b4680c245540003441403180c2c1d43c5c0754900000f601c0a5801605990f011070305c1000900c22942000703032800c0b000d08080c803c4000140d00104000305a0300c1000b00240400c2600205103851a01f800215400041c10980c0c0d1600c41d09160b03544c0340186000d102440c440d00104030200c1c4060b00101d403200480b254903464520b164041002e00805034001050000d281c080c072031b59840c0414a911400d4001d40c00382c1c0c3c20105079810085810100c4e207000d8440c005640c0700540400c016910411035800f920382c589403c07a200d1441502292808042e80c001101e0884c3c040708101e450642c941c0f00240d098481c990a1001a6005050000316081d030020a001c0c0301031b04005010340c18001405641050000051070300c1c00c1c1c00440801207a03082070700410000f0307600392200c0344010740c104085103003511242c1221391880e291103c50b5584400d184103942c0207a201084403450084298840d402104500400d55607a00e80610010f042d40c1e0b0601559010400780d90341d00b014035042c44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 883184775 1250 883183525 883183531
    0x1060803040b0a020c0a0905011509141c02180a0c0c2d0c0b04180c08011703040512010f06080a0c091116030309030815030c1002160b0406030b0603 65
    0x20025518140c20041c55094a51000b000c0605500c504050b10304035855007038801c0028400b0b0607002a0300d5041080c0c0000d15007081c045981003001e03401050051076401c600d850302c032000031500c811044810007030702c884894041e50065441182d542d0080d203901000f2101038400c0303d000c181000140072a8005560f40c0e000710401400081000341c1007900183c0c0400c07010fa901881d0380031703551010f00c40e80d80d00f142c48007a900034207509200450100700800c4400080d500040d41c03500113001110001000400030701051081c100801100c1d04001241c41c01842202e014000152041c40710001048816003c0c0900200d00304016141c1200080c03825001f0654905c041d03807080d944a8001c1c6440789002c05003010b031504510140d4208010201006411600f0449510a88001c5043d848034140175210400c01005503101c1600941881c81d01c1d41c010a03614000359017212000310030760116104919050503440d201084e112044404034940d5000300141088a1056800740100342202051100501040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 883186025 1250 883184775 883184789
    0xd050a11070f111215090708030a0207090c050301360e0312070c0c0e100909030f0e01051c090f06090b10090207210e1509090c1206090a06050301090b0a0e0106 70
    0x13120f1002c840340800c420040d00309401b07108403410651a001d0550855021000220140e407005204200071151806481c94880a0741007950541d03140482d840360f801482c10815060401807520a0202c0400c1c48a500102c443c41008001c0c2c045003502e41a07891b07010b81161341050140d08000b81c12640b00b034490844507540700781c074001801d103843c0c4030701c5c14034030060302a060030307016580081410515031203078481c814042d5540002407900040098000b503034080f1898100300d02080740c600f0b280400408404400c0c075003240028882028240f201c000300381710300010005828403600380309102501000c180145651410255611f40d00c1803644100d1143c401e00800c0030b40c404c0d51b00000c0c2d01e2070b00207111140d034042c10900e00503a9414005000411400200c440c0303007001044004050429010841d40043c09405003440c0402a00840b0380010000703242c4d910403154100010800c010580000000f0710000d0300a0103054503924108030542411200342180b1464000a40d141c203c05019101c104c0e406 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 883187275 1250 883186025 883186033
    0x2090a081212041e060218030604030e0d050c041404020a09020304023a0c0611010e0616050c01090302060a05060d020121110f0c010c02120d050a11070f1112 69
    0x115110b022950b00020802e4409203040c40420540311032030348040d01c0300784c42940c0040e0340700d521103400003000d881314080038043e80c0071200f00070000390450b4420407507482c01c50303218402051a03d0087d14089401840d0781e0024100303290784100f038459102ea180924400c40702e80b244641c80c0e20b010320482c0070450b0080d600c4400303501d450450000603200504079581c0d21101c034034a4100004034036000d81c0c1c503210031181e50110780c00411500790f0007000102043c3d0000b001348400d0710030b1010559980000341003100607900d1003509200c3c1901400482e00d00e007240f42e00030301180d2420b0801a4440c0021100d103482141404002161860605200e544040d8140c44241045051409951001a0607800c03e0101956000da1a2412022030050320000000c44003580ea90512104d98a0a4481c00303190701d015980f01c00014007580700c2c44400c4d5071524540e0100054166180c014078400b074400d4a4007444890400105002030141079880d003070342d0501070001d03410302800080a010040303134010612420303500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 883188525 1250 883187275 883187287
    0x71404050a1433030a0902030118030311090603011403030c0709090b0c030919080912210f0316021002030702160f08070603180c060206040c06140a0302130308040902090a0812 77
    0x100400281d40c009403c01c1002406d034a06a002c242110251340c040810303091015000c40c2055450302402140d110380400403414466108042580303400180207840000c0d50b2800c1c0b018060714100155100c8015a008880c1001e5503510b600c40103194085c03043d02c940d01070320000b80700c0a684908581c02944544020038940d200c2c421a41429101c1d070b5011140c1c03090170442600290f44a01040d031141c65850082c004400a000040d6807245901410401049d014400000400640e100340c950102c07100589001141c000c500c103e0510000f00640c0070300e81d101000b80716149500140c3e044a441c111803000155540320009083d44840e541b144801641c000b010a000192081c1c0100e082002500f203024021666580d0780309029030990484c20041c3e0050041105203d0711860001c000c0074213051030040309280c80004580c034030911015406064002035040001401d80030303030303000868000ca5540d4a940c2c03960b50f818041d501c040c0c545403250103040f1012071500004542070118249070f03c034440c0ba00c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 883189775 1250 883188525 883188619
    0x40632010506130b22140a05091e04170409060e060f06030114120706081909020120101d0c091515070f290906071404050a14 55
    0xd804400101c2c9003580c144001e00101c402039a00303a014100941046c0350b6440100240940c0e0050b0f540102e00c91030010090021b00f2926142c1100e0900d0030420325025903071103080406400290080003903e2110000d0009080c00c4030303601036025113900c403060312041d0729542c0402c40d0603861244200d80c881d01c10001001200700c10012003106080c00303403005280c140912215820300c6050740c065000314010800301300e020200c0200c3d134241d6080f0711804101108085d00001c1c4690040c40040300000300030712080d4000c03402000f42e11019083c01d0030031321950404990404810205c050001101c0c412881c0d00b0b0346916043c04468450000745126000941c840000c000c40d00c0800c0301441c082d40e00401c01240802c040d031004411113070241903442c0700d1100301c0c00000054440e518502c00c0c0307401d55000b44030b420100490304039041a1945006101d0000d9001c140c01d01303208551000754480c40d00d40f000503102d25078003615544810708507140d00711601708249100890146c0502148080c42c01441b4403002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 883191025 1250 883189775 883189777
    0x7080601081e06130f090507170307020609011e03062105060c091903031713331401180606021207030c0f08090918030d05040632010506130b 62
    0x70f50042c0600e440440391503801044444d41d84994800c25110318284050000411441e80201030b801c580b440b4024400c13601c681c881c050314a00030f22a40c5d000034000d00582c4904507814200041e81c0e40381880d11090035018000f400640705455500d52028488411000110172540f43c03580c00002034003950341c1d6107501c0c000039400900070326440341d01c1c59006403101440c809a00c1c0594071036110341d8020306909617406d114140082042c9510f40184080701c000502162203088646154010b081e00c011900041420859264034581c6055145c02003070b15500c00b890590b64101c4540c0004020800d1000c0d0074a001c0c2da242c4d01445025a00400103021a0351070f2400a0030914041e1410380c00c940d203142d4a0106a048040c401c0d59148004140d5002900c0c12060054100100c1c13041a00102c0c012072989840b40590b18569801c10b642d00c00042c244061078001805aa24604450a84882c2035180d4101e420940340343c400200c448000109090900c1d00446503902c1400c3c41e41c2d84c0c0a840c00d1020242 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 883192275 1250 883191025 883191031
    0x1050601110c0a061b0f0c0e0a020f0a0c02040906020d0204031104050f040f080706020301181401141309140a05060f0405070e07050c0d030605031b130209010c0b0f07080601081e 78
    0x541000c1c40000000702c0d180c4060514850711445c1f2605038645012104009103101518a0180070f02c1089a59040c4604404460b03105205041c0750040d100e0500000300200a8440007600d43c40c0000b134820803114607a4018401d880c070460714601490b4902c018401140e43c112003040f80c41250381e010402040303c15203440751881c421800c8925284081e51528141d810a134840c0d080003c0801c0d108245107518016403440d071046480c00b0304690b03d0102c0540611211130401401500740381101c070f00545540d0066880c554111040b501c01c0e54101500c2542d400070040d0070b54141c05040702041144148150050103076400030010800b16090000340d40030040c0150005091010030840601e40391001d0111041d0100c880e01e00090182c645414181000500b1400e442c0c01040c07464050300341d0703481d080303c0c4002803001080140c403140e882c001a11003201d03510016010454810400002c2010202082c0c820401a0781c1c11596441d5040151801c1c81c090341c0c8000d402c078818030b0130740843c0f20040c4030382d038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 883193525 1250 883192275 883192307
    0x601050f070c0306060311010f08070e0d060203100509060a0e06060f0c0114061513030f030e130204050411120f04240504060501360f050901050601110c0a06 69
    0x21801c0302076541c200c2c070028142e00468400b07840d10410818403902508000b109030702801c00303c03500045c4581c020b00064004290030240407141010001c030380c99202030080c076039902100455580c1088108042e40304150704c0f815205840c60700c009510360800354004012a200c102005c01c280d01ca000401110360084c5050b80c511a0b42404201c1f2880707002d02803a050002030380d0595401e810440140301005e025001486201c1c0e004000b0400310614201c0031200f22500a0040c032084144d515044410710b0100b207510f60b00c41c490707880041d40002507500500031210b0884081004544040b1100c16600a810103a42d0341d02a05000408000d0f129500310340c054802c454240401c4200070750700041e01e007c20a5220702d00c1e41d42c1c0401c0200f242ca4484c1e1400350049290361b10b104070301813185580f0342d070441d004240056800b1007003402e4050b03582c2191041e80010700061005140c1007032160b00800c1e00b2505030740050300c0d000120450010205000e14210009010700ba1124103100c0d095a011704040340c548 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 883194775 1250 883193525 883193527
    0xd0918020906030a050402040b060a022503120504081b150705070504050705090406080c0918123408030c07170f030106020d090f27060803030601031406090601050f 72
    0x1d0207955455000f5803184892210008050400380148012141008202c0c1e0040108118a0240c1500080e8041087c0040c4007d14000000414403001000c81940024a068960710008a400c3d4008015200f030340c1441080f00c00e03c270500100070040c111100305d203270f8000d450200e0218181ca10203004182540c0210103e030700301542c0750049403c60340d0495107d0005032010480281501d800e0168a00801402d4014000e07171090174001182010080d0180c2c2c04428070782c0e4220300d001014841c0300105140b10450300d07141c50b541465420740d05082d1140d0340708105121441c1d47c01610040260240c2900035014174211351710a0708102e003a82c04540c00f0b44031400b02c002242c01a0020f040140720402c1c940382c21588951414002a141c42480c1700307140c0c240000001e0901010f204840300d0302c200c6000c1c0c070b0411806d41000b0904484282107000d44142d850602e900421510000401035025520a03603042205030005001d54480700415a22550300ca840800070035420f6104030040c100310400f00e0946 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 883196025 1250 883194775 883194787
    0x607030c0e2106070302090a05120601092703080106030c02060f18030f030c13061b0f0201030b0910080607020c060732062d060111030c070617090d091802 68
    0xa0f072038280d046814800081e0001000101070034441c900600410007036600000702c0b4050b980198964005020301c2c18400e0390380701404219204030032001803210381901c00d0224201203050084c107401c824001c100c086824802c85003202440010201d1240d4204140d8210944407a1002004a0200c41d18105140700c11301c031040d89160400c00444c0120384208600da981c9a01c4e180d00186003040da40325000780040302504030248a500d500c0010320315846905216100c06a08c0143d004181450383c040d0005504000c10290340788603000d44080d0380301c050407179000c2c0d6900442240d40d000950082600810184860000942e82c20182181e0381940749000c401c00b41e5600d0180208c1030380d4506005c1a6118209008480040f41e800150105a205180301078240301050700c0107503440540181c0c1080b1400443c0c060002041c02510031034210b0380203136142d150f80e4800040c0003000c00d50b02c020f0200c0c4041c2c0800c01c2c9003030000d44008000d804d0340320b460b90503280c100103442c803801407007040003265000c0141c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 883197275 1250 883196025 883196089
    0x804030f1707260d1e18080f1c050901090311010b01050f030c0c0109051e1506060c0a0b1e010b121810110d15050a14042c0607030c0e 59
    0x3c04800c84e034805ca944001d00c840d80100b605890440c1449400c45109018100104030b103a0200c841001040941035a55054108540300d20151900d45c51a10782c0742c501801914801034001d601114004d42c3d0300c410038031003044040d00700d4089410f298049903040003503000e10100b20340a1584031a602280038117101609001c0d90035201010800c80351900560900c14500020460542c0d840d10708a0040460020599034100b2451002d0304142c0710705404241c500b50380d40100303d0111026800708440e00e0310305000410064080158a07030b45c01c941400000031445800c0f41050380c4041c21400e420361116107407102444401140d0440010307450050708803080d5140c201d40180c40200f809940401d0f41c0700301c0340fa04003044880f4104411804001c0c110304112598805110200352403d055102020340f0b0003000040040241200d0042e110b82d8842c00ca142424520100030951012142a11183d50345e0b0b1030110f0840b0700d4116503a0100340340c103d10b0705290900f101c90303060b0351100300c60b04600c030050501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 883198525 1250 883197275 883197281
    0xf03161202041812080915040f1e110328030804140613030305010905040f0b1f0b0a02060105030a0f2012060714070b01050603130804030f1707260d 65
    0x5081d1443c0560a001402c40c940c815042580100000061f2248442a683c5a003040380d020b44003501d0340c401c2c00003400030300140b414a07054041c281c108414803080c00745060409803518103031541c424010f19100800010403504203180231098a103002020690654040d200004003500a4a1a11a40d44902481c0608110080c000cad134024001c00b40c04400382c83d0007800e50b20160000c0c0100b034104003d000000b0700c82c0788500807550b4030510050f100c0d51784203030701000d0048070441c0751075003080710400040d0b04200c140100494991582950116a00d4078141f540d0303001c40b4a002005c0860004155000c41d503041101710401800c0300300c14219180e80c0000940d42202c902400c80107070003d200f0b00c9030082d080002c030700110181200e00d0b4240009519403100708841441094010300002000640080c84285114422580b2402d0507480b43e44a040a2040490380f000c01c4400a01c24484003002040c03503000e075400c0691111494010f41420021204071890944403807421002c24003c01c4d0150890340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 883199775 1250 883198525 883198571
    0x70221070b07020a05040e030313030320040810090b0a0f110a1106100b1b0307020414010303080709140d03020c0603240613052b0f020f0316120204 65
    0x1028654480c8001c1c01046014144d5030b1010344641e1800d01241c103180720100136203a01403481c4010f440c449960342401c2d0050500c0307002c02000b00718509802a40c030b501e0400544265500c3d0012161a602012660b804881c03850301d0240c04601000b0000303800f42425004031680158080001c00c0d1a0001590030b80b55801c1101842e0200d5807640b0f070704040000030020280e0116281c0c0003091418580b1951100e584030f842c42e0200c41c0d03140303003000c0d10800c4410401c445191364058400c0001d4454016002e1500707a0a0004900280307140c0c001c02c038442c2c8907d00800603603d00c504442d100d0039140c810407003070070000d4208070254012500d0007403556486401440c85041080915102c840a84490503130300041c041501d48182c00601c805800203007150303162410f580c025114400c8503207003001d1451011034804109140e8140322451403042080c16400750010321b20998104058403840d900301900e82c03280c00592042000010300410510a1020034400118005080001c200602c1d00d1300c0b504540a103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 883201025 1250 883199775 883199789
    0xa02031e190c030f0c020a080d02240108030406030209030c090a05090106080f100c0903060509013603030b040603050f0a050c09040f080918072001090807022107 71
    0x700d000242462441c0303892146806616008480440e00c3c1d90140030b108155904c07504200022400c481103442c1e0031000c9000d00380e003c04031401d062090400039615001054404081c0a0720301c4200703600c202203811141a9217207100a1400d141c10705000f18003e4206031265589882080d640502e55224005500d005564071b020120345483c003409090b0946855501c2207030258000810503448102c08501401450a882808074024052200490b40103909400250000e46004144503c03044158415070b030701080414014003022091781b149940a03070348046101090001104040080c1c407a03404180308110041000a4890f225150149440f003261041951540920100000e10204014451403d07508540c12880d41c9030943c1e8842d02584091402003c0810100300c007051590781d5107881076840c1d00e00c40c08542903d01020010250301800c071200301001c401a031622030288041c0074068200d504103140c68a0104240d080c03151001e0518403444140501100b54049c05c403060004c0c000900c96 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 883202275 1250 883201025 883201027
    0x15150b030412020708150c0702030f0f010c08071419050c1e010b09250201021908070e3106080d08250c0609020f0a120317060a03080a02031e 62
    0x60b140701038508485904032000c035a2001d01308914507801d1200c16a03000840900307081c2c80701424400b0a15120303194803014007074014460403442a6405500411300541c040d034458031940c0350004180c81030803800c80e80310b01c241c0042101c9141d45000c54100f00e0003d007a4034189107802001d00c009c5042800514001903c0071481c115451500003d029100068004656404050400c01c05e01c1c0405020700224100221040d0034681806000f90306540c0f00c8c40c01d0024088041c400c900005001900480340340020400c6d4030240080c0342000a101e10120482e49807401d81c0b150284032141c001c5400e00e40d103c0300542c40b400046050107042c4140354203d0143c0d1901d507081d0500213002003141170000180e400c221304200d505180700d540300400c901140d4210600154400e005e0002c901d50740c1c480d000c01d1390041c03440c1c0000a0422500b003007130003040f8040c0e40ca1030b143c00710303040d040d90705c114003540c400d540548420020710200b905100100358600d441e00403280f07070856601c204c0c440f0659140700c2c1100100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 883203525 1250 883202275 883202303
    0x518060703060e0901022802010f1b080f060306150f10030605010212070b0c031509090c0f0306090a020f0613230405040209010b1b19030306050d15150b0304 69
    0x3c08101c101e8010419000030f5003041603092503002c0c086000d001c51441c881d9030b28852402c1600039440380b600e45d41844014401c0c03ca10302510b5283c0580c009201c4000358400000442400700445014020040100036041d952140c00307030b440701011b00c4000903034891013a113035007040f5a450042c0b1421400440e04c001c51070b94a050006400d0030b060070030903006003804103e05800500900c0007181d110b002280140e8480c0c031819410740554901009080d040501107082c04207a040005a000b010001201e07032a4810714040145901c404054502c892280d008040520061a144450216189014001604250351003200200400d041c0d80003514200c0c401c50181107035120501104c2178030100f524280b225003040d90108000c0e0b04d0520400c2c03100540490003070070842c040861102850134040c2125403e85100c81c2090b58103c1c01d210480110307284c0400040c1606000a9020340d880d000b030070300088203040c2d092042c045c0c09680340b001100c46011402140c11400780f0f02a5004501803080c2c942004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 883204775 1250 883203525 883203539
    0x30203061e042003030c1605060f160201111905060a0207120e0402130602010b0a051c0305090d1205190921020d0506010608150d03080a051806070306 66
    0x810080c01200108a00a9192030401005510070303400039070040e1050784400c00440b220f02c0d11900750552940c5400b002609008405000440002d21070441c6070f4a0002c542c0c40042144603c00c42891400d0603d040c40b0110b503004259100c20759450041c101101400e503103074921403c099918000041141000171804140f200410440341d1048864204501e0150951189505143c542e01c07044c1c2048000b130300d610102d0f02c858050705c112400d0505020f6400c0d854240c0a80a04011300340d070b5004841d0400e002603185002900d8a0f81c4645c802001800c940003614200c802c0e52084101b02d401440c0355080070009131f1a04d8029883c0ca15607510b80d610740302c5105000268031614071108080001d01c440901a9110851805403038403180d4051154030071080c03000c12001003510300003074550301031400000361040d000b00c50288035500001d104080104e002c41082000d01ca0840b019001844603c00240c0107030f0144c0c0710740d800c01d41e41002c403032000304903034a0070f4a409012984480040d8031510204226 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 883206025 1250 883204775 883204783
    0xc0d050105040b0f0405060a09050702031803190206160203072d080616090f060f0f050a0c0602090f03011a31020a11070305071422022a07030203 64
    0x2504044070140404070342c440018000d04c80c000d07851403045c2d41d10703c00b207032042e6144481d00004010a01080c803031341c81c004002075160b400062182d840d100010b0110071403403401184451500e000c16240360300300245070b0207211440c2c001c05490042e20282160708405690100491801080450140305034641c86043d040013521010420076400703011850280310000c4003180103540056072010019190000a500b100c0340c074407550151240b515070305804500f540d031107440c01c02100201c2c2c50340c51520840440c00c60b01071268480d8003000034103810301c040000f83c99030020b045502c1f0043c4400b176004860f030006400c45402e122000c882a0300389507512500e05204a01108050a249004040c10a40c1200d910340241d40d800a83d05160700007143c130703006c074013a1031041082036241e403c503030791140c0f6858581c0e43e400103401403071845503d69010301c82619000703004284282e4041c8491980c803207060f00c0b840c041c4d0480119442c842d91094140c014007414030341e035203681c504c0326401003243d10328500500d410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 883207275 1250 883206025 883206029
    0x12010302100806030c06030c07020604090b180403050909100b1c060503010b0105121003050f06010306110f0a111002070b010e01080c0d080315181e06030a08130e0c0d0501 75
    0x20321091404000f400d540220707580a5607030040d10303410b5070b0ba5500d480c42040d80c8a400c0c0000d43c01103000c90041401038290340118411401900c0a040e000703406d003010300b080b090850740200001c40c00c0042c0c540905000c80c3e10b94010f220264511085a10340020b042175401050796401584080d0000b2400350702c1078000c807801400158003c204a480b4800004c1c01071250014a894900d21140410910a652400500159000815201c00300204490551580c10038803065038031a040100700e40c1e02c46590400c56561084c0310203507a143c11400c0109a803111000e4240e10fa0a0107040185003d850840c0003c103900ca1061142c2d10342c560402c2c22505081e241030300041c082c1e9129001030020b54490040c510002c80d085980380d9265030356444131100203c01d0a48080c1c00c414207541d031802d002aa090168020201c08400e404160440450219a550110b034880e5060f40f06250035004160164000d004071008a02c003000003544402c100d480700c850503590051b05600c000f031014101c090510450b80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 883208525 1250 883207275 883207277
    0x403080a1413060507080c0106030b07021c0905010c031206060e190602070b0304051f09060c0f0801090906110c0a020909030a200a0b07020309191a0a020a06021201030210 75
    0x400c0414200c401c80d19400a03005602c02d200000a03072000384046c80083d50b1250501d0f800074050280c83c1d15100100c0281613941c0e102510404400d52100084015031243e11174642c1e40d1246010b18105c011200182859402d90a100b10300408030342112480c041c2501a00b596200c0c0200c81100c48180034101107500d152402815018100b070113000d03030104a109c00c8824450849841b9103031414818184080100740318507240c51003041d420902c099400030300c0268007035001000340400c5040140c51140320b042d42400011078220041c000800660f101d03090980c02804001003040500b0040100780c0e00000c850300703c2c2d0340f12881c48030841c60031955495000070200065400c0c003003904000352014900c580e030910320b400f080091070b4038803e04102011529403c140054002d0414210203516035000115140c0a070011600e00c0350284039040003441201c7d082d83c8101d2400c803240000c0002c68003c18580c8085000f13404003100852034900191050105141901c0240e51541c41003001a03032200e22500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 883209775 1250 883208525 883208527
    0x610051611010e011404050f280e01050f0a0306050c0408151602070b0f18060a11010f0225060b0307030b07020d140a0804080426011119140f0403080a14 67
    0x1003020011202546d04407081070f03680003070002e41031002030f0030700c0c0350800c01031201c00460004001004204d0100d070101c404101000b905647c84100303020301c4880d110f6540307030040e41032581000081e01581c0455405a9552401c03030601c0e44843e10b6900740040c2c0495426001d20040070300076019000c08000068a1260000308111498440c51040500410941d9040d00e82c0104400c41c6d0b15101e1005a041c0c1e103401000c2e641d80e07040391400035140c0d80c04c41c18450a15841d0911082c078050462085400060481d01c0d011048440340308800301c0b9005c40d00d0100c40b015226a608281510b040207004082e6210340c11510991914880013487e0110280903c1c003044039078481030700c405111008540c0c3d0302034245031102e5103503294100a882c41c4129400005900050b02003101c2400b40c4600c04c1000c1710a000082c0519514200b8402c0b040c05002a0800580b0340d00385103015050080703a2500e260b01140460360b00304482a0491589a0050ba0003030707030742000000e0701891040c1d001075240b03c0c03094010121 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 883211025 1250 883209775 883209797
    0xa210608280506161e080405010c05040f0e090114070807080708040308070f02070b0a020f0f0a0b16030f050f01060e0307060f1d061809070306030203060610051611010e01 75
    0x5540e403042d000d000842e800c52110080c042582c030940340902c0e417910011100003c1000d61400400c14082140c0664140d441c00c030035260401d1055040354110744c0b94520f203000306410401012a510406005041c007596104c8207501d80e80c440d14803a501c0b42c02035807280311151910002c050061040289035000b002401010040000d07003250149400401034034000301d031490210404da15001c616005400556004250703105029800103015a20300c1130002070701c0010604060540da224003200300240351b00034032000501c7c3c0c0b00030004550302c01e020602d000309030603240b0300c0d800c0100e035400d83d148018010070b00b006009003500100b8100724100250014015645444002803443c003010204000308040c10108001b940c00300031094152801c020155039803402c15408034069031900c2a85140649141000101c5d4940a40b082030b045940103405880340750f41e002c0401c10900807190750b20081c03000c02d2180c4113414451507514801c141c400c050749072400701c40c0000980800c5074400303242e040220401074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 883212275 1250 883211025 883211033
    0x11503020d090b1e103b270604020f1c030504030b06031b010e01020109020307150e01140909280605130b1311071406010f06030905030a21060828 64
    0x20b070740c00c0b580304114506840880c80c05506000c0d4242ca8a040414110b201d410b41e04101001c806c2e001c0c01032100003406c101441c2c0740a5403218020032a00660f900a000050003504210710209c065032001420f607100c6c1c0e0404000c4181c21501e03070b00c0a40001d4404075003801000001c0d9020b40d040758044000b4040c20b407480c4415a0400a4201c2e21410030402c2458014642d0017500010b60b03c2d81e000f42907a080a4a03140b10940024002da5400001421f020003c07807a94012000c9915a4640d008054039103000b200500101f008041c0c040e4403041840703007a84e04003034036078245140204054040072403070528001c20007204541c030005e1004c21031302c0c00e1b00306250355840410710546400341c2d080125980700c1079240b080d00c900800e003002d440003200390740a42c0c10b03903c007180341416209100c00c08181c00e61684421812a1304490300101640e00402403082c035540241c04500c28060700581410314840c100d100d10f02070341c1555003c00c0c119885000000d1030070120410b007100303c0002502d641034290650322 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 883213525 1250 883212275 883212301
    0xa0213060e0f0d02130b04020903010204030f021e09010b0a170702030a0305010503011104050d05010b04090318060806090703051801020a09050a1e1701020705061006081806011503020d090b1e 84
    0xc41c4680d59646c801640341c0c40c0c1c5a43d01920702d006002402107448681d03e090480c02c041e071460003207101350322403410201c13848900c40c803050303820002803d411916800d1810b90030341a40810a00d10a001d9040c0d1319440d50700079035100c11b02c03604099000d16242c0c10072050140c1076603410703080f00344241d05100861000c0400d102c00d0f83c08807a41140d1506140c030441c00c2c018014003041004c0e94109084c180301e101455000340d6000c40c0c8805030001da0604a5071600100c502540a817480c9510202800121b41d950307100360005500010314a0343c00f20702002d184400c40c00caa110f00301e21404500c2e4408104240c4c9081421540241003480c0030741e030415202c4034007820b4618540a050101e0100144c200c42c078445c00d5041c0c40c40c040c0c0c0001111501c0c00e1410080f06600380314400c910004648400003004800c940800d2200e0482c04002046141d0074a88192000488040c0c9001016824000004500c03c28000e00c90624020607280155080600c1810412500c50f4550b6941b40b82c00402e10210580002c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 883214775 1250 883213525 883213549
    0x3160311301605070e180a0b0408071a09010e0714150a140f0405041d2802060304060515150d090305070b0f0601020c040614090a0213060e0f0d02 64
    0x240d4981d55009000d01d0b9035400100c940001c1d00c80e11030020049480b110007220340b4020404c00030b01d505c0300844a408150381c0c014011000b070104503a080403400051605001d440614400c3c20aa440c40e109540800c019100803221520113079150040c5c4010081c0900400000d031148101c106000c00c020340214040104408003032142c0140040c036440fa0a01c20140022481742c0c800405070b03206d0300c0c1075815485420a000d4144100c1c036100c140305450814000880caa82900005001c0e01215844a11540c0304403d98581060740d40300c032204c0c016a0b5a500540c8602e109010004103810a81d81325102000740038086802a0401e0514490b8002a00160b90800c44c124030042024005407408940314019180000d200300748281c01d00c401c241e0b41d6800e0070300c1100c00380e003144e143c901818100026038101d40719004202da0f601c3c1c0d20200138140b400b4a50303880110b150001d40380c450002c12007800a12140e00c05400911075100359621868407107042c562000e41200d0032011402ca80e0005020b038502c1c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 883216025 1250 883214775 883214863
    0x181217070f170c1303060f05151e04020903030d050103060b0f030a06020d021e0306040b040612110f1804120206151207150906080a020c030304080c03160311 69
    0x4000250480c0f021204940c410480314503022100f03a80c0f0316145018140c9100ba100d0014201800140344070031034120700305c44010080011a100c0510909420504140c0c5d1803590442e40800c0030181c11b440400050080c841001d00000d0198074500f0400100d45544940c544610304510340c0c00e110b958001540b401980d0010001666010b010380c41c04001c0c403500c0d0818000c0400707031402454080700b11016620815060350103200c401940c4082208a03604e038054241102d408100100111b4941c0c12603807444100078140d40c41601c5043d0000d800030440b00804428040000c042008000407014003041810b8140020203290405246a1880010890083c4d0160a216800321481c2a0821032203000302180a00c0d0681211b404c10b006181d8030b840c0c083e0a0100d88001c010405811162080b80e003c42d0700c0201035802c43e00d903030740e54000e02d03445203560011a1100380038401d070760961480700c003c5e0a846902d80c18910445110450305200403040c07000e2400841d03024030070105c50410390b800c0b445002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 883217275 1250 883216025 883216067
    0x330d060b0301051f1b0b0106080a0501081c0e04020409150905070903061a04060609060908160e06150c0a150207170d0603150903020c03031903181217070f 68
    0xd13410119440c0f5070b051000020102c8800002003400012108503042e64850b5481441c6940c0d4150840180c90081c13286c40c55680c042007a01428100b82460304612442c20300d01f4640840407500090181d030020b4000725000c940d5009402c2007541e50340c0f1441c0040c03800c15014411403816850141c405045403001401c000d444010145108400d401d24824200b0014810012142c44100051000d0494059080446c28101000c24144400100c8141d41d4100294003a0407509041203100c25a5014001030380240c01c55043c403074540752a0014103210341c03008000307001881e4142003501d003801c00140f00200e0b5a10400810000c194824a40c841616519031001c0d44c03200e4045080006181c2580003802d02040e80c01c00c0800848540c00510455010343d0032a06012401000c05480c1e100d0300c015204400c00440c00c00003054041c1d00308008848a1100c0c840b00d4202d0340d1a8820b00884510039000051a114915000c001800e09200d403c81c0d024541003042d9000300c2c00c00750040b00b400c8030342025944 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 883218525 1250 883217275 883217329
    0x70921020607060e0a1e0b150402190507030e1c03030c200c03060c03010b0d0c0309170306040501080303071b06090210020f12090a05330d060b030105 66
    0x35403030200d4030b9240d8006401c1050000c1110340a88403144007400310346030500130413500500c030300d25001c0340745141d002a07902015403281c601035418150604055504150248146225400380c18000401030704071352034040d624031091038024105089044114030aa4054600700968400218044210fa030725003400030714004041c1c803c0d030f0101c1902c48000c00195190604201c3d0001c0864606400c00c01901103400d070b03072550808131486020902860701904008c1c0b03e80c00405400c2c1d0000c4502c8086810002010b002e01d40b9150300e411070004010160783e0001061150b5410700b481424010072440015509604000b4002028100300c00d40c5211040d81c5000940c06000b0691b020f1144d01d03a00810010308510600006501d8103c0c074204c0d4941401070002c0b401c5464486421904017440041046904505002c20000c0c001c01c10701c0d2255244a440e40d500b0b0440090000d017541c2c50743c0514140707888400500c005c03010b40701d280d004202e410009000410480d1940e41c1041c4000341301c1d803402c2c25280 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 883219775 1250 883218525 883218529
    0x1d0102010b09010f091d0c0d03260f070c02220e030c0109140d080c0c0a061d0709020f090f03190f060c0f0917030d0e011407092102 58
    0x4018208a40c2d0300c01110000042d4070802a0070307400071186440e40902600e0205452004100c005e8440440c8681101441c00340500c1e20441411146100c1d00300003030502c44e25210340e4814031b00200c1c1c901e900050001840700c2418072105482d80103c080ca0141d03071405059000c500b00d04140760103040c2d64504510b0280038543c90380c01c5140710007550b1080301c0c0c80b083e640306598003900000c3e13000c1e03c4d0f5110b03941c0700030703215074012450501ca400f6070b4403a001e10340c1360000c0c00542c42d40004050301715405003a03032100000b91030b4080d50542d40004505200f0a8604581740750922026911110500e4810081c0504101c112025220b035003a044440f900f15080110100b0b0505000a280d00c00303411140b00d00030100405000100141c5004650170440c54a40030f40a4a070007204280c0000441c2c1b8409040002c41d075003030208848074a0050599080c00612501f01041c1c801035000f100c01070751a007400500900304080d01c240c0c4800c0324500202e00c186045c03181d03820040d01210b41c845140210410400b59 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 883221025 1250 883219775 883219781
    0x1401140a0509150d060b1e0a0302090405090a050d0906080a0504030201060e0906152b020109050a08060a05150d12020c0603040f020343030b0103030507050705010f1d010201 76
    0x502e001030a40d00100d283c1090003851907200110010300d1502d80000420211a50720958070340000d04c0c004000d040c525401c2002e001d800c0190b050040640130096144c90b03031900c0c060240140d00000c020121a515860a9070805903004101010441c2101c0200700d401c0e030000714160172a203a4000000e90b500c441c141240507040a8202ca0700f0001907038107000c42410006407161080070000065601070540404028600340ca1502d40f00c1046411600c0104214440034616409403050400b00801a900c50102d100c2c0d0b03070340364880c0130a60801800c0160005a034052030b070707100420710f44001409244400061500e023007024091314800045a08440c064001c00101c0640d40d00240000e40340e15062030f0412081c0022503049020340a1000481d00c136106201011807a4160a0030810111840311001c90345d41c45282445002080c00800c0000819580b2040b14041c50182d030743e0542c0c0b40414142180781182961086040118403042e0540e040c3d80101d034201000002d07140385082180810040703001d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 883222275 1250 883221025 883221037
    0xf120b030a0c0303050a0f030b0a14040f0f06090f0b0d0b07270303020c0d030504090b0d02060a021c0801080a0609080915040603110304020a1403070e09161401140a05 73
    0x200e800340b0400320078160404060100200142d5582900250600c0100c00362602191550382000c0036000030301400c0d03130560358500c00d100040e20004418410000e600180c515188490492a0fa210410321070030005010700403600d0555501401001d206034085071198145e000058800101c074004030b08414440d01100802011101060b10342800f00001c15080c42c005102c1100548141884004207080c8208082141034050300d030142000d24010020018000303000701c1d01c0d4400003c105001c0182e86030b00150200300e4242c1d005004c40c02c224050701d020280c5180102041c40b48810040107034010004500c9021030b8882c0380822112010718040b00345000e803a04003a40110fa0b03403565038007003d03088003500864506035003d000701c92510f50440da26210a80740650010001c40d0107002802101b010489004400740c01c40d4001585c0c2c4541c459410f400b07a0b18131a994014041d0a811001c4030107440000d4590101d03808201d90017080042c0000c010404501840c00c804920f4a180c1c6000da001c5d590 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 883223525 1250 883222275 883222283
    0x1b060c02120315011106190b0a05060c010c17040b06040209010c021c02040f020a14180d0c1509060f032a030501080f0a0c0314100e0a030f0f120b030a 66
    0x24581c2800c800b000c031000c0c0004883d80c005400c00c8455030785d0140000c0ca072401981d028101d0045070005100207800b906101c0009908802030710780000b0507486a0b001001ca0780000c6000081c1c80c40e484d14018804905a200005800442414031000c1030040000b01e400c050204c0d40181e0321205180181c504007040130340a580441500c1200d0700003030318003104204083c402c0314108100a0b40741810003c03402841e10301000182504200000c224810008201ea41c8400032401111056000069201c0c8814032084440f05640c200410043d504e810140801080500b84442c1e003a003040f03401840d4440f804128000c05494004410082400031082c100c1c1001a001c9120780500c20540540680301c07e1007081610b1299042403030140102040b0180c2c40b50307101c42403107140c5207152035141240d0b0203a02c038000c840c012031002d0300b6007084502c41c00d10000d03000b0000c4c18a055440c10082c0032090000c0442c07081c0802100900786440d4803800003821540312800c0042c04420a401091070300101ca84014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 883224775 1250 883223525 883223527
    0x40e0c120c160c240f0e0d0c0b0f0a2d03091505072007050603160e0a0f140a03150e0102040315060e09030a120b030309100305010f061b060c0212 64
    0x100d00c000031464882c9400040440040b00800304e208102c0e10602400000344c00540c03500314840ca02d15000881c00600380c0100d50b030000490321003142d0f91241d8498245100310301d000181007012039412550703403400b044429018900c400c0b07021480381e04094192540000700350380c8124020270081140e002c060500d009100802540c135007040058250504400c1440d00c80008005040d107840000540e00c0503104081e00c1281544c4a01e46600c12100c8040d482074180040c41c6144038586d11410103034402000b41d01140d04410b0f140c0307440044040850030200340030f10700c0440c1c01e0011650f4281070618028002000241d40d000c0c02c0c04460090083c4d0300024180444482c0e00700c14501715070400e5081e200945000d082030380380ca00c1c3c816582d10555900f000801c00086946084010ba0f5009011040300079094034500420103002550200c00d00c880701002c00d9550b03006000c082130b60384c0f20f14050540d0b401d00071611000b40c894181c0d180000300d401080c080d161109821928402d011451107403844600003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 883226025 1250 883224775 883224779
    0x30c0e100902091f020601050a0504020c07030201051b01180201030e032d09130608060907060806062803050103140109081605030403150605130b0609150c070b040e0c120c160c 77
    0x1b03484840a00c286840313030889100c08280791505108482220184200070807a0031314581c01542c0750b41166804c0c403d014411040001c86d075000b03002d07002a6005454007581030070350910001d41200c15041200403d940280810001200103402c014520f802c051040c40c8030310342122100740240704101c05190031289984640c070700b0b08a560032400135107400500799010f540d90040101c1d6038031b1842c85003500140120011402c6c81c188a0000c212002d1030072000e0100d0406801c0000400500b034102c0d100080c2d44400400500031100300c0310140b0041d0300001d1000300e01c0ea45450b1b5080c020704060803e401b680c03080080c200481003084400a40d4400c64040e40340341c0d070200000040c6094411070b8018030500401440c241d0302c0e03229501140100a2881c0d040c0049071050080d00405940407502e041030030000c00d081c14000700f20803002001d5520103240c0e37490411120240c51407000d041c140c4154002e10041849603905902a5031108000314501c1d01d8403031901c05581c00505000014000034001440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 883227275 1250 883226025 883226027
    0xb180d0801080c0d0203030a0507150516030b03070f1e0e190f0b010c0b0702070503031c0b06070f1511040605070318320316030c0e100902091f 63
    0x4a8102c401c80415500c10300c00d40c1041c010813a030940e000a5241d001040240030160160700600786140c0201101c0c11200a0417882400320b038015951307001c084900c00034000c092a458024511007000503409801c20500e001da90340024080b41c02100e19410981118101da0714002075004001c0210300b4280358a401c0c56002030030764403042c1071500b00700d40c14041d560310710070454020000c1140040e50380c01c401c00381c581c41e0701280e8034029003200304500544100103080d0b60b0400180c410041034840c00d001041b4600b40010444050817002400350a06008100215040a051403141074104c40401712a6445c81c0e00d8900824616258070203002c0f0104021500c0c941c05005022918070a0f19065156408116a071802c004207114020011415028003c0d20080d8501102072500c0329620200801c100140000d0a0002c500000031030a11b031640d00700144642c0c210302c180141041c100e8055641450410841c80c0d02c2d09016800700c4540010310503501d07899068205840745010f140742e001e01c900c1004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 883228525 1250 883227275 883227287
    0x210c120e0f15090601080c01050313050a0b0c0903010f060518060a030c081c02010e070506160602071103190b0a0b01110610060f1b170c0f03071b120b180d 68
    0x3400301e140c4d215403400842e0b003490006102da03068405855460442c3d440040600b5103c41802d0300315503074090744001e1000149030346a090f0144600600d12521007908600b894211221001d01c2603406003449410000d0391541403520449154540400301d00380e0300d02d0003040600020b64002061b403080118001403611700820522461107094072180e200e01c003044c4d400c0b0300f81c0300b03d01c85041c0a070300300c40c0d001c1007145442001003815075619a0182c4441415845800032a001038078291440140080e02050918040c404440020380481c1c1c404a1145542c8803103107035650041000c0007103680d49a140801c2d80c000d400c010a60780880048981c9880c01d80d603108000212845800c01050501c030b100c00e00c960003403008840d61039081d40000210116500c8195400c43d16611005a140c000c002189141205120380340a80348030500a507540d490b507151003242c0491601c8901d44050750010248188034030300c401c0d10422a00948020343d03948030901d0740410326003440c4c0e14210303921404002482240d0098 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 883229775 1250 883228525 883228531
    0x90c1401090e01030812040c0504021309060b2d190519050a0210110d022209020f0405041e1b08010806150d14060403210c120e0f15 58
    0x20361a4045159107001400d0342c480b0038040208808024000c007800c0b02c10030021070350b001c1c2c01541c8502c40b940d544e50208049a01c01c1440b0450b00c604468244015031248c01650b00030120305200e980b44c2400325011548152947e10511103848040548000c3c000421040d01c114441c0c0c1c0a0700c50303031002c0d0369101401ca9031026490210010005c4006034010b40107005855665070039401500c187d103e440388981c0100310402c9903600d0424248126030241c030031880a06011644082c0d641107520b1600400c819020541c0d114025160041240840c02c4041006803400c5410985002c2480350900c981e0280507070700012106060313840c0c40034444d4480f488820300c1c003000940781c50700d00341c030713600d8a030181d4940d41c0072a44401c000307130030000405103410401282090b0f03038003e001003640441c00880b5981400f105840a6000800410390b00001c010142000056180e034803a04100a906201024010440e407020207042d2507030321390300114186014400c07007404102000640c0d030100044201e4107980f450035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 883231025 1250 883229775 883229777
    0x5040b040b180108070f0c0c08030a0201022101081011072001030f1103131a0708010906061110050a0b0a0308070317011d180d02010e1b0a050f04090c1401 68
    0x10030b42c0802035014601c090302941c2940e407802c01c00003241400b035904219400f800c880304031741d40600081d11002407001e400050950f0340050b90f05e80c405030307440c003010b410224000c80d9016003400410070704500151901c1c803000386540214502580340310011280c000c02e071703001e441c0c481601f04003110060070070803a13100480243c80402609500309403070310454182c0c03200c0c000688410030128054100700c0758400207040c0721315889100b000c804001c0392482c00d030aa8940000c00c08070310041c46540b4a502036078000e80202e2034248040440c0d8290b2554845401c6200d040340c540da8800b00b100c041007500201c000c82009442840d20380c0d0740f4502a2859031001c2000e030001034602d0540042c0007441c84640c2c0c1220743d04a00d1340e05690200c0d02504400502620400042e00c4030b8110491105040c4004540344a036a0000500c044007082e05505080520300c010700103801d062441c2d0910766a000303d40c400d030340040e80c941140c1c041c5100458010704140e40701600ba021405000a54901001c842d44050389007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 883232275 1250 883231025 883231057
    0xe1c0504060c210c120c0b0109020d0207080a02210a051219020f09130e1b061315230417010204050607050d090e0f0a050604141302090f060907050a05040b040b 70
    0x1441d80c08980240c0021b50060a2a03003070401040180d40d035402401c041540034800510f084500e99403d00c40b0b910041d4500d01580014055551056150a400b5200c601c0e00b160b03d41381c06044080108948038401003026003c411102060040a0340b03d2100b03d04d940101c021590303980780078840300c41c540040868520031485c0c6424880c01402d24040e2500740d140d60030003411070600405140c0945d0015203107090b003088051048175104900282404014a0003030031005204541d000002c120500030f041d8107540c0c1c03860204582501c0000003c070b50444900c1d00c5a011300510b040c0d403050181c4103590101e540503001291080c1030100111341b0200c1f424454a4800703a0a030b82d580ba40000c4502290310380e200d841e40e040040d9240e1036942000354494001440020b898050704c14054032840140c584c80d101c44814001c00d41141400b08400c1e030400501e03101c1d03098501c6c010000580c83c500062182c0100704000c00c0b00503d40b801401528058401169104e46413506d88401a44580100c890b915404807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 883233525 1250 883232275 883232303
    0xf061701061406071208070c0b0f010e0f1611030706020f030603070909050a0807141608010e0c0907260916090c080105060313080304060e1c0504060c210c 68
    0x1806204845640c4c0e413050117114903ea0f034410a54250100902c0700c000d11612107500c2c000580700759406403054600400742c2e215035040001414070208000c08414006199605110b10402c0c0501d810b00c030300d001481d252135449031038440f2078103500940800802d49400070903a80401040140a07510400060342140c50880d83c03003014200782c9000744400340c03840d005001040b0220b0b02c210002d009641c094440a444014000710322442e0400d4222904800030441d0b00901134030600b806400408ad8801d0020044045080002021804003800c00e0381404800c0418070301c1c05449403542540c980d604218030404c0e20701403019a44869400005001c1c00001141c007180440c070600c2402c800da4100d03a540c1d00c03941e09180500c107459001074109041c4440c08142003000407140710003107208500c52a4081040d8403036000317a80ca08950381c03102064451800c0f032001c80c850b6205003954104c40c142d00c1e10b841c20900c0360912025039000300e00900001ca401346034030f03040282c1014804945078490b00804a1800c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 883234775 1250 883233525 883233529
    0xa0203010302120d0519140a03290603010e06031213030b07090e1504150915080c1e0f100e01120e030403140312010f090506060304150f0617010614 65
    0x11998280e1800428800d1001080d06d5030407465481a800060074850700305c3d0503c101000c0e040c0c119904980c0080d4807000e83c2d28002d146050300d001c007135041101c626041411040000c10034003050240f079003000c806000140d004e40d001c01400c1c0744070390b11050310b0755200b500e8841c070203508540740019103501000c03c0103d440c00d40704012802c1112000ea0141d00d090700c03400c1c0e500025100154000768071945440032210810702802071403005042141d4005040003201011904003c102c2d031000c0d00307642000341c0c0e1305900c0e16151201d90746047e03000d820005228031980000c0b140300400e800c00e500442e00303007055401e07a6042078600102c003009803541e08800c0079145404061310740d1741600c1c641e1034009110400c0040c4e14003080d1015004000152411f188a221030b120420b14240e1080400041002c1700300118003d5114842c0c00100039503046185103040e0311180e45441c44000100d84295660403a803038410000d81c004006004c0d410418440d9546018100d806402e950040b004821081042d5039454 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 883236025 1250 883234775 883234783
    0x6060f1b061e0403201e120403031e1202030c03071b020330031609080c030a0f080714010f06050901031e0c0f030503040e060607170a0908060a020301030212 69
    0x101d00351030b4102c0d665241c0d13044415800d80320b9500701c8400c0b680041e0f548100c05020350460700e090260010100c08030128410300d0045c0130024890284410041800071941c8000784180100c02c1401009203010410000c440d0002d4021000003143e10200c01c1c4000303603140100460080c030a691340c1710f0590030900b40842031440c5da140b00a43c107501015007604941c0c1c9140000500c881121514020700142c401400c1c5c5c01d81c03007240c0e0034402199050381412456081a414005040c80000601500d03c035040420342d141cbd08404040d10074409448001c080103181c80440f0746041d8410102c889640440080328068001e1070b8081c0782150900102040c1420404683c3d0b0481e40c00c142e6220710040781d14040e00c11145c0188060b00c0300d0814103400b0912901c0708405074010743c4500003c66603546440e9901c5540d4078046c000074400c010411a56001c01c02009120a4103480380d500141d880700d29100964031051168045c88140c0218420801e510340c5607800796040342d0081d1401401d280c42d800c2800d8507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 883237275 1250 883236025 883236061
    0xd0c0605010608093c0d0801080d02070501030914150103060b1903020405060409050f0d020d08010e06041509062702070201050d0e150124030204050607080306060f1b06 74
    0x29884801e07042d8a0401d584500289076500e4519040e90103c00c8004110b80e41200c400c60b2030700c0d03100032500d00c0c646e41d0040d1814010f28100300940b410203180b00f0000e41f1070142d4820b540c101a00c0340030074002c0c414041101040d90781e5110446204580da000042c3e04000c09100a0714840d01c1d00224420f5402c000268003040800c00b02c1001e0075504541c2004002c210241c40e0a030080d50354030b03141c80091b104000031940324002600405028034008002494400360245100800821900400802c0c0f100701510f9080b51084070049010782c0d04440d203e500e18880e40c490346109082c960005a45520303c6607840c0800c1d40b074058400b000000760500b0003a03100b0350b00001d000503810030141061404650000c40c2c60b02c035800c140c230540400700f051480000000e07081400318280d0003c101d00001ca281071010702c8000541000d6041030710b444002040c07401821400340000d00004002015a80d800044512030090b4810450f120101030418040d84402110a403c05124460215030074000f55688808 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 883238525 1250 883237275 883237291
    0x201020901170c09090f01030b0903040e061c0b070c11090105101b0204050c0c0c0901031e0503121006080901050c16060902100806330306030703050d0c0605010608 72
    0x258060950202c0b24102e103006000e89124101070103100281d596100810b40141d211100b005495411414030a041c00b50103842e1081a900800040100c40c40301c40009a01c00300488101c208000c100301a00c205958442d0014481280e079000c1010003900202c426210710300030354054246210341c0f814044040070030b01a5070780c03101001200d10f00c45845520fa1400201c5112413849044480d6404a400c0d248182d9980c0ea5030718004c1ba1814010500700503c03030705100c084808480c9945513848170b40c882b204603404282c3c19061030912400703101c0100200c0c4c4220740f65425010503464604070415048486008800004001d01d0110b98510414010640910109510280350941a000412500441b41d00484429488801c60f101680c1c4186084d001e0b203900f074880b8090752401e00200840b91031142203403045c9541c58401e218001032105601f814402c007803540b0a540380c980e200081e10b40782555000500700d120b2441c01004082d40000782d40520391050340148503d9880c1e100070340d600d4004440c419 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 883239775 1250 883238525 883238537
    0x3051f14180307060207051e0607080c132303070b040803090d111306290f0304030201090b090d08060105041d0a1d06040c060e10110316150b010201020901 68
    0x14499004425030200030030303041e40c100c83c0b80104507034921050f40c2180348103072425045140e0310036040d1840d0000001044000c80a04554035000c1d601800d20b501c040c00700159224041029008440404840409400361140405a0480b035841504200c8080c8410501a000b0207100041c254100d009171001e0b1171200002c0c50a0500c003906106e281c01e043c110550b8a04000c11541405031120481d41c0e00d440034840000c6440d070f04064003800302c0602c00390550040801810901d00a40043d412345440e402c400a500b070b0f80352079908049001d001000005814425501c00740306801c00000340100c200c4019480340d1009a45080054416000d02d01c961f4260b0b42403000b503d08501c40c56040e15030700081c540300024400341400e80402c3c1e1190524191041135101300140024030200f510810000c000a2901040c074040e11030210340750000625519052258a020325400c5000034419524100c1c204c1c03162015100f800c0c100048107680c070400d903e15083ca8480c00300e1941d4410300880b020307003c06848007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 883241025 1250 883239775 883239781
    0x1103040b011502030f0f07170a05040b1b0616020f1b0d1a160801051519020715080601030e06010e01150e030703030201020c190210080c09040603051f14 67
    0xd040300b56101d003440300850108000e01030700b02690b000900340b0424011151611402d491601308001218550364485000c82031020a118960100456050340c01c603010303482e1244a2940c220b6480600900614030781e00520782044190200e2800312100c020706130303084840b00036007090301d944c44484030002c000340e075050303030244070160300704111200074051040e0f2004040000c0c188e4640740c1248280c800481d00492400f5410b40d160340300f01071a01600f821107608030451004d881882c01403081c107440749088404a40b51705d82d0140244042030040c10000140d0310f0180e040700b00100340030030884d42c15011910b880c08280d188240003c12505803400100c0074007099081c215000c0311409101d200404200366001203900c591824403001009520a400140e00c038880c2e11081c81c00d10300c0080117100800c2c4041801d00151355000b82d4030050010508103101c8a40301ca800b050b00c540311f0740340050740060038900300001b0424005142e00b691170820104010407440000301000380c40070300503582d50300c92103074001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 883242275 1250 883241025 883241039
    0x121f08060f0408220501020d05090303030402010f09090f0b09130209193218300705070e070c0203060103060b03030405030a060606020c061c09020f0a03151103040b01 73
    0x4080c1e009400b8124140c102a800103a001507071951403110700c2c0704000d244c020003072543c0401c4121841511401c003541003100444c0070a0b0384e4000280041d04110442010071403841c002c203100006803000050174000c0308107160079440078240381c0404c240200441000a6803e14030b071003400490300e80c0105032030115128a00c80707580884011000d007440a82d50024854409055000d10880d0500d0a140000107010f54000d9030300f0500c020072600402880b0f110741e83e075944000c189010b110007007090310f81440040c10105c4828400c0002c200a03000400103500007408000250f41c000c9030000389205100f640d42c1c1d282100d82c84034140e0001d40540c8154014000182260001d280040d000703000c03242000e5075500028a0664001c03000d45201d55104802e0202e0303507040c00751304a2420f00750b480390325041d540d03210001c0184801d0300c490300703440ea100340c003d08659854030030a118650080040841948a080810100c04c1c100000c11016260811808000300715a059a1040e41c0061001400f40e00c1c24207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 883243525 1250 883242275 883242301
    0x141f060b07020d0c0510020109021021050702012009030705010e130209031c4407020a0212030d050a05010b07031d03010c080f06030f0606040b01030e0102121f0806 72
    0x8002c0f44d0203506902d01291945698212a0203401c40390b001041071402e81c0140500300d41c180c0001c0080156558884000240010311a01451740b000030008541c1d40f214012401003400e400b0f801101d00606141281c80c58940001d40040d100440c1070300e1107143d5820040d1000c607400d001041e08a60354038009d941820381c99000c1c0c854040e0180940c0c00b10701e6855103c48156200c000040040f9400c41c07000041c0c482100160725843c00461400800410031a40d80c095140103008107d0800d4071341c13000a02c0480c401d0020040ea103501504030604103c64401c0903803213401645405808074601b01c00240300090500030181211a40b0705101d103001800d4808803820b8074040c40150451400305105109a102403061100c1d108641d501c070741035400c2210800c002c604000d03000078032a41c040360038140440000f144441c2c0140e412280083d03460f50002c010381c050030740c00326509115480803d88100941e403070400135100c3d501c100714a00c01000100c0044050143c03900414500e60b00c124000780c04061541 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 883244775 1250 883243525 883243549
    0x50d1e0c020a0806070908070605030f0402091f0b041806050f2b08090a060503070e040c0e0d05011a030a030c030c0204090807050f010f09110d0f141f060b0702 70
    0x90040e00c00580c07600f291910742070080d10b0020001e56445810000381c0414030950028150a2500510718200b054a4404010002d00040d2107102501c01140d050504400c0d180030070740e00300b40500380700c50b604d649030000c40c1c00511030b4103503040c41a5030b5814410140c0c400c0c030003038440042480c201d03c28540244008421501c030504d0304c0030200b01c00c1c011514244100b00c20600d120b454001d507039400c4801800091030040c0e00c0802400024401e1040c03440e0010190002803801759800246044800400c894140903c400c2581040d203000000040c40819045806c45040300500314a8030300841040c136640d003410301030150020382d10700c1d83c01c40000c0c46a29400303419400107102091003141600c50742c256602c111022113180e4004070210955000038040d00141d1801144200280d1540ea00c1e0b0032107028405080c144104d003d082400200051203480900303207030300416164041d00030b801c0c5a40d9a140c82d100c200c804c07242d90b024075038809021806280c058448826009042c43c4070344d1f0a01c10030400c3c00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 883246025 1250 883244775 883244779
    0x110706020a151e060602010b0109060e041104121b0b07030c06051009020c010c090b031b1612080f01050d1518080309031c0b0a060c11090c07050d1e0c02 67
    0x3c0560030410440d0ba1182c07124041c1e011000030b5200d00c0d2000103421504050555814082007000400600b0f81014503102c07001e10980f00030441c400c0f556030141d264410fa800c80c000b2545680800f034107001b49183c81041c030076420307050782c0c00c803640350304480507076014040c40100050141070f036402c00207650350081600111a0b449000d00c091726800024141d801400d40c2d071180c0d0390b50b190303641d10085c2d00002e110300500f2480130603469800c0404c800d0008140054003030782407202c00a01803107000842d1048201280d04905030400c525003401c0c1c0200444410380300c0042c042d000c03400103e15450907031040d41006034803403a104c0c404174201d00c000010308114a107602c01d0300303900d1035500d0100d4201001140303d075030300b00055590340c0a000e02000b5161500c01102c1c021520f817480010803a1162411181a00c1d81d50821403014109440d01c004020030b8100515040203501c000c1c0405081c21341d0180c020144200e00340c5200d08098079080b1448082c0300602440c0114000d1400b0200d400f0355000817801d800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 883247275 1250 883246025 883246031
    0x1050c0c03070902070b060a080c04091a0a090b010815040b090a1401021b07180b19120b070309030f110f010e030a02071706011e081c110706020a15 65
    0x10300c000080c202400340d070181c41d031107400242c15001c1207400842e00d64442000c440300c4060900f41500c90360345008284405024542d01c802c40c0e81444403070500041c14401e003450b84030302c5d1324000c440d043c0600840d1000310b861906c50800071503c00e2010070701c0c41c01015140c2e041411991540c682d6951004040c2c08190127010f10000480403c3c0207000440043d11001b00142c2e40e90f100e440b84040c6804130740c0c0003212642203104140b00c10304a101c02d03101c2c03040500c0f00205122041e080020b21740c10801220070907116000b40c0005007024265224203103e80107818a160360764030400c041d0283c1d85200c50060000e406020140e00705802071607080c03043e106c44000c84641c4885000b11508484c2c4404003442c0b2a817020510310003441d070420903403000d0002005130201c1c41140a2040703076598810b0040017040700d2036502e1008007444038070701d40009141c28012140f4003820200103005005064592a000400700c030b4203400c0900c03000907000c040346d110364004c03c40c11a964550b030b440000041220402103807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 883248525 1250 883247275 883247293
    0x304170a05070209040c05090601050405011e0219050606030d052a0f010606030b0a0510050a0804081c02071a221b0f181a04020a0207050a0906030605131101050c 71
    0xf13070707429030601c00c501c1045030300d0203a828101000200140100010b0421004000a001a980c01641d44010000761141c0d0041e01c5c0300c4200c1641881840d2035031103101243c084040d400d02200141c8180141000d4050350b041c0e0b24100302c226003500c04d84100c0542c10810340c24482c8500a507602d070303810b017001c004290341c802c0003041c3c91070742510703d035500c6640080c3e1035403901c607024034000c80e41c038008046c2114244205185120040c000b07000f031441c0e407414070074003e0024003848102000c5800031a11341c03401d924581e00507a500c1009402280c01a2502c0f0220310301074850411072034070240212840102000104550360801080303102601c0e0072112040304a03860414030089510b007074081d0400c0c801c52100503091820201806480034000b2404c40d0602e00000b1100c042d144c409003032100d040c0c0b0056591215040c040e0320346480d03944400c3d003001c03000303d0001c0c060071039a0200c01564407402e014005611070f112090301040d040740f0081d0800c0a010140c01c611b41c05940140210300408041d0303603d400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 883249775 1250 883248525 883248529
    0x516080313060509030a2c032e09031b06020c0303010e011502010b1005092805040b03010b030c0d0c0f060c06050f09070501081e0a0f0606050304170a050702 69
    0x2420907a80300e1105040744100c90100b200c5800340c2c55225814200960400c51400360003484c1c503484504502000e4251841524409604c180041e000c00000e0100e0f03454181c00c1552542c03681280b0b0115a210201e02da5074040355160b4003d580c0c2e1190507070b880c1c038903080580d00b084e981c2d403a420030704640d00e547c00c0222860b940320074009503000b40040d20100116601d09000b4188a002400c020b00c1107900d050403202d480e80d1803500c14441070401b447e0491702d8580719800b08214900324200030402ca80744d00254040c80ca00094040c0640d0710a44050001d6450301081c14240c400500d042c80d49074021060038490303800c2091441a00074025019401e00d203555840016858241e0b80000c800074810402c02c00074030485001d60303a0030150b1781d01049110b00c0c0c00c0c018143c4408031801140d04000d900c4020070a04004480900721540d910460505141800110540100320348214907010a04010002035001d000300c050300e01c940d420000c4014500111200d12480d0303804041c2d03200c2485020300c888409a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 883251025 1250 883249775 883249777
    0x9070e06090d06050f0106260411091029040915050604030b070e0d021f1806020a120207060f0c0204110a2102031e04170f131406040303051608 63
    0x10b5020b400000b507603041ca4404543d0000c01608244103101011f070715051035040035107070f403c170380da0414012021503107541c944024112200c03101590701c907074203c0034020201d500c80d0035002110070411510320043c03062102d284000301c4104010400a5050204000f1032626800a02a42c002d120b0015405500c450024500c0e800039002a02c1d002a004108101d41b60806103200617207100715850107204203554001029260010141c89170f505502e40310a142c2c50040c103401030210070a1540302c2c00240c41e010001d56031801c0401c01c2e6040000d200310100030314008a8918103407400c070303920b44d400c80e601c5010a8848214200c02240c000341e4441c00c00e10170104100190118500c00c3e601d200e08928030442c1814028241005100340601c1003090140c804404a880107140302c65800c04c607103d59460a0800c1070b245005801694080c00140c01c4070464000c10051017000011451210901e4494684501c0c24107040d41054010b141001f050001c40d000e0005002c464444046038200300c0031980e559565 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 883252275 1250 883251025 883251049
    0x11a09101a1201090603080403031b0803090d1d0109030f2a14010201050906060f130c0804021c0c03020d05010b0a03030e0114070b01091d0303070503150f09070e0609 73
    0x40d060011420b41c0060203030b5201d950040c19100802c1c000981161540351452085200c02820b00c00d81440ca01965280030600300365260b041450700d9200c1c5402528151541c1d00803a4500010b62860740040300c20720380050000821030181d68540c0f007a400c60303071b40c00310300c5410760819181000d4001d000200c110501c00c60076040d4516070031b020b4000e840d08010307150301020070061a0659040104005010320001001c0d640000c1c00c540544001c0d2240700840c1816501d03021340e5210302d0801d01075451880d00b2540d41400703188266000342c1c111510000c90303400c03140c1d05000100072341c3d1019000c101601d8100600d081c5980203034000036000d000d0400040d0440ca01c1c0d4021000710306080c40c1c46503a5a00210107141e104501801540781440c650b031090f49405050103244101caa0b1000c07141c080034541214650301c00d03202c10483c0d9032820b20080c050019001154a080b00006800240c2e0403410301c1c140488069901409016240e1a140825546045014501c030340100041c0030864155841e01500c000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 883253525 1250 883252275 883252319
    0x11803030e1002030309060c03060d02060f0304030908060709031709100e03010e1f020a1103040e01050a120201050a030c0e0d0c030c08060403120902010203070c15020c0102011a0910 80
    0x840c001c00000b4800035003a00301c03414083d500180308001d20700703501141c4240d03c50200e100d80c55a90b81e401c800114007001c094406500018046065a00c0d42c214000850043d4002d881d00200700d981c0304101a6148021150380b000900902410800a550300118103615980030148600b0a520880410400c03070702c118101c0300062455286d0b4083d800e080c424100d01300c803060050034004444a000d45050704094080007200c071340c0002e1030381c82c0b540f05c0e1801c488826001d50540b42c1e81d035620f1600140440082c012907201c0c5860410004511b4002101c7c0b009255040e1517190070923000b080e080d40103001c224000024002000c1410301155207591541c00d000d4454130038000a1421070130300e043e00a1854014100030b601890510002c80d801c404003a000d00e16500780852040c40394030040382503018204004245a90610000c5402c0b8402a00c1c100b00c186241d003100c030320310709803001282038520150f10882003004210000c2c6d810704110740c500c7c1d0300c0011000741e054029030701c5503102041d02a55903150 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 883254775 1250 883253525 883253537
    0x41d0a03050906070b190b19030209060307030507060207080111160201030b120106120303051803220b03281515030905030706052401090e060415030507051305042001180303 76
    0xe1440d2070740c4280400e58000307440241c0000100c800c0b500d462350050202910800c12000080c400b980c00b0840e090244d60301105132595071744d940700043d644030341a01641000d5402d1120018002c1804020b4442c080001d81401850300740680054004052940b01950070010f075401d5000380320424051040240741c072040c82c80010f0003500b001011288041e00c401c4070400441d038140e45581c0000103541c3c807070b0f1000640140c01144a140000782c82099404651041008400c01960301640300f0482e40521020144d00d00e01600201c0389411925142c80b10104554443d46c203020328107002c03040600032001d134100000c01320050748440d46075821103103044411a4884081040d80c03c1c4115014410032180d00c1d0301042c4004000010304442094010b0130140c0800900240080d130f500d40200100e034034801c19440c02240c0b01d041480d2600840c2c090240203883c80300354078041078068031a0902c5207412800d803550500700080904808444d40c144541045407900301c0351000d0803c454605c000f90f1103601c0384d0f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 883256025 1250 883254775 883254811
    0xe030714071e050901050405090a0f050d1412071103070c031b0b19030911060a1205060609060f07080403080d0605030c091501030e070b0c0705041d0a03050906070b 72
    0x50b29403211403260440c40000711450411803900c0f0b00301610f05483d0204c46c0450555240c1030b03003601c0c1010110000d0f0842444810a905110b800b280400455441d44c0e54059035010101092000e0310868103e00500b1241c0c0c000600e580303100d42e203403c2a0058490581e0310307000d2262074044c813512141d0000c3c0d805904044100f050340380340c50403c4006103c0e4080301810441011040c08801c00998004014152600802070030007a1401170700400c2000107102d140c80315071404009150306141c0301d40c4850700d840c082c04100c840ca0441c09403204407800910f11440d044101403214240c2d0400401140c841000f4000800000c0403407000e0100c1c808003040020b040c500c1c1c041014a000c074660865405880c0120031312112560003101d6800418080c02d0104404201e948103616000c2281d002e42c823428008901c2841e0500041030242c00c844007201d00380034100b00c1c2000802c00c0700c0214024031160344039204503c00203024101505890b00001c0540382032810315103c040401c0c0c03046030030003140391204800c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 883257275 1250 883256025 883256039
    0xc1101120f0213140108090303070e0d06020406020606010908070f0522020a0507060f091e0309051c031e170c0403170301033309050c121507050310090e03071407 71
    0x1c4c480112030300b4a40550141801c1007e43d4491201600b00b0b010000d10a003250401c0e1074039200780d0542a84854110364950b40d6500013500c4070000d40740e10340080e009040000e444800018208161503040d0346c95a091481e050030403041c170414500045d103000d42841d00161140403880505082c100719280e441c1c0d07820300792404404558206c00c29581c1d00f8a0100c40c0b60200d40f4502d441d02e5500c008c044100c0120f0340c41e040a48910240e0350009a020504488d13000b08801d900c546032002520030b455904185141041c2d1114404031079540390f00140240c1e00d42d691018256440f5504601c0395904640f4140d206d849540085100c0701e40d0588600b0700000420070480ca00c9010707c000b034600c07160702d20031078100100c464040d09822045000c03103031601014024008284540390700c1d180000c2a800c2c0c0340610001d01502c408480c1c4543c6414000d003400102d50781d0090040b07a120340c5400d000c03da1050708000c00c0d1340042070760301c0031101903100c2402210f0000310441200401a170444000b8503030549043c1c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 883258525 1250 883257275 883257299
    0x6030c0207090c0207030201202e05041401060e010513021b0a05030406090b1314180a0504050c0603100e04080d0203041103010501061103090f1c060b09070c1101120f0213 75
    0x1740c00791060103d038038200034440003c2a540a01021000440310020402100d41084060060301c2b110403481d090038041000f255a840030001c04180d030083c065560350b0040c0c0c0104540901c10345403c20300702e00a0340e404100a5005201d140542840040d0030307140c00c45020700c1c0110046040320198400141400101e4200501d90020000c00f0340c19445c100040c84030801e0340d1421303c242c2100308000e200200707580d5503c58420088a03881c5445007901d02d01031070000040d080944065915000303c03084a6098280481241c0c0729080c0c030310020800c0f9140c1070f06031251250040007070390385110500c01040c02d21501e0000710701a501800d417841c10b02d4016000c02d0b08441c1c040c3e00981c148200008034151400001c01503410241040b14949402c02580d004110b007003144c003c100b008444642d16010410841d0f50105071100c1c0242e60040345c5503201d45058911040301c040141c441c0706800c6044140d58428490803496040e017200100d080517840104030141d82110a5000c803660540720203000c0703420350328 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 883259775 1250 883258525 883258547
    0x15080d03150302010f0c050f030c01061802070c030b070c1a0a05091f0f0902043e030f06030a02060d0903140a080106050a02010b0604320a06030c0207090c0207030201 73
    0xe010720240b9540c00a0181c1c08052044005c0c0311200e800303042801030501042039822028003d44e40d440c400c51164500170101400f036018a901d4160b400c141880452080c2c5040c10740c01100e50b00c0c0e036170444c0c40c0c2040070b450084c408401c00582041c12000a0b1069614a1158141c2020000c07507090100c0d0090590300020030102d1954010145e0400c955410380c68a031050803808400078440410302204800307400f50001c040e4100d81404510300300c60441c800b81150000c0c2c54607001440365400c03514070788958501e1032228004241071005c07a143e2144808502c2d00303c84020100c5501d6100ca034007090b803503007190000c903881c5661501c1c160705046d0813600c10440b00b80034075415454000c2200e40940020307018020b001c100440850f0015100e4000d5126802003071009140d103448654074042d5030300e402403200507004801d1000301a0001d143c04443c0600d164180204410b602c01e0800c001203008003000300842c4114450150000f500902c00e1150150803c45a40a064101e05500016014103021 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 883261025 1250 883259775 883259801
    0x28060c0e0f041e02180907090f090203150114070c0902190302070803130515040b180f100f0609110304050c1008060d080f1b1603020d0f0615080d03 65
    0x441000e020ba0702c083c0904034144003903001a10342482d08104c41d50038500d1310300160052507034014003e40e41d8014610004441900305100122038031404c103603041c0d000660b6900020380c040d080209070fa41c002c00c0c05d110b440e80b84d508440e060012a44a800f680710469000101c5543e001034a4244610b003c07140407420722036818207520380046507440902c13901c4002d180c03040800389200c00320104507050004001007050560103c08509250030001c82015040d14100910003460303041281c9801e0104008418045450191080303001c4203262501030211000503581044d40c442e00411144c1f40e910414010a0352402c0030744c1c4030f10389803901c01d00c2c01d410703400d5280c07242945c028140611503006015a6101c82d05662180280b405840c0955241c0505228840c0100000c0b400c44c500d01c80903111045c00f010100c1c00c8414030442303408001a00310403401302075044a03001d0394010102ea0140b805801c02c0d0b11a82d0001020171103c1d02031200d0154903008040c4a0b0420108a4421580350080940003192 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 883262275 1250 883261025 883261031
    0xe250903060c05040b0d11040b030702010f06060e091501020f19021e060f070503161202070b040b040504020c100908030a050f0745061e0228060c0e0f04 67
    0xd002405000d40160280d00e0074090b128145d0006e4110200c7c1554014014080c02e962281031185010b80030b030102000200446140410006049100b1410303d00107507000340c0300500c20340b43c1d00d40c042c0c0ca051a20744214150302c518140381c402c40e02c0070000c00100e18041048000c1c4c105131481009513003074000042242450407510200e880d1303581d41040b01c0c1510541e101d80d42d03407040149001425805000030001585070441c491000b0300c603141d501e0340c1c80d016407a800d4800790354803151fa01d40140075a0081c40d8805174244418010390800d54000c0056043c90001c583c081400300c01c500701501c1c814401200c01400100902580038014001c0b80d4000307904c980c40c4482450440c000520b01964001003000710410740c21514800410a000404500028100500801091046410000303118400c40d8005840122051014404001210702e0040a540902021b092000350301c84180c1192008445032801c112180780094000c1c1700b01a852405500c8600184480401304001d241f1005030700e5002e0f6007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 883263525 1250 883262275 883262279
    0x40612140c1207020106120606050f2b0809151b0d0512040305090d0305041701060f060e12100911040c0c0605090106081b27010e250903060c0504 64
    0x5444030503149698080b4100200ca81d44000040307004d40400c1d070044482d000c2c01d0000c8418012650000c3c2c058440550b4088004000030051051046600c0852521f05011414042c1d242da0080f050740340a50003030b2a11410300170a600050803402c0c00a1000c0446180003070403070310031008204800320940403440940714410350014054200d12070002e010100d0741c0090000340c105802001983c06080024001211601c454034014026a22a0082d580980c00f0080030303600e0b0074014042d00080c2c1d4503070081c003800341c2d190007010748450800e1051141e2010340b0100b808244e00003085060502080031401042c01c414504080e08160070704007410340a03c0c145181d80440e1500b0070a02800382c1d40c41400020580d544001075401492560810082806003109100349592001e40341c80b180801120042d0030b001c50240016909050048600b0900103000e0042004000500055500c0300010b03c500185000c00f009480a840700c0e980c2520104104c40b00038030038000c191199804001c810305050b880c01e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 883264775 1250 883263525 883263541
    0x120109060e0f1b0103060909060501031b03021309060209090f0103020a0f06080f040204020408250b070b0c0a021005090a030f0201020405060906130b070f120305040201051204030c0804061214 84
    0x820104444004221003100d0f2105991182c4e11000051024a03010443d9403000e15000014210070f100641d0842d80000d400040c5c40360440b042401c07a43c0c020070360800d03030341010349120203030290b0101034550580c00d000300d10705610303202141481401d400c2402c1003290304503c100402d004843d00050125012100c003840320302e4102d4800c075046201c9004d00c2c0b541d0707034440c800100a44919044201580910003180104680c0c3d6900b5030035800030001443c01d080e4854039100028003039000090000f07803921001c102103203880c8005002400c0588143c8000e0700c1d11000201c203490301510b50301c945601c50004081415403240d0740d0b1811210610003545003918080028242d07014004006125240019400c2075024811282c40c00800c441c02c2e40540b00c88940c1041038800390120f0b0300391490b9082007142030341148240301e51485030341d058503001e080060b031907402644000c00030011420b1084583d45140880c82c8140036000030001e540c4d44e02d000b5080308070044250740b00038420b20110440c1e0360034000c81c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 883266025 1250 883264775 883264783
    0x30609020a0903060519020a030228020c01120213060906031a0906130e01060e1b1c0506040f09080c010b120304030b09150901020a1103070f060f0b120109060e0f 71
    0x684e008840452580c8815400c01c0c1c01c100c0c20140804c03558400680d48009541680261024500d0582a41c0c00c810504064001c052591a040001070300404040c0d02d03158042c0d544402940b0203008014244509524511a00e0406410100100c0c0080d101004081c0e81400340b00007141c022480d240c80300e050381022950000c00580b000b4800caa84803403412050311683c0c4001b5017802020000e0048540c2c55004201c240f0095445940070b80c0503071241c481c1090b9032011182d014000c00310103001c8100c5000180014240a4462a0720541b02c0c1104201c140a034011001c209000c1d114035a41d0b1a40c0c1c1c800c01d0308642d51100e0803400b40c00d100304d041c40786100c0801030700e0407240c000310705807191307501c40300f0072401c00c0070342e14089521815a00500200e10b4056014145408172511680501c007070343c50724955079005956000309030100c2c0f580d0010016003d50172400120780b0400021446650380780c000b0721031000071b900c207540ea60b40d903410b02401d0044a004800e80e00e040c0c000984000d03041d1021554035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 883267275 1250 883266025 883266029
    0x307060c110f0106090609020903060105061b1c020732010507060504060507031b051b07081608070b030c18030c0414041e0b07031505060309030a020c060415030504060605090f0106030609020a09 85
    0x7080d000403d0010fa007083f90380070000c1820880095604404180351040044007a54100320014803518001240d40b4a001001c409800c2043c000b01104d000c462107408101030408a820381001024043c542c0020010b014090143e40315020124003032821000040031103554801c4030a07100300160000d080d42d40c0080c12034000304c000d14405807144080ba1040c0c1c0c0340c82030903401410107105c0d40d8102c141383c100060f0f101060710050025079000c50303a22014000107000581e506143e00300100700501c5141d1000b070120108004c080d040e941120101c50000f0203c07a14158104a548480e2041008200b102400b079140c4440e140c81c1c0002c9640c09460b0303100804030041050007455920780d0002a4100c02c16100d034018040184100d0740e901e802c0074000d0301d90f004070503041702600c11075101c0101c52500e80240e07800d503940001d20314a8410540c4044000c0e102c003030310907070b141130740c0c0c0002194544031503040c0d92003644110362303402a6516000d001802c0702c034558484107181d0703c1848940360442d800b5a481d01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 883268525 1250 883267275 883267279
    0x40f0302040f02040308120108060a020405300105091609230901060503060a0b0906010c02090c07061103010f0e09010b0f0904031b050c04110c0307060c110f0106090609020903060105 80
    0x48a10501e4202d00081c0305640010b0103d18001c24040b80509038007090a06031091141a00ca00f038449506a8003640100d0143d598020405584000c0a00403020881001001c1c0f070340340c0c810011200246421584259023402494104c1d00e2020146d010803109240240040c0f00c0412185680a9182d100e003c44d5001e150002e004c904042960850309402950203413400a050302c1c81c0e0700706544010020700c264410180201a03440000e28298007c1844028140c0c024003c030100d959421358101385075001420440b01c00b5a1001d082000c140b00c18040c40c041e00950021500c56070400f82c160011b5240144400581da0400300b1249094a0f9401000039051082ea0442141d403940e2074180d880303640040400b1012030400d800c150502c0800038650903c81001e890400480c1010b00c1d005e45c0602c9841d5080000303502c01c04c00200054215844100e1904d41460451340131007181c60700c0342c10401c0c1d40c031120380c42d0382d1030b49014005503d640c800c040041c1694402145485090f0010a4684105204140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 883269775 1250 883268525 883268531
    0xf0c091d1e0c1201083d050c0d090b010504050c0c07090c050d020a0c0c141521010b0705070902030415090305090d0602030a0c020a0308130f0b0711010f02040f030204 73
    0x100382c580c044040c1c403c0021031035100c640350342e10741d10701da551451044282010384181070386000c00740c440300320801ca8140b007240b0aa85680a86000d8101038040078040711280c0700204001c0d82621a540700c0c4009280c416045c7c000b55501d400300700030580c1c0004d0982c441070b0354100722240c2500000a1041e04803400b102006c00c0d014014401925a8018540d0302c945e140d0002603042c440c140e004440418003845a20600e51440c1c80f0b0a898200c6140501540e03086011000c11381241d598110180c000c00205004004c5442280c600904290200783c0c01030166680c042035039010040180211409085002021030540c41c01ea12121400140111060001d83e40d42c00c00d1828184594101e490b0004064010f245100e203610307003070009510455a460100d450244c41c001c00f603201143c042d401030340642d03034071510762121144034080700c2d5007000840701c1003040a070100000e00c426002c20702c5040307162590602040d2842105007504c032803d4000840078410003082c0203d5031450396103402d4036010b603000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 883271025 1250 883269775 883269781
    0x124121511030106020c01030c03050106050f1606090f0b06040504080a0f090803040f05090c03040b0c2b0c0e0f01020303011e080111031f050604140102010f0c091d1e 73
    0x1000038a1a801c03900446030002002194403500003d0341c064441c400c0e41c0810803200c9000040b01203070f03000e02944c2c001940400a00d6801d01c40300e400b6140500150b40e44440548256031401700f103c2d015602100c1c84200c0c031491005003c0b4080f40c1c95404541600c0c01d000c146800d5849403550f10411445005101d030901208c0310380f5204a06030400781601310100c0351344e25260b1021200c03004151003002e104c1d44404000507551901101600d0059601210303240907030712503455050b480c2d04003c03100280b46115454160304007032291008076101c1013004d0001031300a80d00d00011b0020b0b449102c1135003d071104007142c8155036400000c41e81112109500e4800302c0c0610141412000426030100342c0ca0360034130490012201c809801140241d075002d07450104403030940030343c4080714858401d05034403003070074001007000c1228402c0c0540d0a0405100014541030314a0214003101c1a01c44e80c1c0c00099030301c8406104a80c401640d40c508407420400c400d406191004041300c54500300110104800c40070004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 883272275 1250 883271025 883271063
    0xb0904090317180d03020f070821040b0f06010509010806040f1517070e04080a0f0c02120a2003070512120d051902070506060d030905030d02012412 65
    0x104460350044500b02075035800c04100100400392401030f2092103010740000301100c58080d01c2122841c040c100c190f181400720700e449180e010703000000792052401c09a0348100511303a00c2c8000c41d00c924030418001c421400c0c800507a0401880090001c7d043c410b04000000350b0341e07000340c01c8940c04401101c011820a1021804401412181c13129a40960541801080b8045102c6030024002c0450044401d00b941d03c1101100009081d1005000164108118505988249085e01d000c0d4010700300019480c02540c040b075400e6001d922803400d10707000b0840030360404c0b146403c1c0c4200443e162400c10070070401000000c0d19000d05115051080d5600042c0b005c604001744401007548070780030f84050701e503100640400c000c0d000c00c4441c004500d4440c0c4801003154058400d40f0f20a130740060003842a56224810711a11051f080420b8060201569002840d59400c10410640d40030030340c000b081034040103c0050300c40039a1031601c4520046801e0900000c1c0902410002064004034a0032104030070180e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 883273381 1106 883272275 883272287
    0x1902040b0a061125230a031410110f130909081b03040b0f0c0f03041e0b030f040b0703090203030403120816202b0809070b09040903 58
    0x2109000741910005c0051203440303143c020650002c0f581c000103401138a145c1c000c442504140c490708541c0c450500c0154054201c460301408003211030b104101c100d001d50300f100038000c44042100440609103d8000c001001c418004101400e091b09000005034481c1c006c2c02c0030a40124039003c0103100000403102140c0910542904044611001220036441922405c0140c800c0d5801c000c181a401d000901c000d05c01c4c0040d08040c0001c041804015131080e40c0b24000028080c420001c2405041002c142d02a80c040c0054502c0ea903854010742c002c010034100a9014800468040308002c40d010800880210340c0d243c81c0d8a41c0c0e510340081e180c081199000d48009480c5030400c84680d0075201e81400a1205907041d20300e00c1d9039400e4007140391001075039031b6108030405042d555511a08a0034450f003200440b4064443c01d403c0c401c54600b18429202428000c568440d16002414480c10b = true := by decide +kernel

theorem cover : BRFrame.Cov 883093525 883273381 := by
  have h0 := BRFrame.cov_init 883093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 883093525 ≤ n) (h2 : n < 883273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
