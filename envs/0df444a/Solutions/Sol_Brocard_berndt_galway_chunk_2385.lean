-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2385
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:33:24.384541+00:00
-- url     : https://prove2.me/submissions/0991023d-2a71-4ec3-a1f4-acb01ed3f2f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 428776978 ≤ n < 428956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 428778228 1250 428776978 428776981
    0x30a08040b0c0106090902090c0d1413112b1b090204050f010e10110c030a0308090f0a03020a0201030f1508011505090f06041e1401150e0108150a090e06 67
    0x1105420b4645a40c089a140d600f025506c41c0940c1d80c500000c0d0f08203060282c1035aa941030454600080e040300c24038200e40080501c20008032542001e030b072004407885501d40a011b40c4140741040105048070486814607210b12022850140510074010195806103076400c2c480340003604811045080c0b6040000e555402140c10051030500d009003540407070342400d04141e12403003100400c5c01031203090740c0c5001304005d1101d056071221090041e231400580250a44109040c070f0709024018030402d0340c0640480c40348182608003a9400b013440d0038816495030241c030301c096881c1c00440103458070407110615240c2e504507031040074a00b011030348010a0b45100106440945810a05060700207a200038050040309003080708090b0000b50082d803008040703c00003000c01101e01c0b1140704041038811503412900d42135601c001003240701c42c0c5a040324900a0401f844d203d05a001302d40702d0040f500418042402000460540601003010f140d48400c05801101003565440940e4190313610b41500e08043d0300140c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 428779478 1250 428778228 428778247
    0x1303020a090218010f0306030203010e0a020f09071403060a15020606130216170702060708220506030402010e271f12060c02030f0301170706110d080402030a08040b 72
    0x32600300107001c910021401c11804400101e12800007400f4207042020711100710210a010350300c100080c0d0b80282c02049051030f05080240da0380d401c2c0400fa449006d202003428a203192031070205218504940d91842c9004c0c02c080e8408081e00090719407907001c01001000f06032000c0300040b40110406584c0102102c4c00c0c04001d10403424181002840e00c14010030492006200703100c00e0018031035112129004014580c2500c6655000714200203600c2500010720300c00b80074a0501070807507034584164014030301c1c080940c14003003002103129080d004401480001e01660107403004a5840030f000d84070040c0e00c040c898515000c41040459915031310703000c0052161211171003099520f4205003064107102981403140c10301c10913000038801456191107960030f101e40c2c0d200740181e900e044040f0120315201c0d40c440d00b40c030b06401d04e8801d4100c0c5500c94800c00244081c86001200e050300c00210103081c00c41144001190b05080050060341c040c0300f0785041400041444d00184020001442c1854440c141c40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 428780728 1250 428779478 428779489
    0x4110f0d050901060f1a0d0c090602120430060c0c0b06040c02030f07081c0605010e0306190f110a03050906010e09030d020a180e07030c17040f0512130302 68
    0x9000020380f685080424042041d07000703039520585a490f030040350701c8014841e0009891058503000071a4604112654441a4001c0d052030281c3d0300607020b5640e101900004c0c000b00d80981e220b000d02a008444074400d00d40342c04805100e60314001442c24004210365254801600c03030708603108001031506485441840081d03522140c10032001c42d014422400b2a0000960320f0052060b103003007400001440004000721042156014080301010450754070b01c2a861100505241c820700d804540701c4d0500403001e1030302081143c1b09074034007000303d880c0c460411f030310300f00402081e1802c9003600e40d2074440800300c2c04c900b07016180c000c9040e81d02040c03619051009a08240043c2d001100c40d00c052b2041c003080c0340c404010b45000e5402c044005890b640d1680088800a0140110728402c00040c140481d08200030040544920300d90744003840310319034a400c00c9428441801a482c1c4415510300401c00140200c1d42032a4031074042d00c00c0755034109940c500030100b13078410600d150031942541010411420302 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 428781978 1250 428780728 428780731
    0x140403050310171c02031902030318010c0906050904060b070f020315010303020a020f1c06050108071707231905010207090209010516050f032712030a0c0204110f0d05 73
    0x24104814181d142c602c035644d50b5150301e503407007150444607a40300752080d8030030070958200e4203800b080b075440c0f40d410b0030300651242d0040d0751440d0041c922080703045074503205004427030441120703941e000d03846850000d0881c1d8903000858401d9000f62a0040000d01c90108406465010b0040000304400412441094644403d20780e40034030914407500100003103500071502d6940070350180e40300e800e20b645407000124407082ca96040120040e030406154180302c0c0c0d41d800303a4161486281196205c0b903c980110443c01b204220300612903020100c14802c0c01e01901c054140b10690200e2040c103c010703400060b483e03c240c04003101c035160704040c04001d1903070b0403c0395100411340d00400314540b001c0940000c0281c17141c10040458915003034101000c01404201c45800590580c05980c0c0f9408031504400e0b014180032500100d182450744035044514040764150070311410803004614000c854181900d4150101500340e80c0107589041925800607a800144604c1d080010055030740d022141001d8202d500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 428783228 1250 428781978 428781989
    0xf0905090d021606080c0708030a15082107050f0109080c06060103180f050f1906110301050303070b13080d0618090b15040e01020a0e03060108012a03140403050310 72
    0x40329443d9801040240d1940e02624038502d46074450303559011020215100e040001400003000008101300c0758102e5101c518007000c60700c00da5101c255034400c00303a95113000040d000904411150300c0302c403041e81c00c402005101d1140007a158148014030b030103400c5443c811010b8610410001e0400542c1000384501c40d44800d00b401c08112540ea8032203041c02000034048024500707003404052000344042000030100d410810340c00c80e0201043e403a0000300b01e10030602d0071500d160510001603060745511050fa81a45d44c003a0045080030310075220440e02c1c0502600c4150039107003050ba110b01051080f8000c1c034400010f20340100d40c05203812980300e0225000242a46072a10700762003500002c660006660304248d09621382404000f0b0900000c1c0244828541310303025600c001144c0081c2030b044104215421000c405540c1c450381c1e00c0e441c40b07082c0e0b6071034070912500b800400039001c0c4800e00462002d014030203526001420b1252504403c0342103d0560f010307004aa404410010340011100c0024040e18 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 428784478 1250 428783228 428783233
    0x60317040f0617010302150705010501170706050405030307110a1a04180b0a09020c0309060c0a3807050405060d0f05070318061a06070f02093105070f0905090d02 71
    0x949507440441c030702ca0f040c00000d00c925114080a0700b1110042c003541e4100c0e42203402001203503034a6140c2004403101d02e0840200340104500000c0082c017802c00c0d41d0407140e000d005580381402c1075035507005c8070f03144000180c0c0c0025940d00c08100d0002c03c1e0400a5020f9200051030768490030400542c18102040c04100c203903508009031446c10b510381020a0044444507000541c607241c0e02c3c00030a0850040c080c3e6560001000700702c41130755030750015000604034003c8032a003480c00404840c180660a03110028502c8010229100e0310400d00040c5503940880c19145c00c505058881000070039075480302c03918259041e20340c61401841440d0b0311902d034010312642000c100c03041c03003540c041d600d411009101404c2c290761031310359801d17003c4000e036652014000140060703074843c041d24001a80c1200640160b000c0c2d0940700005258003a054441c14040d04c000000c2080c17001034801c0070300855203290080324640034100c0e0008401c3e189011200c06062a05404201458080040c9282141c203003072210455 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 428785728 1250 428784478 428784497
    0x30b09060d030f120f0c0207051005091c06111903060602071d09071a18090105090123030d020a30080a06030507031203050a110904020a03060317040f06 67
    0xb035005100e6510840d06420004c9522421002080060000c08141c80203e410058189a0541d0100324082907480032a010300440e041b20b00202c0326030003245602500142030310b05001c001c0c003030f210800000502c112000f00f0700000070b10700c41190350061105030440280070780d1410a0542c1501580e00a0643c51000f02500340c40d201448844c5525015203075075668803070020039603044003400b910300580340ca102951601e1030214402c45056000041c141041c8a00241540280c90042e0325141252402440200e0a90030708100c0d183c81c4c81403030421501145000d0441c80c0f03030307282480360084201c0260081d14100c005420003844440b40d1200c400310410304000e200300325040750545000b40360902e181c8512543e440042c07410017828140c102030710502c100d003000000c10a4a049040c1102943d40d8180250f4956000c01c00a0311844203548175218028480c8140d01e040907400751507800303e28600410283d03134a803120a1350761701c4071000314404207000038140281100c07483e44c000100440c1c50704c403c0f007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 428786978 1250 428785728 428785733
    0x4030b181902030c0a0b07051606090905191b090e0f04140f03040b09130e060105061303060608010903170702330a0504050111070804170a050a03030b09060d 69
    0x15404550030070107a140001c204002551001c01c0316940c00f4078080c042c0000141c031442070400721340041c50212100e1203000103c215000c0600d0560003241e540c0d03158231160504000303072500034120081100f400054400c41042040c0c90a0040d0b030030149025000d84030811003c1402441d20106402c190446403030401801000070b1606200c65020b0b070800c07200d20504400007151070801005031201c100300d00c8049000700f001781c81c4000409a104045404488028132003541c2c20549501d10324440b00c41e005000100300b01d0a0081c020702c28042140c100c0c08415469075503a40848007285c0080f84503070754840c1c1000c10036821904880001d000c00954104514010100035030360003014103001d181303480d40d04030074000701e0031240c1d440183c035601c00c03034036101d4503010318020003e100444044c2c40c190b09121040e150151014201c4000700c2c1c101c400640f03071508220f0201b50440c48026122168451a811800410400e0003000c140e20303c6540c0c0482c490350294200100341c00c0161401e44510400c1da0300c00c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 428788228 1250 428786978 428786983
    0x30304120f0c0b0a050405071701050a140105010c140c06040806040b06041401120201030207060e0a12030e03120402060c072d0e15040603050d0c0b0c0f250203030403030504030b18 79
    0x81c03006105130042490750b2140380281c1421410ba04c403074038071484003e4420034500107400c003274480c2e0030032141040700c43d038180040074110400b0b209040c0481d4440c641500810b480c0504642030741c1002048a442071204070109004e503005500c48241c0380c010400f44020004d028040c6504200215400d001d4031407902509440d0400603c10184e002403140309010441e40642c041d9441650019820082c15040303907010394544140032021070780012869a2020858001e10442600421910042d4103020329911b504594500207030040c0d071700420a0005480d011001c00900000e0090008941c0340c6584210103440c500700d5520090781442d0814909111244003065043d82c4090a055035600001d029008a0000d080982015002d400b84d4900481c10b20340207880103020710f10485c1c08803142c1d5580417441e4014010b0b00e41d4008074072802c01018401000c1212451090b00c850390141c641100303180c2c00203180d5030069004501062010404000740008412220307405503030325401c026841d8104e24401e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 428789478 1250 428788228 428788231
    0x90315020712050c070f1d0610020304050d05070b0a02010608070b090139050705100305040b0c0a170106021014040f081305031e071d010b030711030304120f0c0b 71
    0x40081c003140781c03000204100169002404251810300c0030750345070f02440c074241f004142c0d410351009020002c43d1050a0543e40150b19100d581d000d07604044c14003003008000c03021110140e885215140000c104009000000c0600c0c0300550000a03000f45009100c0c0d0410095601103030075400300703114034421350741c008030341082c818190488410b4000e0610141c000410210b41e0200c42610081005810031800059080585600716100202c0044640c1c1c00c0b4103503a0216001054846214042580380c007000018100b955205d0800080c6041e03c4075130620303144002d81c800001a440100900e1000405100f2407924542a900410341482c190301c0341000e082c50100010014000003a000100c851036071404000b4001c01401d45403107041c2d100203450589081222a58580104400040c800059190146450b0300c1307400c0600907a0b10300001039505401c0140104140b000c00c24100322071650500c011446a84154689080c004203e10014402c4180e11700da41c061003030b00710100021808403070700c25 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 428790728 1250 428789478 428789513
    0x2130c0801080d1722031205060402090609060a020309030303072721240203060901090c080c03040f0c1511070f17030d05010e0a0c030924110a0903150207 68
    0x807100c5403103c09010680e2840721703891040d414404030b4100d0070540e1103103e48070031120856044c0620380b1124200012441044511980044c04220505041c240140035012030401801540c2c02d142000300400d05690040f9034800024101003510f611140c81d40d9420b400484110101c801c09d82e00380402c5403107a014807910301250510131008c01c0d04001400c1c81008046008802c410f44a04d000e048d88006900142c0701c00d8814004d98002041c6903609208598103000c1c60b60301c4048585074030004800c81c0d84042c005880e118640340b000c030b0102d4440d404082c000c00940308008606403040b48002d25542807000d110545801559082040d11419040c00091302c0050160650750354403001c0407461442005490843c560402c1d000192100d56006518800c5001d503006101e00442100c0480440322100360041c601140d072801200725503c07510704801450740c401800962401101e58041030b40e007004074800300141500c1d20074030420000f4050142d140054502c150709214842c1c0d541c004d00e184003c0328 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 428791978 1250 428790728 428790767
    0x111030408043818040b0303030609101a0301060f080105011e02030c0105010e040c0902070309060804020301020d0e030a030e06040c09090312020d021305010e090f09010902130c0801080d 82
    0x81107940d040441161203c28200900d10742d008030b00f2961400d5410681c00300c9161540000c8040b02030819001d10f44a0a00040165195139545420400c3c1240d02501039590044981d002194048514a40300800c15480ca111078481d03140600040201403800d80240400a100004000b2a42c00071030031030103980c041c28000364580c1a550100d01d5405200b50361500e0790700340000020304540c04d8001a000f180114001300035107850300f110030168030070032000800050b5101403c00180d8464003040380c20a10040026282c2584040003909446d030f00340010806800c005101c10b41150540f041c4810981c92002404030340c40e2540320110361032100c1c4039091105d40c40c0e07050070301014484d1150414041000070210f45074454803c0d0030f4002c2d00f0454440912510002c00804c140d03004000384110b02e80c000303104281e2551404190f81c09000013400303101103507488642e1100140e944003180d43e86120301c03410001d6400040381c401030004006900c07511003030b04035551201c02030380c1c0f24110000f280e050703806 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 428793228 1250 428791978 428792009
    0x3050106091a01180608150618030c0111280605100e1006020c091f1806090204050d260a0e09010b030103030c030503040516090504050d0203030138040f08011103040804 74
    0x7669a401d1f4a00300b940e6001c023001800b150705500200000a410005908442410b250301e00103484910320860b420302284d01103042d155400031042c141240050b00d000c2185031162066031000181e547c1074600c506001001202440880f28071017445e0b501460118501004a01d4900082d4030b5810000045000761954070018040002e42900c2a403040c3d04c076500d0f030060a6541000d2059258400e58070aa00f40c28450300003074449c014000e88060f036a004000001d1118a1740e0340043c8143c820844466044403103c002c41500c1b100030103010001c1d56601c80348400d018100400040300c60503003042101c003000307100600c08694881701154680f5072500703109540b91234038100b40b4079203803542c0e030328004000c8080e4004c618000c1c6070300084d000324403403422608040c0703041c60243c0e1240024060180c00301c079070a29900b01c0d0410706002d0140e12210116078942e05a026a003a201c5500c19002407007030038000082000464024407400b040c064140b4000e6045050541d00c0c140140b055100d40045001b4801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 428794478 1250 428793228 428793241
    0x3051b0114251e0302010e011b0507020307080d0908070e04030c02090c19030c1b1e14070306020c1204140f120d0806010f050c151003050106091a01180608 68
    0x200790000e5000418480c40f81c2c100010100a01500c940c22401942459044c984040c814011810340200c1090f4840c60140080300448954000000a9038944100c2c940024801c8092180c08a80e2040d0b03030700c640c184c40c01d0404c01c6150030220f60100751407129180400011960040006500320b6046581c460981c4a01c0104481c0340200510700392070031402c030340114980d6055409445808460741340c140fa084008040b400c003213104488041c0c08410303145405640240c0e59000d12520602c10407140341c1c0100310307030070152404900d60004c480e5158000380000c0d030074904000b601400c1107402c00151809080c409080300e9658108103640c0169400e5a2081d180c0e65010343d241a00ca20301c0c011a0743c8502128001030550381c00f036410b10b01040c10a0000c0d02031500c25412980a10b180400424000d2942c60b11844071443c020305072200c00311140400f1000520a0040c00000c002505000c01c0c03540003011000d49080144141038140410210500c504000951001c41155800c0c200003900e9600d11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 428795728 1250 428794478 428794537
    0x30a0506060f1602040609050702070b1c0e030408120c0c1306120b06040c0f2f19050d05031504050604022506050c25050a0204050103051b0114 63
    0x58440242d03003800820008207030b01607511038203045402100d041c00290b40e20b030000e004503030040d104000180c00c035010600c103240c7c0d088000d14100650b44030f88880c0780c00300001001112180540c0400c26040003c0401c4000410082c950b08001020b007440e2070070910f40011a030395114240303030324001c100d5281e2030360a41002da030085000704220300618030100d1403450041d45c15172049800c1d03440380c1e00d000c0360411341d00e03c0341c030400c10150aa61030380011803d5108032200395a04001414a01454503409105a802c0a2007075070400b4860210b01030b400003040c03503e142007000c5c100d62681001020f02c10402c503030881007044012802c0c169400185601c1c0c2c0408030300a40300c2e10700e10704c3c06984100110b001c407488200744401258008c0e01c04100c241c03078148040b41c2d2481805520f0150b1401c1091005540c040002060704a80c4244104e81e0054041c0c4c0c0850251750090703109480130b40210711000e507400c000080600185001f40b070303c7e1801030307c04003042c0ca00e80621025001501604c440d41031480303201 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 428796978 1250 428795728 428795737
    0x80613150507030903020d030c02030711060403080c06090601051005040b1e0a0f02060a0510030b07021515100f09060e0109050a0f0617011a210a1a15030a050606 71
    0x3040000e104900d000000600500a04041140140304221004c1d0b034052083c41603034600b003020b5000d507140a000380c88401e034003513119484682c050301c10000080041c1401004040000c9080b0182400d8604181080c0c00c00c241603010b80e0144d68200d985ca40031590010441c0c1c140e654108505480701c0280c00350107680d04d089aa01c1900501c002204104a5044104100d20315055421600c26648020002080e00c009650300b03503c0c41e20600c3c040c0002030f001a241940000380c1e00c110342d58415601403000c02c404c0c05444000e800100340c0419000342c1031951466080441a051a0980c404500002004180c080c8030380740030080e05894001040c1c0c400d802a07402898018284880301e51030b109090126001c62045002040054582500180ca003d0076541200c81a440c404003140d2420f8000c07640b40c1c000d442524407500c4200d006c420801d407040c14140506020400084c2c82440303006072000710100d00e0070240c40303019804c0611900c0c0c291201207d03400300050308042030644400c0c0125a0302d015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 428798228 1250 428796978 428797013
    0xa21020603250e0406090b10050906071209171c050c0c03060f010f08060c09060a09170106170a0c052b060c08011d0f0c04080a051b01020304080613 65
    0x402c07000782030300282d01600c850b184403404c480400502d0303582d00c0ca44040715003d4100c0c540001c0107a840c0410140584003a102407079014011600d80a090303070390104112108045440400c0034200203000300d1040700b41d0f00d040c990395100140f0710044840030107011500c440200900301300000842e900518020302100503241d0016040751010300380007031a030a00410902841c40e90480750b00b8000769a0000052150080ba15204442c1c904504041401400e9003c1c200300707070500c0304281c1c0019900c0c2c00829030a0b0004008800014001e04001486040068040403e00b840e4007104054005c143c185940740c040f50012500300c6032221101d4800281c4009003140c54080341d01c0c90700305805220054001000c640c00a0b510001c450f81ca544c0c0e81c8031125100e03680003111407000790004103070748440481039030480e08d507018140c10242d90340761107460000b8640089440380c01903854000c0a202a404040e04280309001441c02d141c04c0100f0142c0e80e6000508c20388001c5c1401c40e10009001141680c01d14841 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 428799478 1250 428798228 428798281
    0x3020d020f1903080d1503082709070c1709181306020309070311060f0f03061504090f050a02070f2010030c12050103050d0c14100603020a21020603 65
    0x20f56038200b848041d0001404144100d003040070307944004034415490000e0740d600c40d1555040141c4242c1c00648c1076150f000c5055005000c03d070302d00c101da42d84c000881c41103043c1e0790751190300041864140b03100120f01a114401940603c82c248507513031035041c415440b2001c0e0040501d43e81c0c62030304402e400d104141d006007407c0d01c00002e2146511020035000141c0340109602e101c46075000051000ca0300c99076007020346080051103c010910400c0c0005c54028030000c00c143c5a02c804d142180c10030703900c03581c032400000e60759400000d0595064010244d04c0000c60008500304905900d9810711800c007150000e091481d8209202d00e01c48603d04180310001010308689a804181400038000301003c0c0b01410200e0300201118a10300b55501410b810f0b641e100700a4185565450403d07128003022040445403540076602e042c00000d410450441c1031224404082400b500c2e41c01031013140c14654000d4032020780c041c562080107506030301070a41c90680c185c40311130b41d942d151074002c07505414802840f680103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 428800728 1250 428799478 428799529
    0x30b0604330f0503060f0d020a060203030108010c03020c0c040908040909060b09160207060e060408010504050c120a03050702010e01050d1a04050a020703020703152c1603020d020f 79
    0x604803024050300414042101d8550446406407061221024000001002040007440c5400c042d0080c0d0507000002d070919149000c580d00140709031003950451401a4408801005201d909008042e144001d80c201185401c00c00103910341c0714541072480360301540d102c0c2d080e4010008010100c400034017a900c01080500181d140800c060001c0000361031041c01d00002050003003200b800c085a8584a81c1c00401c00b90346040c106581841e06103046581c002c40500001548100a000e035920903449280a072690080a2080240e080407044854559510500c012800a0f030841e04480b1800d409007003c00d07a4618143c0101c0311803007155807a841907418004422140e0b40c810b10440711980040324284010380c0d5940c0e180040780968000a001640004c00400c04622480010409900c03c0080410441403041c5181c6032550036440202d0718402c40b4075640340c040014050201c0707810f640c20b8185016440c5400003141d40c10740e214003078130030444d01130954910740e18209100c1e01c03070101c9102035104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 428801978 1250 428800728 428800769
    0x605040809190315062d1701020403060e03030702030f1305270a020315040905190b010609051f0509130f0204050a0b03090a03050307020a02030a083007030b0604 71
    0x10702d011444200c410002c1c490b8101010f04090048405036240800c45901d07404009286007a2400e240d00c0b40b90600b400844085000c620048035141241d846000244c0c6d02c2d451868914122850782c1c0512a65801c14014884400c0d4003104560444460b00d0300e00c0d4075403c41c1c0d040e9650044132544080c0c1d00071004510344844051540002043d42282d500fa86160350f1411400b9041e03110031241d44c0c205500c04502013105180c0790340001d80d40d40c002d00c100c6d02c25000240c080c0180050000085d541c2c003c1090042241540c400d400001400041e18940060010300031441c64050030b9a8800f01800000b2400007215100c000032454016030035030007841820304008181c0020f61041c0202c40c01f512032044045020040901140c0c006e80c40200249417420036505d00b02c8540d080904600d045000c0c0c00e0103940980c0d01084407164950250500e56560140b40104404006982003111181c0c4078a50280f00d5013051404141d5000c1850304000c6035108111000480d40c0c4140e4101940c1c03444030800d9041c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 428803228 1250 428801978 428802019
    0xb1c05031210270e1606050a09050a0816091505040b120a0c0602010b0109300b070824030c130212240a180b0406080f060702060a06030305070605040809 67
    0x280c00b0350041c041244a544d28106a20740c42c518940003000440110200190341c1f15a00170030914846140401403030f6110400181d0011141d400700c065503000080b04400e0008800302c160040400100c00c01c00c008a50014030044480c5100d694421603030380a09421948030380d1400035002e03031382d00161a0f042c8100d01e000440c40c0c401d070051000661034203401000030f50103a80403138290780c20b1504022420400c0245078500401d0420740200407451403020b60001810312400500402d441d4071140c649191140726400a801a0061403800b883c483d142d500f4541c4012406080e070303800540e2041d00c5c580d41e00fa46403010b0312806501c4800358801070b003042854007564505200400020122110091242041040081c114010800808a0f400018103061000c4d4880e81e00d0f108050808900c1590758500a4100126031506184c25040300003000f504a034180900c2d1f1b030040c4a0035042007410b00b1624018498091400000d040540d030304c2c0402c0510101005035200d200c0b000340f410780c0f0740140703101c0c804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 428804478 1250 428803228 428803289
    0x9060e060105030a0b04060f062c060414070e031609051512060703020c0106150c02011e090501031107140a1a010b0f0a090f090b1c05031210 62
    0x840038021040041024a400b090745404c9a41240f092212911a40c4039103001705010f01c11040d4141c1c7c3d500c4001402a001c11042c070050070f0450f0341940c2e60001c0041301d100820000c084500c1240341a0b0a16951103084030780c250000c4891802188480d00c4401007440d00210000f008079a20b8210000030303202603d03401c16071150b03145a82e10605001c40405215240109407501d4400790000c0c000a07441501c02d6020b03141038502c1c02e00100b801ca1365031648804414003040940001000124010195604901000c440751464080400c0c501e0742c82000074500d581034044c4504141e00c80c00c2084102003114141c502c8203421040c810601c820701c0140c103985003000c90701122501007800c09050010112000e960480e0076a4915a18142011034802c21550180041038240710858002180051040d841400a00382100340003554548610400c68111030042000010906907400d04000840110596101c0c3d1050f2a0110f0543c8030302504110942ca15040036410207441e0308150400c05180c0c5261 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 428805728 1250 428804478 428804501
    0x70309092c010f022a0d0c140715034811010204080106030b0709080d0503060402130e10053f0615090105010e03070e0a020f07080a0206010b040608060f0d060906 71
    0x50400704510482d29224040c440644010400034220741000c588c0160b011106081c1c01000e0720301c0d03661550b44940c030790007005100d080004d507189030103462000301c86100445615140c41c0302c248201c01402092004440b18082e030303c2044000030b14051240207201e1082903d0010000b5500c13140c03030b42c0410b0b008180301e12080d20396100d140c020608403401100d5400959070010080c03c0384140c800e6040c0e0315a8406801150025401c121610040310000350400140c040c66548a40e58100081003203220034507900428841c1a0540e01d070414000c00302440710742c41c544400c1003ca080c403506920003c1410880d00c0d0072060003030318101700d40c0f0180e0b03003c010501c0c4003c4801e142c1c1039881e80e00450340813580703500d1030307401d50710051081c0304072000f41400d04d92001c043c0030094034025859214500c281c00c488001c1318140c0010540c2c0c0e03c0103030180301c02c0b40541a20101d030390170503161490003446200d01503d054001c0f1380d1240c02c008a40c0f10b018041c1d041c2d58001200b405280d41900d003217002411403400c0c0303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 428806978 1250 428805728 428805787
    0xa06050a02010e070b0306150c0303070c150f0e06070201061d2a030a050c04030b0a15050d08090a06080606041215021b07050102011118030a0c0803070309092c010f02 73
    0x414234501c00c078000d44061034603480c002c50956a52010030b440da0300340b00303000f40c074200c40001032525001d002d40500075110080480c08105c444030150220f241c104027614038815a4184003061040ca000324600d0071001d00b004010007d580c03181026400420052464046c414100043c040102c0071800000c60080d04425410040e564440b0414081405903001c000c0c0700e19452004690380e1941504221800038074451060015595540081d005281c00d03e021540a175010403420698648800c00c000207202d6802c12002501d031407000a02e0a04c5030740556074038251340c0f104041c1030020204901c0300000c45290115611082d1880718400700ca42c0800a0783e4034418803402160799481800380603c01d00a8806260410042200c3c20f5100d0003024041601442004403c2c0d01140341c9101c42c1004050044c041c40c0d4039030141c1001003941410749c22407202c1604000742501d05034001481b0041800f20b080c8039801c4005171800e010301401c0c039607034a048840c1c004100c045d0440c081c450140040c180c40c040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 428808228 1250 428806978 428806999
    0x3180806180d0903020d061d030a0e030c03010b0109050622090522030801120813060806031005040203030405060706181110031e0e070812130806060a06050a02010e070b0306 76
    0x142103403000310f64000250807012079481d5a000690320f4212507a1551200180d21001c6200045146503406c0050f41174001040151090700031708050100300440ea2040c2c0003400b00c82c40000010b00340558600c200360086100050001060440280c2c205030044030503c82441d03140c0e40d12021004d050280c4440724098005c0e49080340c1d0201680d2003035081039054031504141ea1070100b0703800004000b0281503819601c10025030321850000b81c5400007800450b1034501090070110300340b524203418404c080074120b01d00f80500c405030340d001095908030717002115680d41c4e418180c80c0020141004d80d51032480c1110200d54102000403c3d0300031442000103a91110405143c18800c80035101c0303500200c43e000c01c0b2040602d01e140b40d03682081d120a6a070300101c40b0444d980e030703984619004100100e41e44160010072090030350700000c032604000f41040e5000f4070903401c040c40002c0030201c0c580300e48000d01c0b0001605095450023904100b0030341c1201c074251800b00d0760303c1c0318204856001f11031a031b106055106 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 428809478 1250 428808228 428808253
    0x3120e090f01050103020a120e031305150304170d0c08061203160f021503040804030510020c060711241012080706050702010603151a0301050601020a0318080618 71
    0x4665441500c80c0740010340070764640001500290301c81d0080404002c0c0b16401c42841c1c85640c0038145454115500450f5100480341040c0400581078102510030104c88060103815240c0009a036001908030081842e8401c184401c410b042c42451503149540d410041050102130f04803c04503c600400c2c1c49030703115200703602c07011030f10392051100345036040c20840d003c800070032149000c5485c0d00b44068204240f08030405150340381600300319021240700307500207803d00030004103001d00703680400190810360810000018030b036210300f4010206004c110010000248011042101612030b002c3e00c000c0c8990008461400342802400b01c442c81181e6a00f000e001441070001210382c42d04a410440031410403040d5901d40e000351001401000c2103648816000c40450a8032040740c4210050040008070f660581840b4860003050f006101d100380d1600d0104006030f6008200841c1942e454074200d0143c00c5c604540c603200d4182501b144110f4440e4008124222800105401751861100308032984c024108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 428810728 1250 428809478 428809489
    0x50d2c0d030605180c0d05090601090c0e06070305030a090b0109020d06121e0309080714030c10081f0e0a15080d023a0e040f050103080711011803120e 66
    0xa11070680c00c8003a25070604e0025030180201600f0940070b1140b54a025051150381040e10f2003507600b01a160850b9004111003c0da51040e023400d0505030030070b503c0c5c0d01d001b40d000030b800b4090b100000e41800f80c008001200c074081c03540300c20b5002e0791040e4132402c6961902c403018001d4120010601e15103203001c10100348403e00802162a00d603001d2008851a9034129030207d100501010443c00e0114152000c610142c050203038070302a145044020001c41002c02c00c041ca85030210030b52600541a10030b004a080f030380001c605d54881c0e08841d55044c08038545980204451a641c40400703500c603030005001361a22a43c1290301c402d14100c0004d203006868010903522410309016080250340f200c040c403003482418883d04e1811688a1140502100304030b1038104050340340d40c1d03901c1c002650140c042c02d210f240500c104544059001c204024a40c1159030310900d9101385038002c3d01d038800368030710b0521980c810782c03520100c0309007081c01c820b203199245400207411703242d10510004101c1400f0f0400c8141080c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 428811978 1250 428810728 428810741
    0x1807090b0315060a0210061503051f05060a0e0a09150b030c1210120507060206090706050f031f0b090319030c030e0f180912090a0303050d2c0d03 64
    0x101010b41c40400c42542006290b51120210700300f940a10342000708413240071311400004280c110405801100504d20090486500414041070765020590100105900f0003855041d03860958141c4e0b40c402e4454000d6901114404129901c403006500108946540d6009440d50315485001c0700c000c43c2c3c07a00c51020007400125601a4092400d1164018036289200b1140d00603221207403040e6440c0c0c60b181c03000201060310001f9a000e501c903100800c01c0302d030b04104065201c007a02001d400000d041c080000c00502c074801406103421030100102e00300c9924cc0c070580c0d2032485890110402d81e0b81d40c00a01c0310b65000b084d80301d417103030040544820b002ea03c40c1064000c42c66040e40c81c80c820400c1690103982404829040a402c005a109515069251010500c3d45001600701c2d156480c5889090185000900404048210401d01071075500e03807070380c00801045d40c2e4141015601e81d40a0b81c0c02074010070135001040c42985111100440f030b14007420040d0110300d91802981c1401d040200f003681034440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 428813228 1250 428811978 428811991
    0x705060a080403120f05041b0501030605131a090702070e060405010f05210316060e0316080a03110a170a050907140103020c0a060606081303120e0a021807090b03 71
    0x940c01c00030307000912804d03400c40c031190607000002d14410a03a01e00ba049920444003120108a200340482c3c41c400086d514400615007441d090081d1420200400c040d001007500c1c0109481d114452148100c148044a00d800320014003080c440349055a002951070302c0620981544c03c030300fa00414086d0402c2e010307c9050f1080c00e000c0f004c0301441c09041c086907203400340c0140020b500a0000e20701d021000c0c0000c0c140400d0070620340840381140c0c10103800f110400c07043c0d600d06520070000c9001d101c100948500703005400600351504d42c52110010b40107420021040d02075031000003001c4c8000c3c0d400c5600ea41c40c4400c0c1c02022015030742c0d100c40c0760048510035030704040382d40c2c081d02e810001d1031501404150000c806140150600c02d81c01010703071400b145410211407003610313001c00748185075010307076003550002002c408080b40717440a8078003901c030b404440c011008043c1c6441140700030103020000c003240c06602030103229001640c00c00708060880709403580c4c0001104002c1c0007402e81c1c00002900c0c011007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 428814478 1250 428813228 428813237
    0x1f09060f090b04032924031b0d0c0b0d05100e090c09060d0803042102190b13022d040207031d010c05030d060527190e011104080705060a 60
    0x1e04680ba9021002030480e00100a85c00160000c140b079411120068000e4400324248501c400303000e080b110129100c5420280207500c6543d0840900c151010221301c111800d542c0d5100f80212400e11107811485d0b50419009400c0004007200c0800884c0d000c680320311080d00d28111010784848140c1500303101600e0f0300485900c07102d100f0a9502c2c185540e01c2e00040004c2c00c200009410750307101c00d859081118195100551070030040c500700303501912178101d05994405401c800000786001c2580810380d2001800300340c00800050b500c0c4402d180b2500b400740d0018800d140c84001c5240d01c03003015030b5034a10340c1e00010b004c402c0034000d030525009581c1a2585030719103a68038418855100611946002094100b00340e0240394004150140b000340f4049240030000320340c460401c07060164a14446460000380d5001c082c16001259520f40c2440d045400c500c0c00d80c1014110388601c40140c20880925001946841600484014064000c1084038101710642d00001e90300d008022883c0991508500442c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 428815728 1250 428814478 428814487
    0x702070e060f09070e130f06060503010b070b0403090e0f060a0611070905060f0a060804060b060f030109020c010b060c010902010206010807060203090d0c0f0f180504150b1f09060f090b 81
    0xf0318209003103641c820298507041040384480e0340000c1081c1701240300c03440036a0345d59990150038015400b81002400303a82c00c205240d0752420252403d03d115114000d0103040104003c00c1c2010b10441800005000c0401040d000341040301103401480001c0e1041407150072000760018000d801461001030f5102060040d2802518048400323002d050010403c41c1e020701c1c1070300780d990706580c1d024440d00a0200b03960340100394035040c580705e0101c03031007203010350312410080c022541c10709409400c036819179001a4016803100d140e01c0b881800350030401c05035588544c1c0800c840600500c15440015094003d80c21691140d0340c1d40710468441c0c003a400f84c130300142c008002540e05818604a20009107201703000380b614940d83c408004419903d50741201000d8221344c0b50820003909100a14800105104403c00c8035041c80d9035850701c08821002c0d120381c07154407441d000c1c14a035114403000e406100e01c241001945801540000d1015502c1d0282d0004118542c0868503114400c0c070000f02901c4c284644240782 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 428816978 1250 428815728 428815759
    0x20d0c1d0d050c06070804210816020103020706060b1804090528080a0f0806040c020703060c030609020f040603110705061b040b0c0d021c091a041203080702070e06 72
    0x550702080c200b81c0b5140f0480e40c242a468607a48000d00021740a20801d68480f81860809030074a905d51881004500842e411240801c15100881e00400c10801d401381c10905184010b8020b8002c401c0080d00442c0b4040d000600101c1c1c0b400188072042154852140142c40130f42004102c6a5203034000d01b865206142452010070403c407412802c20f144055107964000c1a5078140303135580542d5803031001030314819001c1400e540010840c3d800002c02c513001c1c400700b440c4040c001c1d6142414440601b9051301c90298030303405400395000502030000c00000f5555407225450b0010103078002e20500c40001d240028500c1c4000490b020b1321482c80e03000c03014003002d0301c43c005000c2c5c42815040c6c04940c8100d003004001801c2d0703e644c0080468149035005444540e0030030001030304154125101100c11424020012450ba5000c01039109540721080a0b100c44d0666050300320690080d5008008844002c00942d018590480b55152185a2903400c44505540310090f0305441d00d000d0702e407079801c0340c00070070101b98 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 428818228 1250 428816978 428816989
    0x15030402060c01021b0c010f091d07050d09060641010302090a03050a020306010603020309100f06050604030302070e0907060503010e0601120c050d0e03040b030c0a05040504020d020d0c1d 82
    0x9200710100003504011025004940117000e0703014040f6640c0c0f02e41044100c41d40c1081545840400718204400c00514003100c20580181e00380641c180682031000003108940201e080d903640c21840c150070481c0401074548200200f00c20b0180c3c00d001c10001e10500c64060161b507440d01c2541d84208502c52120007043e070101c801d01f980001c03905264007441505103d4807070b1005040194003031030090604012a00505060a8040c0c0102c0c00b018010810403064480c002100078034a50a50000140304280010391030042540750880c0e54400380014000050660000300da9054030b01c038160481054482001e0fa86c2e55007024070403e000300d03400b40700400c0000801c02406134040d1060410005008160b40b00404071380340800d035440403442c0821080380d41c254500c90100d2a4000700000c41c60a82032505499882c04003c1210f420076000103010b0030114801c07016a402003a002d0415512091405040400383d0020851002644d20341038000f14001d108805482e00b607003090851426030f0030f04605018 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 428819478 1250 428818228 428818237
    0x309061b0106120b040201080603010905190f06051e0703060f05092511150f0402120a0803010b0d0f050402010e0f0607022205090601150810080d020109030e1503040206 74
    0x681950388010003d0010003500604140a2103410f02d41520300d0184005051050b0203000103003c1e0303240500404c00100c0009040e2201c14800c15061141c5229107844140d090341f41500604040c102010700601c10900c0926102c03c0810943d0807441c0c0e030b1880350032021600300344945104000050010080d40c02c05811094008074020f601002c0e0440d1005990702c0354020152860019190301b801351036103402030154401040c40c5070301c08425410468030f11882c24038043c1c00a8860403c244c0b1400c0d54003020005002d2042e4044819602c80da504c0d011602c41d41c00c4200164080c506100310640740864034840c0c42c1c0304a43c140c5403031560003400c0c0140010b90003243c010701d811540c00c001d5400507a4840c1e40080c03074490030414101c407101c2c00c890203009484001d410fa002e581c0c4440700500503000c032084d51141c40c06091910314600d541d1201c04000406d1640d22007000c0f03014494250283c0c0780c0c1900f0640035240262034400220000e0401c1c0000101401d080e00440c000034404140140f400e040100b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 428820728 1250 428819478 428819527
    0x601121a060604120b070306050f06121302030a20010302030103030f0f030204080102070c05120c060409020702191206060803090a0303030e0102042601062301050306010908060c0a0809030906 84
    0xe400d084d00c41108400300d442500303066941051300b40c1007141c20381e41405214003515040c0c4850201460a0000c584540501d42010720307002c0c0e80744002240308801c14003c0c3c5589400a0440d078500c2701c075040176201000c1c0c1c0c0d5040d000c0180e1780c114505841d4024002c49040303d62568a940e40d4010f00301c4103ca41480c0c80e1005820590200000a07400300240082c108090240c82d501540f14031f070900b00312146074079880c803281503040304441c00170380e5848038140c41c2159888040565a00042d10000d0f40d1500d041000300070810989070040345c02c2894252202074288603141c204400c0f1b4031540d1541e40c9000703c07815542d011100240c00d00c00039111750401c0e0b0782010000005401d003a01c81c01d081c5155a10101c0c0d00885043e0640c9a13006103e00b40111030050905e00c003450070404101a07442072070706c000070f0118140100000444c0e626403050310944014441325050720900d04140ea00203250358010f2101c60000f8401c1008524803040c048100c40761a40010262460b04140c0010035801c00f4144910307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 428821978 1250 428820728 428820739
    0x5040c05040e100509011b0525060f0f0b030c01050c15090a0515060904061802040507020f07060905210f01050903042409170f10090201020601121a06 66
    0x955a00ca601032680e00c01100000b40ca003d0115500280840b40300400b2200307542e050074200000d070b0140e0301c50714802d80c400340781856441103028a4212000000e071a001c440381072000f00300c0140301c61580500c02403a007101c014000e0f145402080001e45000b22005e55242d00000c0004003150f0041c0010030071448440296100c0c801e8005e02d20b03020100c00c0382d500200d074002d110034500b008000c4c016a042d80341030a400c4813884c10140040354190900410041210760f44402d80700301c0d940f000d06501002c95000700113002919200030029200c1c28a442d00d55000d1080300070105529002d100c3c3e4209440c0003500c40b401001d60b002c00c403804c01e040c007280c91403e40240d40d030103440d1213005e01885202c0c166843c0195550b40c070303187c89001000000f46062418100b40c1001d4480d50b68441690341c210365414aa080c6401c040c03503040ca0402c0901030325035007180305005480c000c2d00c0302c941292110900036003c0e100c4e5a030b81c0d111250006200705500030011003030240004414200200d40a0304890003601 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 428823228 1250 428821978 428822003
    0x131d0c090112050a0b010212120a1d06090c010806120a080306040209030d091e180f0f0929040b040605130803010902130819030c021519020f0d080a0504 67
    0xe200f1a00f0a403a0240219100c801d1104103503010411a20815050046503180103080d007130b0040b800034064808207003203446855002511170108200c05203046140160360203420403181c07040e074070400c1112050215010300e00041c590f01d0141407006495901101500d041d500664030250107070300047c0040c0c0d0040d800c1c044004d607a1001c00c524038640c00c058841c094110f040490b01ca899130a20f0300d460343d070601200e40500c520f090720951200d0310b081c554001300d1001f041002c004045c0c043c03105010b20705407030143c8400074802d000ea2502c1000492403846000400d040c2c06640c41d60200b29000703880b00c0d844001080000c1d00b40e501c0341750312a000d644ea0000914044e91041242c0e0710a03808200801c0d000318024180c0b480d070038981c03402030112100810035034050030810b0800da90a0840642807011a5141e0717000d5455070075040d60900304103049555512050812101d0b95054400020f005204074103c0f03807040d440004800b0141e40c4161142840c0b40d0703418182002030400188100c032404007051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 428824478 1250 428823228 428823257
    0x1303021306030c15140405010903120309080d060906120302060106110f0102040b030405010f0902091308040801090c030b0f04020603060607140d05300a0e1908131d0c0901 75
    0x8038200103030004207000912880d04404c0207002c01d03010b005089403000100070400c401ea800030200c0086039440f16038030950402c0c14109034000c010002c005002d002d00083c58031801d00d0305a121409560440604100403a20b03400741014000945400802513407028005214460040742c458070480401d030111410540c500c196142a600281e114096001d0040180010400b003030044462110070381d0b4080006072134a400140c40c8010181100b0034500801d520700c824000c000c000c4802030000d02c2d0003400310b10194600955000a80d1001351180342d80c9101080d40a07c03201e0b01031b40501d800610083c1151601c104202072544080403c88004400710340001c00324106001a001d413840c103454480e11880b442c0c806201c80308110407041c00500b01d1400b484401e454941074150402118100040c1c1085200c00039884c00c03044001180521884044110801004500405c66451140707820310700c49540c0c1388907544069680641e880d221000100042c4200d01340702c00791120003c145440c40803504d281 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 428825728 1250 428824478 428824493
    0x80a210f0506040b060711040b060d0e0a02190602061b04030b0f150d35040e04031d030c011d0d060204090b01050901051926070f0302130302130603 65
    0x40e5900036016101c508028291500384504c1d4803080c1d060f602145041c0d01d503520042010140d403140361040750381d1041180780d03888210035240070401b180300c07c00071600c00c0381d00b150b40c0d0544c07071070304a01c907080d80d040080f040c1400c09400c00841d501900140703a66158503882c080003a61540c00c2e90701c400001c0c000000812403030484240103401240d0b4046003410b0050226512a41d640080d40c0142480c0214400103110304225021045e011000364880c0001622500d202c0c06180138003a20000002c0790103e00c0781c1c0254000da00451190b02c0f901c0b281c41748004030100e10a5040d20b8242e054004500c2201154000c00205949481c40800ca01100d4607000024003501c030030b83ca09860441e400318050000503004d104001d550760003400d10300d0403c1142400242584030f24611800700e0120004a602d505000d0246110a4681c0c1000c10240c0e0305c02100761190040c0460f2010700140c003400c50200043d01903c2160003902d03540010103405410350b020f20403070b642c81c3d2079424003071566401c000000c030b10103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 428826978 1250 428825728 428825741
    0x5030f0d0203063a051633080a05040302010e06010f050f040b0d0f2409060b010809070605280e09071106240a140a0801050103080a21 59
    0x4030340041e100d007040014416803206441500300b40c0080c00e030500d016200203ca000d412403c82d40307001c40000355145403a9003824402c4406041e02c40c030201d00400d2003107106031602e010150070140c09010040d15203441c0324a000b06006000401e4180b004920980c042e500221303401030180c000400c1c50201102c107546005c009a0280d11100c8911100748924a07041e28104400c1200b16030600c9680d050758000f46022210240c0100110245182041000501044400c0c242d03650402ca00e00304840322079100c054583c01c503040750070510700121402e42d98015105280500a080000c002042c1004003d4801d607105a20403400101034913a030b0070341700d14050f0b0002010001030b9568814914144103000ca040c038090505c000703102035020034404d0080700264080d0f00c0315084142c20390380c200d954040c50402c4518000e0a1708040e440b0004104e89049403000e03c4d0f5000306036054642c00d0764420007070382294030a02004210313210401c45050114480d01c1c051140ca05018003064015500b032642004940303c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 428828228 1250 428826978 428826997
    0x6040b03160503070e10060e030718091a0403021c180b0703030c1d100e060c0705030601091406090601021e0d0306050a06020d0c080d060b030919120c05030f 69
    0x12070300348100e00b4103021013802400d0352401201035081c2104c00c0b000a54050040700c0c204000c0700340e150306558003005954001e11141000040410204d500341001d00b032054015500d48140404034801139403550302462281c0c0c0c143d400b400c441800c0e801030665004404400c88208580c03040518406105425000000d00030345420b00e941d04128600a025640d01034020801c2c0414000034110a900e640720300315000300e0440301c29207198414201030390010041840301d034120b440071841038540c485c0040d0f21000c0d100d08600300c80c5603a1345ea0320349805441c00d88200301c110201d048046040ca0070401aa10b8100c081401910000c41850b44100c0c00c404002e0304040456204100a648084e054440c0b1005400103032968a5142d04119019590302901640c1c0c2080020031030600040c01000401e680f00e500e89001c041c08440c0c3d41380210101500305403070010072401446030005120301e51a0784242015402000c41c0d50b4962441d409482a0007030707050a84072400200122064014400d0080003121b6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 428829478 1250 428828228 428828263
    0x507053414040b1008010e270d270306020306120105070914180f090705040c0c020103061205070501200a12021009031209080405030a0b0105181009020306040b03 71
    0x1e003a8104070603914031104003070050030a4200d0112043d4000741090540700c0a5940c484641c40701240d00c0207059030507110b010301b10310516014582000202e03420301610529512103a0402002c0c501c1000d0b103d01041c2202560074500b0100001081c5401542d0700080040055800c2c409040c04d03542550012074901001600c03121082c00001200c1c2881c10000e017054408540b030b42c10b1490b400410f503101605891501ca10320b0300040e0010390401007980601720243c0107002054140318042c02c008401c3c40104d010900b402c2012580809458074002c00c29007110060007014900b100540c0d10300403101c1550b248200500c031665880104200795103515100d450419658622540001e0608003a485480302040c10540d0740c401182c0e010300c040d260b00954101c00580c2c2c03010341c541001c56105590186801d030040505040602c080442c0c0107048070410303a60040340d089000032010030303410b080318040c12030f0741e5040051204806542c091580050301400025080842070b000919211402d0300c0c445900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 428830728 1250 428829478 428829509
    0x3040e07170106020604150f0e0a080a0e06092103041a04030c170709110417070e070c1203020901050f120103060e07080a08090103142505070534 64
    0x1501d07a0a0340c10300608041c0b003d8219402c15540f40c0c0310b000c800625401300103850740c19400e0303030201503070000c0482e214100846a10b28840d14140b000741d0080ca0682d00842d202d0415660941031090488181c041d00a111615119484081c1109800d4480000361700713203c02d1001180c003e42502812101c11070100e0b085440724a1890f040e101c600031f039000b10412244e02509500ca03c44005005410744034000000701c0c0c00324100a21001074040c590202031132164028483d0b04840d004603000041c0c60210b6289013103543d40351070584103600c0e070001c01840d88800c850350012491295000d040c500005251403480c4c084a60070510082d00030004000036002d100d0010004c116580c412940800040cad4003609900d0300d81800b154aa45000030050003134480011445100d0b03110341d1080c4d0b0440ca0345884031210b800c0100300088051141c1d080d804001c5000610039002d24041d00c1a1030f000c50344a80182520441805904070385041e00301031101d415401f81211006c232a2448402000d4012402c480c0703000e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 428831978 1250 428830728 428830757
    0x1060c0807170408060a0f11070201051602040b13060504050c031006050d0f021207021501140f040e0f21040b0409152d09050c1207020f1c110114071103040e07 70
    0x4507941064023120700c8a080000c82c0060341c2141c251080c24410341640c1c0050705150001ca8050200004200d90010860a1880b17603080b0a41c0488203860050f501000940d039807120302c502601c015503c4845100d500802005124400c80003003002c411944400f1034015a18a00d04099030041c2c0381c91021462003000f0064100d60400100040d90701c0381e1203200d5603514100000c460042c80b41d00c030301d016540c615070100d5281c071181c101001c0c0c190703071204445040d209969655150800a170030176001054010035010f290360164140d4050395944004640b45c140b030701c03020b440141413841d16103032010415103000071001180380901c00300c0a120308090600e100c00c4500340c02c00c80c206030800b203000e03440c1100380450105100d09880c40e20341e014106000503250301c41300380c1c50b100c4c0308031100c400b80c442c41d00c1c1d14030300d80100d4114007443d410548407941c900070360340c1016083e03c0081c001c400045603000b0016004070310620a50f1000344008003980c1c5040d8542525483c0800110f82280101d040900c501a4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 428833228 1250 428831978 428831981
    0x10b0a111606030902011413080708010b01050301171c1d1804020402030403170106050d11070f151509061e0f03020402210a1401060c0807170408060a0f 67
    0x80340302a02000d0300c109841c10000030600c090718020542055520a441411039000d00620010800105045521007205001c0b202c00712020b4001c4407500e0281610000e03096038140211080080140c440303504507070914043c401c00d180070311780c0d01c10180720b603e1103d0419a05000d02c9121890aa0b0320850700792079040605100381d650a40c094000c940c07201921340501d05014031075070060b60444025a072900c1d41e041c110340c032009401c2001c200d00d1180b00001040c0d40c04c00700804115680001c240012980021411141d0095280c003a0000441445070000601c0721024071020100701a4001500d240d80001e0407400d601c140c001c44c0d0100e6941a0a2085c040c0f00d02da0a01e50003003805041d0402d0f820003a84100d0200f0074400240180d8010840001d000310320000340b464080020301d0b6100740d2408041040207404418501500d14941c00700104406115060001174560403d500f0f928120b803e640e100e012012a01c140e01d680002400080350a0009218180c080d251180000c10002c2c0c2c1801ea880 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 428834478 1250 428833228 428833247
    0x1107060506150418150312050a030b04020c0607030b03030c19231e0118030f0e090108030a0c050703020a030f0b0a020a0c110a0503100f0b0f06091003060b03010b0a 72
    0x11260b10303051000f00300040240c1144050200260300c00b04903400406800d90004c00b26810082200743d5906001ca1400e030300101401c10110150750a01c114040101404200c1c841c004031940950840c0002541e814000d41007045040006000c5074500600c0480d0541040e0f1125070320014103c00302c401d00d05101c8019680b00907000d00705400d0101300e070701303642c035541d25201000c0600848070303c1c5800c40c031010350030742c440e081480090041080c05051840c0040c02c400b01301c4140c0b00490700190911060f4200100710f54181c4640000462500284401c266420b03108010300312030354401c8010210068860054034401144240d0050102007010316000501d5400201000b01e814070520000000d5580b140b003141801b40c00c11001c5071400c140a02140da0b82125400081d054800c60f9240d80305182583e12000e00001c0b10748080049100020810186412443c0031a51011040c48240c413030340340200000500c0300349403c00142040c0d0b1058500c441c5d0300b09900024080390042820810783c0d07000b40e00b00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 428835728 1250 428834478 428834509
    0x200f130806060907140c060103062406050f0f0903010204080114070309051f1506020c0a0501080615160c0602030702100206090d0503150d0f0212060f191107060506 72
    0x4007101c0c90400040f4002c6200104000100100e804041066800b4541125460402c1b03000303541d800d60b180d00b4290050203010b1203a1214110191680043c66007600010742560425a41c051030300c03070889011010350300290f2030840d01c08001c1000c1e18155809100400040c2004000891a21385042c90090420001080c2c0300c01c0c0350900001800040c400b00c6c1220340046040da10320021003e001c84d40c2e0041c006035800401c4c1c0f007031410011421075000070301030101d190100c840b03e0030161603500469a0031001d41d44550884101001000c4407144040a8203459200500d095010401c980b41c005800149600c500003682002580c4000e50501d103441074035061890001703114a092951900d13a0300e04202000c003041090100104140101d0203c109004600040c08807032294000e08000320b280c003021004901c1008180c10b08000e9640101d856031085100f06a143c3c030b40e5450551241160314000c241c1c07070310340380c0c3c4901004001201d030300904031190003110001000d2405105100100d03c0900c85d2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 428836978 1250 428835728 428835733
    0x8070f0504060b16030c03030e01020304050c10090f1811030408070b060901030b0a050402060d0603110315091b0a122a0b072a0b0703230a03200f1308 66
    0x1341001811540c42c1d84070f5045c0d0500e0300002841c01400c00700c008105040b011a29940000288810b2240014211050500444102002d01e201500071b884030102c5101d41e02c0403605501341081040203c0c0ba08030482036800c00003103458505c2c00c0002c0201c1e03104460485958402141c03a04c1800443d20255600c0002965071031813075410345d02c420140f00070041c0a4140baa848034005811510f0b018117599000071000b106000150311391504154118070210198080c2c490707070014011464900074051b0080904e9809030642c1d00440401424440f04a801c058119050400029084d0b0b54a40d040070800d001d070800d2040041000c80c0d91030403840e1440c4110450000c01030a014100448045460066015500c0d81080c0d01e0480521030510582130360000c0304024003400030307410034828018160340d4400d91300c40c00084d900b6140c0c0d125102d40d14100010b6224103115410000c0c1c080d520890880d20303d0039480c04800600e03406000c00d0342c02130348411440c000105010004031180c0607510f0150444001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 428838228 1250 428836978 428836987
    0xb0f0903040b0d02031506130e06040c0f05070303020723011d1b030109050d20011b03020c03090d050705030c0402030105090a050c040305030a0c0c080f0601031b08070f0504060b 78
    0x400c11450060f12692030419500001161031007050a0a82012000c05840183c944c035045a01208401744e51103000700643d01980007400501d81441000510318980c1c0307400144019500088903103400ca15012024140d080050700007103002c07000340310084401002e0594020540c0004a4295080d8601c664294100050544108000800e0089c02c1844201000181e1182c4500017170241c01c3c50540501180910a46198019803041c1d0742c112003032244240004401e0a1461035089079205d010f0b14040e100f40000a0344054441e40040c00020011000c8a0403c0e00c940000b4050007050041221719600400c401c22540c101071064002c0b15000319011410340d850880840c0b05c6400050018009075914000524103000c2e1905075405143c001d421a510b40d800701701c0280003260458016140f800401341c0005580da00021180320010141c00a80101e9195640c2e40f030411000d810003030800000d000010590303607402c010441c004c00005115000302403410040c0003c50350035400c0320007821010030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 428839478 1250 428838228 428838239
    0x306180b280219050a05041d010f050d08030109092919020405010e0f01090315020301050310230a180302150a02070302030418021209060601120b0a050d0f02030601030b0f090304 78
    0x70754201d03030300d40e980c01c01580e6501400c100b206c070b901c0346070000d50041d9850303005024800d042e41c4030241a80d81c00844030500d079844078100803041c5040c42009003a41010001840300030144d0300240c4035641300314990440e00b402030360b616030800031060300710300c3c0f064500080104407851020090719800c8240000c510f02410300340004c3c10b40c08180c4c00c041c020600b0030300c0203049900c160203000045411046260328030514010721801703540203120707940c4070307210b844840c0018050074407802c00320043d10100131090b00740354441c00090000c02484140d001d540c581000103404081801000355611a601038180d00b05801c89070054031402800d01401e5903c1403001c2d02c0000d4000080314280c800012028401000c0360716505c020f88148080340243c924850184100070000103001030240034240c0321510728180c0c41c640c8004869207281d0715a4010b172010400c000f1811f014120b6101640a840d03091032284181e00070030f1520f076003a44216910141f00042040c0d2401c00d0146503080064900a10314080c41c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 428840728 1250 428839478 428839507
    0x302100515010c031b060c080114010e0d020d0203071802090109081b0909030d1503110415120507150206060109080601030c06032403051c03050903040306180b2802 72
    0x340740044c284103003045801000a11055807840b2913034004000d1094039503490340100045400e01c5142030011148403080495070041418030f800d030743c0203445107807003007529001c20511040a590590b0540220b1b407001c03640316110402e900402207140000769492804c0e1000500c00c0c01e680c0e100714038030342200ca009256007011100410345680c0071030b581c020646461400d1410740c483d207103041294524048404250700301c13412240045900925241c09003c1d2400240415603603000c0d10f5a420000c0300400f4840c100004514080480c0540d00311800303540c83d40b0000d5a000349841300900036921110400440703603442045030b40504440c81c050b01c125491b680c0d402e402c800d01030117018207044d160000240b80d0307540d50383c0200040c204d0718500782c0c220303541c1d00b8007984844140315440c3c4410010f0a080407068002d0103058010783c1848011482c06d40341d5111140140302040b64000c0c144100250b4602240d04d8080b0240909080c0040704034003d00007640c0f0100043c0f20305019a02da0040c4296295546c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 428841978 1250 428840728 428840747
    0x4350708010507090509010b0a03090c15020706030e0d020618070305061906050d030c03030c030b130f0e0102040b07110301092a050f06091917031b0114040609020406050607030210051501 82
    0x442c10b0215940c5491301d0071341c4280c135153700003102481804007040c20040c0e0000f000d20840b02e4a8800700703c1d00c0c01d1144656181d00c8100380d4000903030b10103800302d5060020310b0040780d20b034a199030507038240944954403142400420f65840c0c1c03c29a8194040718044890711071000204811120408205842d940142407000700c1c0d0702c0a82455a19042403140134080d070021034030f190004000081c2c0f006040e802c10014000381d100d452702e4625042d1074003c4544c0520031503007076450500c0c100e424017050765140582e6415265600d901952109200c200040002c00101d90344028024205032484010320f4401c0e00034082d40c42144101c0c80002240708585034a0308840404005031405890503641f0400e841d5800b415500c51000c0c5030395040d5a0341c665030040060300840108050380360030a50800d20035808d85403420510400d0001030f1f0089000140c440c0c0c44564500c3c0f002e4000b04010381e80d440008c106030445001034016030082101d03a03d080b80c49105d081d610000404041d0340421202c40000c260303100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 428843228 1250 428841978 428841997
    0x23060c03090a0b01060804380a0e0307081801020604020f0f031c05040503061f2711090405130809120111040801091704350708010507090509010b 64
    0x4100307605020b110031254280c110a03103c41c196520b09000382005011a02501c400006900c2c10301100b046044008510300041e141a82a80000206060291002d801d4a2460780d0383c0c0440140b0000c1400907000e0700f80105a00e507210700070b01c408031642c00790702040e160454218004004c0143e40d0302c100e40c03294810680b04416150500c1d80800d00d004000e03c0c4120904808450900e10f841d8420000c00550344182c007175a80340d4882c5002c56140d940100c0d1200b0740c030b007213580c0244014941c0d003401d1148075094190001c1418a08582207046032202d40e421081c00000040138100e5042500405800800c101c004d2075860300b058070780e590316004d08400113101d40c000c82c2c824030994800750050714085c940301d8402c5540d96510b0303021600800c100202100c50b80c40600b03001d413034030030b14130159030407103ca16901c1070303040d90421040b0514000050340000d00d03111207041500c003080208495000340c81184000207440c18131035000340048460340d01040c030481c292001440034010072421703a0b0b800e20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 428844478 1250 428843228 428843251
    0x905010f09080a080c0a02220f0905060c1303080301060306090c050901140309100e03090f031506041d0307060605090105040b0a0b09010905031603060c030212060d05031e03042306 79
    0x403c241c041c581001048000a0b601031a2280020188101038100922058448d101000312090000d0090306807410908003415942020000682e565104001842c000c0103103d0340b40348a030749a070b030303040400d401c281c000c500002d58844080c000c1c44030a01c13503506805850b00709a41022221000200941d0358165006042403011000c103d190508020306040000c1c589800e000d09031a081803180d0780e070401d040361441250040c080c0c801710304020a01c0c10500f040d00301007c103199118010b01c009490383ea02014001301c0080d0001034158020f20180820310301c9094041512032030718080081204040e00150711851501080c44d102d80c3d610740d031150460700c40c01d1910327403500704030750050b0f030310314156842103406002d2202e818075000c01c2c40380e04000b500d10910341000a541c840200320101d00604941100c841102e901144007440c0400303454140ba40b10f2800c407440c051031010320000c00451841c0b5a0068100442480100300c0c1d9204000ca11800500c41a2244411640c000c0ea642c40e01800441900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 428845728 1250 428844478 428844487
    0x509040b061504080a050c10090f090c020309091608070504061d030f0114010e0f01050a0528061107090c080609070908030a0c0b0f06030c060f0d0c0905010f09080a08 73
    0x45400410f840040000724180c80141a103400c000391915509801d0b0b40c803030071401c000d0222103409800305000750b4000100e1107030300c5403c200310100240250f400440c20751005010040083c1ea071480050b10600100e5501c40380dc4010308005005030501801c19010302600f40400c2c8812071b070081d07000030741b11036003550407512040c0100424100f0620b802007610650178a25415402d0f01d10941e0241290212801c21006503111601c01c00000002c1c000c036a40b10f072200a08000c90700c0e03e46010000c01c40d6000b01c011031446203c0605440003001d030311040100344288075890b1164020b0160314000c0c1000c07801031185540b46500140001030003040ca40c420300303449012488030b81c812046040a0304120046a940f440344074070180060560107811101c100280c0000b03007010341a050f0340341c01b03581d000c1c0082001c00743d040704104681c0c00c056101074000c0c0c424003411450008038003500071190501c0e12148900380c20f0500041240c242c6051540911007900390401c0403040004087e0942070b00b08142039100c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 428846978 1250 428845728 428845759
    0x103080313140a080325050414040f050103050c03070b13170f060702030418090209071d13090605130512070606090c020601060914030c190b12100509040b06 69
    0x1400b100c040b01c2e0948111034094082041400040d03005421812000c240e00180c40c201120f142c00f040742c880700060007408104188148815101d40701c04001784003142c0010000b1707038101120001d80c401c0c0c61035840100b595001e0300b4103011076805040b02d4408249031034490b03443c10785142c9203407081100091040540047c000d0040c407400c40d0101650081d500325080902000350b584c0c100e406004038030403c03e543c954841c450784c0f0406486d20390160800780385640c2c0e240207407201101e004112501d12002135002d65155548050b61001611703291002400c660310f405e05000702c0e0f80050031081064003801000c030101d00000f4010302e400c0c1012400c00d9490205142c440081c0c5a10780c068444035003407041c1207a03060307004102503050380c03070680d11240c03c56610500c203d0035034400c0a101c0d0705500141010700380303400d060800030521201020814021a0703251040300c441d5002c00304198046200a040c441e010b4040c1040300c8c0208421a4503a8080c10503031244d00c02d000003e02058400e102d4401d00d07154 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 428848228 1250 428846978 428846993
    0x150c0f0405030a12021b0108241c0c1403100207060f06030f050606150d090204152c1501030b010c05010e0307021513051327050c0103050103080313 65
    0x18281c060300303644041d010380c074020410391100c90011002d03025030b011040c0d04003440009074500740740503510990284c9a184002e10050510010aa80514010080803041e200c0c20b08080d444900c1c0034244401086a0400c0c0300500d1540e0401110100c0c100105441594009003020b50420400801a80c40d00285000ca0040545460024000b4201a0004140702340c441c85502c40c03a00442c140c502507500c4a0400644029034030100c82c02c25000d01c010320400407158800030140348003600006011802c039410b460f80c2071540e40400491010711201010b110118280e220480001442090790390520b12800004101200300e202e0415a4817280c010140e8858840404080c1d0090020084400c1d114103036601e96003c4681640148804641040c0c07600740c030811a10340c0403807004810303401070900b81008803541c00c01144144c083d8031030703d0414081c0d40b801042d40e8607484805000910048034a8107504000740d01981905140c0781000420106207131404407076002e0180510106202c015140460 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 428849478 1250 428848228 428848237
    0x4050d0201110703150905060702060601022109030a0c15020c0102151302101211120f07020a1406100b1905090a263a09090f0c11150c0f 60
    0x8005c8034541441c0e000316445a885000464050300a80e030f540d0707503600310a0360b440200b40e07036150043e8415192250b207041d0b00d81c0b01c3c601410780c0d00221403800429800191400c4012a800e480300b40040c00f0800c041c0404c200651001740490000d0007001402c80d0010751a000302c02040c0d0401e45400e000945400f180c0e00c04a030b042030380213001d031441e217030190130040c8500c2409281000c0c1600d042c00c4042c1c800114400c1d40c09641c485168071034a65627050070303110f0400014285030207602c14802c803000050701c02c0d040845124a2880148100d1400302001d9001490036840301d0145001009003201b518940c1020703402c0b000380b40c10142d070f40da1100070201c0d0030a0800c1d804915200e020a00e1910320f0b0091002c90b242c9a41d20404540301010f00300e40306545030f00c40380c5100b0074103e0303085400c2c43d0b00792402414900e40301080c1030034154aa41c2e260140c040d2038008000134030701a52000b1302c850302c541290064081c4625000105083c180d075007011164120080e01d03ea000c604081951400901c0b41401c68 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 428850728 1250 428849478 428849483
    0x80403030810081f05010501090f030f05030c1b180903030a09080906040603020405090a020c15131202031216020d030f06050613031707030f0c030905090907081204050d0201110703 79
    0x260405201c3c02c00d0248124140104d5040301410a400040c1c50343c4110303050015a011844034040307152555407141c1c61031304050b00454083c04244102c501c000e40501080b0040c19140096a0010429000700001c42d15903200d0440304c1401002804019030001003940c2c2d1029054800080d0714020741009400380c025481c0310b661002c40082e000c10307419450b40240c0200d810550308038020781c8880c8510016030290400700c0c0626400310803c0200a40c086a01a0700880111139864410090b6110780d03070303000b0440021601581c000509030310301e103c0d4000280d43c00072191a45103180d0541d082d00139100e91034070380742038101503c0720704240d618441a44490010840104127940c0d540c99000703800c43c00c004034402500c5043c001d840e0380465150000844101c0c55059032030340c0031070040520a84d00306a0380201542001107268000c651601c410241d940504520340090000503e04001c187c50841c03404420b060034201808100300d6a1503140b0902220b9509003002c003590301c00e60401038a400c0391a41701 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 428851978 1250 428850728 428850733
    0x120c0c08060c090405012103120f091103060603161401170108010b011407020a0512031c0f0f2705030c0a1208060910051002030f0f210408040303081008 67
    0x188900c0c2c4062000400c5a9a81a00c080c8800d84c0d83d1038076000d03003c151850888071804c8414103000000d224280d40b0b079106000d02d1000030b01613040310880f07044600d408402c544981001c0300900072460100300c3ca80d4082e000710020001216144042103007112503124040c0350004100d03041c10a680110800500400a54485000f1750381d6a89141d01800140d0b82c107a01040c902510291501c0c4210212060660081c0c01c00e20054070302000d0010542c0702c550410751600042c84449410801525143c00b00c1001c0b00000c01c1c010f030101c01d10401c9840c920039001003c0d00c0c1003a600c1e40c4180e048862043c032a011203170704036284440d040650451049602100c0c45000f00e030340d00c104100043c0d2042e1070100300e80d5644a456503c41e030030300c008048180c82c001d48800b040c2c1d02c1003000e441e051100207100d0026106407820702112464a0205804c00602881400c00200e292504070601c001c120325510709040041c20523060940360003105101781e00000d400c11161900003440450b00b11054001402810708 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 428853228 1250 428851978 428851981
    0x3091506130f05010e1e0726091b0307050a090b0109080a03120c05031519080a0305070203010b0a030f0f0204110409051504290d0b011509060c120c0c0806 68
    0x8400d0010a0240106038542084401080c02d100701d40c0070041ca0200c0da1b492000080c0c8801c41e00b900c0b0170708c80c07894088800103c140c40c1410848000e811a005800d020000e200311001d5202d41150711941c044801c1c080c0d80451410441c546e1240085411034003c04800a410400303c401214166216000b1040034402c82413070204156210b0121b816041e0f18609c10402d0000c5000c04885c2d074482502c10394962540581902a185004016540e01d000c0300c1b40d001d000d203035032003030020b00780608083e00b50701041021846900b50304084c0a243c85003601210288140c40c25950341650001c00d03e03101800c1814004815002c64646502c0714036001c82c0844801c3c0c94564a1798050098802103e610101c0c03039002030703021032509140c0910040b5041c000c1002120a0248000500e05558900c0240c5e0115035078400318045411680c5240c080e01c81203030000400ba02c2850007a02d56911a80400d040001181244012500e0408640c26280c0c8a2501881c003680a04145450300e145401ca0301c40c81c0a08070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 428854478 1250 428853228 428853251
    0x21020d0203010308041d010f030206130317070c090504050607110703020406171603120c060b100504031e0b06130e010f050105120c1e0102030f0c010915020309150613 73
    0x2800317801103035003030103000c0d01300080c17451100d005403001e1081c4414000410828030043c5480320181031410300c10204140b04590701d032501c074040320380c0b9800001d0f9203100003000d001780080440400058a0034041c1444182070959440d9941d000c0104640c0811600021410310034400b4004c18008640080050080c91b0311200440814103909111022510805828940f1240013040f01d00440341c00c00000c12403c900d1400030307140b512001d84111203959840c2c060740030650780c4070340d40384110059a403929126825032400d60030050038145a02901b0b44440c00c0c100002d403001c1c2807140d120005441e0000c1e8440e49950302e001401c0c0d1412540047c3d4207198400b5842511544194101c450803207880d214203018800326500d40101c0c080c10307030300191401020002009024044062044180b04807071605100d05c0c4d0071090b540210340c000e03039281d441d8115170040c0a4203490052410710f240104626605103404080d903105140114558074043c0b0100040c556600e5480c0600d40d0007002034280170420411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 428855728 1250 428854478 428854493
    0x61403040b3d061b020a03020f010c0506090a03020609030309060106030b0109050301051312050903060a1d0f060a0b040209010c1202160f0509010602010b0627040e01020d110a21020d02030103 84
    0x1400b81100168440800320120200200c590036145c3d00502580c07a1641107400740054030420085050500c48a06103140015201304461440b4103080c0014001c1c003001442c00a08103003000d05000081c0e4001d10a2001c1440c000c00c0301c1c1e0440303009003400540c0410100058803640c5996022992551a0004001c01c14401c110907030440b5205041803100414510b1090311a4001c1d10480c64050f0300c59800a8003204459102900d40000c0c80d11805d40e513a00603140300c0c54240210098601e68002c0ba0074480e001aa5000b00d010427101180c0030b50810038090300081800114500190085d00c0400c0a645002d00a000424080c05505000703554240c5038141c0681030509803240502071412040000760261040c801d00400d031000900c00362402106200c2d14880c10016840c540c00216003c00c4400296601e126002503410307007000145e164080c200c0c0e50760031070709041d000b4454458100608608150f03c56000802c0d510100300d40c603e1452071203c0c4a00030b02440d101c024040d0310003c000b20074080c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 428856978 1250 428855728 428855851
    0x902030108251202121207080c100501031a040c0f0b13120f0206030a0b13051e0601080a0f020705070f030c12082b060906061403040b 59
    0xb07101d0216545401c2625010342c41d81c0c40d220781441d804a01c0c40010041c40c08402180e14507840b103003110504800b112100c00d071039102c45004c603081d21002515002401d002c0c80510003210805204100c43d40c91034494070b0b061400b601500c0721504010000038108030020f0b24035805489414116082c03145c0b81c03080c175221030381b01c16030104181040c5c076130000384600301094840c842c0b984617140f040013007800ea0900507960005000c0211451305c900e40c0118a8454401318800d00f10000004a2503090141055902c0780c40501d0038000b5220140400045903000500d0300e030000c00704034002484000d81e00801000b4010008000d0080c0100c40c0d0000340c0c54040c0c44d911050720f0042c0e221565155546802c0c0e00440c146072030081c002d0605005405c1f40302d02c1d0b4410b0041500d0508031301c0010500140d465000c40e03e0b43c5e000340f222155604414007055521130148100c01e0240d5841503e5814141c690580c5048000c01e06030343c00c003500c0c0341c080e619481114034405e5035446461b001403c0c8108030001081c2c410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 428858228 1250 428856978 428857003
    0x30405151303030203040f080c03280b0a0203010e13030c0b0a09020a090f0b0a060233040b2502070e13020a0303110610180b0109080a05061602060714070c0902030108 73
    0x300071f240450441004900c0d003006010043c000d1079038056001140181c1d1000003c00741031400c10410500c007145d9040440d40c4104501100140d032036041c250280e0394444003030310b00f4840e6010340e180d0400194110344000e1765180c01040c3c0c05400d81c3c2e100d00907006080d4034a40250007102c009000182038215403c41c0509140092050002d00303004d41c1400403055251080c080103900603980d20048402e840071083da2a15820348441d07032000c1d0300d1008941410280c40441e00c1d240610204a000600f440200300c1c43c4240002c2c04544080401000790b41c2e00c86030003810017410110003c54640c1c44130181c240940395001e00300501c0d040d9a42806000983d002805072054020080080e07501401c8984510596400030540c17244584001480700081401c085024144640a0390204000340d0800138200400d12460052407240b400b0001103100741519081082954000c00a114100e030b0040045201c0144a14034503488040b00c2c1803030f04c401121a070020302c0284c030010000c202c02c00d02048417481940d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 428859478 1250 428858228 428858249
    0x3030a1404121218151a060418150b070c090b060409050613090311010e0312040615030501020d1e0501051c170313050c19060c0201120204062001020c03040515130303020304 76
    0x1902064200c010a144106c40d0b034460010071081c4822142d0b501c082281c02c04c04040000c4085078850f0302294180581c0090000360804a040710401c20302c00c02542c040c056005091060031090400701d5014000c0b4040c00030080c1c0c4800004580d81c49100e208030f070001e442c240030f2080c02450704001c2c000c8070107444da0f040d007035003403114182800038000f04031062680b21282110b1590384d00d80344ca100034002c0b414003000d102e071243e0000004c50800d00148c0309540394003070005186a030020426000e03104007607010820608100c0100082e0f0346412120384a200c80350b0440a0410541c030309030b1140301c420120b1243c91800881031040442d00d504048008510440460b54186c500504201c401c0e410002ca03240d1600e00d8200500005100c0e40054100c2c0d407040c14250107590f06100480b050780c005400103000901c00702c88110b900d8081d840d40303403c0d0601d81d42c000c40c03070301c240d14038081c0d2607206a00805004034445070301500342c55110760454640801c4405500301c403d459242c000e489900c03c0c4510001103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 428860728 1250 428859478 428859491
    0xd1e050405160302030d05071b03050304150309020f0d021c050d1202070b070e010e060d020901090f060206040b0415050702060103420608030c03030a140412121815 72
    0x481c41d1520b80c1940e40050007031101040e8000101d0b4260f100460407500e0700325554502041018001590018500c81c0002d1615103040c96004101800301600b11000c040c00e0041c03000250f11100303088a101c04058034024140710050010070300c03d8010403c61010380c400024400140500444d2081ca0f982090b40e44030800420b190406069000d085409040144180049a4414001d6610b9180100c06040100d01c560410001074081e411608500d42120780002d62485290b03440300440019145240404e41c0e01d90601c140296a641d006000500d85104030b0040340600486c2040d032190104644c10620080c90401c0d802034451100703210403941610b000400103005880c900c41c0c2c0070351000c0180000744550b12000300c1d075195604050540e4200340d41b807001040d42d0705d09000520015510301c00560ba40d0804030340c01012140e60050f00d842c410501c9040c0800902c1d801289030300e2269601e0710481d200500c018500c02081400d01007601c08085255035402c1141d9095601c00340c0800c1c1c403040011717 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 428861978 1250 428860728 428860753
    0x50105010e0103021305090120070b010509040c0303080603100c05130e06060a080c0c07030b04030e04050708060904021f0309110904110d050307062c0d05030a020d1e050405 76
    0x1c01030038003009601481882281030156030b140d02040c2c1c005d8010002107040d0400902d1020340404d61401071341000c0300020040180314064000780c0c014842640e45100500e0035441e1175940d4240e1b800300504009000001c680300d1340d01080f1120300608850703c1088203c0c07802d000541039501000d400c0344100549000080c0090001044621a07040a0311661403d41805c5049a10b039000400b10a0b1521051050300c4800d103081100c8000b0b14811710040c0c0542c1040c1c01c001d0800007404250034070582c2000308104425610008a031307004282581c2e50561510750b0310020358461a4544020000071401e00006c44095058018420fa5170040c4a030761034074550f1100740020342c201164090300240d0150252030765820000c0260104a00540c01c4d281400d086903120001c1d0f0303607403102c240c001c101503464031650010092145008542107200400c8500c01a18015040d030000500306001d05602148609200c0c03810340080c0d43c001a510088030b10202150070b1070009250948040d19030b403090b82c0c10300c0d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 428863228 1250 428861978 428861999
    0x90d17040f03112b060204030b0c031801020708040302040b011e020106260d0e121603060f0504020f22020409020a0e0303120f181005060405060301110405040905010e030f0705010501 80
    0x401484e951a10b04200040d00f608200300901c22501e084e402c00c4000041402442c0351805070110036001a071b00e0510040005c00b81e64111007400050344104000f50006800000b220304483c1d05980114007e51120010394408080000c000300c0f04020b0009050707110f50640c4850291807002015034480703114840e190758800d00950ba004031b40d038000b8800401c80390103184119041c200007000c134041c0c0300101101c2410b000c2521000341000c0c0307040e00140200050350041d4003601c5100c80e01000185040d40008107698483c060482c083c080d08046101e60408140a090145111007001d56031207a407a07844070000c1d8800c59100c400100341c402d4404003031402104a841c0001402c1780059540c4417060b446500d018050042c20307008140c07212112203400180268802c01285203000110340c40d18005000684200030405446645041d00d0b508003446860191810b441c016100007440c1c144a00c0c00380d0040915004c1c44040c0e100c0803410310030518204001305003240c8900001d019076640d4030101c22 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 428864478 1250 428863228 428863249
    0x703060e0f06010b030c16030503060a0909150905010209030106062d120b01020a0f03200d0903030c0c17060901110a121e050112050f03070503090d17040f0311 70
    0x64072070304030304010001c000c810f03c0034582220040d40035501d400c0650385d6401c031183d4421411008200301108008051900707802a500910404070148240801c0f030741c40c944030942e002411068075544a8030740e8280402581680c0718400042d000300109602c07a42c0c003900e1480d8180082128803010010040c450b044412541c80d5804181c0740c150202903808924005802010f11513811841482c9000d004101d01004524243c1d0080c1c07906a161103600c998250448241040d4000e00c2c0d100320495610300d40d000c0c601a0459400d40b5040d030708800207240c4080b61020a9200030904004803000e0002c0242c0404c07954010712107007008020079103c0c8280c0c04914002c80703580348013152014014a0481510750060007444001e40ca040d200484039070380d444200c40c0c0c04c0e000000280d07901c05988040040c200402c4a80191005c02036041034180c0d9219592441403110032401240005044420084104055088170140588481d180e903103420303486000c0440d911050b64003203e03520b01460750341884007812 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 428865728 1250 428864478 428864503
    0xc1e100b120a0308070c020307090204211106090406120b09060f0f070c140f06100b04150c08070f03020c040606110a0204021b0a05010204050103150b090f04020d05090703060e 77
    0x10807411002e070301c0c20f543e0318000401c2d18040c40340084941d00165420301ca520041d0003103075401a02c580c1000a030034000d201c028004200702400101003400706a800541c048455000ca608a80c2e410b44080404e000e00002e0f40b0a0000d0082200c0107001c00c890b44c01e40e140f0481043e0202c954955884c04003510100c01030f01c1181c0c2003071201020a9050303201c1c404508116024200b03400312400f00c118070300d00d00f070729075843c480360794111100744480d2511a5502c40c0091862080050a107400e024541140c145a01c1000e400c0c40f5025462504204d140c906a030314194120942e6000102a802c000e902d4000307035840ba80c443d6240007404a1543d010b810420001e0f400200100103690099003031000035484014030105001d18618184640c200c200400d491b442c0c458400580c4480c80c000002d000d4805040140c9444101303900300388010101c50041d2403180c007045413030b480f0b40a45500400d00912500c009c6404143c1003008000801500080300380c201c0744241c000b0000d1081d0302c0c48c900d49510f29802c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 428866978 1250 428865728 428865733
    0xc08060912071716050609480301180f0204180f060c181d090f0a06151a031b09032505191503110f0c1e100b12 49
    0x2203402090484054510714030040000d8100ca80c003078907418501002146c211285070306c4008210305640d2940240203020f00e07003101d843c201c0d8443c1c02d002c1040b07503681d201c05c000001c0030318191a00395030250068070b10300b208030340070310700bc0039103818455000d1340ea8000c01d902450900442c0340f041d4101c4802030326210b0f040f030100c0c840c02e0030780e6413640050000300a0810801200c030b501007900b507088000f010f009200c00800f00c140c5185500741c8270550700e0010448042500440b00c454180103000c14900e02c1076a00000008050081c0140241025225042185202d0010f40403110441c00c460055001d09403206418805a1041d03000c024188205407419405811401190300d6030760303d070000d01c2c62184810800326116512500424194800c0105900c1060004c82041084803640b005000d0fa0341011702d0180b1180c101c1084000c034900c1100c42601500341c001994165401050041d41c0a20400308a403004000d03400229503558120175001c01c040d5858022301c400c2a02e8003216004030068000007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 428868228 1250 428866978 428867003
    0x50a030b0d17070f0b0a1e060e040311030c061501021006060f031e0e0307150e03030601080a0e010518120423130e0105070e031519090c0806091207 65
    0xd007614140c015040c03c9400346403922403507000170075030280c4070b2240c00b0b4000c00103115180c25800401c00366860300003207070842c0307060414000c1d40341d84000180c1c8a60141400c1010100000c0160728510039899940b00300c2c0502814400044030403200380458510076400c440351584c40d80301440840b0310700c1c440d02d030201310000c0c0a00040f0340070b41c0140c403011421b40001c1c00d01d01c00c00c000f801e0a640c5002c000f01426000040c04004102c40f01a0400129200610810280d0003d0b60641d03624440500494180200540041c48410a64000d0f0104806040c020302c2141848054001c010000040d1401903010b403103e4640c6491109003a5070844142000c0c2e01044040c00a076aa120a00c82283c1c6400c002c000c00d140714070210900911041c0d045000002481e450404401014030b6202400ca6120303800402094404205021085070031002e0440c1541e90034101c401e41000400281400a0401c000146d0020f80c1c2800803038020f00c1582d03028251074400d02030a00714103080c410b00600904001401c203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 428869478 1250 428868228 428868263
    0xb12010c1d0301020c03040315110c0d082e0905090f0a14070b03070c02180603060411031c17060402030c0703080c04030f080712081021060c050a030b0d 67
    0x220107035403808028000514000c000740c2d905045a10641042c1c1c1e000217000c94181c010780c82c0d03203e903d0a41a04666071820250304401d620f40740c20402090307078104000da4020a50b1841c1c10305080c20303c580e088000f281c00d020815144003001185100d0202410b280500241e4680390102d9000c41000c1004090300d80d1000315a01d414020201400040051250304008110f0300040d1000314000c0a003512005002c07103813031041164a0303d4020000c50600d0002e4144000703a2800511107410a42c0600001552580e08003ca0f1a0080d840d22003240d040c0d4407a001c2880d1500303d00180d800740310801a4142d00d542c1d10741408260710064410881c100d034100481c3e00824030804000f500701e83d10700c203000c2c41d0680d40e48440713112107100c0c502503421060004581042240b1400c10b078854400600301185d00b40707810071010104086ea84550034040d2403154800e04403100032a09680b48a500003820030903508032807002007183e00b0a186d54004a441e1002310a4507140400840103420f610107146509051480d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 428870728 1250 428869478 428869517
    0xb0a0c030f1d15130f09060602070501051c09060234021008071803081206030105040809041a131401060e061b0102070f0503030a060501111209120601090b12010c 71
    0x10314440c01450000c0c130030301c1d80c2c1d09210200390000b4080f0748000f018140c05c010712441243c016901020035503015003030030051643c1020a540d500c030450200031402107100800d01c0d0190140d040f00400365840001c1c807051250014024000c0ca01001c2481c461001c01c4110000001055000c082d42c0104048a000d0100740b10b400c03129801039581c685005034403030041d400003641320a0340040b02c1802003c181d4581039050002c0079540f01004900034082d600b00390300c0d134046610403485201d00540e194017a400030501210a0300b100f4510203402200d01c584581c210380028065210070074506101c403800010250b110310034050641000409003844c04c1d0002c805140b4280f4039000220340b070354091010902090301104403201c074900900c0907554a19105400408440040d000541800644c1c80300003004c1c10002182400e4514494100f49e568040c54005807680c00f00c00050803441c031070b180000c120400e01d900704010841003903550084843e0400d868a00341c907208014400000c8a0062206030f80c4941d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 428871978 1250 428870728 428870749
    0x10f09020a0903061505041a01350c0405210309010318050d210c0507120c150f0b0d150507050c07031a0a020906040312090b0a0c030f1d 60
    0x58100318000030382e641d4407501a80c401d1219174004200000c03040000b401c190194104140c1c4102007030000701c201100103040900c454400c22000c04e94081d078016a590704800080341c191b04080f11b56070600d841052440c2540c09400303440e01404c90903203800c4e00340300b0904c0340c4110302d10300c00061030401c030b2070500441c002c1041b8942880c0d00f108001004020440502000c1ca110503a9650880880b501400040c244840c805c143c18100385400d140540c0103a00c5401d46003455809600300d00203c00e101000c5800301c504280141140038a03038003030301405005604c58440100079003014809064003a04001922035407441c0508040d000148040500380564007007644400d580c03d01c1401c0a0548022520b00a141d400c11a5070303000207a420940c2895100380c9540c0003001c076905518200d804008244030f03015503c401441c15800b41c12298455008ad10204013a107606031059845104142c2c009181c864848400d4000c01d00620002010902c580c10091401e191040c5d2044c10410803028403101106 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 428873228 1250 428871978 428871997
    0x20411070503030411150a0c03080f060117090304080610031a1005060705010e010c050a030b0904050307080a030e0d081e04020f130b1002010b03070e070e060307033b0303010f0902 79
    0x2511070352200c0c03070713040c84020b0005140d048c0d81c2c2c0ca01055451501910054020700b9440c40c0b0147c2404000d0181e0f072000301d8581c004c0fa40c5030403800540360600510300d14015904645400e0149030100124030100158003011640129100502540c0c0d8542050b1004019603034000140e04442050289003000c000419006100c0c10000448220300045642128034418103000004c0001a4808007030750316000c0c00329881b6040b0380f0900c890500d660365623034030311503c00d00818000002c80c030007410b64026448008130003046410740340b0054200300d0042000b142100c80101034980000001421901c0080b2113101d1503011303090607065000c550030070601c80c528000320100251607503000840e80d1a031032013500c02180d060b0000315a68800c1d004060070040160070036080b03014464200050540c0c000c400c0441c140090781c1960340d98031401021400346c00142031002901030402e0f50000c074140c000c138101c2e0945841182d01001684c520400030740b2440280f007000d03031584200b00244a006080d9000302603144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 428874478 1250 428873228 428873239
    0x3130201021006180b0102120d180803091e0109050c040218040213050a240810030b040b070e0301111905041d012103020a0b070908010f09020411070503030411 70
    0xc0101c92540c151031407034201001c21002c002042890800320302607442010001d0010f4140d64070710a05000541c0603610031401090b4580ac003421030040c0a0420750380b4a0b4004070802d031b0f2441c01882140c0e540ca01560800c1002d01722102081c1040303010722a0100490b4058094110b45451034104000f0350445594a050019184002c0f11702d580c6510050010500f0a2071050310640340108200700320740f05501c000040b003159401490200014005115401c0540c1445202c9459103e21b108100525400c0201000c00c00c41c14001401408801346100e14190364603019801072a60515080c3c0b500400c95140c285400e00c0000c030141400c4200c4d59000c2c04503e41a420565030b5819055011098120030f200300c1803120040c0140d542da01c100c14180f104c9229a40d59814036554000d6031191944000340c0000c40e070b07d0100c1c500e544542d804800814042000780a148601015580188480c0d00220b01c44d0740740c0f42c001488000054241e551464122000e1801c44e0742c0ca071141003040103520f04903903101c2c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 428875728 1250 428874478 428874493
    0x90503010204060c0c0801020708070b040816060506190602030d0506030a0606030f1b0f050103020a0210050711061006051603020307080406030203061c0c06030209030316050d0815060313020102 85
    0x1a202440a0801842503a41d0380301383c0420382c141600c070000a03802c844090f900400c01040450030150031103845590086400d4807950f100d08011400d400340d0f4107120410034250703140700284902a040f2a000c1c410486000c4000f80440110b20b1520f070240c414407000d42c0013031204205002a6a1080c0c3e0701c810044e003510003810701d558a040c2114110b40049840b0340060559005200c200f84c4c0c0c02d04000b11200040b001c0509151000e801070890f40b0410f4109900002e0150303045102380121448803540000900c41414219400791419680c1402d9800301e101d08800038100013090203034402260303500e8446900d0587d04100d42c040c8442100300c290154481003001c2400100020001c000801007503900680302c1c1044010030042d0742940c0e814950741116005030300c01048000105000320b8003c0d081c0140d80342c4d50f03180400d04602444402030180c1101d200510305000c408645841440307102d0303032802181c0d9601060307000c410300d0f9131702810340281040c00001d103071280188120911600500458018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 428876978 1250 428875728 428875739
    0x10c06060b0703030518010203130602031e18100b0a1707030c1508150f060d111207020d02031305060304150507030912170f1e0906040b151f09 63
    0x4562220b1001c50002e5551710412030386108031228180203100c01ea0095155080070420280b03e04400e52018140300c0e40040030840400c084500c954091303552445c01c600c41c1ca4441942c220454100e10301c08007600030540424111b0107139109006804034000d05802d844c6080c50614a2340581000d0b480c41e551040d0f0798044041004000d04000420070303c0940d42025014030401088000041c24045120344607c40e451140d94540e01c0c451044001503990329101c0911094001c05051081c1c042c181140002403855844280300259074030070800b507000c49409188032541281c2c0c0c0c1c804c082122081006103e01071205140c440d000b50b0b0001d0240c14248200c01924844d05e044503401e441410200303a49410348420883c8200015000e015241071020400d080741c1c0b0780c00180e0300d004100c0d101407203d1100240101030760201c03014942900c003049129502c2c104441955416080d18240c54020030400003070039000802000c01c000410103480800102000040c141107001c1030b900070028000303d907501003070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 428878228 1250 428876978 428876999
    0xf0901150c0812090d050313030e0f060c030304020a06110a060906110307030b1003110a081003061e060e070507060203060a03060e07031719050d02070203150a050601090311010c0606 80
    0x7462120707003481c000307242840340f503c4d8a80400394500c1c2d401e200040c020055030009031f08100c01026018180f2004800c00c1200140e1804031200940f42c0c48080899060380022000010314402d6209540404425848810a84010039182150f01c01684101a000c00046130354010440c40e0b40b003aa4041204003590b030a401d81908101c92404c0002e5039505510001d242c541001040408541020010768594290030041d0740f003250f0506040c046240b002c102070100c411170b020025600138000b044005000141581e00300c1c8640b00d882e0149003010030120700c0144207210f46009040c0c5444403450002c41b41d0300c00c80a900007c280c5a0720080c00d00000010400d0381c060b02d00d4082c0c40e00043d090842c154604175440c400f03180794044082400340404104030456155600c4445c550341411900c0b0a2480303c14070280c86069002900b6014007081251a030782400581402242e0861041c42150b4a18004541000ca5440302031700702c00300d42002081c99405102c0c11103101d4000d040c040382482d1a61140700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 428879478 1250 428878228 428878237
    0x5210433050103110102151012020307031a0609100f050904030c060f1b0503040c05060f0409020c010614011b03030209060c01060312090e010f051017070c060501050f0901150c08 78
    0x1140b113502c81c0142903456a05110f01d00d0b2104081c141011581002d4a0a5844104502546210349080b075142c000755a010441000110b610803d8130000c034800c0b21420709042800c2e00e05501500c4e40c0c6011880c013661100c1e208040d40c588044941d409468182000403600c4003030001d809026a20500c1804610540114a240008a02d02145180000c1c05402100303002250740e034100715051080c400000ca6031441e080450313070708854164031645400b5800109118551001d0380b614400902c25080d070106402c800100e401d6400c03481100c06050303005548042c0d43c100c14020304200301d0310705400a40603034083c103600b200140840c1d0408144a08603070840f079003500b0a4408403800f40b07003402041d0348560400e010b420442d500842a5145ca035042503088080e0142500c202c0315441041a0213115180001e030b256001c100c82111810013000280410040c072030141c8001c0d00b0071002051504010030413205800020f0701c0840b00b030b0304c0c1ca0a004c448040100030070040002485203030300840c02d484080c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 428880728 1250 428879478 428879483
    0x1b030a0305040309060e091819050d200618030c030f04170102210603030909040b090706081b180312040806150d020f04110a05210433050103 62
    0x14141014103025044c41c545501c020b04100c0a0006420152600c005454004d800c214580d4408001d0b10189401c1c51822412100100c0d0b003d000001844800a00c2102c0546141c490000c1c48084120880d00e0030400c0302898090341c805c2c0d02082d80e420851a05803006072030b0301d00b034074101460a14030504550055201440100000c1418880b00740c20540c48000c18007490008c41c034140c00722490348000c0030700d281a1140b02c5829400118640c40500444202c0030004047d110680340c1803401c01080700c400e8030f0200c1e491003039034004074205005810040c0214101d80084c50a03881e6039a0b08030241d0b01003482c503580c1c0c0c0e0090416465645041000c0d05090b04241400c42d00c81e070a09008500c0c2940041c0406800800568454130b286c4a4104400c070450b01a60031003d46550103000c03c0182c000f250b0016451a400501034904681c428050460780500906510004d00c15185070061800286d9011302242e0041490000c03100e001442800c22000700403000300c02c2d826880f03980d421500c007640203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 428881978 1250 428880728 428880731
    0x6010804240b0918060705031e01032d030818100515030f011815090209250908030d021c091208090a0f0b060604030506040f02010905010f05030703021b030a03 70
    0x5140c0703403400681c3da0364444460000c0f0a10555040296a983c0101030003203000c1c0322000021900c0c48e5424642d0400740301c64000940034031b503540c0c5001034103048500c40c5130b407160308402d500c3c070340017940c0c0d407034240c1340f00d8159423981e04a89034603981c400c1e42d103c00070104015200b8174155090034049801100e00c2845a8071901143c2800c1209141c00d000b48024600307945e902d0010624455541c440d06810003d820000d1505c0420121404100528080c80b001e035000144a0401403c0100e20a0600082d8031a803580b45000388181c1c01525408564000c0c2e280a820901c1014040d10595002d04a4500c6020b601c079110140c0c1c20b6420112982e03802c0075105040303c0340300300e680139070041075140e04809100000e00d01e1503101e8545140f103141d04100200400045400716000d41d4440b001c3d100a1500601a61114105842d24444550030800200d0109014800001d00340d80a400306000c1c4540706e07194240b45941d000c01c00c5009500c041d0070141c141412186490340c0c1e80c4200090701c7c01d207005840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 428883228 1250 428881978 428881991
    0x102060108031306120e0609010b19030f06020a0225060206010608151e151c0603050d1218080d0b04060503030d110436090206030601080424 62
    0x908000058204031100c1e0300030803565002050700400c00044410a19214030741080c0b514158004d8030f01800ba00d43e85125086c14841003200c194800000031108548845036619482000e40e0701031083e00c0003502e605842d40d4000085034550300140041c0c031503807040c4c800d040c21100008409104200c1005a80d03240c00318248000398040081c94054001820710b42c080303182041508031015014041c09000e005c143c007801940b0110f4070100300b187e0b100148034000400b2050103500e440c5e000018540d191813001c2018206000c1c0c90700c60b01e01a29081030250840701c0d089001902e1fa460203080250050760b5030346c20070741c0c13000110b088589220300c0307021119a120300001184068850840940e480755142400800580d83c001003294960f80e48a200484c6c02d50194074003803000c0c0101c0d03200f00900075605045508042070b00f801c04501c500c0c040940044501b0b0143d540d0101c40d07540354002e422110803c007148580d80603584095002e84500ea01c00100034503100700d8004000e0b6100d000c045140c4900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 428884478 1250 428883228 428883241
    0x30c0c0209040f290708010f0311010c06020c010e0c04020c06061e041107050d021f0e1006060e0a1509170309130f110c030307050906040306060b0901200a0312020c060f 74
    0x11010303005480d0b894100c6c2154145481c0401c008038510008000b001420800052a4051110a120a90810f00031520307484201e0800740a0003030307882583c1c0c46005100031f03240b10b4941442500c1803405104010f103030540c2c4070802d0107010509907003444d0381c0d0b88902600054590300c0e4001e449081c540d060031242c95044070b1416518105a4072240720640d007082010300c3c0f04d0448041840025840b1000214400c24034030511418039040c03844120071641004008501d0580114900c3d560300c400341e61000b134486d500c43c290044160044012030000d811040704021a0036a603000180002ca07100680c0e01c0c3c841c006001411100800105e807007081d482d04081050300c4001e1040c40000c00d40a400e99261550f2000881d1310f900c8000e007440c05110001c100500c40d0385891041d5409582d00c01801c11031240c50f00c020a40680240007003900107440342c4c030304000f238101d0071104506e140c4a050042551a1155a0a542c0001103032030340b406c003035400d100001010204004050064a014803032036103904025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 428885728 1250 428884478 428884553
    0x12051605090f0606030604060306061403060c1c0c03060b070c05031b01050316020708060903030405120f090d1b09091101020c0306070f09090c1e030c0c0209040f 71
    0x55105520520002040040c0d00081082c1e0560041c400c890140c0d4076611140020020020741c1c0001e08214504000840d03600000d04800081c02421411540d99503a410f00c2035005110b0440c8040c2c0c2c4045038040d4400c0e019140e0000c0740300d03285501780070444548401c5220215041601e0079108a50801010000ba080c1030000c62000c2c0072035040041554211800030704144070190843c1490480c5032054900c0da0310900408000c0c011445c281da09a0030082e40c0103640382c200380d0b4141c1c0c01303000f11010000d0b84030701f960455491002e54107015042560507010454041c004002c02e9420411000706410b50480b4410101c02030101c0f804000303802895400e008800586480555040d0361004483c612255400542d05038882c50328548145200000316040b10340c004160300141003241419801340b09035402840f8007080021403403001d010a1141d60045060700c0c00b04258002081c0584502e4000d030a0982071290b00a000d0007907051110f00c1541c40d060030800182112448400c9a0300600700322041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 428886978 1250 428885728 428885773
    0x70804120203040510050c030c0114090610051003021e0a030c090816030f030c0602070804030303050601170711030c1207030807030603050607120f050718050d080a03151205 76
    0x200e2000b54101030409001c900c02d003048203031400c00d018000ca500103e44030300f0400c03242e03040d440c0e800070f00c151040a40340d805000c030140c503140307902d001d1400054003044080c8404011548020010050308174074a0081d0700a42c0a101c16480d20f1038081d120101c081c402c080100b8240318103540000d0b060001107401410048907402088013034000100308a0540c003071504100c19242c00500740f40322400145802e075207800d00b407003000305907a0003c11244180210030b0050400c59010f41c8085c0f00315074418004480d42890010790501c0440601c01007804507110b00c1c069004001141d04072440d000c2502c9903d0700d40401401c0b10404203000041c82030803d94040601500701e48507040a208450660b5506a211480200003c0c20003888044401036401d240d0807403850036902c440100170904003003900410040d0350044a20001c485050000340608080021003900c540007401c0a0401f028031500b1400b40040e2020701070986404c3c9804149020381402c00200c0c6440b98004140100016102c100324914 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 428888228 1250 428886978 428887013
    0xb06030d020726150109050609150d08092704061820130f0b04110f03010e0705120108031909061e1808060933060117070804 55
    0x80b00d03200b00003081d01050107034002c50100c00c0c82840e482c1540d5000b49000203900024001c800c20000003e062020360b80045e0085d031041c0c0b030300700183e40d4941000b200540f0400781183c000b40b08600520100d1113340c00b0703203414200108000f155100070041d80d00b0b21441c00300078041071007890043c0001c000d00c921a00c1d5014000c3d0a1101c507100c015107807180000c290342c041090386502d20300207403866a5007610700201d0305030702c8104010b20403021815034000c2c041095014050b0b86030a802110b50300c0400305660008540041e16403950b801c109407005030350800361210090000030312417000f0100a21158a000e4603440d0015500c810100007900024104980110280102c00c241441a583c1c000c0e0360710768403440e0189914a40c0c2d0080800c0701c1d9403070b0314461940c02c802110404a8810b82c04a0003074064003c0400700c501e0260a91000318142ca092020700301d22402801111080c5009103c60f10741c040d005040840c04581304568078104017004494a13070018486008020030000e103400e03140f640c000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 428889478 1250 428888228 428888233
    0x20d050117070603050702120a0e0316050a0504110904020c0f010b0105040b030a020c0703150e12030606121302060a031b0c0507050d0c1d061503150409031107030b06030d02 76
    0x1d144101c1070703440d03201c28001c1c1c10405840c0c50024440a00810011340200014103203e903440d000b07204010081200d40c11454868020b015018694005000448040d01c43c000c10503d0345a10340010840104801082a58040001d0028541d1640c071031001c0c1031340c400d1700f1002d0001c000000c100a030071240d0600c1c44505101090105029400700e030300c1030320360186034600f0042ea00c41e0030b03820b0b061502c00c003507000821850403011600e1510f03513660007120900c0042c90484261a100ea4038400e01800110f4809810050522841006411005203a034202c8107161001d071410281c0d40110704a43c1c400a60f490200e070b15510b140d017070741204c00d80341031a6580624100c0c19200d181d84c0c545498250303034030a10b40300d440e98401e0340c014004001e481c20028003104054461b142c059036a464549101150484c0c031030315461148141040040b41268400c401f408400410000d000040000a06000b18250300300224488804c2007442c0400004018602581a100c051300d054001c00d4900300541454400311b4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 428890728 1250 428889478 428889509
    0xc08070f170c0c011d03060106050a17040f32160608270c190501020609031c0c0527031903020a021c12050d0b09010e040321060801020d0501 62
    0x1c10b0042488400d01100b441c00c200004030f03441010311001c080685144c0e06004000000410b20780003001880c885080d52a19a070522034259203150014007210301404142d0300850800008010242c0d0501d0354030034800032116000c200c0c10b10780008444c1e8228a1080c0e000c403502c910003100001540c402030640e89049c01d013501d130010b0060310700c4104c0c450001107002c80d80f00c420740c000401c0c00410b605400141015003480540c00f0701345403400c19441000d001d4000c0e00c0208220150100843d507103601800111058004014058001482e5540c040c02c1040028400400c01c41038a0f20305400014112480b52600c0520340105070405210410490600b50750440e42c0740069000314065880d6a0102d484450a40c00130040c0c2502413004c09004152003041c006444034150484058100d0f80b403294410401c40d1100310a1040108081c003549040301a00310000340024030802c03004494441c110312001010010784039540940321070b82c200d5480e0344d4021907800d10b100590704c1254014003146950048a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 428891978 1250 428890728 428890747
    0x4090f29041203060b1c15090221010506031b090303040506120402040b010e0f0d0f08120910020301030308060f040902090c0a1202070b0f090304051c060f0c1e0c08070f17 75
    0x40c02d07040746c08110b00d54960500c00e0101e441048810011300542806554840074003c0e09800d112000040d000c41903a11070001c0780600b400c2055900c120b00e900b0030041c01c0c9800005070342460b007005901940c18842080042419242c070380140ca0500c0a50508041321b0600f407040006807800c408055041050983c004025542d1344901322061880540b1110b000392820b007000c11b1080c51280700549100800624520300f29007124002c2c4c844c2c21a20151100d04c00c040040000fa440700303100140c00600c8000c045580da1400303107528200500000c10001c1d411100d035000c125020f030100c9045c1202c680c04103422800c65003000d0f00c602603000e0b8402c21407410040c2d583e00c1c00f400002422440303160a2210000d50032003002c0040703078041d050003031010038408520b050207083c0703114006080b140c071400d0955504180714140261140180142c0394080c40d8501d4a60502640101c040d010040042e40c500c10000b082c100d030010084580151680314081640d030030800c0d040300c68401c0c2410010001c0140303410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 428893228 1250 428891978 428892007
    0x14030a08040506070512040e0f070c020901170a05010c0305090c010306150f090b0c0a020f0603061f0203041d0901110a080606031008011e050604090f29041203060b 72
    0x82da90222100b5460700000d00f88541b034078001340c1c81c1c80721070000007034003196600800c0380e1135100d0018040c5540d1281e9039450704450041180d0030080d0000b050780300611030310706640001408100c09a0444840d624540c40c4c6c1800c0d01c0c0003186180200360f440c800d11205480070b200035200081c0c00e080a0100903d4680c91019102e544408682089007005500600d2881013444e20020810340c490340e600c40030011250398840c011500c0482c8501c05501200f000781c02e00100750f9101d0700c0300411312449513122030240c8010b04046108034046002c00c00020036070f0440300307078a1a408000c032100c9121614104030301d14215a00d01e01505c6000b107060003c02052544031002a50040e030030307501c49840b500c60144619a19040741c0103004603508011a28540781c01d004000c2d440c1e032442a04c28407003070b15480d0600046450018010b0311310b5800d41002e80205014800c514803140c00e1031500c941c5688026034801d00c01b0380030b80d001c403103010702c0a1900c5c590035070500510004d407104910003850006c000701c4120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 428894478 1250 428893228 428893237
    0xc0b090a030b070e1002010c1209080307030f02130f080c3c0a18050f060d060506061306111002030f040318030c060c02040e030a0f05030916060914030a08 68
    0x2c203246460400143c1d6103102d0030803c4001007000c0c2c20700d80b45072105d080c040d001e0320790780000d00c0004060602e12612049a03001d407a40051300300c1031880ca0760b1240e400c1100a0814035100c40f8009408005a200170407030446108002c00707056840360803990600b45004d007800000103441d4464032180d0100007858030070703244410354948203901200c00c42c01c5100800c00642c0d942400780794005039440b40000c60349003045100802c000c01d5031042090f641c55a860ba8011401602c0590b044184c51400500140c099400300760401002000707681401040100018010300760303045000010801e2030425138850003000f4031504020301100c25420b61401c0d215042040030001c0c0090100708070701e084213503003c0ca01e4034a400516005118101d825490b98000f83c00820340c5003040303004170314044102c07541d000e010041c5c8007144900e1b500d0a0206210034402c0b0b0380e581010780106e4403802241c44a180044180c45044010001c64490074030341407400040440a42316004818001d0b084a9a40c1d0001603070107003101d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 428895728 1250 428894478 428894483
    0x17090a0e1521010f0e100e060a0213051f200c010507020d05010e1f15090b0604080607083310120f060509010602031312060e0d0c0c0b090a03 62
    0xa40b4900795061a2410000c1111000c2c00354079058034006981059044203884400308002c40703a44454181004e0100c0d6540030b0000c1e85034001ca0b000c1602044250020311012191b050b80160640d1a080007560111085800c002e0b450104011a40415040b54180d0300720200c2002d41408518a403044503141c09418402c5810070000003200021591100c84109280c2d0708440204081d003140601d541e030b118594019155400170420064002c0c0e1114000c0d50300091a00c1e4240450916115504010300f240d01e0303406174003440900c00481c8038602088180d01c200c02507524171280b403c0202d101110107510920042d8641304000c0f404e210307007449134101151201705607400384101000782401c850b04e50035815002500b600f0050380d40782e40c0070a82c0100055420031610344210b640d961200303903501c2c4140104000c0d07605500781c0411900d20035146041a0303d010b1200401c1c1540030804403414081202d4240010483c040480d400f4010600072040103040520318403441d110601d40064075129652000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 428896978 1250 428895728 428895739
    0x120809040b011209050a031e0203040509100b0706140c0f030f0606041205030304050d020724050913050a11040501020a0204051816080114040c0303080402010c17090a0e15 75
    0x1c090169100e06000203078018040c200f000501038038903080b9160035490074180d00060115508000c0728084d40007555003550160004d5182625207002e00003035030401405a030800d1081d00e0300142060f10f030070041c800248600400107240c4020b044844060030003400a800e0010240715040400503800100c0382c0000240c3c0803c0320554415001400d1480f0715040481d0384209448200d0030407000001450040748a28199803c40c0c91108040343e03504440c0c032a0055000b0080c0147c442c0031842a80e902c0c039501c4c2791501c42d21340b00c00c03800403038846d080803036081035896500c00400403c444a8481c170804500607024071071a151501c00000c0d80c860802074080d101e595140080741c010348440d40207003100385e008015103802c0f107114040f00d266491144602141c0754242410709102d045001c8225100d00c0d480140d40f00036078110340741246c0c80b02d0010003ca0511100300c0141021841c0888144200300040201c1a40d074080d10044c0071038681d065000d40002050103091000042d018103812400205c10740f41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 428898228 1250 428896978 428896991
    0x70c060507060e120d05060609030703121413090c0e0906040b06210601020f060403050a120b0301150510020a20011407060b04050c0306090a020a05040f091512080904 73
    0x5002004100c40c03d24009075100d1507000b41660800300024003204008101c0400c03540c0c2d5038409000341482400256945504070400510010706524003022540b00e062030940711418000c000400c040d0b200081601c0e21075020302c000c00a4020500a060080d0075a00e4840035070358840000c91a44800076100e42d10898550384901215250001a40c4071203034010114050030001070020360045109555141c01809001100d02041c02d00103080e9000e10307415034400e8544101c5500c2120300040e0702a015501d103483d03001c00320403540c09014824140024041d856104c600d88000c20a08070f10349400b14003907402003485000850045540752211003001101110b40d800030f600100e46082005250310210180441c4607400d01c4419403100c1411034081d40d040023380c0790502442c02c18002201c4070365004020f00e0020340c1c0b02c4c84603005000c0492603800c0280c1400c1e1644408090355041c3c0e008441740c01da83d8030504403800640c0714844018001d01d00341107400c4c2010f07141c0740c84511581d00c1c2c0c203010f981c4908 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 428899478 1250 428898228 428898233
    0xc020d051606050a020304060e072106060e100f090c051b011506050c010525030f1508150a18080705070306020c031803010519110c060c130902070c060507 68
    0x8011007a201e6204800704070300d2405031240c40c002e4100f0b48050300c10a190012074154080d001490302c0c00e6071290205031900ca030000103642204003004074101c40305521400005295a0390480041c003401440d0902d942040c1044001d842d45a07950b4010b0710030314280460040c00e903400004031814004003c60112002400700181409000140d040d046440c01008000940541c00400b03440014010002408951504401c02c08840240d410300a1001d0150300c0411000b03010b03034040c4c0328600c250700010030b464034000140d1603042c4c541e034818002600300440d2003410140c440211648810300480400c035001201c0c641c842d20000e00d84005100000000794141400820080500290b41c4080c00f5590703002e10b0282c9070344907001000c007114544040c2010b000d25103010700400d88213820f4100c0b24602c110b60905980054601230380306d12446542040310443d01a0280040d82c0f02e0810806070303da45055032108540b251200768054404980b046c822140000d25000400003281c03850b1400c152900d10a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 428900728 1250 428899478 428899507
    0x90d030804050a121e030203010605090d0c09050112050610030f02060d020d020a0302280806210303040f02010807020f0703112101150b030f0109020f210610030c020d05 74
    0x601500a85482c0c1c4c40d425080c2c0d2040380c03085407000c03610346003001c044111001c0d82640020b00076140800c4003806455414101100705d8050580947c0340030046030f40d1900110b089130801e821000e080382c0049041c50074000104203094218840b0940c042d102444c5032034000f050164050020b11502001401c80801e00951f01500d5a101001500310355540022102400a41c40300c030101c5a241c0d940300b404407820034201249841007640d5201e15609594160411854150b181c000012051071400b14140d80304040014512480c4986400118480c06000140820400601070400c65000c40c107140d1500f031010440d2411070b98410000c802845503c0001104059049196290b00460310640c0980000540190859070b6403403140030b2800d40c4810070814644401c440d00004a80e1050042040c9001c5a0082c6001d00c0741e403601c01e00300308100081c2940c540a0a45485a0000c10814000181b030800701843d4860390b40c0c01c04010650125030b000c0d4581001d07105e544148800450510b1b85000c88 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 428901978 1250 428900728 428900743
    0x50d020a060333030605070329060d0f0207050105060909030703080a09080307090e06100e06250b041a04020d0f05120d050a0e0316080a050f0d02070611090d03080405 73
    0x100c2403c8030009543c10228100d20080d8403055400310b090030003040159000e44602d510640d0410031100d58200e031031200010b00c000d2042d503070303800440800c482540c1010510958a9900c1d0084000d43d503610306041c980d00756000600083e2203000080117114001d0300020488801a5240c1406051666104003400c0104080500070b04400400401c0040a503845201e0384242c50b01e5a9098413603858610a00034070340302501020000c00c0d40355030708400610740b04015041c4259000412410040315404400720b04920307120440e0041c0703502c0d050000304400d010f83c41c85a001c2c0600100c280e032801ea00003411502e0013800250942801c50b5002c800d00c101805a120000c0038024110794036911805084000c0004070342500a5610f00348001180c2ca20200032104a400c034000a5028058240c43d0140c80764400c090f05000c0c4a810400c041c2400b00307040241c44a0803e02100503201d0b03680e42003030021303034a600b10348140e00306040007407180b00d58890510508083d00752030002c4166a4070320386280380001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 428903228 1250 428901978 428902031
    0xb09071706060405100f2312150f100b03070c230f0309150f04091508060f040b0a1a09010e040309090603050c060708070c0b0a09050d020a0603 63
    0xe40d5031040020000016140c0e001c0d001c00ea60403c00356548000180031050700307020704000307a40502d1080020006002d03000c0102521a0351008166007000e00181038a100c240d41c620203600070800c0703100818140504c0a5102c2caa28054040724980000b40448000a6006805441c64040301003014940f01d050428a00d43d800b405041480c041031940c62860303404040ca05605124071081a41c1e9040040309a0f02d03002400303800c80420417043c4040390040d400c1421201040f400c2032000185480b0300340180c030449448091494a01400d1a008504043e001407542002c00064010700002800c2c25a4080e030040841100081500c0c030040b00182d1600031718007a0754420b00020000c1901c8000c81c198034081d030304c03a07252211115921140c200a6507418800034105400c050113070102810a00001d10a03644540303c0781e07181c5030b610f5070b501600038102d400083d610100072645110b45a085186000039001c12140031701c0814455000074000310f070600880007010303103800180c04071220341690200e40c6203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 428904478 1250 428903228 428903249
    0x3021b101101020705010c0503010801270b04141218010305070905010e0a0504090606060201050601020d02371202060604060b04091518020306011d1f090810020403020a0b0405010c0b0907 82
    0x4042d1f0042c2181c100707010301a00c41d481c1460072480c0507154446980042500b040c007101c290807648502060b02c0700180161813403000c13062000304115040c03000001020854080135110201c000c0045003506030351201a050620744000d00c00c525411104c01c07001c650003440e1103020020004042801e07070f040d50b4801c1d60060b0500841d00204240ca40000042d90010f40c02000b43c0d0f6121001240d07035118007106e41015070024020b0900b41030041c4030388600f1407401c41172004403142c2400c039103074100c81c01a800d980e600759400c00e41e01c005505002c080e401c1841110103100396070a244040e01031f0700c00c620811600665441c103c07103c001040101100600700c14110114461048400314041e41c811030f641400600142c80100c10600d01e0750b4056030400000d4080280d031885101040c04005c2d44440207800c0c40110b15000601040070000c21600052541c0701588580c41c500c140180c1c06215004085088410320040c8100e984c000d10303c0400c140c101c9112035140e00c804074982d050407195003100b040d01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 428905728 1250 428904478 428904491
    0x10b060c0102071401051015020c0d060e06101d090c0a06021005070323090a14281106071406042009091c021005040f03021b10110102070501 62
    0x8a00c10341c041d1141501603045a012002101c88031401c0300c508480c00130351929590005c0c0141c41c221340100000c03054a004070703025100d0f81000101d1142c1c8110080765004e0302c0340341040105400b0321800e90044500a04200c1d0349041c21000115156042580d50092500300006446104d0420548403032140190070300c3c5103103071240c10007521690604000c556803400d01e400700d0100340c031074400c401c529100d004070420941c3c88121080d202880c00f80c1401c1541c400d40000d04042184400741c4003001c4030103c010701001711245000c2030108a1540000e14a1440010b583c01040580044000c2d41070308548540d9100c2d024a072416030000100403400d130a1040b60200400c03c18100c1140b04103448803e035040e020f400ca50200401f6000803a45515280c102d03d64070f02540765410011586048a80181c52501c540021590101d800466040d6180c1c403a49040c0028150140484601c8102d00d925070013508601e00e020400c3ca0350403030143c40800005650014074280c003941610071881c0d000d0000c0c04070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 428906978 1250 428905728 428905747
    0x5160c15080f070801120201030207050c09090303010501110f060708060312040b09121f110705030706090611040f053705010f020c030a0b040c0b1603080a05060102031b010b06 77
    0x107080101d60b92107034411882c0c003140d0780300d005a044604984001c464030744003c02c5507004402942080b5000c8500344140482480d1560710b503640c43d81706001da24004c1d5203a603d80400100581c500076407204c80303a00b007085008003142d004a20f044c4c0c0903849040000d0140c2319407000c41d180205070032158000040c007040c08900ea00d00940200381040301210795140d14420301000303507102c00d03003160b1084055402469040e50840360342c01c03040624440c1c0c98540d0a01086840300b6086a000c0301c02121181c1ea20302d194030070464640706102140300c00703515090525040034441e80c41060940181882481500a100403034140c014040d11b0f62100491034601d070400050209816032400d008003400725420346008e40b007141c1300181140c1c520701c000300181341540090f1107170400b88001030400d0b654040c40b1070340480c100210400410895440d401384440c0100d140c1001404020054003450045003840306120450b0380c0041a00c1005009084402d401c805001c1078a00400342c004500d60031a8010908104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 428908228 1250 428906978 428906987
    0x20307140a0201021314030d030b011107030f1a0613051f0312020f0f1b061b030a0e0d03050d232a0429070f0c05030c1005160c15 57
    0xc800550040c0c2c6004103441b214201c50700c03d40c0c03900858169202da04448103d03031280d041140c0791072040c1001c3c160104c10411883c2428155041500c12007628904902044414888581d94891070300ca45600740c20f00a0025101d400001500c0d601c3c1a25080410121124490810f005407400c8504404650f40e80c40d14141c03c0131198086009802070a9038140322010100f4a07a82290212f40906020700c00c0c1546c600f0080700b01d42e09590002d00070701003c07401d0034403c864035011100000c001c3d5100e05049a000f071405010212a07401070240702c64410001e6040070645000d035103134050219803003941403c0340f000203120011402c0c480d82020107010410308203544201000800a24415200d2407100303001c0d4492181d841004070003120b40c040500400c180038188000840c42110395854044242c4881c03065040002058441c0b511001041003546000c00580c0041642910b1150599900d00805001d078050541100c4001d802c080151041107030b0982d03000c000d03104015400c601e50003030080082 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 428909478 1250 428908228 428908237
    0x71e0e191d0601022509020a08010e090307020303070303110c2d03130302010804141015061803030e03070b03040605040b061519090806160909020405010909020307140a020102 77
    0x4102140e18420040c003040c1c00300655201d050182c0003020aa880c00719001d410303103840c0110b040c901114090101e0018030714001000014203c0da03031220741d54141081c4a54801001c0c09510096104114540050f10040141c0e0b10040d00360400051420081c0341c0c0139198070400000028500031100c0703990380707540d610715051021028001041501e100c0c3c80d040340da0320311400152034041e8962010401c010f6103c7e9100d25407007032040214a55030f46030080050724000709060b01da50010b8840801c411b03800f800000131030041001d46451b2041c00000d40d453301c44406580400760030031014001d48801c50314104180300003048044d2085a49243c1810550300401041e5030071a0303440003c401103401c51400b80c80650001d001c07103000d14070308144240b05040150002521100b4401040340001e641c0206001207442480710100606958020b114001e29070040e030303001130b0070042c414030017401182d03408815017041d42e524000061341c94031303104003e0782d2030640b02210b05181440056484046a4190040d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 428910728 1250 428909478 428909489
    0x9050d020601050406050d0b06030111030414060610050d0b120f070e0108010203070503010605031e01080607080c1602040f060305160906080a030f03090609020a17060f071e0e19 78
    0x100d5a82e42c030341d01000145c07072080c840d940d070010b800b4480368003294201c4500f075040743c0000d0001440e80b0460700000ca040d041100d0544400700c5003800048014028883c00d60300c00c00480d5100182c0c00e5625005c1d0035401000c14080c01c5551f03440460800d91180c010074841c03120104111400018282c601c1d40d603401d8140a050054844440002460f82050003601c3c000c1043c2d40703490742981e0030b0100031030b016003000302240c105c41080d0200145201c400080c0c54040c000d200c018100a00e4001e80c041e080038005443c1c551440d80800090110400c10354245c0d903860380c11980400c2082c0202580d00141000703803c0501107015440d00885403481a52015003290ba00f0941400315a03030781d55582d512501180400340104010444400d600b505c203502010120740304900010b917901c201e8010820f200c023150052036000030b92032601d900d0f05400b0003455501c07a00c42c40038080d40c1c0c0340c458002412180d11180c006c01e004c0510382100040ca01501c1c1280c4111005085035204101c040f074940040065840391 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 428911978 1250 428910728 428910733
    0x204080c12030708030c0d02030a140f06100f030e0f070314120403020103050604022b060806220c120804030201030e0a03140904020d05040614090a0f032109050d02 72
    0x20800c50706164801001410801c0061410451541c8030700d030070b0b079100800881034820104040c1c130700301c0828405140100d41c0c200b80000c1c04035058054450000000c0d14845c40741480a0810a1aa0312040c0115445070140303040c01078000801c4041d400f5150903d01c80030300c1e000d00e9024400c080710020b035040459000c0c1c01407205c429140b4180e5610340744000ca444000090030882803016500980003150030946c00b801c01858481e80310b8804030003030003021140300c03041c0c0b0561719500343d03682c18015a005051224090300042c00c0c00c0040c05540222034030500a50320300080302d14281300640518400810b981c0889507100c2c0658548001075a22a0000300d0201e454201a1150100001400b19403c2c2d03144e1030b1a1404411803000d01d10a420102c3d40b942d00503002c000d030b888040d51500a49004610422001c211402d40c1c84209042a200070b03c141125802520602c0100d120ba2061410f400c1d01410095940340010080d1822001d4010005800505041c0e09200f0820300081c0304850000a034207 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 428913228 1250 428911978 428911993
    0x3010305060412050703050909130605131704050a210507171501150e150d0b0901060e13020904060312050712020105130611070f0b0a0e01290a080709020408 69
    0x410f0b6445d020342c0e10301900144080c0b2000465080050b10a038100c41c0b492008445042c09a03075010581c4c4c400c880e481008440903103118100120f00c50348803040690112103a06140c100004030b080342a480c41185056201d805074508d211114081040309a908082911149600d8240c21340f000e24483c04a040b40d441200d0070902c0341714003240780605035851030344000d40d401c6402c2021203025040c24039007a8484d09045c0c40c400201909030081c0209a0009800306a44076501c04022041c24164041028410407140580c907aa69040c49031064680c0d00000613100c007400030110340181910b0300010014a408152620b620b604100500310b036a101c3d00102150794401e0204900366001610140401c88160b000c0c5000a6040c0d088050340d01e92001c1014180a42c4d40c171000020740c00d03020f090391030080071001d003c441281402a900580c510034003c0c0856100702c44009814280310030344c2c82240c01e0f020490400ca55402c80107400400824040310207440d00c078650400290b11502c030707070407443c4102036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 428914478 1250 428913228 428913263
    0x130b190504050f010819060816091a0d060207050d0503160e030d0f110d0905120d08040f1a040303020a0906021501140111010c03021305010c02030705011b050102030103050604 77
    0x10200c50558801800e007000c503c0107070006540c550340107851012095a03003851075100f09107510420300140418002402500742420740305801003e140c000317807066802c007040d40710403030360000704044000c0c801d03100c6c400d007100b8909090009024200005081c0c2c01240610030240e980030010354001c40048075400c95a80708030805484810b0600c0340c0d030360960400140c07111541e01070001550480c3c600d0410384101011410200d05280c204190700e400700e14408020f1105042c2140719540b410f003041c4c010000340640f41005040341100400081c05078040e041607008004d41c0c0661424446414042005503081902d000313030217908080100c4c40041e90307040300090107510010f41c601c0c0c052880092400c00d40d0070119076a01b21000b0310040303814042a0100404218401d108001140c1600d540050300c5042014030034410018a6029604110030800e2080250b500400e601c0100c40342424402c405803000c040d164030b00c031002a0040c00a51010000000384000410640c1c49079109440503950b154854 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 428915728 1250 428914478 428914487
    0x8010801020a0903060c09090510030308011e05041a0306040f141b06071106070b0109060909120807201b01181a3604110f0f130b19 58
    0x1c07582c440011a005000c02c040385130b0303500100c0303800c03103500d0941011500e0700b0a5005072007041c2c0d0350070804d4030399260800038198000c14050140c4903070348004080803c2080d0020800344540107040c42159960403411942c40708000c881d420342000f40a88056242900b00703813003610706a8006680c00302c0c4d1086440302c0c5100100d0849554220501c0d201c050300411014000c03035402001045032a00f0341c031440c803031443d501e14000e040028400c4041c1a0558141300500c020355049a000c0c1503114146002000028426010780e69031040c203182240517550b8000007180d180303000410550b41d000c9031202c0104a03640100d071040c001a20a005070880741110300045a4000b5200032106c480c2e084110240b100e070704890505050210124211400e104850701c2031850034506008c0514150f003801c5c28125411030062085900d500308650801041007083c090b411940700b0b81f218a01d03040c100151114001403920252042c2d12004608a010740b030315200030400d40d50000303500220b010400200c645445124 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 428916978 1250 428915728 428915737
    0xc070c050f1309110a0b0307030e0c010c033603020405100323070e0c03180a02031e010906230c041d07020316060c200d0c0804080610060801080102 65
    0x42c20344110541e55202880050980c100121062035400c81e104200ea5074007034800c80980781c0d81e2221030341c0c2e013081e0b040139007120820f940d454942d4100a1001005a0300800626103450305400c1018032415149801040c03518884180c41001c00000c6413140004140b0741c461040d2813094034200000c0d1962020b000c010b282610006107001d200303108407510490b505442c0352105e0084411640451b403206418040c1d01c10449038a02c001001004101d800404a02541e840c2940300c40038001180040d00070a480d01103100c504c285562008442c560408070035804603400c4c1c6e80091007045034030000b400d04804013201880c4203440c0030010011800030088402110100e490885941807008204e40c410503001c07000030040c00950209001d02e001d0000300c0018030002d540300d61030009030180e0088002e0400000e4007000c900222300c10048180301c3d200028400e4010354036007040c4800d00268500341009100319000703104107005130710a10011030210301140d000d5070219280c40802ea030701e4030300300303800c0b0301a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 428918228 1250 428916978 428917009
    0x1e0303040314070b03010306050f0a181412040b0c060601022a04180c0906060c0b01120804081b0a06030c050a0e0f1210050f010e150a09050c070c05 65
    0x10030001080042d03844015000100803503000ea500700baa444003031000d2034000f68401d944058640040002481066080070340c000466081001246559420041c002c40c0c41343d0000c09102440b0804010548100650610011107211190740d9503280c001d400c03150b40080407421614402c05c00814015030010842a1a0aa000c100c1d08060502c070070050b00b009401003015500b10f03542d0200501040011140b44070100d0084050000e290315003600d81e0121a403070f0b40148108032502683d8000240c24000040c11584039201840d00c4041d94104041c542c8100e910844891203401c1e152a214a1004508014068201c5580b1103050780e6150907011340e03010500c00c0000036030400044504034041e02c80b2124054002c2e002c04091004000443c0300340e031803107070301f260070b5403201c5c3d01c2580c00720380d0b8001c0c0c0e640308070b158081c5401940340002c002e288a80107400b154241c2d00c03100241d009902e8a00201e401801c4505c130502242c1032840380c03400a83d1020800b80c4607159003000101e07007410b14034103401d282030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 428919478 1250 428918228 428918233
    0xa021e060609042d030f08012c06030114040b01030c08030702060a080a1508010902030106050a1406070303090203100914070b0406121b05090901080609070533091e03 73
    0x994642c0e030070110407503000078802070519009134000c060001038580e0035298841e031144003010001040107080203c05074050000c0d106041902680c55034000780c20348042440c5500320a0a444080001e070141c0040c0982000c0180342c04201b02c00e100c00c00000d5812079026408244078181c03900c4640352a03200b02e410294000a08212080c00c4510403450982e0040651400017041102c454003601c42c0c00413580030100700d039184e41c0c0680640c0380a00c208401001c01311000100302e490081034101a40c6200c3d0028802c1801182e4503040c58029003250385201d03401015141105504181440103128456040e10b40c800a201041610440001e405e42510350083d0000c0c02c10745000000c131a4020809045012a500d501c900c4401c680804601e00d905011902c80c582c5030861081030000700d020507804152564040011f000c9007540208000081c2c407015913036a0314814200d048104005241d00f5041c0c10260920001c0c07102d0340c100d0f0060003000d00708982030701e2100c14150324050314940070b031754940d4142c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 428920728 1250 428919478 428919481
    0x150e06040809270a0c082a0f0c070303090503060f160504090e010501050913030905060a0915030e0c032a0a0803031005031203010e06041d030a021e060609 68
    0x41c42580140200103001840090810207074500070841419041040e04091211824070001d00300740d02400d5800320051a00151a160440c52000d00741d801c08442c10b520032a4042e041103c0c1c00d90310854089244907004181e4413075826403c0c46d500d001911065001591804e03004c00d00c0e141c0800c17200d0059041103004916500c8484100c40080061380300e60050110401c400120500a03020b041d088104150000409604d01020700c18800300040040310b816500380800c100182c1c0040520007030310001c0d54841e440e500150f105a03803039121034004403840c40c130030400c000e9680e81c103801245400095100b030f680c10010107010700d5030300c0c0d0300c0c1c0c904024141d007910794031200b525460440b80c4c10800e009003000700705a51a103400c1e0542d401500e07400e86a43d01750a007481a0f00b01001908074002c08420400c2c995031600b4580b21a2141c0900074912036516200d08040300c03490320740042200440070301a260303200e048200180d5201e01060205165125002d182602c2e44408264988141c001400c007400a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 428921978 1250 428920728 428920733
    0x31204050a0906031a18120301150207060c14070504020f0702010f031a0105030a150602061006080103030e01050c01091b0306150302060412050a051203010603150b1b01060504050403050304150e0604 87
    0x85190042806c83ca40b038101300c254980503410000c00345ca544e00c0604407503595052404501401c0c440c22010010740d07010050410042e0352282d88041e44039000240c1c00c90a0308080440d03402c00400350b1045902034000325488205210307280003000e0315031003600c50019000c10701301d050b419907000717081c4880038030000e0902c4200f0794001d0000b568030207201e042c001880c00e40c4500400c140102a000754006034003007002c22140700302d640140d80150495003054040b030740c5582e9006200d0200224101d0400c100815000903036102508103403000c0d0f80c401e0704440405a0230381001c0120701580b10a0300d05900b0503c0014a138443d9010aa0a0300d030058507403031515040c41445200c00031528401c4641d4400c4c0150030000ca2020f220740c060305000d81c00481d17a00d514120004017511400160568000401c070810081c0503942b00403a106e10301504034818100c03441d24004d5005102c80d41c426a04181000100810542d1140046104510078200c6410006000e4094800c440000000300765561044010802 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 428923228 1250 428921978 428922023
    0x515030309040f06050a03121101021c11071203050601030b180109021c02040f061d030d110102040801020415020d08010e04150e0a030201052a160809031204050a090603 74
    0x10820f90080c00811080d175680d0202c1e8292809174815503200e113001300d00225681d400807503203c5404900c5c00940c281921454a010410310340c1c20708040e01647d0b0400307a0081d9078800140e0b061180c015003084034200c1100d1000d0090179080701e11700d0000c0e1428415020600c0c0030b110000c4110781038009041241e00707000a00000750b024640103190485142100f40c11088140014006010782c0641e00c15a1807505038082c0041d000c2d140007510307451440700c0c0300301561030010300368003400100e246c006942040590381038024440c5410208007940001030114170403007110001d80401c03407641e00b02c400c885024041202d54030028000e111151a040d0042008282d00860711a903c070742c40031000581d0705a000e80350340b80220b42c400031005030f5151000c0007403000c2029144071441d2500188000f4280151451030703078a1042e0140c140b82c1d03484c4109110280540482a5800c50a0145c2124a48502280150400c2d00144078031031050124240c0400e0041c8035019800490358426100d440d0414503041600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 428924478 1250 428923228 428923241
    0x108100303140c0a29011703031314030706200a1407030201271a060612040f050601030503040905090c0a0909020415270b0d1509080a090603051503030904 68
    0x656128030b030a54400314117904035590510801c101c0403544e08111040010b03c42d03505038808160b280d888000c40007811000700899500040c1c0d503407002480d4000d803a00f50305000301e44411204511001c2010360802c010385e8480141c2820340326150150ac10409449009441001c020310000340400d940d258242e00000d002d480c150380700340004640840103ca000d030320342289520700c0c0e4071410a110f500050080b0038a44007141c0c03d058480344c40f0f6142000c080744545c071450011101e0300403410002000d111a8140d030711020340d8800c041d01c50a5030740742080ca40d00d40041c0902c070ba0f6545810081350304204005400100c5000c040c0c00580f4045c0b8094414000700340da03102c266003041d01c40c454010740004880b400d201811070030301c50904008903444054150760f00100350034400c6181c00c803030b05070030b580e50034010b244194420307803c082002000d4181c001030000060010041040800c82d21400e81e0010003250507190795950409c6107031b452801c03d03803000d454015580c1d010341003084000f8481c2065081030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 428925728 1250 428924478 428924497
    0x5070209091c05091903050304061803020a0e160201050403020d0e040f0f051503070b070228091a190603020c0309090103050f07050105042106090209070e010810030314 74
    0x4450300d04500103039030b42079000c002a5100280c800030f022078680ca0f02010059101d142560241011400c51b510a95248154040c11051040c0d046d074081203c451401407001440e03002c1e200d1000c0903034464440e03900d60b10544124030f404c0b108000d6000107070320510800b807050303425500a2044d020184016038103500c501243c40d4019480d40b10b03001d1344410304d00a150358145203e000082c140351072400d403640c0c0304000c00a648a504912010001c625000c41903076403442c0c045504030b00c403007001510703c96500224480064012101200000c0d81100c81d444074044c1e81030389490543c002114004c1002e00300910609400c104c1203072405210079840796024040307081240d0101d034500190b00000a4801314260310443e10382c0c4c04807041c060360380410710101004220a0801d40d00702810304c0d0700a8140007018010780884404003910005029458010b180c880b60090300040d05800c1190000b0b110300c0c10340c0032350360120b100c1d2404079002060310756031a01204d03050f9031031a0404409001c1000d255000083c0b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 428926978 1250 428925728 428925733
    0x4020607060507081f03080d0515120307171606092a03020307060f0f0c0302010f14060406050307050f0402130f0e04350c120c100f0c0507020909 64
    0x403000040ca0391207100c0c015429610b0b040c0030f03450700b101000110410000b841c84c004081030f90402c0081c92850503a5080c0708480c8000ca100da44000c580c401d034500c400805030f480f0100040b01d4120321030100c000d0000e24040e109143c130a0080e8411441e261181d9080c00d1114458003034003001156181d80800e800c07511039403101002800b84172407650044100350a030403100e00038040400440c034042055400034002c0b81402548001c4141000c0c0c01030703504050709010301c255903054100b0103100394003820b01480d0740c02d0108050010051903403118078048510340c4c040e9203000c90104280c074000524004031400100200d1448a004050001a4012464445e190003884402140c54036078000c07800060005960b001405103030a05005640800003000050120021400c0c01d803000344003a50529071241900e80990b8803603140200d1031825103e01401074a081c004100d100c003a11001ca40894250390825040c824920b0300c41680040310190080c5402107002080500d0060514442c169070000e001402e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 428928228 1250 428926978 428926987
    0x1b02010c050d0207050909010605011707020726100b400519050c03010501050f0904090804080f0c090402091003060e0d20071403010906020429071208040206 69
    0x301c0c507260118600c1a200503030840039041c801c0303081c46000d0075480140c5000070b2014078076007130000c1c3c00b80041e00e007042c0e140d601036800583c0c1b46000b000f24100804028030b40300035501c0002c49160b401c1251180d45c5105010b031310090380c15620540600f062106008150050341002d17800b60741480c8409035001c4400d600e90f02c0d034810a100710403591445490030464042511f2404803442401610905958480c5910b4441070000a038440000e6905540080c00c240740d80e1822084030100c180030700d541650b8003604000740e00f410004290042c3c0200c5400c0012103290006409019071604d0250b20150740100303200c000280513251109882e900069610354400c0307403e031261a0b00064612043c1000380c10742c4003820350800b4984c001803140e074007d0303e080009103090403800039a403101140d21030124058565845250030780c0c4c080d440348a410741d1000e03085580703903942c820071440c1d0304005c0d5951450820603503110403094500700c112100c0d25800400b1000c5120082004d4541090150040e0f800c400c0901 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 428929478 1250 428928228 428928233
    0x15120c0306040f060e0303252a060507110a1e120305041e02091317130801150620100e06090d1b0b130b01030c0905060f011b02010c 58
    0xc0020b01880c00b030070344404a80c5041c00d265082c1e031a10740d0101c1465004100300031106260090710820142c104071103000d002c1100b1000c8031400d401030441c0400004160000d504c8844500f010313888140300303000501c00d590303d0100503520b140300c000700c1d044c2c5600710250b8400014071030030980c0719050b00c45910555540c0c490300e464040315100e0240c1c2c800f0a039100244802e00180c0001d15690440903900c81187d0005580400c0324100003a0000c101901160000c1040142c0202440400c2c60f40c40c002c1500d0710103800003204100307464454105107502c0e184525500714103040b40042610095103840000d140c212100100b07110790000d5046e0b50307005c0c1c4980300a280c10f0600400d00e40400b248010080c0d402c00034426420145032600c1a414428104600855168000307122540140c01200b18901e569840b02d80d07110303003a41410700414100341d0600201c20030541c0101e00050b90728085080141d555808140007003c8640040326011801c1444010154000420560307001c0c1c1c8103141c1211400c4903503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 428930728 1250 428929478 428929483
    0x3010f0501080307050c0402041d06030f03220914040210030f05010303090311010807091a160f0314270f031002030919080a03111201060207030b010b0315120c03 71
    0x380c00503180ba81001940d981480300c104182c01c18540115011494180307405030b0b4a9840c1100032007000e141885400047d001ea50500038001c140100c5010f80f9034038564a44900d01300c9580c8040540b0146007030324081090080e80c440d0000300900003400c0181c60301d40380c00f0000b0b26100c442030f0754101521855000c51040c1c060080600940c402d0312441041800e5140c1f0b080d155803d00d031042d040090307a00c1009003031a4040305103011076510104200003619034030815283d6210300e80f400030400320320894501c00c0140e100c0700114181e000e50b0f00c1c803440c0790031006140114814042d09401c0710701c0c03080b00300982d503013010901c0442e41801450741d08840500000709041118110714000c1c00c0e071b03011003000080581805803d40008068420707000c02c08403540c0342003540c02181640410180c1d5016042008807000741250400300d51508101429030b500c00d00207503074001900048074040b404500005940714103d081e00e00a18800c0c0e0040c1e000c0520005010002c400c102d10000980f103030b42030308042910103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 428931978 1250 428930728 428930731
    0xf0c1814030601120c0f0e0615090109060f1b110316030807030e040608061812071e0609080d0204050310051501110705060f0909010f05090708130c080109030e030102090a031103010f05 81
    0x4043c6a10301038542030040209100d194148000c1c0580e0420ac0104140ea100b100d1005941da5424a44214501103208883d40607080d0348504000f1b1508441d1014002290841100d900003242110f15007101c3d04041c0c60075483d64880107160081c107004110010313000b141816240000540005110f690344c4494628011040d10841c004203251003140131901c00c1401928001d8200c443c3e6286000d2695990280400e0000340101040d403805a0b81c0081041e5500f203815400d0b000070b007180c3c541c4a060140300095201e03124040c883e1151410209641650340100781c4202e50200380c0c8840071810800540e1803c0b2490b01140c3c031800b40980100300755031250b0140404284e010302c040d84905000c0c00744002000103070482001c2e00c4803150100060790f11303603c401798800b5552419484a8842986000c454000c0410003400901000c0000c61441015440200264065912191031010342c00a150803407050201c100c3c1c00140560081c80410040c4a0320b40411201900002c2d124650312803242c203e410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 428933228 1250 428931978 428931989
    0x30f18040c08060405090c0d03141306020f0105060d030813050a021002100e0f0a08280e0102010c080f01050616060e0a030908030a021f0f0c1814030601120c0f 70
    0x82d00c109028440c24580b28203580070302a5030040038500a1000001e4030958050320084c20040044a40800b10780d008064622425980c0100641d064030b03508041d40790321800b84420219880e00d00010070519001d00500781098058990510300d8039001041c1c211442c04d1002542c291003500d1140005880d240502141c03a9080d6015007216146921074509039004035080b442140d000c150003030380340c0b0808911804240e610000156507456081400944510111030314039201702d8070110300c8c5c60170303402000d0428410307001d900030801d079008003070305036100f55040e91400000c0014030014025400c00f0340051040c0d8612055080c0ca03003000e03556202c140d4a000d00302e1035154020650301c604058001d541c003006032051001540c202406404000e41e80c0c0802c0d15000c50880080840080c41c602c2640401d002102000091088500c0413202600303d41000c1d60354a0049600d50001940c0d50f0241c441c40d40b1800014041c10181c0d10b000107080a514a01d18203548003550030000150146442c45003000401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 428934478 1250 428933228 428933237
    0x4150e010518040213180606090302030c21100504031205101707030b040f0302060609040809101709010b01020607020c18040804270c1b0b09011b120b0102010608030f18040c 76
    0x10b04d601c071b42559550750141c0184030300b0076801d00c0140d402140030b12144209031000000500881c0c000c0b8003daa1b8040d1068481c003507407400214550241c1c202070310a501903110782920310401c08003e4100c0c4c03005c6881c00c0003000c402078148801b4020700c04408101e41ca02e002ca41000b62242c450740c10003441034804a400003818200c500c100b60701401030079440081201d00014924058898000382c0c03048081d40341c4504c5940703442d540c10a000b000d162140e00846d42411550340b0300301c48001e00900903003000c54054814100000d96041c400140ca6003a50b102400d1600850300e0b4841582100703101810407100480248408241d140c4030842444d401d00c2c0c0b44e6100c0d0054082000280100c6020440c95802c00030b014040c01072f00b4070761120706080d0961040b4510420b50b142c0780c5240c0107062000101c25001d150186060500d42c0c40000d840da008041c0b0f504002e120385013801642254424070446111350020702c0000b180080381800340161640380c042c070b00d441c08920f50004045941c0d0310070050104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 428935728 1250 428934478 428934509
    0xc040b0a020106051c03080406020702060d020a0c062a030f110a02060f010b07020604060f0e040509010b01120606020606060a170106080a0f05061f0e0405010b04150e010518040213 79
    0x515107081c41c541d02c45c1c0b41c42c005d0746141100d51001040181c00501c046d2009030001880c0c0119100e51041341d4402c1e050031320440d100c440298000f8841800c0391400e4442a0030030084400100c2c02400750003080c086180ca14001c20114442600608140440780007910740c1e41d0300340c3c12102d001100603c00741100c0d034044c1003d85044080c85503043c4041c1c1200c0820b0005004e1381006807561030803034041e1042404c10ba00201c900080803150810400c0601e500282810140b001d20b01054004010002d000d880340140c140d940074800342140c1d07003446040c00590014000c5401400c1500c010032940c4103034501000364000115040b00c1d0410282d00007400a038414080000030600b5201d0031001c1d17000b12a05010b541001070010f880a4030f14411907010001e009405400380380100c481302e02c0700e0000307402400150303503501140d212600240302e4801ca15100540c204882d40c86141d0683c62018140c5440d030900000b0300750490380c6450b42c0110343d0010350800840320760794400540d50000b010409190000c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 428936978 1250 428935728 428935739
    0x5030406110708070b2715041706090703060b120109111507030c0b0c131404110a09030803072001050a0c030207050c0f0a0f090b0a0f030f0b0c040b0a020106 69
    0x81c10043c0d4401000c81c1c1142200f4850034000c2802c8840601c50f00b840c51608660094042d00b03480340b0441348581c0f00c400c003455502414a000007400407070346002040c1030100d9084002680340d1100b224614015002100300b4070001e0300ca54050140303e0000f402c05000b850900b034100b400c5903001101500d4290100d4240042807410f5a201c0c41001094200c89041c081c50755009400b01c03441c0c007401810742c80203800085203003824074251285050b601d951600c0e0595181101c081603070840d2210360003981021012541c0c0300358030040313814055459403540c602e94030703503141d8040d103400142c280810060140c004142d096540b144804180004800001c2c1030300f0300c0100300f0112040b440b120f50034140103110040100c0c0001c03440448410081d00d4400d4603a9507180080c05c924540e8021190350604400040b0350300801d2707401241e41c110305035800d10019071100350409100400d07100042140b010410060f0004092002840d0403140c40000c076401c1a0300c454075221507810450000005030741d80c0c00104113 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 428938228 1250 428936978 428936983
    0x213090c051905181f0807180b040e130b0c09032b0e0103061d060411030424051501050901090306051302040f18030f11030304060501080d0809100e07030503040611 72
    0x803444c42120b0b019020b0383c0344025500300540c03111402c0c0c180064400000c0c0441d010740c0e800c1d4001d041c0d184000c1401c94903900103401e5600f0074041c65000400240c0041d8080714801d10503015603800c5070b1b11901070364641204480360b502041e4002e8245c000d03200300540113502c00b0542c40ca0f800c3c0d59512501c2c540391010004090580c9040710a04060030504200000e00f5a03d1103c80e4010580a1944d200e0b40d80501040207042000c8207841d00e41070001c104070038403148001d8a200640c40804850a185012465809541041e610500328140440d069401c3d50b00030801424907140c1030401e298940e03a01e40b101d001302d0300304880b940d801b0100005101c1c110b1805200350712449501070010400c20740c00c192607a003a1a1110001400e120f10655400700c0c0501402424055171600400c072a035a180c11b01d40f40700030f0f02003072042c000b8503c5805c0c0d041424034060048642318110150082541c1b425054030900906000d507441c2101d401403000100c045070b4280004c201501c5942c4031604000000c094052 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 428939478 1250 428938228 428938267
    0xb0406020d020a031e090e01080102190e010815012318011e0e031516171b0904090606030615080a030e0d14060a091101030213090c051905 61
    0x781190001c4807403400003a0040d070286061201d0319903440c0c0d402030607241510302c1d2515412455881c10b002000140700081500101a4503003812400a18502440340c1903d81010001085000c20301d00d2000400800807031603207900c0d818052500b0050010000040c1d141c030340f203105ca0380c0c6128400103002a030001d003900403282d0180080c6801f108141070518941c5c0000d0740382ca900b90070842c3c0c40341208129a010071001501e07241001c25081c0e2030a02541451140c4001c01512002c10358050001103e600400d01c864850500100303620210700b82b13001c03c44056400210021741c4a599201080c0102c2e000b0f120b000042e610500e80000c68601c8909001c40c18030842e808000ba59010340501800a9400301c41f4031030342031007030318801c0611001d8640504400781c107100d6030070a807181504002600003160003100d0341d280103118083c420725207940110b0581c802c00c00008c044580b412410450001e050707100c42c0c42103185282c8641489004000f49070a81d0609102c140041e0010901030307080e96011340c052 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 428940728 1250 428939478 428939503
    0x40c0303020c15401a130306050901090203060a050103020109050114180a0807080304030c0807030c030b061f020c090f060d020112090215030f0a0207031e1e11010f020a0c02120c0a0b040602 83
    0x2402c1610307106e00408055082d0000a007142e03111700110782040c009400507401e6681c010b00752500e502c2c1c01c5040302c0060009100517400244802c0c2c0000e010750107401445945511800804d00e48080d020b00b46103040c0410a20315089401c40c440011110010f0007a940900105406183d80b1840c60030800d0709040d0b99040080c468000200420014000d07010364411241d100e5003803030755540c07030f400002c0b250b2102d000ba1419441044860400c050b03408601184000c0040341d0200d1603031100316000550040460f8141c0e003180000c0b8140d00991701032254001b4810f0f0305070012400416a501048142c80740d00316040c86040040280440e00882002ca47d512211b02001142030501685004204640b10101400140c88040e1000d0905202c1c1a14103032442c201c0903100504032002030020512085402c001c180c5520381a040810750b1201e00841c1c111282c1943c07540f02c88121b0b071b0200410a000c10a211a40b440f40403032000181c0c0314084490700511040c0c80007a1030320b1030b05001034148084801c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 428941978 1250 428940728 428940779
    0xf0c03010f0b09060112060803030705041d01030302121c0e030a091d0114030f060108031306020a020a0501030c0215150907022a010201090803040c0303020c1540 71
    0xb07044241d1141c0c81e40d5984201c00746030070b11aa41c0b9609a200040c40160401401804004204003121350480010000c9642c01303880003014031f8010034180b0104000703020050058001c04240d4554038030308405001c41e40f0850407540c24504161565200304c070b60001030819150008110344000c10f0f08002583c0c003c00203400d0785002410f60710145091020305000790b103401c46901c41402626201000140c5041d07920343e0032141c02e9616400040c0e41d90b004400458407440d02d01d075011941c0b620110799040d2070341e80070f4104203119042c2801900507004070080c2004520078107028200c2d0780c11044055004402403800d0994440181c01440700007030001308958155880f00040188a076003505c9014040c0c0e94400100805d11351460040b405000b440c03030090640a004820310040c0322070f288a0804803442a02100c50000030501480318181880306010741e807000c01e00505d296110391401a5600300c0601e005644c2da40004285c50075000d84c80743c0e00c1c3c942c4082070350040c4041400310f10300741d4002003880075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 428943228 1250 428941978 428941991
    0x2a19061404211505040f1704140f010c120e09010f0b0304060b011101110903070f0503060f1e010303030c0f020105060d0f062d0c1805100e030f0c03010f 67
    0x10900c0d96460300151140e5120020b40a0007484610729009640b4051920240203070b0401c1d041c044c2064100103402d581540007080c00c00540c4036588116400c4901e103c400500c4140d4800c10400704001041c0b070541401300b41021040040d82c16985404011102d0700c0c1d00350212914070500c600300700c0503007145200c000d1000050244020042c1600d0340190b21180120300ea296400040340c08882d03a01550000d5820802418240110100680182d800550403101007a42d02e0024400f42e408038460f4a8241d0000d0700400c00006041c851150701200c004050343c03c00c494080d2206446609a10a60001c0c0d5207200c3c90050983c03004e040c2d0200c129520003800075082c44c20002e05c0030ac0b000d4a006051103030200d0322404100c203640200428001035001210950b00c1281d01107403844064400d031103880d190402501c42ca5015408201d5440f4a40030440b91080c1001d081c010300301c440c0c01d814401c3c020542c18442c290b0b5410002850350885107005070104056100615094807400b10190030540c0c00c020307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 428944478 1250 428943228 428943239
    0xf021002120c2110140d0803011703040305030711040b030a0203120a030b0907090f080a03080c070f021e0f090f041212060602070518092a19061404 65
    0x19042038120b03910038092541c902e0790007420b904034001d07901e0320410100c00c2d104002e0041c42d02102c0404641c100039200664500150804c8013905950790010205941800140512140d241e2280b0209500800301c0746420380f070740c540510710f4001080c1101c000e0260301d030fa00350501b041e0107050b103141d80940081c07103d040e055000980b41c0c10b0303102003100c0d600000f0400c1da9109100c0c0e0440c94036000c01030941e41c0039003441140202107900900039070250380b64400c4001019200000e003401c000f90965542e4416403070702c00744420203078041c0d0003d0300c4007181500c80001596401040c0c2e4130300b505000b10240420801c4d801c0c0166004420242c85c49400c180d810807400a4900d40616401075000121400082c40403d080e01e90122801d4030300e004518000010030303001d4000646c8800d0b68402c40e9440125a1104007140140030112070400d80c54000148514040a15611400490809421981244414502080840d01e12140d03d011b000010310040150070b4010350b600e4050303102404228542390409 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 428945728 1250 428944478 428944507
    0xb0714070b0901092c06060d060b04030c1a0406120605031902030609030703120b1c3f110c060d02070b070212070f0203120706020904060b130302040b130c0f021002 72
    0x1c4040c0003085d440c1c400051095030310031003111141600c0000c10008035848440c0708103250080e0004031030407106100041130300758a040707034420148600d809003890542058400c4803006221217801460a403100c9002c21955001d006902007040305194103000b009142c0101458000003420581c441e410412941c00480d501503080340403c60045404103107001407902050545100701c418000005101680c401041203402d000f40c03840200c01c0011108030a803244551521900c10005010209940344009285004c2c4203140000140e00c8141d448030300c0c0c0940402d0042c0d21480b000101107a001419000b080400c980c0385801081920040c003540e022403034102854868844050120400c1800c040119030b810042201c00d011500c0340d1546800d00d03454250040c0d0081c0d1039103072080f8140600420604d455000355034140351655036030f044503403840d000e110042828044240e00079920307d000d41449400c50082e561200e6140c1d0b1050301c514181340c002070400c900352161031b50780c0d401000341103940c80b0403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 428946978 1250 428945728 428945789
    0x60e070212180103090521120702061603052503020a0822021504031e110907020303161b08040515030103020a0530061801060305070b0714070b090109 66
    0xa00340051050031a08101d4a0507001106d1040c0b5010307e030384080350401d0044050001f4100c0c01410708002e80310014166102d0b18212071311085070380410b9950120311300c260030581e003120030b0000d11101e0720083d031b551101100031024440d001c2600002d40e001550b9000074920380c044011002d102030600c40720800da4109800002c0648258090355280c1e0244080d00200c900031170380b02c2204014038071881c0803092418000360007039580070742e070341000e00c102c0c1060b1201c43c1c4105029809145150348640b694a0480049000131042055070b200341d08a92a05408003060366010750105d60701c0701d2400007000744401804e584940450000c0c001000141c03075800c0400281d80c411a0f404c424a0381c9155980100c001c01204020008003810a11a21580105040d4000c0070f01441003415005e0030f034003a5090f201d40e84001000b903403007507000b0042c943c0004050081c0a20a07440d41a046940a51803894681e490b003102030260f0000440700281d68202103c0c1d4001d000c0c400d2040b44c000c103900303808600640e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 428948228 1250 428946978 428947027
    0xd03020f041208041e1503050708220506010306151509120f0b04060f050c0a02071a040b04080303070914100f1e03020304150b150705010906060e070212 67
    0x70992800c420000f806050768041c0501241c05031502003042001094901c0600c28051140e60300e040c0b00101c64032901800748242d1244c0c44072080c1c5d1311007845002e0b03103102840c4560304c8444e010800f840021400d10400d402140070700c0c1d0129103420039038910071141000b9401211072128403c9010b0380c2640000d0240700b1074416a4005070300c030425041007101114880fa0041a00460790200720402001e0360040c0018081a10304025940d02c0e103c00c52894400c90783c02101692180708100401c140002c4001c941000c108880340c02c06030b0383c0340c07104600c0c2c1040e009600c11b80c2000c030410940c194083c4101c401844c0c840c524081d02003032000070503918030b1819041c60030001c00c0700e0510840f80c000e004019515089090101d2880d0a20000030300039002981d0440741e288102c20042c2001c0140c0c01a182944401025081072072010903000b80a41d00822040369079548480510b00030400a1040b00020008240c0c3d1804515103500001e08204048401310000d10042c04907006980e8501c4030108403e2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 428949478 1250 428948228 428948249
    0xd1a180706050309010f020406050c060105010305060130091202240109020a031b0f231b0a020402070c06120c090909050a080a0903031d0f0108180609030c0d03020f04 73
    0x1201e928444e40501280c28464001c00d0001800003407403603000008110041c1721030152502c0f662608011070640ea0142d6190340060070189148010541301d04148a620f40c411818240303069000b10b1550981300100c809a402125603402d10003d56010300c040c075443c1911412030100c80c41e135411800d05103041805a480d4169010401040c2c080c041d41c44080e08480d50f0740c0400c285440042c00138001409500c40301c000800c00302c15020217140c1c6442d03100c0c644400c60030035810074100d80c0d542d50020000d00d0a20019200c0c82c4442801341c3c4552004154450182c0e10050781242000800341812a11200812125103040c03000148181d0042c414016201d04c008003080303036401030a00340d142c034541820142020030300113100c071050390700100c580301140e102e6150042c045440315030350b009401041540030341089c001d0800e01510b610412103607a1091900600181c0f2407003940c1d0035841c280c801c40c0d00035116440060059811034041045500e1815949001e500e0031305803018401150260b44036450221303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 428950728 1250 428949478 428949481
    0x70e0a0e13150e101509270219090204030b150904030e0315190b01090e04150e0307050106081603050a0206090114031003121706130b0d1a1807060503 66
    0xc48a4104485143d0500e00f2204000c080040b0180113100c000e5542c2141e40040340c000403c8001e501840000c0700750031201e007000000d54106046402c1054408a900c09540640a00d00080814000001c0c00400340c00503140c9045151214060102071b1140030381c1040c00206031004da03668106140d11642c145403040810511402091400d02505006000074840200b0030040e0940b113039000a8284801c141845900403c02c01902c1000e06800740c04690b000c100002404a180c0038110f40f000303da00040021481505c1c000c00c0d01f960800d19044070a80d4580078104140002000000700c4e0b00d44050424403014074550b2010360360112110024060500490170760060b0b801a803800c041c606a412a040d500d1424030000850060303240022644501c1429502100d14828002007240c401c030200700c3e040d1511908108104104040703410044603403074020070070070b80d19583e4080d845c10344200806001c1c1a403240f0b00c04e107200c0008010304800764011001c0c4c50005000100c800c1107981a09200e6070344d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 428951978 1250 428950728 428950763
    0x81606090f2105010e0a0305030603070b031306020307020a151a040506030a060b19030c0f060512221b210c06050703050d11040501022a011202070b070e0a0e13 70
    0x5080d00d9000c000717103402525200342c14180c03c4401184a0740d8114181d074280303038403260f044425000070b0360b0510034212040d8070030f07000600990081d40c2000381030040303400c5044641d64141d8400185414076020a031151503002c600c1d1a9a1041000d0590440301800f6515002c800711ba901c0003c0f03000a80081e4a9501a404d83c2d200c4601000d8010070301c0030300e20541c64480c1080d040c0781545214191100e060110f000078601d1103281030b24002102e002d81000e031915825007004c1c0c0802036603010f4044010742d0442000142c40c2020910200080d80c0030107070381a25260b10020100d00c0c20024552100ca2102d1801c00640c54503241015646681042a15028581811a400d0180940e02c1118518186161004038440e102610882c2c00987c21114410507480d0300201203003521503400a0644a030034407200c0740d806900c4550040340f80c4c000060070308c0349a80303e002010782d0943d0b074400880d1021803651210700307140980c08040c025817010406241800054201015007240780a0240300311040c2e0000c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 428953228 1250 428951978 428951981
    0xa271d130312180221060703020a02031206120706110d090503060103061e05040f30050c0f12090a0e04030206070810090219110109020d021504081606090f210501 71
    0x3000c2e13009424400180105114100c890f80100c0d0300488501c030b10000560076a200b402181d099480340c0d400340d4209913100004010664010388025400f85403503803482000c1104029040090041e81c0d04c16200350b0030003484608240900c0407910801c41004000d003d50b840008840d811281d201c5400541d00d5945020703962001c0b902d00d80c4010182c281418441030083d1104400c2d0a14021820b045080d100c5204050740980074200c440c50210001041e411494011400340000d950303900181d0300a444060800ca003032042402c41000314500104086440e07061188000300078005c00d0030b40c03250506081d100690349140040070041045a18400142460404150900100001d00082d5151038030310300100d950b1250360110300d0000f1207020948047d02014000c2c894040d8014142c1c0032108802c2d024000495182802049000800c00c00010041010000f9141400511901343c200c5424208014030035036051780502840c01d510b540078800480e4442e41d00e0500301c500d1142148040351843d0090 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 428954478 1250 428953228 428953271
    0x809030a0c030309090506221109030d02070e01152a0b01060201020901080c040f090b04140c0703020d02340b04060504080613080a271d130312 63
    0x51420407651030000c00c050b00074101c2000c1d21003010041c403850340c80d68144051f005540c03482403d01e400f20714102031025031076401008242c2c06035007402d1500101001081c5080d00c5105044010703880a8004c008003411156030b6800361041401540300e098891030014403100e801d074002c0702d41e142200d4101c5814103502d013034034803041e5003e00303200559030755624083c0c000c0d084040c20601041d20b0700c00046290350f03034070201d40a88204c1c40d42c04140350b003008440d40003040d030844500e03041942e854032415843c82030b460381031042c980b200c1040c0c0c0d101d800345402400c0c101c03e51660019544103000901c000c86040c0203003c17050316480c66030080d060800c92401180407040d0b03c17090038070304006030101c5c815034071100030416103149804a030799944410721404070101c04200054000001401158000740c4500c0301c042c081c5400301c80c100280c1d0511402e0301018840782c1d11007107046141d101404030098010f07000035802030381002111241d501644000e03200c3d030a00b070b0050840954807503441c582c2d8440c911402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 428955728 1250 428954478 428954483
    0xa0c14130207052e11030a150302030322080109050a140a020901060c1a090d022503030809030c1911040c02070905090709050a1d1b0405040c0e0f0103020907020f0a0809030a 76
    0x380210494a1790400c0c5a40c41540d4048440303050640c16100300c400c0c01018001c481d4064001d6103001c0d255800040c0a6202103c4102c52850010002a00c00024040d03580680e0285010700031400c0585403411a070500c030b041031006a0864403152025a96218101c2d045820070704051000b1a180d207000c00304200208245000a104041440380700c0600003189040d01142c2e400700d038960845507011941c3e0f820300c0a4046504c240500302400081d201d050f0369904100c000080700d0801415101d0346060904c01c0c1100502440c440f80c02000703001d0241d403c14a80c58050b10304200c2d41105410094903080350f800350303002d52600c400116401070002c2090500404d1064410006070510340d198901905800160382c20b81c1c00410006400311502140808180000a0003a001c03a4101d1040c003002c1d242c003c00656550751400b4000500d50b0011890511640038a0a03c03e0350f5030551040090305200644106e0841d030016880d44441c0b00001a510240b030b42000d00341d916207000d5000a0310341403510400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 428956834 1106 428955728 428955731
    0xf1118060d0609020a0303022a01021c230309060a110412151d012d0e0109080c0303072d0804050a0c14130207052e 51
    0x50190340b04810114004150340c00080d480741c1654426000368010254658142003900c80c80001c107640c000790800c65014990000796110140f980c6150303651450182d110300e807400340081c1e0100d40c001c22525240522030840d105415002520900440d104e05001b240c403031101800780500e0103080c0510b4508040c0f8207a4604610031101409440841700c0707171401c01444203030f0b02611089041010304215941080c10701282192036800460341502408603010210502510964405170294813012034401900800c050040c049100c00800202d40054440c1030f5000c00720166210f101251189080051003540c483c0310140d803a01c050005402c04840c0040d018010030300c10340c126003d1f000b214500e5000f40c0d60200050000e820100440c1040c10f0b0540c0e0620f8020481d81100c80c2051045d42840d681da511590f0f28110944110380484032140b9640d0089486081e10380d030f07450301440 = true := by decide +kernel

theorem cover : BRFrame.Cov 428776978 428956834 := by
  have h0 := BRFrame.cov_init 428776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 428776978 ≤ n) (h2 : n < 428956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
