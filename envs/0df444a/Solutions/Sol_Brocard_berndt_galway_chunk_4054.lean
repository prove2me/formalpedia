-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4054
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:26:22.132261+00:00
-- url     : https://prove2.me/submissions/be81d235-b56b-4bb2-93fb-819c0ed7ba4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 728956834 ≤ n < 729136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 728958084 1250 728956834 728956841
    0x1508010806070215070f03140c0a020f011a06072904060f141f05030307110307090b062a0718110f04050d050709180308130c0311131e 59
    0x304021507001c40181c1c00e05144c02d1081a4003c459031400d051b820300300303004c15009011142d6464110b981c0110400400034081c0000e08042000340d4290741c0c00c002c0c0b1101913400c0e110a1045805a0074214640b0903c61a00d800100009482612a0444e4643d03e08071158030b002009082406002040204000c100c030a11411074000900d44041081454501d00e603000800300801c00689035401d6448007205034089d215400085c03200400706e0703665500030b01e40050341c0819800b007036001f881000008180405e00d4055480c18005c050b040c1da0030a07080340640b0b80d0b0700c034080d15024106200c0e07008035210389900340640e2014000700101c0d4406a104413060004aa0305c1b080600c01d150300500c48240d1041141e800c0b5000c4500407622030742d4041c014205030742008519401420900c1c40e009040d80e0410403d148822814065103442445d40d07100c1000000041c20b181000700b0064203040b01380b000503c0300c031030540001405005c64240d4a6004040402c603880c0300d090310561800c0c5000c07a0742c004110300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 728959334 1250 728958084 728958091
    0x3020c15330d17030a05330603060120010f061a03060105070c030614040b0a1a04020c010236060a050703030509070b07140c030a080706051909081810050d0e071508010806 75
    0x100081641071400e4030f005084107407d0b02c00744540380000101d002d580c456210b10a00351000380d501d080c10030340700100c54001d0140038200301c583e5091500004951b0384001c040c1040d071001e107081e180346984800c011182070f441780d5000c0751184001d07070010000c1030042c410008400201c0c10a080c4c0c60420341001500c041000b0000ca481c9410210000c005c1c1054406ca595100020f03503016841c1c04070386040c103029010740c2050040705080a00c115034120002c40408843c0c16511007030380c011031259024050380340b058200c500b002c503104101041c0080e01c29445560b00071690b01c160f50380f40b03803949420036065016440940d0b034086001101c0c11220070070b00c64001d410500300d004041c00e141d507544456082c00b840f00701501c0299140300091600c0c8207140340c0307803e45405034410440c9120a240125168020322100028019102000c07070030390070203807042c15400e0000c0e11568200b807110f1a111024003000100c100b0a80644130000031007048181214203808030507107918038190b05201c1d40324136004005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 728960584 1250 728959334 728959381
    0x150501080a0201080402060c161505030103020a0b03041b090c08010f0602060f04030e0603070f30020c12030a09050610050a060e0103020c15330d17030a05 68
    0x4100d0a100062006841542802c3c0200b1580d034030300004089020300b1a58119a0040591980001d40c07584201c1c81903038085954401c90303e01039001252140002d002c029000503e0802c14010096910041c5500030b100f215191a61740ca0010035108544403607000d51841d54403105407040e0203401400003400742005428110100703280c548000d42e681400740054608140c0c4030041028035101c0c051100c103014019022940e24103110710300401c10740071201040c0c00900d200c00024002d04400041c40041001c3d94506880340c80241c200310000d50200e0342d00415031240e0034115024000c2e00d000385200f40034440d070001e119251800d0003400d050004140d00100f0301242c400b400180d0704d410601d400c2d42c01078503000c26102820401a00248076000310509107106600c40614203e0129585070f10071002c01d41850030780e1a90340503201d00c040c43c10f0105600014000b003c450982030030010440c843d80241c502528604003824000700950040c3d4658034036a84800c104280b002420610403c481d000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 728961834 1250 728960584 728960591
    0x9040e010f0f1404060e0715080117011503081309090b0906010f0b180406050d0b011502010b211203010b040305121602040515030714040e010b03064015 67
    0xc03c0d040050309031000b80000c3c00103594000300c0000c64410400305000c0d00c68440c0c04070020010b610058050042403091041d0f8a003907418200046070180140000c540d103002d40351240c181141e450780c4468202d82c1c42c1c50080c1c84c0940c0000303046221030040c217004038000c0c040136415003443c604060510205801411900816000810101a95004a8a80002803a51750401c00d260000107000f0b488180d0045900050b1142c0000034454404100360403606486400403500c1005d03141030b400d0303804580c0c40c5544261002c41c0303110190702816642280300f018100780c035124103d00c1524445500b007a046000c212070042002d10070047e040201ea003075103401c004c00c1070904058655406a840c0f075003000034026916140451403558040d4503a0640610040a13140a143c540c1111100010701d202c00a1240e814410b014205140600c2907024840300500035108079543c1350300845100c880501e040040060303031403814400301d507002c1c040070f80e1a40040b44030781f0030000d50400c075644615076a072403000340f480d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 728963084 1250 728961834 728961851
    0x60506120f090c0a030305030603060f190e010f0c0f0e0105070c091a1011011404020102060117100f0f0545100501031e0506070806040209040e010f0f 66
    0x15844112a840026800300700c031240c0e58000344500b0400400e003015002103111101004140e0028050352141900303604a5040d0781d901003c103081c1a03419110807141008004c1e642c810b0520a401c64010000e40d20000301d80c11840c40d2100c0e0460f0700c420035840000303c11415500d00154440448041c214092a140707003021015214080082a90f2258000442c3e440e42a01c043ca035a2900b001805040240010303010340300c42c80094440705070f42078811015468030056440a406040b4903c0c015038040e80208516801d001581a044500158070111842a0203490121030414014840407640805010074140840c205007070540740043c0000003950b54038031401d0f0250f202c0301400c1c02843c504034403d42503401c1692400750010200c14980041d809050f18840d4113100640003071341203a10401082280c205101e400301c1e4031807000c40d0000d116401103000b040b403562048004941110700100014a0300e80d052000500315100034201e4225a5114205020612418401d40401e0550000144031040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 728964334 1250 728963084 728963107
    0x40b10090203011a280809010b040216030f020708030d06140405160305070e12010c111203040609030917070f15050304150603050d05030a050a06120209041b0e0901060506 75
    0x2113016221804d51002290b85100c0445000040030f40ca0710300c2d40000313a60000c03000010300c6403070101c800c08419802c040700100b03981054070071540d4581601036140f2290640baa004c4590401083c40c0608503c9220400b04c1c075500706000400914a2411001400c01d103440ca21460b01ca5001c100c0c00d11541c605400c12070214810341c802e100284503844e00041a584032102505d250743d4084225400c4200b46014034905c00c415880301a60300041d0b00d801080f090b00d49200c1d03956034140340d440d807411442400483c0010383c01d6007204010f58864180b07446241e0710b55054800c683e09041040800d03a120703480c1003022565044001000d40f0400c03180f00c42c0c07003440e450b0181c0607105c05030000f404071128400d40320240140c0d03400b1501440e80711007075508519400304010510b0308181d40401c4a41c3c504008114141c0c1d040c8240130407610000c0d2003107050840ca8007000410000244148d58820540c100142030881c05940f0402610440b0301512941c144400c0041c2110101e40020b8082c0104100400118 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 728965584 1250 728964334 728964359
    0x16020f04050c0a0c0c0f0303022506051b010f1a1810031b0302120a0c0f0e010e061f1d0909072106110301060e04060e07050a020312040b1009020301 65
    0x541c041e0503c401c080246140c4054820241d40c03001e20044c84145007c4200750303010482c220400411086192004d902000380c0d80f6400b00352045601117103040101c41d030888910b4070203002c11522000000f82088014030300e0404e450842c02190001075400a06540074600000d0856190101c0f2200740d5881c6480e4070301e0100041640030142440e080c0c90042c01c000c080d800c009d140035542c05030820404401246083d95210b4400b00201d5450802180126103c207040c40c0f0501120401c2c11070065031303440c00450940000e00500303403030340090450781e8003025036864452101050307200f0f41e269950211880301c0310140d080c81d09081403113080c1a00a1050552000030001e055038129040388140c0c11610141000a180841000780806d04180b2034002c213400c0c16003d14125041525080141d019100800048031058024864503c01720004104c00d14031a10140c012601180103c0c0e02e4000902c022030004070342120115901c444078000c008580300c800071904010840e2050035810340d41041410441c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 728966834 1250 728965584 728965597
    0x6140f090d20010b0d0302060f01081606030b180c0d0b03010504020906120328090b0a0c0605130c080a0212030301140d080f160507050f06030408030603011116020f04050c 75
    0x2e01a4400700c070880d0120a40c040d01103408010841c1c100e81040745070207501c59808440341e0a5040350600002030f107401c08a07040f20f28034410914120f074103007040c20680062603c05240342e000740e0b00808042007420203018143c003500c0b682400580740c01d07010098609450311074180078000d90418081c0801a2903456003030390000d070200c031014040381036420010300d54050700381200c651b1881310400c40140300482d0184041c0c01c07480d0342d558060680392003041d4281d00c6103148140010301040a0130021650581c04141c1000084483d4124004c1ca1340381d244402c811074100d50340c1500900801000c600c2d0101c035616101c1040d9000d50308541c54040c621030010034280754030380039102a50f03d10f003c0080c041d080b2440040009221515003d20010418280c0d901013811a1180b20b5210b0210715482c01070140c0c0440540107105030700d155036a076280d050350340025240b41c3d003541d22000c2c820b8170825200c2c06000c419071401650803000409004010300042480c18a80c09a868041407000015400c0f04441d01e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 728968084 1250 728966834 728966867
    0x9051614030714030f0f0708060d122007080c0a03050703030f03020d1b02070501031a0105070218190f02030c0d051003020316090e011103070f0c06140f090d 69
    0x22a5034541c0b01c20b4403080103d502441d120710b8000100003894a800304e08038080c42c1752400a00c4e035a40c0e034410544e110541034480341c1d802007621441d18000b6040210000e0650441e180003201d01c4130800c5000c1801201c170780754a45036005071900b480a07410030010246200803c4079102806480c540318652030b442107002c040c5c10041e801803400c18480c00b0ba012190344006c1788108214076100720080c207008034145000c0e140140101c542c0004c19602c42d0180c0e45818242c1e5500c2a0046400001524983d01c841e0040342c204080030071a01e1401444480d41e4410310100b1500301c00d03084c203010301400321a04000041c55142c030510a0003985180d0609480c2107000171280010325132190440a0f030510340940c002580741c42079083e02507200000b00c5e040b10488078584010700c81031554420a40c2079651038440300424100c1840090404c03403040b4054005d104c1c103030605240b11112500e41000381c2d2020f0140c00100b01064042c8102400c0301c0c038507540c4c806882c4008d801091700c852802003141d0711101120a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 728969334 1250 728968084 728968087
    0x212100308190c29060d0b0610020708060103060e1903020304050f01050c1b01030f05011d13140c0a05010c0f0b0619031103010c090e0105060a050405061309051614 72
    0x194507030240180001158000741d05203101c10740e13000303039194243c52007a208000d801800c0100301c10f8240391007483c0c0c0741a44030340c20b5495a590a014840e40500c080d804001f140b10310800082c40c0d000031710184c1e000c1c44c003411010444051044045d4038081c0b40c01c40d02c840c54030480c1c0642000c030350301205035000d40c0ca08480b03503072070180030700012200c0b8000c450003412603014860041041c2d02c4801241c60b00c03080c00381c03824881760103d400b00c41c00300c1c1c0e024420340700100017201400781042104440c0940c0706007590410b01480503d034031800030740b501c140300080e184e03440700060001703914007030310100b000b40804d10300b00728050400e60b6a00c0d00c450300f41038010040c030800d001003a050340e82d5010351200701300e130440c06000265907400c040c01c030700c80c0400c42d840c0254600200320210500c0742540e1011b85011091000e5242d20b00414450036500503401d241c20010180070101e45581c58030010071502043d40141c240032401c101c41c3c2e0f401c0f2030340680300c28550b0b030700c801c40351403950342110040d0401d00d04070f241c0a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 728970584 1250 728969334 728969377
    0xa1a070c1104020c0118020a140d0b06011106100f0e1e04050c06070f1b03020603010e0604291f0e011809050106050c060609010b07110a03020a06030212100308 70
    0x50060301940220141c55420b1201c0c8495041500e28811b000c54002c0700c050000d5a40d800318000400480c2e0011600309150301c03003020106000c15410750300000107140804040d42c02148540c02c1040a0b41c2080c620319002c602040309105192510014107030f10303412704680f400d140912140e881145000b2030130070000c20b00000d0a1280c2030100c0007003088043d010742d50364100313071920300c2c01c038a12014112425018004039242120505852500303903a8081d01c100d145034246564070b5258000108002d6006499152146000c460310405450703000c000000141004102c804014982584044503268200c603c071900441d01c0d07000c0319088030a202030a100c600e034144219015503004a981001e42d403182443d000080746580030f4020714103110400c043e600161144004c00104075020b105480300c1240520211000c03800e100100704908000070070142a559a0783e0208034204160761101001c644d02081c0e0103ea01840340ca6103a004981841d9503108508583d40e0005a002c1d034091400260105001c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 728971834 1250 728970584 728970589
    0xd17100305060106020706080903040305060403140d090c060f080f01050d0c0b04060f021902010807111e100b0a0e011a0c0f030d141b130b0304050a1a070c11 69
    0x40050340d0460241c0380c040d82c60341406591180e00d80305410010309038a000441741d8401101792026a940a0043c2c545912243c0301220f420100400c6425100c00810225100e42c000c0d1042c2c800c4680700da0300b549185458a100940b01c1c4080074124400c0c4a0400c0c00c016002e084c5203e1241590822100d4004581080c189111107500300e4101e6a0f80c1100068040f03001600242c1c2190a4911682200d00302030a1041050030810440c000a01050f4002d0100e060240a40703040b1058204480803100008280780c10700d0080c04010340800030340e03000110400144641800f46240d9030100741c481002003494000303240301044051150101c0080d00c0c000c0c0d05049a10002202c114816110444441082c0c0078203860f202c0e80310007071a503103843c03600242045c0c40e8002040301e4408c90010310041e80c0c420121030041d0b0380340d00031103403002c4000c000ea10208100c09250061130041d0b0260004040b40d48141c40d00304180104682c0c05c80c505046a41007021069120400d4100300b64412511180340500170007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 728973084 1250 728971834 728971861
    0xf060c0e0924060301080f0d0504060206161e0804021e130b0f09072c0105030412020f0a0c090509060603191e03050c0c01030b0d020d111c0c05030d17 66
    0xa41c40c2c3c040e800000004004200060042c1580c8041c01650040007000e20142d4080c400c0c0d1040c0300258201d0300000d00d100321108801c2c40c101442d41060340d4800c0800403c0422203214044043c04510580103020950500181099010203202c078450301701010a00020b000110f143d10350b130b203556100c144080094803031001706070709520064000911802e02600c05003c0148a0300d108694104000b1344c3c25042900c1003419101350700607100c0c14615105e6444514040a64440e5042544140c1c00c500d10740400802803104014014140e942e002410081e03100306840001d04030040c141d00c21818002195404601d49980d5111000750712a0324030f040ca8010640030041c00000740580400f1000c6052540010041c000a0b1101054a110003801c100660072182d00d449070340d4201c0311509901c0c006041540e11062581c0c043c10001d5000314440d0001881d0f030b2621034041c2e070986409589081001103514554000d0001100500944000c641c8000d2000d00c0c4603400031810081880842d005040d10507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 728974334 1250 728973084 728973151
    0x60c04050a18020f160b06091b0c120d0b01020705030703020a1707050301020d0209210d0c060f02030403030c02160b0313020409061505030705030601080d18120f060c0e09 75
    0x504ca44030031034030b540906500c2c0001420380e50003078800000703940743c0b5101d003285100700d008440c45458030200044400c0c1c55001548640860310440a00f1441d440e40d80c409058264001c1034007250030021705000904024455111078080e500215061005a441884200c01d80c1e034107038114a000074030070702c1561401000d80e0019801d944001a0500e0310034082c0c006154108058601450b4013400f400b070020300444599074002180c128089000400b849002e4042000340140800304200d02c541d40040202c0e80140c0e011130100382d8031950501d0352501030151038120650000714401443ca007408003000c61100a021100a40d007110a40046643d268002d1500a40000d010020a002240030076015a20303030203414481c1c8654000081c0c5468001041c9060342d0303e0402801500e81c54840c150f40e42111102032800b8000b07500b41c0400c0d1b01000c00c5840c003119000d00b051000105050620808488041e84944108204010011680c0d01c8030040c40740c01c50b40624098004c0b6514140c00700b500c40841 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 728975584 1250 728974334 728974357
    0x15190902092101020307091d0a0f0608010510170712020613030818090109060305120a030b10051210120201080a0b0d05030418090b0103031409040906020a02060c04050a1802 76
    0x3000e10724210b040550103148240032546a4603082502c0303028038800b2140c14003001e5481d050750400101c83c40215040284158910301010810390380350507a6a081d20b5040b0387c12941201c1400c400c0010014442c4101e040d15103a001521080c0d04204050554110002000e40a01400030344080784428007500c69004541115105895041d054410b810610003c0319031441041a00004102070b00548102012a80d0200c010110000660301ea0301094110b003580405043e03a0303400d424a40e0300c035200240b240c001e0540e241a40e8851214020712840e9026140900c05043c415007132000080c0c0071404419507409082292aa580f0030070b01e500508505c08015401111000c2c020041160020203002a28a8903000304026050398207034030100c0b002c0001c040c0c44001000c00400120f40200d50401d6403280b403003e400e103040540070202d030541d10b110070110388150340020306002841c1e046c451660811101d00110385011329200002e010004c040c05601c0811012096080e2020203590407240480f989 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 728976834 1250 728975584 728975629
    0x30717010e0d0203091021090f05010609180204050a060f170606030a0807021e100809192f0d060b150702100e01180e1519090209 57
    0x20044240d019048905a0450328401c101070300092500200594031400d0016024031402002002c040710640e050310350382444c2c2c00e5411160499110306008074042c69000d0420108001001d103009421201250f1100003c03525187c008400130300c804642e003c629404440c0030920340c440a0007032005080c190303ca020080c045a000040e030901585454001c006540c041d01c5c0f090b0b9585091548944400310020540201041040c00501d000754000300410000c00d0403020344180a4085003001d4815041c0c0702c041081c0c40e0070401c400004009142d03804040c0004040c602d000c5d03969400108285035031035100324540c43c00005403031006010080e07111000419505600c40b041c2000b0008020400d00d250281544d11b1000401c404c00300c0861390095806485d0521509000d907085400c00d4901e00d9aa0411030300c100c043c44150880c1407118003806440b5054802405c0108032800d40a55108001c2d024440e03000003103201e03031b4000b1043e100b142c0210102580c4d8405800004a01c1907040c0071800b115140b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 728978084 1250 728976834 728976869
    0x20102090910060f03150303050a021f0614010e090406020c0a1a0406060e09120307050d0515120f0c28090501060806041a01140904020408101b09060e0307 68
    0x6880042c5007140c4580d00d520b00c2c034008680049040d102840f440c104488180882000081e206000500e0700601a2040d10b01003440b140d07950041e5002c81a030080d056499000c14001c2c00420205417201c680d003420b200d49991540c03030100d540f51000800c0070740030710b42c04182030b9034051051120b20031660b032054540c0998250004c1181c004c0c1c0080c1d078203907400c9161040200300038801c08002c2d0b0043d07041c071004200c804900c49803c61503500c0140003404000c001e002494814400b405503030b0049090f12400140942c00070700b40710110f07611a8408203da17002044840c0162404100c0c007441100a950040c402000c031101020790700304444030b41c828004030b0b00d40020010002e13032145041c1c911554902d1480e48540301000240c58400c140b041490580e034400442d658056110301100001c2c0515260074055020000b40407030300700e5404804180c01545101488005510480708011403140c1d8030b40c1500d82c2032000038082010b03402580c00744200b0100c6422aa54100b080b01e000341201100d0503e00391 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 728979334 1250 728978084 728978101
    0x51e2110050604080a0c0602060907030b041106030a020703180b0d09050f06070f11070e150114190e040603080306061b01050a06080607021b010e0114030708043f0201020909 76
    0x8071708403030544010807103100100741380380701081d120300038400780c002002800e0a54440000790000034000701c40307148202038138000549501001e1441070703104900050710354075541005011120b651030b44502e000240e101c14000a180001502c6000303001c1c000c001182a201e2078041d242000c4980c607a12544911400c01090a03400914890f8114035940e82240186d0036075840ca80d038a0307003400745507000d052210000701031002148401007040390502d0b2042c2c2200c0c8516150103c1e0380618204200c2c010f1510140c00c103d07070814030645000c48140c50402c1010710356100e241050102a20035803040800140c5400c0510303085446641807184c410080289007050f1040b100100031602c1021500c0c0142e00000301a07a00209940301010101d4500d8859507542c0801158581c0c3c3c0b00480c0b5040c06140f04070521600b141c100910710410082d11034441d0342c105803c0c0780240340e8020001c3e1070700b00000d1044001c3e46241010010a107685414042e1490000613410b0f40a8040c2031240f9401c20320010030012840c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 728980584 1250 728979334 728979343
    0xe0a020c010b0301090f170705120a0c0b09101d030f03101d2d07030c0507050105270a0f0b130212070315020a021908040f06051e211005060408 63
    0x19840380c15004001580215200458000c5107405800c0b50080580310044100ac00000c0c00100c0240c50100800c2c41541e43e00e040207882590002d50a500510b002c002c400b560303105002032501841017034103a2103003401d003059a0344100a10144d20510120110700350441c028480005041d08640282d860050404004021282210440141030703902c0c524070140303404034030302059444880d101c0c40170940d904001a00030b0007803181d158040088c10044072020503020701c03403a070140c070780000d130500009945401c0101112000c1c00308211138204c82104800644103018880d41c10342e006034419607555510b0002d09010311090006074101000c0c1c19201d10200010502e4025a071042d0460042801407040100403070003185808070250340405003070b00c205c42d21402c450b2941840303041804c0c60162602c00b040056010b61b0f0044000c9807005c60102c08000440752414441e464400c0481d003810080071a0300c00c42d034500600c01c14918541800315420040c0c60150170040c0401403c11950b0b16a0743e0b001070b035203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 728981834 1250 728980584 728980613
    0x1505040e0309031f0b09010e1b041512050c0a020703141905010f0c080c041809080a08340f030b030105092b0f0f020102070f0f03030e01060e0a020c010b030109 70
    0x1c80d14101c00c1505071b1920b4080319050340c0e000c01001000355181c0410726000740c4001d60841070000184000118940c41102c8494040d0b0541d0310b084249480070300344403e403a80500800340c031840c01d0010041443d80055640216500a0176100c03040c03101c0310081d4200031085818503100303544800c9080a01405400c1070403403107200f141c10010303074003175001c00c442c004815a00a125200204410020822a0036059040c038840100020341c00daa25541d030440c41d444181003130b01166803a02040f81042c099484814101d0b070b00c0030b5262101901c18560000200e00c45c0028007070065501c40c500c942031203948075604400000e0001c100c1810034282d0030755140e201c2c80402d690b10000c040403580c0c01c040031100320300981d4103840b94081310807618011343d003440003140000300310741d404d200100201d6100d1344d2040b001c07405540f40e5040c0f03020344d080040c00e440c41f0481c1c04445e80e04003007040056210300f5040540c071079000ca1005840c1c0b08603000035409404600642035040d070810308414103001c000420300c0c42 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 728983084 1250 728981834 728981893
    0x60902151213021507020a0e041b060206040f061a090c040f060314073204050f03010506012f100b0a0608010b032412010c030e011505040e030903 64
    0x62030341e1070040c0004001d501c600021340100d5a2a080c59036524000d02805207244000e002020076503c40302c0d128000d500407503043c0c6a450444064009421951100c000a850288050412031500386c81c4e05001c1044120010040c9584854202e0240d41a4003c4181d1943c020703c150761a003445c19450b00150407501039407050100c81900002c8141c020702c60a000039a281050210940d0752502c00d4819030308a18a1104142c507c6d003100c0b441e03044254940500c03030090304c820750f281c83c00d040c24441050a10340c0c12a000760724150500429070380242420240c4041072a203041b1030031002011040a90007050541c00b1342c8070f9080155070008641c0c02072064038009480f001c030304a40c0c07034104558461342840344181c40c03503082010801a492105c1901c2020b450541d460940c1320f601c1e0b02103034082c40400094001c42e55130720701e1640d01c55414010902d100d03003070000a2081401741140460b030412030303108142c4075907a2006c603414400c0c010300070f458070001d0050544000131034090f180c100c540d240713510412 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 728984334 1250 728983084 728983117
    0x16050f0703110607030903080c0c1525050a0f02190f051002010207030f05090604031505420a0e040c24080c09040905060106090503150f0f0406090215 66
    0x2e140c240001601c040c26010764508050300c0c6151940c01e00c0b0340c40b400d10031485016980c0721442c141c64241c4114100c0306c0c0a400075030f8545905800020131607804544903040c036003161514000c100d0020b000c805075500b041c4090849013081c030008090084000e18186c091140380000241c0744070607801001180c00a403100c25441044200417070803031164480040106900d000c480303168910a8001c0c2250110141817a8034083d200c3e1902a060340004c8050301d50252540304001400c80204004c002d00789400d00480302c900c002844640b4605d03c6050450600041d00c0351000031950340001ca200280100b0030060400e00305806d0080d0004100e0161200c14003045007400381481c2c100c0107480e103080312607507a14001d0f150281e954801da03210090850340030f40c603000204041001444250300815690f21380003800d91404042c14200000d203403d2420758005c1c6c808000c80381d01c84140e0300303912010207414150aa0750750f10b404030040c1032240000c3c2d0840c51100500e400e07803003d14010000440000e0301c4be07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 728985584 1250 728984334 728984363
    0xa060609140f0f011217070b060f0d12030c0504090608010b032407080c070b09160611030301171207030f090801050910020a02150a060303090e01060c0816050f0703 72
    0x60700c01d45000d0b9035843c4040c00b040010401103842c01c003928010307032140045000200040d04010415041040300352014140c40c0305224030b03490020051501c1c502d0603a8036802c1c200c2191150340014094025460a00d40c84140c0301022910480855000c0c102030103080000c01d8403650b2450090840804050180c852000e60f000061896031165044c005402500038603a40c0b4084115100400034211202912040c0400c1c40014030070000e0511481d10f8200409520b41603120b10701080d111988800288014001e1a660300c000100850381942c404100d901014134a42143c00e2810440544000c0300520115851040662065800b48204041c0ea10155510b4407650400e088030700c00e4842c10069440b42c00c2621000e10a9005026541050b00698060304280702c8940d6407070108441c02002d1640d6808288205500a030a181c00340c007514001815175070500030040d2071342c0c00d90040a081402c000c0348000006413405c1c860b5070300c0c6a03c0015100104e4003840ca1a913190890700088500d40b03501040d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 728986834 1250 728985584 728985601
    0x8010b09010f030b13031716120e032a030403060c18060c060c11070f1a0c060109021e0f0c120306030a02040f1d1006090615110a06060914 61
    0x20b00280c070b400441081907501d44034500c1c16141c40319602102800881c4488a11480490b4500361040d803184d5085181c0c8151060001c00d205000e4001107107a92601c100003040c800b0004c15140c9214000b00074403040149400c50400ea40405002008544400200482000110b4100502c002c80d25141c0d500240d1030140e4900e90303805240200c400041046400002080b03a61300810815009030905c00751112132208041d09103801c84e00b0880c980041c001c401c01c8050f0f5040200d074a10203000e02c174241030a10005865885610621841101725000b1072294954640c0c000300e032140900482c1507507502c03403d441a0020540100014045031700400d82080c8100740c031401101d00c980402009087e468180b6800c00000f020550300308018140c0d0f07100d403045c81c1000d40c40d2242150328480c0040c440b19840e07500c49402d0710401c0d008449180e082c15010840500e045100801c04440340c00e1507948082d41034102442c15000b00c00c06801c2d207082c0800001c0d01500344d03108801220b04c0022050740f40c0e454024 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 728988084 1250 728986834 728986859
    0x40e190c09180210030203061504060302070b130b16090b1207121401060521090c091f1a1c0e010f091703131a0114030f0d03050a0e0708010b0901 64
    0x80e400180845801c1c9605105e58020365200900404140800d1507a003030210341500950015000301e60300080602c2885261030180c1c0d4803036211120341c0003020807692034500f01d81014003051481c48510595140b440e0041d422000139140d1340b0702c2543c803120768070782060184900f5370b01d40380450031303031146000700c0e4205020740c040049104102d007107564070702103040710507511081c02c42840000d041154190000b00e94481806036100340020300482c201e16017000503a00c0050207042420080355a424008864010f10000300c800f49c004441c0a0300302061080c0d102d124103070748141041b140406007001013506501c50118120304800800c039801072580b01d442250013008025141d0300c400b0b9074a44600410b0700003560300010b0550000c82800e01e0f5078600402840094120000074a0318006003c0044050101440040200c006040e08401c0100880d2500c0c19006e0060070107848000003a0401510740209408074642030440d02035a0391030714214000c00300c83c80c045c2e12031443e02000044c09440c040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 728989334 1250 728988084 728988131
    0x9010b03040c0b0f0408030408060f06060301080705010810031406040506010605040f03060b040902060a0302041d0601080403030c09050d050a12030b0112090303090f110a0605130302040e190c09 85
    0x403014030355281000c1c10064181c00c02c0005884d00c07a0104070104901c81c0030300142c402441d10000034542401c00c400b545403191401060140600010310040184000020714002159000e0030081180c2d103074a124403090302460380002d0007005600100340200700c0001500d41c400d80c0113500307803005643c81d1001119248614491261900c1910701e052000c0ba12640c004a04440e0003400060140e00307603804503885030407038108100483c1e8042810425014075000a100e40003030b00010b810709251100020709031400c083c0018041558521200300c08a0040100b031002d483c00514401c22052a80f0300682d482144030b50440344601c00030740c802640f034001d005030103d02c04142c4410707140d559086411001852074201c00e804164892103140081491075140044240c00b480d488801c40a8140078440d1100d00380c0d1050301042010410007905440004549056030b90449001c2115401030500c14601841100800541e41c1c00c1c2034010204a020032503402160240c40c014800028049200c031900c03640d51 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 728990584 1250 728989334 728989343
    0xa030f020714090c040e091b011b140a0506151e09060904060b090c1801080f06130609020d020a110c10030c030207060e1f1811030a0f05070509010b0304 67
    0x600a8942c00e20f8018111540301c0400c1100c40e08050b038503450a82210816a001d240d04c3c0c12402501113a00940340503c901e200c020700300a03100140d4440400300305883c0c6007019010b814544d00200000406000411545070450211021410100c119080c0c4011041c4d26070b10400007603082e8144c0003040c615208100300010b000310001d81d42c2200303122100000500c2219038654900d0784500b21b948191400d405211050210303031719145c642d6a010420008982c415040c001c000d002c102d948a20440409c0e0321020658022448046920303c1c0c45c050922a003064400360700200e400c01000c1c4813030b4054420314540c0da884007003a42c21914a980c8400314000d2880c0c10210382d98849600c40d00a4000201c2003000d407800516000d15610ba417401c0324502c0c180703920150041d10003001034481c3e0600444c0410001941000320076290302d80d001491170640401000503052400e0311526603801d200c6810215008402c4540145051400e80d03100d50b92070041d03605c1460001c1c0042500320074603040e2440350342d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 728991834 1250 728990584 728990609
    0x504090503071b1203080618090a06020a0e0d151116260a02011e0c05160302031303060606020d0309080d050603191b053118050a030f0207 61
    0x454440080c4060410a41c140060306200d00042d101c28a64113007800b94003d642d40d1845080582c01c0020264152080c009501c544c1d03410310540010206001c05025800035006036240300115042d980c3d41611140203901c032014014bd1130502080c18101e900c050010b4108105624061043e0180b501610920002e40100c0b004e40c10001042d0004000070480317854030215882c11140183c806580c02001c060340140d44a24642074040f504544103800202825004d011076a40b8410003403a40c05480c61046518100701c50341340c1418000c0c01111049600640785084440c0c980c14541c019107414812540180715080319000054402c1c42224a43d076845a03009140854001ca0030014000250040354140100115081c0382d6103407070095901d0610507064491072801c1a22648070002103640100c4c020050310110805c07168400812250402c22150201e05090910324090700034001c04448450703518403001c8180c1441b60005059034414070075176441880c0072401004a850715100e110708080c0c21207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 728993084 1250 728991834 728991847
    0x160f080c03030c0318150d021306020616030f060e010803040602070602010501050a1509090c0c0203150f01063605030c040605091303030b190612150501050306010e03010c0e0a0504090503 82
    0x45410000040140041071114411206ca02d1100705074480c034503448805500103103003a1503c50407a07030302000304610300142c002032904694803141014510240c00402d540c401c9807550b600c07603990211015144010b011107580d03840346041650380d80b0501400700036104804c000070b0380310301c1400313124141c0304050000445280343c10034102040640204e10000c2c42035030100400d030f00f0300a10400c11058925614202402168014141400c503403120750812020320038204500d0300d80717401c00c080c11a062481c2910f1560150750040a1103045000c9800b01a100e0b48550400c50041c1e5074480b044e680114151158006010204011240d0364400d00c0c0c2c0006100000800950071100070441003406400c001c9a010903030340c001881801640e0640c00900300c040d206010240d4000944030040344400350402402280c5403008001c44114400d15042050020010700d41e42d110304458005028003800074000c0710302e04c41c0094103444403040c0c058003030008280000ad4514040c0114003030687c019010354038186 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 728994334 1250 728993084 728993107
    0x1407170102180f041e0203100602150408130f0306051005062a0a1a01150206150f13090614090a030507110a05030318030d080720160f080c03030c03 65
    0x18040b04480d1320554882c001d4413808400c0440554000c41208016680d107000014132a04505a0300035504650110a030203000b15506400705822030380124005464800b100f40d042042c181a800c00c100d0081001c41c000200075560f000303607009625544a01e00070f643c495060020034012082900403038000040c0754501a09101e199035203101e002000d071000110241c990414111180c0c820808503c0380000400c0f440340c500e070348508000383c1ca2000d0605410030710b05d0341c100c03076042d1007880d07204800a040100351a9210040c1a001000c005410b009113420341c10003900a01d8145c00c40450921070000151418a0100c6c2c1d10302041e62584030241002c003980c41e0000304540411100f60042100c600101b01d5540800c081c00c44a4503808032295842d25150a01d414150b41c000141c1c1841001c038207000c02c1c41d03000b45a05641e60030482e00b640038084070241c0b59140021103264611192103030203011940c818942068025241e4a030115060800c000c41410b0780d80c4515002c0046035001030001d800703a074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 728995584 1250 728994334 728994349
    0x30307020d0507080123090123150915010305010f06090902090607061b1b0c0902030a1506031a09071b1a070e09090601030503180d140717010218 64
    0x124003a508440e180ca44404d02542103500448000c004140d81c0c1921103a02900d4021965001040b00001d1143e20102920b8458034042c42080140d0744070144005000300c60101041c10300c81c10010911141400c041d0041606a01409181d0340007904100c004907251200c05000d9044401c10341d03038601240c0c68102031b040290806001140e104204000c403101281d000d002da00c0307020340101030b010800ca0441c58060301c1d05426081c0f242d03503800c0b95000c0c0c4004c6040c2c0d01100c41110364290000da0b81e45d0318103500030014041d01c00020354882002c04007048256042d0310001c41c01c0d00d840c540411508650301040381040040741d80c0000103020b40703100d01c0d080c60b804001c951038501ca4046001c0d003488501c0c0348403000000b103500c42e0005220810404488c5446007141c1c0e0006150340c0a8a03507541113407901303900c030711402103102800c0c002c4640016264032550015000c1c107070410601c0c0701524103001d2007515403107a8401c0000000d25520403400d00f403410310843c4d000c2d000c1c028050b42d0007142e950511269 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 728996834 1250 728995584 728995609
    0x100203031305070b04270509030901050901021e030406030b06030408070f0503041716060e0f040c05041a090907090f060e150d0608010f0b01090b0f0906180f04050603030702 76
    0xb03401024000140d142c6508040c00c0070301a40600703119100710000764808404050058500c04c6410002840036130080401112101c91302882c18070303550b480500c0181c1c5400c0051b0030580e046d000701065012000000b00240082e2102c66030240107010700a4204003240c0000c1c1ca0103444944100300d503c0c00151550250443e9a202d14141c0341420f0ba603903130200200703864500d20340382500641030030081022004a060040e008030b040950a0841d00c40c086081c440a280a49000e680e40d118004c64040c0200103030f400a18200c81d004a91a440c104020010303017000c1c01d8607000f0300c041004101064041c05426003907950f4129882a220b1400c40d0843d05482105172a5400040d83c000c2d14a83d806000001d00440580d030402298103890300d00c03080d003180c03044c0b001004280d24004640425a070711801042c1102d200040e1036440341c0c4070095444462141c41c1c030044d8440d4001520b840e00d00c10100d103128203000119014103807074900790140001d407031044074050f9142d04100810001440c003140301c1602c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 728998084 1250 728996834 728996843
    0x140d02030a110c010b03060601141801021c09050a050405010305120a17070201050f07032d0608070810060f030c170a0b07120524100e0d0308151002030313 68
    0x982c8945051001c940c0e5010f902c043c80565119207605080e420200403141d000802072030301c000388080c1032840c030244c1e000340440301801910402119403180c1c401c01035052050440350071209150f402d000301816196440c800c041c01030001c0c0030001850301c0e241c4203860403680c203c4064103810001e404070710826400000e003442803025050141c03100040c61254680703e150f96400001d50ba00f4419071202c151800244403008040c00d01c00e0000791040c0803008a4480403c200b00500c801280283c0c40c1c014106d5078201a0300c6104030200004c0b0740c140065400341481d4494401c110390390326060205a00301440c000034006001c0e0b4030080100d04407040d080d80e05106054142c520800c0a82d84444081200ba03521100140200000302c62503901c0f0b120742034000c0322014014a4001800041840020328454500d1007182c422030807241e014000c01451410b03010045c42c4d00442c0707501c0d29014241c07140c1035504503050180b45852000e0742c203107418103040c00080c5400075809e541d6000101d12210556000c02c94 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 728999334 1250 728998084 728998091
    0x4032a120807150b090a0c230904020f120702121801200c0102011a0901060f11010e0307030e09240d080d0e010b09191a091005010e01140d02030a 64
    0x4114100b189420203e64144003103509510302080102c4248050008021240b41503d5031480039041011000e8440d040a40300c90b82d01200811103c46000b40d00040c1e4115000056002010368000000e101c420b82003164845a52600c003012070360f170141444001d0304141e0400c0102400030450f018425080414580750900c0c0051408210f01d41200d4842003101e07622801c400100c540e028050100444840e144004170394000200140c03a00406209072018003000802070451544210800104240098001d000c80300e0340390006aa65030141009400180040b0b0b1400014a40003100724015420030382c002417032408118003554182c01c4292825030210059030804005104000034002501e1604400204080302800c0300d82035450107c4010311481d08a020410f202c2d15404544807200341a07103002580e9040400343c00700c00c0441c4492240c2c80808002003000440904407400d00b92902aa00d10145d40009001510103140c416103440001100b8441d00b4040505a40a154042d400c1000031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 729000584 1250 728999334 728999347
    0x60a2c100510030f0606030c060c020a12030c0b040b0910020427020d06030b060a050315070507050120070302010c0503160c1106071b050609060702040902150f04032a1208 75
    0x20094103800d004212015526506c08100303000d1640ca0705001000760742840741e80707010781c3e900144080350b02d402040880c00103401c802d0241485031901c80705c4140d01c5006840c841c00c050410b0020714404582580407071080c2c14810a407000c00b0f0081c1d43c100c8100081512100c10103411503251080c0307c08000c050305500303000441541000780905401103004140c2d0411508000040c400d20078015000503000394480d901c000c0040c00000e07480c5078850550b10303020352901d00700e117402405061040060100f40c03240208032080e502e540e800400f00584240c0003000080000758040e910790008035520906c0d501030304c1512402c607006400c0f000c81c940c4980c056040d940020b000089031900140300503030302000508058080c03492a00782e040050803007110310302c2c281052a000900c15104103031001740a161910035000441d01c07034030300400c0010301c040c400503110500003d45480c40d40152005030340710b119042281000c3c006001c002501c01241132070307102c400d40c1400d00b2111700d410180c0341202c01000c100b018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 729001834 1250 729000584 729000593
    0x90a1e081c0819060f08011a280e010b0d050a0e071406120906061905030307170c0723190302240a09060f021914010b03060a2c10051003 60
    0x10100a000c0f20503036190411b05200304e031803c6078000403418224081103011a6000e50301c1e41501902c25004880c15504d10741c0e2134803030742600c0b40c156001c1a050701031200080f50300d0b505040640040b9082c40e10400180e520501c07000c1c1500d010902500003508000c100f808490410795083c3c902c00c02c050202450803001c540c00e850043d20031154041c0c01d40064040c410301785054200989004200c103002080103042000080c0c0703034821071200400c6840da0400c01800b00c00181c064480610009058601d215a03030003a40b83c0c50309070031081d102459030b0b003c1e002005191007003c1c0080304c0782ea98040a00d503402c0d54244040c558103c001481c03010300c641c0e55241c9200d5410000e0954090503620105400e2034140d002d042c20007840c0c500b44c19904115a0340502c200c440c0001c5021940140b202c29004101d444014014080c00171420b0300760046608200034100250001c0c15900c0c0000303015124281e0700710101d458141c61096035600c9420103410300b840440345800c0701d5002600d50607040c03000c5980307555 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 729003084 1250 729001834 729001841
    0x50705100902030f03040b160c030f030c060b030d120902030304050306010b070b16050d09060e03130302031516080402040b18040605010e071211090a1e081c0819 71
    0x5031000095210004001142400c0c4804e401c601d0910000b941458107080d0458414020700a100e00c204403507000314018030074110000e400540c2c2204802800008070f04004004401c4507406072003207820050092440e00380040c43c1040169282e032a543d101131090110300c064034a021042e40d00d40320900001c9050358042c0402c0d03000b06070b045c0205985040714a091517504000a01c0001249014060098040d801c201202e440c1040c0d0500000c0b402d4031440c00314010074071080c3e40325091001080c81b10f02200752500a009a81c001c07411981009146800303900c1b10181102d078050311517034419268144a005000407038000e8401040454180c0050012132600c4c0000080820394a011b00e09000520685200d52405805136024903801440c292801801d4000d80b42085080c5c01d0360b40d00303003450782407001c01a80c0c00c040000309000b800650320749001c1e131840610360803d941324012030780000e001c1100151041d00c00e1420300045050300c01c2d10341e0030f540702c120007451898510a1020030a080094520 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 729004334 1250 729003084 729003103
    0x406091b120204140d150204090e1630080f070b0f06100f02030f030a02130f140402090f040f020d0c05070b0a20070c05041a0d0206030601050705 64
    0xc10840854080140200403064040c62528014410001405800c03000190180c580c03005079100c00c20101d141c46c16400e8402071914010000f84040b81c040744012541d0018200d110080b01218824845a8031100f490f500e41d01c11070b885042c04903c020f19070b84079804110b454410015110750740c4241c54803012003581c001362244040d410001070060411054010180c2c102c190950180c00301c2c50080c02140300c20041c0e042010600031841c8500c24002d1080044400ca01d02d080b2216031a030600c0d409800c0a5000b0150141409404040200c1c214003160302200c219440c040410301c400340310605020003540441051500520003586409454496014150404c04214001a0703500b4503501c5140c2140d0aa1401c00200320040101201080b004250a40c110300c0a180004080c08112405141e050540c81100810600030407888203003c60303041d081e42150002d480070b200603101e84500d034980c06414450107910240d25020203000d03050402c003655100006043c1139107005d80e0368907200d26000944 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 729005584 1250 729004334 729004361
    0x9071206060305042307230414010e1b371d030307030806060c151f05090103080d0b01090b0d0b0a090506030a06090203100c0e030615010518040609 65
    0x143d0a11003040440d205200e550300007130045250000c210544203460b40a079201e0100405101495041000745c07102190040d420000d200300980e5484a02071440880244a00000f4101400006640c031950704004028201e00601703440c42c12030940841c40300c240c0d03402000c0250010614100510364004420300d42224481d8661214102401c000c850a030001c0c04803090003504144180b200003600252501e80000c42100d441c4d8941141c4485985041c04d11014441c1480881051040861024030514800418014070024080d294024408242000e12000308080c000700920403030720074260b1040f03030b002070145040b01d5051358414a038403550708020b0152400680d20303a00c1240d01e280010010005007510300050041d031a0110000703444818200c005005079480300ca11604559051040004103948030000700010903c06200802e2004004500d5000e44900404215074070181c1d10600107007441650307a1440d10310032204a85071250b28182d01c6401c261100800309d20120680600302109018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 729006834 1250 729005584 729005591
    0x36010b0a0824040f0807200307060903060510170f0f121e0f030a0218010e060d0e011107030f02060f090a03031d07091a1806090712060603 61
    0x85000c1092000a503032080c4125403180b20001d074401e549005940042c500c400114095035143c0c1004200c500e282e11000303101070030000f113034020440c00700c50000303506808105d082600c1e0000c1090550b0b945550040c04c010520624040000903c55008035900c4421001032503800c0e41e1b20030440701110040301e200342c00f50b0400a4042e07500307041003043c062401c08640040120107410905e620700d5100324441e80c00340c06540c0321185851a401012201126110b544155903486c1c04014000290001064021241401c1458980a62040c0b1417000c0d2410000c04032440c03c01c031440400002c10321030f15108210354039800802540b152050140503024003e4446a050883e07151000341401340080002020580940a02601aa000882d00c42840c1d05040024131403100d900e00043c0d1504540000001d4490107001180302d0181d9004443c001540350250000c0102050401c1841a141c0e680c42c003610012000080003031420403042604807000f0705120340c40c9110594400182c4850f60070601c00318bd20b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 729008084 1250 729006834 729006851
    0x150e0a080c010e0105060a120201020708030409050a0c020c2d0a0f031a01030c0504020f09060c07080607050906071b0812041802310b0d0e010507030903083601 70
    0x1028083d0f00d24031103241c0001c01540c80e00600003130101303155001e010780c9900821002001c40e402000f203031020b0011502282d440e0b0b50340e001c16101504003110544001828030701c507104501d0000036440b19440b4020a00c0c2c258143e04030491100d60146c4191031118a05241e10074000c3d100d0015810282000b02c042d180d1141c00c50400401600c44002c41c3c690b0124000010000b00c0d520380d03100301c1941d908641c096550040d082e5080da603130180d94085540f003640042e03149000d07100082c40340700300e41ca00c1c03082d10340540e161602500c3c02d0082030102e0707800c42c004022800001711806019046600007894139031803d91100843d07464050203115021441200107018094440424007041506030884025403402041d0500400d0030151640380303000c1c108410003408404513024000b00041c0050341310042d00d078a000c202a2020302820b5980001c1d5500e00404105e085100740500d100c05501030725034503043e444103028882a010405064494001c0c5508411070884008078404060f0079208000300d118407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 729009334 1250 729008084 729008107
    0x50d0833041b270f090c03050901051b0903030d0c02030408120a050d150b0a05070201200c1003090b070306181506260708010e0121150e0a08 62
    0x21144509100c04007601c8810100d100c1d8081c4500710b480e504a040d150f400c0c2a4000b0348620210340750484403140401c0f0fa0045800281580310b00080200c07964240055102d0545450885074103561064000451440c880d81d5290b005d401840c20460180c01c5034034120760f0b00c031080110380381001c003200181c00006003007240000c1080f441031482c601d40085403800b00038100140103842001401d8040544503403040805140d41d0801a000b030000c0f4510a68402c1c502c1c400070051707400301000320b000c0b40300300703446e1028000c0c2000c0414240c0e00140090802406550811050411451514040603212058100000c035101e000030302441c8152404503840782002e04a507928083c0900d20620140ba101c030b019050038001c542a4200e51050604070000c03551580d441c10001d140e52056810700001c1c8080c403507002e5100240d14101e400c0f054500000781d8881c0c40900f14000c80340c0c181840c0345201d002c0900400c0708007508010b0304286500c006060300e030240c0182c1c180a42c01d0401c1e50b0074000070031b80c1d00012 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 729010584 1250 729009334 729009341
    0xe010e1603060806040b041110050a0201060b0403080901031e020d06090b0105030601080106140f040311030606060c1f022b050a09030c0f0204140903030907050607050d083304 77
    0x40065041c00c1c0851402d0a0f40341e80d9805004101604555921012505100d04c0c0f942d42012400c0203007000c900d81c142c2000c090220b500800000d00107602c1c0000c0010402100e50581e02031301d90250300d1758600000362004601421242245105080d03903819503130303840e014074401458800041203020810502e00a00b00c0110341522302520305120b8100100552681c0c80740b881810340d01c080c14815008507441140a0710380c041c458030000c02c40c00004011061082102d00c0b03080807081202164902c0d81c0b801c2c10711100c0e000d10350001030543c0c809000c65844070140c024640b0388180941005007407080c6100c4110301020821100b0b0701d640307401c200514284215002d666840b1441860511080c043e43d50020808148424054110030000050004550381e64000003078100e04c401108642c0d007040c03188180c60398010345240060744102000042c480c1010000c2c2e0384c001d40c00001400044446090603101d4420040808d000005001250140f200811208030350b00b2040e25180e1070003100600510048 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 729011834 1250 729010584 729010621
    0x27070e0301060b03010303170c090303130e011a0403030f180b030406060603050c1206061603201c0302180411040302010e0a0b16030c0c0e0406050f19020c03040e010e 73
    0x1c3e103020001840400c0e040503c04800d18907210600280d540e4100807500d65018a12155074180400031714150a080860180300544800c0c071520b02c0d190341d807030050100030801c6228410410105010410100340070340b80044070480c140c1001d04c0003040c048a424504840350700003003201d03800481880184440340c41000003400660404101ea0b040c10304072032415004102851942c0201c4c400001c40b1921060140d0f1074082c02803084902c018036900d4091b10403004146100c0100e03603070101c10b070101000040d0440d40340d0155544510100031445c4110060740c08011600082c000040c507101765501d880c0b01e241594403980c2c0049440340d05610005280700210b16000d403040009090034130084102404442c0819944c4400310258100d0707144c107561001a112004c0c00c058003803203000800100e80151a84a00c1c4540d1080004c1d540f0741203084d03142c440c1130740c0d2007040d0442600c05c1c0c10580d6030740d4003c046180d2194200c03810b1039601c044100d05c0840076040040d89600c03c00a0154221403408900311 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 729013084 1250 729011834 729011849
    0x708070e011d030109020406090501080615060405101b0501020a0207092a0c06230c160305030c040f080f121204080d09080712110708060627070e030106 67
    0x10400050340000340908040851003420720039400d46100d50307580035801003c10f154040c0090200e036980d0180c9000516091103107520300c0c080c480c00903142c2d0980b10381c0b500c15200001c0000342003604280a1120310460204900c0074040c07641d0360501c0d158240d0001c0c2807058840c81c00980d95081d960002410145242c0c0081409800c00385503510310481d00d900c070360440084000144880d00010030841c4d180005601c0686131314580317100e0006410b69a0340c0c00013100303541c40400406441d0403030180e19600c102d1503c0c00c064822020442d0000740314400035600301d125000990b081645892030b969404c6404d038040301e8260310640050342031240600c03003c000c2c1c40c8841c1c8030500302042400048801400244010301220001403030400e5403110381e000c5081c460300281e15a07152800c91500d949a000800500c80108401c0f00c5031035596140012040d05039043c40020f03100c40e844610520a5140e005500c1c0300480d040c0601d045150031200444034800e207255074690341c1a025240506003101c03503a402259 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 729014334 1250 729013084 729013097
    0x516060507051b04021c05160903050607030c050903030d0912020307050304061206030602040803090a092c010b0904050607031b080c0705010e241005011403100e040b070807 76
    0x40c0031402c0440c0050308202d02c0c4128446038402d8100207070081c41a2500c8408203420504004001455540254400d6203043d601c08079401a080c0155951030076840001d02c1980044005400c2c43c1c400c1d002500c1c6155203040c0715082150300c0700024210340000e540d0f0501d155540d20804148034cc142c4004c00c000010f40041c501d020381940700d65481c3d1040d4002d5000b8084654041842c0f4241540094002c64124100315159529030080316141d510030b00059101d2030600c40041149003041c403401c0802d0f0b202003c0040103500f0b00030440c1c1d115a00000450f00fa55880005c08401e4130380e110120b10491156000d0002c5180c000310240440d0340d607000102e804500b0b80c60310302059070029005d94100110a10550304d406c80e9281c40d5015201d40b244807881800303117541c0c03032040c802c0c011000005013030381a400c003410340c2e03c481040441d541d8a10070140040d01c0c803605201403030040c0d0011500404c48401c1000c0c5241c40b045110181c032419102212040406410001190791000c44590088224503162 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 729015584 1250 729014334 729014347
    0x81506031305030c010603060b2404060309080c03030f07081302180a1e0b0f010216093c0b01020619020a020304050a03080c21030c070f0b0405160605 66
    0x9146000c010800480111410600e00074804100152012004050020302581d81c5a240100180020308020383c02951014904000d01507000d606001c1000c4010005061510303210044003e410160000d80d202e01040010005d886000d100442c41015407440360815400c2c59107008103030120041001f02106070707640400005a40313000481c08510440e009801c1e1030b0b114519000001c0c840810941008c41015105000000c4170307400c030408000c800ca400d980d0340d103c0b0100582e00d070303101001c0c40c5d82d600a00c14400e00c21242c40ba400b4640c403582c1503c2c81145210740c5d240c08070b0784103105082c000c4042d1480814040070503880c003d00250130401e1014190320b00341808104030345c00c001c3e20b400302c4241d00410203080b0a8400c02c19680281401008001c4181d642c2c101001070394440322440d1068000d41c1d650102000400194103007000702082e241745903998410103143c95801c04c020486506400040d10400b144040c40801d01581c043c40140212035120019411124041c2e48103005000713003030044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 729016834 1250 729015584 729015589
    0x3020606090c07030c060b030f01061e0f0e04060e0d08060f040207080304030e03010e1e070618030f02010203040312030f0f180b0907030c150207050d02060f09130e010209010815 78
    0x3a100f249034541018051140c0341d281c04805408216555078051090100d040c03203003032054110408940d00c0021a44108a20510032820f0382d085014048003a51014400c205401100071860b48c414020388000031030f40c1c8600100c07401c004d10076003c3c600043c0c24100b0310895140c2802004543c580444003141303400b000345e549058a0000500150500610b404015042c1c2c40070f400809030380000c482a5000b88058080041e50b90b604211b40c01c2040c4034540000c41d0701809504544441c4041c80f9000d40070070300e181d41e140303503001d1024012411804140400400610341c041d00da80c84030120388012500508944566086440b001502e000c1d00d420600140f9103003503128406c01449800000e1070129a441c64012442d210f10369100a01000204500243e03035001d1038800640951990300b501c6045503201b04005012081d0200658801d00c104900c40100b04694020200100c010340111808610902c800c0d0466901060603602d90350002a6a80d81e9a40f029000354869604400162800302c600d01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 729018084 1250 729016834 729016837
    0x12190c0513121e0309050a09020d050619031506080303250201091113200c060117070b0c0c040c1d1504140a150905010806010c15180507090903020606090c 68
    0x540000d00001c101050f000c0c188180b03003550142101820840d14556035941d81c00095010740301c03110300c0b2803418020030014500202041980080486e4a03c812402c40d160780355844480d00342c4103c5180c1c0c03048005680a002d0000d5440352070002d001000f41c00340030b1240e07032505c212043c0080859140c00301c01c400080c0da1f0b8004100aa1090399208005110b81d402c50000b0459400e038000890801c5000c81da9004142e402491400c48060a0307034140e9a842020701040c0b40350269829980c1c10800301808210030010203070003100d801400b110b001c50000c0c0007203070840d580c5907544000101c10000703440c034019008240000c070490075101440c0e80c0c1008100c4010030300850081c070b45c2c40200704443d10399a584403107001c40686024030320100d0001d140d04025280c00050f110b40c0b0302007003008000541c60b40c0201d007401480c1d0b40140303945848820526440c002040110024100b0020f032106690103d00100141c4004c0d00c0085d50000c0c8245d094140a03149c494000c1c9050306c101d000c8010881140e60140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 729019334 1250 729018084 729018113
    0x308130b0a18050601090c09080601080307060c0504120c0306150b0405040c0507050709050f0703020708180102011805030c060c0406091202040b0603090d09050306060612190c051312 80
    0x10001d140d002c03200c0380d500920100d5a0150140c42108004940b00c00c40740d0081c14460b50945907031481c65921640c45490381824400c1d240c0d1500309000c0000400c1c450b4002341c1a090203803038518542a160041c0d07003451124200305031000844040c007401042118490200c09050704201510307003c0c50100c20b50340f10b02c1103008880c000c80c3c0361081e40800900a02c1070300d4000e540310b000d5406580d00c0b810303080d004003001c070780702804c0d1070700d0802081d6880e000b8030807119840d03000340540c0d1512880740104010380c002c01500a04640d0b071111802c80f4003d14180c0780459030320460180d69965035141c9800d1a0a0b0041c03c000001601048100f180581001d800c000b119103402441d0b849001b54000a40140f82400605410080c00810080c856130040307624041e000041c1c540749003550b144c0091503138a5204071119500f00100304001e00c1e101e500f0100d0700d40d0003901e0442034208055071202080544041080d04070200354040740d0320203181d400001840280644085d036007030140383c1e51540c070045c00005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 729020584 1250 729019334 729019351
    0x30c0d02060c24070f0c03050403080702130203090c030705101707022a04050f1512010209030a030c14150403081317041e0305030304060b03030d050a05040308130b 72
    0x141c85038510000d008588091100210640b00680031103c040c56001c4103c8031040081c40161501d01c0c45401074a11255041d015078544e4101811030340c1e403541c0b6a1103030b4401c0c1e034003150761840d011002609000451207884200040c0550190110a0519208054012500c980b034403503801c042e05075001e152440c0c20860b25400e482942c582540a070b0030219007808407800c003c1000304c103480541c050b0b8490800c20400f40c07010400b0343c0d119800c04040e4042602c50301101c03000f0501090311440c000040426030303071605c8001460b1050040000303280501c01807041b400f103410013407a281408000e4200070b0380320030004050008080184880f56445100803c02410310028001051403600c410f420718090642c0607401d0801f032000030039442040c3e00184074000e031006011600c0543c407a292040e02c02140d5011000750f080d91919a10000134085511806401d84000c0c0700360240180103000c2c2500a069000b0b0009450405040041c10058001c0c540c08400d0508240d900c0010000e5010682c402600c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 729021834 1250 729020584 729020587
    0x6080d03021605010e060f16020c10090f18050105060a050703050a0c080d06081902030c0f0103090b1501120b0306130314040f09051f0902071110120b030c0d0206 71
    0x20888101e0341000c100310090401c2d07280c00710b04c05e980340380010750078043c06000022020903615011a54100002001c9507070042c3c106180c0c001d9141803424802e01da074100342c1001100c0320740704c440d08040c0113466448400d0104a1042c80c3c20300c0109442001d025050640c0c0403440d2071140c500290003442200c00050800a0000d441d60a181c810300d800a0390907401b5001603942d20360868a000908074030b00400f403181c0102c20388074a04d02c03c40221036801d40d5016000e49900441001007140e02c685210100b41455220701c1c2d11800503114010080c410f5035903c9503614042c840400040503541c00340ca2625030b03103240c0680c2d980d01d1ba40004805038420a00030041c1003038032042c6011201c0080e100b0f038000710040080f60101700000003440034030542d045004204032664901c4884048600d600070f0b207120030780d0213220078000910590000d0a40d40c0c046e980d0401016600c60105941c0134245070018001075000d04640c484010f1170203004039281040b0014100d01d201140000c00105030250002d215940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 729023084 1250 729021834 729021847
    0x10605180406081f15090e010f110c0c0103111b01090501020d02071e0f0305030a06080a030e180405030415030902120d09061701052106040309170106080d0302 70
    0x42900d12880c0200000c1c0c410700003240d40e039000d20340d540f20091520b01c5110f13440150f0340c0d200780345100b0107584515415410180624000304040101000c2c4401d00d0700b9529480c180c0c4000000d1301495107290f01c1010500e9680da501d6800c43e06000315400e1450401d400c02004480ca07082c80340580b101142c02d580e041c00168668000c00d0300600e040342008101d940003280445404031181d021b40700a60050000a480885510700e0680f02122003800500302c07010a9582c0011900c124061076102e640c444000808075120440140341003040f10088000811501010f00030b410000040140c550450350044c0f01400e056940301c0d2030740210302a1904070340074120245540d604c02e400ca0010709401030042046d040c800040c507034035213400013481404201d00c0000055032502c1912943e4090b40d040403408041e9091100b0085a44580011002003200c40c8034901c684240901c82c8602540c4a501c60424aa243c010310360302d044100c920718200c5914052042140c40b0b00454419114419840c006980305e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 729024334 1250 729023084 729023107
    0x4031103130f05040f0203040209040b04020d05070312090803090a23040501031b0506030f01120812240303180f1c060905100515010e120f01022203020108010605 71
    0x40e40c0d080800c5400504000510b000d000404600707445040d0340038001007161070050400d82c8400d5400a400000c0e1100040102d0030416986400ca0b02c01041c2c50603c21007902d86038500708942d00180e54120300400000c0c02203411903080802030a0300c102443c145403c25000801a860f03600c5030030b0b4000001c4800d0248510204400304015000820402003940c483c00c01000701010364075501d0041a06040c0820646014030580e4850302c14006003d60b2682005914140c041c1002c00480d0681d00601c5940000c1c0c043e452070781d101d0302510300c038100e00c680011440c0c2e442c11099290340d8000c0c0c000308140040c0b0394948205500c554010341d44079510761004008140954034000e8030040406030f40040b0010881e4941288100341d004404550301500d48030312a60880d001582c0c4105c84040c6d100260419500800c0016945400240424207200100e011241490141850810f0340d9500144008410f451648500b80c1c006161412100850544d80003805120b4180241c02c14048081448840e18 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 729025584 1250 729024334 729024337
    0xf0e0c0d0309090204031401060e101e1502030c16061202131d0f060405010e01030201030b0d120c0c08062703041e0501170610111e0c010207150804031103 68
    0x802c2c3d00b1004540c0c03141c1e43d05185004441d41e03900030740d0075400d190000420a840c07240060080c183c02c52a05605440c044108007012207040c1d9020360080e0403d00000d100c1e0300c040c7d500d0101c05164000c2d5956196031901c040c2001c04001211901142e03044c014007240d44c2c020716016041c01c10080041e038070503000100300880b03070700d50b03014881010400f01103a0040c9020070006018002d02d10880389240c50f0602080300740c9509004d165501c0082030010000340d0310917005100c107c4002341054403034440070345405004090107214000482d900c640703e02c0400c81d5510b5050001c203000c801400c81e50524950f404150b03880380110342044210910b603156035400074801c03500182034001107481c1d00c02e07503981c98404400040c89600e0200b11000c41940f400a030a04406104545c010a8400050b01516060351011138610041303096120303501d42c1d01c5d868011180605140c040545c000c2280c050340c080020324001c101d41021001c00080f0744801c00d1150080640e0390082c1c0e0506181210fa003d401d051440c1d13 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 729026834 1250 729025584 729025589
    0x109030b09031b0d05161e0506060111241e070f0816022802041401240f0c030507081909080321060409170d0f0e0c0d0309 54
    0x2102200081c404045400401070052a1601007100320381ca2400b01000e803512440401c110116900b04440c034840e80100c1501c010603803246c0e4103640d8800c10700c0c0f50118031000f0208100c0d0160720150600c0004d40c0c1181602e9044001030004020785515410404d007009a80480b03e130383d0303a002d400855030b490300c203013140d060803004403082c0351040c500b052000380100c1c0004d0f200c1d0045400103003ca07114104101821610340d10b181c0007801c1c2c40718400d00740c0007414401c03101c5a590741c6541114800603a640d001d141700a60f0260300641d841c1d410310f0000000301440302d40340021b280c03445103d000c02e00c1d040b20074861080c20314108000d10001d10300b800d88440c414440020640040015880c07444ca19100f08801a0012903030303005440d0783c84520160760784c417646408a880c9100603034420a18603620b007900b640f0005c090808110880641c7d0b400c9201c400c0f21039205145000816015466078241c0b04200360880c40300418803c5131085614940c0340d81c40c2442ca0b9004207440303460782040c18040d0351003000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 729028084 1250 729026834 729026843
    0x6041e150306050f010912030806010201020f070b04022724040f150806070e040b030f03030c0403110d030905090a0e070f0810020301050901170a06020f03040605090f0d030b010903 79
    0x100e4080540c0040c000d114501655110b00003951080c0c14035407041c0d5100055401c400b00806426403580c8081e41c0c920b0009281034115074003040100c00f00440c2c0390290441d07d20411802410b41068410010b0002c40c071840400c0c030800720112000d025240c1911140c02a0407268039030448101034038001e41e440d620410540d007050910501c07a540510070b0740880c10b0419800c0c0e0210078103464120700c90f00c588c4140c906e00d001442e902c0d9034540500d0598000008200d00400310ba1030843d40c01036107401e64000703c4030750510100129040007031081d031102e02e102200e0100e0303a03c10005020340e405000c80b40d0a01880d8010103c1d480011500c1c4180d43c031103140c505400d41107134207095032018040e1600210707016a0145006d0040d0181088045000b43c038141c40000780610102d03800c210708000c01694141407120300784241d248007804589130b4801400e4026003c0180e69891505040c0702d810707500d000c0e09200c450390068440150703181000c600e800c4144228036000c40c245108500480d03414a0540001e007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 729029334 1250 729028084 729028109
    0xa060909080c1e0c1c0b0906010812070519060e011104060f0c0209060123030c043303021b0f0a0b0f07170a0f051f0b040506041e 57
    0x3050040450142c44954900c8044801e0001d0703040200e440b40b440945001042e40c800b86844c051031810804a80ea074011941240c3c03012282c0d0740312000522000c0d518072000350000c10045c8980b04090000c09a00c0700302d0951246805a159a804e41e6800818243e1880003c2c410003802001103c0d00414000c2d00990001d11079000d0502210b44240d1061107a180452000302c0c8100003a402504503011058001303100c510ba541c0e072000107698448840d001e041c200810b0800c00f0b0484501400030b180170713140c8bc0e00115150b0b400d10400607201d504920000309120542500b0180342070003055003242103080d9140c0542c403001c05085000c109d44184c41400100e0007a8581ca2851600000d80c4030350b100d008203109103068907100c1c040c00c00d01d0000d03101d0800089c03e482081030301c002d840c0b412a030403001002e40003804600200008084840590319556114910402e02c51003003804d4500e040903241039017800e4901032a010000c1d000b8861803042d000900e082a846c030700d00c90410b010705c000610b03109a461 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 729030584 1250 729029334 729029351
    0x1203070c050a0603061a0702030a05191118070e0f040207030e19032d0c0e191a0d06060503010203130b010f0e0a0902041e0c030608061605030a0609 65
    0x2200c0040060007003901403060940001405482801510102c401d01d80040032214480002d8501940c8186000e9070180316503401e04000550400642c00110000b0004000000c5146440d00c01c2c510105812031103010200c4103001d06e00303124202079421072901d09101d0f000400b0207000c00c901244c00c0c0c604a500901c080b40700c03810300d50407009101441d0411605801c0480d42c14550b901074030010b0102401c40c45500f40c9800d242001c01c4c0d200b007410500c01200845499580d47c0b141c031840344580114100000c0c440c10303c40500b016040310826900022018003509041da6007104a041d12000e24500c90b0305d00070000c030103010072540408003400c0080c00a660b2071030102c0030162000140351f030460301c1c042c03001700014501d0b103694103020542c4d2442554034110f4607034100030f2015100000b401d0740c0c41952030600c0c3c00c010180c40c041d5114882c036580041901304c2c00850107004c44000d5800001590482c40410003280301d04622440a4120707824520340303d445e440e1481d80149002e07004080c120f8500f0b00b02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 729031834 1250 729030584 729030593
    0x41503051f150803030412051312031205060102060712060b04060207031703040b0a09080903070e0921041511010f0b0f0f150306030a02040f020a02011503031706120307 74
    0x400c0416481a082404030042100b002c200985541c0301d01c4000d82c100f480860001034810745040d0000b011443c10386e041038041c800d0a000c0000b00e60140500300400000401016001444406404000417040000d450981b00213902c440b0f0090203441000000c04201021032030f030f58041e0340035100ba4039220780c0b81d82d01d03501c2c06551480d1a01081d40c60350b00141c41d29401b010b00404491240d9400100040103440f50a003c00140013450011a000710040c41b4200d0540c42c1000b03102e004000083c040d00d254184041250f007000080c0a01040f00c42c011041c11001000c031004490485200c90304806e00c0807421401151240300062a181865080c8000b45003280c009030400191914111210081826070004112107805070070100c9401400c59018040e080c444240515031102024040d1401ca82d031690000e400c5590300b02132402c100e9804900b280e4055030910905d1010601104866001419a24003401c01e01c24445040c8016004000085035034482e105080400d00200040342e480700642d182 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 729033084 1250 729031834 729031873
    0x110c01061d0c04030c06120b06072a0f0509060109030b0403020a120f0e012d05190903020303030a020a180312030b0f0d0215210a0615080604150305 65
    0x1003aa500782104400301d21084882400c4030216980195a0303e80c4519000b4140c0d9804011500b040c42c00b03684210183c0245c688100a04046210b03613428100c90740050008a0741d5400355101180c4040026000d00c11441501c071120182c0708203d42c90800ea9030b40100480e2405e029400c001c104003071760028081010f80004155200501c16256045038142c1c02a00719000181c3d0011a03000a801c0b03e040c2c1d4241d4090381404130304881d213041044c02c000742c030200c0303181660b200c10203a4001400050658441454204540980c2c075041c80c18060f424a160006541c0b404040d0001e83d80a80c0042d1010303c5901480c00312001801807a02d000750985d4a05088034440d049000d010042420a81d40d0156483c0c440744044445400504145203040e8a0b028010a015140c8150100c00c0c410000c0d4a86001d101c0e608009600c0115954049850542d54142c2601c0c0b0300d600c02000024030207902c0326116001050039602c44010340740001c854805205012080160350b1001d00140560313194041d803408003a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 729034334 1250 729033084 729033119
    0xd091203050c0313030f030906150f1502030405120a0f030c120903020306070507050c0a0906080f07060c11130f0e0c0321090307030804080705040c0e0d0204110c0106 73
    0x228100066a9400d110ba074081c402100c60b80030548641080c440085d0042c3c0700303940480e91500d800113500055540750003c0701d0030b0300e00c45020502015010170288800c1c040c190701074400340d10612006c1ca0900360180d070f6402035004440c407500603d90210700740101004152405c6420030361102d0440d0860a0260085940a809480c0c88a09060100e0000e019541110231070340d020b0000c0a55682e0100116a41c0e0841d1004407030138000d40c00c5202e603550752021882c0261425400010700f0514140c40740e40341c91000c1031840140d401554040103203941210070300f81580c0c0c01c0021242101860700000761310705a5466103128544c900070309100e24404503030022242010981c211070000c44a41c0404d9078420403407810003101f9241400e00c50f400e840400180c500900b001d000c4503403c648a5807001c07000d4000d9044080658483c07042000355141c0f600641030b441c03406040400350601e81c2c0e0003041c6060102c03200a8000c6803031703104828001d42424129900c074200d0710000c2050075140c510705482030145a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 729035584 1250 729034334 729034337
    0x9060d050723070c091a03120901090e0f041b1223030405150c010603050304031506091a040504030e041a1e0105040e06061201060f140a0f050f0d0912 66
    0xe402c51441210400103c2d0b0300c243c2c000340035120292601c2a460003911840407900c4902040c0c040c1d41c0300c03030740b0304100e91161083c2107880c45860301b04140c0010201001940075940030800340043c0200488510400c07130704141c0249a0009400d1002c0d004c201e4040c166200d1009981c080e2240e0083c001a840701401c0e0801e100006c040c41100e28081c540c1c1d038000d038011554044c08890ba8180e8401e244c00050a020301200c0c000b16007242d0300e441d000d0450300154003e80b0484404002c000d10000b03d8400c00c00a07140b00101000302c02240024003a0b03035002e100c19640120b54401c00700341818020084c20204000042060140000c010b060401d09880d180000d400b41c1889014511144e6100c034401e50910410f03900c00d4282840c11405201900000d0b02d80c9412201c10411748070a0b21004c40b01d41d01034015515071420600756044010700c941c1c1140d805000125080c05049040c5078060034503101c03051140382007a1070706c9079a0b4440c05148500400014004e240810300001c0056080d1080b01e039840c1c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 729036834 1250 729035584 729035627
    0xb090c010e09011509032411030910050604060504020c031308010516050c0c10030905010f02040605160c15050405310c0302040b07050619020c0a02130e0601090b0a09061a09060d0507 80
    0x100004c410550000340c662070190741003404be612010324240c0c400c541c44500180041031071079a40010504070303480304805940380c0c1c10000380c0f400c1c00c000c2e040c60b807001490000020000d6142c0703421154a400c514540c840200000052119591002003050b007070344050040408444203141c1301301400030440100111074950034030482441c0c1091520075a02191129103802c1d01d030a522462200720441d403c40100d40369651541d02194268941401c8a0580307281d48901360380342e0814042200d0411320680c1c210139904c0c01c208445401044e2000919400b0702d0f4840032034400c103800d1341540a401181c0002c58100d0001c10302909110380080c1150255055080603681c80100c84001d00a074410016030103e1940108455801802c00211001d82010203e200285100c030003250507090078020f9000d5100300b903c41e601003080b894484500401000d2000041108174a00400b00c0c410501e070044603140580c000c0b5504985072100c01c1152100b041c0194204014a0b0548010f000341034150031040c0c500b660b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 729038084 1250 729036834 729036851
    0xc12060b030a0c0e09060d03050c06070c0209060d1a06280e010e04120503060105370c050a1403121008010b0109050321160b090c010e090115090324 65
    0x1824184c880581c01400000c4035685201c00d22048140d144421000c12a04105c040741c604401e124040c061905a03486600c000e102d130040001406024008500ca1100c03a003881c8c00051000401603500614100c42c2040da603695800038150f031600d040a180541c0c4003458422440a80302a14025144901c0042003542d8941e181041e0b040000c4900a207900f0b552460b00103004d0281000e076901003c1454081d103040b0041080501c0d11a010486040c1c2c020b00074000300036401c0056042d04220020b2802c003005034403d4075001c0e0f40e100a01c0001d8403000e0b5120f4500c04c8210140111903030301c0d9402d21a81c201e07017441000070300c1d00040351180d03c1c1c4035481c0140e1352025600c910821001c55a000340140040032040341030541da46030304004082070040c1000003000e04490030a01c56480b90003020341c5807840c035050003201c0c02c0900031960700d4104568a141141c56595148000341076131071000304054000d050410a440402d0305400240034042507490307a200010891111660030b0b103101c14184071a58 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 729039334 1250 729038084 729038087
    0x9270718090605012702073003051f120602040b0f07030e011707050309010e07080d0905091612111b1c080711100903050a08011a07060c12060b030a0c 66
    0x110001c45174080200b0b03c188840e050103503030300a410502d005d00710003090130400b0320040d004807240d0302d00d81441100a203c01c00d03145030075104841d800b040c141e0380c5011030308040c0f00034108030385d580c0a0302c0200e84401d07071150180000f5034182d40180c0702d20740945a80300c1083c84a0141a08282c80440005000c00d21402155102e0510b080c0240040030703084901d61500c110564043d04001e01d403110565a444402c40001400c108800081c40701001034184140701440c0104180e5031a000203000c0c1000a007030000f1300c4908580c01c035560301d45182c101484404442e0400142c8092041c030908601c0100301407000d410b0060149202d60710344001c80e00460680c0e1042c0f80514043c100101c042904900001d00b03980c00b0f0320b0161410344201d4282c464001c2501e40c00822502000e00c103400103130000c01e901c00580c0d000442a400f5080300c0342c41005c06103420700009810310540301c0080480d510f40c0100520341e4064101e4146400f4075800911030346848584195140c2c108075035480b8030328142a0141c0610703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 729040584 1250 729039334 729039359
    0x607030603051608420a0b010e0a0519090501030515070e03070302091b0d020a141c020d02040509240d0506010b070f0507180b0927071809060501 64
    0x5616400240850540f040b043d12801700e1a0b408491607030003041510040c0c40d03040034a0204c8441d4500410071103041c200e400700100d07601d00d460030341400030491401089aa904040e00105c903000c5410005034000d607500907011040300d600585010b800c101c000310400001046515a505c204c061300382180d6240302088650842070408580c01d86c0000b1014400b41c00e00301c2409074882c034544071b02e1021101c840c81a2241e0b91010304488950b9502244106103158803200d406940d980d000c80150814000c203110171004003c1803155019980e00040d8403007082c500b0b4058034024900144981403a1628040420011041c46c8099242d111070b00c01e042d81501e400d0b0406400942c009000b005545e003130000041c1e60340e0010360291200701c40350300302c2d0f000141c0401080000e41a1150200802800246043c040d2200d4070a903030b204404120800c00d0040094035a544036132072208800d001c41403002d100500701001c60300f201c554401610b13500c82c09055160400c40369944100c0301084660398903200d20520 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 729041834 1250 729040584 729040589
    0x60b0303191d0619020102190302040302040507080415020a0c060f0905010b040630290c1903500c0708070614270c0604090c05070506070306030516 65
    0x1c010f0620070400084190307144044000c03400d000051070050348901c0d110300080350301c54010000741c00090034021801d041c02210f4000e1402c0c2080e0000d428140e903084140840e899468401d107a0204610780441c0c85016030009180e04054200880e450300b4400c48041e08881401307640344e6080c040c40940f94201744c81240d088801c82a42d007501d0f048880003203403541c1d080600b44288200403101040100709070094540011007503045942c214180d00d015200110750040910f50802c03024032058403184000d024258030400b040c40d0002300d40080c040b124402c144040300b41c0c2060420085995204002401c2c0e5450807070740ca001d450410703080842c600250800c21038031942030501c02c1c060b000021341c65901420500f403142401082e540d15030149290341c458102c48020943d408449101240f0310503000003100c0c0b8180ea00601701001c1040d0102c3c01c1403180d88a540102990382d81000101c41c810410768503681d5208050f00c045092192008010305901e0000780c0b8140100d22281c40c072444030340030000c00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 729043084 1250 729041834 729041839
    0x28080408090f0a09020f070c0602011406040b03031c0c020f1912140a021b0103140f180304140f0109320909100605040c0c0609060b0303191d 62
    0x14107281ea10501a29030020003140303401c2110b10f840030403a00e00d0b90003d0154003030483c10442c2c4074415802c0c0004d42006683c00036081da4540915a001c407110280456407008044d00d01007880002c000200b03146215811484044c1d01190383300280e6407006070881e10fa002c4e40b650072901c00581020740c090311030320800341404010640e89e11100001d400001e10440d014118103002e141d411040052040a620501a00c1d0068004d45206065200b00042c1c40c40c40038000c0c40c08114501c0d00e0080e60032081c40c00340c1a00c0c1f80200050024440d02784d100345105a150b03c000a89448566812000341d20103da408900c2c86035080103030440c0c0b194841d91115040315240c0c40c0c007506985c100b107a00152089d01c86030702c0000700c0202c0b0780b5202d03e449000401d4054030684000f4281d4003401c202c020120340b41da42240b4404e50400340240c40e1141c0c018200d58456801110000b440005031a003034006000200502d40c06000c081444140d4036a034111020b451115a00c40b000700c8501490400100300c000c1e1235051303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 729044334 1250 729043084 729043087
    0x3120906030a0b06040b040312080f0f0a090206160c0e061002120c010204030605041b14030a08160b090f1b01081504060503011a041409030a0810030828080408 70
    0x1a400340b5180c118810552024004a01e81a161032054500307a00940060703c0700c86030342102540309a40300301703441d5025040000d08031441c1864950803102410203001c05a1a944424540c1e05540c0e910044510400410000d01a024118580100340ca14035100d10380d156800c450002c0c5150408250000c0c00245030f50140403444001d407a00b40c4241c018401b418002d41d4288400700016070980f160314000c50180e40000781420300d00e5880d544c0c0000c0e5821400050300c107607100c02d482c1c2d01d0000d60540c07140d078007101c855100c900302d11190704c4030003000c3c1001c0d2440d0781c4038050000701080400c00000009030401074442c0c0310f4081034000e0045801c1403800340000d000000088020341c2a002d100341c2d03010020700201d00240d8480c0040e09480514041d5000d5030200c042d203881600d441d106903001c0144841d030807241c0b443c00300045c90320b81c01001034400503c01e00000090801548042c0c600203140e000141988441c0c8001e100001c0703084072208501d014442d011304d101d0880c050201544034552091415 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 729045584 1250 729044334 729044341
    0xc030a02090405070e041a16021218040908031b0c070303140c100b18040b04020d080417160503061329090f12030c04141f0804020312090603 62
    0x4007440010402c2d02c10340500b002c04209903a2444c0b8040c020f0307001d0095140c460440c1d00b82c044402802412a840c0ea00e900d851403612150082511321000f60400c3e1000c0e2107120000f40c00e81d410b410420b01907407041c070700300c1884200030740c00e00914010002c150100c0180001120110201c0c46a04550300c400d510a480400009114440b044000e002c0b1024807428054654045480d201041a0444100751913903c840c256040181555001c20402114103007207040a4a41480d030003000f0308040d0007103e00701495018412104110f500402980f000751031000d242410194503900b0a486917221302440640000f0320745400509035000f12401c04295140d80c2c03599446101d42d0044d0340e20214000d01000c211f40c00000044202441080410058203035100c45072140c50800741d60301c895911a04080c001d20800001076415501500c8030001d00b008541886400186584080c0e4040b001211616103140c210590108665008510940440b2145100c2c400d412801c4d00400c0d89030b030b802807003d0001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 729046834 1250 729045584 729045589
    0x305030d050712090b150a0e0f090304051f120e2e0e16270e030706180606170a020120071707050118030308040302070f1706090c030a02 60
    0x709800518906040d050345210124007800e0311020201500d10103001ca080014000501c80e0b2034092410446024103043d0503c40041010680a084181c2d0f01c0100b07000211100c00402c111005408010306080b120074080c0099042c01c85008207810018070603810b04410b0740c29502542d241419031402402107c04031210300b1029004151001c05014410710514510041500c202d1821b244002c018082c0040e50000d45504e01c0000d501001c13081325030300400000d0076500c804440700d83c2403060010401c0e80400405506e94010980058001c62401c0d003060350104101d111400e000703204400512003981d444000c000c1e042c044488100301c9030420122000150710a02c140c19610b0a030003e2001500041c2c1c48051602881d0b0304461920b6426400306c3e010780900b080500002c0c8001d00c0c14941c04d40c0b00e80c1045400505510008081c04010400b040070107000b40a02c1d400740c441c42d460b009505135514200c45882442800c890614080c9001103002c000b4041401c1c000104080d00800c030740d465075030a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 729048084 1250 729046834 729046841
    0xf030c090d0c06200a03020c151e04050f03060702030a110f120c0709050c3004030327021806010c060219030e0c0916030609090b0103030e0a0305030d 66
    0x261680c021152841c0c080018021050b80d0050f04260b030b42c1140064440780c184101840d08612200164844000140020360001c0c07000003501090750072850940305851107203182c5c05004401d080d0304000c07001300c0d00941e00b2030340078004803401202c2005010551070706141d03c1d25810b41c1ea1310f005030030400c14007490381d000b03843c81480903168508030f40d4074000c0366420030b003403881580c05c4200c80d000010301102c00d04010804940542150503040213142000308201f032079441890003d03021462a48820310310f020210b0506807011015401841d5903107000c0c5002401400d90017410008000519000f00100c0d07440c0c40b00d1500b850b03000d4450b40d50900b18000303540c8611070040409e8100a02d0388500d800207a624000340003841c2c81c8031031084027181c40c5030000d400d59800c513595542550144440d210266207500510b5004450100c43ea0807400700044220068052174201c80d0384039040c1502d420800c14505401b034126030080c2d4500796200c90810400030784496500c0b000e42603a1083c400382d03806206a60 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 729049334 1250 729048084 729048097
    0xf03021315021e0717031801031e0515150f0702040207021f0c0c060c02030a020906040b0a030f110415060e03010603060e0a05120c1b0303070609140f030f030c 70
    0x11510301050035005000c01d4604403050b0401500a801c04000007040f0070340c001c5d0f10b070b050f5001560030141c00e01c0755000300700c59050120341010745642074004004418265014103403a08401840710303282504008910000d40c00c0c0380d500a4041c101c003032900d50900d1007618840798005016030b28050300e07602000302075085404283d9000102c921030300c4400c200c0c480700818401d110303101c07401c011b110f905000c100c6204c1a840b2a05124600030403400590740801d00a1819a045450f4009500d0301e00109005124a03110030760461100e00001c01481054800700c0300061050405c001c09000d51820700040d10821002512602c04510040c042180100f081e07000024003d400054019900e032103500a0301c500340c0941066801c03481c095020f00c10f05200401003804254429841c101c000305856903104580b81c0c4c0200511480300b0701c401581c0d020b0044520050b0040414081429941025102c1c10100d8a0f640503c1c4213140c840b02414070080240e0f9200f00c003801080f81180d030b80088140c120381c000d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 729050584 1250 729049334 729049337
    0x6090a0b1e0a080103151104091521060f0c080708090f0613021e0a1e080f010c180f06030c030902040e010b0f0406121103100c0f0f03021315 62
    0x203a550215040d41d6400340900c02400c0c0da42c41c880354954100080780c02d8501c101c59696a0401c5540500241d1150443c1e0803241218000070b41b460356480c140980d106141c103d41ca50b940e05160100030f1222840300e00c80300f03d0180b0070401c0010200e0b40030100b110215003280700480d50000002e00040e000c1d40e05954041880010b60b180c1d138804207081e5080950440f100340e4a004003100000650801740d49480c1c001a90f00c00c017800c080302d43c100140c6000c60511401500445c03414401d849001100c040c00c005011180c210307001e1000c050043d034041c004000f107020001c2d008140c004595121300211608a6140000750b00b416410024100e0241010003825014141c40784d600800503122442440d00e402e041c10000603a07044c2802c200b01c9009a41040a4841c034100b42050010000d031840821146601c18001d410241c152008241440d01901c840e0b540903240403043e00000f82c01c41c03200405040f13123a550001d0701c00d00d850306804900912280d46d1091407440f40601c460200c40c00b06d00c0345614039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 729051834 1250 729050584 729050617
    0x304020d17030423060c092205060415060804030e1c050109112e0c14060609010614030601080c0c100b0a06020a0206030705090f04060303050307020c06090a0b 70
    0x100d071540200c0c1240301c800030424100010400007845142600005000d00b81c0c014604e0409101e00d05565504029260110249000a1103143c990b0740701010803011400004070110803c000d00da68000b01801c0340c80070301903400c080f0b8016545207001c1021090300c05980304c00f4120b80351901e0881d80c0341c12260425030070035074041900b0b2020050741c4003082121300c6040045041c0c85586001d008051070300c3d11130b07401403c100e100341020740100c00004107040ba03001101c45000516031000c42d402004040043e040b0f062038012030102c4074000c26824410074080d41d4a0764941d036a110300320f41a11107042c042421810901c0803446640c818400303190003c100418042c10141305c0e0f0b01003400c100c4105041301206d5503c0d12a41c0f06400c0c124a15401070100380041e0400c8000b90f00810a04e00c00144000100308000030105515075801032000c5540401034810485141c0f01d150190150b401600d0300c2015105000303c00c81b0380e03d80b007000c941d51141c000e031022425614000e00b20806030000543d041c44100c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 729053084 1250 729051834 729051859
    0xa0602031306020c010c0e0a0b071407120c060206070212030f04030e090c0c120306030307080c0106150302040617010311010e03010e0d1716080610120905010b0114070b01050402030402 81
    0x190f001074400301c1c51300e10001032510004200074040c0c10941c004203000d4500107404001e8244104141c6000941048036410300456200915040280719000a0284415044000c043c08220302002d03050f91199001c551a40e02c41e1802070380c2e078506180711880b81c070000b0000102e50600040303505402600c43d091141c0c060b1001d0b400102040301c12100d480c0410f40101e0855091281009590040c6100c0220079107103040c40d5000c031b07449111704031001d020000009010300e0714003002d600243c0203103540000101c01d89824013008020358058495400001c03e00c0e04100d4060010040c1c880c101d951011005100400002c015107a0368001303240940c3c17555896082004845081c05115803498165544260207000000c410440000182c0381641d8540354000071006070f6040b48800790014021038010072484800c0404540310071002900348030321810100c80030b0403c80c05401035039240364240c0381c41c8009000607011665a00860b48050090004100100014100341d4000c40d0444d00140c6100d48800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 729054334 1250 729053084 729053093
    0x40f0f0b04080903150903162310061401020723060403050c090c16020415080f01060905090a110f1f0206011404020403031706030129030c0904050a06020313 69
    0xc04881c1541c8442c0d000500c0107040c0742c24410702009541c5103880e181d890921503401a52400b81458a03001c007040b103c0300340207200315412a070f20b1160f014141c0303516a03540e45420a03147c155962500d0728490400c9e40120781603640380c558080703807041079004140c25841c1190b0f029018442d8044812107a09144861000740c480714010000346000e08020111b00044006000c004503004050300304455040c4001350b40004910845200c1540407100491a81080e0310112414036041c0c0c00140e0600c9240078900100406400520440320044c50810660f1f5400d076055455038000d250040580040d001001010b28040ea1000c03405ca50141852040445000100c284c244100d00c0c0040903a022500400500000300340f1100d420781c064409604140ca543c0c0c0c09041c01d064840c103007400038894400a10740b07440035448080711591322500444001800e00041c3c074203030705d1550f80c40e00900514a8240d581c0c10300b10308007805294403000901c01c1001e55141d800080d003000d1b0400c0042c0500d00c0406002c01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 729055584 1250 729054334 729054353
    0xf0f140a0201020c0c0307060c0623240609060406050319020f0c071e06050918180c0301090803010b0a03060906090f051e07030207022107051e030303040f0f 69
    0x45a07800040c2d80354900c18101d0310300341ca00045280300e03038080002445420750081e00341604992248003c201c0121300451008801d01a480e10813030084c1d101c00304800c203070800080085100c0d5688803074481e0040c0005010741c0b03114070b0151940050042200304002440340005590246e40c1030890001660759040500682e4040603a40040d4000031558001244d0b05201e43c100a0180110344d01e080032404201003184541e0340b0400007030010129104a8688843d1212102c110904c0130061151038206036101445094544c0b442d140c4c80390314a1510182014401c000103079420200c0f260a582c40c10b0044034099021804210415803180f60005002030207008440190010410101d41d64000c40041003c4980c010920360700075144044c4160701e1510035452603002805440c02603075032102c900114072100544031112010034000380c4a42c24001c0085211030036500304495640288616528102141c0c130700e6080035505410420100b00056a03240c004025207205100201c002d0540e5110080781 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 729056834 1250 729055584 729055597
    0x406080d03050103052b05070f020901030c080f0609101515030c03230105040b0103021e0903162102040608010e1e190206090303070f0303020904060905070f0f14 71
    0x1c0303038650006008000c0144107140c4215070b8142440c1444984c1089400d41c40400c050714005c0c00b40c000752030414041008509441150003414004895941c3c5c682081c080e9447c0c40b0b889058051f805401f0345130306000c10f5407801105003200610703544d18a1006d0340d0050011080c1e00a1211502c1070000b02c40f0b90b183c01882c00c1c006036403800a00303c5141c1c04050706a5400f901340b1810f0207030142c041c070500c1c055181c01505594056500113422034404005a00900c104000c3c8042e1003100e80d48184002c00e10002003103c40c00540950b1510741e012029103211800c1400f0b0120b0954800c021546400c00303480e850492240000c00109141d80d0f11511682141d41c1c1e5242900180c001c0d54452a44400191080006880d140c005010418200d0140e04440c801d041d402032049000217441801030794100280c0b100660040d44500407244035140280082d070008042c94083c5060620010340c04010344a0644200c150b40c0320895003c81e003000440c2c1d1540d10410f0b48080c05081d103480284040d950000d08074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 729058084 1250 729056834 729056837
    0x130b0a0f09051b1c050d5007020d0f02010c060c02011b08011d040501200a030b100c0b0711060907051905011e0525060506030a050d0e0406080d 63
    0x10041c3d07040c0288040e5480355403008280340404a20440042c9001480c09080945480c0101e100407400000178803c0710000b460700200c03180c43c4a0324204021180c940c08591401140d0746401514903074480c510b90107114406580590008801408200140c0906220510515003041294044e95840c41200c00240031080140e66a50340358107007409010251070503100354104100590714040c41004da101031900501000c0041070301142c2046425040102000d543c440c07441078290b40500c400c0e402d50400380e0020700080c1000505406410320346000500c0d079401d5a03e5146460140d2103140d03101a018254208010b1452032002d4540003c0c800603009514410203003211a242800300322002c90040800a15410032182c100590ba070231401003115481411603610f8069280002030b500f6000310786544502a443c24040e5441c0203ca0b4001c400e5148999420440f03600d6030010715985641643c0004c1c05680130410807904180624100751012170000e002241c190b4840004070f0611065000607030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 729059334 1250 729058084 729058123
    0x140705190605330d030905060d0c0f05130b0702010c050a050706020c04152c07030c0f170601110109080706090201020f060709050613080105071205130b0a0f0905 71
    0x35810396154540f4045050010348020f28400701c003201003100001c0f44954451030002c1003d004050242c00d0400007420000e061540300d400700b000410140c43c1c0a03845600181c0f40701c4800030264090410799010450200c8848942414038500b01104c0d0b111a17000c0c2d0501821101c40c2000500c01c0204030a90307131007240030342040d40c94140b003c0d280c1410002d00c24803650420000503184038403214070300e0440b503501d006010420801091101600b0030503140c04044030307046082210064041e046031448413001c2e03a40c4440104002d408940f09407900d04603821814a48001c1221580708881400c07e008000b400020090541d65810205605c4500211b407100c1d101d1540c0000e43d0f805228000d183c2c83c402000d0a1507280c500c1c4024400f0b4a035004583c8900c00110f2002000d10070101000302415146000b0099801c0206000e82407500965006202c503003010001940441c829460724903040d8003440b42c04680e200c200c1c8402c0070303002040e0300740700607580c801150010620420154030b00c0301c81d80d10b000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 729060584 1250 729059334 729059341
    0x203030c0708160506191b0c03020a0603050411040b01020106092408060708040f0602160323190c2d0b0c0f12071809020406030b030a03140705190605 66
    0x6030820843c290410243c02100c901040a52a12801c0f624030354164021012035044d002c1c81034035030000c0500c211000301030108031032003040101d4903800e064170b000b154002034803a625981102580ca0840f8010328010090803003141c28105034007d44203015050001049180c2c6900521080311140c0007512038010060b5090f80d030000103c090480a481c2000141140f403170f1800029000b00c1010704010312402e4010b0680342885034960541e807400c90810604000000301e400c00804403c03070000b8000d4492888a092000d154032141160006e1404144054402124010568044038819070035205003944180d0300b074902c103011858100300c1c2c40c82011f55041100b04d00700100c005500510054006a0400802c02000100819282a0740c020304451800d41c2d80c00000300c1c0c12601c0c40c0d441031540d400c8124041400c4066030060003c0e6075065801300120540041019a1152220000b41c0803a141089004040c8801002000d01c04c2c00b0308115510408689007021150b4466a000d48404c0e5031401803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 729061834 1250 729060584 729060599
    0x3061e010b0717030c07020a0b0a0f09061b0c33080f060d020609090a0506130b182e030b061e040b0103410106020303041e0203030c07 59
    0x1658050015080000d003464020340e1802d64800e40202500341260000c40003c503848441001c44040c607502401c4074180603560792503848290800d0034910080361140c01c818807442d01c9003800200320340305692070754401c0c0925003105800042404068031054840040807815510b404403e010710369042d14420300040e010050440261640e111010410002000703010f080f802040009800030000c80702c130130062080e480014580d215600c0800d800681c60301c10400214640d0b8030a900ca00403d0702c1400c1041c0c1d1400028040750f01101825a00418400101108500900c0000d0307000448642c0f074803921200500484081c03402c13924000d44039402000500420550500b01a0044820384030000398907980d0b19031001c0002d15200b05400303184c1d611503c109603031094126080b45030f001f4040ea03500c41c081c040740000818807104103213000440d10340c40c0b041c059003000c00c5904980b030950203035007162525500c0419030701c210250154043d60406100780940c0c1d0a00080160864103c018001b05117040324 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 729063084 1250 729061834 729061891
    0x6050f1e013509060f010506090409061b030614091f0f0305030703090e15042d020c0d05091c0f080313050606060412030e040f02130f091107030810050306 68
    0x144913401400a01140944841c4614190741c0115080ea80324080d2101080007401400006405a030811008a80660598204c0ea0031443d02d950309006142c1c81d2841184e2180d0b5054040e5001215080081c000f001c0d84400307480714440b4030200034900c0c0d07078565121018004036041914640c01c00910a801c041e0014806401000301d02401002407a081180c0c0d00f000c6191010f42d80138517129290300900700c6c003203411031000e02e6407041c52401103005203400d02d000b90442c0300c000b00d26100c4c48000301441ca01503403d44800c0300000300305041103488014512403030010000d00711440c040c0d540240e4000382490004e107100703000b0b6890503004043c1f1410040d00e03112000e0122400390000300310a100d810400320255403002c5e01810a07010840030700c0c000c18000e0490160842d0078500c04110100d101741e00031034105c121042240c0e8401b22913240c1c0c400384200c81d41082126101c400800040c00060f0140740100d030700c1224030100c170855550b0b03240403c0c14a4030803510000c030406101c0580400e000600d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 729064334 1250 729063084 729063091
    0x50d080a0b0f100909020a0c060b0d02030307021903170d0f060315020c030409050a06030c0f0501080f0408070210020606011106040203071a0c010f060906050f1e0135 73
    0x1400340100c0040d2008241410818a06180a00910501d0014003030050038103074010100c0650441d580c207c0c0300001000d42da1025400c0b50031038180350f42168945050001446a6900100618507140003a420419101d200c00b0250401d40c948502c0040403030b48c12108034003a95a42801150303a002c02103058000c643c445060b0404071454008207001041d01000040802000c80400580c2c1d007145a00d25032850181c0c0e4800c00410b4144410008600309903003004045034070030f10310400c6050b00c0d0900603000c003c284c0903080c00608100001110100365003c906e80080c040d00c0e07650300e041c0054000c5840b41244440101c00b580c402c00a024955130310407906007020f03802c04043e00c0300b400c0540c0000c0d00d4a03001e21400f18502c00b1004000d910b40c8104040f16003c40800b40200f1019420307030321090241c07200b032081501041c5041400102400c1001c20760032241e2008011107103000707120320b40c07844503140d1344500c81c108280320203038058240d2000013020a0442c1c0d208800c244101e0184035096501004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 729065584 1250 729064334 729064351
    0x915050405151522230601050d0e060403090807060e032505060309010515041119050f12040c1202060d11090402030c09011d0d0206090418050d08 64
    0x24041102286010500d40c8a080b281c00300d001480d141c0c002c0800000a416452581c031000603118020306a500b64a24034002c40365204c140056903c07082190900d08a00c900070f400c01d00c00e40e001039038644c17095008004201c861030f000146400542c01e035510b04007040760100d02040080c10f0610a5520400a0b82c005012525010b40701404a00110791a00100c0110344140c06c0c020f44901400d505101042d009800b02a081c90f803240707014007515003c0c04060f0342c242203410281c600004281041c6c010f0300061000d03410f0a40c5000711291031b20304500c076110f8a003401c002c018070038074221801190040c40d031200280c9425400d81001d00303100c00800590b078005008091072001cac540068a900041e200450501000041d000320120104c0c1181d00c1341c1082550f00c60310010410100c56003036406040d18480a030384511640f03400e80c1c030309140245800c1c4c040341d01a00e4003094a005150400080641c130b07030064004510450780041105140d007410400710740d00e41010006c2c00005a00084203540b00701c15 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 729066834 1250 729065584 729065591
    0x6090b0609041a1206040b090a03080c1809010609031e03170405010906021b1c08180c03010c0c02011701030b0109270302010c0e0a0e010b13030501050a0915 69
    0x9140012001d20440342058025612922064042e48a10303410280d2201e02400804048658071a0070303440303101c11a01100e42440c50404290251800620121a141e041e01c90901ca80c071280350301c1c559500401122003680303031041e482d82820340750a02c0040c001c03d400d407500241c842c10340c0781400f4150345202c0600c896440d0b80c0d01301c0c0d0101f640004449900c50450f00340020f01d4640d03040c01c2d4090031140c9805070040d8000205403042d8884078005000d401801c0d81a181c00420203202c1040065080b5500c80001e0642000716003200b40302804900c03040120002ca440820881c00400d003911070200c54003001c540d02904402c10740d600900b01807124003070402d034a88a5819660360100c0d824040c010011501c0d030b9025024800c40c0c0490000d031380844080201d20342c65805280007806840e01c00740100c00581405010707002400c141d0701e030300e0a40301d4841c2c008980768203112041011f03401c40403000f0090b00b24100d000020904c28440c0e903000380140003000c11030304c0e031500b441c0c0c00764510400100c0e462841c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 729068084 1250 729066834 729066851
    0x316061d1f05190b0d0623010e06030c01260c0408190f030c080403082703011503120509060c2b0c0b0c041d1603051308030c13090f0609 60
    0x1210802c00c103400c110442c3c0003d14070b04c1c000205070610040100181554a03010702c40d00b0030040c0441585245030703130004d00107070f030381e00c030140d1100baa0401d8400c03540507030008901002640c025050285505040e203c4500c070b190211040995803181614207043d039800001d07051000e1601808503040c0c9000b2a900f203070f440344880d6606070701c8180000004d010030041c1c03071440c0704003c0540c04583c003d64110b0300207a2208290550a244a03d8281003608a003103800000c3c5000d040600412000043c41c0344e640c480e13070b46151580f00c84140200000e5080040410140000b503566001515803038602d00c0c01854088101079280217040307240c0045454804000c0c80c1300240303540c040c0e4451030b9075605c060b0000507901d40d40b40084540c05140c01c040040c040070714804044440c455000303807003801d0150307031885a01106102582212400d031090302100600c000c208020440450042d50030050300028a45400d16040d841c0020325954dc200540c05900c0f4106035010300c0c42400742d013019040c500c20411003030a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 729069334 1250 729068084 729068101
    0x30f0b0a090b0c0322030e0a080105060117060301110c1c08010f06030e1c0f140c0604330903021005070912020d080c030703120606020316061d1f05 65
    0x8000400f0328100000c00000108404010001060010f0080e0488032441046280c0a82210780349218a40214442140007540704014001c1c01c0c007400c0180c4505400506850030f2940f680001401c20740c05640311002201009000b50050107090b000902401c14425004c0c0740100400c6c111012004000c1d5003c010b0140c010500201421110345080000b00240b960480604114900c1d00031684820640102d031502c94102031420788400e844c0d44c9809164110505203407190080a44003012a880000010000745078984019a0840d41c00c01c0100354440009a48180803844c01d00074901c03680f14003030340c07003019010030144507460300c01d200030301180c6854280103010070910300c9914242d14483d4090b805544500d01949200fa03004902d40365625180d00040c0d0f50381d446500308500088040c002d41031000024800e25082d00c61940c0654544030b10b40001c0c0403a44006401502d40f00d03500d0741040404c0394080c15010a0019410140950725659110480c5180d01c1c500c1d40c0c1e00d841d042000300041803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 729070584 1250 729069334 729069353
    0x70e281a0904060905101b03091509020a12120905180f150604090b01090f030c0e1015030603120306081203090f060f04110a0803070b0c0f04030f0b0a09 67
    0xe40181d540031100c0c1e031030f0706240000e07041c0c0303a40113805c60284020452242d0034541221540c0c42140344110028260460300311300300c3d2004070024002c0010031203202a41c0d940382c0c003c04d85003800101801c41650300c900142d10034800302481100c452400c0b401c02901c641d0070540b910003d0004858051504d04640c44030903d4120041124401c1d20f10740340041c4800c0f0003880303900d4002c2c1000e040d581d2182e440b000d480c8000c01403560a0790120b401e5000014002001d00030350402d0300c0d4041609180c031490840a8a00ba0b80041c0641340c1e41a4401408610740080c0303032526500c0c801640d4041800351031414016650100d10700c0e10020981058018400a0800034004000c0741e680559169203070b9130030000500b8070415400c3d21502c0d009002c14018801d00c4c02100c54011130103502c0080d18801034008018801d2034034801d080301c1c1d81050040c1d41c007240c0d4804034036038440c900c00c92140c0303004050800c112540d409504110f41003921503d90405105e40308c9044d43d0f0003158200c042008c4e090070740769101c88 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 729071834 1250 729070584 729070631
    0x11120c041b1209080f070b010906080a05030d05060120060604110408210903010c1d1905460e0f010b03040c0f0f05121c11070e28 57
    0x1025203a007030f04020080001c0031103d00c070740d02c040c019403a0030040c070304040004420321980041300d0800d540415900f2000c941f100381903502c10011450201424040c40c00380c00001c04950510150020030380850340c05085d00c4000c1003e000103090300780303451170800003141e242070000c6068000c24031052081300b03070000700c2c01300d040326801210102c0c03022490b05406611a014000e9015420712407016180c0c0d41001c035a1340031803000c2200d80f40816045051000000e0046840340f160b803447c1c0810086400c0101e030001a28111004030540803d458200444403240b41c0c1204181c04000140d044200601c4005040075210341205d20005092520700840381d90010300800348403050020100b400c2140d0b00240000402503a801c01000d03a6440032001808001841220f0040c50807800702403440c0c4001c0f50b5030007100300c50700d00d02d034011000380012030703541100d84008503107440381034030101c0c80c400c0300e004080c8240050305420484404505048080c5443c0000c03040c0c0c41c0e810046110882521498403100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 729073084 1250 729071834 729071867
    0xd030b150d02070c0801050631050601120920010c020306041112070b04030210031401030b28021908010f06122a020f0d0207030f11120c041b 62
    0x111000d10720075210083c4104100100600f0200d40c00040050064002070700c152822034000000c101c692000f40801c4624210032804c80c8030b071000101d81a01c0541c0200d400040603d030201c0e14580b1041c19000b190311024066690b0b00c001c000a030890980310b9403e2407205020300c0e040444403281c0c3d0200b90b5440300513100130a5180880c840341021348442c18254190642201141c0345150f8074080900c80f64414041a4081d801c981221082503029010341401e04030441e2040302507a00e181c48522115001034408650a5090300c282540140c591124054820380540010b030707107140c2c1b84861164840c4440d02c0e5414001c04600401490680c094888100c1e9a1410b0100305110840321380401048c2c0a030400100920303c180d1402041c4048500c000d46030701c1c1c1d130220b94255101d8400966900480b40320080140e00001c0b0034400580a40036442540344100e00d500350403074081c0001501c041d5000e803440411751001c000340c89a4507090162035190520715600700100280040002c01e10121020140c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 729074334 1250 729073084 729073087
    0x1090e06152a2e020f091327021f020f0d1d040608031e0f30190e0c0406060804030909060b0f2d09040e07060c02121504060e0d030b15 59
    0x2041750000ca40190b000200310456210000744850002c0161300414a42c502002000e966080c040e00d0702140d0701600100820800c030540b550310102801001d1086085000e03800b120000d92a04108864003007846407259481400505003540c03492840e902c0e050701c00c0d401d00b1000c00541e140031040300c0c0f0454442408000f48411a80940103511480f00d101d84408000125071000c51154814030945c0d0f030b0003100c3d20300c2241c41e540a89008400c20b40b07584090461751542c505004e000780d071100070441005c0059865000700400000c00f218041d030b00050108544d8401c00041540c0268090060640450208800d9052140c0d8010341c1c00b03400c407401601200051030001801700c940030144504503d0800c0410807210392546080d03600800c4010340118140414000e040d40041030800c140c078100d03500e000c0e01100540030002d0010511042c0f0440b8002c4001c011030002074010303400d100c0d500541001c1000e071505400c07145050481d003801004c0502d4060300b80e03501ea442000c480d6044600b2001507 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 729075584 1250 729074334 729074347
    0x29101b030e0306010905090f01092a0510020601030b090303090604020906130e01061a030c0a03110c01050108060f01090902010e010f05040e04050f010b01090e06152a2e02 75
    0x10358401d04650046a450b02c00c0c5030000524040079040b40f0300c904464401da59603441c1142e28036081e01c2c181c2c3c1d001806100c81c880184034046100c405034004111400c4540101359880001c03071001e030780d4490f9500c010f801944c0180f051110100c46c0c1900907602c00e004618503d460480c8a48948000d00007d1149200001003910366070f62410200600c0d0240b5010410070400406850007824a40310301d45540300d80754000b0f1462502c100a07a0720402c1c40c80080da1601c0400f8104030010003a54a4081940f4010b00000801050900c903580c040c0c0f410384010301040c2131501072240a10030580c007400c3d1090402400400503680504815030310032003804c0500a00c07540c0d14098034035000d10b0300442c00c6d225480c020001801000151a100000f1141c020840c2007008401101c40c004103001e0284030b000c0c010b01190017800c01e00501d01c020800c0c100d0203400e10524000d100c01c030b0f20306108886500303145581c0c4031090503018002a040051005c400f100c9204002168002d170050244180301410382c0806c44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 729076834 1250 729075584 729075587
    0x2010f0507050d05030c1b0a0b060102030f040e0c04030c060827100506041829090a080a170c0c0c0103051306020318030c030a021002040f03200429101b03 68
    0x1618914111f06a4550300c050240805560b200391580003650780d00f000c032001c501154000b004861882042074000c500d00b40c100481c0d0002d0b10400f030883c114403003003044000701090100d182d15024009540e6602410300701158400002c52040b4484403000d2154121120610000103180003040c03d802030101c1c03e907688030005402000c40b5400c6500001c0c0760700e071280c2049030010403110118402a0301c10003030801440442e509042c11112442d25501c070a07088030100322000080c1c03010403810303d05200c00e1031103154911041c00090702c06085c03a00c0b012541c2c41840f4000e018000143c42c0c2881c04011780c0c41c2c40c410018a0000c0e805002c2c0c4019400000300b070060a040100040c0e184528045a503505c01c2030100035603a5010325500d10046c01516a1008449018001c5504a8400307644100c1c0740342c1552142441c212050318001c3d5100d00c2c0880c0c0380f90546560041c40855030070141d42c01104500c4a84114440f40542181481a8545413020312069044844844200d02e04801d0704c40c0a01c03140fa0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 729078084 1250 729076834 729076837
    0x1090b06091011060702010207140d0801210c0f08011d060c09030c0307060f0f090308090112140705192604170d050a0605060a0c030e0d0c0f0302010f0507050d05030c 73
    0x201d07000f107024503010003500540540043c101d0510500c0d910400e807640f48081d580b00d0f81ca200c0e1850005603010700400400079a041114600422000200050700b00c07035507840c203540d4196000902403d043c0e40704000c824002c0c400d000b080140c07000101c00b40456074040d40d4803410005c0603480c18020100c0d9060007038a040121140010001d0101c0300040d031250782c09010b41e5900031215000070008800d40c1a060f00c541080c00881e54071909060400442c040190b4a491b04440701203911a500c0d0102d003001d41c00d07035407500c0c0203510b40d440e00c1c2d80c1d500300b007040c402000c2001c0c800c407824845221104420034103010715150345210044000c4036140c60f036280640d07052603549108002414041050415412103600c224000d02c120340c01003000507030b140148841070103003404010209008842c0388001ca07018a01c10860100c008040080d043d003155101d90000b007141e0400090344c20801818070841d604100341d4010322200b400c0c40c504180321951410781d60224421600c2c02c00c00b0100100b48030140d080d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 729079334 1250 729078084 729078107
    0x1401080a0c180f290d0c0b0706090f0c05150a05030c070c051513050a0e070809010e070306051005030105130f170409091203021c09051e0304090501090b060910 70
    0x100180809104141c040a0b6021850300d040f03410300d2120784c1131610749001d41350360090641c844902a8100d01e00540c4005c00c2d0802081500c1ca1900c49502ca0001a413001116400610072480031304158101700a000f08500d1860f40003211b02003c0200e109601c1d04107069a50000c892249159503001500d4041040080fd070f0110340c02078003071020302e29030050410160030b00c40001820342c0b04155681080080701d41443c40388981c0c1c1e0018001183d0b190303100b50780b410b52240c2c25400203e40301e05030714011441d02205a009840195071003040c042c400503051407580060900314001d02c0f40b4145540d50304600b4444140003024410410f42c02130802607a2441700c0090760340089525110b41e520700191f03011301034400044400814010419480e1070080c400c0c0c90320070340d01181c1050710003445210075000f4000c14030281da062040010711191448001075500d8901c0400300516141d41c80c002c122401c0c0c0fa0182c020030402810700d03507001515100c120607185903900440d041c3c0d8812890034810b4405090a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 729080584 1250 729079334 729079361
    0x92101110a080411040c1b1109180c0901060206060919021602010305060a06050d0216170405030607020703020102063919090302060417030f040305011401080a0c18 72
    0x10458800041c0c10150943c8902d0107254810303601400c00301004110b4407135510100110b50307660440d01c40201454444014a80b00f05010307200c00031240d0000d5985d0508070340501c1c0720750b14405801c183ea0802d101a0000c0003040e40c86540950400b23802035210340b80102018011180c010002da4103841c541c0c021000d00385075010866907810414807000082842d00c0090740843e04020100b042410302109040c00c44207583d540500f011100c41e02d03100a1341c807442481501c44810313004100402c0700700d15008106c5482e80000c1b80e032249848285818020024008425500700d1081040946d801203070070be03072000074450350841c0144107004d203071040d81100e0203082c071031541c01044000c40c0c0608001014100d40c0c5502f442050b100318441180d4180b102e000094004200303200420450040d0b01c41012804580801c0d00d091407004c42c450304540c0c106510640d043e070f450396034641002e001c5070702c07a50141000d20003a0071001c405444146400301c0b140308056650303500c4004d8402c42211540000300d00e4920 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 729081834 1250 729080584 729080587
    0x6100c1a0c030601030c081b1b061815010605030c0d09080a02070e13080403023307150203070f180503010f0b040c0507150903050f0a0302030a0e0309210111 69
    0x22030041d81090300b046030340b01c0c0464035198000b00154080c1e030400323100703400a40e440704007000ea4131540041608030181000665414042205c0e02803000e0000f14841c00310404404605010112258079080390b02c9400a0604103107001446115440740841381c0c014402100682c1d10110041c05800a010100024000340804100c0d0740b01280e0100380001143c1d2040f4150241b612609185105800910401032015a0070441000181098100c40c413903600090313507065403411030700881d2801c041101c00c100c003130013800100308003002000003040c19a10101130085055142690010303010310030703da45030b4060001031036950480c1d000860b0814040c11001c0c2c005d01040c13948450640181025817517040c0301c0e0341031030b03203805400e44520300303a5031610b400240302c285030840d8000c00802460502c0b01902008030410507080403403043c1006083c40503299070016a289002900030301241c00c001038001c40350300200803000d4241d07604140c1d120b4101c0c0d2000e202081004945519005001b25034507001e00d01c0c030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 729083084 1250 729081834 729081841
    0x6130903080603010c0801080c01201e070b0403021302090a03061a01030e240c040803161a010e0a11090a120209090708071512141e06100c1a 62
    0x24041e080d54050b44041d0000c0c080d56050f8070050340d281800740640c802c1a4400050001c0941c81001400d02d001110ba080780320454202c05c4403401c1c240311100f00c50b00001b000303205011280c0c04021a000810030400c0d810f0505042d540082d20700d0882d000f080b904581c011035003c0755030742d44156160003180c1c84481003064000c0e0382c920b608842c01800f002c5000c01e203800c00060900d03078041444440810700d43c00302112050000080e00c013a507800f80c0040d50840b002e000200b07090500300018240c0b1981407a42c4030f80c064841c680f01c41036540610486200c0707070800004010b00820282d0068200071169000300c1c000e640f0082c0c100c00c1e40944018968020340800d800150040e0b40207001c5612402a00d011a41d592140c00031507444185104c0c146481d8441401001038104004242e10749003c5490043c8443c0340785140101a17845842d0381e00b2003020980309110f002498104843e02c921500780c03602285107040c10000704c010310f18079603031010b10280c1022403080069920280b20714040400c142c02d043d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 729084334 1250 729083084 729083087
    0xd05031012060b3102090904030503040c150c17070302072304060306050106142d1c0507030b0111060c1e030a06061205015003070905070c0b06130903 66
    0x15810001191001181c0e150803034113850074002c0701c0d140f140c040c6c1a5503450322079590482c4d060b400100f00f61802c001380b0102283c00d0f54501c3c40ba180c034106643d2813010f41041401d1031444627560780d040c504a51070401907040000c0c2c01085103c1141ca58041c43c45002101c509103140d10101c07812541da00c1407a203a404400c1010135401141a6907a55036000030314130300e8181c040c4c804d215209500000004100e020b03580fa40980c802d010002d01d80c2a480c900701418032000340000d00a0646807001030340c8030401c02072500da051044444618003440c01c1031035451440441c079280c501c00780c0042c510780c0d00007039824070301c11414000c080a4120018400c3e924900414244010320850080100180c2034205500360f10649000e094143c44600b060800301021186411030b00c0501428001c46846850902c2600c80d03101042c42e0341c0070a0003042c650010740c1000d0800d030501c075054010001131444d1205000f00c00707034000242842650300c094070f85601d480d00c0000a01c1414458840c0041e80c1c2880003031070070503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 729085584 1250 729084334 729084379
    0x22060b0a0f090f090803130501020f0705031908013c1e0f180e0f06010f0501020609060411061303060504030c140a030e010302090a080106170d05031012060b 69
    0x1145420010488400004a010b06540c0302900c050600c5c041800820038087c69591114022807142c2d00041c0740a111007038100c850340045800791401e810200345540030540042000b81c802d2170918141015604210303044030302a0418a0422a407488081c5111321041030803040ca0950280c8640010312959503441065000680c3c0d1050ba45004c0e40c500000c1d80304405c650940035607040301964600402c420921b48000e00c2d502100d40321300e2080840c12041c0c100c0074858980039228181e0144013080c01d20001a103070450160586810b9031004040102240c0400c1158001e1401242c0a81c0d480c10a0403a5030320301c10050b000500707400e00c0e02c0280b1003095004a04036003400d110380410410801c0704010b45494407411400035001c1201d200e25800360398469401004483d4009088540c000d40314401d0b14211030b0350360062150f0101800440c0c510301030401c4200d0f8641260b14080b490740c5880d203551029508503200f00007048140206030001c00c8065004bc800681c0e02a0003007440981515111414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 729086834 1250 729085584 729085589
    0xf09041b0b091806041404050f191110110303070f09050102011a0402030c070f080406020f0304080c09042a180b0105070b091603060c1722060b0a0f 65
    0x650104032000070780c00040300190b51030041c00034825100d04184484039009524001d180079801660b03000003403114000740c072010303000d980600300800c401084c4004040c903180e010322522440d014994032060004400040100144406648081c400c0001c403006560480e100c0d811a0700e17270302010003000841648000b122002c00300540d80e102001ea5620b0044e42240c03400308000742c015091100ca1551410543c0085810400c11400649404490f850740544540c28000468442e04c2c0004c0400403142e0402030034001d00180700140d481e15107000c03e065030315442000545c2c0a051481c0004003448240136a012018408844401d040c00c02551600b0b0301c420680598a0540310a81980f21441c0b010b1160400500060b1a52803030300d0f5041c0c48000e001d803002418128507115803034441e01103103007241c00d0320010362082c5400301d0701c64000c000140c0032420500c0081c00401d00301007000305156000d0416429a49442461003031405d1604140003d031240c40341207038000c00000000110700d07124609a404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 729088084 1250 729086834 729086873
    0x150b1b060708090604061e06060e03010b041b140f070b091c020312130c060203071a060607110a050a0803070506160e010f0c0b01090902310b0f0904 65
    0x1180d07a1844000d032140300d810b880031000c0e0351102c1d001800090842c0d00140d2062104408074100d540da0307440c880f040d1031650700004009441d4a146034498202405030704a0410100c034180507010070711070040c2030000580c0f0300c3c408000c41c50581e814038a03a940b0445190002d0080d03820364a03142400d00300e02005e819260b981041c42043e4500011982c113001413030800c0c016501a500d400b800403501401c225014008105144410760200d00140514000e80d00408981d006141c4071006d504210350400310540d1460111b45240e000c01840e40d6418080724085607020303101c0020703407007010040340d40f0646e00c1c0c0140c1e400411104010800400000c09420024440d1b412514550307551800100e0701e40e803161180000c603440b081c40c030351158010034160804005034540301c080c0450b182c40d20000b004083e4000782c01b080c0d64810b040290b00b011314101151b045030452078601e8419a44002d51040f400800070090299101070860b125907804c1203441903104010602e19503424107040c001c110200410400302d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 729089334 1250 729088084 729088093
    0x6051003140a23030409021b0f010b032a030a150b0d0b130201020a060f020a1d0a0303030203090c0915030c09071407170711091b0d150b1b 61
    0x1071440740000380c542080c6034410b0b00c1080c8401e9403000e401c02e08000e100c000001d40010b00020031061050b1000c0c180700c1904c0304c4605600100400710a0a144c0451001d1165904100200499407400940c00290a5150f84007022003000c40740450000f8000000065260196129070030a03c1102c8134105c0e03e0300c075041c1040080052506c104a0045200b03140201030780f01c9040010209030f840d10200c200b160060060f5096528203640380303000c49541152034441a0b40c00b00f44900080d80c00380c2c28004081000c4070721014521101d00003142c41d4014440207003010b8002001440c0c12a081c0241d0303c02640282050080b41000d000c42700569000d484110b019100b4103128801d14a030040f001030060341244c4881180100c100303007160450740075080580700c07561505100340041c40220000c0c100207001d0307111030443c6070b8040c00f04049800c1c041c041000046d0703030341003040c600c81c0304c5000c640d0300144c20800064550b03a50702a00d40003030317400d60050749040c2001c540070110b0a0301e030140700319030900e43e015035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 729090584 1250 729089334 729089363
    0x403120c050601050a03020a03060507030902030a0515010501032310081f1104151209020a060f12020309120d0608030403080417070b0a11210703020106090b03210706051003 76
    0x4800303144c80041e41c00284040c8c10004100340da4070040e00901d5a1902003421710b60754000c01c0c900081c201c0e088030103030311604d0710001c096200250580544002d10f0240300f10095001c5103010302000c09448407112400202060030032003d070354244000c00c8a00242c40291249051500c101d0700c00120300c6586508050803450146180012501a0348030f0075440400b504102d1400c840342c1480c0001415075607981c1c888180540e840b400210014440750340c483c12401d111100061680c000400d141150314014001c0c40107010011500b0300a49040001c41e546030030420200da4060a2140d100400e58080094040706100b9000001c000340e8242d84c0041a9201000358440e9903060244940340b4036400500034814041e00c100941c1d07202c46200001c60304465548420300c040c1a1f0748a080c512000e60009a05080540a004680051001c03150800c26030305444086611030608210106001d0170300f480c200d40e40c0111100f5525001d802c0941001b081c81c191044544100490101b501d440c05c0391002c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 729091834 1250 729090584 729090589
    0x160207150f08060301090201090612020903070f061701050102120c150705040303021203011a0c010b03100c02010b040e0307030f1b0302010605122d070915030b1e15060403120c05060105 81
    0x641030003076810380d1016040ad107007981c00c035180030f4a0314410808a40130003a841c09035804100303100142400000143c03d8030300e00100604070146903c04510135644010040165030780206081ca40140780e04415951842c0642000e4107280000b180820704200313440901c450268003601800c1900d100e9022103030920800074000c59103000900c5a040001420051400c041044501070980c0044401c004126041c0ca41d00180c2040364107410040da440ea03030240c89926a9090040003151801510200301d8820700d400260b8981c401e15101030103102c440c015044a10344982050740c804546030b45400340d26041881c009000c1c100320b104039440b51118800344001e440010a900c1d11401c02640e0b102c802100c030088400c1d02c000756200b42403090194240005282d0f4890240c038803d9100603601c1d0800c1815440d054101c1c05010f0f002603010344206012802041044895903000b168480b162081040c1910020707000380f10755040101582203000b02c2d0309442d900140d5071180340b445181522641d07030300d4605 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 729093084 1250 729091834 729091841
    0x50a1a0411040c050903010e01050604050604020405091f1a0309010c0f0507020f0f150304140616110705130906050c0307020a1103190b040b0f0f160207150f08060301 73
    0x40190514900c074001c0c40061070543c1c00b5950103510341c00e085040089100c002400c650502c0301c2824282d4440007040030f281b9242c030480354840c0c4211000c504281c140400b090158000805207128107143c00080c1035030400c1100d440000703060900100000c1c00410609e10459041920021190340c20815550102c070701400c0d0744109840145d0314581000d140d90200710003929103076001c0340c1105c0c00c20408801a03c1c1c2c88201042c510000d03400683e0390905250400c2d84020402180d8190341004092081c000d010310105a419000c601d48400030407074100d81c070383c2810151760106501c400c1d240c000d01052030242d08003800d1780f4010341c81040943c0e41d4001607880380c8012100400181c200340c0381d4a0015502200b040301500020301100d00c0c00300f8800b11800042140301c0141c68804983c0d0400c0100801d000000f64082400394030b40700641082900e1418100d8040c0c180d40000d60b0000100c3c4615200b00500c400900503001c100d040030300c844902400520002072050000740c00c0d2000034542d82014003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 729094334 1250 729093084 729093091
    0xd090f05060c160206030619060509030c0301150611010b0a03110906041a0103092103240509040206030405150f160e130506130606080601121a0909010e0109050a1a 72
    0x143c8015440325580c2c2004065800200126442540441d4450340c0306078102d08180900b0f0b20f0303164180d03660200800c01d45050034100c000c3d44268103044034511090b40c46840e100c00c85400e820006055482031a4442c054000b1420356600b00002403000000e11492440c90000c5400940c0c541c0c100d91110b800b440180c915207840b046080c002040310b0409548039600030b8035250b010307400800b50b0101c6440382407032402181e048000069250b10320424042942c81462080121511001400794034000c00b044c0b070603030b0007031000c0c0c4510400b00024080c00380500c1403030798075001010010303654039201a0095090f40261406401c040c0d2802c80400e14a0048001180e8690700820784c101501c0600118400b814005282540000120994400d030f1b0303445005607800b40141e03860b44a2245440800181900095000c0754520307400c18818501024041e03041e02012623080e1307164490380c4d441000c41d40c098200c1040502c855071801e0700c440e00b84030700031840380f01082c407405a96101d42e1182d900129440005e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 729095584 1250 729094334 729094357
    0x210a06080606090c0c03160c030c0816060509060d02031f06021b0607030c02060c0109050127020f0102071a0304110d0335040506061002030a09030204050c0d090f05060c 74
    0x90041124000b144c005000803405107002c8910303140f0000c002e99080d40400c44200e801900c150340910810a40c604410090111000200b2035006209001200f6480601c035000a111001505002e50303128003080baa000010041c080d552418051000302c0c410a40748510f5901c11907010012401500c00b10760480c030505410300b003c54907614002041132543c00013100302c3c144001c1c5000440162204400780159400c9107000181460042c20042e0070b6607400e041c0c08100308d04001c000da8071003402c0280045130344d4041d07407007413811840c5000607850100317180c0082d04500d210b600404149101c0100551203035114284078040c2851060900c8490101400014045000c400b20940302606040700101444418002d50390710305d00650b100c1071420b0064901f900d81c0d401400c10842d0070704001144030303041003c1c1e00c02035161526000000f4000552400700a2186869070701080003070500c2016034002001465003045016010b2410800404100d00100c2d031a000e00400200d101d01c4400a80d01c0c2680310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 729096834 1250 729095584 729095599
    0x1080a11010f0e040f0905010e06091606050a0507140303100611030f03010320040f020a0315150e0105040b0f120f060d12021614010e030f21210a06080606 68
    0x620100710240031a10b0f240c000c1146e560b6144000b140090043c2401c20701542c000d0865800c01104140c10115003810900080e42d5444040201c04e900600b1035040e5810752510a8403400103140c0020141c481201e0070542e8880401444904111000c0640464006071500e8400e80c040d10322241e00ca008446105900b8075003800108041f030b044580704104072500b41c03aa005003001030000030301110b500f429139184e11903001c284012482d405200e041c900d481d088e40c40100162505c0180b0084180f04503e07402080b0380e1182d0200113900560540b0080c050701e0f1546520351051111a000c55008010030b0000400c41030f0104852140a01e05980601070240450b032000249448071071078070030400000001c40c0b1900030715400c5003509143d1200505982500c0341c1d00d220080c400101005116011248217800165003c0c038503000014001000b1401c59103030f0410394160824001560164401c0b14204200c0c142400700e24a101400080c410980300340e0070031099484400240d947e44040740e5480d00501c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 729098084 1250 729096834 729096857
    0x2a1b010201291c08031512011803030c0201111b2a010e0a170c0915060306240705010e070b040819060b0a030f02030f0309011403190501080a11010f 65
    0x60035001010f200076242c8980d0000030050303440640d103034421160040a2050b41c1b000c01810700c2d042c040e01c07440c0f20b4000002e0105034044c03005c46c010440b1820008048c183e0341c00100424034000c0d0000c40c4226034500ba090340b00d400b050800424090100c00d1207095000380f0035080740306080c01e981c0a020a28890b1a0110700245600540c2d500302041e0040c0d40c02044842d00090403d88524001144107900c00a440326000d503105001d55410044c0c901c290503441103103501020f44a41054903030041007180d2141e01082c2412042e00c06854508032500c00c0c0000044210234800c05400c84c445d03840f150401c48600ea45e60300b031000b42c507001e540071f0342e65680c02c00c9084031400c280110a003071190703008a400080d00000003000031050703030b1198800c46a070100d0b020140b05500d010305c000300c920080c40c1c019500c0c110a07500024081c1e02d00e404141e92079040800032480e040c500406081c030110340c0940030000d80d40c4034500e1682e1f4410079981160031405a191044042d44121310312801050144c650000c3c550 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 729099334 1250 729098084 729098089
    0x11030106120605060711090108211803060403050307080907260708250b1201060804060209040903030504050c041e110d0204060807110706052a1b01020129 68
    0x8400c940035045090700d5002c00f05495840c0c0000f0945540714080000e0603114400c144501d07040140d102c0c0744c60340c00c03060412803052070a00c010041054171040c03003540c40668412008200c070b86014541c2c1c041c0324403c00c010415030000000d50080e501922500c00603a070740038119940305128010046400e605440c10024001300c050550007080f4514144d074130084d03c0e0902589040c0054103440da180d59504a40c0d000c200e5410103190241c405401446d00d440540341118102401c180700d460200482d01c00010240101e6a05075410094024406c0c00780c1e01c20b82c1402006064207480a0b6514003540000050038a03040c0f14807050340c4080343d2184400071890700f03644010a2a440a04100f840070070040c3c0a1342018070040c00540855200d0318090304128000030b1000b4040c1c04440c0c1d01d540301000a100311174004041d2007640314207141c98140c0030b0f9100503584009410380500400c81c842c448040383c48150440000c20000e80030390080200c0012100c0300001981c56010010541c10b100d90040c4150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 729100584 1250 729099334 729099347
    0x11706010f0b12060d38100e090a08070b04060506040e0d030b01051e03010e31060e0d02150702070303090312050c10050615030103080a0c140f03090405010911030106 73
    0xc44c01414106a0b010303980354098060341c1344942415654240c40c503100c076400710306502e0000f4180506100140c0c54400c4000306405094020104805482400540c0851080000d2030b00140d003d03074201e84410b203d14004a0b525003e8070220b03081400e180020b0803074100380c032401507809203107001010810600e0006800420b4500e03c20b904003c400c03c20310003940d01c0503400d800510b25100d5125541d600d850025209850068900c00e150101500d19011590050307005000c4d001c1c1007001103954403034a140040c020302c0081500502d6008100c2000704440d004030340c1c9512401d156100b040142d9942d41c04980f521214003009000c1103c0c2c040034804544c0c020b1001c1c0100c00720b0b0a2644c68980e03451525450041c0104411240b00e4580307042049a081440405103a107000030215030455045960320032287c056151030000700300c070082c420b0f8184142102a040e18a602405540c3c990160303030301301500d940c40b40c844a8043c80c14480009180020f43c13092410359281c4245003419070342461803c6440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 729101834 1250 729100584 729100591
    0x7081201091e2a09050f01020c0a170106030c120b060406080a030e03011103040f1406010b1615020a0201060e010e010609050111161725060e0102010603050105011706010f0b12 77
    0x102c621526801d0300f0600000410710a2156500c070111010300d440d003040340c489290907030181150001030742c4050541300d5818110945901c020080700a450b0f0302d19035030061906510161a10409000c0000c61041c3c4610b07a2440300c1c0982912070300751360f81009000c01c0e59401d1050075502d500581c081000f0a101d020b0085008000500100312407600007800c101503041600c0507106038000300014010824150300300c1c403120304002d02401c001d40c908414010309005610301c18800440204261081008070014050402113401046480b0100020000d00820080c050100c00b1800c2a0010460303d1a410f04075048603155603803596502d050400469903180751100c600d15910412000d03201e020203005401c0060b000d400029013200c50403242c110302d071000945030107200c0f2a04501c6100c182d07502d601440265001030415001300042030740101d0040603182d201411079461b042c00424401c04000180300c565600c2c2d01214000c1c0d0300c5075a8050322030254850180c80c0307541002000505503241c46055032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 729103084 1250 729101834 729101861
    0x7050d0e060a0302090103090b1e07030c0503041217010e151905220c05190e0f01080907080601080a122c0d05030703020d182702090607081201091e 65
    0x5144848e035595020155064401c00200310b000d50b1080b0802084403000c9a00c10342c40e19080c00304a4644a010700340f4440a4805010083c0860302001014000c844240c100e20010f202c1e07401640c0d6950545c01d02c4c001c107584864a00250000f5074102c4d02d4603040c0c440c00303030b00e14254802c0514901020070004801009181e01030440d200c460034050340c510310441d44001b032103031581503403180c02c0410040403544c00504d00d400d00c110505101601d80b103031900107209000030b0806265603103580d8103d91030039080c4e5106810900c9503100110344041c000c9101c2002c5440703001c0c1c95050315000201a90000c0c01e0882070100c00000074543d680007204000740d0381e07040001030903049441030241c44450075980b00788026400b40e40440080340e40e10b03034440901c4d4081c0801c20b0880001d0b90421240001d106445003500078142c130f04a000c081c40c00d41e1603048400b1030400920325562a03100345070000d40c540096150300380c15602140001803003503580c02020b14819450310740c02c1c0d441c404803400000500d0040755429 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 729104334 1250 729103084 729103091
    0x60f1005060a02010f06120b060f12010e0a110102010203042a030206040305150a061a0c0106080105040f061b0504031b2d08070b1c0b03060c07050d0e060a0302090103 73
    0x1a03903240c42004010035030459001240a100740304180c0c00380c549590015803800c420308940000f2800e41900c0940202048a5501c0b407a1a818000b80440d08038410001c140d518150760700c0300c120b00c002510303510710b840380d101040d2901c8080c00590807808102e0340904213051242032407110384400c09a03100d051003c080c3d4444042d40b250049401604160030486440c0d04c0b401140200344c22407600182d02025000c01031001700d0408840e6035440780d072a81500c1a240000c2210340f06c900e02034114202904a42d0004c119503e402e0034480000c1140c2c10b1b01307841581c5010100440518000b041c8801c003502e0b0b0b211a4130301460350341d504060030a40503a04210302c0c2d80d5040414043d0601144900d140c448404610640311544240d1003040d465510030556503021000030885420a00c080c1c0e41220100c24400c0c1c101020552840080c117603244450741c0c14000c2500708001141d40002902c42c80b8044c0f4116880f03584403078002d940000900850550011381404804170f00c61003600201081c00d018074020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 729105584 1250 729104334 729104339
    0x30f04081c020a12091101140d090303060e0a02030708130206130603050a0f1e0b0d0c0312080f0601140a1b06060312080123010c02100306050a060504050102060f10 72
    0x1d1a0390300500301c0096403580000c0d200740c20b1940400d580f042d803201e0341c000704090003842c1d0340d203c603102800c2c2c0c807541480500c10b11104258101e8041e914004e6031040700348025852454014001d00c0c0c5402140c0520944001045010309584240c074440d026549444c801d6841c0e00366284256110080100e03070103a000c00c603030340c900c0101c2c80700d800c000d11440c0c0f00030a05040c94a240070a0f2034600c040181103604d0070fa04e045500002c0c140b088038000180c0070008080c03028001140300d80100300009400c8480206000007001820900c049140b03c03140c1d6007036030588810140c00e81c1000252010b50000c1c2c00448024601c011980050407401120700745241c00c0c20104803c081107502001042c3c030310581c5ca8004006001c405400401e82c0d0600b454543d0166040c400c0e1495800c2a4000947c10800c61480a81d200e034000e0502c42280340e00104411240c0d209542c005014042a010300b80c001d1464101c000381c0540114295410303180144c019040c80e13560b220300d40c050158001c4c9501c5c0c2c02085200700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 729106834 1250 729105584 729105607
    0x230c0108040f061b0f14030a09021c0f020f10050706050c250b09010209030703030315050a0314100204180905160b1308070f09020d09020604080106090f050606030f0408 74
    0xb0b444009184a4044c94602401000500840300440510b010310070142e040d0496080c00000322940410920360000b101442400072860700440304440c800710038081d01d200420b1181c56100c401d410351080304c00c1088095240140542482035444913001b040c000d1050303600250380d5412550f403280110a402d414800b8814461154541100b440142e030400c00794604140311348001c40c6580011403a00a61034100c072940031941d9412240301c003400301039480c036121254a107080c407108000c280c0180080300c03050700d9041030881c44054104403c0316100d4100000003da03914020341e0101c84d4204115660b511a04052602070488070078125014000c4d04415080b004022340500c000d480504640ca45800801c480d840018007030b0742100d1220b92046408001d210500748091055a0402c90b000d81c9441442d0102d1018080e0760400035032004000c40d004c10702500c154803110480b04c08440a001e400100d04c03504e01299404d9034002e410540410024885550244401d504144a4110145442c034034214 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 729108084 1250 729106834 729106841
    0xa120519020a050901080a140c0d0e01020f0901030f14060409080c03120601020d090b04060c1a0403050c0106050906090c0a021f0204050a080d020a0618051009230c0108040f06 77
    0x241804200b02013548a440c1d41d01851495100080d10f804002000100c1c81b200d50b1000c00500849100342d001904064146068001510042c4e50000075502e843c03003440110956001114864002417074014800441100d0780295904000c0602c1003600c40c4c2c0f0f4900900003c1e1004403c1603800e21001c1040401c6103a08100a122804040c05914800d00b01107000909061900384003030700308a03c101050216075503202c2240e04660722410521410842071a000303124801c60702e0441450070701300c2d00700801e2581090003084503007100c2000b0004203480702c0420405840903903a150304241540f00095100344000b00400c8085402d0040b2040c0ea031408829261440c54009903510305500441c1c1000325042c585132003005402038030080d007134014418070000d5a480c020440a85810b8031407030780c0464507003262000000c40d5044000d4448210211003403e01401d980c42c030881e12044030b001096421440031f0004090101e030100039010301c000f58030046072210740c090019140e41c290558044005501e0b4403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 729109334 1250 729108084 729108097
    0x62e0e090a050a06050a030803010501081015271406160c060c120504120327030c260d08072d020f0c0a060c1e0812010b0a12051902 58
    0x90100780b6190004148094403c0c59205902491080f40203100081e101e0742070b41d054072800e01e4140d13410303540c0b402e005502285640c804220285007001100c2e00c0703a40184402e02d0b1460070b40342d1744190701406890070b110306410f2080f403098104500200c0f4091510200130000c4071480401082024841e8640c1c00209007641d010001041401034000100195078400904210590904504161030940c40d4070006a42c00001420800d01100707103048000c0320200c0303800f001036001940415948a01d4680f184240794005d0188001012a92600d0b0050341c01c8806808800d22002d010005c5680e44259850344000d0100c90621190351000580607940042200c10b80346410a514444010810003034103103102103c1d09071058000f80c1281d450743d101e08407842d0032200c2e1072410944100e601d0822003611000300c0c480c0120410500040e0088c07042c0031016041109035064404c019036642c4211445500c1030080810215206c0b1000d44011211540a9948041036402c1b140c0351265a262034403c036403224 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 729110584 1250 729109334 729109351
    0x4170a0f0509060723120306010e0f030f0607020f10061508090102120705090f0a052d090f01030215070f060e0f070605031b070c030209061203040f030b062e0e09 71
    0x194621551500304010358860721003c1b0b48058950b09013400020f059042c440c101030f006468106000c441510708000140c05036030a801920707010704042800075201c107083c0407101410b00c0ba0b911800d0001d0002e10400d811079079244c8505d4030180048400f0f4401c080c000700590101c0d5401c1c01041540a485c01101e4418082956100e98801c407000c200b200c44207440c444a40103542c600024003903038842914154141d14840d41c40c2d04411025800f00714030b602c0c1300246a030020910010312210070183c18006040e81d2088650601c4120a0f030092800e501400d10090302504080d1030030408640158060700400c504441620380c01e00f41c0e410224940282d50340400c0000303500004000c2c0c0401c10f61840004128500c00070340c50302d602e46c0c54070f4600390000e000191003030400102265055403030a007e005116100c0342625150f03580d4544104803c5070700e00c42521480404400034009180088220401079090464907000d1203003402440380100504c0c2f40c0c0740501041c0c1d8803000140d0349547c000342c821000d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 729111834 1250 729110584 729110633
    0x6010e15011b050624130e0f07090203010e090f1b121f050114280f0f0609050105030f130c050312031006110a06020a0c081204170a0f05090607 63
    0x400e4000c3c40704c0f280701892001700304000f1102483c2d603640d5942a1503455814010a20b40d845128803070612682e903030010101e1148040006005680d0380245d03040303940e40d0300f10119590700e070f02082d506c0341c0311842010410f8008480d50480f000c910326024100c02005404050800740b00c4030540d250805a180290854440c20030002480486010f12400b4280c8007281c01042e066100c003192000c581002d8840800004c60a80c603581d0307154520020040100d0310400c02c00b55075030704031440507031054013604001072881d40c0045030f1075008400b1a4000e41c401034445485580c1c11708032803a154055441111400440c01000a05d507030100f21200c059a04004216501d04002c00c108035a102d03035501c807009000c0c0281454180c4040414864200343d0440030269036030030310400442e450440c0d108010500100031403c100d100b8030012a840c4070703d10034400b240c02c074801c03820009214080c00021070000751070004221049072080e4041e128a4002030030280c00c281d0f40399600c21883c00301c0b44260400044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 729113084 1250 729111834 729111841
    0x121b030a020306040c111005151020010204030f0b1510170112031e0c060c05071a150f0d06090b041e03171909030206010501090806010e15011b0506 65
    0x5003817058141c4600d140c00e007001070500d1b09642030780b641d10340421a40b450b50f84000044050000600b014034101c0018031501104c22000701c050070120820341188081c0c90004540d103030400c3d0520031a010340b80c000c6815180c09001d551a02c0380360394020035031040401005048940c0d92185c6840080a042c1c0d51181e00501c03d411105d45200c1005a200c0c681a25001d13028401281c0c01051888071030200b0b0701850f1000c1c2c4081000e1fa0100c1a12000504042c90b180c074200384164003002411466200d0481282d181c070791280a15100081990015107c42680845400d1860440c20788444d0007005010040070710703155281c080c02c031440c03600180c8100000404100411400da00f000003003501c0382a0521035820162001000d0a81d00c00a800c10381541c040840c1d01480d1750b00d481c0200f040f09243c140080d0941c3c0c507000351103041c207100300c0d07000c106014408100d4000100b4202d060700c3c418542c0c40e00c180d1303620320303580c8845850001c01414007010312403062441400c90b0440200302e020310000d140508 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 729114334 1250 729113084 729113089
    0xf241509032d01090f030e19230103090c06122301210803040f11060a02010f0b032802010302040e01080c0f0f031903050f2802070803121b030a020306 66
    0x307281d00d00c103050036458104d500e00002c002103104201c25815140800403400a40c0c040b82483c0f455080100d2074140300000001d071441c03208640384042ca44407030000c0142da1240015802d84008180040101e100404140000c0d403003030f0340031030a83c1c0f41803a01140103081c403c034450a0b562010f143e0a1110b4a640c0140708122103800d01000840314503071600485c2120703440d0104a0300024000512450180310042c040c803c600818811800300100306546d2040102c00180c02001d11003034020340c0600f0440b620a15240200b098040e0382106d4860426001101c8000381d160101400f0480c1450f40c00d000c0400d4030526030328568080c0003040e0017890419003e0b07040081e100e075924909071041540c02112182c584012824521510f850002c4411035070b03551a05548500451001c0c11380340402081420603c5044d851810244042d00d84e40d801c3c03c81d80c0d05040b622400d06002d459130303a900070040d4541140215072101c3c3e108020340d02184c9400c440900c0004141c0c401d50b078010f401c40c3c022081c4292407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 729115584 1250 729114334 729114403
    0x271109010509070801141f0309060b090106050f1e0a02070f211101140c0a23030f030a0216111201150b071407030b0f24150903 56
    0x141011901c0c00340514203e140200070700014003030b410014034601000c42c00740c2c1301c202640e50a10051074032503d58039144036009000b85a50345058500e43d04040c010303a094205500c0c25810780d00180c0e9001d00c2e100c0840412029075003c429880d080080e1048400c6440340e1050141c004107110307134041c0100515181c0480c03002c7d890f503080f40e200055a103030301400914000441821076036210501c0c0c9040d107000b80060b6030000303242c50b02d200e003c82e0000d0203140014011510110f514850351a041026108402150004041c4164481c2c40e60081261101e48403514000e5544403480481c09440c291507011400e8001d0000241207654000080400c841458002240c0c0c2403811914001c014002c026001550003140d18420681107143c00180382d4240001c0b0400c5100d0a85940100c1e041c403560703843c102603645402ca0b05100c0c0382c1c480364081042d075070464101c49102448202ea042344145c80d00104500001440000e0000034002c0008000b0364a0034003000141e110f48041e03690b85821016000121f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 729116834 1250 729115584 729115589
    0xd05071d0a0e10051e0a0606031a0d14031605030a0e040c121805031b0624090c040332030c0a0803090c0d05060601020d0905010c0627110901 62
    0x1c0074100b034600555004000b810303900d90008100041130a0300c600e1864031641302c1510300003c2100b00344007006110301140e04400101c0d4802d43d41000075008a100700e00a900b02150b0555100f080410f2030b00c041000c42400d456000389030130980780b0300780344422030300fa1000d0740002c1202e05402c04070301060065040000b16a1128084c0e405000746071a0300300040401814041280005a0b18250306000040b0b01d028144919800700840c2d41d40e0320410405104040009443c0c01180b09810018a444071294020700c0c2480e403004141801d20000d80c1000b8030100c000b0944010b0450034803000000c1007000d0700b045076201081c0c0d507002016507030400328200c40300c2c2194661065401000b071100320050004040c404035400c090501e40700e481d49040c1500b003150b01e001d0940d02c4403040d20359006008012510502400c0241c085500000d400c400c141c6115495109160110300030f094440042241034005c1162080100c210000100e0500c6104450ba01d03520030540d5800d010f5408040c9034200001c0e114003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 729118084 1250 729116834 729116851
    0xc0304170d1b030c03030c051b101104050a0303050f0f0412050c061804090507080d3b0f03010f0606021501080f070b0d091e0614240d05071d 62
    0x141c00800f51005010015007210080800d0b03903c50580e04111310400c15030320750011005011b060b40e9000041c0a55424120303007440d641030b149c810b90440340d514500461f02101c2010301035079030300c620b5610190340c150080b65240084040400001000aa03c94000c001501c036490340c64449400b0b0b420003900d00000c840c81c082c001d2004220b190b407a4100e4900503405e45000300e070017003194010f0f03190207070030100345601c40c0c440b62061031074001d1002e070000b032103003805102420b107200010702090341101b2035951000e816901701c2004c0500041414003810b46180b480016001181c000320403500041200d00e0340e4410b03c0103810920401d00d01a12030760850b07004125060007440d5406115803020f417a14003600c500080f40c5030004845d00d000109410484010360081d0001d01c080c01c4c039002c241c0345100d925004490161a05100c1e0a805c0c45541d06140914008206280300c558200b01e80c09a042140c0840755112003034118403000660100012000341103c1d03c00c2205044202e8100043c10402401440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 729119334 1250 729118084 729118127
    0x10603020d0b0c090a03230a0b15030715050306030f0d17060105070b010602030405040c0305090706111204142d13060e1603060602060f0a02030c0409021602030c04200c0304170d 78
    0x2230202d0b031401003045c1c0104075460300707001405a82002a20f05544c0b540005c0b1615648070214242c0c0341c215016612404056054810f06003903103002d1912090170b80040310200302c02d181c1c110b05408268070703d5503208006041c0949852000c0d116440181e009130310200040c2e000183c2444142814011022400a1400c0030700140c14a031030344a40b59201802110100040b042540c0050803040004040c91002075000c1030340e868450301c4800031000009422405a048a110360386c000103000c091038840441100d0b42e10400c0f106100300f0103811460b038003641c40c241d215240403400c6502d400e01d46008035132903642d86040800100d00a42542c0c003070352041055400020802c10b04c0350340c3d200500d5103c0341d424801a40c0f660b4891060020780503607004807160510204001d140e4001126540d07507158022411103140d5400081003000f52481e44e80c070301c000c036001c41c1c46001d50b103804000507060750580f0005903800c0a45a204059102c0140060109554440340492182c80d800100e60b210300341e048101d14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 729120584 1250 729119334 729119353
    0x604030311071104090f0b010e010f0e071b0201120e033c0306180702030705012d2703090e0c0a0c02014d010603020d0b0c090a0323 58
    0x80c12100042e0342d03c500076500e4101c0742081110896009a82ea94440d40148082d6119403001800510034010700e0b1030500100f00114a1803000100c80340300d510256102c8140450540d90802e10b000c58a40490600a00300200a40b2400d10f0040040868060300195129440d054520390420301c102100c00b00c04100b807194010f41040e8000d0604240040303c036040e926180e42c4003041306d80c0c2d0383c08401402c04481e80240450641c1c044010495680904001e119105070665403c0110304481a2510500300fa800c4d42407406403217401014803242c07131000110561000a240d01e00020148d00214002010f900d4140040d4040f92800b980140103406118103004200e007010303006105004000c0e042c0b000c241070380790155151903562040a25410389540c80190302c074004525221312a221460540c0c2c13000700d01121410144158803c6940080034110b5002c01521740d5544000040d00000c170380c081c2007020310103c2c0c0340c0ca180f04d4002c511034080900090f0242c0b95040c11f150000409001ca500001a203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 729121834 1250 729120584 729120593
    0x4120e1302181008070c1403070b0603010e0105060906100314090105040218010503100f150905090705010212090108071106090a0605060108191814010b150309030307080c090d05060403031107 84
    0xf45070302025900700441b4402030380c1410000740d5000320aa41c50781c80000740050800075402c00c20303802400150028440490440e0b015400c5e03801c01c88243e900306d030207038000950500d0615111590300c1954100000c40d01c00302c00e0400001c080072100a68980e4480f0103000c1142407811070b4807555010b05400000f59414600001c1e142e08000240080c916124130540c007541032142e000c3c503c03589900c3c0d002070b000390f81c640e03444024140450b81c4010f1409030b80d50000e030b5035001088401504241c06c0000e403410b8140c100541c2d050724081e00600801c0940c02800c0d4001c02e007002483d010301070110050000004c02c1c079003881500c1c00188850304101030310301849007020162080c0048045582400b2410030b90581ca44104410130003006495644411241c00d500b8006502004101c0000e942c0c1110411b10112109020b110544030b00f89158010000a8806481201001c0c2c01400ca032207060303e4030803d24005904400888803c4e42c1640115041c0010103400d48107420100c400603043c9802c002c4240c44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 729123084 1250 729121834 729121847
    0x110f01110a120813032102040510030f0e030c0604060e01151d15010e040e1006091a0d020d0609020f06030901020c0d0201060b040b090a090615170f04120e13021810 72
    0x386c00e12645001180c814801c0302c1c5d501030300c028000103492a800709405000060290400c009414510f0b407816481c0f820122000c0b0480700302200e410000d02d07490300d40f5031b104002130204110041065503108003500680701034801c02402009015641d6400503050714a54408800152880e4161076406140c100e0a98114080c0d682c1c80c1e40445002410107044d00d0310354141801250f03210741c407a141c90004506e40030107602841414030201607c0b100c140604040c40148414048040e6001c103916023000f0028200f50002c3c80d03500d1000d40349031030062030240800c10503001501c800c4810b0f500800c414410003002c00c10104002c8252001340061803920307030140300030b2049020f5184c1226002520540c45e03110003006000503c0b040341c08100241e990240c076039040800207001800100c40e0070710343c80d42a40b02d081c400e000303e234112508003107510380783d03034000030090210402401e010700c802e003a415540d14031141240228101002683c1c50107543d01e10403041c0ca11002c060321502103020354800c0154841c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 729124334 1250 729123084 729123107
    0x100e07121202070305030d06080c040b0105070803041b03030c02010806010926010b0a030302031921020325080601030b240f0408010e0102041809110f01110a12081303 73
    0x111032a9948403507060032400d2558982000d0080d1200207041e2140c480c007a4451000c80b450386041d41e60207004075080009403054240311070b000603021310480000c01c2204006582240c4910324005110086903c8807080380810744c030940100f42c10035400d00644d60011110b551011003407070102009810b15100b103034180c0c0c1e84140001108043c0002c072110710403d610002d6071140007001410340703940d030b498001d5480c0e2010010410001e1921900303c81113004001c40c40d08403100c58802222040400c0135034000b0340000389046204540500354070f6080200c00540ca0800300b10343d60b5250249814000501681c5107100c1e511b0080e50400d10036000f030360a80b2a004202c1c1e080c04c1c400b80e0f40d2049407500744054007541c2c1002c08254a0107024589a00e01540104200e441c880c48c8030314043d462070062030403540c0f41e60b40540030350001c1c1c007410198545101d5065440f00141130103610000e500508602d800c200a808807607103840b400c4c911071f0a0303800c820032650100038050400d100020075900204681c3c1510b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 729125584 1250 729124334 729124343
    0x16030b0a14090d090608070206160306031e0605091207020d0204060314071409060f010f0504090212090105060405060102100506130c080f06030f07120206041502100e0712 75
    0x400410100c40035900905412880c240c038244240c00c060420795100d4500941490102d0441200000c01c94068980188210415006014280d5840001e0400381d81c200200d41d00700742e940d603804800102c200781034007428280c5100c550402c0c0003901d040070840358060024412a840103201401695030f0400b00c1e460700e60305950301440d1781c000c0e00c00316002d4901d94000800f00b18456a11000240700091100210b406c0800300302100590300d000d00081c01425035449030031900c42c0400c2c1d0400c0d4082c4003104d014036002d150a40c07425640c1c02c48481281c1001a0307040c0c8182040091261446090041640061003104c0030801400d003140040c3d502c580007007100407450748802c001041566601a0902982d801d039400340001c943c000030003840508100c94000700111682d004ca119814000345611080e95500010034102d82014051540026142001c0364045000c00001c1038044012072056110308041c1c00070010001c02c00c40f02811340c0d030071034150340303940d88000810000c1c41281c0701140c1031a41c12 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 729126834 1250 729125584 729125603
    0x2090109090203010f0614040e0f0a0b1009093801030b041103041b1a03160206010602120d0219020a02100516020f0409060501030b07090b040e0f070c0b010b0711031603 74
    0x9941f4080c10700e001e5940304060100b0000100240e68181d02d80081c8a10a018402c2080450754030400114040301020900000d00502050001c204981d02c240c540709020100c0c1c0b0680011240040100840c0e81b034541c1200711404040d50141d41c05002d45484900308880c1480381000c040d2102e4410700000f0320207010184c40c200001ea010043d4041c0e100904000d4104401c2e00440c41802a0300d42d2007941d55428a0100e071600ea540107201003643d82c1030f0781c080d034007404100100000c14011600406030507004c0941c2000440d1003086503c0e04541554400d401a1007a08502d00421941d605a11406800e01030204007694800421400022005904036175100c035281045011400400c40e00c800100241c2c0740000110502413600c680302d200380142d580c0c1644c102d0316800700c3d0000b402644120748501c00a031011402c01c0340e15020a580c030035250302d080e140008031525070211030142a440300144402c005120024040f10300d4144c3c0020b5000c0d0b000340303540c009001031540c10040c1f5201c0078240788078 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 729128084 1250 729126834 729126857
    0x180b060304030e0117100f080f0a200a08070f0806041502070309030605100312021204031412130807050a120f060e0f0c030f0d080411130c020102090109090203010f06 73
    0x10304110b0042c405c14440c2c0d1030705403401103e02d9039030140c54059550000c000100c001a031010000703061000385c011201500b55040d40b03035942c004021298054074824161420020540d03103440b1604402048008002d10041d4544600c401d02d02e507040c0c0000340d4a803c21410000030403c042d02e69400e01c0e20b010340050f510035182c1001c40b80014a40c0004140724240b0003481181078070604800b090700d002d4001c013403074250030070310aa03641e8002210000ca015000d11040002c218800c04a0711032042d924141c40100e0b9810421050700d5000a10580324041009820300c985c0108110090251070203032a00c9180905018510804204d01d140043c01003038000d0b42c2e04100700301c5030801c103401103041c41120b466940d61542c280e120750805190381d020307200c0c0300004c2442d6100050680651388480d203034008152501d49440e408050408070301e0350024220741d81d1401d01c1c00304d40b160b0b22003414070f54001a2240e084000041842c2c0c40c503030107115001c0c011300051012070500340e030b02d8003207511038105000c0d40c03003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 729129334 1250 729128084 729128087
    0xa02010f020307050702180114090c120f090d0f0504150e0a06090305060a090209070503040f080d090b090f06060f010905040609060f0801060b030402090603010b090c04180b060304030e01 82
    0x503a280d406505900120074840b2260300300c00502046482141e03661006050080c5c6044105400d00c2101c828411000099265081214965411540f440800340c83c04000f482c185c0001c000a41c1c41c031b071581204604001159900303100850050616280150000c188110300a1190183c3e01a03455121111b0070501c5100d4040d0b030080c0f468260152240b00311668901002e00182c0e02c43c40b0170740c0c0c180140300c001006140d651250700e00440e401000c00000380c40d080802c40311908024011110030402e05a910f01048603400605a5461840d602080300c994074500119000005007062883d079003c0c000c802c01020307000c5415588094282d400d02c1011800400483e0010074550007c1e41051800d100402c01c0102600a50282c601100c1008407040c0e403288a82c3c00c0741c91a02c0342c0383d0301c6141030001c50014a000c0da24190812001000070403481c1c0e0080000d0311402c0f05548d040d6070480002001c101c0f1080005c0120107c8008500c03c124403020803021900a1100600040c1000255591408141e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 729130584 1250 729129334 729129341
    0x1801031508011d2b0203070f05030703110a02032808040b0d06150807123b07140909030f04060c30030b0a090f020d05100302090c0a0201 60
    0x1100d08038860340240e54508040c000c00071109500b142ca02040000000c0c400001841513140b20510b00841690303d25808464440841400300f0085002c1001080d0108040034a0540e0460003007000d5540d92500b03113805000d0010b00902020140c10a00010026079000701d020b0310049020406000800301102c0f40b00240756410b080206503e00125020416a440c00050089422550f904001168507450000c041402070082c0600150502001030110791240314244140d210000001c5400d6140b100d80c00076295903941d404401100c0c1600403030b80d0785211040710506400d0780024020144c2011030f0b807000b0340d450007400340c00782607044081036543d80c00708116000201c00b000ca20391950740300d0b00010304402c00c080c3c05940100500107060b00700701c13642100da80703040510040071452025000003030740940342001040342e00c00c407840c2001a4034900ca01500941c6040c840d801a52810401c401e0011503a0142c075150010400d41c00a00060b00e034000602d403c04c07048140d440d11165450000c0303014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 729131834 1250 729130584 729130601
    0xb0c0415030501091d2509060909020103051f0b091f0807080c0a0905010e12010609060e13080a05130807030809010215071b051002030f0108060a11180103 68
    0x12500c400d8200911198507500c00740c16612004800e03c491200303203a1301400b0302d4a2411440e800d4202000500050880341703901004489008607803181c040d0b0322804d8004a4046604c050400c030388a800542c00c560381032058070380c0080001207402070644080500303038003e10b25014510481000050b170746032907507504110646090b04490b81c9404101c541400400180059404078045040080850701034a00902542c0c07010311242e803050446031501c001100c100400380405500003031229400b08440070203001d2200034090121002c110740e031a00c41007030440c010080c8505003080302c03220408000b511510403110361904c9480c0c040e403141ca4044001e1108a410350240d07000d4410900d00200700100a0081d04032000309800750b5000c01d01c44000c40f400c600c01220324000080e001501510200d0205502409081c080c4003200c400b00c800a880404903842a10705c0d83c503008111004004218041042a601001c2464280019000701900d5201030085006013115040c10f00301509103030348207501c0043d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 729133084 1250 729131834 729131849
    0x4140112050103081209030a05070308180723060403050a0204050c21010321090e0703090804140316080c0409060e060f060a060905010905060f1b0709060e010302010503040b0c04 78
    0x703950b03607881c258003254800410030613600714010000726081d01c04025240725a50a490f898549009640d0440d21504020030410340c080d088003a08a01000402c9140083d001c18900300700c6031080030380340152400d440f00d0414428a410001400021000300315004900d905076408122a1580b80e41134419008055206800d12407003182c49480c00d26030100301c1c0c1268011255103142d003e1000e15946d40550b0100c4100115500100400071807042c80001503000c085460f00090490361562169007175402030340489241e802d501884c44003403600703000c603151141e070305844207454501e0041110349603010600c0701031146549981741418081c0e01d4010b00c281506a20945040f4035045200da601c0141c00d44183d800750340d89900105000b1300a041c40c0056890584498944da81f50108020081d40425590420075000340040224004403608041002e00b04c80041d0001030b0911450b801101e68aa1008441c08481001040540d8101040303d0300690000c1c403408256940a003040054070030380c4c4c8042e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 729134334 1250 729133084 729133091
    0x2106020a020307080c030913060b0a21020409140106020715110a0f0b04060f020301180207210908010e070f0315140c0405030601090516050706061e031109010b04140112 74
    0x80c10120007011140c002300d940018030b09840150100b00e901c54011541c10794010042d03d10014010004000fa10610f84143c60764208007140038810b80e04a5482254140e84234081105100c0045000034090001403000f45405131801800034a54002040035006000c441c4020000720314041c404071744003d400940203001580340e4549100e1081003102d00344c072051329100b102d41c40b01905000300d034101d0701c12044440c4030000c048202c0000b0350180307604030b80303104180c612000050524078025040102e541c46260320107280590707080c00d5621180c02c2c10415086441d043c070002ca070701003031007050f41c6d000014040c50013204643c44c002000c1400c5003000c811a01c9003080b0504800e0001042514030135002d854850b643e0b0400701065401c10b03034241024108408100c140c99110304060135419006040204921380c0d10a640129080c07a0291200300e02c50044081c01446002c1981800214042d80c1111282d890001130180600407800b034079102d8110b0544c14806a84a4a02030545000405040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 729135584 1250 729134334 729134347
    0x111002150f0f130201230405041104060815090c0705030d05012309060315100b07050105040c06080702060c0307050903070b090a380c150405072106020a02030708 71
    0x104184841121902c5000c4407900010751074542c100c035012078055040e120055640c01e900302d0581450790580c41d00300070400030310002610355120b020724001c03a058144640d40d600d0a0403402449403800500fa0b11400704009400c1344241c84603580c0941c0f203044400900d84903501890007504500c9103294000805081000104541c0605a00c00034240c5402c04400c000f0130004050110388201158a42c1d0b1640014107501d100619094009601401c15120b10f221a91030345800301c817940101d1400d8840d0382d51181004108144485403101504050400c01c6036440d001300c0080d5a2080201903403100301011000c1000140200b082c0d890b075410003401c0d00d02460311100c86012580007000070502c6110541000a014010829010305250395010b020000980c507125084810460440c0a003032050700300481581204280110030250041c1c560001c02410b0a041840c9004515002040d4208414000100c21101040310a01040c5d00c41300141e1240c041000c04d905500881d00c02620340200068807 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 729136690 1106 729135584 729135601
    0x12190c05040b1b1606031404021c02040f0603150f0605090a090f0f03080417030603030d05090f070b13060201020301180203130819030608060411100215 67
    0x310740000c0304500242d49001d115051000499110200c28403003191b150080410158006d01140403608050300080e815200e0b1b542c0ba1406c580d06800c9120031510369402032122007aa011040103030070741e00c4c01d0410301c03c1c031140c4850540c2807808841e035610f201d0344c0c85058251000901481d406d40eaa03400250001e000b508800d039811451074040c0344c0003035440800140e54901c44da0b41d1580700d0400b0700d0500d8080c0e000b4986d0880c0e04405008001441e10000180c40d80c0c02d5114801048640b07850341e406042c41055103180d40c1d107000701c4e007012940201010050080ca10359140c4081515501c2408900700d000c28041d404044904841b41d4190b00520740156401140c41660030120f030302c0954070040c01ea4002040c91101300000e030000a540da800d840703110000d00d03080c0042d00032868156035114058543c2d06000c0d1183c1c400700303040c2c19154420042009510401441d00300c032414007810 = true := by decide +kernel

theorem cover : BRFrame.Cov 728956834 729136690 := by
  have h0 := BRFrame.cov_init 728956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 728956834 ≤ n) (h2 : n < 729136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
