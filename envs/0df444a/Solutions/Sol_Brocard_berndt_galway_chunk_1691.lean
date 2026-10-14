-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1691
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:14:38.941707+00:00
-- url     : https://prove2.me/submissions/07be67f9-8f30-4edc-870d-30c6c7fc9608

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 303956834 ≤ n < 304136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 303958084 1250 303956834 303956837
    0x60610031803021006090204060e130e01110d150e070e0a0f06051e0c0a020919020c0706020c030102120703051306020307051b070b040e040f06050c0304060b09010509010510 76
    0x1907030030344001c80381c406550400d0180d006800080c54212640c1660181d81d006140d4600f00314505454440c0c01484031402c4849244660741d1811210310301c2080303801c14002c1140c0c0f070000b00b040d04155840600243d0200b0901070b2164100503106c1104070249050a0841e28403500f1890070f55202542150b40444000c4032070b901c01404100132480e580403805500180c840d980300c00b07503116044040b00380d190000d1071003404503800400000003800004951019029030544480d40b50741c482e08013020302036140110301e21610b440441d101513a0000010050b080300c105400755000802c0341000e06003030b84120742d0170010203200c00c0d010811492182c0d114131390082c440190762144c0841a92003d06980c000d5481d1000140d010961401441d250710743d0f940728a42500003456810314250442086005078490460240480c00004060213800e0205000d016405801004a49002007501040707810a55082e0341d9207181034902526800c001d141c1c40c0c1a560020310100c901da02e0074082015480d40340d500c040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 303959334 1250 303958084 303958091
    0x14130b012703051c0305090601030c06030c022a100c08180414070e03011425110307060f0b30010f0218010e031c08070e100206100b09010206061003 65
    0x2150060141e44581c0551303d0b2003806070840754500405661016290300c1d9581c2000c0d0040000940051300e91089610a04001c0340100407540c1c16402d0402500c01c400c40500700c103a002d40060b42542843c0d01c00720040303907880301c601401c1d10125181d416010005288182c10011200c005048c0c65042d590368200500c08110b240f500d440d0741180f02e206880038004181c3d40344900403185002c3c000c0c55000b00241c01e4032281440d00215512041114550003040e00c0c81c440700f0011920f128403039001e121080f150407242d407910030785421001012928105000c0e58030b0a04400b00038a4030b01d0094400782d42c00040e1100401900901c40e14010002c1080040782d0f60381c280b482d1021f0940d0015010000b40381490140541c205400500005075150349103110303800c0720352007841e9000b800030180240449407510401c00d9442c0241541c00c2c00384660055070082c044025108100c0e030010304144541080188070001e103564003841d00d058000d1000d07071b90241c1c20000004985052031a81e0303d41400d158500030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 303960584 1250 303959334 303959339
    0x12020f04020d0e010612080f070326100f081f06091107020901090510031b050901230f010516110603160206060109031208040201170114130b0127 64
    0x40482e40640da20040481d01c0d801c518034000c2c0280700b03e000801001003445e281001c41e60b034032802c91080100548103010042810340c00d15203e808248202c19405081e03d140141c00e495440600400b140c22456458202c80045420781c88803100303c0445425000030b00307000403c490b00003c4a50140010003120f55109000541000303180a00880178038030040c02076503200940148800284140c000c2000d06040009001d0542503858115080f0390b0010039211010303242001c280c4c064100342c0d20003944801c210b8004540754191510301d00000118100c4418041003c5060043e02a1010f107180d0118400384100c1000120101c82031100510035405950030002c0c9200041c5a908180c46201c84132120482801c0095010000d00d50408400d08002d84814510b6440015460138242d28104114817a0003242c00c59001d103401003080407040001d91110368441c50f64014020340c0c041c40c1c0b407013600702650071035030780125100f030301803200060351071100c00c2c1c4e007529402d049070300004058900c82d403110100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 303961834 1250 303960584 303960589
    0xd060f050f1e031c09140d020907021009030809160303121a040903020616080f06011d0a03031d01030207080307030509070315020a09080312041104021204050c0a061812020f 76
    0x103690040e013050010804203c5110001050f1206940203080030443c01c2024081c03aa403512502d09070303164111984000b070396a00310201e08010500c001401c0c00d41c1403401013420190014400b42c81071306810b0480b981c0c21703050803a80022620381c0c07002a0104103400e8050803101056008180409103416440010484040105085440004041e401a0000f00c180004031240c02d81e010450280381c6032000d06400c100c10388030001900036100d1030500400300041540a8810b11100300d25040040001040700d58904000d0444150030000c0700920120792113a905a60081c030039035210329008401e09055a94184080c2d00504010304554060300c60a20000001030f5080301c0d8110044040d400541c9172041610080c0203241e9039048100e03903820911a0005100c11380f204141e02039040111124000808404240240300d40040b0790b1014200728100400d1080014440e4510081a1201ca00e901d5a45d10110344030382c4806502b024040341c1030010400c4c04006403c42450301e000601000824809500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 303963084 1250 303961834 303961843
    0x308040b04060f2c0a05060d050f010801020a0207030b100e0406020c01060b090f0906011404030609050c01081003030c0c0b121602190201030e010905070303050d060f050f1e03 77
    0x85944003540c000750511005902c19100e890800346800c04000c0844001e200c5240d5801c3c103003490682e140b00c111000c000750741d4298070000800c40130b407880743d0790518142800013034031086071203400c2c1030b404000010b280d0805200712901c0480c150f018220300c0e4156a0752100401001e0900c6001c1c00303490002041a40702511000c0c05070780f04010041c1d41c1c156145080782554030691180c01e481d00c2c180860919074440c2001c0311450342c4221180700c52a070320480181d4000c00b2080e44031b1a0303888042404070412800703a0141c1c0019000c0d00480346a8040f8200441c0e1000b000c0750182509125450200002401400e59040e40c41c40b43c00160161520f89035080f180360807140743c040c814041c080601035030f641600c8184c2c4603410207101030046e5183c0c1070390340c19485800b0780f4001d0401d0f41d1079802e0119500207502c441c10b419484000d4605056503410f0040554000a071440340252130503c000800f01500b4407214121500900100c0c0d00c06a503a0400110b01008880012040020b01015520b40d400f480f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 303964334 1250 303963084 303963089
    0x60c210a09140f07080a0209180f010c1d15070f050111031e090609071707050301020a030221060d1212090302030a0f141b190c170604110613030804 65
    0x140288441d0b03540c0f03480c6614122450780068016007000403840e0160b1102070043c1d92041e0f8120b0280300f00418402c0d068902000b82d44501055440c0c203140452141c3d11018000c3e88081d6090381c40200c454100400c900c45900f8841080c200400300140c9001500c0c4003202d010301c030b00510000401e0410442148550380c012200d00069800c62188449030300c0a4110903074011007140001c0c52140b0780016100e070b84508500032641080540b07410000104000c224413005850301800075519404e0005014019402c040a41448106c1d2580008000380e020300201d40718600c010109040c071280d075250500d10016001c2502d04004040b0b0710242b20401c41d00807503920512a0340115900c080541000f030503031581d01ca0020800490242c520a1418500d05903460280b0078408003080301065100726182140d03031a130540d005103403400498213120810f54100200c03a800118141401c444a408603210304003210020140d821903c0301140b5418604007801d00030181c00100110a6100c0d00c504032180c01c0740e03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 303965584 1250 303964334 303964373
    0x1031a0114042106060603230c04091505030606060a020a0b060d020306041101110102040509040803060a1503020409110a0f0c050c040f0e0d0c0c0e0408040b0403030201020705060c210a09 82
    0x22003504013044003c1c401c61009011a140801401c070300c6e05101c558210002004018004000000c80e44031000c0704105c4e40180180d0504008078842d40345681520fa02c43c0c80b4680c0b003400b403040003070644d007001c0003144c255034020b5000d0704140702c03560750b1880b5810000e8506a0020f06800c10200145c508014060086014140c0b9844021503000010400c0b02d4041c49010141d005020400c01602c41d00714441e00140d00400050712135890f000030a81a0074168059038003100107840040c0166015802081901c00c0000c0c00e000c004003507810a101481585400c42c0002c1c400d01039207080500c18005032051501c12016140a4540b00000406850210780d00c200c1c0c06a881a514001c0300c020401d2100ca20080c0c1000e611400d0305480d140b114803032921424800886000010303041019400480c1d0151400680d26922562a4100203000350440d0308119018483c1d0030118010301307205400d13103061490b0020b01c0d0882000900f203e800001c0064105c46d007071a02d81803803c000a5803100540c3d80302050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 303966834 1250 303965584 303965639
    0x2011403151002060604060902040b0a0516022d0303030709050402130f2606040309060809031218061e1302030c030102040b07170a0507061d06090d0e01031a011404 72
    0x5c403082001300e401d60b034081161644100420000090b504054800c284510b0801c0f5443e170802c00601e840d020000c4400961081103081141ca2849500300403804080701c4401c1a0006100f860030705a0f203110031707600a800714080403400c201c10300d459001428045c40702022003400d0740d07035408140550301094010030004001c95000000e000322403d840e5000c422000300078034240c102914050416140d40c05082c0403c03910700e00007400c0c88070420455424481100b0041803d1602c01700c04900b9a0380216194014019880410304015a0518495800c01d01015084941c2c40d2052081c1014903000003c9802d801622a19002983c003031010b0300040c1011034601e0340d142c0d03003854041c6400c0c20000c1ca00303440071014051000680d82c1301054a5445601c20000100c0d00742404100c03e1a01440d00c14600a2140004104a14001040300d0360005829200d280004603844010360584034047d00c0c4c1003000c070301d24121040c0c1350b100780b0100c20480100441c0c00e2905031140d0701103024242840c0b540ea500c0d103a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 303968084 1250 303966834 303966841
    0x110702150d0c05070803010e0c040305060106030c0e090f0718091107021008010303020607030b040b041e1d191b120b06010302040311211005010f120201140315100206 73
    0x1080c024200c00c450b0a26145140c68815542e03e102400706000b0305031661300030310009070503101110459005d503400c001220402c2da990b000c0100503244890641000840c1003001c030103942003800da814010840c00701c0344211a519040c040b20b510454600d030201108040380000743d0360070b2522030419a11202d182490761030841d401030141960010450104001e041c00042011a5010400c03d420550901d00450302074451800107000c1d061f86034030564050314204502d034a1b84100c2016440d190b0124505000280c00d1034103c009010f0215019030182e04000807540407a000c40480c0c01c10301d03202d00c01c00045440d00c1c0c64200d61017521a00003814201d03145d05035205122080881d02d502000910b015071600d400e5941b00c0ca440c07260005064003d510881c43c0028510851109a0f40604004200c5514610466240016080a101e03031022840d0898000c11110741c0c2c2c840718044990103850700460034101c9440c180c1d9544c030082a14034000d030000204d28040d61401d0107654000c2d1254020401c1e0f05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 303969334 1250 303968084 303968107
    0xf181109070807090e0c0f03011e080105100b09240304210e040b1f05070b060411030c030403110a08030a050a05220201090519080f0a1511070215 64
    0x200c000c1c0064062001d0b24081000c2254001210700c01d9401410a51445449002c40b20803c0e001e040d545206540c404070001c40d02c0c5590249108100d18401700c011500d95540880031308807070069440c1074a15500440c10300404004600030400150041d0203500890094030700c5250300c078003c12610414580000501c401d204c41e00400da4000125040d1080c0842a40340c406400e0304d894000d00350223a0785070151441c0170ba0b00c002088807900d542141c90818500030b40401055a405445c1c02c0f10314580d2034000c0348407070030544031b030f20b45d4007020380560ba00e1034441d42e04900b82e9420040048040042d6442944071408041c06910f205074802c0c041641c89040c01078819003502c20043c0900c10080c0390034200141340303020782d40380200b1155415400c1070208041c00100c45c01909500f2407600240300081d4015020041d810290468010f83c0654101c82c008551403611208050400343c090b8583c030000d4500c0202c15844141942c41049604d444c2100a5010905204180000c84100c103808a9032600e4030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 303970584 1250 303969334 303969349
    0x70503041a04080d080a09050105010e0a271403070804120605150108011a0c0f0304090b0306010b03010e100e0f0604151206020d11161106030c030a0f1811 68
    0x840003036856402d150420f00c3c4280d40d401d00340b000b02c040000903c046800001e03e80c0c030026a040d0000024043e40d1386498601072690025602101254603004810300a100c1428410041100b0310a040c00101c1060311000701d80c00414541440d1800100301c01da00080c0403070300070002400104001c442000c201e0801c0b034115480280110307a007180e11591940c090385d00000302c070b064070003e00c0486004104000d42180a020303442e0381c000c0ca0700c1100303101e140e12007000000d0701c1201d103180b609000c12030300b400c00e040d116142032052031804601880188011020034a0301c03030707102144032644505180d0b20300e600c01224034203885c201610b850102c14042c041c1490b000c4d00607804414000c00c1c8407640f90108505142c0b0030542c002c0c4c001035001c00d180210ba21590802c1d03880710240300c983d9444040c1c2070681c5150712240f00307003141d4000f01e46a141240c0d00303103501aa4864440074191500b5580e40c03004640103044010202c1c44400d81e40d10a40c4d0200d0310342141124482e0080c13819a0401a0035000d00004c3c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 303971834 1250 303970584 303970619
    0x1415091903110906090402011101200405040f060602100c0302120a1d010b22110307020601140d02060712121a030f0f03072a0314010507110712020609040207050304 72
    0x9aa40704200f02c4c480d02c8009015401c04d030b080c40c24507040d041000036140140400c403816680050651540304406000c9005482a41c00841b4200280e400f003c00758000c450441c4144005604004a040b540300c51076031180140d0610790501501d05a0154920021140121006180f0580c0c0b0210080129901e41b2031001d500c2040c40200003230900380c0700088100d50601c00e0300180c446030704401011044030790080744c402e40030204116124103007010080d440781402d0181c1c000000313151180c28120f2500c0c070001c10305250081e0215203801c19948a0381101c100494854040c0030354842e0342d010f0700036a4412201e41c0c4a142c90200c100e000c18204150038019241c01954050b403115140703810b51140071040b6202140e06c03219841070001196541400603041003d013038003403400c2e40400030503c0b003920900643c65080d40e00810041c1e0390310009450004040150301c400d540288402d000b0b10b5141c0540300c0c2e042c0c0c0010041410000e00c000000c081c2d0340007400c200d48980022604000340305c440c505c010174 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 303973084 1250 303971834 303971839
    0x3080d020d0f0b0a0902090f1807110a020d03050d2901020706030908040b0a090e040507030317090a03050a200a052a040207060209030f0604110307141509190311 71
    0x50f083c2d40d0800a81440240c3c098010800d0703001a140007035917140100c811089030040c2a18401d41203104885545150454141e00440d842c41060055083e0200300318808550040c03404440e14066101204d03580c0104804881c40b070755400e03201500e6100e1400800c980c42c2c9200d1000302d23400340c0740002414400140e00a40925080c40021400600f200c41038030301b0340d140002c030745d40c4680306e200c0f01300c4210545174001c401c07120812003880284003011075140c0c140d0303000351183c043c01e00004072a0f5440c100d0456007448246c000301d070110b000030712030802005071030720a20300740f00307207031007581c0b002d9492185903d0a130190362103484182c0c1045403d100f0408540d8031a0b8215904120702d0741c00c040140c42a11030984600e0340010000100850f66050756141d0b0f5000c3d013140d0407210803140307040c1d60708420340b8103658180b404c0c8440e200c0381c9000911801900c040c200c80d1341180e2500030600264040c1c5080902c1c01c10000c3c0710a0420b0f0700c4842648403240e25500001c41182d00d103082034508008455103290 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 303974334 1250 303973084 303973091
    0x30a050604021e01021f200c010b01110c010f09051002030c010b060c1002030603070909060203041a060607020103090f0602031e07030b0604150309140f120405180901020403080d020d0f 81
    0x200f583c0c0104111800c05030b0030b00961000d180210000008001b00400c81a2404040302224540c0c201007001d4040e00e40130000030080d5a807040b0066a03664019080080c0c19409410700d03a1603548604410f02c4401480d04100031907541301c0e0009101c10b502180007400590000c542d4000c1c03c0d909010b0001c0d1890250b40c4203190840e040c00307603900d80b002c20814031281e907000800302d441c54608208910060056040070080029289041070196106540589186d011510203190a021260700c031402040002c215504c0c2803442e07401500500101902a12220100480040890302c070b8002107218a00c0c0e506d42902e42014403020a401c07100180c02c0004140c50000e00c0c0e0301c0d58803020704550035540d00410900c0d0748003042008401030020b03480020900a0151186014604000303040c810070070700c080c10b95414100020300c1c00d155002c3d500c1917990000e9089100c000707404811440e503400011000c005031401e51652146082544002001c1c880390b680014180ca090501d44104a0018624101031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 303975584 1250 303974334 303974389
    0x15040212011127090709153f0c0e042705030c070614040306050a0207050708070f05090c030f0603152505030411060a0203091e040612120509040605030a05060402 71
    0xa1401119001302200313041d00c0d44041c4070650180360f1410301c40740d644a80080c408c81100c440d072440607000003007005405c1c458804040007001c1d030050301c40c061526070342c049441070000104005805050203000c0b40440c1c5015020703601c050007032804641402000110b9840358050f51081c9000159400080ac100c0341c0034503c40701ea0301120480303040b41c0d08003001040c00d44071030203110024407402400500d02d1094030000915001c0206034041226071402c2e1140c0c81d0307540da405011600c4412140e00c91041410400508010075040301c0b6500100301a089503c46101d5a4050007031030401e40e103540403900a0010110911014000e80ca4a043c13146420781c154201650380c01600010494403078852440400c00c404003e02c00c100303a80420f080203001141c01c0301c035500c4104800d0b80e0b80c00c445000783e003482400701d10800d11030280080d0715840f01030408464045e000c00c50382034101e070352469481925620001841d0f03078100038200c00c0c3c83c0200c002e80309a00305441000900c5d0400d0b00c1540030303503d8101d01e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 303976834 1250 303975584 303975587
    0x10509102d2c060601050a030618141f03120c0804080703151e09140a140c010c021807090f060807032f07020d0501110a020708150402120111270907 65
    0xd41303401900070700381144c9480040a095000e0301c056002100901815450500c010702150411044d010b903440051503a42c5a040f01c400a680c030700c01801d6a48018082d0400020b524202200359200491424840d09141035032032014070751096104007259484684180180841d61007410302d0106505002c00081e041c007a6a03001c078031a40030404841d140d480750741d10103102c0c62140100d0b08445030015112046418940094660404d0a1040c80380c8510000c1c410b2a500581401020603001861803407015020455000e120700010a440704101d9a21800103203503450341c442e50060002915450700c14544205c00808139603082c0034452070002d01e4940c0c0c07004a03985c1500440544200c14035a5526a210700201e20b9440b40000300800c29032810300b40d6501203101c5400f4040c0a4443e509503100e0607552203100e0380e1000312040164038281c000c00410b0051401114900900c111000082901140c00e91012040d800881c03a4600e1404d005001c000ba900ca125400b40c0e9540040344c0140f05030422000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 303978084 1250 303976834 303976843
    0x601140d02090403030b042c030309060c1b0d090303230301060f2006011a1c05040f050f241009110d1b0908010509102d2c 54
    0xc019009100c1e040108042c0b40c42900071446072240a00213101140b09442c0c01c180c01c1c24190381c80035554952442c00c2d42c0315500881128011043c04000b4059510380c1c02c0d140600740d1001c14000501a844030198004103018002c180b81c1661580b80e40d0342440c41c40c00e0241501c916107110b54070703d0b008e0040d04240e6001903015281504c6951030f21030680100c0f4001991100b4854040154005902660080a10001810b203050ba841c1c0102d0341c00c030311708441c0d542c00240603020101041a240c081d03c0254910b1a5201550260042000c516429010b803501800d010b044015030070260407417007041882104c02140151004c01c06c2855106030b07d88201d4880100409003c0c80004589407881c031000744007a10140d460000c0c01400030440c10000d04200181c2800000d41c0401051110300300192149040c0b04e0300d4443c48241002c0c040c0f40c0d1f402c900c08801000c01140c00c45000860718140e0074441200c607038840404104541c00903078100c0c81c04448400e0303618101252920074490b003c0b000f44080118 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 303979334 1250 303978084 303978109
    0x1e0b011205070203130b0301060212030c0909040218070305070305060307030206090f040b12030301080d0f0c0212011104060201061409010602210f07030804061b02120f0f130602060114 81
    0xd00144686501000324214440d0070000540800350f030750085039804220000358100c030b60a4007264000d11041c1c22180040c0800c0310b00a070351250502099519081ca2620b640c0c1c49480108003034000741001f40f4051521905641c0300c0002070703455080000e86030b094480c130781d00300c11f00714000c0c460b26195600080141c41003440d164050926410500d0258403142c1125202c00c2000b0008030520380202403481d030780d0b003003403181d00100e21440e500039040c18081c1161512505041d5600c400c031085640074002c0180c44881c5020b140c4d0360791300c0b441440f00d1151000d8009012107600114281e0303d000b0b000c4901e460004c221a02c81c0d283c14004114142d00051242c04a02c034400e0b07141c0d840c41041c0c41c0d071030241c056405105c145910010b0410304069010090780d10681c8110420003802a1408003083d0075011002e0f01800359210300c40517800000351801614502c1003c0b00a60b1800e50103d52065030754001c4540c0684101c498101400f500d901486118054403204600c180b8061340c02c00041c41410412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 303980584 1250 303979334 303979367
    0x4090e060a050c2d0903030c030a1205040b04060b031501150e0a0f12110904030323060f0f0604230a080d1b05031e040807050108161b0f061e0b01 64
    0x107202402d4130120341003e650442d280202580e0711942c9034284692603512880500f40090411600da481414180c0b00d154040c42d004044248195264ad455100820384110103691601c1380141c0084662041d2492030b020300000080008a005601d2025000c100e80c1c00000e40705a851000910241c501e46a80204503501000001c0034280b617810702002c001c0c0c3d600d40d600e40080c204d00412040c103400d90040c5540c124018090010b404c2d113011242d03c2950161034940d844003002c01c1c841ca480c81c140340f4606200000804440ca003642d6503c902d401205040101010410010005085031600e90520300090028101804070513503901e1009109032080d400f40001c5e280f20301507100900c0750400665041034040c01007200202412206142070717401500c1021520300c5111b0001c2030552003410140e0003110110114840c080300b000d41541c152281240812500d41807000d8280800c090480040c1164083c0400088203441c1c2c014054488402e882454901420310b064581c2590703114202c42e00c2842007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 303981834 1250 303980584 303980647
    0x5040513120c060c022a09040206030a2304050c0d170a05040801021c0c0309021309050c0a03030c0b010f0506340c0509010e07080c0c0304090e060a050c 67
    0x348501a02d124000c1d91003e4840c500d0318140d242802d400007224044010b0040d2104904806a00c0700050301d0301c04915150010441400304005051140166400c054003905c0429a150306003179010b095660000440c0395500b4400c280002c0c440c06200100c004101600c070740061400d682c032a100300000300551003040e941c0000e84032602d584128103440c040c0c40701100070742d590b001c882d40420741d1107035910600d41464a0640c08071522400380c030400f40015030242c0704810000c0301e0100600180842041980d490082140c1d0444603655200002c02440c03182d01c4503026244c050500301c1d5030703c405811480e000c44031064180b15540d0b4840a0f00c0c05100c070050700a031244611400319030090200340d14001ca04501140200c1000240c04d82c02043e604180d51500341c0e0f070b9903990401801c40050f039680300032a900502040c0f840b5048402414102518421285055602ea030700342e04880412650088a40092091064011407801240e800650300c1410505001c0c440400014078a240a54a00402107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 303983084 1250 303981834 303981863
    0x3040f0809040207200f03010527100903020717070e0c031906060903060f020301120215070b040308060f040c020607051b0304080105091603030507020d050a0c180605040513 76
    0x2c590b01200c0140b0792249042c1d0903c00894070700d400700d25000400500c500c142e4503c559042c14140302c1d2521030340700307090f10306a0b46003104110b01250300d40501548443c05510000c000c18040ca0041d90399880c400e41c002e01c00c0c81d2404103151194503080d06000800d4000e5682000424410400c0c01d80180b24203046170b03070700d884988a40c440007480e404051141d601301200064010f811002003401c69020340c0d410300080c1e10000000701288001d0051800c01c001c0c510140025061108883c0c0105000e40f0401c3d20f440010384a0000e041000c503012000a10302000304051810f2143c0a812000303000c0e1001d104440d986240a52100c00c010b1103802000707404101034008080085011010f510030b142a2540c89440d1404680601800c41e07600c41680b06101c03010700300c410031203d4002243d80590310941400c100b9820030250780d40001b0305032464840e11080d000070034150f1380c00d8001441d80c003208000d00ba0f041e14024013940d11b10782c010341c840d034941001c0000c0b04060360180c1012603880101d80c0000720 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 303984334 1250 303983084 303983089
    0x3030e0112050906012c13020102100e0c040b010203180402030c131509050306010e0129030a0c0809160e060303070503120105011403011805090102040b0a050702041103040f0809 78
    0x15000d40d01900c81410700c000d03c0720802c40829414169407140400c401c3c0341072000c946000800d00a0000700c40c07a440000001e001c40045409244946d00c1481901d0a081c0404840d40680c0c404902d405040d0b08081400d1080746841d01c20001800400e002450401454491503602d410705041c41c03a010302d40000000f850345041e2f904407994175a5411a0070080764480340c41c50f60004042c4448404558010400700700ea00d4002240c50484500803c0f03094160701b044a07610207007c2180c152400180301c44501d010040d82c07507001d180314401c007110004944e40c00440c0200381000c05404034a00d07400c403804a4080481c500000400d9401c24110900d00e502c5a10210780345105004024155000114034480016032040a040c100d4500b6a00d407900e0342c00701c03001242c0520081c0b05028200003c400b189030546000e0704065804440f9000040c00c041e5180c6003201c1c968451400300300004c13070000d140421894184152900603640314000d80c114035040d036640c5060405840081e1810307102040701d04455 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 303985584 1250 303984334 303984347
    0xc010f0908010908030f0f0613020a0c0f0b060a06080601020a0206180603040813050411181212070c0b03090706110c06040f03061404030518180907050a06031503030e01 74
    0xd01c4194000c005003c951305010102d508140c03038101000c2c4146c0b01180404212000490040301c000700412421030f00e54001100a6000b21811003c3c803c130200e458021500c080c01d000582c502030115000c0900e0b0910030409034000c290080300a1040740400e004850340d000030070b0b0010302d5045c7d6009903100e0001d2154941c029103101043d9001b44000100420000031401a00825696540c0e200900e80c860040006560f0200040c100308170041c40300d50035000c1d51281c0ea04503060051300c00c40384003200c400c1c40c40c01c050b1413a411340798118000030441c0030094401080b0f40101107036459941142003120b80c040d1142043e201b0002000203040c00b80400070800d200c034105148008144036540c907600c100d4020142c005100c159991031a004089440010000140f4415503040c0d40b500d144c0104280208003021411180b250800000003545910505a246841c05000072100404410380b40c41c08002181e60319804c08001c00d410041084042d0740c4413a001c0080c1c83e4141404220a001c800048400703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 303986834 1250 303985584 303985589
    0xc02030709021317060f060607020d201206060d030809101a012604060218030f03070b1b030a02031b0a03060f0506090607080a0201140a0506130e0c010f09 68
    0x1142e200140d01c41028145a2004085428408842481c0d42c06524044d031620411110002c91102c04000255940307044001800c0325440280b42c50100d81c00b5495250300700065070708008010a81002c507000c20700c1c207900a285034050141c000e048614004003c45c03110128244018144002c5a021941e940001d00c0071640e07d00400404000c02403040298a01c02c49203a00840d000c946090007803210b0016042101158203501300b100e98244d21180d8030300c402544090140300100944e000e18580c1c9640900114056803c2c05000310f803200b2890a0140c034000300602640014401d010300f42011029003030a6030fa000c9030359140181c5070707540c4d5103e030361a89401c045c090101900010b01080882d8255010070300fa1034401d44286500f649400600c121b62144012240d804201840618001111403008104450440c07001007880c7c80080307c0c9054000c0107440107204a0380755810070000e420008600c000002403800300340510702406c03141545400b203824849042101010000204a0085869600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 303988084 1250 303986834 303986849
    0x1c0504080a0b06010816081302240414010503011508060328030305060a05030703060b06070f0c0e0603011103011e0b0d0c0324180b040c05030103022e0c020307 70
    0x10640e074146002184010120343c960302180e10300c004604a64103264504040c021a0f071200a000d885040211402400c1c504040341d20600313645c0039480c0141c4000140954415120105844500300b50032541d0392001c0840041c1040b00510040200f06074205400c40d41e1000c03800c141c82e50f61905808a410000c000315810003011806060900e1071800c0740500c0c2c0b03443c0c081d035020012030300ca43c1c00700038411a60b13214290381035000c4103040c000f290095001c88800700000340b50a10303102551b1703100d10001c903015005482441142c102007002201c5075a2060b400101200200030040107003225941502042c06071b8243e25081028454080c00f030315140c2d001034a403a8090740d45a41009040c500031301008200da100003410725400446001660000884c103c2ea0400c0015135141001d902920226840d20015800340d00c0e9003900c40141c540c0d201d448900500c980c1c81070303034079070450041c0300d00040040601030701c01580c045404180a9803400201644409141207040051a40000781c5088444e0304040d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 303989334 1250 303988084 303988093
    0xe040b03060f090321160906090b0d06090f0e060703200a0215041b0b040308040b0c0709180b0c07020a03080a051213121719020c0109051006090c021c050408 69
    0x40b03046850305c2c4154880c0e8006c18030030343c8070040b0803803c0711044c015120b5440420084142030001150036000b421260484410000e4080d5450301801c0139109103400380c2c81c5842e42c0310bc65000003102400701680c04201403d007440103551008203c00c0086c801c0043c02c60200010540d084158400d02001c81000300341c0c0003410042c00d05042254201003a091408602c891075080094072410100555003213a4004060342d0900745800e00c052401c1d400710b4003178519402603043c08070706c41d0413a21a0810084000403040e000800c1482c0a950a11014001c00a1407105003e460010303610110080182c2e503101880e0794a0702e070300300015222801480d09001d404800001088101120340d860f2214050180c182c12440100c004000d9030b07041c84580324094003240190024540b0500e10031280390140d0318000c0185403a10712030741542103c03155030040b41c013900f0540040e00c0031a0107010302409031000d02c8042151601c81c02d806965801c10031240a4441e10301c401c0e215000303006005a8004100403820390303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 303990584 1250 303989334 303989377
    0x50703030f090c05041b1706150a0c050c0a050319050102090a03050f070b0f0403030f0c0204090506090c030304182304080307021203040b01030b0a0603120e010e040b03060f0903 78
    0x244109843e5010f120301462030490700314680a250101d010203800140c90b880392250032407814030300350840203000070341002e0030402c406c0300ba54000b401442800c4281d50b41a00210703051800f28100560b40307003030611030516034400b4400c40d0740128503842d07201803607100020941164940140a40a03921705194407044190001091200119140e802c0321054420340e020651100c0341c2e03518501030b620704030035000020301003400024001c01c425943caa01d82c0c1042c4d00504265070001d400d4400c0b020048a181d000070007032141c08a4100502d1401c1035041700610304050403c248e00f03c0102c40300386001c10003621001515030840a401d4401813103d42402d81030301d45d29190030031140d01d5209441c80070051060403400310f582c041002c02d490140d580300c4c1640205074a907440381d44001300b000d041103480c1641c5c1c1d400040050080c244007100001c0607209d14a0061014001400b2007503581009c0b40643e081200f02002940c010603804e61000401180c01d8264640941c00c44c610f00481520503426040c0b884c2c80c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 303991834 1250 303990584 303990593
    0x504080f2a070509010e010b161104050a06030b0906010e0a0f020915070c0603050105030601150203120a0e071a04050607140f0304030b06121c180e091507080403050703030f09 77
    0x1414241c0303000f5608650540da1b01c0c00206007080e03091140c0788604c02d0a0095883c14642c24011307226a0303000b015001c0c20185140c00060807580103540d0040407030350701c1c3d00c10010172032002031380c1e0b41c0025103030003074032301580360021400c03074408010040c4813110b50700e05413182100340301d5050300c007141800380031000629031001c0c600c1040c0d808950103548040d10040001825407290080f0b0741a26805000703003203e80d182c10310050300101001954000d501003481810000c0d20841c0425102d5040b68002081c0100d9020113103050940b15003144c000b900425410340550b480c544112801c4440a03104159111400e041055804600c01d400780e519003da10700003e0080c500001800641780113140031105a2500b82c01c1002c17080d2034492030803c941143c60b040440c4035811004d9115004141845103e2005500d112400da80d403075004412440950021711011040801000010080c1d00101c01c03d036090210000c2c04003171008100070204040090901c0415120f504161200c00141205201204181c5071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 303993084 1250 303991834 303991843
    0x90a08120124050a030b0607060905010617010b03030304020d0515010303030e010606110607030504060605100909050f07080408130e0c180105090f0402091c03020609100504080f2a 79
    0x2218106200141c960700e20707a480c02004100e442ca00d4070303000d1030311000c00c8017030740030344440e0000603882034041c014a80815414015140250703c50400061950309010080040216152600b0b1b92a0300d040d885009640700002142d070025012242e41d45c5144c054641240341140c3c181c030300000350344104000410507400d508403a50ba1440b002c000c0c4212521b9080440b540c1c0040c900c050300d0b039800400882e48a500036488160000d029003c0401c486413942c0220301e0030840e40200c1c40000e032300c0c00410000100184102d0f6040701e90304140055500309018014034581028101410080001509080000b40441110700620840802070918604842c00c1461a048080f9140318403540843c1240158821403c880801000620402507036012806000081d00440c1e01c0d0341d048200c102d045800540f880d9a214078030f0b4802c1c1d0042c0460302d844003a060608402c981040c0a15080c8818040010051420703118064a030700800e0341c13102c51030000ba401e019280e00b40350215028810064581040218 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 303994334 1250 303993084 303993089
    0x3120906020c0f0a030305031003080f0c0c0a1a030a0f06030309060e0907020601230303030c070314090d0f0303091a090f0f070306090807240b0405040f0b090a081201 73
    0x809545010514800b84821800c20101c03d650142c400311041c80000d000750f019640280054200b50714542c0c8170b94800f42c1991010546400166020410b15010542005401e0607402d05440080c00380745050300105a244100b030145410300c0c0c2c08400290b42d00d8140c1d00110510f240302c101800010b076207090152614015024060002e640d14180070351600b003045030140903110a600800c41a03180c10400741d50142c4862102c42c114001c0d03801440380c0c1d90200041d50181146075011a62011240760103407c0e485450740c0a580c00c001070048445c1070791042c02018075581c0181f501d0940c44500e03e400c400070440210014142d44580079074070001021900040d1044003043c0403141c4000883d8841a5503420784190342c5c0980c0c0c440e0308184005881d0783c00410310070740b03c0c90040d428074001da943c40908117400071080300c0104140b001400c074404c0a0103401112841514208000d040586a01002c884140da0260003180c4080129040f030f4001c000b204003183d0800d040b6500d0b003402003a8114030715000e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 303995584 1250 303994334 303994337
    0x20901030b010c03020709050705211f080d0c030c0b090703020411070209040206090109180c0f03090f0f110d050f060105150304140106090e15090705012703120906 72
    0xa0750310302081d409205400c5205415070000d200080c0b4080514001d0f00009200b0f104010341030101b0b240801860442c0d0302a85009400c802d21031400c440300c44c04004514040310b40600301480d0401c40d840022a1248103500c540c644108041c619050548100860b10002804000301d03e04100136040049281c4007500d00c212000d1242200040b2070100307a0041007006580101040c0c041401450301c3c100903c0004418103050065503030300e100e41f0040c0c08440e01c0b00310000c4c1e1628030b1807003016800400d110300d030748250070f040040c224561079800c2400040c440080c5080e004081070818070a10580b600d045110041080007000760503d055519421091070300481446464008a501c0c07a10301d881d50810311a042841d0305603603d030344440742042c00200152080303540e601404141941a40246c01480d840100140304c0200c0001c0750260301c1c0f40042c0005402d41040c0341c140000d82c0d01040c0031a440d1081181d0030400c07100100d4111203828103900c01400f040c3d84507404c1241c96040011542110680d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 303996834 1250 303995584 303995591
    0x1521030705060619091a040504140706050f18011101060b04030b01090c0e010503070302070606141306060909020f040503070e1006020105070503040305030a0b090403020129030a0602071b0902090103 87
    0x800083c00b010f42d080681c2d44c0540d29400c0021720000798158400007800512550309a402074105000c681141d00035a010340780d002c0702c282c1c00c0314180400c204d268000c1030689081454242d00000740f04d000d004010300c00e038407260170911800081e889440c500c0c283c0c03032041000b000f07426500d60025040c0d601c01c0c88129a48042e40000003210038503446091000c040704c0e10b8100d984884500111403e600083c1100b007415404d005c4030b008200382e0b204a002408411031202c0001e080341040000210611800030380041c1441c005000e02a84040101d084501d50300d005030f2100c07e40e00d030150b198001c070381140e9018450314400082a018840340a805684024a000c10b8a034480c2002c81c00d03074030300320385110105904101080c002481a0011035021031914030001e508560100080e4411005170740580c0144e468103000d0b1f10550100c010041189903100700804000c040c03001183c4c0b01d455075070b405070000f640850311406010021504000c903c00f90150442000d45401c0684000d4010203142c1d8002440c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 303998084 1250 303996834 303996841
    0xf090605040b07170c06040302060601030b040e1507020f030d05040c0e0c041215021c0513020102070e07030209060d020c1218090a02040803070f05060c04030b152103070506 76
    0x510210303001e80d214004154078042c1c0f0303910341c00034401602c038401d00c1e80c2c2d400304000c2c2d00b0041c0c2400144d0065209a001c0d0900f070402d1400102511b0300516001d01c40c80c58460201002400010803020040c0f48043c4425a0750320b00304280c0c10003800740980d155074040010240e02c1102d0550010784518441c5070010903080e00d80c10001102d10b000c40380b140e11018100700c1800b600d401100c0c0058814410b01d02d0506603000c0548404c1030ba040014140d034007002c0300e032358105102400e02640da405170034442c0c41c0c0d840b00503640000356102030504c1000e0924045c580417999091081c2c040321010b84010346000d5441c2c00500000000f0751010602c50b840c5c3c00b43e0304195200002c01000c90341c45124007c4000140720740350007000200e24015101200c0c0079800c020002d1441000d0000c0e280c520300429a00c901801c3d5070a00a040a5004100030401e040800c400c0c0005882108029004001026100d1010040001084205440e41180440900b10340c83c40c9a40c0800000140703240c0f817081050700c1c0301d47c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 303999334 1250 303998084 303998087
    0xf030a0c0c0e0714030406060b0a0329060a0c0c03020a0608040308010905070e040b01091e1706040b130f0b13050c0109150e03010902041805060711030304021216060f0906 75
    0x40c2c03e440711000503000e6480203140089410103103030464041c44002980580c0c1c0c58000c803081c0e1010980f000820703144e1034405542d0f00200307083d2100a40c0017403888144280c0f080010f00030320440e2407403c280001d4a0420301813000c018803c401441d40a444d06081c10380b550400390910304116012000241b100c4000b286201c52801014022550343c1c440b8500c4101c0344040001400000b140a8100803840100003400c00d1408440441040c2c294088151103080040300c28003e5a11400d02300b2030ba002500340301c009415928201c0d880b4040c1c2e41000c818203403074a06050710b0305282c20b0242c4034081d070741c040c88000220402040005031203034040700d8207004280015580b0322103e101e0720940c0c0f49900d040d00103040c041c41007403101c414010000548110242d0024081703880c040d2224880c0880e11850b0000c01608201558015550381000ca0f20071540246855a0307100040000780240c01103c81103481c0031040109601d18000e200842d960180c90f0f40e40140304240b01c40340c0000241941600080f8030703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 304000584 1250 303999334 303999359
    0x21040212030a0206040f0317010e011a030f010902030402180103120305130b0a050c04081903080702120708090607080304050a050c010c1703090a1202030901030c0e0f0d050f030a0c0c 80
    0x41415402803c41552903484003040400d500c2c200390240b0448c883c2480000d04115034460113001601c504480b154105255031220900c0c042c0d45140d004802c00a01a07000c042076a11030450340c070210050398130b640d00d201080089052134000c120300b004490000c0100715200341c1200340c024495400b00500c0e41c5010183e08183c18000001e014125080003003a400000b9030895a40b041380e4110192900355034103415480e000f514000c110403106185107500404d64820b14458020032984020006035040815030080c501c40d013140207010070300002d524091500c87d8000e03104a00d410910007a201d24240c10400d4403165004030444050041c0b100480c050340c059010068283c1d003054460303c41440c0310910300401e90018105501034400d81b41050001361219200f2502d2920b142d010f90b444024410000d000c0e10a0100000140108800d8500060301d90b003e241e83c0701041200c020440c620141000c03410810000c91a2000b4000011190801d541240c881e0800d40d20510b421a007290303070f9803002e6040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 304001834 1250 304000584 304000597
    0x3170415231906050d080409060b0301050a090f060312180e07021207050c0627010509011403060f060f070506090c0a121b030308152b06022104021203 66
    0x81e5480880411050350b0b10200e00300c0340c420220300008405032107030006403801350488000c03240100f00082c2400f05004a0040d900103210110b2803508550500c00049c0c80701900e4003070017007165038441d8a486000d6a41d040500110341181003030400076211540100120701640c8810740c20181d165000440c05074800380d00d44618429409440354040c0740d036204500b544400d60984240c0b040c031110744c0300d9903203400c000c002144141c0b140c40c08001d00d403152091100c03000c0081d64140541803080503241c0e6013010300001000405840e4941d41d82c1e80b0303000958898a4440b071150000d601046180389080b2203802412203a015408a03841d555580541a0399680c04056040c2c00190485003081001e211000314100248110841ea046030400c502e05045079002e903100303400103880b10003400850320707081a40040101040e54455009800d02c42403540c0c00c0031914000c030100043c0403540040c007001c2d90560f80740700075201208030601130301803611402ca00305071403ea20880180120f10909140001292074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 304003084 1250 304001834 304001891
    0x61118030d2f0a1202010203040b010f0b030c0f12041118310b070e0406060806031209040f02180f0901030c03030c080705160e07021501050d03170415 66
    0x150000d19a10b00d52020b180c0500050b108034414540090400c1c0384200b11103415174001a164601400c080c0720390300d01a40325140000f001d08042c07020203541005c40c0d078003000b805c1c24141d954001d030110303e0080c81928a59450000950148020058021000b680800c0121402c80000503901ca9111300714005440742e07001025005c1400c16118201c1d01140964100c072040d0441d094025190b01204400840b2801c00062030040c0c421003e24103882000094907a6248c0008d05213800d02c0420340d10983c4072100341c0c40c6440400e901d001c5903540c0d04180303042c1c1d031046419500c40400401640515200e1040548206441100c04040c1c2c140944540e040365040101041014615102910000100760041d5000501005040c0c040391080140c5810070486400060003249881c410891030300d00500581e0454014426205000b070031071200c141500c0742210070284000c000d241c20744060443c00c0e12035450000b1042013205010308001c2c2048203c8264609000311520b40140e072240b103400141045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 304004334 1250 304003084 304003127
    0x1509080909070215160827070f0305070f0605090108060f0a2303030906070b06030102070f0b090c04020a120b12010e0313080a0c03060515030f1f0c020c010c061118030d 74
    0x250346e036511604244030b0901d2101c2c000290a400340c0b4407030410384a90082c49c1600340c1c0700010001c101c400c00006004100c811740c0303021604e0030120014064440e411a0340d04114044001c603100c1e0b03585007000b0079481001089034a100c3c1d0b4401100c500304202c45c1d40c19101b1f090000030030071a42000301c101d81040000070005407811265aa42d040c1400014209540640d803e0040d0400260300c5240141592f000389d183c0036040c43e00801c42c0303240c011000c5106000e140103104040c071840d04021500f9012480e00300c003140503078200011940c4001162101c111307035801d040141d4001c03000400200841da00152a0300419521500c5066a414413050000e14409060300200301082d15a0300154100349041555030101c034041001a14060440003011440e4120707100c1160301c0007105030403040d0101c226006005200040b07a010351544480b0b03803c141480300402120341080704036402544004080310741ca6440740c41c000303000c4440c080e0800310140a07218594891403458081d82d00140f01e81900300d41c44 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 304005584 1250 304004334 304004341
    0x60602030702150c0d050414030a020a17100903050a080c0910030b03010905070f05010f030516030c120c03050f0a1a04020a090815101215090809090702151608 70
    0x22901c943d8000b80120003050500c00c544000505200104034442e035a6150f5458508100440c2e01d01a08110454401d0703001300e44d18030060b00c0301e142c100110303110101d02c420310780e1009000c00c2c00c0200c4c60390f200140510b400d580508150b0482c028049611140d41d03042101c4d5162000c3c04964451007440302d40c131409850307901d14007910941000c2034000c0c0240020840002c5541e03190b140045540001c48521000007080c8031650340b0105d10070b41800b503440e0620440c10404418409080005103000405480d1038001c04a68010746400c1040a98500100401c1100450081c01040262556100c5900400210399800c4403402425941d02070f56200048a800b000104002944038000090038000384010020b0007040078091200f0201100034800e070b40346003641c56180c03501e04641001c1031200812203120003040d07022030340c4042c2c45050507000803401e00300d0506031038a00a80c090554454400d8003004841c41e4003040d1b01c460721a10803011003450301e0f22202040781810740400700307000680d80e5000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 304006834 1250 304005584 304005589
    0x9090b01052d01032c01050901060f0b03040201030902090f06090c030903180a0504090605090c04230408040308040b0c061006020a0314070b0c070314031303050711040c1110060602030702 82
    0x7480440c8005040020715200c00740c0341d844645c0d0718a001c5400c8074480c00d0701c48100f08801c0c020303039a10501c500020041c80d8180200c41a4031100c5000d60f07060307400040002021a4040c0c1d010011880d00201803040503e05844600381100d4111209401101f44001050175a0025003c0c1d901800400303003e141882001902144412040c0191643c014002e900c00600b581b92482400c0840d8001c80d0041100e24003000c02c98071f010030b20034a450007140740c5501c0d0380f524407090840b10b0b03000d0078440c00c0300003d8999041c070304c031940210b401c0603008030030014001580f00820801030094440a00680d4125030300c80c50f1003090542e56200f0f040160300200d41010000b441401c07040c02c25460045428106207954a400c81448812030790302d9013801001a402e0149a04a0000505e400440f41c080d441c61914030a0008000d4001200805003d00032502104006080824a47c0124054010030180e103004600800c0c2e030018070b010310514000c00c3d0303800907000038900400d010780d080740e0003c0d4030301212a0b00b0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 304008084 1250 304006834 304006909
    0x9110901120207031713030305060904030f080901020f040905012c06010e031005090c01110706090e1306050703060906051203040b0a09120c3014100609090b0105 71
    0xb10100f10060129814045c200d40000d40100e5880c4482d807091250340c82c000e002c07542c0c00340409105081301d0007044000780d4004400e031020400781c0b03000d06040d12145440f0b40a03008800c05010300200205012500300c203158011412074085030f441420280802541a50480010f041560b000b4541d800103881940a03090740c1d00c41040250441d5034800d1051102d500301c580a44081e00075030020013802502d0b6070700500401d4251425406001040c0c03500c1b0001d403140780305105003100400d00300c00150f01c0070705194001a010350030150500c140d1a10440090044c40c0034021079030442d240034400b10f000e080c0074900d9074041221034000c40c60a801c0503215906604440040310401c0b501328008035961004400001455100304140b00800c1d04129014003907400f600082076010020302000c202100c914003284c4000c64018203204e450300c050a400c1030915800740c410202c454106070000441105d5548040c49241c0200030021150343c88a00b04002880b5481ca000d41b07203101c1e1410001d201c0c98841 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 304009334 1250 304008084 304008097
    0xb0d03091403160905010617070909051005030a0b01061121090d080c0f120c06180102190806150910120b0d03030e010e070b040e0c04080f07091109011202 68
    0x804407802000c6558200349441c0103038001c0060244c80317100401803243c0100000015450360700f404000c0d0326141e5001401103845110301c0340c0b641d45450104000c85101810f640240c00050251a030990781c03424901c101d18020b00c075181c0003801440420809500c081800c00308044040c44410a030214801d1812a40d0440c18110350b0110039030035000c0011301600000c005249030329002c0c055a80a102170541000115003075100c44a074100b02d1400711410120314194002901c03c0003026803883d140d0901d00902941400080c5a420a07480c00003842d040101c2c14400d8030112900c0b10405407048092440e8058080300c25000309d0749070340d4220b90500410201c188004003174000210b0b1003580000070011110042d0a07800710783d0369aa0092010000c0c01104d149480c0300008003801031070a28285120703c9280300c0c3c0d100e0020450086464603251000b201d00030032110381200c01c04028010f00c55240c903603d108a2182c00d15201c0180c03c0c85003018181c8180c440140c580071100c030125040e601c06903010f103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 304010584 1250 304009334 304009339
    0xc0d090f030311072601060501080c0d180510061a07050606010819050726060307141c030206070f02160533031902030c0d3c0b0d030914 60
    0x104000300e0054564005c1601e030f44100190000000c88100c0010308550f6036401050401000804118000d286d400840300100070401e030014041c41285074005070010000030040940c042c4408400c1d210038590021015205000750203c548031200740c21450910441100a0450300018005201503005440d240d5024a40e0000e4005414060140204445046800c44085442d440e403080d03081c2c84810381c02d101084010007400241c100f0b60300083e510707803440c0300343c0095001003950001151074002d0b00000345166403a011100400c607281c06501c1c2c5000b2a080c80c002070080130008000c40c400107203140c180e42c3c21480108407034100801d02c80c00300312098000b1007a4080d0443c1c4c06504103a80b00e03060b03292041b2044103480f42006140c0031407070041100b11055a90051007808090885002160001c0041d102c2c0050b41a40c034040e822043c09840091405600d04a60100b5642606a50324001079102217002c0000f0b525120402c16082d10101010700000d20031300c024081c1c5a600510300c800c59800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 304011834 1250 304010584 304010593
    0x13050f0310090b0f0106022a121002180306010609061b05030a090302040c0306030b240a060809240402010315150c0501181703070302040b030403050c0d090f030311 72
    0x10407041c5056461614003111205014000c010540c410300380100e01400140c405020b0b1199030490b891420102840f01609600d4400d00c0b014803030b07850301740c0040008440b0041c0c0d11113191021080d4001e400c40c7d170310103a070b1245a1180d24602d190110b900d9050390717003580b81c4080c514281502224104111254264200144c05030600071800800240689a80300d96600591600758030502c415034000d0100000ad15061200500004a0903034090398040840307040307540100100006081419289e00c00c454002d803032100042005980009294440d007100c00482e801203c680c0c1c8100c0c5154154010b5080c4001083d01207001984213420441c00003844000c62400035441b400b81c42c031444102125000411861038428081110a020700205440e1242d45601003100b580c981044a2021700c4010002c0040000000c0c81c05001c0d41c19500540866a0220f4a0b45418035028080b5400210920300ca8030070440124a46481204042c003070710444442e03000218910743d01602e6009188075038459a000b07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 304013084 1250 304011834 304011853
    0x6030a120201110315010e032d07030c060f08010503070f050d050c12030a0207090b0a03031404180e0f06060102120a140309011d0309030d050d0b0d080c100213050f03 73
    0x281e0343c042c41c094602c900c001001c10b0210f800240524032100394150181d0401041c14214800c9510300e06c000c620701c1c1c9122001c1e0000c05002a00781041600014150003503203202261036a031200214215030101e803510b9210381d80701c2e010184c0e00d01c0d45100c1c3d81840100180240003d080c0304001590191250044035101039106001688030314200685020365070000ca516040c0c2a4100540300c010111070404100c030184510106070034030300d10300000c6c05100011101025000ca404200c90003048401e5a01e64111202680031001d0418050b00351000e2043c030654a0443c500400c1950082005800511070050014418079068005c540d15805101066021126480d040c1d0000c40c403444099000080101440c4038003c850305d5039002c018680c1d4014804640d084d10001400c40aa44240c105552190b01400d0800c026115402c1c5694002c48030480500c1042003050280138440142c0003694094040e001e000301c102d02811010544480300484100840e0404005903403030281c0150680f00c1e80d02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 304014334 1250 304013084 304013111
    0x60f0911120403020c190e010b090604090c03150b0306031e0a05010501090e0114010b030f4201210207020a03050d0c0203010c0e220b040e031201050906030a120201 72
    0x211410f030050f0304800d2400401d49000c8084066001c0030b6a40380c0c03005401e00c000c0800d04a814012521050000299084c2c1c5655040c155402403801680500800404000090107031040354a1000140c0d04140c003c01d005d503003001030345c0c4074000183c020032030400d41d00d42c2c2071031b00b1071000e0701045503014950516011503820300443c0d000c1d103126003000c074240080900712821949030050a139090100c0030010f1007034440c48012260032000c0c070290f441ea1900c8503d20f071800a0005055041e001c00e489801b04840d0302504404c01c0741d2460404007816225001d0700555001c0a003403011941804980d0b07011003200c03041ea02412102e400940351001c0c040d02c80d510646080c00190f00b010104050a040c02c00b149400d00549400540700d1900c01580c2038540c0200341b80d40f0354000040300071410610358624181c025448540c055200800601820011a800c240c0b47d9100698020b018400c20001207074a0510300e031007500401024008141d403010548a6402010303500c82d8400855480b04410310541 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 304015584 1250 304014334 304014367
    0x204030602070b010503030304030512040201020316150621140f0307031215050d110301110f0c070503010501060f05133308040809010e03120409140a060f0911 70
    0x154418400103030740d102c042c03c00b1a8940c005902c450f109174010410440025808010390381040001c1c55243c10948503440141d080d0b0103094100d0b908520404e01c480c082c0f0101d0308400c0480704540600b0042540c4462070361580c1080000641d03003400840800f40c0000d058026541d041c004401e064031390351000c4c0328583d03095510200054001480c50b1445800da265140714103e104248505803508040ca0130010900e240700040020303100c04030a030100322454401390015240700720402140d41ea00d035032055100600342c0250584286da849280808905401c0504c600c0b41a00c002c1d4446081c7c18414030012219a403003c0c01c10300701c0400b00100000d030f03202c0c0d0320741100400c1503203449040301c41158011010a000a0705410701088510028400843c4c80c4004442001100b032030080030b282c1181d80401c1c80c01400725020014018006800210351300701e54020050400941d10b60140c42d221650200b0a4030207500505030380e484410700c00c100300c1c0b1540c0d210180c00004214881d0804041c0304402114 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 304016834 1250 304015584 304015589
    0x307060612030216060804060209060d0e01052d01030210090b0c0a0314091e03151603060f1d13140a0c1e03060e0c060403060b03101a041505040204 65
    0x1072480c10800001016014040841c20400c0641d001d0511443d06400401d6164041d1010b410310b40c0c0090705464686a00085034800e22440800340621392100b82c806001786001c40342070000d4400e1001d01940302d0b03000e01035071035147c2c0724503000703003030740c0d085400300290300310b0030a03000b414400807060000d40c103403810002e4610004e24402604104c805401c000d0806901c6610508824504015025060380d40c548041071070001d02c6007240b2140461800f01c1c0ca08022240220094540c01003048800b42e00100c002c2c1c00020650b505211903582d4400c00c1c44a54a240514001d1000007911034802c41d04c2044800c0d41f0045150f83c642c646000e5071500710543c8845a454040c03500412801e03001d0294594030341c8010044400841c041d02c803c528582c1400394607010082402d07480307101807100d020301003001c8482c01c040240041c0d030b04c507502d243c000010104071354610300038050450408144040c034032410070203c0d04004050b841c01070203010440201b031400079207101903c482d036000c15907494900c0074102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 304018084 1250 304016834 304016849
    0xa020904080307140a050d0e0106260f010c080c0d061206051b040b0403020405060a0e1008060a020a1b0201140c010e011d0712081e090103140906160203070606 70
    0x790b03030600d070300c004003440108428042a050100075a03920b8651140031150346511801000504500c05039100f4054141c44d440b0008403200f69005185800c00d0914101c0160412800c9803903004009506c98282e40d0781d5001040814410130000e804580070300002c0064a070102c20024615841d000c01c26101040903001b5a407a0390f4030740c100301c8403840784845114009081441e0740d040910b0024a40014411808000d024540b00d00208015844440603480a00300460140040e031604500d0f00840040304d101e2541280700781b201045440120b4800c91703580400c507030b403640c802d03003154041c00c840f112500c51300324100207202400550000c601c001400c819107609001060312903101c05402e0a5031402945007016030104031200d11400c00000d0030f40e0460350442c04103000b4468900b015202030280b881c0107440c1601e1207190441c80002c040c000d050004007604c04002c81c080c9210013680c1000100d0355981c1d150b0000f000301e51140d06041210b200c0650501c1224508840390b980c0c84241d81041d0300410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 304019334 1250 304018084 304018087
    0x3050402010f080c03072006070f0206071b0803180f0c0f030f060f0603120d0b0103060e0f0103140a06021602031c09050402160f0f150c1403090a02090408 68
    0x115a80300c002c95825641901d030095480c20503000441c014880509008240b04c0002e0084084030a060075603164910241d00341e40441c83c012030090701104003260002e0060048900040582d40640c8100e1083c5a101481c40c60301035055407500081e038005050400b000d0007041c102c090411040058502000c1340401a21761202c0a00038003144074580c0201c43e1085d0444140c01c1c8500d100025480e601c041c0c460001410380e200c10001c24249081100b0500142c00c00150481c04002c0d10b40003404d840a081c0d800300005030b41d8802132040c1c0281a505040b09100400041000c01c9510b4100d00f075490210040c3c4a070409281d60361412648101d800203601000450510b042d480d00b88007080410005140c8590645051107005000b05030900035107100d2523001c10801d00119401da65940c110794880c3d2041001102c0b400d10b0207034407041c3c0100316050030101040880c410701d075004024000070300d51601e115420388411405450340004103414000e104946407003016036180403007035004502580286 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 304020584 1250 304019334 304019341
    0xf0603151003090809092a041a030402030d030504080d150906080a0203060718092d0c1b111507030e0d0b180a060219030617030a080c1201060305 64
    0x75401038858080d40034140340143c0c400c0480d103400c089420110044481d00002d80d03803001411000c007040b00112240390300c40365a034000904454000d005a80750300c4502c0c00c181d00117030355100c01807104a40080d0035401c10026202e00034041e030007441e0058800c00d500390a020600b400c1400320751049001c610300d00010002040030b036a9500c22440038000ca074002e1b10030310049401003036941401030007403401c009c5e0704d00c07c0070007040b0140144005412480703014008940b0300c0422002d10403154082c1c903060782101083e40f00540c0070380b2560302407800359150500c1d038466800f01c409495192580c02c3d0b9809602030070305038140c0e940707405103d50741080d6280340d51141c06605008120f03480c40c20100303024440b01642c26010a6062042035400404111000d842d00071501415042500c89200104041e0010403250340d054007010b103606200a456404000303603a030300c0720042d005c0e002c0820000042e40040040c0096140300e08030540c0d210300300d801420702d807000307030740642d8243d907802d0303000100003a90b42051 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 304021834 1250 304020584 304020589
    0xe030f0a02040f200d0f140103020316050102070612110a0801080d0e06120403121d120301030c09020901021212180609060c1308011803111b0402090f060315 69
    0x15242010b0411808104400008000c042045201c0091070300e84130011542c502c0c40701a030703080503910070b1002c0c0017402031100b07a10b144900c0400a0004911900481900b0b00c00955442400400c60f10140d00030018185400030548203202045000b0580c16110740304846068403c0c4010000301200359110005503252081c4507040c000010490810051640051005982d17a50700744c170120300d0441c0c003207080c44d2500c0c41c06403103001c04601c0444596040502048084461052505900b4240810b40d902100000c460200c248400d000003000d8001180c810700903409a47c1c0507240000c0180116801d440c8004074000e2141c004a102200355400c03c401c201d0884803604400310f90740c2d000c80081115042920f447d0361280320082c00616040c070081007240f114032186006100822007240204200c0d08002d0b2421100864400158085821580200f04001c0b001034500b0485001000074184944881c0404c8041d50180c1d440d26880303c120490344082d603403024025809100a00072075000c401040d0f00707 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 304023084 1250 304021834 304021841
    0x70e0910050903160303050601032a030b270603030403150203011505160b060f130605100509030a150f0e01050601020f0304060507060509120f07111c02060a0e030f0a0204 75
    0x89420035041404030046601148000c4c03145140e0604010485a1b25480120000e0a280740308405c01c40d10100d8110b0b504035044511340c03280a00d90b605100041884040c0811220116224420000030600c80c00003080b0b0141441d4000381c9c010140e0385019503d40b220130441c48108604080c09500100401056041c1101d00c01600114200b09003045240c0c03c1d1111198800107026044900e9076000403101e644d0120b01c04a40c1000510034950400010b918000034051806a180900d21041c2030441840c002c0c402e40d0004078009004048070b2006689031107003000c000450b01e83c0a40c48078540d0056031b219000e07a5982d900114000121132510700f00091402000845203c03807034000300010f01405034000202c3da0f0154000d0b030013045907210b4140030742c98900728405903e0110008a0340b0244403c0c014010a480c60240300c2c00c0f142840071808000b442000720090b0001514402440c60050078054041d010703d1880781002000700b0040404a808e24185007052269604858403190440c40c08e4803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 304024334 1250 304023084 304023091
    0xf090f040e011409010c0206060a030b100b0409060513110a05070503090d031d15091009080a1118100303030b030f0105090d020f06060310110f1c0501090203090a0311070e091005 78
    0x2008140e2420146c1c046001c0242b50300016004050980000c0c640381c0c3c0c100001d0000303140c2441c44681d81c0c0d540d0004200207210a001d801c0c030480405260b0300c0340d000d10340a81c55880e502403d0651415031102c0c0282c40039171040b02c00700c5840c0400c2c0190740c49a85c40440e0206010302036150440c4c2407889100314a00c80c00e554038000d01c00c1e4102c02880041070014010f0391643e280944a0054100e08a241034505030a541d10044146c403816264900f00105044000c0381400160b51408a0901b200108a54660100c54120f000301202004001203403103600f003400b4104001c2d00703980d2050202c2c0c00090a40c1c10495403540e00d6030291405940d40c941c10484480c0c0080c1a4004c1c0c074050034010002510741103440c4240d201c464aa10000d20310040d043c08640683c80c2401006a807212410300300802c2444011a1000e014540340c000180d000703541c021640b04243c80b4002e40103200641da0180c2e20f56070104003042032481940400300300f9140f40503406005158000c0100001e003584811070301a542c004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 304025584 1250 304024334 304024337
    0x609100302162f0d0308060909100e07170f0a0803040f0609030206160509010816090f06030e21070b15040e0309190602070b07031206170706050f090f040e011409010c 73
    0x490510000c281c3c415030550301f100089654002507159900901e00c1c000c0241203244035145800c54a00d03828400058a80840341141c14050703071100081c805649030300250304219802c0c0c00100e038400001e90180000c541c403a1084000300855085074841004840c1d82101c1200540e0003802030100c0750400f10790070120a480c0c0e01e4958a0f080d021800203020440103081c800700c8142d5a40d0803a00f00740108480c074003406003001440c85c001d5407050014054989854036116a01031011079501c00c082c40b100590350741c4075100d145072501c1c641c0c1e07030b07100b584a1000307060390310b50a41444040544d6580d40a500710075000400215100d4401c00100b2000410120204664503c50201000f60310b8010039101c046074003050042c0d4803544c5505094840e0070941c584101410314002000c43c0e0060100d0030408a1708420003207650003901c1d014191558070a0749415001404d040c481182ea074035001450000c0e82c81b0250020840b20b10000340503094415082040d01c001c0d800404025001909103e04900c40009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 304026834 1250 304025584 304025599
    0x708100506012307110913030c0203010b040c0c0b011a160201020106030c262407090509070804051b011409040b060d0e162103030b030f0d0306050609100302162f 71
    0x10107460441f5078042d5401800d1041101011040d590298050000c1580141050100c0da01c401c000924005221608480c584107060011504080f402034148922003110304503454184070b6040a04100e0301c02e43c00301e04564803035202100003003500580b100200401c1b640d541c070554880f40d5001c1c0c405018102400c06a1044202c107410448400000b2004036041e502c03c50280c03600e00302100c800703245400803500030180c141844030481d40301321414440c60141003980c03c08490802403010b059807041b500f0703000075844183e08000b070000c070000f81003a03000240300042ca041034801154080e08480d2443c0d141507a9403000d881402c070244005006140c0d004d050310078135404c141c0001c151901a00d02051900150f41c00c410805019500c210190f4100500b100c603000c5003040341ea039032902c0d00003a080000c1e0900c03000246500309581034a840c03130001000f0008205000b170086000303402260b1078000c0341d0402c48007100803907205402009854821500c08141104015007000340c84050102036000c0c0e0103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 304028084 1250 304026834 304026841
    0x1517030f0405010503061207080c010f020303040b1603020c010e030405010f0f0f080a020c0f0c031009030c0f030e0d060b04111204020d06061505040e010807081005060123071109 78
    0x201000c0303034142c40c400d0034001d88a484080110b0036900440070003203a148200b100104e48102d00088100084000b40d03150302400038900c404030b03203a00090b580100702440c0c510100d404280d440e6440010038445240042c00c0800c80c2071402e094580325124100c05401c00034090086e940d100a4403a80905e550600411000703080100800e4021409500703003c100740400400d845000c1030301201e140701445012280b6641c00d1040c020344428022034028402c1c400c00c00984440c030f8a44c041d550300ca60301502c4140005015858030315200318011400c404200c144c0c001011240d0301c030100352043d14007607000010441c40d228140001c0b15084001030100100034414052030051070507526074416815242140e00401a1810710003414070358020110480411030700422380c43e4010090070843e0540b401000d41350b40d982e561240c80ea14140034080c840d40028809645e000d03644d030441e50300b0034010325007200702010b000100104080c29101c501e030303c51800034070fa80c144402d42d402542c040310104c601071101d05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 304029334 1250 304028084 304028107
    0x140c1b131104120302031e0a080f0108070509060d0506071e1b03030e070b0307051215091609150503040317060f28090905060a090c030201081801151703 67
    0x4500c20f00e285140000c1c0380e032007098401d0040e61101c0482e401d0b2426a48550304d03c140098220121080000e1894000039082000c0d0000c81c45c1220700c408081c21885007800148413120000915290f0058801c036001c0713000440c00c02030103104010aa440700007000303203080d2100500120341154010003031f00400300c1420000100e07914401e90740c507041c0064a1044410280d0034500182d118280105000c001c21180f19001801041038101400d064140e0740c0d00c040100600141683c40c0540014180001540d555101254401001c20706e04040345240d5407070a40a00361518640c800d00010700120030301c030401d80c000d610000c0400c0d155040d00c41030301e49072012034500c4011040d010310400c0b116941407101c001044000400e50804088041515155441c0201403c000030341140c0d0f074854000012a80400c134031131203064541c04003184150900d15001140c0880c2c026200500001c0c000c0c4030126100d009202d10401040c0101716036000310700e0034850015041d021141c5401c60340040001503a50b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 304030584 1250 304029334 304029337
    0x12010b041a0a090e0a142401030e033702010f05070206070c1b08030c07030302070e04031704020a1e0609060f023705010f0501050604050907140c1b1311 67
    0x540041c0040c41440d501c01041c05e01500c2c50102c0c0320740213070405043c04600801320040c142204196840390344070025100045044030109604214550030512803074407048000c8000b146a40c080070821010b88000c1c05000c07012603102000580982e40d072703480b00d034a0f014140c0907a0f0380c001846d002500003450b250401402208000c1e500903d0308048503848811409041c600b00044d04003501100c0d101c01700f01c81000da441106002c240d0252244072800100c100800081910542e4103a49030518820800009112898040c008a074001a40880401c0028106a10241040d1692002d817081c920340300024041c000c140d00800700708a0107000545146d40c00240000205800106070301001c0c41081141c074001c00340b281c2580160015200300410321505401c05091324515107020091070f40c1e91030070042c0c9403080d40705441d081514100052200c0d40511500e4403099101d130314940c5040c000c16216410503025180114010b8094003407001d590506144207100078064a0013040342d00401180180315 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 304031834 1250 304030584 304030589
    0x31f0605090f0316141807051b010f02032701020f12041704030c21030f050c01150b0d0e011413030c150605010e102312010b041a0a09 59
    0x10b4100182c02114079102045207840b000707007440c0c00b40240f0751124200d440fa10044403849104031400780c44008a03c1d40038440c940154444e40310f103031408060100c1c541c4643e4002d04040d10f25581d80d40c0031f21050030303140011841001da05503100d81d520b0544404c0d9420352520810540c550384103101e003500d100001780c122a003100101c0480400b507a2240b510b02c072a514442c1e1f81024902d0040340c000100410320708003c2c02d582025400714640c04c601083d20840d242c1101001d0005484000400b031898001c90041030740c20b43c0c0d0000402c1e6280c54a507042540d00c0da079846180c00c030303e00040a004070703a150300c1440b040a410000074841c00200607074203c1400c50152608542c1642c101c0440200340c007420410740025802007101c0f4103002001c403098020101442881c1c081401c04900c4002e62500d40407105004540c2c1d1554a02d250403c0c15414100700101e83c001c000043c100040454514100300040c001d003014410141d0300c07406c2000b408408110100c0c42c1088107820b111300e0019071340041d8040305 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 304033084 1250 304031834 304031839
    0x5031e120c03091809060906041203020c030d110903010b0d080304020f01051b010b0103140601021209040609060e0703150f0b16080c01050106080601170a1d0f03031f060509 76
    0x201c402000031000c1c01c61003105896540106840814007160103003400961184184405641d201c3d661000e803e034413088202c070010445907090031054001c50081d030141c01d84000354000c483c00c002403a24601c00705c5440c075080b030300c2c44840450f03451014a07007400b8402d10780c1001e550703c00c2c5542c6030f07550314900707400302a100920690000f0361414180c1d1081c0700365840c2441000f2404410a000800d03a40280040791200c2c0c0000d00308110a071503100e515075018043c1c403040c1d00178400d030720318805105a81e401c0b01c0c01e180e80c001d448000000e15544140550001340c04080140040b5082400c005411034106400306c10031030740146001c000701d61040b20348500702e4501d0343c140b036030711005d2460801560494803801407500710042030103542c442d0150300c441c5c1610950707100c10800c0c0d01c541c80199254641491143d1240a5100001c1c1d440c018a410503078508a4107210398003854031084507a800e0521503103804896a002100b045402c844500c40d1052200a40010240d541e082c804000e00f94852131602c0e50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 304034334 1250 304033084 304033087
    0xc0906060f05190e03030310031502040e0621030f13060207051302070c0b0409020a020d0203161e050a0308090705100801052701060f112805070801060f05031e12 71
    0x19002c4c0940c02212168034020190781e660b26001401c400c002e241400107513000c0001d030341c2c10442d0107003510848050f50603500c04040c09690340d03410072a013000c03030000700e00b084016149682c82d00341c8200040c0414a8145081c41d0704c1c1d22001d541800307030150a0b4000c41c110342c0540c0040205448102191100c80c0d0580400344c3c5c0c5140b0790510440c80ca01d41e900420f200c0000290028440c0040d601130040c404c055420b5401d403001448003280c2d00d0203144100044550380e00c00100c00550b08038040400c150741401c101a45802ca03848071030400c40e1400050300869003080030001d11110074003800c2e001c0e00301152144800c26014800038500c0505002d0070380070341440050040501c02c1800055551110303802c55007002c0d0713107521000700001004491500800c0c0d01741c601d1120411f01107500311a24110340e40c104c3d90035541c2c003d01c0400c134102602c1901da5001d00400420359100a028101c06408543c0074284072514003000e145c501102c0c4501e0b0b181c009038800c0d4241f06c1c0c10000c034031561404010030817503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 304035584 1250 304034334 304034377
    0x90615030408090d0804090f0b210f0102030405030a090f03051222080d030c110c0f0d150504120305040b060907050904060e0106080903070f12030204050301090c0906060f05 76
    0x10410710410f00c00661180000c0700c480c080101107401842170300d240c01814400e403890361250300d054801d8455400e40c8190001c2c2d2000d01c1f4a0781002c0c420800c060703101190384a15016810a089a0040e035040d00c1580002a9401c500307500040383c1d100514030452440c041d2859a01c401e030300d60100d004140320200c00010210450b056410b04083d40000010804000e2941c504078a641c944644160401090030000140320741c601550740c0690240c09a03018013001c0381028204031000030407014590313201c05e40c5140d5201040401500d500e910035151000141801c041c1405402c40c0307034250b002e400f00b45c204010000003c0381c0d60311b0203401c404180c030a82019180c024042e102801010755035a0400e1038800000380c41c650f2065035a040303641715180c0d400a511110a026103e1040890142c59441c0e2015a40700040c0d10b0541445d074850030b0701c0c00508158440c7c0c0043e003074441c041011340c1d40c8070b0039000600c0080064400c05000b00780394100202c0305261800050411f014410482000b010b580014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 304036834 1250 304035584 304035593
    0xf0e090d0e0a05030d03290f060d11040305011a101e050d1406090702010c0504030b04020a0f1706070207050f0f041b050a030f0b01050405190905160e0906150304 71
    0x4640181c00000d090310b00325000b45c070009000f400c080e040c1d5036120b241100c60301c81c1e161840342c5007020828081c1c403101340a89414240401a8041c04108405076a648001900a08140040c0010758407400002c0740c903903103810a902e8045144c130409845114202104148603402c81002c4081c010b40d040751032098001a00186e446001c0d50f0040700d50319091003e844022075a22404070312071802260301d21110707180c550040303080700e082001141c0403410030482440861101c000c8158068801410682c0603900c50031040100d403115445000d2418980b07006051600b401d002581e070000c1c00f072004040036854030002652024480c840b0ba8010102d00d00508611b40700d940102542042c000e8003081c00da0a0010300910962084000034002071030104d226098410501440c8200f040c16920241441c0c1400e042109413400910002c0800e001d400c0c0c00600d40c90305001c0c140c420810400c0310b054071100b14101401401100d001306108103075420800c500d0f075540c46105801309110b80c1e4050384a0382c0300d260 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 304038084 1250 304036834 304036849
    0x31b1b0203010f020c0a03110d020604150f06090603050d0809030406121415010f050309031e1603021e12030a052211040c170705130e100f0e090d0e 65
    0x43d0700d103d94000034588041da800001c0760070307501e4440c0c5d030f40700d00d0020542c24083d102e07426850b004006800001c00b1401044280965a5600c500540001091102c402e8040106d40081d40402105502d9400410500a0601c400750311031680713007800122841e08010300e0703440b13100324012100ad01c030180c200100c40740789951114513450000c40031011749003003030195a03003810090f04000f0b00103038502c42d103131174200e10800a80340034000032030003981404046072203000307040c2c0505003282c050a000e01101c2603070a4085900150507005e034014052000301c1c0015143d60070b41c400141d00709940000c600d543c1c9162030f60101d90340041030503000209620348080711640e202c41c034014bc905920300c5050340b100740304000302440e8a08004403010000c11040e2141500c81c4c0811160300902420030b1000640c08501400040008540c1c0861308500d240d203400103030005000070b0342e500030f20740d0034440240310722007100c103014019026450040c51940ba00138041c41da00d5241030141000c00c131455000d03c00f0307502c4031907 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 304039334 1250 304038084 304038101
    0x1504030c170c071703070c08010203160c0803010e071e030e0606150301030b070c02060d0f050f040f1b1a030411031204120206090616021801180e03040801051006031b1b020301 77
    0x30b211f403180d90b0f8030b14000f0b000c1d400070f8601c100c3c1c588454107810031403805443e82480940e40f0104807802c6a1030800031881500707000707200900f0704c818030049106481d40b1000d4081c065409807000036421003010f0b41c00340340c0400101818041c1407058907001c802c3c0d05010503203044a51100358050075640d000011a502c1d5207036000250010004150200021500c0e0499805040840c0702004a40e8614180c209600700c1a500074110900348948040841c03a284100941e00300300d80b84100b841603481e02801c440740312303040640404074004002d00040200d540e6075000c9441d412002003c1400300e64104045a100301d124048000c00340040d28400c54607110140c500205004042c00d231201c582c1d180c00300a0300004442248501c0e10f035266528000d814401c02816103004030710218812520701c42c014000c212059400070984002d00c40005c1c861024000c0b10700c55071b0360712002003e1a140071000307001d5070120f504000084162250115403035a10282c0d2100e21051212030f24800061400840d00500c81207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 304040584 1250 304039334 304039343
    0x3070b03011a07020a030204090201031d01060501110d082a070c0314011b0302070503040f060f080106050f030604090813060503011401050403020306060108091504030c170c07170307 80
    0x500018004214401440c100c03001694054a52400301c1031941a510480c0070081d44402c0002042c400b5081c09d503c98102588107040014481d4100f04a8044500780c1c1249840c0300c2c0e44a4009101a5074840304c40051501c003400245440e45020320041d04183d401031200c0d24903501450341c81141c01c0c100c0304114940c102204455030781c603518284910003251500098030106000c400268840c0f90501c2007061b01106402c42d81504042d030348048019600c01081074a2a100034030022804013108400f4030020b01c6c8a848511030b200b0004e01c0a00030b070030164071000c1803200500c0000c0448442c3c2040345d80c0700354115000030b030080075403805000074010b450810404400d103820118009400000450603190502e2903080000030203401180c091080b404000c1d05900f081000c5025075018007100c580003403404040d07034071110410201040408044070180c0019a054030318106021898810000130400e03c021207140000e10003020b0b644001a2061803100c0b11ba4070a2007040c1082072050340e0005901 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 304041834 1250 304040584 304040593
    0x10603050c0d020f09011d0306150a0302040f02030403031103090c06072a180902010c021318030e09130b0f07050c100219210e07050627030c01020a080c030903 70
    0x1201300709845600481c0d445070201c2d14140c2036511003651000101ca0500d0000c0040500e5a90b00303c4070888004680b800c580c103d00786410210050b0f40780d000303150309090301090040e140d2030a814000d06903001040c01d046061750420521805071000f18030325030400d00a03291281d496900345041c4084050804485a000c00c03c1c03903281c104200760703109100403a504080304500c0e403908548854112030002d40c0c024003150740112008018100340038000d10034107002c2ca0002e1000c0140c620780d03840400c017030f50881c0010b410341c80c02007072413a00c0c000441d0070001c204262000c155040d40d40c0880c0c0d080282250b61000f07403c0d80002d10a51080c81190141540700c01550031a90400b01020042d40200074100000d19008005449061240c5115006050328407105110000e603105510300405281c0c10103221800780781700c00303e40e9499110051580042d049903080c410300341c580c0300c000c150140000e00b0388290000d42106c4810780e8005030502e00c00d0f800c005c1181d0340f101d00214852440c8603801455806014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 304043084 1250 304041834 304041847
    0xb011a13090c08250813080301120b0907060c0609020d060e030c1e0303010506160b0705041d0402100e1906030e0d0e010504030f030e0a0305030d0605011106010603050c0d02 76
    0x1690381100c81d807a400b607164800740fa00c03140440c140d02d1007005081000100d502d4490f044583c07103800d5081d0001492804509195220340707500125a100741c10038a141300c03c5800503420020b010024550000c0e01034040c0180c00d003441c50080080c3c1303421001030289a01d5a20400540d5a4a2020b850041d4001010881c642c2003092080d221f8001e01c0c940301650080100e41e04480403000c1c88511800c072950040c42c42c503030a110810000c1c0d00b00c1c4641c08003d103a04984400015030b90501e450081d10640c40c2e039521a03150141a400c0814941d403900d1114034120188401600e40c20110700201016040549016003504040b44400c9008140e070400304e028640c0c00203101b030700744d403000b0f03080400d4074181c036280021040d007600d0003122602c1c0540001c07820041040859540000c01c14003500c2403410380c21100e01a800a024403035660030030b840641000880300c00c00041c503c10440108000e080599442c500043c4440c4c441d20b05108400a15803520001a04807404000f101c8084030110070441d100c68 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 304044334 1250 304043084 304043099
    0x70219060801170319050319021303020f01051801030b12011a0a050a0e0105010c03030b0d05070e09011a040f0204180b01020c01143702030d0c09030b011a13 69
    0x1c030a01c900b015000040c01001c001100100440f212019581004254074261800c1150581e10040811603503030101d088a41c0c600510340010101503003001c0100070300b2815401000a54000c0c51212414000c007006107050040c1e030514146031403042400e000800354024030104141c203481580e460815481c1c03103c80ca0400c03203030640000320b4040541d040e40b14942c945061201e00c0d03c2c0d074010211fa0040c0c59004004541c0b180c3c02c800001486454042240311a080200710420708003042100c10350000303502804a007949441943d40710700e2120081c00b031a80402c008214985800403654080c0f42c0300d001b03da1004c229501114000c0007a08040240c90340306c1e020180042581c0c0207414014000d04014842640c42185100c002510b6610640e1070302180c40d003d80400c01c401001c01644500820300d9000c1d042e07601540c0800410540c0246079211200480c81045500d021000d90901c110b5034818400303d80e09180c91810340c2d0081e0711000a80c441d40446420034001c0c8000240e000100a00206621 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 304045584 1250 304044334 304044347
    0x221103010f050406110c030d1e0e210f0906070807170d0c0305010501120209010c05070b07051006081e03071e050f15070f05040509040804170309090a0207021906 71
    0xc0740100d04c00c1158906896a0380c5e601e01c6004464a000c3e4814007820000b003103940c0c064070b0802031121301c40c507042900f010200f080c2d82c0090a5401507401c081d02c503040f010020f095400d0a0030303141802c6440c09024100c1d0103a28080c031031426000ba100414030b00100f200c12070458980030740080001c8031101e101508a03071181d001c025003248640c01c114050510074028011241030f148140c41c2c01001d400741200e02c40c029044900c0150411104041c0300300425000e01ca54401380c4074080c01c140d030304c41090a1062410025000141c00146041000c00080c03a0100e001617815002d0911109807200c2e07140e1684c038501030f10704086d203018591074141e100482a41004002907206606071507164070f560b40300075260300342801002e10100500002070083e91089001d04694110790500604058845d0301088040104a40440382c2060010b0140110141c3d40d030f03000c0c0c2e0a000310001b145042e01142c041501d100b0090303c8030000035000304043c0119503070754002c0c1803408840c503000c0c0c8618be41d440c2c005014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 304046834 1250 304045584 304045591
    0x501080a02011814130209040606082e0501081b04080307110405041a0a020c030d0e060c040b04151b03170106180308161202061509221103010f05 64
    0x450780d0032020000d031190350700044084032a00d0201d038040f2480744d03040c408001e0200036a50034069080050905c95950340c800c08020b424241e5403a180f51805d04510b0312400710241144410fa1000b070341196402c11510350190a0300c2081ca80201c090712440209000c0d5282c280c1e001c1d075000740115000c6041040040601300d07190085403080c074007000007024442101c1d801c7da000780c229022072806088201070368900940000080e0001494003068a01860550308001c02001c03a40d900c1d440c400307021620401110b0340010000c0107151034640f41010140e03183c0308074402c100074011b0700c18407882503d005d42c071200303c800200f2050600441c000c1c03034020202c00c030704181d110b0b18110681c00031030700301e214050708000c4540c0b03003030701905542c2151126001500980f881c426501008201d9500068400e010300d100e40d00d480e0010000381c1000340748000350440d00c11140740229030900421100c201c0d0400c3c0c241c0743c00a941c50f103254481c542e060203441824240021500366081c11481c1c5034015155204d1440f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 304048084 1250 304046834 304046837
    0x28020d021c020a09141b0405100315050f1305070e0d030818011a060c010b04110a0e010203030f040f1401020315011e0e060d0912110618070b090102030403060501080a0201 75
    0x501c25203480c144800c580e13855200c0100c1707903110760000c2d101d49039071000f81d03c90b480041e24103401c007507a507800505080706100c0f170311001030780341c480894424181c901c4100107450111008000f513005e00000c101307403c81408000c6221504c800200700828080c1d200300420071000341c01200b03502c1d402c1c20060a00c03c000e40328070900c01da03601c20701c3c801d00304107204001c2440c040300c10085001e00c41e1070400c0300e9600114140a0695603607000c804060703407144186031161180005454035900250380c00303054159420340c0e00341950803c20402c1907032031001240ca40e00c03c2e40040764503890285402c0c407038034a00d0702c001c10644962002040c059540403000c406450280c00340e0f0f42405559041000030303a040c0000208038041500e607008007099181500107040761030034414000601c5c200300c0d103603805003440f081c401c0320210b4805e80030203480c07003424480703182d001c2c0750700101c14070441c1d2044030103640c0d40162041644050b03011850a40d560310920440d030003150000000d105658446c2c4546440e9442100e040f030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 304049334 1250 304048084 304048099
    0x812030601080a060e06100306080d09080708010207110918010507050306121911121b010e0f0307050f0402130e010e0601110309090705040302031c080928020d021c02 73
    0xc02c010214052201603a600c1720b440d10b00c1c0e03200c10044c090780c0e4a010742040d040c9070b00c450b00032031076110412040030f9104040d60f0342e405151411001c141803d51982000c050780c4d00400005021800890342c2d800a0b1070107450b00602e603034075900306414540c7d4003607040b20320394204400d2212250f800f101950249104a50a140c1d40100358200c0303648505802420540311460390244000c100b440020080400024005540d01c4c112080303242d081424940046604e2815030b042c500d480d5130f000500240c400000d98070b0140402000c00000c6d951520b62040500c50f24005600040d1600c41d9015560500c0c20294082001501da24a456003c4000d002c0c10030307030a1008000890642c443e1400c4a245421540518030b00300101f401c0c03020602004103c481403000c00c110000050318100220711450b000b40401084007034903004010000800130b0000b40c090392245000000004100b42100040001c2500c400010411403010811415510340302950110700c0f1040d03100103014100044482c40c1c8201d6100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 304050584 1250 304049334 304049341
    0x60a0e0f0d0302190c051011010f050103080715060519080d0201090f060e0304180c020607091505070c0b070f060f0203011a07030c080c0d170628081203060108 70
    0x104096071204406801070344a41c503c04940040c0d041401011401019400e180701e440e2408980c81040e8500702e03200240c84190341c0f1112207401c0c462704071740941000b0280015413642e01da0410500a00001800c1e0f05a102d09000d00b900d4158072902c0108806450301451000790040c1c800d0a5480348070381a118000c441901002d98410300c550242c566000406030340c0c400f8030b6203d500c01407154403429402031000300000300340034030101d4000130111480d00008c150030b404510001d0070480c029201d0301c00d0242d140c00911003000007400c00c50200405190041d2903036a5400d2448941046a11002c0000000200c0105000e611000030450501901080c05420b6440c0e041c5022480248070308402e0560080e2103019174039100b801070401600910300801566a103403181286903119540d45413113035011107401e0746103030b800900c804682c0d03a070000c00080a180400110750b60311881450104c1c0e0002e540e03001403200480c6618440070f800b14004507011962600d1309154650310036988507000c21100c0001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 304051834 1250 304050584 304050589
    0x2d050c010f090812070c02060304060209031b150904022a12030408070f02031606031d03030907061413080a0c240e0117090304030b0141060a0e0f 64
    0xc021000fa84211550304e0407103100d010000f080005020f001c2048642c50102c00940e5a04000c0d6024900541c8016503a50b1400d04041c0b81c41c1c8401d240c200440740000c101d00d15035031071086070600e45869003c1562394a05140c0000d00902c118040700ca542000f0301412004101d05030140d12070b4a0002d401c4640c8110391940c041e40f00e000440d801054610100244c0e0001240c4200c00c1c2181c2e80701031704403401c51000000a001c11449a00108000781d82d4102400c046070319181280c424500d9003001e5031460500c1c207040360705c1380c101d40100b000740070980d6034103400c482150781101d8586400c03c907540243c0d0741b64004e268907a010101c0913502c0c0b003c540000f18141413203c4290b000c600c2030410400c00760203030354400d507030140c4100c03078041c180300750461a218101140d02d01c41c2d104520030400f540da11400e600c1c0143d6456410307000180d080c103116005a1170740304544000b10721200400744403100250211824036071980c1d50031403d070b002400480c080c0e400c150840b0340021903090413141d19039044201001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 304053084 1250 304051834 304051841
    0x50f01291e041b030c0509060d0b120703060b1f0e04150906120203060a050402090f060d1e12020c0102070603020c0709060e0414070b0a2d050c010f 65
    0x20080c0303005482801042062030868034504040c91486084011442464006000c0703559079002d0300011048095244000c5a16206114001469040190a10000c6030104050f400b51040982d00d466441490711b00d255075804030480300440140403614202c2d145c3c0b61000262a0b600603040c003e035115044815900480c154054003121169206121910001c0402001e000328000c010407103121031002240c1510140034403c01341c0a10000e01444038900d1051520706000100044e52041c544018000140d80ba4100240c014544031101e00090b10743d1030008402c41030504004180c45039002d2002011400e5000307050405014100e040a4110180030598a54241c24001c50040e006a441405524080da004c0c116641e142d00c21118040e880f100104100e91450b000303003560744010005c100410421240241c0c4110b10f0030003501d01c6524109206016006140050041c0880140041190031081d01c8001e240030b0900f40b80ca50340c81d0350380406400341e4440c0726442002c0d400c0019030140080c4500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 304054334 1250 304053084 304053131
    0x60b1014090109080f011a180123040c031a010c0312020c01020d050103050303040c170d050c21040f0f14040b180717150102060a020904090f050f01 65
    0x49821041240410030080194400315540d4180003e80c6000310300e018080003c40e02c2c1d8400d001c00040c0c07504011441d100300241046890b44a0840c15090241003a2400080340c1110803040b400149001c81d07010440602e80c003009030f43c0c1c0140c03414901c400c6a0754590813264040700900a100102d1142100450b4450b4070f81c9000703002305840c154142d80c505010703801003803d503041400041c01c15000c00031010a40e80c00b07a0042e18a54404400e00c014010115040c80c02001051200400c102e200c01c1c4681d25110484a03403028000007081e810b0700144103006000d40234140ca80e01070b6248844014011068015004400303d8502101c0081040c00d00c1c42988815201c0c4100784010340d003001c0b402c11000e01031580007a9000518071300d15081507106c1047c8140144e401e501c800c802c0d012819800c2d542202d0003000241d41440f880f044085598000c80c03216048041c80e040541d079000c2c0b90020074003410300c1c08130040c030107002801001c05004010900c1044403074071600034480c0540b1001c41542140b9000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 304055584 1250 304054334 304054337
    0x405090a0201140408250506160f080d02031003060b0a060c080304050a0b0a060303120908030a05060303040f0b030f07030608030d020307170901020a0e03190b0c0d09050a060b10 78
    0x92403104003640c014007111409510401c1014a001e86411038a420000010824030b5401c1e051000c03c00d00150b00450400501002d0354858280004001048104429028041c101c0300000c400c034410302c6004400c8448020f10340a007956a07041503641450a0300700f030310040d030300c0b03078a441c0840d80301d89071104452040351450740d900d0300856216241c6a9841d400548101c40078403580039981c00003001003000c0b501c200590680090313503d245090142181d000d03000759420399441c06141d80c0c009162901600d8101a01030400521940c03807001017860341c40b65401100003545000c40001d039624030480210f1189040071800038881e15002c9003941510303403c0c09034815030f42080c45108140300d202d501956100140d4034080d9440709076145a440c902c202900d640f2401d9400141042403280c00800c03085036544160b0040c100c3c11650f001403146051400002440b00e400e40002c0f48150412409407003002110100030440301480d440c051380da9010498007229142d09100b00385c207203072500754034008151005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 304056834 1250 304055584 304055593
    0x40803040308180d03110f06010b0a0e120106140a14010206061519120c090806010504090f05070f0503070b0a0e1c240b0901030f02040c0207030602030906010e06040509 74
    0x7150303161040380d00300540b106581d00414000d0002d076030f114840c82074920300985800902490625034a420042c1d080601d01a6510030001000588a80f000715900e020840c40c20405005241c40040c41e203220070201d1170040c0d800c0c0034021400700b0803690a2001c00208407102403160b175407650f030291400da5050f141070140c1c10040018040f42003c080e00388040700081c000f60306d000000550b410f884103038a406000041ca078040410841011441412010350541c1091007408c0d10701605159285414001c160203692626103a9040000002071180c926174031100b0340d9035664031000f816006400d280f14840c400d10a00304005004900c950465070750b102d4503503900b101c1381c2000e01403020b948951003909220307a03003204035040410000d010b840c8010f40030109040031002d101c00704900b56400713120014450b0403290010800191421040c1d0012a4192004100404a41001c0c0d0800d0240d0380041c000c2c0740004200810410041072003416203d50400110840c1c44600902085440489103a5241d40c403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 304058084 1250 304056834 304056839
    0x230307140d1401090b0a2910090906080105070e10020703110a15110c04060605070204050c0f031e13020d020f031e0c09010806060306010b0f092706040204080304 71
    0x1007864031084418011500d444102c2d95214019003103668002041c0d9210400105011050601f4001c80700321800d44102e1030303000540160200d0b02c45000032500c52140320341c810701e07003104c5004607500c500030608024100000d650f03030781c8a2400303400c08488600000308600744000b41c0d444c0840a18006115550042c0402411903071a045a07421200d401030b40455103100005400980000c1d1303d0100c060360340e451548101400c1d079107103008000420240325504010051141e070758401d007a41e0348203070101c0e0081120b456500c251102442010036580074404000704012617140141381112136215262015501d40c2d96503d480106400543d000075441140000300c0b0015141c0285100b441c10001001c0c2c0e1847d820941200c07400b07071100c3c00300410036000b82c200c10490380742541000c1c0c0180380b20800350040e0700d8008002522940c1c1405101c01f50b51011802c980040060416240382d81400b81080401304800340840c2070f0801e601b2643d2084414240c00190a41003a000391400c550060000354289070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 304059334 1250 304058084 304058089
    0x120601060c0f020402030115030515010f03180b04050a03081e060d110913050705090609041b0b13080d031116050a021c02030f19060e031323030714 65
    0x1030803a070300380c0b03071a0740000103180942d4891004500a1002c4c0705041c22203515104050140e8030300602500381010b4000c08241181d0700414018104a45490b00180c4030a4168030b00280b0001c6410190078000c0400420003007000005203401181d00a03150282da42c7d654a4000b4111031403c100b02d40310012a41c00300d02e050902203044034800d88501081800442da94011410300300b0100c54148288541d10184418480c0901c8400042c2c0029202d0007140e241460128a0f02c0f80050710080000079441c2c00702440d0b4003100801005440c40305440b03079541003800c2002d400003481c2d004040150150440800c7e031180244541401c140e00003811905104c014602990320400e076810070380d034074040c51300e40000590704d0401c888030b0542c07285607440035002180181458080c408031204038590009480a010030894a00005200c0e804a0045070a181030b41009085010781c040c1d0032000d000520b03000c10f500b0044404140441d41c1010001c00041140080658511240c41079107000c1403050714400e602d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 304060584 1250 304059334 304059347
    0xb0907030210140c0d080a0b09090d08041a0405030910020c03060105130618020c0f03070b13020418060c030b10050d020a02070308070308010e010605070506180c0a0f030c0512060106 80
    0x31503103e10807814601e803594442e00f08140380200000040c080300410404030f032980300300111400140c48041c541d281c80d2882c1ca41c3c0360968a100070510001c1d000050030400c0040a503c90310342d40e80c44001c401c0c04c10b49030065503901b011083da88a00e0b02c6070700d0240e000703200003055050140014002c1c20b00380d103400b0512444c150002103010226031200c1004c00c14215424500c0615400e403e00140d40d1088105111304082c102a80024140c004004600102c3d124581c995004240c107060a540c4081501c0000c0003002c03404000541c2c070b500c441c030b554144291a400007030481e2550b1414880e202d8400100300060180f2080480807500c14000d10946441c0d640c040e11704803d0b1030040f600c503607440c1d4a8010302508450f001705c00240f14000140a50543d40040c40e0040c4000c3c14424140010303503031480c3e00c8280007404c5081d209100e010340854008204615094541e018040d00091070320fa0b0801072000506000544181071451000591828121403094482170380d9805000e0503401d100c81120003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 304061834 1250 304060584 304060607
    0x306060a0309030e03010929090a151404030c05010605041b0809010e07030f0515040312051317040504050f042312040f050415050916050705010f05040b0907030210 72
    0x7000552040d02c601390700c09218000119000740c01c20151301848903511a01c08032610b80c400e810200700030520414030000144150440d074080c144000011a045000d4001d00c00902c800070801d40040a00043c903402c54040301259000300000d0107419120300a10083e10300c09084c000c092017021f000c0c10f41c014400e05409400c01070700d100104440d044009001d2811000380c20a079102d00d2241030070402c0110400400c0e9186458000c0400301c2d240030b031030181c400c0c10000740301c210311a181e10025851100b107180080c61185e104600d0882d0181e1031240c402550041c3c00703260300444c5041d000ca0070009202070410321941e0322000c004114500c0a0403400350f07024400d841105d0740319180c01400b800710118098405418160345030103503585032008000c00e40b440005c4c0d23a1030b00018902d05111545481c41400d5008244410480b141d480025007154144a4444040e25551a02c3c1d070702d22001c8101d40026021ba40206642c20190f201c4588140e03e8200c9880000e41c8600745400c52103050f805414074036038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 304063084 1250 304061834 304061837
    0x1080c030604090f200108070e0607022206090606300c0c2109060c1205030903090607320d121b020f0d03150506090a0f0f0311060306060a030903 64
    0x143c0d074805d507112100c0503414070324140c00a40c01200e5180550340304811690040551920906084a103004501039200d1040040d014101c001120030020034585440b40d404500703100c0c20000030b0f5a41030600000c0043c0d005da07400080040b04031100040415205450a0650700c40e1004101040300300710340200801107401041c0809880c0c0c1c14045041c01c1000300885181029124154804000080c440070954000e142401240c80d1340e00007041041203008800b00302406c0031542e07a203900820510310b001d80c0b0081e0303030b21200c0040c81c00c0400814903409010480e080c8890b410040420403080c8018600880a4034580d2007104803040480c0715601c005000c10000c20b0000703a00d0419005420200724030080c41000da403221201083c800d50802810100960381c0c0790420034004500181121401c107481840c1c8540004a91541103581300301000c0d0042002440a00c41c1d01d580d6050764407209800d11060f00e1090003005000d54a08201b402c8034402c1f04001d00c00341c0390054140c400c0e030082001d00310035070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 304064334 1250 304063084 304063103
    0x81c050f0d1407090305070e090604030e1504030c0e0c21101205060601020f06060d140f07081609090b22080310180c090e09010f110406030b01080c03060409 69
    0x1201140c00c800b0150160589a07510303d0000d0440c2403a52030500d2170352007a1000302d42da5080042080d000325032a40c00940c545004041e0b1f4181c1d0f00000c07001440c41401d09247d443c0002d0000420280300d0780001200c010300c1e04c2c0b1107603954082c00b1a41902034502c41012800b1420b0f1180c076240c0006c0c00c4690700a40b0f00002070001034403480110650102c0762001c0300c2d40e90001d010300810b5a010448040c0e48400c004c010a01407400001084104140c580001c204005400342030400d48000d10522402c584d910044030205980e40410644d5010301d4034050003020f0b03d000c00420803245a0054080c8035820a84604050304da0000d0005081c482c5445c09031101c50b08c51484002664450007540900c601c1070030700b020b41e42021001d2480e02040280c2d01c4185140240150f11603800070000021524440b0300441b2503070394035181a001d050085110b5040d00c0c0360031144181240040050002d8658540e000c11804040d44015034880b00d0555041c0e03031101d02800020800d1515400401d60144960100c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 304065584 1250 304064334 304064351
    0x10c03200118060f09022115070513060504231311090102100b0d0f02010c0510090b0a0c080a0507120504050106050f0d080301050402210907081c050f0d 67
    0x242194004500c200382d41c07110407281410b01040b0700440840c1440a1000c001050311980001c5150100c045c01c80100800300d580c0b504840c0060100940080307451160300364629000340010070360b510160400307021910a00e008500c1c540300c0c2c02920141c0c0c1c25884004400300840c80141c4801095070b101c0d603032080c0c4c546800e00b8810752a0141c458600601c428031030300c1c1c010780d10000e8146100402040403191a0140f5000d6075550b502d0090201600314440084080c054001218000c85007030014015110b403031481c00d00180036070300c0404c41d44e0141071188690380760510a042552820070300c601c00a800d0300f000c1910f0f00703d82d51126401c0416400e24481601c1030400ea2000d50300b0440b01a2004d956445081000d0300300b41310800301000086403607034040e640b1a0386480c5103000600031179010726404610b10211140100c2031201c20340c6000f4040380c10340f51080d2095903844860281c1c061601940114561000e20210241603500b0300303131181814500d1083d05a1110707048144a6892a82c41d505803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 304066834 1250 304065584 304065647
    0x9060604050a06031b030b06041e0207230303070813050c010f090f060306090c0c03020307030e040b040207050c030f010b1804020604031202030d0c14070f0c0803030106031505030606010c03 83
    0x5140384180c4960312005c0407031841c1480b802c52031005261078042d5040c5607103030003447c801c24100c0c0030880c0c06540040e1a507929040450100700c0d81c2c180c0c06840d00c4d101414040e8148004040c51240a0560321408075030785480d809480314040210040003a44000b07010340305503000d0000c00300d0864284c40d040c41703c90764680780301c03100781081e51102000c25661081805442c1d1140101c1c600704406042070044146203943c020350340e00c0380d00c6025041020540c01501d40f542c55420205000100800a5407280b6450130083d890307041c5040e038203210340f04031014903080c2801805040c4038034a0081a6040f0180e141d000c1241524008000700e80c4601d0420000c00003600001c2c1580e00302c5181d5005640ba40300c0030344030b401161003901e0031000b0b0080c400340100181c07003d1422201402d07802100c0340940622443c002d2030704001500145040d010100002c6541541640043c1c0901420441c0404407a0f40d2010f142d00c60f8410b61341140001d607071000400c08a4041c030000311220306064200c000081111a2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 304068084 1250 304066834 304066853
    0x3060c021b0d0f080d0f05060d23030d320103021c020103090503210c070b18031c27020609010804150921030216170403051e0f030309060604050a0603 66
    0xb4140321700d0340d1707901500c034040c2c169124403684205c1c140e5101c04410b5541d251940786007400304608600400c141d040342e545110034410b41e9170081d440355040c0140e510040b1009c1801040d5a440c81e210320781004840071840e280060141207c1e009014850450f02c140e400340030103850298140d062603202c0013921300182c0200020042900d00078104105000e9003c045140040050990340e595102404804045411203048035000324030b400520290040384049681103008501090550034103041098259002a40004035200b150007101001d0703140d515a0307483c0240c42004040d401c400184442507255015050705d0781c0050085c00c4000c980b41c54105250f0a03a00c0c0544200c03843e080d441c0f245400b000d024490100851450b0609508104800744a000c060b200b07140c4c0588a10480890000c28450390021640555080800d440c5201d154911018414004440242051046a8401c1c2000304013000b03682c012050758010b070825403200f00801000d80800b604212005035181400000101c6121 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 304069334 1250 304068084 304068097
    0x7020a0c080a0c0b0f04120309090903030c0210021309090204022203030314071b0212031b070806100b0708090d03021006090507090509100f03050703060c021b0d0f08 73
    0x50041c0040b00c9a03241140e00190550f00140a00340240142140711020300269029207a1458002c02400c2140c10121020003295001000e09813908242c0c0d010b05d545138000c261003c55030380840e20017054a08241e01217104041407080800d94100060003180166000201103600082c030240c100401c1900c02c0046003c400108206007110b001c0c204105a050701942001214031243c0380c0c038030f00c0c1451000d0040d86200c00c00801011a40d2806811507550034010504020400c089039160303001c0c81c07800c411030313880e03511000b410307100302c0e100080e61b8000020701d144582d084c5440c59204078540b102e00b00700ca412800b012500c04209010706440c94403256810448280282c0c02000d501100c42c900380708444a903040002c0c0941000100941103800503035090840c1c0080e218806a69101c2052480b40400c54000c6002c01180b02e10000a020000130490b003541d000324070802c04907552913026603071840c0329035032042603041400742070a851400031035040740070f4040c08100700c0c00c03011651600040e83c00369 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 304070584 1250 304069334 304069349
    0x803060f040212010f12080909190e24040503091002070815010303110609030f0a0306030210020706080c0309060403031a041d01060803031909050a050d020703060f0c140307020a0c 79
    0x3e0004209000b600c90004005007104400030a051a02d619516001c0c4240516940603014031804201900c14620b40c48800007a00300d002c202010f910321119407034180c01c80d0f580c3c0d00e1a10f40d41294400008198025000d268000000c51030442c801043c04a090114514101540140031001407900700900c078018220032085134005481d8110724015114418295210126520260800107480300000854206503841030007203441c1c03900c600c0200d010b0a05134000940025405140104950300050110190380d190b464445c203656941410309001d001c201d40c000e80580c40701000c6800710b07029a00ca10094130111840107030140c4444049415503034036002c0c28039510224540241084420320400c8050710b0342401031442d41c101440781d80c40701c40b03450030341308022641c404081041210820054601d07561240507540e1180c2c040e08007175101d0f03c0313502c010380346141402e00b000d00540061043c8284e41465459040308511042003011840c1c0000385480b0551151015450108403002102c83c010001c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 304071834 1250 304070584 304070617
    0x16081b01113f07140901090501050f04030204060806071e080f0a060314070f061404030605060d0506010602010b0a0504050106050a080a021308010209130203011d07020c060a020a021002190803060f0402 88
    0x207900b006103400f2101c0004c0d0b090b110107125110007a0792006151080300c009103040c075142e084101089046108541c030080d806490032100184414011036000d01c2201140c6a02d4015940c20924461009240d00404009410341c40020703054802c002005030030102c15140055043e8495a44414481d00c3c0795000000d03900080c42001000206920840604403900e000c0d501241c075141100170390f0240b07000041015440d0000100161600a80b9030b99068200b4111845569a910041e008005481e44076001c0e080441011900d824280039041c100c074456954149041c0010108442b002c0015112202c040e40801100b240c48a244038104081e0000500041c2d40d196240c04100c2c0100e40c079007001282d0360050004001410000c50840750392010b4141490300d5543d003150403820441c030002c400340e200d40d010074200d946550008220504ad8801d46144c001e20309034400c180d9035481d90304c64100c1b5800e0f03000202c00004442c035000d581c20030000b804001ca18400c41c0006400c0e0b80000c55400d094106 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 304073084 1250 304071834 304071841
    0x10825031e0c0303021506120d030e250306201b0c09100807080606150c01020f0406080a140f0a180215030f0c03060f04020a0516081b01113f 62
    0x10448558000e4411159440780e0306230741d00c80c551600da0642056007890b540d6664002400810312030104585110486906052410b04071005890110300058030190300d0404014074034445001c05481050800d80840d051000211051446040382e44050f55580940e0700624030700d0321540c5480707024000c19400803081d03034101108a81713810410b034011501d07a405102440030f20b8460a12503007003034080c2030b4641d0790b0707496886055000e445014034a50840c1030002e0700080880c0c3c04805240140c052200900c020311a410101342603a2080c0c4558103030b6101c10b000325541c43c41550103c100410040800448104030f50002442d8103004c02802c0c0c0701500002c1001040030061082c29480034180c0c10726811030a140000c030b5451101d0400351401103600169500c4858014000c0d00d0180080444da00700450091500c0d0079a1b0700070752600d07111040400403280303d1003010700030103a85d04000700d800c0d42041d0b809c40c50303081c4030040305104001c0e48100031340d000c1448035181081d85030821076401c5030b011402d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 304074334 1250 304073084 304073113
    0x10e06120a14100203061807090e07080106030b0612071101090f051506010f0206190b040f0f0f1424060c150106050307020a03030c1115010825031e0c030302 69
    0x20f44030880d00b158074410010408541d981696070b5010071038240700b140d45540c460f4801e03540c240454120090b107500704401c01c03092581c0405040d040c0c800179903082c0400070310241404820b0240c0c01104240040c1c140c00070301100d1080d001c880c511680600003003a550b907952540d4190a526140a80b159001106001c4202251a0215400407001e00c1c0210454000e608001d481d080c016003021110380c0362050015400900b90001142c65100500401c60260350b504034030f005050580140c5210740c00c083e08840034401d40d00c921324549291380a200081d64828801901c000586c09a04015080c0000001942d03150000030b00440c91510b03006148510100340c5501900805910160800004004110000c0e5000ca5a0300499905090201e4000a1400c007070352006483c40d2075040380e01c5842d01450000f94031440140c100d40e540b8040c3e46075800301d84540304480c12440d5246001900500b420000500a01c119026107400405540c8110003144e407034500030b0344164420340059008220410810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 304075584 1250 304074334 304074343
    0x1201020414090903070303020309101e05070503060109030f05010912050d0501080a1203020310030b10180b0d0f05010f020d1a09190c050702090906160207060503010e06120a14 77
    0x310301c100c90105080c5040d164443d0740e845004001010150080081030310408204121207000c2800030041c4004607051045584800c0940c140084450400c000705402074010b4048030b0060790181e647d8043c450948c1c4450b030584580701d000315495946c40e00c80d90041407110071040c0b1a0366181d9540359840f0015212502640c4060300b000301183c03c0002003d00080390401c02c0039105482d400c0140e16555404484170f4a01031075400a48048140d004002d0b9000d01c4072460303400d440c1000d044410302458600e9480440380142055900140070840780004516070941c045401c3e03200d9000403034150312420840041c0e8020f9880d4000480e180d9510000d00314860501c050070348005c0d540002c2e5032034411001c1c058100400c900c002499501d030f40c0c07945014480c0040790f07002600075000082742d04100c070000741d0320501201c000358074005200b00c10303080c2d5102007443c0301160301e95500e0900b564208500c1201c030703800c0900b0481d88200c45221861801e8401c0c07080c011050b0080c2180820b1481560741e941c01c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 304076834 1250 304075584 304075619
    0xf0a0807090602060105061b0f060c0c10051006050705030412030e04050604020a0e130b06070b0601090803030103080706021804090c08070626070201021b0109050712030807120b12010204 82
    0x83d90407210061200d500c0300400e03500700e1084404c081d1090101400014200050010041ea82c2c0c00340600700880c91015000910040c030080c0111a0400f100f1051041214429224545000c0c40d54904200c80d0348200081c0110f41d004105480ca860b50b1090a10310801c04007200f02c010440300c0364481150724092084030f038000d50035a4103510f807100c2018002c00c001032583e45c540c03168008011101c454045980050f560b900041c3c00c41d6911483c500b801c0d00d0040084540301d0014501050105003103402000f40c0f4101c0f6440049581001d00581c0c1d0303540a03402a41d03a80100c0702c20b0704c000c0030580e6150b01400070280d0003862a07845690902031150308084007174211a013070180005400b82c4000d420304e108061084088400050780d1070f10030003240a07105507a0340400c4100c2c05040c034086000103511031400d0303601c10390450344881d944181640c4100510040500840d640c940012502c9015258074500d0b001207000000382021a9400112003d850b46429a4103a40c04941800607400b6022035940b03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 304078084 1250 304076834 304076837
    0x1171008240f070c120e130e060603150a1a0a060c061a0315190203040c0906050411071e060e070614040506070f060b0a1d0a050906011a0f0a08070906 66
    0x19440d200c40042d040d041c454800508500c117180350010341d903104880905813401c0040c0021306440310702c4600009403900c5203011180b03004210120303a140c0341c00910041c01c80700c0ca1220038026662060664000c0c4100d004042810a01450709802580c54011075005004692034404008040741042421039186662044140710100711440140d940040c0003030321499000340380c905035500c03504c140300017017024001d0300412070003c800d00040003001149403080d03400444040114540e00e0040000740c4501e804034228200b020401c0e100420a5a0301d401d0483d0344450503ea81a0003698607282251a2031140303101c3c030781020f07070248211a40036154044001e43c42c505241420b0501c4006103052041840042146240707400f1482040b03007540200100040c010101d0710b850365100b10905940401c0b144103035003005e241d00050001103071445890300501d200d0006002036800c1c2014008001701c14040b0143c6a84141f0900c10202120350052a12840f00d540341c0c50305090003107001d40302c1ca8640d0070035070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 304079334 1250 304078084 304078111
    0x60711030c010923070e0a0f110408030a0807030515060c0309030604050f0c010206060a0b090a0312170124030203060301150f031112030906090a05030303040516050d020117100824 79
    0x101d043e21204150416054100003501c144681030030300041c2750190310380040110105001079000d0010001d440c000b0801d441701113899551340801c40440308201c4800c1d48151003215004c3c810f04010015090500d0b44d0ac08983c03401c0380301d100080c0742401c202c4040b540d5500442c190000c856041c000341e0f9036002300380014a203500745000040e41c6a4403074050b86444000100b12503107a40c1d01c00b03041e030000315080176000e052078001210052071503103034443c1d00000c1001c02e4000109a0110292408000c041203460030201108860490103584050080b552541d00d504990041d43da031444400c000303051900000d506545145402d5014140402d050352107030202c2e80d01500c8118011048600050040b030301680e5803041c000004001c0b202a400c26500b510010041000b0000300140000f006181c103400c055400380c0d10420041d0b00000300794020b0010b02c006030705208154603101d101c2d40000c03204582d031541c03a032540516450213823120382c0c5030040360102d0101c00c90400f11803081c5400c07a50074003114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 304080584 1250 304079334 304079339
    0xb0d061811101d0a12050d0f0e030c0904030509120a0203012a0f17182109150702030a08190504060e131b020120040503060711030c01092307 62
    0x509210145000e40e2490401c6041c03010440c0e13202d008000281c41035451903610741c0602c0c10010341d1200700740440b4000c501001500d6108902400c0e00e102c0c80c0000400170081c3c1400101032200c503100c090f004a050150911030303080b09a07038494454511100203401080005034900404d429100007c024100d41241c500d00c3d04036424035041810071180d868146010304100b0b1160855100250050040f40d8103000c5043c82600c10f04c2c1d0301004e040098020441d50304160f003828210010303002a400b1012458200000d981c02d0404981d03106000d400010f1050801595801280c02c124022000303d403032840000f00c07030000c00d4101219424240780c51600d507080508095010b081c80c1015050644070b0265600c4080d42d00c903c82c0c0120030000940e42c003428a050178154068040c05100c100e090103482c0c400864030860178210160350448000400500c00d0784c4800b10103545040806400d60300e640030401240191180900580003c90f1103800c924400055014420b10070b420035409200c03880d00441d204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 304081834 1250 304080584 304080587
    0xf050c030f13030c150b19050307060e040f0218090a02070804030b06061b160605070c0e19060e0601030b10080f060102190c09050c0310090b0d06181110 67
    0x240e58844400c00b80c0092000079800c05581291100500030304800003c4494000700c000c035040a4034819098a22081c05204440441d24110081c045c468040d40320b10002c1000510540320310080200280c000281a144040c125090b40d224090b008409061880042414104103292a901c002c08510441c103045c00d0340d8602c0d50610407844003400041c11100070850030b90340c41046441404240c0c1800412480409030300d0344030f88242100c4d0310340c10110300c00050481c1c000c034101c0c3c590030762006519000790700305a4800c14006000d00200444070341c0400c841c04141140c403a11026001d0300280c0903040c83e00d100018240c8003064041d43c0243c03c500318141c0b400c0e40020426410900440d41803c0e5981c50380e0041b0301e442801c0305600f000158000154003071003090160f00c800d4030100d03501400560b80d503c0c404810ae100643c0d0040d80700c1541c4000b0003542029921800d4007000040584004940360f40720002924009034406001d4800141070384c040140d100d61185002030162900c26625110440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 304083084 1250 304081834 304081861
    0x1020316020d030512040f02010207080c090115090812130617060d020f0409080705060601050301030b07080604020712050324010504050103050a060b2106030a0f0f050c0901090f050c03 81
    0x30020300403201c0c400d4207010140114141ca00c80500104001000d1415080000d104201c030300041e4003601400c00c002c101c0c83c1000c9444034003203501810b060b8241e4030781802c11080060124120040000d0414080b1710104103100c0c1c5c80e03c1c43c410200c00c84c3c41d00d00e00b0038a03140c0c005160344001c05001040702c01561817100080c0d110303170000c0c2c11501404441c43c0b60000ca000c4003c0300c40140da000b0300d400c0c070000402003114060300c0c032079001c0c0e07007210000c0d07480358015075141c44203000140101500070005562316101d0881254000001f410240c205000c40e82c0701c44a0b42c81c4004403402041020040120b8415800d820350f0b0a19015201e03074100313002c03500010707103944100d00032981016241c4000446102c0140c0050004240303803d1641e0303844086003180001c111f12a501c1d241200c41e00000710325280340c00103610f00c2c2560000c2d400340a004299984820b04030055904640d18040d40010510035581d1003080c074000d00000001007900d07040c1190304411190700500e804064241402440344160b04d110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 304084334 1250 304083084 304083127
    0x14030303071409011e050d0f0b09040f03110105040b06010f020106030b0a02070201020c030d02161a0d0b01110a050708100e03070303180f0807020901120f060b01031e0203070e010203 80
    0xe421961000f050f00100c8958a0311800c1e00c0318048000c07880010141e10600400054103946010450401110031041c103840720603040685c40000d1001090200f20003070805480d5038840d003420075000302420b0a45d03003503d604413410755152140703000701304095030001c03810300c0111811701c000c0200909513070340c00e000500042c21111320507901161060441e40200413908600c44000c00f11000300d1070703400009680e122120340c0d4444d850650300300003801d80c100c1d417000d03804d040aa1040f10f050910800c407a0000300f19848076103041200c2020300c1201c2da6014010b0150040c040c00140c4181801e100b0024500040100c9003118103141c20005500d080c804400c0e60003090b454030300401d540b00107000c81c403001d5a00e08001b400c10a2812000000c00903c0c000a02c24148241e51404503681da403e80d5109290307400c0c5001c0c0c04c0d0550441503100150a50344030b405c2060050400140a000090349a040c20b03044001d401c000c558000300303024545400603e90f0041c94024401149030a120b20b501184007000305 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 304085584 1250 304084334 304084367
    0x501030e070e0601020f03070605091608031815031005010807180b031f08010c02010b010507152409020306030724030903050405150a1701120f0809040e0303011403030307 75
    0x2c0418110f038401d03c0302900c5445030030101d070b8640351141010001043c00f901d510b00d003881500680d0030019004c512600c2210700c4c40b0040c506041400d1850300403180452407a0707030701c41c0000403140c18960742c10f0095030103070078803100750051a4282400903044090151080090144034608600e2075807a12501d40182e419210a56449459180044102d01d01b650300c113400c0760280c0700010500d20415400550308c170780691300034803514071458015076542c4141c1070054581209803202040440c01a0030580316030003448081c0d00a0100e418003242c240b1525005520b140341c0010a2041e1494100400008ac00e001c800c400ca9042024420405880d02107148500741900e0300800400e02d800307401542c0007418040c10f00c01c42c0c901807020118595008031045400304100500d400d032800d554440982c140ca1030a1a050b50501032a00c5003000305da403181e0126981c1400300400592034031503004042c102c100203802541c81e54148121340c501c88851292039802684240104010583d1207240380c003050961 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 304086834 1250 304085584 304085609
    0x90a060807030501050603061c17191e1407110909010b04060504020a090e070c020a0b0304230c012706030e0d08090a02040207050c10020d020d020a050709020a090f0905100501030e07 80
    0x145015000400b04103d410000880450810f0011580724bc11070711040c00c55640780150310039144541d40c90402d983d609000165401c014001d1039040d44000c100c00c40c00781148a0303040c50f01c040019110314044490380c0207a5101c01c1596111300b894000d40000e030100f114194208004c0c04002011006035220705500c2044a4000c00c0883d402418400c110703c0d000382540c48000d49802d003030482544141d50441d20050300380f8240001556019041740c10030b542d50007404e0300c1c608460044aa5080700718665134440795091814803c21501d084c00c00c02041d50391000700301c40f480d1582481c00c21440d0301000013808809801c0050504001c141e034072440c0d83c116401625915503041046c58102d008600c55000010500c03002c80d50344d00015441201c2e1001d608903440c400c0c41d600c00f240c96100c0a040100681d00c0108103010b04c5050f5000b40518803a20304e4a0030f03407075079030300b00385d0032180525400b2607590390b998014040c1000395005940c0240c0000e0900f0303c07050400380a080d56401840c40f80141c0c5009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 304088084 1250 304086834 304086889
    0x506160c092309010e0d200105190c0212070222090f0203060703110f0c0114010b070501050a0239031804140903040605030c090a06080703050105060306 67
    0xc0454282000d0a081d01003000385120041c240b003103002403010240903056481001500440d81401502c0c42a00c2803009030000e00440e980942d0f22074006441e8050003014074600819505007485428032aa4070850009501001c20b9030741c0c022960641400400c64000c141da0100c289444422900015410340304001d03903c11000d050345c40000d100c1c00c40394005040495400501040f41496944c072070085082d500d40f521070303090540484180c0c91200c40d5400381840f51144070b00c4a500680000d0496400106040080420a00007020240c10006000c0d1000c21000b092000c04d1003441e034040401d10f0110b1420006c481c24412403064440d580b41c00224900b47c5041c81d900c41c078010740c031a00300281200d884228903150520911281e10000c1d00541c6052015050700f070110300341078000c00302440503600d041d003810421034071a84014010081408100510721aa860310312900d0000c202c0c6a541c1030450400d000024192841a440300384204404d00034040386544400c0800240f442034a061907201c4c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 304089334 1250 304088084 304088093
    0x706061412121e0403050a03080105030607090e090703020406081501060305071d041509240614070c081903080a090213150504020c011d030a0906030c170114040e07050616 75
    0x5443c04040c0340e400c04045800001c2240c001681c0d0b0b00c0c01d20031345680314144e0300c5405045d5140411242080001c0319110204812130f40450420b070080210400e680525480e03401040c25620203601541d1a58032400d0200c110314590010a4090061071900740300c1da0070f1020340141440d0500f0340d040920400c070002d500350340c0e0700ea078040c21741980c20755000c07210b166403248810020503540e026140f466076034440c1490f0407491205850141d5220792542c444800e5a2681d0101c0e07030f00b01403401c440c044184040440c200300d0801030030400040d44030350044c00c03c42d00c0c90002c01c03244c40a40080d152500b030600920050799407419800c1d0040030540b0001e45900d0300c03101a03d09024a40c00950490b1000a80c48031480c410f4101030071103c034400d03000b00c250120b00e01d00e9030340344540107050000071241c88040c44580e2080d000100311552624180d0300b041e0480e07904402462007030780844d440540640d402060340c00c05010350580e102945028041051600c000306890744181c1101d000d404049820540811 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 304090584 1250 304089334 304089367
    0x15030e0c0108090145081204050304080105130c050f0a06030e10021c0b06040612020f041508010e011e0e07110d0305041104050115030b030c06070606141212 69
    0x919400d000040200d080c1040403c010514650000240766041001001701c440b10140e840580c1e0100d00e16150000c4101302000c40c3e20302a20407242d90004200029030884240039281c09800d500f200c01c507000f8a00e00d051503200f20f480d44914002c1c03010b110b1988495071008406001c86a09040c0441c44448900600d410b0042040c1c0e10303554035101061058100d0220021949940079a9204101080120040107000d020f21b01c2020002840500544100301664010708840c0258180309410192200c2e50072742c621035840b02840015403088010400205110116801400f864030002e080722181c0e880e0b0400c202c01805180d420941c4040401c18141c4149440f13070a2a1080c0c094881d081c01380c04004000c5e100640303056400c1d40650142220300d181c544103082c1255468040a4445456214160081d0810803800d6130306004401d814aa1620781d5001400c1032403107a0400124282013a6a91a6140d11840075602500d0700d03559000302e0204c000ba04805c1c0e004021440d07a1604444028018035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 304091834 1250 304090584 304090601
    0xa030c03150608040210081306020c0a0b010308191b06090212061602010507030203060604060f021e01091a0c0a180f090615021606030b06071a0115030e0c01080901 72
    0x262464141d0000b505944a0074041c0541d100b160410400205d460044400741e0041d107808081d00d0b4a8107540e000500250b0051410412040a541001c1d9854588945004d4240d1098401e00400195481c2c54580c02d46060251000340c240b05200d10340c5803244100340440c040c0001c1c2141d954100c0740b002d40d5540418480e40f04103840c02c6816610700210081629a10442d240d40035601f01800301301090301038000c3d2445488090501801c0524001049500e40c00b040750301c00075401141010100c0d00d2020011004000c42030740041140b8070249041041c0b05286400b104104800c00140b00c07000d0020740845501c000c03640380c40c55031400c4000e041c04402401c1e07480012182804d0303400141c1c0e65501c0d0810b4084421703203c4100004000309005a84803001616030b800c0b024255038080c401d040c008d42c400c028040002c0c11060820b0110f030ba460780c8951410b50040d541151081c01044120f0800c0ba00d0704003101589028441c4200701284c40d1f64510f107141400303050120800000b98000341c00d40c4010391 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 304093084 1250 304091834 304091861
    0x1202060d020403050115080c0d0210030f11130504060b0d090302030c0d021501050f01020618031608030a051b090904060e060a0516050c07050f0604080307080d06090902060a030c03 79
    0x140c0343e81da0b180a500030030428050700301c00c104800c030028180401150185c01301c41701138107084142110b0740c00c00500d00d01001041062540d142c40e810240d044c01d100b003511004066010030f549844883c00f500c40c0440c15409a4420380c2403c5040c40340302540815542100a1044e000c01d0420151505034258060a0f01204441c45104001c0c004181d000801d0140b071610f489450a144c1d07202c1c418030891004110442e4056840b81d03000c1a00281181132002c9030001c060196402e0141e21040c0900006d0345d42025903803690044140800c0c907006100f6217401c100300c41100094903038015885a40e900801100c140301d8001c0c18001801d02038940c11100441c400901030303510521704001082c0040c9001d642c00c402c55941d00c10001e0240d409a82101d580d240100020310800b440c00041020305691880c40b40e400c041e042c0700002d00d40c041000070304072452241501c00c2d03c5a1a1250b078008440d2141c2c0041308181c1004600340140c0c40d00d0044507040c41d8280350110b042184003038240c0207042d14000c85072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 304094334 1250 304093084 304093087
    0x16031203060509070c060b09150915031005150d030f030509070b03010e0405011a010207050d08070807030f031a01080a0207030c021e190305250911040501030f151202060d02 76
    0x1640725804440201010321407402081000190340501905640803203141e6882010279918412910709142c0f0b2980c00030101c0d40c1e08036801101004a07090003400f040c441605620340c0e00b888141d044552110883c0b10041e540b030254428561402889200f8952820041c15a606c000c514011024070400c0081c000d0405103da880d42e44000d010100c210031203041e00c1d02e5190101e8842203482440004080d41c005034020400302d0b042c40104200140d00c008215180c5030100071000c0001d01450103049180c0c044e460f0b00c5904000c40c140135065929580c1c4190643d210036041000b00d0780c01152060f006060b0031001a00c40c0840d180503034080c2d0041d030001c0c0d800510503000c1c89808040c140d4038440b140c001d50304001007504000c0e480300c41001034000100750f50040d24507000301051a2140c080c000c040c2d41c40c0e01d09803569032104582291048950041c41c01c00003d0107000c256014003030000d0b1564030460402003429106612141000c3c0c40c060340c5ca80c0342d400c44060701903546150076030300101c3c101282103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 304095584 1250 304094334 304094341
    0xa110304150b060a0f57050d0810030b0708061306030c05010f031803030c0203300915160201060801020c0606091014090402010c0618050f16031203060509 68
    0xb030305c400162041a00024504806082d52000c070740c64200e01c80c903110400c0c000803111841c00030b1815a160780c401e4114090b1900e1401e42e101c04da69201d078901c1c029405080d41180c3d140000388903040040c40d001c044c0d0946070040002a0515030407691119103407401c0001502e40304000741c1d60b4032840030021940c03418880d0100610440d13000c1c40301100e1003600c421b80c810304280015010354901c3c0b034203501c601141e446c5510201e40a5004501648072920507245408003142e41e00362155403180c10740080c035650341c18610108a000d403802e0b401115800061654080d181400e21b01400c006040800c81e9203c03040e15401c0c03038000d4100d24058124500295211542491559030310301003180d84600c00d840000107c3d500c1c03d4419040410341c6c41345220950b090240310180b042d2910050001c81c100009055a00c01281e018401c00780d00e540c540380c0c45040880c180c00c0481c540070100d98649044d4000000364051490000342003802c80760301060705003007124045c00540007404241e000c90340001d900c000b007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 304096834 1250 304095584 304095587
    0x20604020d14060a331205250602010b150d0c2105060f15180f09070c1505090c01121d060702210405061305120f060a110304150b060a 59
    0x42006011541d40078540036030f14141d0718000d42e5646801c1c100003800c45d0050000c05011101400807034056400c4032440500544103041305407480214410700800d014091200c51f41c28010341d0039400e401c4890080c040042880c4c1500c500c2072040c0c2d82d403c0b6a58000744200640100d0740c108800d011401c8409030203180e0905900501001c5441c0c0e84200300036020140175140009800803c41d40064100c6d040c6602c115892100a462a81c129849a4440e513000c1d80c55503141c40f1144100703003660310094084614a0f00782c42400d4440c298006907400c0c1020071040580c00100200c0c1d2501c07d00e041114042d81c080c042c001051812541c3c54401400840d003140082c000075054054000c41d82102c481f0400381c00001080010b0001c003254004007048208954900b24000d820a4000c07100640509507894001030000c0e13071a062a030030070303802c60020109152424413002c0d17405140c112060150b001000f540c101988402400200410007610b00f041074a040c03644111090600904a203541d81c0164a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 304098084 1250 304096834 304096841
    0x5130b0a0905061806011701020c0307060903020c01080606160305090402030a0605150a1b03170403030b0114041202100210050f0f090d090b0f0903010207061505030a03020604020d14060a 82
    0x1c181c8040c829a000700b810310b00c40c1150454410401c1024201d41d03402e01040c40c02081c4180b8520f0036540d005d00043c00c0c40d034030510050014a200e00c4001980400030324000c2e0408415900c1c590501609404210135529490300300d64812643c0c180c82c407242205032805407814050202c6140d0030500c0072040041c04c0400343c0c4a5001d0f0794003161800740803415004958494030071860f442d00082c40c068400002c0980032090000c40398800d0520030151028200e84040141c401c840590020380c031916410442c0d40c0112120950602190307640d850241440805107840111460080c080c15111002000c11482440b5103500702581c01e0050019040414400394985400c0d101c816203c025480400c11081000500c05035641d503e444420049103072100526064000100524400740b0802020003541d40170710051242c9032044c100000c15810924900801e2460303034110500a900549400022980000c0c0181d80700741c0c11200701c14030072a1450116540710140d01500301c14030a400a01c10503504541 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 304099334 1250 304098084 304098101
    0x603080403080c010509060c0d1814280515041e050705010e0a05090609070201020d020d0f0c020601030201080c0c0a0209070f111b090a0209030a03090812041805130b0a 74
    0x21700c4151603c180064844000b5611101450010800100c1c1059103800c460b030b00302d105c4070071030031900720070340328054025640c854121080d008010900c50340c00003e107050020342c83d0302c01031040100706982c40e00e94805200300b006210700710032000a01000000c000f0038002c030850b480c14603c201600d1401d9542d51500380038150100300d506c15407232100c1c01c0241e429011210010202e13001034407580103010502c40701811040841d5000c1003100c4a00341c59000801d03012044860007e41c09801682c0c0400b02c030009080c100441d0001d10041002d82e910504040c2c01003001402c4555030075072209500d28001c15400d0082d0800d15140401c14207a0300034901603451060b81c0c840c00030396080c0d128046d45524841c8010700010f10000300031941070400024031680101444030040c505111003001a261880203c1d0890010311202d03000e00103800140400d07480620148407081c205400c21028648085044800030300017a99540062900c11103035040581035030b00040e40602d641890303a07084019142d040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 304100584 1250 304099334 304099357
    0x318160e0609040f06020a020c09090708061b0f1c05040b0609090a050d180801060f0807060f020705010c03030f1a0414010308030c031f06050a090602030901090315060308040308 78
    0x66524200b080200348540c0d4080700310340031451150b03250380094000004440440c49460040201c5455810b011740c0106110401850614035080c1103d241c86401086d4042d13000c0c044091000c50708503d001c0c0e6110344400e221164540407500b040e0310303180e807481c6d8500f24014246000c0c40140f00342503000a0103104142c403445416a0340c000116030303030302d1503041c0101140c1c001c0629181180c0f0892a441e440c0701c0500342e0700c17210f0313640700070341b03801e403082604240c6000200520402010108208940040030702d41060f08041611810180d00ca030b0540c40b0b214184044058541e003018030aa001c901c45e41c845140400c107030441034010792500c04640800c24022440e000c100d0041c2044421310700c3c12280c0c41802107203540d8408004c81001c3d0005002c60310b108203603020303610180220340c29010240c14180d0b9202d4440f0380f05000200400200e5000a065400802107484182d038080c00d60070075130307401441e101c1d400940c0c0e41800000704103550010b0111030300402d001c000c00150b14000c01c04004c45 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 304101834 1250 304100584 304100609
    0xc0609050612040303050717010306063f06111207140f04030f020312070812060405012d1a09030f19110102030904090602120c03010614031816 63
    0x3104144a06403090000a4400810110002c0c00081c8240c0107150311405a01d0300201804504138050301e001020b03001240c00a4030340340c0a00140b00b01a850710201d0400340c0908440b41a4a2403c1c2c0020364003001101d8116010410401840b07807540100b01d440c144a0f084035a9000120003101c510390041d284100040c41000b40d5204800c0c94070b0035510403200c4025414035051441d542c005002c440100c00300c0e09030003600d003022075045454000c0c002140c000c11b42c041c4d845112014030b48000c00014011032003035180c113005211003640c05154003440f000400228113070300c120340e0120002c1c40d0301d54401010042c03551034008449071400c019050840080d03046900000701c04404c15281e001070551910328060038440240481e85610562004072018010380745011100d50100f810707254000b400383d403055000644001d60408042202c0e038400018884c00e400c40d41000c000a1609a07003001c1d0420b03500000c0007252810003080d141407002494142140c2c4400c001200c0e0054407100e510540e08203241 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 304103084 1250 304101834 304101839
    0x9060c011508010e1e010b0603160e040203011206023108011406030d1b06020a0e0906010807080c0a0e030304080a14012d020912100b0f0306180a0501090c0609 70
    0x50045511280c9204003400c5c102409500c01c11000d40c0c0041e03039400f15074035402010f209868a40041d40030f4000c0d020441320303e4400400241000e4aa201418010f0348100b004102080d503110030340349a95804007015030f866003000d581e0800c0342c46501e400e5400030303a408244058460f1000307009041314103000007030104010001102a011504403400d54060f00240c01d940c03c09031044064007030540034950a01c88030241900c5031002c0f40c01010802c0d01040c0d070307000074004034075140340c6195000c9024a03001103289849000104030304400307010320095510200c1c0c0f1845990003040c8c48049800b01900300d88d152941e50507016615954502c040c4c1d95540c1200300b524100106010700950043d4100580450a840f1034404240b4213200c0c801207159a424802118540d40c0c03101c0400d20038800740010034003d1501d0301140111982c105205100300c0d40140c4604003134a021482d217500007040c0d0303a402c1c140102080c400f818400d42c04401009946841100700400a0320308000301643e44990b608200e458 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 304104334 1250 304103084 304103099
    0x6010c2301050a0f0b0d08030c1c05250f050903070302031002070b130b0705071a13050c01021504060e0106030f0303020301060f140d05090f010204030c0503010c03051905090309060c0115 82
    0x361701032621074104065079055070100ba0369400458101d01d2001407146840d5210855910f805003800d000041e050315401805008140201c40408809803098540c005142044002d070681c1e00c2c1480d000b05000010840303040aa0f010710000c0000e580240946244440d0703081e444009500c11501142c0d04000c040200c8e440c000c2903240703140c00581c41030030135059440380b04090b1882c0e00018011140348c80b102550f03281101d10000014090f0882603152703d56081e403880c01600b010307041584103046501400c02c51070300620548000b0380041d0005400164030b20160350441c0034101d1900050a0440d040c0041401c044d4503900450489144d9071350010410a41003045560300802c004101c4150005c0c03005803640906584241e4006030b00c041103e1440280c2a01c107070980c0c21a43c4142d07400461170700100304a090a000764410340c5d20b189001c0109141c00b00c0b9030048554160000015150348070000b500c81003080085030348540c0d006001c5034803511050b020b03030f01a0202c8107010004554171040040d841 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 304105584 1250 304104334 304104341
    0xb1005071401021306030b130e0a0501060b130315150303050408010b240901110f070602010e01020702030d0513230319121d09010902030f090c0906010c2301050a0f 72
    0x2d5203091201c02c0900e06171086010342101881907031301044541c19912107291a01c9010309800c0100042d0080940e81e082c0707207084400b07942c444a00708108009550415501d00038000540fa800080d10070003803002c46264000300f1092411405010b0f0310030b004800c1c583c000c409081100d848500030301401c40d0340418011061010031021100c007000c01c1181801c03180d680c014000e07200301850045001d1b60000155840d080e1242a10381868100f140d060018590a00481d8004080c100085d450401c40c3c0d80401c0d664090000d502007003020208940c656240b00741c10030b900520590400c0101c00b00b03a80030044611814901080c480d1045003075605141c0600e60007101159045103040184c200b80500541d211500c2da2081150a060903181840513603440d0400b902130000030f240141c90b40b074440107101c2c403960040d0041c021a40131100c510844e507215401990301001c00e1a00c80b05803491450001012700720601c2c005040f40000300b11110315101540806e00c210605c038000d01c07403402210301c26000c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 304106834 1250 304105584 304105597
    0x8030c0d05160209090c041b1206080a030513090504030e01080106020d090b030a09060908040503011409100f0e1b03060a0b06030408030439170309130b100507140102 73
    0xb203407004026a0050b1901d8940e49600106032000d030f600c0208a000050100c035203210003a06031000712803000e14401d034803417800d410a00c2c01400420800741482d01c0c40b03955180c0725030010700700500080c84800150b40c8101e42c5008001c550418001800c1034a4050840a20f903240540055002000081c24610021f64400d12400f5521480781e841c0c00e00907503951680c0000c094400f011707141c94415000508501c14640404e00801c481d035112790800c8109800c0d26500141c10070b1500b81070703003400070050021a0030032141c07920040000e030f40002c50fa042409802160900d004c0b07030051b02c504a0321100e032003400d411074020880c03d03560704c1d90314205408100c907400035900b80c00c46800e00014000039080001950000c1c0103001d04c0030802c82e8111144104c0c818402c0000520080c42400b40c2c44448491841c030151050b4083d46240020440a2070364900071034414921400b104201c82c80240303290383c0101d08d218009803108180d00840791001d0103d5011150460b03800320f503011180700417a010310036900c0d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 304108084 1250 304106834 304106857
    0x70203010c0f0804030309050c15030a1506120b190803030405010b0306160c0c03060603080c0c15070b10050604060f02100b060405011412010e0402090a090512210108030c0d05 77
    0x2503481c2c07a20301b140284001c038811030305071007610501c45181c2e5400000d02142c1740c00b002c200341d4a01d0041c84c2c0328140d40141b6002a09854503c005001c641c1e0440c44410040302c0340343c4006107040c0a540021726030740c1c000c4044c000d042e0810b480031846031404401180315501902c002c1c002c00e01c40e00141035030389000302d03480130616000c0c0c10002d044900ca9010800d078540144107403c14180c40351110800c59549510850350050006082ca1302e0540920071036600d0f8004442e003c5900f0b25070420303000c141c850500020144820701e400101c12030580d10340c000c0a40805080030391034130f45810b80500919003140c40440540b2895030b540680c58120300816251130320180405007060314103c0192160711f009401000985018000c240c040d00e1002c28542c0200030032902403215003080d005011160030050000b500c4035061a40c6440031a00000d418070f01c0c0755a0308501a91145d0101a2414081100d1061101c07446c0c03003030000070710302c400101508600103c00103480c050342da042d030143c0d00c134881c5004815 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 304109334 1250 304108084 304108097
    0x31f030203100c0201150f0602061e06040902031c0801060306080c030d053406060603020c061b120a050601090e040309060e04020c010504030801030b06031b150405090c070203010c0f 80
    0x240e0020307480c3c1006100c1401400042100a1603a2410050000b60341111510b009070301c03420000c09a0402c540c64010506202089501c030040c20207464000c0018611801a925215568219241003004860319291400008200722440c038004089020130311070000003030f04262000c1443d42001c5407801347d402c0024028811840c1d4800142c4a0343c218003000c154000104818001043e516507001e070803010542c0c61245100b0541c035120301160b105804c11010144140300f00c1c4035900300000c2c403c4c0c01c2141e101c2c55860f413200b1008800c055110b101c6080c80c000c40b400060005400440c0c124600902003600c0c0c90000310380340c00c441e0714400350890b000340c00110840003c0101c0c2d0b0080000b0a2000005803015140180442c4190f003981e109940c103d00180420b001082840a9a20b4640e00450118050a42038055070b0820503230105024075140300308804071041d5164103107481207400510000d4020030039890012035150b002d8104580a0f800707942000688100d961040c03030040b011401c151181d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 304110584 1250 304109334 304109353
    0xb0304060903030912090306050c160b060a1a09040e0c060a0e030a06020703020c010e0a05030a1112070609060f05121f080f0c0a0f060e0105070c03021302031f030203 73
    0x40181076000001d9003030503581c0843c5008076151091041180b00390b52141c41c2150302e581392810454000400784a16000144000c02407003034001c09584402c0c2c1c0142d29650a80c8940300021120307003a551003131408544d0000030129101d0840302500c034107001103c003000051544844030340c8540c0c5409100b03500490402412516034061108040c1d48900074044039848075103941c411b4102d9122000075405a407210522461541e40502c0901d600700c0305555240400740f406002c42c1c1c0c1d800f901240208904002100c400187c5c0f00d4440d48400d14114004944d82d1a5560318042c1c102289401040005002c5084941050b0f00030011a101710f030180f2000003040e91307a000c0c10034400504109000710b607602c1c0f80c07000a681c0f5042004180d07600139178010303040408c0782c1c4040007016101380d84440000718507827000700000c540003a05107050320820f003010381d910200d03480c2010f00c1c6000340c2c000960200e600710000e00301c0d070555070140d84140b06075810b40075200003012102c0ca41c1607061000940c15440301c0740c40d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 304111834 1250 304110584 304110593
    0xe0c0a050d03020102041a0702090601090e0a020a050904060f0e0c030118050c160c060f110601060813050a050705040f0e07090f0204170f06072316060f0603110103060b0304 76
    0x509107200c0c0244001801c09480da00030707191482000507483c8041c0c0000c40d1300025491308040c10b6070803940034205010302516002496212040041100340f0440d80419007440d80ca0142c402c44000f41401407080090700e40311901c0c0c60038a085030103032116003486540010170381042002124107840d41e80d440b100040c041034130403c01038500204020b100d11424042d2850b1036169048042166215144400c10a0f040403c001d100c500f50308250000c1200782e4400209100d404101541075034010700d413642c030075034030090380300101790082c1c1c00100280305850311103007071050225400081e16803c8070188081a407044d000f41c00d45d4074002c0a0301306504000303010040301030180d2207052841c3c079840700503003050f54900c0300b0700d61a81c000c6d00800c0960802003400c4a9180280302d0140d203c2c1c014248100c0c0ca8860b140c000c1c00005405e451115805000502008014034041003001e50550010050103190b60b44140d00010304007034402111962006d810000c1c0541c060b01440c01540d0318004401e080d036850303485 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 304113084 1250 304111834 304111849
    0xc0206010614070c1706060103050c090a03060902060c030a030c020c2209022110050c0c19030302040b0d1a032107110306090a03110a020d020d170d0902040e0c0a05 72
    0x1150803800d010304c0042e0000d01d0010b206074503117a04000d4a610300d4000000750641d0300c000e10030503801030100600701d915652056044140c0350000e000107030000c00c52011a045200e80645145a44000714402032881c2d4590003e0221150941c00d03509131204030b0702444481d4210310f110100b14118130328590000c0d02c080e030100b110540000c140303200600b03020391403090711031030010080f030560040240d20b09054607601889400c1031f007850529280040c004251615500e00c000081c41c0301840304a02c50030706109406690203000c041035070030f0361115000703141d40050849031590b070070710b10881407103004610300440c42d400700444819214200441e94a0304016070350005404884900380301c8110324050f1820040f291241400760020000441103090181c555840d01811070f038194440001c650068464030340c2c00110603815107201c041003103146400b400c1c0c17404190328014004008100031004403500d41008081600a460400408144c15521512000805d222a8211780c0c00b00c802c0005007820b42 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 304114334 1250 304113084 304113097
    0x41a0306010306030c0f0302090f01030c0b030a0e070f031a0408030a0b040e010c17090a1e020102011d10140112021c0501050c0301050a1203080f070306081207060c0206010614 77
    0x907000031030316107076500d0320480d000740c0e0040003000d00841b000788214140741780307810341180c0d4603903105c01d01e03602d0f40d60b0b0b0720100445800303260035025000c030100e5401c8c103540d0041249414564107170382d042c81d08c47c2c04000300844c180c4002c2e01c8281100003034905071022002e800b070103113030002241c6185a8840300680040d04200d014550001d43e5616180107814087c030480b201c0b40d1391582d0380d041d10b20044405211982016002d43d034250080d82c1108001a10032500d2500440a240c00282950391800141c0c01451065440c00c12200021501d081139080860110395030042c0e454200405500340d1041c115000f02406080b92406096a00340054640304040c4140b419002852a020341450380d2968251001641c2c04a00c800c0e0100040c1b20034501030b07003d94054400981070840011302520003d01d414001380580d180c465091012915141c031981004018010031021a4420f10800860700d00725882103106440261400400b080307c54800300c3c241d41201d50641e02d6001200341c05011810550104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 304115584 1250 304114334 304114337
    0xa0513020f15030c0405030f0f0a03030b12031603030513261306180e0c0a0c0611040b0c0708060f0106031113080a030f0201050c1602061b06100506041a030601 70
    0x24072414102c408001036105025040940740c0f01c600d48800c2c10f282841085100a2981040d00d45100c214400551004180e40515001c01d03610310410125121071003405100140707000005980c451180106107114000d40700c1c1e502004507175188422803c6a04144000805d200d030840500e0700449410f008100760201d03195009032030100c0500c1c59404200c000d41c4100e010076061541c1030b04154070311a0580040080225064461400c1c119840d100e00c40c0440c228140304240d100b9000344070302ea52281180c04804580669520381f1180340000d141c0151810144601c14250041843d40003c11428010324422400c08401e900707140c010740140c071800c58500c1012001348007007800602c07240104802080c680c070160120f40d00c541002408402100000000c0d03a040c0014020a100c0b600e048420180004915003110052480002d200303100c0c80b041d208a9889152104000c1d10b80803402c00d000d1400344020640095840e010310130140a640308288214545603100f012030b4074428025903201405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 304116834 1250 304115584 304115599
    0x56060711060a0c030206010602120a0f0c02060313020f0406050105031308090405160f0e010806011b06021b1501080d030221010b0408100209031023040501090204050a0513020f 77
    0x1500c0106400d5000301c2070701c10006610034050b00606405004107030260816102600050b1f0103482581039a2051128140c1045401d8610007c001e200d0041d1199881d070050000d540ca00388000350390b525600316602a40714030b02c00c0c0c01740410351400e445007400315001a11041d0a40d1f5441a81204402d441b410a80c2c042001f0001161165910300c80c1c02d104812004030415a81e008aa000f040c00440b26108410301801c078102e415540e8000d0301c4254011001d28040c07603412080748401140d81d6614030010300541c00130812040a42182c062098810f46003000ca030140340100005182009080c0304080864011000510044d8881e40041c40325032850360700445050101424000d888100b64000303031034900085030a101c20607081c00000c1c0501d20000055050064000001707450368100c90a600400384d4512940a45940051f4000d01d0b04070b000b83c00700c3e124580740c00c00354060b0826150880c400d41c5001d000800c2c603001ea208a9004424810146852030340603400d000380c100402d0f15240d8040701c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 304118084 1250 304116834 304116863
    0xc090606130801060e0703290105130905150a1404050612060405010e1c0504090507030e060a0c080c03070e0909010e030a0507060605030a05060f0703560607 69
    0x710468060024007010000040040c0b40a81501240c0b20262240081600346206040c00034030030100507581d10140d410850102c280400142d4451040e000316007100009480000f516040d103500680c030030b40600c02e01101303402c030100400038000e03200c0c040d800780c1240e10107004081c1d04156000690100001d001804c2c1c01c200c07929a949041c0080724103d441d607444d00100100403c4c184000b105103441060f100610707000000018104d40580d000b00c0980320b5481002070001d52081d04250f188070341d400c050b00d480342892110140500440318011020954a1000c190800756920880b03101d041656130704508001c401041014442025240c7c44240d903ca0f10320302c58010040c40103103200003864940943e55070351844c2040c11f0310700310f0380050311130382261016402286010030300c0d0703034002e2140c10922541da481070001c1e00100700310500c5402843d504c0c099031400240c02c007445620505020000d11320b207801c1c613441c1d140c28400601c080442c2c042c022038000060620001030402203104a00c82c500380301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 304119334 1250 304118084 304118107
    0x1407061202090312041221020d0c0816030f08010f0506070312060f1d1e040209041703070503041b140d0606031b0e0c0c0c0d050a1209260c090606 64
    0x80241c0c0140e1350240800c80e01c0d86c20030030584000042e04440785c5403d0100031940307201035103d210308200c401c01d1218158403402000141c40440e100e040000d450109540f8290034010800500051044003003000c0c40e00220350201c04500c4c20045501c01071120f8505080c4d80e60407070310110700e802a08582501d902001c11010444a8010050000f0380ea1103890101d0a1a400711a00800350801d140c3c0300c003e15a03581815841116290310a0701034400c60815255480c0002480c00c0a160762000e440000c410b024a15a0010003036014600581d01c0064080c1980744040e2031824610889039003e402e0140d03000141441980030090600074a000140c1ea55a526401c03007415000c00c11081041c5d0b0744034103100260140d40c80540203100c0021080c10600180086551000c0d40c00c07140b0300c9102089460410004100060046c1590002c08880c0c4c4d0141d0000140408150b405504580700c4100c1d89007501000707903002c041010880d0801000012030345014424000009888550480001c101441c6c554 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 304120584 1250 304119334 304119337
    0x180421050705010c0f02070b04050901060c080d060303080411040507020c09150306190c0804030e06090f1c0606060c030503190e0f0a1704030206090108060402190c1407061202090312 80
    0x212000d4a4400d00005c0b8100000e0624089401a4607204070901060050b03494100404d41507174107509210228a00724207101c0c0c0c5034003c201d40580d001d41401d2021082580c06003000c1d0181c2e03c202070907941514020b0410003521400c8440c0c60040e40410158485485c011000f190805a03840e040c0fa80b4442c6500800e041040880f0300030702c1c0b0101d141c4074840b282c401c2c3c454046601410315041800d8205954000e2104c080b91000c1c42c4161400703e0881071550311545440b0a01000620026000b400300c1c5c1050390b21000210b040c0c540a242810009a4500541c19046000da045da103403480c1d0307501e0b50303a48402c1c90140901c0301a40c0c0da50f07e00300171000c00100445050b120f0310600402c001d04151902a00c91010b038400d082c80400c00340300400041e154141681c1e0708210900300902c0a03555100420700134090350749901c00000c01d803103601704000c0e0007035000c1c0442070041034241c0c50241e035a402c9030f41e240b2851040100050f0034101921760060682e000c0c04152000806888a608a0036401d0350103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 304121834 1250 304120584 304120601
    0xc1707020a061e0606050309150c03150a0510030b040c091a031b0708070507050406030c05092e090612020102191103010903090509070c0308010b071b120218042105070501 75
    0x121b90000103009a50001700405001650702605011007403800000c07440c620f0001030101c2c40490401420040540d503100340302c5002d028040e00702050314941c4140100a000c01084060145190036004024980304a1503070060b0b51020b08083d80840398010000c80550000306004211080403050050448014000382003441c044c44101d038a460040c10503600300001e60b8071081c411480c02ea001c100040010304601d0807100200c4000106da03840c040110003003403000154180c6034044005881400d841003107008203507032440070200442503c42c0e0349100419504030003c0d0240e40101222104030840d01d500282e124450b00030710b1b43c40010301c0c021a080d075403104012408640402c8041c0310703a051442d0202d40c001c01c81d00e42502d052089880241c00c180040c011001c82010009503281405804c100807010032140c601d4544000e5518103000310101303030b080804c030710480300301010104400101003c1d41c001c0f5041064102900d400281c55210032041050300c0d0701703000c020b0010201040080c82030405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 304123084 1250 304121834 304121837
    0x9030106060e0a0e161215032001030b0a03020405040c0312030207110d0f080a140c0a0c0b0408060606030604090515151509120a050d030c1707020a061e0606 69
    0x950b1541408000c07060100d80c000f089483c0764034042110407024441700d035821300076905112806514811101000e850f071003022011410041c3d100008000803010345100314104802140c044102e070000440603191420716080d07210060b0003051000d13250a901040c0c1240c81601d030041c14941e0303035880801d272040b80c650071000306c0d5010407504140311190351800c901004c219110030084803507540d625411006048041c0c982c3c10046155090280166110050b04155040450b1178035044203403a6541d103102241200d0801340a5000200f21141d6000e0304c081d034609038090007041d17032001c0c14440907400c028407072a4043e03241c444400108009100c90b1820000840032080d02d407418510321010740070349500c2d290050400c05a040405040303d01520b402240c110f808040e5021034015180c904100d0a00180c03281c0500c06510280781e07011391200034940c801da1118021501117051319070740c9800449035807025030000241c581c0000c0f00d079807110314000401215500c26842d0307400d2920031181d00742c00140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 304124334 1250 304123084 304123097
    0x905090114040b01050702061204030e0a090609140403050409050c0d051e01050f01051213020909061503010207080f091206010b041d0103032a0605070c02010e0405040503031801020903010606 84
    0x1245003018003824003d0002800e20624014203035011030380c2480f82900303488074952a000407a04042c49a02441c203103113002003866130b0154070b51484400a0080b88100103c01d1b02d85103c4105040d41d405c0c03807a00c25030305920748074140743c074041c0d410020300301c001c2141a11080410800c5c0411110344034940c080d1080b4100300030042250f195407400800103801241c8100c0346100e0303106031680d00404885100c000044040d115845481101a280d840091700035400643c200400039103050001d01c0b548149034402d080b40c83d00c0030780c40c00d060807486040c44c003410711a4108407492031090110300174400100050401c0c200501040750041c00c2441c00c0c0c022850a400c000381c100003400f00d4400b5094070400e4203040074203a5145a5014083c0600da113019101c0301500b81e405003c4052030041146810307013001d014411460800d00041140208100403408551007100e00801400c003441401e00c6150f000005502d962943c402d11007407815000c3d500025590200100b800c1c82e202809190b000303055913151708 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 304125584 1250 304124334 304124369
    0x10204030303061712090409051509010c140708030f09210301090f060e0402040b1f0306051f12150504020706050f0112050304060f09050907020601090e07141009050901 74
    0x1414810051412203135a17480082410a1140040c3c111500303410200c50000d01040d883c9000d070b080c44c925110080c0580000030401003800010b401c003010203400d50303440403c90300780158110a64019000050704001003400003e50070401c90481315040702c0c142049640b4841084010070740c1c03603007110b808808148080010490294140075925001c481070405001c0c0c00d0a207400d0401c018001070002e403059403100901016a01c4401041380312801261284400c0c810440d8094003801d418484d0310f004801d171440f860106c0c11810902c0455007021340c4c80c0003a038241d000c002009070003904401d400c00142aa00001c1c5544e81d0f100801000b0711074900445c0307a00c0c060b110b0080401059000a0365000c5001008002800110490f02a1a00f03424084400360340560201ca4240b220b4020325005044042800b1a06400050740ca049400007201404210038441c561030300c4069910030074013a0400c04410094915202c90103882400d103c0c54600d41803540d40e000920000000c0e0b204046149003036020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 304126834 1250 304125584 304125599
    0xa06060906091109040c0c021504050a2103080903040b07030e03060a020a020a120c06020703120b010201020903070314240702010b090103150504060902222412030e0301020403030306 80
    0x4680040071200c80402507840442503c3c0603a20035611001d2156031b5401c0c10b0080c0902581c03a50744200d802030040400c0510302000c2098a512034003071b282c86060901e07400581c10064016030780e00201322424200c62008107907001e030384403a0060b04140850001780004942c423080c0c0307806408800d029585400e0101c00c80428542804006000c64403994010040070024580015100903d658031100160564040384c60845185107010001041140000354031001c0c0340e48036a40704218400340404122a0441800590803882003a04840e09500312000400109084889020b80c0d003825905a0b144805445040d0340c0380c80d8000000d45290100e04240300103103a0920413280b9124059a40d084554103580314403803100e0060000c80300c0039448200103404c000458001c0c0103440c7d13000d0074090400200c0e143d040300c2d0b00f600f1303400e01d504a13280480c0c2003200340313922a040a400c40c80345800101c444c1454980042040324601c00c1d41401980c05000c645604c00741700500085000750b40018035141003105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 304128084 1250 304126834 304126841
    0x30a0e04060f06140a020f010911031b0a0b07060b09010303210908040b070816111206010b0703050705070305120415030e06060f04140f010e010b0a0503060904140a060609 75
    0x1c225a40141c1105000c0035130001e181d0b2981c500d0740f1074007a0b141c14105178101c0c5001780f070885a55055082a6444003006074142c4500c0078568110b081d1112920108500e268000040d9201035000950407030070028003000c0c0c0000c1044034003420300030a60745220360128a8081003a4000c50008650740f80b4001031980d21800d4100c20b00201c0c6040c4010401600c1e2121070b03015034066103186650001e11041044049012a10340c019196000c0c041c681060900b40680754251400c1400387c03a12000c01c0c0d00e21180400e506043e100140d822909000356514103e406400041082702c0a22036042c01001261082011420000c418902c00380e480d03081c105184262643c2004103010325082c6010099103200201300154042d409848159800d8040c1380014060107644c02114419040f61003440307081441411464141e031003e061a40305a680ca42c0e61407010310030701200e44002901400070514074541446181d07007107805040e1400d01308079604c92081c1007003235114045500a9a6050821058041c0d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 304129334 1250 304128084 304128089
    0x103020a020c22110f04030318080d0206070809030a020a110f1201060810061d190606030203090f0d050304110d060e030703020705040606050409090c080303010b040f0b13050f0f03030a0e0406 84
    0x21400c07414010300c5c1c48180c126004600000f418001d400030100c154121001001c00100f440e0000c0300e00c0b048100342c1c060340701c83c2c0503191440090080c50001e40d82c040004121111800103034000c2000d0712091f260a403103a000000016480b0700220035070020350b680c11481d1149808540000034102e89000c1e406072418200b4403c00c0c2d0740b5801d0600401c5030403a240f41360265000360081c1c909699862450466420140c0c2811a12152600c2c0707002c90501d07070541c013551040b07140000702c41e0040c5901f009144c2c5e0390625114140020400c04c0064002180c03041c8400c03018101504202c0c0c28801c50b6034040c00d83d0f2000c11151101c0c1c1c0085221002d00d9410424400141000c1d0380800c042420064000c04a03c99401000d5100340c4841d003000401c29a03a501c1c0008100c01d00540b80c0302d50715540c12005a40c0300c0c1c45041c2e03811410300c002040404c41001128800e0401c00b035100d54040c50442803002e1020412155075005000180c50740260f202400209a43c0c805540c40c0d030b2003d802c06003000229080c54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 304130584 1250 304129334 304129361
    0x10c05210c0702120114070c0b060405040b0c1e0406050918010501120e0708191202150406090311060109060f120812100f032306060f0103020a020c22 66
    0x80c000e00c42102400c01c1110b0107150144c40700c0129001101403140500440640b90911168040030454455484056055000c0c40303200c10b488141c40b50420001510320988018180c0c9141102140c010040e030002048400341c042c0c07041c00804251802e00c80107800660007440030840004401200703140400c0e14440e8a400100344008550600c40000c00c80c102043d840f0000076690105840d1a280421a0a00074101c000403103020255400c84100224082c410840300202c18210b541c00143c0042546100300007403100e6100344e650360307032202000307802950410340500c000042c1003001980c040c0010b6018240044010611901c3c004103201c2511090b8030589807550091004400200c1c41b008a4500c0c00701019043d2a9840c2c1e007071024448e1a10750b01c200e11880c3c4a880010801100b0360080b8400e20406d401462600391030201c45c2d0300d03003204070394290380402102d06500c002d600a502074003040c2a284100c5090312003840c085514001424040c0742c0c041c40d401000740e40c1130a2405010402d4144 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 304131834 1250 304130584 304130647
    0x17060a060b070b150103090b0a02090102060f0103030f050d060306240b090303070b0a06150c030f0e0102030a08040510061e1208030a020309120f0306181303050f0c010c05 75
    0x43d1104050801e0182c4418007040142c090311016a00c00d0b00815007054004070788a0071400d0010310040207501c4501c04c540036001c4c0c800090481110560424102c0384c140c0c80e96240d09030000c90803a5a07130b2040d010140c80e80e41c0c0e80d0000c804074149125548224000485200100b081d8070b400c80180000d6601200c7e00b00c04c20000800543c4001c401d8412095200d101d424003901e4114100020f421203420070005880e01c24203203110707150321800811215010f40c8030300210b0301000b07a040300c0754040c40d02240d001d49e00030001c030ba1f4401c0c070900206500a000f40180c0301854242d00c55102034602681c4240c19403111000c0c03000d135103207610040e90000e0550301b198000c03a0a036561110054000144840055640440045d81c0d100e401d02160b90200230300d00010360345440715001c0e0040d03604241c0e0000d000b04501682d415920201441c194040c4040421040f4140400c0c0e804480980c0000c02e855810001804a90b20f1071340d003402040300300341c041c2d101d02d61600c4245142c0d0090a80e4840c1400e5500311 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 304133084 1250 304131834 304131847
    0x1a0d0204030b25141c020a08190506010e06070606080d050d0e030c21040f120615060516260a0816231b06180a02030c011817060a060b 59
    0x41100b44034645050040c07000e6245d00c1c1861030030410340030b40d0508201c0340c1e0000520034001c41c2d110705042e1240d1390011084090504204421040b16811681c144c081150307404101900d240c55406000160b114610105809440710300941c00c20f41340f401d40d24045880481d14041c500f08602480c1d030300300e599000450030b1004e80c1c4401c43c0d9512500140f0705001e4820080011540380c417408450260500c0e82400b00c1c46540c6822520206500032019103c407494001d000c090b42d09030742d0340c460031116165101824030115003040002006140b500301c803004040320b070916102c6800c0192859041d12116001e49503071107040050258003000b000d10440d8144100c4c016441134120040b00d04840446c82c209085c141c035600624040e208440340c141c008218400e0f090407502c000a4103d20410410008425480915003055640c520340503000354190440001c40141d03521800c82c60600b580c2e08503880c07501c00c0d980d08150b180c540ca803020b0909a5007080c000c21015810314042c5200422018000510b0210b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 304134334 1250 304133084 304133087
    0x3060f060304050a03110f06101401020a20130524150706091509060905010e070f09020a03090b04050601060f0f120507030b19050a0b04050a1a0d0204030b25 69
    0x8590752001014865280d8800382c186c802006401c420b060703c0d038116011818151a080390b01d0314140b0a0644102107418203007000c0d480850803412451380002c3c4e64001c3c2e61582c0b1003541c060041c886072030304020320342005203542006004141c05801b041c0c8000c14030710040b825810480213500d02d1b55004141c1180400c48001e5140d04458080d500f00380001500030641c50514110348100d45c12200396402c2c46050b205222031640050829440b42e4001c004201c5082d82854940c419031250603800b4184040800400100350018114410300703203000501c00c40346568100c0c10600135101a1800d51040005020080d08404020406010341c24800262902c1e014010043c0340c1ea0070558a000380c0390404a4581c0e806500b000000755070042500542c00e0500c0c4940300100918801c00b0320469032484001690a64933048409807130000d05641c035840d051103400f0b903031441521900012007400704103e4218000b1403000d40051441198540300500b003042078076108100a5000c1803d000b04800e1342c3e441c59 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 304135584 1250 304134334 304134343
    0x15150409020a0e040201030f1103160809070b0c010b1011060106301b02030a0801170a020d03050f0d0f14090d0c050a0b0c090907090506030c070f0204090803060f06030405 75
    0x65106030304401c4140d4543c40120040c180c0d001c8c00360507507401c2905004950f00c8100c051807242c0072841c06901c0c200304500017110030080c00d45d400070040e044110284403403c0b002004000001c07201c400420201e4114000c290b1100c1034028900c001912108020f200712030038881c15004217118501800c10214540c280195442401c0340008031080c1d200c1c0b00c002c241c44c07940160340c1c2090411800d6524100021001e0340b02e500400000c00051414000403031210170700003c1c000300c2d40500000b00b1050710260b090000d00e20b1107850175414084c080c441c410700030550000510a40e2402d02c0c002c01c080d0311813a40359080d52038040306041d00f040003c0800080410006180346035515501d00800c00606a05105041503410321000d014266080308021a030003080c001071031900015034598900340d4843c101101c00410f14019254051020000b0941e80f10440e80942000da0140d840c400038030704141d000030111008403030100c0715070310040200600c2d4a000482340d2004082683d105103545003903958152103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 304136690 1106 304135584 304135589
    0x11010507050f1516090f12170309071701020304032c03030f090315090304031b08010c0905031212041707020904061a040c0807140c15150409020a 64
    0x303861151241d20f040702d056241104030241072003a00340004030601415140c0812308080f0345980102c420055008030b1058008254407880d011904a070607145a0000d021644141308110119800c48032aa40b11050116000c000a030f01e5074184031904131003003030140c0510010a603c2428091140106842d2100b1000c403401101d0f900d281c014444000c81e038041458105000410000f4240c02e213a00040d441c1e001c6074131a00d80c40d100010300311481c120b0b08d007000a0550070b08120608042c40418128009203074868a0007a51406541c0501c0c0c0242c0002c1c070705121103600e0301000070b4410503a140154002c04543d8141000d0400310068000099020210000d4007448201d81c13405118101d06050705880d440c6042da2900c8040e07400c9000002d0310901c00004101d000001c00e4140244e50207036400d0b48000c10a0304003040110b106006c5200080c1c041d501d890b0042c009039071400c035500308 = true := by decide +kernel

theorem cover : BRFrame.Cov 303956834 304136690 := by
  have h0 := BRFrame.cov_init 303956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 303956834 ≤ n) (h2 : n < 304136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
