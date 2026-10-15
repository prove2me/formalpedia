-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3812
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:45:16.544659+00:00
-- url     : https://prove2.me/submissions/e10aa471-9b2a-401a-ab61-6f3e0f94ee86

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 685431654 ≤ n < 685611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 685432904 1250 685431654 685431661
    0x2070c0b0a030204080c0603010311190902070b063c0d15051906030209010b0d0b030a050609070b0c0c04090804270b0d1a131403070b070f0c150603050303 68
    0x800031342080c0705a080502c10b10740381e915141030080c1141e050b6a008405c60316000c0c150414000b000207100300810419403004000501017489101910740345209000754401c500b401d10410140301042031064090200320807041d26044100f0745484940e51140201d2845400c4807400100001a92440070b041c0249100700a4001e0440303a01ca0307403160320304020750381c5402e031070038400d40403a4240d01000350400d90f407400601420007204c000c1c128070140c0e590080380040342c42004c00c1c20303c02e101200301d1b01d1703074040420f00c50341107024071012010b8910b0050050600c1041d241035030307441510040e2180210f40e1819204107108203801210042c0c1000198480664588c01d00142500200420803000ca40b622010700d0f894035041951750300035900076006500d01c03580b4421200c01060080c0c076040151050401550001703000314021309402d102140a151240024140031005000047c07203d41080050102c0014258024004e00e00290308a00301e030400306403103c0341c90000e040b950800b0f0050b12021041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 685434154 1250 685432904 685432907
    0x106050a030f1a01061403151201060303090503010213091a180108070501050711010e0604120b040204240e0a09141006090c0c03050319060b0a17160302070c0b0a 71
    0x269602d4501c141152108165407103e0807802c40c90a0181000050992031581042140040a95000118450006021294540040c1c480c00320840d0455560351503150800a054004221000810060b4000c1d450402c114000c0400303a4002c0c080c042c17a041c1d540251003014841584032012040703001d0030b000c0000c55070400d0b020703519909228001103407160394404203d41d4402e03002e4130f16042c3c0c050940711070725a0000c019141000b108042c160804400e000014002d141101c0c030903c3c02d405006912418180750040c4001d50701d1055824482a0007649a10a98410305200000700c842410140e005503c03403401c5413000d094980c5002d000c0c0d2a0f1001058012500420400301c101d848840c200002655a19a07000351288a11301001203134494010b4808280503400540d4444140b0f82c0910a640c000701d100c000316109078200c89410700c0c0104403a88895085a840c00c85120f45004001da60b2030000003c0800b441c40381040e104141e00800e983d000c1200f526140300203820b0b1342080076100c0828500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 685435404 1250 685434154 685434173
    0x40506010e130308161e03090512211315060e0604060b030a0b030c0607030302210c1605150403121d0a0602160b01060c02150c0a0b090106050a03 64
    0x6164100208080400c8080c640c0c0149403030060f030715450f8a585961480d070b00c0e00441c0e02500340c040c2800302074031088070b0190446c0d0316101d501c0c0e003684000a1007001400c150b840d10811501d8072880360070030440500d0044d04609044000c07640c554001080e5074440804000041502000a21035540c203c06215091110381260090700c850b41002c00c40b55480d4001c102c10f551301c4c2d11440001040c100086a0021150707000a000b181e0040d046480342c00170007001c605160301060054001950101c0c40d03083c012106038070b20081000460204155091003180890383c6e01c0f416119085482510340c03940708201090000d040040800e0440d0552440d007030802805034a4000980502c640c07500e980031583c102c0d0700f400c010791200e001000b01507400c2c00c0d9a0b0b07034000b0341c099202c000c80151b46201140c0000c0413207007105d011b07207116550031040701d4052061003441601c001c0180c043c00e17018070090fa402c080004a042801da0810f4040015895484040c1c1c010820307a04441d81114406a001c400c1c8a140107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 685436654 1250 685435404 685435409
    0x40b1902120301030c061707170c07081201051c0c090510120c050301051003200d0c1202040b01140702040908040504060e06120607080a021e070f03030c090b120405011404050601 78
    0x2c44a20300c5070061101138813030751f60449548000c143d89004d00d00001d00103c9161b40c0c4260880c0300d1078030341000743d144c403c4d450b00f0000d0140505d080480044c005030400301c0c002079003080100700d0002070068580d1103200391007013409074680c07582c1d275100002d44140b680007101c4010101740341c92280416840c1081d6200c240e80d03000301070280d800c3c1070109080201d04030707410341180c0e088120160329090b0010f1101440341d110003070541c0710b00b21103d00c00c04119403044104c0244000303483e10100310103605c1408180d507001b07804035041c4807000c0303c1c000d443d0001d60b007201c0d1000e6040f80c000070b0900c0c00e45407006071400340c0e170015038209280c14004250402540c51290043d80300b2140d404108188003070640d40c0719070464540c0000340d007043c04102c4c3c1a100ea0040c100440070004c110010545009410b00c1c0d81d0060242903402d01c407000710384001d240c0c051192843c8422070307243c420b00d0340341807481801480c452070040300040e54415002409100003980311052440f0403207040301e9103040c1810b000341e0351031007030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 685437904 1250 685436654 685436657
    0x601030f020a030b180606120a110a1d0a06090506030901151d090d05271e040509060106092705040f02031e0d0309111003150506040b1902120301030c06 67
    0x2641c01c043c0717035000214564400c0c031004080925110829000b80c0e40d04501800d260381031500c0c0c0343d02c0c03401c070803421026250380445603545505403452645100403005004130f0302d9002d44490300b000d00c0545c2e440214841039601c15601341c0c0d0740352601c00d85c41e030041c0400222501032100100e004900c4e241c5c03e0307900030300800780b0303200c841610385414000c2d988940c0c9001c1c055004c60800c0001e0640c00c003600044491000c0c12902111401d441a8007013055413a141c0510364001c41109098540b03890300e031007180e4014540b02c000f0300480d030501c40c2c098540e10030b42c01598013202c1404c5400007180d900398503a0f01040d441d40e034203204504092038110035054001e80120301ca800341008010403c504940d41c03a0305548890010441d60080e07070030a0b0000d20800c0c0c42518005d600103910502d03503c90091848a110b0150b500194030400403450220464090308414450001000b04102007413030748041e5151100c0c03000e041201d0594031402039260165903500f49200a6003c0000005c0c0246d0101d054102c4255 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 685439154 1250 685437904 685437919
    0x1507140c01020f0c090708040c03080d0207020108090a021e060f0d060f0b0304080703231206120106081e03090901030c030201080a0506060304140106120f0c0605090112050601030f020a030b 83
    0x14243d030a40742d0b202100c2c015041101c440028144520902115420a00a160b103410084e100e8481c54419400b040b044c40d0100e4000503d0000c55a0110416501482c1440a00361003222035002400708140400103140302540f800515849583d070500302d5440101d0b8903485a039070700c0d0304882c10020749018400c002da485a42d000c00a14900c10004681c480c540c0302c01c9082c40d00000380e8081d51a01500b007201948000078420f60705410031002e0083c00d110b18144d1804030342d46009420440c080b81049400702c12a410b0550400505800098444a400e00480240070fa1000351014500c1d50051040d181e500904500c00001071105444800c3d050724000e9075408096581e40b801241510380c15921a5001401080001e0109000e00c000521040003000003084a603515100002050700c0b6034ac3c00d60b100da070700b03986070070030004407854100c000d10304c0b0304206013421010b078000b804d00c00041d881c400f0400d44820011380c460b03200c0c1c0d0000600c40c10522046440d0150b001009004000241507076008000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 685440404 1250 685439154 685439173
    0x209180103140d052d07060504110307231212031006140706020a18141305010e041e050d0507030e01030e0709091109040605071d030c1507140c0102 65
    0x40469904030020f80f82d25803e02c2e01100481c03c05e4005818190707484484a1302c1002d10606080324000c001041c000d1402044a0419040a01540c2c9040e800b1a10a601c503180810400240720400e5108102c0400d0410024600501081001205246502c000e00480e00071102c441800d201850094042c2e101814a4503240d800958040010100ca2036a42805024840c001900c0d0340003400d020030a4076200101c5150940582800d46081d000b4150300382c0705000e810b40c2c3e8100605050f1030038407014802c0c842545011400f241404000e23101500d85003410b0038420110800604042009034002c0480301c00352900d030300043c950f8203c0c66080340000c095902d090317019803080c06514400c5d000a0050a04540f82c0b003000e400403d5034400480b0315240001f21900203030f4400100320b1103140a100301060b586094140180003102002c84041041010b4500f1341041e00c0006410041c00c405807207030113484407440b500310b819000713121b801401d0031000041655101c0c004501c030742c6809002c0e0210741004a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 685441654 1250 685440404 685440443
    0x140a05071b030e09070215010b0405030f010b18060a0b0409020d05010e04020f130e060c0903010b10090b090f030f01140c1e130f08010516031811040209180103 70
    0x4024070809070006a82200e6040e6914100403160341040b0107004030750100b005e181d05554510000d92007200e1a500c0842d04000c4d80c10140820912071500000070800c92101600190001a6448818280780007242c00110540c031052000c0c405089801c1c0310030307150356680560101035800407144100150400340006015401441424043c69005144c0d0104d907003150184031403082c5a1a84c0035005496000406444a0070302c20f0754081c1004d05641683e0b00e0245050500351408600424002c201c04001607084551024000080d2240c0212441c0d4034660340700040e0011b081c81840341c0c1d050142c82003d51214405610009110b60000c000e07003445e69800d040300100c2c1c0543d504410200a4200140c400d81200340c5c001e000e0210154200c001c61602ea820800c5074400b16040502241e66605c2070110f050030048441d02a440903181c1480214400b040c0c48082080c440002080c000c9200500103035595a90161100084040c06007400c0f650000341c0d10820b21420300c000d4568580728104c4000d5007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 685442904 1250 685441654 685441697
    0xe030f131a030f04060605180108010c02060c07140106030215090f0306071d0d08030708091005071b030207031b09050f0c04030b2e06030c1719140a0507 67
    0x7240c200c800e6a00710340d58442c3e5031819020007030003100c00035542d11b000301c0c4a0b60344182e10143c1e00d82c080c10510340d641c10020280d00f101c00203d294400e543c0140e0030888846500811a0b000c240d0200841d187d1520f8100f80314050032131904020350000c010204e8010100b10040030300261602250b07003082c24005a01030685404050300e0900004955482d60714035030351100c2d2011901b51010344460b074030860325210201150400d94843c800101282c0500802604c100303e10400343d801e02c8002c11507800d04c010041c0003502c6030081d03c042c00030030306580d034203040c0240305000085411050000c2c51150101c00060a01c185001e00c0490501e80310109240d55100801188a01d038203055581c40e042c01d6071509225100c00801440041400240d15982180103400a05001c040588000011420030300007800780c4d050100d4240412941ca8103903941070b04100da20300c0d000704030015645101e00001104c07a01801a20b20b10030315002c0303100c003030110040385640220705c14459580e6071160800404143c2040707 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 685444154 1250 685442904 685442939
    0xd03060b030106030216060603060e0610060509011202121510180302090405070308220b0a020a0303050703020d0e0d140c030703260a0509070603270201030e030f13 72
    0x21040a10043c00078074041d0340108841c14941340e03989025500c950305e0105803182504111076040c0c4a010029036404200701858101c881600d400742601e041c080c0c003c02502805000340e04020324056040b64160842d811208541580714002685260806031544084a050f010500428020443c0c20409128100a807009800e0f0503020104078030316000c0229880c409007003030f00c40b4020441c00000103011940107010780c515844070341c0103501800d544070b102e10b141c1384c0c80b0301c0c1540310030088452f42c59400300710400b0855040c203001a460b111480110024001c07a414202c850307242c07141429144400040e0075101c03811030345c2c0c0c0d0040407402e0701d100031403406847c600b406e841e4001d0214100090290800d50650154084041000004c0c3c0b0050f0044000940300006800e654005011041c5010320140020740180d040610443c03c11511070003040300a0703094400d10340c2ea800100021a8801c0d04030501c03450304c1070122038940024070183e414641c084c90b0718415a0801840c00122240031826507401d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 685445404 1250 685444154 685444169
    0x10318120f030c0c300e040501120201080f09010b130203090c0d121d040f02071a06010c260f030901051b030a0c0e0310060806090f0a030c15180201020d0306 69
    0x41d00e072407030740e40211042851602c140030210f000030303200c8808100300c80782620410a69030455006c88000a1000b1180e06030483da4000810080880150b40c0091603550030806032082002c1c40e60300c00d2549401008010300490740038450402d04141c4004940266025100944c15115003d11060410103c20301c2c0780302c010b013095920340141d003281c0c0c003400c131ba084070741c072044105243d00b80164001811030f05800b2280303030a80ea0208800c014000c0034010071070080d280d611890300609001001a11156200300c0007090220402c1c00028070584045840070799076514041d07030352141105140f05125420403a2028943c1d07103008009101244010f0b0701741002141e00081d0780c5151103000d005009020001d0500c0148800292040c265840400400380342d0401030100040d2181003180c400c1c00c00c20003a000b00c00070f511040c1300000050b8085100c200055040c18025844005807074581c584401101c0300601c51840c190501d2080c000701e003400032a240c800d034281c4140f10813801b0203808580280c0034042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 685446654 1250 685445404 685445417
    0x120318030f0b1510050d0e01050105012106080a050c011701031a0601021f06141509010c0312060905040309080f0601090b03150903090a23010509010318120f030c 71
    0x400b04002a8034140c201c2080500d4071104031002011514a0700f42c0041d141c00254005100e050b01d4045104280c1c00402c41c000070301081d41f400000030f00350890320428150808502c50800c0c1101c3c1c3c1a40841c009040000903980c01c10140d040c01c584944555041e140810a414500f06c498600504518180ea48c4498044440700c1c0d4880d075084580d80082c2510705501c6504165a8688049001c4220f0706495240c04560941019805c40b00c00703070315100317250103001520540d00121003003030103030b40101c4000e181040b0441d5090900f26210558800e184016520300403012a4980841d00054421400b0f42c031842011940d441c0010740c1d40c802001c0080081d000b079401804517640e280c01c10003d41303070024100c4108481c000d820809042080e90000328a41c0002170030501d40c20300c845244001c141b2402d1050b604036507000b0140b0b04d00900c0c11228100f01000074100720380d03070180d404070980a28007104158810090705d401c0300007a00800484c00410702d02d0100fa1811403080c06420b140c04813580c6c41d035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 685447904 1250 685446654 685446683
    0x6040b0105040b0f2a06160507200409150f060506070206030714131d09011401090c0c08040303081519120507080d05041d011d060307090612031803 65
    0x9030480e400040800817000c5114401342c0101042c4611144010700e5140649401e04111840604024090b100501444814001074010401902540c89001e040c8070381c144008901e20001801444c11050041001050300502d0440009039441102c0c040c011640801c5410b41301c00030420b050060110082d0700042c108002044544200c0c01048100d0210003000e082160b0302102d04408401508804e027000c2045100b000200c035145849900b0074081d0740200900d01488202c041d00c0c0c08140100c900d915110f04000b0707041032055410000c91500801401d45580c0c5038036000302034440945600d11600a95403140f0402d260402404074501e426500d5005200c0c5000c04403408407030024401d40703072400b5402000036003a0091100708a801404c0e55015a513a00345001e182054149901400311406150014006945103121412550034091b00d0140b940e610400024900f0340c1d5604668440c504025001684280c241004100d152081e00c401003486001104103485000c24800a4040c8401c0c841c017 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 685449154 1250 685447904 685447927
    0x203010f03081c020a030c021b0603041b1203030c02060604140105150c030d0c09080d020309040f0b03151b2503120608070905280c03090c0e06040b0105040b 69
    0x1c0003420f44031644280500001840d4200700e8120020b104040303500d0fa140c94035010740c103004014405a1610151100f95040c001107480c50100a000174034505801c1c4900205080b41108400140400c12035000100e8542c0b800502034070f03980c81d020015204110204079185414051400180400804140b16070b00c0c1104020104081d04035145006008000311503001c03000740010580c001483e04040b90340e40c41e0b0030300200809429480408950014017201205a03404000c64924880403130300425003400e190311210042812002c0c1c0b6900d0304c1750b03c121107814803000d11894070030589050101824600d4082c001402d2040c1038a140b00d01c00344030f006c0007107a20302032001000c0b1030080c0b41401d032036808070200d481110348a800c6088541d2240030100201e00c103901482da40007603140500400d8582020300c1d11020340360710442c1408503450348681902e0364440d503ca0080d00750000c5030190000d98850b02c0d07580e1000c003a50141e025904014500c032040d4011801c590071918450303000303840d10510459 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 685450404 1250 685449154 685449157
    0x1e0b0d0803100906030f03080601080c030a090212031c06050d0201050405041a030d0c020310021920120d0c08040b0406020702150c15070e030309090c0c011e0f0203010f0308 76
    0x105000203024400701240104044c413a00c00914880c606c65031360000c0d181405090b030940240500c3c104244142005960b001d01802e59030084090b00c008102c0d50034510004d1001101c81500046922000c618200c0648401881c03031060360000808111854070340b001e01000715250940a80130a804200410260809900100b0009220002c501d0581110f40010742030103c1d4018080028410140080c01e501d03092140001c030b038940081c21450200c80a2004031380700b030150814014030000a802c07106100c1c4088c55106414051015541754644555100c201604000390700e40a0f10300d420015642c0310300445669028981281c1c0c0c48480b55656600c11000c1d5000b058100c2c1c0040321900280e50400b104005045200130780806825401003c0598a484400003040d400c20400c448034189999100481140c03912034060394907281030795509000100720f1284240d0300d0110761070007002201040341e801ca52040ca01a5101c2071011300031404484c82603000078081c11004051918007080007529103030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 685451654 1250 685450404 685450411
    0xa1a0a080a021b0a050118150e0c09100e0f0405150a02070209040320070b190512010b1308010519230c0d1103040503031f0f091e0b0d0803 61
    0x107015140c86100400485000c0b003c107800304555100e038000004000c1c0078016440c000400791040c2d0315404998a070762a2600020b0050300303000703699102031103a8440922010140000c050003a00e1281000c070068450003042d4400c0a0b4030708807110110b1011648251031501440d04100240224a6050415101d2480150501030401d50820038040140c42c2c048a542c03007540203441c0c035a03180c03000d076501003400c2090b001c541c85683c014130b000303201030b1002c0d0068030340c0c21811000c207040c0c0603010301050301c0358480c01115805140307024000140e07483e5400f00812080460000c0b084070542c0c1c0d0142ca0f4281c2d10141c40c0340141d0803266503201403000a5a20910f201c062140f0200c1e0301d030245500c8030500e203c06480700b28800600250415400c4a82d0007660b0342549400350991031803800d511181d40700c2c0406800034083d20603080610910b48410b8800304040d10a500c0d91001580d59201c042c2c000f001d256103602c40c28288418020040642031040c401044800f408054036000c0c150389450290744000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 685452904 1250 685451654 685451671
    0x9080d0c0504030b07023316181211030d080103030c0c0e2a130e091f02031510020d0c030219030507021903020a090f18050303060a1a0a08 61
    0x2c0c440000032030b590800e80e83c0540c0381c54015144080c1d0440c610009001c80640151410244510344241d2182000031940d101c2500e01d080760240d80300d008203c400e148550001c000c0d40070401c801062078509143c0c44c4032814441c1140c01ca80307081603014141c450f00110b0000000c01c400c4001000401e02803608084514465045c3c1d440c00c680320641c0884c0b0745030a03030f55600f4001b210f041e0825507030340e21091414141b01040e021820110540030b09005a0290b02030002341070000300114151803030030400320f1042010039040200b1041c154000f02e00a403c21150844d2052401c0c600100ca401c0092010399502c4281c0c2c060444610b01050a440044042504030114030a488036503070f81030a0514003048081c400d07541c2680d903003424010070041400c0031100c1c00401c5440441040160346420707001044450200d40482c074001d85070040300041c4542c0c0d407020b203400e68007160b0070200301c404401948240821501071410940760380c1085148130f9400c0d140c8030900020080c1440390f90280701c2007903015104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 685454154 1250 685452904 685452907
    0x403030203090c0a030308090d08010f051e03010501030f06060b120c07021206390a0f090905070c0b0a0608060c09040e030d05100806061f05071704150309080d0c05 72
    0xc12000c1003010045610686c0000c41711010f1184102040c0100880900c00b8070b402c4406504000080090301d0700d80c4030386071007081103d01e6000313a0345004041030869040107000304800d694a0410854000081604888007441d12201040c4810220166030075080c03407940d182e40c1035848844280b00c5600044059030b1000034000c3c41c1111190030001181700d5010701c0204100000d00035543c80e070050121680d505c28084462200f42240510400ea52030101140b40c2a0104414000240c5036100340d500b04442036400c045c10000c0d13081d00100c0c9025554032469840e50955500169a800c45160b40154245904140d020070032440161000d88112a070003003000520000801c00c03680303540e00c480400026181c0715001c2160481030b151000009002d0040500ac0c0d40c50101c00042c12003d140500380c9030314068500958400e8410016515a65806244050b0b01c0f4801c641040c40350b00b29202e5481c4c0d107603428001000e124403c0c09407242d5250b0050b211410200750808050242059070101404c1040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 685455404 1250 685454154 685454173
    0xb0105040c050c06091e07031101051605030c0604020a120b0c0306220e01050610020c0607060605132a05030408030618040303090203060f07050a0f120c03050109180803040303020309 80
    0x1003441014021180b04000303244008511940d21801d81076181c00080c6c03504024001c00114141106161070707a00c00b403074100d565045071410710008407910707500507160b44404104007408000c0080c10700e00540c02100e4101d4001e0762a0100261920386550003031102c0d00307180201d0b6643d9648809540c10000040c014203c0c401910116204411586000c0c551a5241c1e101400344020a00c80c0d1030308600c05541006940003805030181d1744245d0b40c2030443c0078241c0051709000388582a4400c5000d030000404080300d1070b50449100003d0301d098502240c4558032200642000369040300101e800754500d80320b65056076039035180c02c840c54000134102c98000c64041e541900d16511004078500ca2071080c0c03400290300d2080d005062038400000c200e004003040d4a01440300300e507003280960b0403e1a840c5060540e2809811080320b6081400c0326a4080600b01a003000e0100c0d01600524181c6401000410405010f00040c440c072142650020305048400c20110300402e05c40d40007141c0c0711b0040030482e45041c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 685456654 1250 685455404 685455427
    0x10305071d041e11120a0c120818041b020604051203090a060b0a0801060f030c0f3b0106030f05061504120314161e0305042907060e0d09030b0105040c05 67
    0x10264102c900c046d00210031074010001551280c80c09489031801e0005620040da88112291141d0790310308042d00c1c3c8c1201440b81c999260740010b41c003801c285d00d44400c40da86000c4013a60300c8000f40c6044800340136440440380b540c5050300603288119a480008e043c44000d6443e400000c0070040b0000c1c1c0c12019540b000f00e80340e0024025a0b001380795104600384042d1550a00300d0500400303030050003100c1020340d8208104c0030424403481d00440d051502d00248401205a41e18454100802e00c00e0601b801000042494060340f106102113004e640c244400c0e03a50800300b11903111080380c00f0210307000070701043c00015803503c0b081d02d000b80b00341000e044071001d0b01001036081c2c1040e105504c41d8407822103450108410180d024015a007014070a040c6080c0300d40c2c0c00f5015005038055040000c2d000d0340701c480c088e1410101c46040501c41c903046907880d030090612001602c00800001034910032155032021881c45989440204d0760414804034490f42420100000303490604011002c012051040000b1030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 685457904 1250 685456654 685456669
    0x14062202030106080d0c0c21031b020306190f150e1e0c13050405190b0a051906030e0303091005070306080d080615120c070218010305071d041e11 64
    0x4006884000e06806c01c0d1a2020400c0e805401c00743c4003028598805020301c0108030310101c03c5505081040c0002000b803041403a5041440019605204100c284200101401c01c004518000400e00b445250b401c0030010080c0c446c0008508041c9483c000c0c200601901c0240407500500480012008403001c0c400384c04c56401e00783c503501511000011296a9140101178050050009030740c02d21a51a2003030038580c1484200141003c86074981151050319035400003003101400000308448000070305003100d002c004021340034680100349886031000b00110300005907031150b80803034024010300d115440d0400180c1000b625500034161107641c0840e441da8144011840082c841e035135040580352080c01c0180b00210004100d4900008005c102507076090451100c0d4072103100071f003c03655017110b440883d0071443c011200e81e00c14000640040100040440d08004940c3c2c003401d1100c1300c169a50601b42c1034a01541c00520b0006101c03040301034240b0004402414902440c034265a0940c880d0204141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 685459154 1250 685457904 685457923
    0x10050c13060503160914011409030106140f040b100f02120c031207391707060e12090f030705040f06060809010b0a06180b0a0801031406220203010608 66
    0x4102c0c08010402256104000600204024508090f50b180f82c52400156440325040c0705041210034a510544080384600300e0301049000381c000c008803552001881c803056040003a00c3e114541da108245c0b2689043c2c0200c003034038040101403910300c0144c1401517505a0001c10b601040d400790245d43d403c1c04e6503030f90103000b040018002841d902d00503075608001c104001402c40d024044078410801100e401002002c60602e929044001d00541840c10000c00c00c210450042402e041181180342450841014022851060b1424000005100111034423500f4120182c860710310184002079052030071001c0048036040140540c1c01a0b52210080b0303040d2400300f41005c10071078680d04104500341d8003111882d4440b203500000c01119a04100245054540703108400402c000ca0001111050121030204004c02c01d10011903a6645002805001003001744002c0c1c41740d2f01c021008d8403020307c0100c0c844c0d02c00c0380b02c005104d5200c004150038000c801c0c50880117a805640c1c900010070b1145003000038410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 685460404 1250 685459154 685459157
    0xd06050a090902010807171b040f08031209010621060b030f030c0c0a03080703030b03030409060f030308011d0403050f0f04120507050d03052505011a0f1210050c1306 73
    0x140b800c0d40d40005040d41002030001d0042005c01c4403040148501c81c41e680741c200400e80c0280106041030308018003e4026a0010045488503010003d8500c1c000002890700d01580864000d103641c6030604513080325054414000c8690040b08000c03088000d00800030640e603c2100001361040840010038505040e000c0089210b078000980d040002e04100050300005004540041016040d942d4000703081c058140014203142c1c50703d04142c1540da0034000d880c007415510108210b00c0da0b0741c201684641906110540115847e54000304056518030b1118011000c03d005510340ca803034681d0f003107400340d025a000c0b501c4080e042c008940700a804400510003044e5402ca050f6030b1209500342030307080c44407a40c0721610842e802c900003000241c00c002a00c515504040f41c6101048680c020070b005070705001001001035103412840140344840500811030b150040d039442c2d0580f050541800301240a028010306241d00c030130002c60342c02c150741d005168020410007056040591815203040e0308807540d00000d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 685461654 1250 685460404 685460411
    0x621050a0603050714060d0507091e030c060509011d060d090b22051b030709020a0f03110406120b06090301140415060302360711150402060307050d06050a09 69
    0x10030f2100c10031116015046020144c0c0521030450009480e51181c0503503802013644600014250700d000d49032a500a0241c4503c1c10240c14811a1900481600d07020072104001c98a0002c651188a4001e4910042e41070f10b81441c2a1b45441c90b80e041a8150910150700203010414450103880d24000c0341801441440c9030301c81828140c0120201400103968001465117401c0d02c00003080d4001924903113601110f0024100203510804a814180190011001c0d14000640c01440341da2088030b0084400c002d40e0200310052281d490300380e03184514840c060000b06120640c1010042c294003010110310020b1149180c8610b10000ca03080d94003600894081c0c80541c400c10042c0210340d01244480c99201d041081590b0a50340019008080c8600c0c0d000340c0030380c004804105070003403071404555060b501c10282e141d14103030700010004001d41d550720701c16024101300c90752140564225a40980c0d030040200c0c1c00c641e034801c4111a1034101c02002d200c01138a80c80000b405d6141c9884e01d20180503181000f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 685462904 1250 685461654 685461659
    0x9010b130f0f1a01021c202e05070c17090102010209030f060103020a09020f070602220e01050f12070e04020310091a06060a020601050103020c070306140921040621050a06 75
    0xa8101b10342e2901c000c0d082540031004910300e9501280801e40101e1242001d0b56054200c02110b10301091010300250424520791002c2807240202d01e03030160400c84080c14480e039920b0708402ca030360b01791945004114540320304142d182d1441081c003a081001040c4001401c0184000000340780c0182501558041d03003110006200394140041a44081e2240390000d510f06011040840503071b00c903411001e007845a000c2036200000300000e1004c0000010410071420b0503403150f480204414003882443e11800b001d4521008605081100e0500101080c000d42880d62804019499080c00144100c2c1d05004145583c08104e0107842040c695a0207240500c140000010f8030601302c480181050741310340c0062228842243e070004010f41501c07070a10f00582c40d41400c3c2e00140c0b4040480d04010f008038240700d80707084104904002944541c800a0445d94040300a142c0c030000b02c0d4001b4030b02c0c0d40e605800c220034001140981c01000790300c00d80c00d0044054100145107802240c205550928446403100c104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 685464154 1250 685462904 685462907
    0x1110f070f0303081303020c1c240c0e0904021014030f0106020c0a121b180f0b09160806010507060e10060905060d1b240809010b130f0f1a01 62
    0x122907002140d01d40917001465a80c5010b5a41ca55a40e1610300c9842c0312a204183d001c10ba24900e20f0702039000030366855a5409050320460309030000d2903040518070344401192100d116039540a890900a004a5101d40b150380030b00c16591003e940400c28440b404620013000858403000350710960701400c102d061035050020003070500780003c500030700c09c4140880a01946450303544100c2629400300007000400c1c0da600800421810b6640100c0348c0c0445030f109200e007680a50021081007122540c1006130007030110070000301410a65220328030a00c41c80c0e14400940c020003650340c100e03905040081c20f081d200d0350360b0025141c008095207600e4002d41e079107028000c024000c0c2009020500828455490b00202141d410321a106020303055022a0201150180c0308682c410094405008105004002134090103030400c58a40241c00155291001440240341840f54102d6940018040c010842d803201d01e600242030071250040289503140d14450303021090340b00700b00018030401d07a01121030410100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 685465404 1250 685464154 685464167
    0xc0f050307080f0a14040513020307020715050c0c040504050c0909010e0331081b010516061e0606020303060d1103071503140f1b0d090605240f01110f070f0303 70
    0x60003100359000e010a12140c2d56234140c842c000c070282c41005031030b40c1c0d81d400b04078035084c0c49521a803100001c1d0740700305a8040d884001002d42404000881d01e90400c0f29080c0400c950f001c460280c0260082413400c021454142480c981109a10002245d060f000200160856120407045484042c0c103e03150725440454460009214800c40100790031240351801154581010580201e14451000d2072070010343e00030415540c00c0d09510012000c11b0080c0c4c54900300030404240d480b51007231661410b00c0071401d070710700800060720500e0f0b01031819500c0340380600441503201202180c5d42d00400a0707880c1d07070f03880070480400280041a050854081e06d03c001900300ca0342c9058060030342c80c0c0441000200c1c403a01c100c09420180450f0039201001c00903200c1c8501d800b034000240d0340e540c2000185410300c002e035000280100c01c240014003516000c4c1740e82071404030341440c4042d0450841013400c00076601411050014501000c2541d26030443c4500803410300c06960070005088084c0c100c24010705038800e2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 685466654 1250 685465404 685465427
    0x1c0c03060905040b01050108091212090601050316090c030e01020703020604030807020304050d0f0807170a031505010e040905070f0602010906060f06050f0304031209030509040c0f0c0f050307080f0a 87
    0x1070208510308064842d8010864140560b0341444280b80105015200421280b11200211400c0303507224012a507014061007400d4903460384910500001203810300e03001c210104030440303180c206180c03180b9082400b005401404500400e055030340041d2541c1400c00c0c0000c0c2011407082c3d018100034a81485c002d4460b05018040f0b000315441400b06004503129560384610700350704400461603408081c81e00500b07900c0b8501d0700074020308828020b0904061035501034054a1915101808a484150744401601c0c0c40d0307118503400900d50404c405514209584401c1c80d081c05103054800c0325855100c0707020240120b501c0400140e46d01c0c901001404001d120b2034000e455809844030b8014a002c80044c4a40544020340920150000200e010035000310042d4400c0b0408500c1480390310715906002e800c6401c65510345004038280f0401480840c441c2407a00c0c1c2c50030365500e410810078a06d44a00440000c80303142200c540c0300401004000c14003c5c009490fa2017690484c0a030b62740c140460003000c240296 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 685467904 1250 685466654 685466669
    0x11e0f0b0304060606080115030207050f2508121803150c0703080603060403210f050c0d05090705031e01091b050a06110c0d052104090b030712080f1c0c0306 69
    0x140f0231100c1e00b00000c02008101e10340940c4031400f90400c10304040c5d44080c0d440301e51080d0559443c10003002c2148090101034229210403669072400b00907100d04d4209120440b2210811034140c000380c0501c103429800001504030303540f14491100350f0515001c2070b1020820804042140800c240d4854621136100005074044c0c445410300d980c0140c115110000c01d4150360522200d103440b000016404051204140c10090042e41030040100b00c19034015100d900b4464113103c00242c8580300090221b0403210060024803c0940113120b1914070700004522500c595203851006012800c0820f40b10480f0143c1580440c820b41380808000c4541440c0d0b01200078025403841c170030799410021840e41980340d016598906180a0343c03804608180c01100d0b0f0030812010941f003e43c0ca0840740e03015206551000c5020040c00d18101d04144d0b0b10055807149203d1180e070318100c080090303004006403048040001c0c0301814100d40700c07881c100241170540d200100c5030307550341c81c614202d9141c0076000042050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 685469154 1250 685467904 685467917
    0xc1002011e051e0103121407020130020c0607110601080307020d06290306130b0604200a02030c070f06050306120723031c08011e0f0b0304060606 64
    0x3010301d40c0c04100d00075401c00a1156540700000d505521956125000c1482d03199100b040e90384034034080e80d200100800c4980021105100c140100c4034a4007214003094050315070081072103030014040c1100520032402680c00354419445400e0350094005001540003c1c0d000d80355600c0c10450003080c05640866100742540480f00401c40c0100120445280039015118000041003c0c00c25101a21039801d180d10aa80e05200e41d42c04046000280c80511a00700d09880060712003c85581e01c1405ca2000030788456000008030708240303050b901c100002d110b100c14211580004980742c50161300860f584101503040080d08505400091201d040030f0041c1c04400d0301082d040c64402804c500004100c0760242d1106400e45034184005c0008000501c3e400ca4101c0b415406417181682e61960000128001d1042c84110141550041c441380e110240319512103406030b00e41000c050070400c00c1d14422180130b415400100e44e140204600c400900841c000e00b030341e2801c151401e5400c0b00c01c543c0c80030041055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 685470404 1250 685469154 685469171
    0x9080f06070f0f0203040e09060f0603010c0e01030203100306060e0f100b09010e040e031b12160b0a110304060e0c0f010f0e0301020d0204030516060807020303061c0c080c100201 78
    0x421610b62a031500e09854002c00e0f10711801e20503403944c03090750030440c80140c200d001c2016002e0001a041c0c41401400f842d42034545a003000c0c94243c980645042c80480c4d003400e801d02c415407281e03010b154400250000e8007000c41da0781d1192011076525070000c0c1d03884550f5804000400794600d00281e0004c8405000c07800452a016006215002d4000a10704001000105000e550b4480e04480c0e100351070b14040c4c1e0303941c0d044844501d80b1680303001c0b20035015010311125280341001c2c040c191002c040d02c0c4215051808260b69407000d002c000100091003180d075541403078030624907603000f4520946c4222400255100203200c0c1524040c1c0c114034003032145030984080e80e07190b6400060349241340c0c02c90500c0c5160300f101034000390190051800500c0901e10110b00001405400a01c42c6d03044440f21240c22045916848111803d450490305140503134020404510a400e003180500c60030040511201d010702d0b400d982d0078586003400d03404041ea507802259104102d03d0000d10000c160103403030000300210308 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 685471654 1250 685470404 685470407
    0x14070f08010b09040f11041503060e070309170703050a08060d03210b09090a0209060109030c050f0d1e030f0e180901060b07050a0b07050301030b13020f1009080f0607 73
    0xc4140108225440c0114103400503440302c0d04020a40100b0540500c04e40c0d0071135020100711f030000c1c0308002d03090a044050201c114024400d040c1076070f00e0640d49199036a02e01c002903020740450081116080c41041e84a001e500c182806001028401d41c0c400781e81d243d020381c00600c0c1541c040c0000b48142007001e4604006034100900b01c16112946844036560100301c0811001029145522078100c181e042c00c0020f00603000c41c109002d240301301c600010f2a160769004458881c11800004c081c0d2170841021f1240f4504041d10342ca003444000d001078a1200b00e552a038405071003230b014660b8205100075100003019042007084920103901d00c0d08a02407080ba038000740810510070141c100004070740002c41c0c0700701001e4000401401e000c5850703603551080b40c548503561f5032180400f035950721660808034998510810450741203e030041e2004440e510350300310403c1c03031118a000499000c000c525480c0c0441e00e803029a08140b014940310302c1d0303074031b850680710506020100b480f14840742c000e0b40400513400e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 685472904 1250 685471654 685471667
    0x11d0f0708040305090415030501110f1602030304120609151107230d0206070f0906120c030605220b150a18030b01031515061d0d020a0914070f 63
    0x5181481c0085098485040070f481c10700c100d107119600b060404c030320342d90b408005102c18002c89128200801c00d0801c00c43c0b03824500e0141014280301c4006c100101659180b50105110609000400796454a69644000b02d5482e10040003101c030b1a40303c052003014408280c5156007000c2921000384000c05a0b40d81111940c82402d20040903016400001c58405240e4001c110103061140c0860340142c40c1d40380d010f55920000c0300c03010006440f500d040080300740b00d49081ca00f04ca82c0c61711380c4043d0180c3d40c0c2d04600602440c10400b02055030f81e00d80000e41c1c0d40d0b00c650614880302c40c1041c440317450b860544e2000071b680814240c68003034841192000f50800d42501256543d80d00c610306020000d251543c0c0d4500c141071039001909030440000084184041c0740080c03098402d0740b4408000c05400c00501068400707081c412600454004000d141c0c00f83c3d00004000304800c1c0081044840e0070700c41c1e000801001e11504010340540e41d4084921001d40e40c04006a003040e16410880f0414a0700000103001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 685474154 1250 685472904 685472911
    0xd0309080d0207050a05010203010602031b1609020304030e0918070605031b07050f011109010e09040f11010521010e130f0609060f020c0d1404140607030203190305011d0f 75
    0x10301d540001c1c400c09000092002c8125140d00c076000391766030350f90341c0002503880d041284420000400000080a02c141c0010f844114007081c4d20400109c3c3c3c5021041c00003900300030001c2d03003401500380030159030740e40d201180d178400c0204612150003110740360704140ca4000076811020500601b00240b103000b12840d000b11880301b0080d44d44c150b81e034000c0e02c4d041e0709201200e1001720f80ca40c284128032a900040703c010703003441d40084e81c940c158641500d0070010840020389002c0c0141d031541c034000000c500d441070707181010041818480c1c9070a0440a18032010001c3d01c810b08100c504160040c000103610032a6aa00508200803c4113018200d4440d1100456092401840c0681c0c404040e4200101078028500803080140e0440d02e5514441045844940c50701c49070000800c40345498001c03000000554041d00d0f44940e00740480c509640130300600d41c0c806038041c1c042d8403040c480158001280c80c2b05201c4003016940c041415458424024410020b8105c04601c0300c694604108801d00c1000003590f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 685475404 1250 685474154 685474177
    0xc120c0e031e0c0307060e100507211b06020319091e0501110f0d0e0f0d08130c03080a0f050a1b26070b090627030c0d03050105030d030908 61
    0xc45018508003610b0300340b21001c0981c145c000e0300000590140c10140c5624980e0b004d40344100141200e00c011034452041380401810704a00114540200591039502c1d030040b0b2450030b0031003003440401114103596000b08800c0b00c40580000420070b0a00c60841210807082554500740003401c03c960b104800944015903480486903e1240384051182c250061034600e100d0350020365451083d0b031060b1140350b114120100c141c0742080c060590340040068a408142d580501500301e0009401c4211081c8501511040b00c410f0700d2100ca501140c1c40d880800b00551003140b07195a2104c86810182520f0440400c030700901006018901c640c68024042501400408140419400e40c910345000c1c400422604d0703180f00e40368032816040008403c0d0003010303141d000b031348680407035902c111030313140d4601040700c4103112010003a61492401500038904030304030300a1411380c0d007407052042d4a82d290400042001002036111401045181411300500c01e00c00030b549020710004120362201c0c2c20b144102800305a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 685476654 1250 685475404 685475443
    0x1407050a14040b1303060c0215060402090607050d05071403070221010906060b131403030d020307020a0f03031d0109030806010e01020a1a060a2108031503010c120c0e03 74
    0x5150040d03907000c460143c010010055112200403405410741662800121001d03032908640d04070183c00060589000c44404642c0c4074196140c41c1800701a41103000f00d00c0e040b13413040c800140000e5090082c604ea401c1c0d030340d6440707840e814142040c01011078806465080d903042003020401684614140c1d15905565031101036403812a80300281c01801181d101403c020b180c141b001c2007000b2000010f0101c102c2c22071900c03034000d490314501001804c030302c0901c030351503402002006003440d2541c0181d40e020b401e03070041d01e0303107120191207007162040c41300c008400296482c10641d4045c80241140c0050400381d4000b089070203880c2d500174014040c080c211605000440384030072202c0e80300300100d481c0503510140c034250280140c040e00704416019a183c6100c1d0b2041d601c04281c4899114080030001c0d810415850514060389072102039601c064000300040003450100c0203075441c24058010807060300e80d120450302c402c00e401502100c1980140300304001ca4000c50b140a60380004e0b001c0d007402c07035010601 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 685477904 1250 685476654 685476677
    0xa06020a030309110907030e10060506040905041e0503070204050f19050402060c0a05210f0f03040c23030d08010f331d0f0d030c0203101a01031407050a 67
    0xf450090804440c2c45e40043c1c1002003100e91b65041e000020f1290381d410455481c0d2184201150035038000b4014160040d006110030072121903290803907a00580154030500c01034085841380003102c4503280d001d40b484d072700019070901181001e210b600e602c00b032180006680c9092505c6043c2160340080c60f021021600c55000c10207560340d00c02141d01c0c480a1508039030019440e8503015803116400c2a00512105c80c50022500e41d4080c0743c21240d040106c007040ea840c0c0700c0f074001a0f401d2078001400076200a00760f0310300412580305c42c0c40e007600081c06113060000f460402d00304051500306440200d00070460180010040c3e480061101000d5034101c0041c0301c40101007000070300b2250503000e886640c90380d140700e898101c10b82005984003021041030725502400a19028232a0500440782804d4000441c1110f000c0480d00c1034508481c4248010280c1d01c4840045510500b69020788085112805003001e1a040940c1c040c82070500d5000741c650800705c00c2c03034400400b40460048074150820f00070241000f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 685479154 1250 685477904 685477913
    0xf080a0908030a200a0209040813080d030b03010c0314061c1505010305210909070c06060f090608060402030c01081905090d0f03021801112410050a06020a030309 71
    0x10103841ca1a00300c0f030300c03000c080c0c0d4018900e0041c1c000820908440a00c090b0413050049002d40708543c003c0d00080480c0c032580c3d12110558003540300a00030820780c201c08a050341090100a1a03c0135665011032040c12102c100b508484002070400245886c1001c41486202804600e1740e0001c1c040307508641c2d800c4004000f44030241c0a160041001c1140710055100340010741c8028180ca01513003c480040282412850b50000c0c41c81c446803501c10140003003249440d10801142d40060603161001c6851201d50b10402521203540082780c001000032030074440c20300f0600c9010300034980344004045a0500d070700444d440d80c0c1e2640405040041500000b0416926002d010040c2c15541030204060300d010317090750b916590418008400180341400000c0454860300136600d46032100840c80e610300c101d8000560b08020f14405a000328011902c0c4404100e00600c81800ea10541c00001902458814041908558640c0100748510f038404010f10100303500050903202164142400101421030342413 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 685480404 1250 685479154 685479167
    0x1140a150314011701140c090f06070813090b0117010b03060d0209010303030c1d010807080a1506021f1b0302130b0409020901080a1b03230108030414010305040f080a 73
    0x82191801030200300000d40e54014513480503040c41800c008020b161030811120003d04400c0d98146e41d840d00c240080305242c0303400301c4143c05800b03009080d64500b50595a45001503000402903018543c5d000d10300f00300400c880e010b51800c940f02481c14907241026a0042a94603d0601540c03280c50b101100280ea141c8402000c100410b80041c900c000b5036960b03240080203000e040340700c1c2d40020810041c2d0116601c0031440202c00500503103481616580f010411580000d000300003c004039110946a0201da0001b61984054902503024205000a8130f6040c00303844c0d4202d40404c100ca240c075420402d0424440d004104500c05440c0161b502d000c240d40d0744c2d031900d68540141caa14100014000744404181e8010001c9035001c2c0c07682005a52546029001c8032400c02c0c0104151b91031135091904a0b2190340084004421090900f04514514400940e0760341d00b42c12141c0e072540000b9090151100d48000141c01800c2480d05100364509951015003140f025080109901008900e050383c09000b141c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 685481654 1250 685480404 685480421
    0x3030e0106051c03030c09030209040209070c060e0705150f0f0a050d020d02210906010b0706141501080f06030703061116030302030a1a031e0f060403051201140a1503 73
    0x20403450f0340c40c42d02d008006100b103c01c4811800300c0d181680c1c0c141940d0040b07150340100d903002010902d090352240c003800f0300104002e0240b0704210551132400300041491003541c0009030030000a19040d401c0c481880390b0b2170400c4000c1281544c0a015504611900c44105c62032040d0300d80030b16459501410b01915240a182803902c425030002ca0740b0200010182d0242c00c0f1944210300030441c0481c074004007520303540240c45041040e0003010060200514910003071010a115500000f25800341d603403488501a801c1d1094071082040c469024442c1d0380c031030342154005045109041c030303030f0400c0d83c0000c0d500c0040c0c1c400100303034036203c81c1401c1d16000c45400380c44c078140d410042841072070098900180203520464908460601d0091800200c13002c02501820365a03000d03001b025102000100030030482c1c6140040519403040d07810b0040311388814080b040c042c130711135243c3c4c0d92182e080c040b580c135403d2016044003e80403241001040c103680c0729042c0104507002c4051382100e200500100320042c10452 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 685482904 1250 685481654 685481659
    0xa03080319050a0b03061513020d050106020d0f0c030c0201121a04060906270623011b050613060216030507060605090705030c0a021e060411030c03030703030e010605 73
    0x8001c014101075158184100c21448660401c6165684035010302103034082c01080342c06a00041c001102e51061521554082a00809405c003480c0c011070741a0581c0d001e100a2442d05031107000400ca510b8040000300230800c01070400c403840000c0440001d081007085c61001e41000f50061030382040d640600e100242588002c00f06120281400c0e0309201c0d0100d404203114000c5140480004058840d031181d07005540050f00030b405035146600140c3c0070036030300c00c0000c0040d0340e40310400900b240310a600003040d00c49c00d1505181c0380e841d10001402c2c0140c1c003c042c1154102c0e10140c0c50000b00f0204074a584400c16442140006209003007100080c00394201ea001e4100042c20208107242c0c00c0b0000d020741d9441800700b4032080b034940e0180311501c2005e94010001c50010700c04076044000c4507014142225040c030441d101b180d030b20040c013900000c104000c90f4040d009501440240018902c90300189401900281030764261000071a03524840c05c403015080583e0380c040700b58210002e4001d900100b600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 685484154 1250 685482904 685482907
    0x1602040b06030f040c0605040602150402061216080a0603030905060c01090606060c020306010807214704031d0d080d14100501050703050c0a0b150a0501020f0307110a0308 75
    0x51403d82440410540e4140c0741c402c010480040c08a20840803a420745a041d40585200c0100380c00c0e9a0301468090003c992021090048840f001c1e07030880d0242c851a207808000b088951940350207041808007030b107000400303810a0070a1002c47c1d040102c050854000380c03515035880800c04006c40c018030b004038004000c03c0c242200014501c1c0d2206883c1d20641c000c500703a03043c59a031a03c000755909128401c0d2900340142d010001400420201c1003c0d04c03034020040700c0d55501e00e0485644404000000c84170b400010490b0b01d040181641d0f03200401c00d03010091514850404e501e000e4141c44a003413030f0b03c0c0254042988038589454807100c181c1003035804040a6201e032588840e540140078000c3d0040c66402ea4400002d07c0000c0c03103c8a10111481a11114036090103030314226086c2d03010402102062280c8107014000444200d4554401e140112103804107031080f030704014403c1042d0744424110740c0300f201200031252002c01120010740c0e01100c81110f100f504404100c03402e803107034000703800d0240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 685485404 1250 685484154 685484161
    0x40b0601030e2a040614060702060c0d09090b12060a0e03070b0a090203060f0115080c09130b090114130c030b030d030f0c1e1416080706060f05061602040b0603 70
    0x25100003289048410000400f15030303100f0284400c45002d0b104800b4010340c0d416aa031300c0e07401c1c40c5004110103800a00001d28003100c0d03035456443c1414001c0004000744000c4400c200c854072a11451148904c211941b0741250710400340b159880324040e002c90000c0c0e95079881c0002d0507030b00b00220340e9103540c0301c17544180614044c01403000602c0501c500380d000c0d01880e000103400301030325001c4905030b4150340f05c062209030310318404a4011303000801c03402d000901044040c0c126611020a00746101030b844c80451003401c030109026001d9010703172200381c410a074501c40042603603402c0050f4000c0d941c0384600040c001c200141c205d000c3d09480d12801d805005042c40700344580c0c0d05410021000c03031018000d100389a9800d8044461107101c0c80901ca0400540e0041c800d141e1048810011000340660018117140c41c8003c0c90880c0c0d121001c003103484290000b170300c80c20000303103026100081506c0074803044010302e000c012850500c40d41d803100f400e08035001c0d401000c65883ea801000c103064003403e203039100e14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 685486654 1250 685485404 685485433
    0x12102030f060d0f03050a050405040e06100b03011203030f02040b03071e0f080621030a1106010506040302061c020d060b07020117060105041512020c25030308040b0601030e 76
    0x140199a035102070a9140c00048881c00c2c00c0c55510056903000502491000c99920111101d8001401e01c80401c0b104102c006901c1d640c038018004d00c01e1600c8083c04941c100650a030002c1d500340d51110100e254207200400c00d5180e100404001c0300d805080c04a00e1110090010009100300d821200080c8404400c1c40641507000d4071041440e480806032010b086480e04094400303450340b411507000107078403200184007420002e4182075210b414a403402c84e1000c05000007410368110b5100c4100095a40212041040c000c1020500401d403e813842450a400d640210740c2e14843d8964104a0402d81250002c610303201c3d030b044038422401540108481500c9801c41800c03903220700b4080c0d0014820500301c000c101031826040c0d00481e4141c4440c0d20301807030301c0350b401c030b8104e04160403005202e8082c2c02658000c4850004007041254000505a2100b440514504403229a0280320f5004141c11040c0b00013608144a69041600308110043c2580ca80b00124040d10010305401c456008102342e0000c070a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 685487904 1250 685486654 685486657
    0x90103090c0b09100c1203020f090a03060c0f0c0c0608180a0f0b010503010513021203071502030103020a0b130e0c0405030f010e19050c040911100206072606010e012102 74
    0x510b040302e210410004c03e03501191160041d0401608001084c4400039565002e540148244100c036060f05080100e804000703541141540e0098401540b900c54031030886910260512842d021408d003003100511a8980c001010058022a0140915040415140300b591141040c00b034100000b00d841130f9075a440c00c4492401421011240c5034010f4001007014941805642d100712401d07c1c40101d290b4881c3c007000540070006400010500003000402d01084115080c1c41e0b61142c0e001025960794074600c18441c1d000c105a200c056202c0b01408541160320341d02d40030004603165030500380a1a1144100090703e8891a0b000c26414818021b01e00700e408819003000780c404200c0402d45114040c0d030308410000c5c040c1040028015009100748900340d14242d48079608a60103146000d40794581c4001044242400740004030150340600100211541d10104448403000c180b4201468110b10405c078120341d240240040303061040c1c01d140035540341d103d000801002400c04a2600b204020460244001d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 685489154 1250 685487904 685487917
    0x403051f050f06010e040915020d02040e070c0b070f181d010819060e010b190911181c08031504050a02130b031008151501030c0212090103090c0b 64
    0x3500d00780340026012020051405100300c0381a1250190310032084100002000314803c00c82c0c0c403a400d00e0034441f8103d0b4510240000c1e0490200042c2d8071810422001c0c21014010600020070810101e09d20004448061a43c0c00c9003407402c0070021300840b043c0079140d03000480710450501030030000008106420420b5002e0f600500c542581450b40c807880c2c03968448803c03440c4a510300120004802c000b0b860303030344460b5401142d5000000d0704d5903040001102189020142000d501c0504030603c66401e29216a04041c0511001240340010b4039001030048075080400c0c502c20281c100e41e1072070300c88492840020003070b800006955203140c40c440004e080b143c1903041501440c9010f0005003084518422290444089101c2440403441d120a000300769200170714401d80d01d20032050008015404001ca40e600c400c124950041d24501045005d2141c0180c6610700d0415091840c0f46103c4c940118000400760f01d87d1803982d0b42c40b004880142c3c0500034100c0700828900d0845400103003045108050840c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 685490404 1250 685489154 685489213
    0x50703111c05071b05030c01050c01140403020a0b072a030c020301111e030906040605130611031902090a050906120303090a0b07230304020d0f050607121116030203040305 75
    0x1032204100d1074040141c00ba50285c0e60305944045c081c40c4056004001810320380354030500100f0040103030900d40c1d038000003d5508a0160740540c44e9003003000001c621a80d404001403418681c0c40160803c0c140024803125042c480040305090301d41e0505118282d00742805801a0003400300c070748100445034041d0b001b5003440300c2e844010745551a6514003442100e004041890082005803135649030740d401448003402c0035045100b008090400603009018803880c5180c44460b043d00e030303d4000e81c1c07003405403000f4608031100340c41080b00d542c0907507030310651400b518801c1c1e034150341c0d0b6500c0b000410818003e200c041d030024032000c420418174180000d910000207200d000b001c0c03c00e80701c600003030300c4000690081d00d81e524010481020303071551000195071720500041c03e01500208684480755001d18141041d5603079040034080005441e0024210b143c0c0c02d141910420465400f8505096980a103000c00318921180c03000002c00d040c420010380700a1a080070503a80e0340c04040c140046413218031145e001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 685491654 1250 685490404 685490423
    0x603020303070c29070b220c0603050a0e0a060b1309061d0c0a03141c0e15041211040609020a0c05010b090f041202070e0a0911040606050703111c0507 66
    0x1a044c200545540618090100d00c0e18100390090307840c22481c1c40010101000e0a1904c0c03042c482c000d00c0d98041007107241c042c0442c4003456090541c01007e03124010f1101d040700341440702c0c10840d50300009141e0021504941d00003001d001e140001103405400c950030300d80321414111100203004403a0700205c111034502160380c06020506901031303102e0588005039644148000c0313080000c29100c100c4004450607040a80b1600320032000d06284401400c82d1410008800e101c0c5229142048940042d52007a041c1c6000d0500e07282c501d0b031040110580134000c1214295100c03501481d292070300458040c0802150a540f00c082848005010122040013610150b0034085004800d04001c9001d6015010080b190742c600c0e51540c90301411844100c003400c08600c01d806c0c00013604548042c40e94090343c0202c0c408940720825061142c4408140c41c80b9900c524a080c00070008680c102c070440c4c1d20140d00d42407480c114051291898242011880510f03984803150100664040d8018001c00d0007034491030014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 685492904 1250 685491654 685491689
    0x40512060403140c0f0102070b07030e060603030315120312060a060816030902180108011b140904090f05030c010204061b0c050906120a1203060e0c0307030f0603020303070c 76
    0x859880000740c40c0500030030012548000c0c40b004803401402107651880845000501c0000c40c0c0742285d000e00e40550301a102c0d2014840d0459042c0202d02000d58030400030000c0303082801c0066100c0c80050600ca0241000040784e2034561940c000e0400e2a0495805490300d0f0b402000245400f40710840c0c15922407200701c080410214000c01800f4000c5285180352039120002000c260003c0c03551344003e0340e00540b00b40c011800c899044042d20301901e400800440c0318000c2c1d040c03058015140240030780c03e10134807071603441c500d00711402a5200c07144100d07804170384490f99082c0100c80d02a6168040c009010005081105030030540027401112030320381c0c5240c0c101ca00c2c0ca22003040814100d00007061120035100800640c9008011280c100c040140054196042100c0451400c500303850200c07416500400051135443d0907108200003489445004c3c8401d1611110071400d510008284c103040c99a990702c960100203695201502079a406000c4036540d02c0c950800b100c4400399881010000c04200c80e11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 685494154 1250 685492904 685492939
    0x105060105070f2904061d030c06060f0a0f062f0303040f0c050d050609061e01061101021326160521030403230c01140d0608120405 58
    0xc58440940000c05141d14501a07614203e503090b0490684190103440da0500512680c010086030081b4418403000880440d0341018291100840310902101e400901040503600c20118420380d0180d021140040300401c0e440000b90004135940020000900c41c090100e0082d40000115658070114909400841d450081e280c03200c4010311000002c0d5042130000c100019005200c0409080c0b28616840c0b21a490710081103014407080416649a0311200a000700420284442d03600018011814541894000404018244180704000801075042804016080290f0640e5100c3d945540801d041a55444103030b8402c00c58040e2142240d282030721600001c0c0c0b80010022000907240c82c0140e0503500d0002048010858418030441e2010a90246e03140c046040c001000654880c0340d10a03210001117070640a4624007141100302a84591058102680c000d99407030007207080151104e030390320700040c480009407070b05038405011889048080e01c41606c403500508207940050320307803c0c4e00740d588185 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 685495404 1250 685494154 685494157
    0x705073605090c0310090b010e04051207050307050706030614011809020904020c150f2206090615030b0106170f1303110a030e040b01030236030715020105060105 71
    0x4045040148401038554810a15040103502484803426191802940f202007070804508405110f8070381c0d940d0a52904022108134041e0140107804800903113480c0565a4503a5014000203a994030711022400300101f001c200100c4200729400402e80d15201da81c2d000103000fa240034002c2da0844600318520340802c0d441041d8401441030814001c501e03051034806408000d501c101e80315038203c0e401b0020346012150401c80954810319141c48001c0034982100f00d02080c1c080600034001341c0c180c11503500e1001405400a1401c650003080010321800c00b860004001c102c8201a044107641090000007407001040303c00d030495806d6283d1701d00781c0315030107507c10500f0401c03502290552549004290302c0900c0d40103110b10380303103c0e00f40407400400c120030300c2e40380124a85c0c0403800540e80b21040341c0541064051403440a1003800c0650034a24004e4454401405003213a5008240c201040640600740e02e0342e448024030740180680f0f007815260000881c2d0450842d405c4000340d802c0001180c200d500c01c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 685496654 1250 685495404 685495469
    0x170a1707030e040b01020601051905041d010b01020a05030a0815091801050c070f0f03090b030109061a0a02030d090c090606020f010b09060d0b04060605130b0108060f0d080c0f03070507 81
    0xa001c7c0c00c2580c2401c00300424100050f20386001c461481e500810f00b51914820072040140981062036081e54062503142900e1200c54042d0445d008140d005c0002072000bc1950003408040c20104020740c1d0380c2a00c5006c40301d02098a0743c1c010324407001d01204017603030b10003e03d0b1146640000c0c01076550b40d040748580c92194240007000711811003207500104441050252840344a854011105d83d078034110300c00d440e00b00703800c030003542545c6d103004001039402140700d0f0041c0d5030803208213424040034020180d101d0154452503802951100400d50030400e61041d10809400f42003410445540c8501000790386850011240d4400d610f40040b002075403401540b054420f80e80108040040c0c00d01e80e6400841c1100a001281c50715101c444c08103ca81c0c43e00922217980c18800400180300d405400010700307144020302014010041201d0300c3c4d03803c4d15600740b40f40740d6540010380340740d0356200304c0e00451901c58258130b081114040800c45004009000c01d10108030341ca00310460484c041c107009191103040021 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 685497904 1250 685496654 685496657
    0x41103070212040b2532070b0a0c050a06020a020c09010b070f03180909080304052505061c06091b03060e040201083d0b04030c170a1707030e040b01 65
    0x20f002859108415111103e4618000050090440b9450340c0e041b810302070042086080b5071440005241e017241d03c000000304c0b14880c1d0010803000345003100310030803446240d110104200c10380030b0781402d022003040f102c00c1c11a48510215900c03800c58500a4551082c40496803003640707004000104a070582050f541c0c2c07160807100d58115242241d6081d1501007030600962581c80f80a040018100050310580d01600c0c001c102480d42d81c0b40c030b171819900b8007405558400140c0e4514510f8840c00c5400200e44080c1c1e141550401d130380c1d080031100ba176400c02d0f12403441c200d0f8a0811102050300754541d0042c083c0803010383d1120344541411281981070f1002e40c06806a080d8441000601540c4501c056540200d0703ca020559100801c2000115055038080c0d02041c140c0041c2d0310070801650650400001c00c0c000052780c0c00d041c215500e04d040c10b040d610034640b8103600a0f61000c8024801d0012506c0701d42c1c450b0481355000d070100c500d404150030545082e404614503c40500403410709000d10000d99005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 685499154 1250 685497904 685497907
    0x803030105040903090f12060c1704261b0106080604080a18050907030902091303090e0a020408070f0510081302040e1e0a02031b0603070302090f041103070212040b 72
    0xc00c0c041c0001403204103c240d0800002d602c0005154044141010103480054041035010460741400342c182d4203000c144800300003009840a00101d00c0c21003141d0046d510900901e8240242c5800f2048038040070007070070101e0310000c0d2196040803504081c141d4102c02100900c0081e03500d041c5251a950704031030140036010200428896144251b110940c5200342c0d141c0c591720725480f04081200f81c04110b900e20302182d0350f0101e20095103008840140c1c403001c500d0210b060004036036401000220244607d1640424101c00f040c0c1c40000c42d0140d601a00040701280d0341d40b591190016007044813403181d2805101802c8180d4a0148140b413068403c1c04c00600e081840c0b4143c0e42400020403820300303850403600808255031001c030581010b4140500c00e00b0700070501054280101410004140f141810f5803488854143c40343d1230b81c1c403e503544180c0320305006840740c014038041600ca0070010381841c0d2041c034069840700082c400801071401002d031a8200d83c480012100181c1c298800c50240d401c10040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 685500404 1250 685499154 685499159
    0xc151006180b092103070b010b090109030b06060d090b0403090603020a0e0613052d041a13060506070f1a011a0f07061803020d0c02010905010305061f05030703110408030301 76
    0x4040002c021441d40501011200c5000c130a5048420003007400ca0180340d08001000e4062200c0840000c1c013400e4022040c51401d4004400a08003c9040c40300429010b0344000240042e42c8400c241d0340d110303100010500001c080e070314100b0840c0310200da00b107010a450032300219045109109a4190039266101e50b400d1056540400420b0b412401444200720700e210b60100e80354a03600b1504046042c00401c80460f80d00c0e00104014054452139480c1c0101c0c540910300405494201e0281420401075503080802031901440e0b901504180c0c00c01504158009501010010a640389481c41030203000b042d200081513591441090b102071040c0d000600e290324000b0022a601c100030008540b407462000d150200555908083d501d042c0010340c80040c800c2042d4041c507805209040340003a82d0302e407650301c080e096070010f0300d8182203002d05410181c1d1900084c2040e1507c80c42c081f18101a18050000c20310041401001d540c021685000001d042003540340c041d03541241500c064a540c2c002860a40c0e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 685501654 1250 685500404 685500419
    0x132003060109050906030f1c030605010804200d0506040b04030e01080f0103140304050d11091f09050a0204081005150d08030c0c03071505270619020c15100618 70
    0x2130041c0034994503000f4956507800d0302c0c4040000c00301d08810401c2ea491014030080014080710000d81c000c0d4140309204040100081e0031842140780104541e003036140194610010038022120040028004c1c031911042c442405225144944141c1c405d0b551884491300141c0116024075050f070b200d1100104030001440020124844e40020441ca107080f41e00b05982c803000501031000000c01500d24145c1c8040c0901d0b141400d0712500d50003850105041d0000042006841502c6001c1c85004580340c0da80000c00d034450490340440e8001c1c5481c0c4115068440c9848801008181c290340b0840d4501800003410241e08104442c803034141d400000720b5085507070f945100c010a0380804c00d01e40141c002040040c0018014000d03212844441c10340000300380c60640f80d04c17135403480c0407051442ea07202e08800c4a1048180010425030101d07100459000c20151092650081d000302e80344014179004d8916403d1807082e441d1140c0d8441e8003803202d90000315543e10425144100240b01c54210180c03280c07010b102c0388 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 685502904 1250 685501654 685501669
    0xb06121507030e191401050108060a0f020f070305120108240a3306020102130302123d05040f122714030d020607031a13200306010905 59
    0x74005040c003055800364038160314240780b44050704503201405224504140b00c207811204030883c000d103008103d69410040402c2d035540b4000c002180e925152243c80c010840c140d01600e0a5a800030b001d00e880700e140d860068800c0c3c0204011589940c1c505000040c004000070715449a404000e0902413501c440d22581005030800a0031104059100c0c4034050400350500f07501e10a00711103005030b46620141d00c400c0700d080e46d100da000c401160b005009245000c3d0b81201031008403941190803008001074084080d043c8034401d45601808040030b01e40c40200c59480032008209001d10801904005000c103810003194000e80e0058400c664850b00040090001070242c0c00358111410f1000610030390090110300d01d010b0162031004039a20040401224422010350340e803004048000d40000c3d20382c000002c3da81c003001800c00d020162141072850b50a02c10194004a281c009081030781c00d400032280150180413400d541c048400007510303000340070b2a0084241c9009442c140e41c0c5209080c940020056503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 685504154 1250 685502904 685502911
    0x11040209120703080c0708070302060f3a0b0414012601020304050c0a080d080c030a0b0613080d050c0a020121050a140112030203031f0510020106030b061215 69
    0x80301c403048011441200400010005600c5400c805559030504408070303050001035804603040b644010010300060351388106407400c8200600c415a15100720442a007208035104550019a59513103181d0701c00181c16001600c00803d404006200170700c41801400102c80e80d1684220b640403032100144004615034681603100c1e1040c0d002c01d1181e04a0550729170032a482603404070380c1c40e40301000b940d00904110900400070b0505201034080c10700301050207016000c1c002c14410018070000001541c20800d0341c401e100800000c0e0100b5140c240200301c50001190074010200e50b4461400542021403040041300d18600101c80034240804d219801074440340c1c1c071034940240345900e401041c40713000c0d440e10075544650f5500d40045080b01c1d0302c261aa008840681201c07400b81d0034541e04c400400d03000004c0b243c0004241c80311510700070101000f07625207845c035080103500c42c42e007011801c80305a054000340156070144e00480a01d4403500204007942aa00380105025000005681841840141803562 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 685505404 1250 685504154 685504159
    0x90f01270f0501110319060b0f070212160602031b01091707110409200f1c05030405040c08010e01080d0801030615150306180b0102061b1c061503050411040209 70
    0x4030100f032402d00c103041c1e405c00c5807000c403508082e503681d00740c0301d105009840050002a920714030b0250f140f230b81c81d54280f1480d5406030051050240c58039038004100141408142d0034030160544645442c0000e40301d6216030410107040200b030016100181c0113100d10f07003c42d60710501c81007001d002d4840040c43c540221302e05480454407241540320b00c2d1228080e02030002d1285049201c40c0c00f041c03c0e4103070400d1907019014040d243c5100170714072607244e021454007140101d440b4204840c08a01d80b007032940c800c43e01301d5034010b81406800d00c80300d0742120005050303e01c4203c0c10141030781c1b01c3c1c01c1c0c1552001628900000a01c800c401000802d495030f01485107812000b0002e0f14450310350500d00d00c402401030704de90010740e58240410a2001d120450100c200f2040030501801c090400004e58070140900a1301c1d20100040e155212003417205d04507207948103950404010801c281ca071410003440e03241304120820b038928a004003482e100c1d115507403280c1c0d8000c24418850102500f480000c0d0441c0380044d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 685506654 1250 685505404 685505411
    0x12030f02030d2313112e0203070b0903090a06050a05090307030309081e0607030b190603051e1e0c070611090109080613020d02011205090f01270f0501 66
    0x141d03051000e0043e8007012481010f00010b20030401c458004400c4014184001d0714291805074001400c89000c00369452002ca075900111040712034000003058015003c01700c640340c51541c0c400d080b034010018000c00d0303010340301d90042d0b5031340e00c00b90603101d101d01c0041981c44085c004060210b0b0f80a880641412141071900500b01441d80300032910b0020641c1050700410202407040020060410101c1d00d24940075442200f00000340f00b01d5640c50b0310190121007496229141c40e01c042e140c0c00b6407074610841c0e4080300348201d5a54800900240400d450a0005080e0715004c0f806400da9090040c0c024071845058154005407102031406503800544441c074107407010000310010485a0240491007140307420b5a5a1ba000c1420003d84209400da0200c1d669030840d404010761044051a100251601a1481a81409541b00482c0d42c005000030301034a9510f000b0500c42400d100080030354504010307074000c1100e03040d1a034003119407660b043d4001000075001c1403440000b4407000e000c0c4c0081e520640010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 685507904 1250 685506654 685506667
    0x6031b100e100c060b0103021c0b041e020306130b03031b1204080115060306050105250b01120210020f120d090503040803031501050324030c0418150612030f0203 71
    0x296091040401000024260b5500f6005028881c4209050b410090030308614000766080b010400c06d401c007000201c1190b4a040841107900e454000502000c030200c4040760419600c004a8002d42003940c49502030100d58140701300b250303914451049418801001141410941c40d0300c007490350303590800400d15000d0220b8401c1420310690241c4007500b00c2e00b001145a035091a6011401091a0300c04410581801d204105998001080b42c424008614064401203c00b0204011405540344010286082a800044c24200301176100289610855403021140c6101d00203e079503404480a00506c0c0d08658070030301800310f042d0002c2501c44049580480d0300c5103a42c0b107184c02c0d50056803040803550000005c0200e06081c24595080740c080909109056081124888040ca1841c0007842d0000800000d02c0b80c20340d40030412001180e1004209010f030100c401c40c01101c1e0260340c1c0044600710b5800480c0b8401c0c450500480b000d80300314001c941a40b0502d078804441e501901107000c0b06502040010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 685509154 1250 685507904 685507909
    0x60102010609020d1406031606050a140414030114010509010909030c020a060e090901021c020a0e03010f1a03030316032412020109090b03060c0a0201020d140f06031b100e 75
    0x240980c0e01c41d182d0001648520b0703560a105441004103058441d230094090190580d0800644105a1f24140b030000c1e103070480e1210561700040c2c0304052811075080440c000980d10701e480896000d4007400d600a000f0b0101070781880312844020302a01e0750214800c8018066007030315603c996103a502915000103802d0352034001ca2801c0210381c221100203001c1c5420182c4605005440503003180680f0002c52400080032030008000c00b0304a61304440c640c00250654003607100b0180031003003420042c020060314682ca00e90000038104c200100c0d214604181c0c01100501d0003209581c454031000b00d0049000c0320907e412401031246040c4038400d4090303000b0f1503c1c0c40300d040c5859000340c60a60031460500d94140009408001164040c00c500c90a0410329841e944001c01e0300c81d04400c1c441481a10b17090606002ea01901500300d030309661503e48000c45201100020501d40103181120794844d03140c54074404d05894010342410359605444090f9108424289668401d1200796249805110343c07048500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 685510404 1250 685509154 685509157
    0x403090b07030f050a12020310090e030c0c01030b0604150f030e150103170403080a0903060b0d020d0311010e1605100302090901030803150607030e0f0405060d0303050a240e0f0c1206010201060902 86
    0x42030b4042720070b0782005202d545d9541c880c010004001c40000c60400141541103941e07401446080c504054070342c120f00c00c20b07840700c3c001c0d60301070111020b0020417015110f60052a1074442c4070100006030412210307008404001c14411418240000070006603070075605c9036401840114440300149108000000210b807114000c3c020b60400307655408541c0746182801815034982c040724034071540301540c0100041e0f8803035124808441e414188581d82c1c2401906107401441250440d001d02d02a48001d2a0340308001c2c40c426050381c1003103c105417200c554100c11812809082c0b007503508032150100600c04150050069680001410314168868140303401160481d0405041140414039011a802c12403a1032000080302e44010f507002c200c64031340040081d502d105620400740505a03204080381406c5200c3d004200c803020b00c10011603200d80b040706584561201c0b40b04001d00002d030741c804541030880070142e150154000c00e09544c200f2030700020001e42010041c2c0031a06541d80ca4a002442010500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 685511654 1250 685510404 685510411
    0x609260a0c030503030702070f0506030a0506030c040c03091b06050a12020906040f2c190605030f030c071d0a020904090b0a060f06090315090f080309060403090b07030f050a120203 79
    0x3d01540c2c0b242420b00c0701a00c1c0c90807581102807140b05000b400c0c030035501d504050b00c3d44480c80650126540d141c00011078141000c480045400c0781c10080c0d400308894260300042d03149482190381c1d402c04568901420f40c40c030034602903a80091000c2042031987e80c4209120080079000000062905002c0c5000501c55401581301c0190381e00d50100800c143d0015048829481103441340d4803000341075018840700301d03040090181100c11001510122401b141e68065409400003038119168040080d4000d42d80e5042904120194031414501003054117060000c02000c051807c400c00c00c5031280140140039401c10007026402594801150380410b1103800280d0080b01540d5001480c0b60130720031a40544c0381d158101c101070200303081003000000e16404c0505a28008143c0c0000c00047c0d174a4000e80c0116030038000b80c6440e0003c0f003031000070000441c001d406140709483d65041c0070341d030381d82c1940d05000d07112000d400329803001051a2280d000b44020420318a0300d2414401703180c000e11541e81280c1059 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 685512904 1250 685511654 685511663
    0x3032208040f1e05060c0706080709080a08180d030c02010f170a0e1b0f09061f030509070e090a1211120705060c121b121806010609260a0c03 62
    0x82c0596510300364500d80c040040d00b001c0da01c25140008400e1043d81d9000c2c0c0f423290b001009181d0001901d0315203d5007442e009407507150150781001102c1d050640d030135000701c0090300c030200813034030840010305d400000140d9155141c0c0300e181440c0e69680065415125040c60305007880051400118944440011039114034200c500014603c224225114500082c481c0b0400400d40d80c49000d034080e0b51440c84901541c00c0490717103100c0558410000c15030246608449130000380b180e20f03072014a1074040c3c0005104030031680c1121070310b65a40c0340e88104004280d800503549d4110968010201b0845091111000d4240c01c111a801030b00a030401e1400c3e00d61540c48030415004070f412b008124061011540104c00010b815060040b0740200213284240030b413410101d03440c20182c110170b044448007a00e0001251010082e00380c507085480e60760018046101000e40d0082d003001258190007000d0f203d040d6400b03000c80e80840c000c4401031b045450080111701d44640700f0f520007203002401c2c030400c10000d14072a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 685514154 1250 685512904 685512929
    0xd18050a050d02010c051b010605042c16030f0309030c170f060108030a1805060f0405101d0d14030708070b18030d0207030507150e0d0203032208040f 66
    0x1281001c41c1840e00c5030361008216410005400034169120003503c014010441d01c4449100b0648822070052446502103070f046810090540c2070303850080b0403490741e0400c070803c1c9030842c0c0140360b400d070325095001d986024240e0212030900110b140207403680c200c64464144419425160b84500e00c031760146a0015141c3e00c0c00809032400030800740228030303807031865800510941d418401c2c969120300881801d0020000c44500e030456101100c00d200005120143c800c6583c1c0c1c040210f0581c69502600985004a0940320010080b41c030030033107101c225500303442005c101c02c0c01008214140c1010201510030000106c3c144400e1007090004107440c911030104599281c0d41c510740101c001200500c2d0340d049002d0f40004143c592808401c4900702c41a40c2c04c010794039002490144c5003400381c0b007801f5120f07002d40d021054170080280e1107860140710348000c84030740b5442d018049903603100407a61207425003070410788000b103260000100998144109034a030305042c0c450b0803260756650b4552010381c1818a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 685515404 1250 685514154 685514173
    0x70f1202010e160e07120203010e011d0411061e0f120121031815030c03050a0c17040c030b160e06040e0412110709060f0f08120d1805 59
    0x10244142c0400c14460809403440c00740b410403540000e5014401c3c6041c880345900022001d512480112080d9112214110f4a0b561108007608100ca024010032003034280b01c0c47d603003241c00209500c2d9445964840400007180303698009101850704142c202004035402056484c09004030700014022060740c030041030741c450408264031118400180c0c00035000260401050702c45440c1841480c01058040c240340d4070000b080400c1c40300842c1181e1018892000c81007100301c1c100d80c035030006840e600c207070381e020301803520b0340d0040504580c245000700001c5010038031107485844002c0400e6a00c01c2c0a001014440b6540e07031107141a00320115003e0840550126043c440f00380c1145145e4a54501900c0e6182494105034002071031040182c0f006d0049000710303507808145031146400c4078546a141c001c0c0c6680079036502140010b0442030041d426580c82050010508015603c040c03000c075402c00000705800743c00904a2000e550003026000d41540c0c03518510b020071407a208030b4002651081e40104140b12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 685516654 1250 685515404 685515407
    0x11090108060a1104271b090621091a01140604030312020c12030a1401030b04020108181f1a01090e090304030c152303060114070501050903041e0602030d050a02070f12 73
    0x5881b001c485842d0201c5200d95a00b082d0321050080039281b26040c40a69415010518000a041e00d1700c42401d8609184598040003100c1240c0350110b41805140080c51f41ca076070364444124128201300d6080300c400d12040020901c110126488500460340044c40c25039035019503070814508108245288400000344012100c0500c00c6018501c2e010f03419200035411540e410058100c05000030b410031150401045d20004458025407259000401700c900c09040803000141e550680c031400120f00345001c0b01411848418003425003a048141c0d101c409081c00d03c00c004410034070141001c00144401c0c0070200000c0e401c01c45000250140d69850a404420140001c140c0e0004240000e20820a540320307184000c6c0300300a9030b40203030090034901252028a0131041180c05084805883e40d82401c00340300e00010048000c1041d229100764641d030240c20300c0e216141404103449610010fa10400c882d000b807071582e610440c0c0041d8140005403601c10302d5251700c030a2000c0140c0581305403940351410714855 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 685517904 1250 685516654 685516661
    0x1c022e020f07061b11090f0901061d180f10150902070c09021608120702190305070b070c02030a03030e07050d0b1302040207050307030c11090108060a110427 69
    0x810904000d05a0b5030078440004c1c09082c0c1ca41c41c10405690f0380c81e4a808220090303040e03007001c5e28041c2c2034500528000c605101019000c1c0d9441282d5440c040c00400c00074902030111809050304582088291142914254180311003106106180641c00e0941c0089409000c1d103403100305e0710000401c0142d024945503c50b103220b0340c4415400d80c8100702540c0082d20705503003103003203800401c40142c0780c580c5803180c0c0c00d017200a20001042101c000541e240c2c8a440454a40e00481499013280c0061020302118101ca00c803480001d8003040051000c0400101020340c81a1300103140c0c500300002810590200e86007130011001180460b8841860f0141840100004002807000b244c2821404107546c0321a00c01141c041c1565100303c1c1002c40c21030554a036501207a0140d80e1020841c0d5480d0101d040081c0300c0c04060404071180840000310541c1441c1061083d41a00c81040241983d601d0b6104050000c09089503070044401c02440000354000c00326259400101e070004207060480b444032080e5046 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 685519154 1250 685517904 685517923
    0x50703030c230c0d110a0f09060f0812220e150411070803060303120c19030504080301141203040b0903100204031a1e07030903030e0c1c022e02 63
    0x41c20b52039882200c642c0d0000554a1030010300740d583d00d42c0c030f10041c100001c11502e030700315040e08000d0340800050036a0180110b10120b68030004104190780d1a200450b03481c903040d02c21580c0035400b258294038100350090090441901c0500904e2603000080303007412000348240c4c0314101c10195042046919400d1344000822880202c5081104074070503483c1030704a00031114041c002c450080000b0303102d6101001129407411420f01c0650184c546420002c90f03540c00381945840d50314002504c09280c80c0a0300515028030f500030384050030750382814500c004020340c064107607502030b1302a0711200c0f080707400340000c002502d2039100003503a5280340c40030b0625081d05519814a01c1d03104000230400f0403004d180030340031050850520f2480d9283c442c004d1390390800d91426809104482002d1061603a015804001d40d00c0c440e4030140b0018100520041d21a07814000301900302c851501108450010b80c425440d00a100411801c407401d040002ca081924500002c8640118503002440545030108100c030b08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 685520404 1250 685519154 685519193
    0x61404150e01033c060e04062a0e040b030102070b100503011d10021c0f1b0e0f01030f110c0d090510050901031d0a030f0809030c28050703030c 63
    0x107440c2c1501c10348806040c1c4104c0040c500d0811030f11084500100390003000040800781e05035600d604003810301d04001d00100645650340142c904810f110078010020030303003581c0401d44400c002c1020000903c40034107040290158107550030000480061102c0103050302a00120f514000d080f0f04000c181803c607a0079000f0061480c10400e002c200006d00014000c3c082100000c01503250340c1005180070301d640c800c2071004951418910b01c010303000d01950210920500490301504140000d030360a84064034000342440c1c100c441000303003441d40c0d40607410001140700003090001d6815503019a11a2a4100c6160303416146c003c0c50304865081c4d480017018000c2d1008039400c800f614141c88001d03084e8410b005180d414580c80b2843c2e070700c1410b01c0103411062003800c0c0e02540d51074440c80c0790081001500c0c540480204400f82e010030380741c25001054505410f1954024685140c41c0c01c4c0180440302d030600303114810a4408a51000a803050044200a611030340760b11510100c0c6e032409410307400d0500102c21 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 685521654 1250 685520404 685520441
    0x50a0912020127020103090506160e010903050c10021e030903010c0302030903031f030c0801020306100f0c0f0609051e100212040b0702120a09060e0406050a061404150e0103 76
    0x892104072110740010b030030b0f0080c100044500061005074040d103c44000075040d4000c0804219000745141500c54521480d035031031407c80d40e88040151556050f41c000030b40507601c031080c07500660034040d0303002c15010002c1c01155607c00c48004c010b44060141403000c4070542000c603500180d41000d010311489042c00f810194118030300491040da0368000204510081d66684011280c081e101203200405103070081c2c2500b0020340c035050501d0107940140e40c0705001d0091240072030100c0e07206401480036102c4a640d48070440d155500d41611564000b0025200d899a91800b03e0018000b0080b01d030000b111800403459082e2200178507800c0c484690282200c0f540104551004100d6944032603a2090340025140310b25166110304130301d407140e0420200701e060000241e548507550031000540407603415555102c00714910400b840280e0b50380740700c3c868210000107000d228490240060b00e18451904034070604180c2d44800198000c85404008808641224140000c0303503410701a00b110710301028174a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 685522904 1250 685521654 685521671
    0x1c060f060807090b091014220507030501030b060a05130f0b04020c0a0512120601050c1e070513060f0902031905040c1d090a230f0d0906020d0801120201090306050a09120201 76
    0x1c21f04040252100b4840c1c03d01805260000c3d40c0600802030600c000310003003000f072510b190060000d0000b80400e54010b101d0100158240c50180c030090280c400c0900000307841c00640c80b00402520360241000e04854035506095600d8032580b02400184070410020032403a1100d041190810011039296900308a081160056010449480d5500101c081ca04140e41d031001d444c40398140465180450342480b4210547d02160348006122810b95000301e88040e464800c80490a00b10307a400d00c5641c2800150f60010230044801e030380516170120307842c1211810300c0c24403120b0718201c1c0ea0840302141d03068017202c42804003040f117180f00c2c0d80c00180710b0700e41d41e02801c180e0480355880c0c1c4402002841d9204203a007110241012801e4003200c0044141140d4841190b03220303072a2611007450400c8005240610001403480c80010f1049890078141c503007018503401e240c80310300380a40000701603051005804000001440500c9850301c01c0301c41d00070000c0c0100491a08104a468011301c5034210f82c1090030f00e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 685524154 1250 685522904 685522919
    0xb040b0d05011d0f030a0e0616061a040b090f0601020307020a0e0f01150c0f030905060a170604060522110c010222060e0d061103070503151c060f060807090b0910 71
    0x4031100c110480c1012590f00c1c7c0d0301e00c00074015100b40f1003116108003800d010801040785542084a030003240300c8441403450140010301084402450b8016032200303080000c41c004a0035104140d821400c1881a80c0c50901d407600401c085492943c40740107900501801c12460b100030a119502400c0f0740c120300c01c125400c141004215244100000e400d08598032160000c05005244981c0141800791a6940710b07101528040c00c540c4943d180351030140401400244075145c184240e0081d94801401c202c0d0811648440f41d08000950b82200100d958584030581d01d001c15070041d01c0b50100000001d03948801d02d0b00d0903814038246000000d201c5240a0b400d202041e0030213091903480000307940c28a001030942c242100a4240d09058000d0402d00106209860354868010351103504101d0400c44c2141800c0c042c01012910522222010040110b014000070126008170f8042c55043c0d00c046401138030746c00c165090180740d0380418402d41d5107154580407400c203447d84650004058101052607494001b2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 685525404 1250 685524154 685524157
    0x10060f0c170a0210180512030906011503090c0f051306030b01150207030b070921020d06090203030904050f010f090b030309150f0a09031709010c060b040b0d05011d0f03 74
    0x390094464041102d00d6824070822007403115126040c402d1010103c021708220902d10080d41c00d4410380a096441000010b00d030b01141d009500f01c900820702603281913018030350745000340641d10800d5107852403e0040b4080504005c054020240c400c2e10961400c010042c02108010001600905050b020030220380300c1111a411a807200300c50f9075500284000403818408aa00014844012101445105503000b4900390503200c683c0c08428075035041003400e000340026120001e50001100d0445c40002d900c46d000079480d130740301a0850f810300f00610006010307500c080b0b03842403a01d100c0b0b0004000001d11250b06c44020803405104200802c818400709440c1e20031a4103050090740c0040280444440400c00c035900c0a40c850081c6481b99606170004003041d00500c070613500388140000712000c0c28030714022a007900d4016102d00500040607621030018000c0c100f0601d038010790304e141c00f503001e858890b503c034000381c4203500028615100b44640a20303042c808144088ca9407000f0001c8400880010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 685526654 1250 685525404 685525433
    0x18080d030f0519051005270c0c0c4f020c0a022806020109030e0609030c090606042c010f05060331030c0c0b090105070b06030106090510060f0c 63
    0x41010450790345c1d00200043c41185544542d4010409a00004006200e012503100500ca0322502034141c0e22100d20f00d180c3e60007111007248890b0400003d03246189010303101c6c180034100d03294000c80103080d00d000503103c4809031101015601d404032590310300c4207466240c009000e8410300c021820020140e0149940c1c50782c1010082c02401200b02100c400e440d92a080c490228502c40040c0d03200c0c2d200d010007806030240003011000700310b0f004a9842145000c1050302c40510000c2d00911101001608225160202030b00140e0015805c000c0403071404880100c00e141d07071030010070350b8084410f144000c00e900e000c16480a01c1c8000c0c04001031080ba42d500c011250400c10007907101c00a00c5488410000c803a1142c4141c4441c0c0311000043d03000c06410070b00d4081240c0c090f9141510310f584d107016600c4188107243c10036000078000c00615000440030b1284640016000e000012042d403100d000508550042d26a004203071076100c0100300c1036a015881c49102039051920044540e0b156648c039540d1010705 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 685527904 1250 685526654 685526701
    0x4090213230405090a061803121a0904030c05011a0f09010b03070c050c0a031a0a2c0307021302040314031e070303181401110c07051018080d030f05 65
    0xa0021441c928810030120460b0368210340100000d9152030a10404000004001c23008035024644140060266102d074501241a03500441078000c80c84003042084140284100e0a0181c5069000301241c802d110f00201640f02d50740400140004108206841d91410b505901c2541100c0040c84050400000e89401c0307005400d20b1041c440300b514043d0304080d2103c15154015440050000030b01c90407d01400d003050809a44102030340340c000c2c8aa00751080105054507815000ca03c110b4031a050140316000e180b0708805481c10034003140d001070a21701903070300107801c2d05030046402d0081c460b00208125007d803118006500d0040c0d00700d00c010340000c803040c0381c58100c00c001ca580001e050003500072405106001031f080e001a0180d1504055802c00309840314070640ca45400c21850300f916100721406c0300416070050042c91328140420200c0c072002200d003820480481010b90200d609403450344050281e090250410110f1076030010121004075440383c90090900e024070001c8644800400c044084d507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 685529154 1250 685527904 685527911
    0x605060418050705040305010c1e02010203041208061912060606050c06010317070803390415110f0c01030c05030601120f0b03240921090f0402040902132304 69
    0x3e0000c1651030b0700881e80083c10365405c1c03203100c90b0205e6006411144880708031948090b02240683e0403070803400104c6000b071040031000410280c10b030040720001c3c3d02902c0100310800c1018600114489c4201c076038458a00624040c400104100c5103000d60005004107250490400841803511680e82c00c040c40013030700460a1110380040403201000301c400043d0406035503550f900b0b0103112502c000c000c00d0000340c44403204490000300d104031074441c8221511410f5540c2d0903d410149541e102d59958107002d401c1c000281d103100941e0b40e00b0322246204800001c05009060091000034055a4012100b40704001080040042507a0040e4017115041c108400010307a2510803011400217000fa1000d81c0d90600c5240c0b0540720040851030106115052080d034488142c8070300c040d465403000c0b40507022140c0200703030222a2440c0d4100021300f4ad400b4000f40180001546503010800f264800d41210380155000103101c120708281d0782541c8000e0801c3c0b1441d0f00c0c001016800088001c000d030101030b104545 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 685530404 1250 685529154 685529161
    0x703081e04050d12021204050313050a05010e010809070306150612060e0c0a020f120705011103070e13110f0301080c1906050c0a140a03021009032a05010501080c04060506041805 78
    0x419174162464800005880c240e02d041900701195aa0003680c900c20002c581981c01043d03d040400c011800c4840c10b8583c440305056100c01500c1d10f0780024400c4101d40b0940200001146c0c03640141503003680007050b854009410000c004250342202c10904810604000d0104002c181c00550300d030307020b000d000106403108240c00d012030804a07202520b946501c110500c0700320b622107510062140138460402001200807800040d207290004403034101c00308100f07020706205030a0042d001611565035610002e200c03480044a42825006800c00c1e0320400c1010005014010003000f0600c008a421180b00302107000048018800c0d07480c50081c00200314001c01c840c0c446000820904801c0ea41c02030328070000a0740301107007513581c44403220309400602c25481100d5a890301c2c1d104071548503400d603440c10160b0340381d0a02030340001840009821720060004035400442c400b8850507020b0002140509104002d100401080e50340e82e410107072240c081008100180111840382d1003a01b207980d000401c80c3d5a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 685531654 1250 685530404 685530437
    0x609010506090d0506070801080f06010e07111903050702010801081603060e100509030d230a11040503030a08091e0a060506040e1903080721110d020703081e04050d 72
    0x2240014080d1007481700b8000c000e81c2001440b03040e0b45c0c03e001198031000500c8845555640288680d0003448038440c0454061441903403183c2da01100c035001c41c0c1e8074084101c174402c000700b134044041d00024000300e2801c0031503a101040c9c500504d8400d00030000c004840940010340e04651100600c0c4030f60310404044001030501140c541c05411200030481c6150800c04940c40e9400340321a5050f092a01d0302008540d80640034809442a01c007032075a4203a590151250700808480341d4220f44a00d06000010707065804100405080000d603484200d00d044c895162031170041c0420030400c0c0341d401030108400d401c8001944000b0650040703400f00d8aa2140004600109070070b4401799001d0048440c01c0303c1c803424842d10710200702d100b562451f0055440700c02c11207610101c01410004142c03174141202054003903030441d010900019420314900505480e960b412030b80011400c0b40410340400402099144092500e003144e25410b1900005103030641c0c68a0700c801d4142c48540a01c02034051011b1040d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 685532904 1250 685531654 685531669
    0xf040507021903051315050a1805101206080c152d0a0806150f0d0f060f0524091009031a0117011b0509220c080f060901050609 56
    0x400788a200e1402c032043e007001401c950110712074540c10040410001141ba410220305001440c00c0da4a503801c2c965411b82c22070700400e0703039135205d0004100710b400440e0b2552000500440500305454940025040200704000d69a041d4001105c0d40c010380d6403600d50340c6a4202e80100d20140d0401c403a51000c010042c40d00c90840e22011a1810102c0c0781d00d20b00d900803020050800031260b403600002650380c0360030400b508424003040c4c14004006d003c000c500305080d8025040803203004901107107118030305082c04110f8206521020312403c03021801c10071800c00100c1c1d441d502c6200303526480100c001000381c003c688160403c2e180500c40518950481c00d2040e00c0344005554031100301a0044a03100c00580c00403428090b104045212100006151405108032031008460b298816080060b0070070070348198119030011742c0c0020024221110600d034a202c40c0348841501440080d070018400783c002d03c900d074020b00c042d68909a0700103201c029901c021183e0b04448007181c03002d0384d0b01100008030348038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 685534154 1250 685532904 685532923
    0x821120103060b011e020a060203091c030c030b09040b0c030c0c01140105040c020607090b09011b0c060215010b0403081e0315100201060320010311040801050f13020f04050702 77
    0x40164a200100c02c21499030041c0308203040c26640d40200342c9807084c00c0d10407182c0c400402e00241e4800c5481d40002000d940203036900080b5141520080c0b085030b149413402032204141840001c0e40c1e2003a461400b9094450714050a030113444806c0c0a01d455a03a064030035034080d041c460010b10210004103202c3d2004211005d03521044020b00880d11405c1403100f5491080c081c051085d400c200e80c0302c900920015280d4803030002d942d15890311500d441c404a5040d8041c42d003181c108618400c40c4043c1c0144242c10303c184610641c620b4003e42d2600c80c0090030b0699040401c0b4241c40100010401c269000c420340c0c083d00d81000d00150b40300d440b4140c01d146104040d816040030100442000825910708140c091140d906950b444032200d4061012800ca42c014000240403000d41880e0880c41e50507104408216001030600140e22108448a007845802961010b08540c3d129820405000309000400e500241503c100000e054010f600007140030f0b00440415004035500c1c4005025540f08101c150003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 685535404 1250 685534154 685534177
    0x307020f0f0a12020f010c0b070f111504230304030303050a060512032a070608091203090f011a01050708090d0b0a060305120a140f0c0105010e18070821 67
    0x28203954441038004601c06200081c0e203e540c0807114405e2650091000d40041e0f82e020102001079034412806a0703003503507000c400100700032400070041103801c001c10851b290659207a20385d61031860649004d0b0188485510038820410039002200b050007000010340d400c0d06d90600b0701003a0355607140980802015150b1203141d02680158141c01c8841001c0010010b845501030300001008102140b451191004401c2e40780350780c02500b0410800744580c1400346c00102c42c84c00d13211380c5456a1048082c036003003699031451541210400c0d98045009216100f150342c01c012040e088a000d140c0043e00d1070080d00d0b005406940000f602e1541603aa8801003000302e940845800b460341480000b410040103580030855651194004058403401c03e8429144030704000c0e520704840251064825182d504140b12242400314180f00296561100380647c1d8041c052501c9940314903c1c0407852034070703c40b5400903602c60f143c0018100740f20820000c0b038141c90020b0a8101104007000100c860111031069550042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 685536654 1250 685535404 685535419
    0x1519020307050702090906010509060f0406050603040302030309190c0608071e020304050114120711190b0712231807030602031b0301060e10030608300c0307020f0f 72
    0x60701c9500400a40303d82402614581d04980d10004146d40d669000e005040d4081e4000c400221540383c40412204012406030010071400d03a2100440ca07190019241100542c1021040001840d8100411f0104900c252018034502074a6180c14003004001d01416080281110008252174001e200420a200c4840714030403444581c103400035240e8000e0b00407140041c0d901440c601201d070050051740c401c0c0b40308101110060300c03122400d88040d40a0020100c4a0007101c1d1608400d49038a00b0062070240200585140c3c0e00d44000c008002c45010b120070000b02d0b00c3e1040464480c0c0390781201e00b26913b0b80c0003410015482d40c2031100440c0e5a8048103441c103104400b0003004111850f00a18028428000c07a070505068166002250703003c00d005481c005008410401c66620704250110b5200e2460304001031550384882c20181424040c458080e19000c1017608000201d410170300061141a411200e141010341070459151244200c61000e4855501811074085607542d01c400301208250041598 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 685537904 1250 685536654 685536661
    0x20d020d0c06030501080304030c0905060f060c0703060b0907021504034803050f09040f0c0e010f05030106021b06042412050f0601050d060f0b0c0601120515190203 72
    0x6074192011800b45200003400e1400014100500206a406032a031006550031541c0c10000b2250080100400700c9601c0000e201c1240216141c24001300700c1c0c880c203c0302030051142541003e00035502c0e034004c007a004901c0c030001c01c0b881a0707003c243c001000c200c15490741c01c180c542e82800c07900f00080c6045118603104032456032041401000c255204081c1800710040041241803411084052100c03002d0301140c000c1100c40c05219480004110301d22000788002021014010301404503241d40310300c5c000ac2100681914125a0428110240c0c11460320b04540f5541c14202c00a441d0401100209040e0801c69542c0c9500d41d0707010300352000b03003122810202000d0700d0b00b10030828030046400e00801007032500005002c0c1c18aa40125449504502140750b034944410004440552081c44498007640e40c504022400c2200590000010b00600b06150744510840c0e4000e814000183c3c4400b4071500c1e1103100320f001072000f20b1141002401507030302a02c550744412560120b9a2244514030304a807000040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 685539154 1250 685537904 685537913
    0x20309030a090b0901172a04030308061210020a02030702040f1d0607020c130f140a0e0303130f05030403050609100509162102060d050603060906040b0f04020d020d 72
    0x941580a6550303128a0b10725541c000f00f40d02c42c46004038860000f04402c545000840d1810310080d00701e081640446804209075244107061a504a0701d5a0100400541002407503885201150001c604940006400b41c0d0341000e01d51315680071a40010168020624040c0389000340103803902103070050400c2c005402d40d1840c4400030450303885100500030794141e4040d11aa00040c2007031240105400900040001d40b0030001400752521803540b10a0310380000410640c1e40e4021f030894040c92201450321810300101c0d084c1564400b000c80c02096006200301b090701c0c800d200610032410b402464604401529003050740c00d510035074001408a1058000f8007069207000500c840c080c1e1000071082000d520b503801d1194480f000c3d0350400c115102c600d1303414032290103854020940c1d465000380001020400c1e0b4082400364015800c00d00045969104206d510b0800713106040d4040c00900141c00c561070103540b01c40031203c000c1d052085c01d61902e8000740440d1214140404a80c0d002854490221420300d072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 685540404 1250 685539154 685539157
    0x9291329010801240305060d06090b090d1701090b042301090b010c02180703061d061f1d0d020a090504020a06111207060b0a0807030c0b0a1209060b030102030903 71
    0x103032900060001000007102c20500c03203c200c2031003030303000b01e6691000c1c20704044001d054003038203a42c2d00480010110001034614800c0030f40d040c1c440d0300030306154034105071280d08280c1c0b400d50500c1408a070440c4400709844245046d4151154403400103440c0c00103d000c203004001443e241c1c01310890500503080c90900803104541220102203080c0034103a500c1d07004660040c03075420000e41100207000c09c01a441c0452064940c07028051a00048003540d514100741d001c00020190700d0000c51400600030a800c0203125010014103206450034903001c0036030014202a80d4010540d194116015098210f036248841c20081d26001060065080d4a46000d08000d1105640c00c034859a900000010024010b5030201083d8000102070840c1c20f50100e810161303035010301c0303044542a5803040c1e40c8505070f8800b094480a401c00b040104105401c40c40c01d003071074007910303040038064a4080c000d8072140da502514042d43c0302c420000120740340c051071605402408080c044968154000310030071142200000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 685541654 1250 685540404 685540481
    0x72d050f0705011803080a0e04020a2a1a04030915120e0d020c060705010f0e15010801020301121103011503080904181a04030215010b0301092913 64
    0x6607841155540019103200100e01c0075801d410008002c02c0000c03420940280034680c0c003034103140301c6854241001408030b90228540c82c0105d10305070303112407103054081083d00c40032440d0320080141400c941c417122141d10328040d00700103807050400042c00305441401840c00824985400005080e801c05c800b5005c41d501d00303402c1c202c1c145826856510803a001a10320011040f94000c1c2c090445107005010340382d4081541035860350b4950a1851809009124290703501190310b028010411550b0351001c1c3d1044180c0c0000c9490780140014005a04e4400c0107400c034542c006c1d05001d51030096800310b4050a84c0e07a5031001c1800c2c030b540f400000d1004030402880e900d003048800300000040500b00d520802d801c500050710340400c0450416112243c0b40c225a0414042c0c01207441002c801c61030018598403d07000803061200c00f0004005529250007403d40d51b20780005901d11500040c0c62107035940303447e4904180704444040d14680800210780c010001d00040001610070318603541d0f100300c400255103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 685542904 1250 685541654 685541683
    0xf0807150c050909060402030a020c0613020907090e0f190e01050a180c0329130510061413020409090614152805130f0b090c072d05 58
    0x7000340722000c2c4202c007210780d1200018002190783d03c074042880003e402c02814018415400c00c103641000204000b940e2041c1d26482030501644101d105019100c40060801d205200310b01c4802d02100301e107820050380c0100400c038090071a82e500c40e00c0c0e60035071050300c20b00b00800c0c4c035100361701e10748a006400881c424805648140940c8221207002d101020454401030f00f810107100c1c0a10000e0302c4000c12115203e58410300b82088511071404568081c0241c5020754041ca038511964100701d0140041c440d1485103e00400c43c1c0c030328007800d00040c400403c544500c155000c224060355014580e0549000d0000070a003040b603804c561400c40000c00310601d00460540e018030000c1c0d00d800b007020031240615400303403040d0700304100488002c0400c25040704403040b00a00f207101080588483d10401440e507100340c40072812800c2862407008540904c01c1ca0340c01044140f04100800e0701050403590320f40c3e0f00c44580e090412444e0302c40400140c2e00a00b6490410b50f618100c4240305001880d410044004c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 685544154 1250 685542904 685542911
    0x9040515091f050a060f0b0304060b04110901030e101109120d0e1002030c0109030323061c02030c0604030812010608040f0f0539040b13090f080715 65
    0x1180341d919a0b81d1002140c8010b054150220391511180e19005113030400640b0707601140c3c00d0b03102c20782c0303600c01c0307105400c83d240080d030200412060101d640164003210000781c400300b003401d2100c1c00c00c04131031081000041c1031540f10f00031502c0d4440100300010414003114410842e400c0c5407080c01a01d13511501c003943c031072101c85204070403000010950301464141a01c0d483d158a071400300344107010a025413044c082d4007081c400e03014000028001c0b410310300d22039a0300141a0140a4030309a442d1112403044184504142c03c120103621440350141c10b0707007243d0030790b5510141d507031000915040e12000b41c0c1d0f070445800305002040012043c09810313689005a80004207a880710b9003128004801c031006080c141040c0305020208007543d03c69501e0034040d070107903080a545011009003402c000d0888400402007003281102c98090881c99038000c0b01e0441301440750403112000548414400b0800c0d6081c195980110402c0290440103c0c80e16548040404d40711031180c01c100ea607200c5038008607111a4207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 685545404 1250 685544154 685544161
    0x50105160204052d160e0303041d10141806030a0c140a0501110703020d0c080d0c0b010f0509010e09030c0d0e0405010b0a0c03030f020c0106090522121b0209040515 72
    0x702030070f1103104680c0c142900c5c148800242c421110005044041d035010b0108100129010406025040c2003c664101055160600c03d19000f801e07480c9a01c0000200c007129501c0e40e0399500d1000e007401d4035600ca2130005440e183d02000900701905000c00412511510f01e0003e003400403450500b00c500e004a414610169030703000192260100405c9100c07880c1c1241d00140014a0007415242100d4010b03604074104c25112102c030b5143c0884201c0050100d400140c5000c10400c0d11000c0a01501000d00103a01c11440c0001090b40c019040c0590b400d005031150019002080c10402d81e1502a01107045030070f813070656400581851001c902143c003030350a100000c0b440c1180362003192032800c11641c03545114803103600c0803401820030740d248644e9641c0801c40e0001080007401900c014001c0240300040c6401c0509240100301140030f03200c3d44640b1042d820a001c110421401c100381280c81c240300090000402003010100b02e480030003035000c2c07a90000e1006001c0d000924107044c3c5102080440c060300c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 685546654 1250 685545404 685545481
    0x12c0906030606090f0c070c08030c0111040803040b1606020f13090c050d0506030a050f1f05010f05011206051c0b0601020a0507050f01052a07061805010516020405 72
    0x181c1101c42c3c3d0382000380d4001144044881d9010b6a901c5161641420704200156843c2060b0740303000e90120125600104005509400a1140485565021205070314003454000070b9a101e00079031040e689104404140c480342d800c1622000001158000800c41d60341111078841481d5070050a44120001e1040801040e250418464410301d011039032075860a100c0c8040f81080601002008181c1600414800b80002401001801c00c402c60f410080c101400040807401c0c80000c240301e8040d582e50826004002c0c6500c10201071058038028a800c03881c4a20662240018041c0760780324580000d0781e592500b9200081240710500f140c49694080d83e02d4560f040126130754020850082c1060700800b00400851620701c1d200c01c46408181030017802d0902c10710390750814503100741010340c0a00c1032601c000d038004000d00098001d080030742881c00c04643d00156410340c901042c018503040c0400051024596580e01f42c4102096038028018000e0b413410040054040c521000444900b1a071810342c2070503038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 685547904 1250 685546654 685546663
    0x40e1006052109030d060303050a020c010c020a030b0912040306060509130b0105040209030a0803040c050a080f031911010c030609060504020906070602030406020c03030405072918012c090603 84
    0x295034640c0c2035003030000030b0349110a6540a012a5018401042450107a11135030042c14020740c041e49400b40c4a200080380641000054083c040c10082110380c00001a03441405040075240c00c03215100403030b0f0762009068601040c000041e240c2400101c0e00104000d15600160103131801911a100291a00780e82a010040d2501004050340c400c00018010303400d0644c007800c0594001002c848001c0b00b81c0c1c6550070581d0082d41d081c0c624102c2101e0501031403e01075021001403060500408091a40400b46612805041401042c0341780908101e201c03140b2a0705104980c44914000300800004000d025005060342c3c0302e5042c64900f00b200000301c5280c01d03c2640c0c211200503200f2441c04032035a903020020341c4000c20848119500740040a9119010000780d032045105a008001c041d0503d18540380b040c0600310112000c1e8120500c0100c0c4900311030984c2c4442c51102d60b542c41180140c40143c501b10950314010b1294210b07807000c10000700e0128424070420340c040e01c5001003612880c09040c2c6a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 685549154 1250 685547904 685547917
    0x319082812060b031f15090e0606031e0912120703050f070c0311120412050606040b0d0f03020709020c070e06030c0a29040b121f0605071403040e100605 67
    0x10300c1001e1000840441c1d9a24410341d400ca0449021721640f900c842d00d11409800750301d101c20000b4502e0109114a072280080282c108400300c0300b8508504d091030032828600303480507103221a40f0051000c140310b4581008004446190b45941d15118601c042008101d07030012912a00040d09110102d0401720400c004540141c40036583d02d00c21500b651825034030020000c90b094075601c20416040d580403103150240000d4900f10700107045a810a041c02072030304d100940b00c42d214500c3c09010140c956901c0e000015202c0c0e1000d0341e903858013494141a4106900b0781e00c940d03180b0380001000c100014010580406540b0b05c2e51400d42c6a4a920b8285541c60040c55000c0d40c1003e241030302840a0a0344010846088844a0683d4840d680d4480d02d140c07607400031351291550040100ba50078548070340400b00d0b42e20400744211420000f14040318190f000800c2e21507e0705100700091200b013072285205045403500440000c590352203580d220000541c0108946203030720100092008134105100d070044608 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 685550404 1250 685549154 685549169
    0x10201140126070b030403020109050f07050a1a0c0a11011403010503030409050903040909030c1118060906130501080d1106072109060f05190b031908281206 69
    0x720128550b404481d6401800403460180f040310300c0040c10801d02c000451040d4400da00210302444980b4100d0303e4044162403100c820340080350240800d81f01d0792854000c5034171040e1501c4070340c070403090101c140384101806950b19008602d240350a0268071034510b18040310a0f40e4a4030311640c000f001d40c2c540d0000307004042e81900104010004808a9008070b50898018000e42e032406039103c0d0000111110004120042000207040300309001011141441102d000c0e981146800e186443d0f0440d8800020b02680c400c0c4041d0001c01c48580b129100c0071808028074108000c203503111100b41e035884000c04032460014900c00109808810042840e6020714990784503c0f00038242d60080307400119400d0110000e1641c1e900544010881900800303010026100d000a51802c2410b481585680c96000044019003000c0002d0500c0c2c0380000c0c90402040c004085101c40c0600746801f107000d1180e080413a20882a89900c0c5101a28550f10004064001e450340510b144c840b003141c5082d2040c9204244 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 685551654 1250 685550404 685550429
    0xf05040c080a0206070b090c030d02010c08010f080a0209090c040f09050607110d0c170a05090915010210180b010f080606091506160c061220031b120f060102011401 72
    0x5c00140400100e54220a00d08140d54580c07580c030b8007081c40e0042d007440383d00050b03440f582d08500c00d50f0810810303030260012503103007845641001660f5966003280c41d0300a01400444e0000b5440035018448907001d60b80042080c8a0144855105c00140001e150251024000e40b004154202d02880a00109050680c00340c15258003604049e110076526010980c0c06030080314103a083c2104040081c42140c609403100307500c440c911820310816610060101c10b5030b101e96400c0f00103a1b81c001490078200340c40c003000440c0309207448290041d091102c8500611010071030002040350355029030b415081c0e68207002200c0f9665181801c11040b214203407414401d040106807604450f003008030060000c200d0f035081e8005600c080e5a070300c0001004a03401000002c9801c058544010594018041d4110400712229450b100c910403044061201418011142200240c20442c2803060f009a610340a0203603040322480c40c0c403810450810b4422541603005500e801740422406030700c50420383c161805000c0c0709 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 685552904 1250 685551654 685551667
    0x30b0301020a080f0403051615051315151503090201080c191d1801170123100b0a030c320307122c07081c120f05040c080a0206 56
    0x41d2001c4e0060400d800f0400108403241e00c1003d42201080f0083c800d00d44015680c0e41000c80e5001c84002401c5d211044106403413640c0400c81283d4058038000e58010700107450f400042a90000a205900c40341d59a0320550801f500b494040c0d100c00d030164000c1c0c03103c2c0e41c255640d01c51211b503440b6400e141c1c00041240d240c0300c0c61451245000ca4101c00b199020b0090703070b80f00a400661002d4100441c1c40c881c3c030540700103006c840d800d082d20301c06540e40b09000303020210910b481895240b980000c00f0341c0190045000441c804040c20850300200540c62070340d80e42d610358000040151811541703840200309100718040721801902d02000c80703a0343e09a80310b0100d01d501e84c807001d1141e2000d0800b00400c80f1100484412164600c685a424480071040c243d43c02480705081c5001c00803181072000e181c005070010080c05c1070200d0044400c04030603045001c1d02112920648030b9491064910b05917038034020049216240c1503110314000c50066a0b01320066036914001a5a4050000c1c025040358060011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 685554154 1250 685552904 685552921
    0x41208011a0901030f05151002031317071805090105150609101808100b01022b0c060e0a0c090227040e1207030324121104110a030b0301020a08 63
    0xb0303020a075014580403c5244d40c2400c244107542090303880c5a41008801580d03050b600c0e0042914200e280180081c40c1098034102942e42082014450b12551003102d800484988405000303e6010780444880041c0380745095070b8039401003000f2106581e0a41c81c040100d55600381000b00d0240140006081500d818008001d1013158010320402e0018400e1a00140191070300444028019162079070080c40100345c00d03034800c001d60b1342d01208581035401207810726103111143c2c40b20402c0c07060002c661b041182c0c00402e0480d002d04014202400c01480d2031458a008840031901840c810f0050390440642600c60501d481244544c144541287c210700030160041040640310b00c84c0014005e000062111058052904080c4103691540360302a00040480c1015011303ca40e240b240309918615210246071009031b00d039010680614000b0844240648041101c490000c1070801d40240c0280700c240c1c40410840e01c1500b1080d241070102c1d05010f8022400e040c14030035100842e142c0d6844800c0c54031003000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 685555404 1250 685554154 685554157
    0x51b0a03031b05120a091a0403030c080c0106091a2211040e040f020111190201030b041b020309032b0f1202030403090f080a030e13060815041208011a 66
    0x410340120249a03030b0703801050091040c40760103108110601d903611280b090090042e600344c0c02c4047e8101150342020100c410a805480540303070701d410311040014650a000700b880c000e00c3d80c1d4094079802c1020115070081c1e15082414440007a10401c55032a00301410080760141604009102003200c40c0c0790074400c09180c1154000d003000081162410f07842e1080320314907400441d42507400d020382c07401401c01c40d64404520b0700c215000402400c6810a080c540c50f00c001c00780e24010303040540300c0d00740510994a071741c80041602d411603c0c180ca02c00c42408040d4481e0004191107119000d025483c1c00c800e00c00c00e4604180381c540c505a420782860104c4c040d520059100403603410010a10301d42c140b6166280300450083d07010303469200020340b1b42055007a041c0e070aa0082080b5400100007000003941100e120503404908030750255120070750705014401444254403070759840c801d0204000444510320009030150340110f06810011003500030640704800c0c03e110f03645111640c4140e000741501d0010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 685556654 1250 685555404 685555427
    0x80601120b010e1201051b0a02030a030c050f0313140a020a030b0421030b041a06070311190b1005220504050106050d0818031b060c1216051b0a0303 65
    0x144078016602072004130b440030404c98107801290399070350705211b101d100c022801031a207010160700a00d41f04130050025100c0c01072030714980c01c0c580c07100f100c04105405201600c0c42500407510b2143c4a103070036407030264055200f03441a134907803115140451403e2808280c1c4801c807500907280390806440d59032510829030b4014030640b2014551150380040044016030700072090001c1d9070120b81405900d00304022140000700350841045550080d0f011178542c1e000b034440740f0303404d4203040347c0812040303803164100315402c50366405030081e021035042084520403010740190342044027100c4503910b440a001150000064500e1001010f6100484040c0c49070803843c6d00034460400403c805580f0004990441041401152194070124440105004010803c4180441203000300041c002d01c02c0000d03045903030101c28500403540054507000720792003000400c0700340e9014500c00355200034040d4104010305400c0400c0710340c2e000b00625200002c030030799501441501c005000268891441d034050b1003803c07500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 685557904 1250 685556654 685556657
    0x2040209090403110d05070c050d0c030c06200c0603041e0b070c02010f03060b03060d020d050d051b0c211c050c07050103022a16091b080601120b01 65
    0x204035015880d114071480034091482629241441070032200364a08229452007040108441071040d90302080c01881901d04642c001e8131141d00200c86400c01c0659a50550005012220b880e84001162580034a144081c9010440e607403500030760f80c516042e1260002c2d21100d50280f002d0000c03c0202e83e4080c8240800088029112401d920b15030301c2d03143c603e40c03c480190107d18108016030075540c0000c10000c907a0454078042040500300404401e06001c080d041300e0082800c0c403000003c54840344040700009030040121102e810300c80d0001401d80e0b001b00111700c916003000714150309882c400034032400381540040c440320000c900c55114100c10345d001c840d480800d12030515004a40512000000000349841c0e032802c1d5510282e004091500c500359105a04151040002c10703129043d00204015400b00c12034022110072a02090720b142480940e001c15031521511400940503c0aa02c41e9140c0140703038405035039010195609868200046900602040c00024000a81e078150f90000c040820f05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 685559154 1250 685557904 685557907
    0xb041502010b3604080a0f080906040314121f0816050603100302120d110703080f0705070510020319080f04020904080d02070b060312070309060827061e01050a05010804020402 77
    0x108807520010f031800b9103041e10480c01c0024030808882e8401d415424601c0d031030a180203d8180a4400e5655000042015080100440c401e5800f2070b00401110010500344c0041210350800607801d2007102a814800035880d1010380700003401080c0480c030716940304249411184002e142005001540e4002003c0c0c009081d801c0b107000c001aa10b903540e640a41e940c550040c00d8140310401d018258118007000d601955010104c10000a10700344d040720340000305d040b001502c40100b443c041e40740100940002c3e61018061441200035a13000000c0c00c8101d0140440d034500c951070340c0007941c20300350a42d0240c01020440c4c0c001005410000b05460708203108541d01c42c0f622059070302c00400c0740c1045a040ba0b4101f18442840414070f8100480460160440d40e01c603d00140c6d83d070040d044d0852403007100709200c28540015200a140800c858510151251481c0d42075815854580c5900003142d100c09000035201d1100012840014007a06070b03000032306032800681c1080d00541e0b483c0001002264403d80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 685560404 1250 685559154 685559239
    0x1027060f1401080c090a031b090501121208010501050307030c0c0203030d15090209060a20070329220f08070c17010c02101e05010b041502010b 63
    0xc0c500050001800310450340801104503000040a40310b01400c404001d03542800301070281da590010380c0302140d0340704120540301110f6445104d03040c82d156100c8445149018000205200381001107881c26108150210b01130040c044140c6d0710348d200717000d100e000441c140000340746640030307920005002c1d40c50f044c4140c820307c82d680020704e5030744000300115a454503105810b284d03400b89200e107809000311400035428110284042020360041400050802c20102c2c00418180c007090004441c1c1d00c11407059428407610390404403012800261b0200c1016074141e9202c200c0d03050702c035030540202c145a07401e13840000d519415000c1440013010030b0f5003440c800100b0f03200040c14500181030303851003941d102a00e140780641160400041804001c0075906080305544401c2e408280707201c80d900c7c0301e2000078000410b190141c2c201c410210030804921f19140000c280000580050412140c42d040120705e408003201040b070030b0320b403503201c100d401411015103003004110480c4260450320035102484610300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 685561654 1250 685560404 685560419
    0x106261b07061506090509090622050604081c0b030717030c010e070905070810030816080a27180c0c02030a03030207020a0e0603031e090a060206010e102706 69
    0xa9040e5040181c00f01005410480c0c41c1c0c10001c194021706048030141d99500d08603041ca0707102c803130080242604505003802000c0300c05442e010902801d402404a0300b81c0e281174508016154410031400380c0f134002c44c070031540200d29140614144454054050031505180ca100c00350400050350310b6000e40d0000340000b2070514424400c0f001412440345c01044414074004001b0101c4c4d02c0540440100324103a1704005c1111a04113860085950001a02c1d43e0782140a81e4104405400f0304000d0520000143c03480b41164489008412120303051034034605003070180a45448403016101e0303403106069400010202c805640e0200d19445024141030392059050750000e03040c100c001100301c002c25400b16040e400e5061070000c28001d03220300c8484a9843c200003000a03600d0003008202203c42040c00c2211101145200c19031b401c010000c0c102000f040c0e20f5581c040e4940000340603180404d280000050b4020412580200480c0c20082d850804603009140305804420f0091402810315140c440005102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 685562904 1250 685561654 685561661
    0x623031302090c04330e060406050702030c061c050609070219062c0f07030816032703140d17091c120c030b0901140409080705060106261b0706 63
    0x1510180c00000b0082411100785c9030b8601d0804600c1c100040e0414041d1151104030403a0142c4440d070500503240c01d45440024a0140c2228a494210b80b01252030042c4400300340c0040c50404881c081805a9640d07034040c071000e20001c03034095005038400c4502094203608551340e00b2070f2600840b0081743c0054000415908207003000000d5080540085401c0769000003840320088280c0e00703902400190b440d50310341448600881c0040145401c00e031500c04101401000c1c40c82140c0714607405081c00103190701d800001010f0600c41620001004400d00d00c0b00350010465000c19800d07520303511502c0300851441e006014004012445d00d10866030444244003840c100f845030f0415503902d560451304c0c403500c0702d82942d8800f2402014542400e01150945d41c0b215034160540e0304903405002ca40b40520300080160100b1100075000c001c0014042c2c0078850081503290580d2041d844203c0410703a03801100395500c001c00c403002c0c140c0c180e030b42c04074007040a02c114101007018401c204031704040554440030103c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 685564154 1250 685562904 685562939
    0xb010c0b0112061d0f16030b0f0c120108030a0e031219020a050f010f140709030303051003080d09020f0a1202060d0f0513020f300a05070623031302090c04 68
    0x85600072243c1d0b03c41710310200700c01c00c84642d80107036070040c40b0303d140e0f80c458a00c207000e01500c000d10001c00014055020315029140c150f00705a0f111246543d540d25442c1d1250b101614000000304501e618148508001500020040e000c1184514114805c030401002240d0402d8850843c020003002d0300205a007000f0141a625264000003101402c04c1003080031180142401480d00301c03007200700f001c1c3d10740052a01040b41d40500b801728003030359555000b44038215940c1004204036400f20368000c808801d9070000303100c2c1e44240e030001c20142ca0b9008000105405d8821100581828a051401820301c4005460410412300c8049001c0182c8901e40d0292081166a030520b000207181c28030031340ca030000d0002ca4400302510501d4240c442003503d60b031103803907a01c120003281c5c0581022071000c0b142000b200300c030780b82c0003001c0e540050384400d13004041c00f6441e1511102d084101d50013002d00310b6014110f80c015409420200075410303075036080c4071489000610b6031504007810700c0009108490528403211 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 685565404 1250 685564154 685564211
    0x10020c120a0509041802010806040506041d0f06011a04170c13051509090c010e190314060108030a05070b040201170a20030103021507150c030b01030b010c0b011206 72
    0x3220640d4005000484801d04c0e005c0a80344628600c0d800503036000420250000415500440d16680740e402040107000840302c000104280241548010360703010402c440c1c50032205090f2041d590b680d00505141820003e020b441e07003841007004026074020039110343e144028032400e540380c490100f000074403100742d16203204000c181c0311010003103400c008907203e10068000301c03070b60b40e201e0601c6020280d9a00078940c0181c103201e2134501802c0310751755060a0b0610381032121001c1e00015103a2801c05a42110303035003492994403410001180480300402910141040703a03480c54200507203610340401141d405441a07050007685403a0620100401080758400d030105100469aa010460228101d00c9005005442c1c2441400140016511402c4502c0c44040003800b03d80c84c0d182070b040500700d502e103205151a5251800829685e20307a0940c200c00c20081c0240c0b81041504101c40040d02c00c04651007008018582590040c48603102c8071904100b0341d4000c4000003610b400c500e2514000202c1c2d20300031078 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 685566654 1250 685565404 685565407
    0xe0711060a09142802010203160606050108010b03040f0b07050c07030305041d390a0e13091104051306020f040e06061204020d210903050d090810020c120a05 69
    0x806204071501e82e501084021002001030b0a420044d0410202a001c0c41150000c650100d10b025a0700c20000d0b50046500202d03100100e80682c80d14030000c10462148a021030130311030002842005c03081c19640305640241c0c48841000003a03590820101c00107100c141441414403184a406404005250166202e07480e00b6136110f0a00c2241050004804003c10b002c83c418010032031949180d04041e80c0c481d0146100350170031240300c00200c9003281d0190310f000d0101b030042104000f903a80881d00e04d035145801c1d50442485d0f10740041c00402e985c5100b0000e812404002e50120b0103042c203074403065000c500d403072040e010952280e03542030681c0d00c01c211030403080102040c14800640f104100980140c000c90311035203010001c8000d10500e05006002034880c102c043d51000030b0081846060a10504c1c07012401c203980c104840250070100c081c042580c4a10600040805442c01480c610702610b80040040c040c3d00309651890002c0d5000c1c04072481c10340140245d400044050502404e00c01c000ea40750705 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 685567904 1250 685566654 685566671
    0xc08071410020702030705041104031a1b12070c0309090908030610090509040f021f0c0308070516152003070e0f210a080301080313080c03070e0711060a 67
    0xc0c40c166160795080995841007101c0e900503a8005804411030b038007500d005c209110702000d621814012907001030948401e150030285403001c088043c51155103040881c4040d4072112014246a000c1d800e0003a8400540c080414000380c010790311490180d01ca490312401d413030749561154042d25690042110001c1012060090790301c2d00c2500202404058582406014a40350002d0300708140508090014070650703107164250340350400c850110380b0641c50000071300c1310b40c2040104105407040080d0300007090900481c82c0317030384a00d0844103200412141203540ea81d06403075015403c00c040c202c58207082e036120300704509811010151030070b004100c812075031a481c0c0988060f0814a40300d08a0f032182c1088048405641d440395809000e1840008041640c80c6808040c50f190288a43c0080c2403540040000038007610000010203450300c13100c246290f000d41d01c01145036a481e00201503545900402403e00000d920400040d03032005080ca0f10000c0560a50035841c14594140c508400d8203880d01c0d4203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 685569154 1250 685567904 685567943
    0x132003010b090708010b0c030d09080a020c040b0a091e09061b0c05070b1b070305100f27031701030302060f09030306030619060308041205151b0a0c0807 67
    0x140107000300c041d103484115103440b900c018808a414090b100f40ba40e000301b22403809181c200240d80805003001c1c000c001d9801c450401d42016009540c1e500014410200c5841c41c90801e801445110303100070b00b01910302810042c43c41301400202c24000807400451751488100842c5000d0185d01d14060000040c510240c4443c2c01114110f007416070b4103021420454100040001495034116128100da80d9100c041042111840c0c103100071140f0702a2255040c0403040c03040118130007101c290b00030010889441c0802680c0182c454600b850540700074120000d000c21040f034075001c1070092007881c0c4005100c104001d20404010281c000f0340040c0e00a000300305402500074281c6400103090001136045250050003e56982c00082c0f49500082d0003031034070203a80300d40c1e41000300519032204c17085403283c3d1555002c5181600d2001c1c2541e541c07051103074101a01848600460161081185034030307500c41030f4882c02d05c4540c450350080c0200400b40c007413000400c4d2028086c1c6240340c890071180052002d04440d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 685570404 1250 685569154 685569161
    0x3100911010f05030705070320150603060603010b0d08030a0b1008010603110313020111010e0111032d0f06030c060304080a022e0f06151107090515040513200301 71
    0x80e040c09000f010024080810f401209552000307a2510300900c0700c2c8000030040f580310030120b854414521860001008158101d8900d901c0751a0907011140300340c0c1c502080500f603c9403000e500b5004038100b00a80c0101d0301031001075501036418440880d400b410103001c10364103001d040c03044001600c42e000501100d50701d0701440d0411051000c0290460601041447c049444260000c1c1400f04800e01e0325050502034000c0d50400080c0002041b940d00011610310299008071882c40700d224101040c1002c100d6240d0700d8401200700e0f203a9110322503445070354039600304201400e02d80d03161254140800d00c030755404004521a51040b029283c480c0c00106001c0e1801030300130007450044103c9041c41078060002a00c4030700241c0f0440000c50004840500d50000f0103080e001014443e40a4182d904815041614a450540c100342203a115954908041003120001e81c0c0c00300c007041d600d4410b283c0e189000e0f04400d4208600384a8400da005181d41c601051001c03107a050410702c0c0001c030344640103190070301c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 685571654 1250 685570404 685570427
    0x111612051005012417070f020c0603161209020301060303050a1107080d12020d230c0309060a0911130e0705060708030403030c020a0b091018150b0310091101 69
    0x4040c0640c0d4184102d0b010311301400d200c02c40d402c05203081016a064818a41d4444400c40d4411040d070314200310100415a52840e0031090161246800c0c5410f6820240b00316441a558415120384d80440c500c01252480342209001d15900d898120000240c0c2d42845101c008500c0b035180c0f50307991065400d0260180c9100c0400ba007040e0441502000214404500c0107400802450000d00e0140e0720100c9400034000c52610003d2107140c01c107040bc8802c000d8503841031641b0b5000324031651344d64103448a0b43d94401143c608400340c00c11000f00d4840e0543e9003024070304620070a0514800071000001c14003050341d11081071201502c1d41c80341c0d41e80840c2031051402038a800d1b1401d900c1c1400701c1d240c1d83c08030321014200a0070180d5506442d558940b0a002541e035013a40010816682d00b4001b1429603201441000c000b02146840c2c4012043d95825043d481203503444980c0c06241c9607801940d900408841801e190036008410284640210314407d180c0e680e4425000c070800c41600000042c240c40207103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 685572904 1250 685571654 685571683
    0x30709290303070c050f0d05100506030c100903110a0905090601050a08030a02060c0c120f07020a060e01170403050405060c010f0606050301030b130203100906050702060705040605040611161205 85
    0x40011102142c030750344021061791003d950381100c5603151008660081c0400c68090440e005580743d0300b80303016458001c1c4c0c0c001d43e0110704849604120038208811840c50103610b2021551205007040018903503c05860b503148020515444c440d66807030b126054070001c641b41c54080c0c100c0030040c442c5240c900340c10f41c00f5041f0180118206071080384007035a40d070310140c210420284040380503001004200304030070070b94084107003058889500d51800d10705504071a030224460740002d08003182e075a110384111118580141d4650005a880c0302c000d03480300c0381c0600b050f000c0000400010a182d1200c00042102d0345e629000080d005207021f041e6011188070b500400304104080004001080003041304903005000c4003102240d610003440024030340b2503a030b209240080d041050a03411701642c1c1c6d00644c41050103400b80c80695075100021a40c600c120700400303001ca6401d1009120592107a400340704503404071800c071240301441c00c1410306c101100ba440005008540136603902000f1040c4940070700c103084c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 685574154 1250 685572904 685572907
    0x91f15080f030d0f0e03040810110f04060f0e0a170106080d020c100c050624090115050c07050916021b01170c160b01140d20030709290303 61
    0xa00240342d80341c0c41142201441251039840304901d052160b4451012482c036441102d81c2c8a550f00c0c40183ca1303d5001414200d0716281c6104050352641440858900b050304100c01c614141c2441c0f4143e0743c0e00814040c00c010090103054000c2c0c00e4481403003c0c4050075080c0c8241d501d090000d40b40c03e00b0741e4855000042660020310050541680005006901e040700301c8a8030810741e590b0200b291545074148001e0701910450007440228100007680d01c4001c0c0c405404c00c104a155003062000f004400e101e940341e0003208241036181b02d88200043c10381c0715550410307105407a5840d00000c1ca20b030030a42d03800c420907200c00559208a0780410245010511000004140b441c1040020303000c4901e2180340d104c031220640c0095075900000040341c0c03001600039009811864642000103200200340120031801003c44100c40180c40c18440c049500c5500001d440303004c50500d0040c403110b815800c6440c1d05481170200106603240680a9050005800c43c84801c01d681c185070740280340d80d10308a41e0f901a810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 685575404 1250 685574154 685574173
    0x200c0d030902030c0d051f230415050a020708030a05060f190e18240601050403150e010209030318010305060132130e0406050c03090303040b091f1508 66
    0x43c0410404000801290b4500d240101e500b051410500300c586102000f03101d4450000007690745602406690341ca044001e0760501d85042c1d609035446040d00c0162414010490194612203543c02140d880038a040006d42002510380d500141c03900700340d440c1c20f4034030344030b208210f01414102025503212170308491030501c054600454250300303102809207a4043d500741000035006500c883c41201110141021102d50014141d6066040300014040004004a0102107880c6600c24000e58041e00d400c03600300039900c140c0b245540000e000c510881c0c4607a540910104091f07a0342880036208149841ea84000540c0922000400300c5030018119818441c402403c00d103d120010114010303440d0b641c03190100e20240b41801c0d2000c0c0a0030b800e55584401294000c1014094412142d000e1440fa1500f0300685e00c03250b880740c00350b000c103c4405191307500c18000900420707011810250070400da4003e0741c909070b28080012002810721202c0031074040e22901c400c0b1130f45103100900002425400040e203800d04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 685576654 1250 685575404 685575409
    0x270921030609060a122d12111b04090c05031e010506040c0503040b04020f12070303090b1914070813030b0a0c02030405040b030c030a14070f03020604050112200c0d030902 75
    0x642d505c0d00030300f05221800010089000c50a101c5090300580349281340002007a01d40001801920314400c0005643c5880402264200080c00b501d0010740220903a0007000076018000100303000401a10100c039003403000a0641ca060103081220380d002d50b002140780411940c82802d64030040c1141d0700551034407554052460f4417205032a0050b501800c6680c2941fa1400025100f40c000080164040c8442c8a1100c0079480002c0c518122131194444038549952800c280d03200c0c2c0201113007240700c0d0003846280c442c1c040c842c2072150584412001542d040c04074070346411070141c000e11649403c00c50320751801d0041c4400d289400c0d500207041c24041c0421f8400c100000d480b4051440b803107010380d403511400380d03441d0f4042c00007209002000d03048919450450070087c50901c0200800705940c083c494000c203d0102c0d100000742a41e4014184034500b5260000444804081003622a0002d40e50610402426105030082c195064514121504c510316003582500b001180f41c200300a05151207444001038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 685577904 1250 685576654 685576679
    0x10c020d080f040f020f03120d0c02120910050d05010b070614070909020901021203040f060507080c0a05090a031209030201090603090c0b030c1306020f0c270921030609060a 76
    0x7503441440302c48805130707500c0401c03042c4100c90b102c01c0e414014090011f004404810141645504149060021099814040c0d8440903407010380010108108002420ba081000941da0320b0a501d140040c0341c02c01c4100102c04944080c0c20100c042e042c000307411024044c043c0181e15402e41a0b4242182d107051080e0003074102d1290744102d0303842ca60080750641550f802400342203c1c0032a00044503136a13240c1072405400002d0030342d20440d01e884c07500021490003407141003a40d20840f0400400ca1504049010075169a080002c40c1940440c0809010001034154100000c8022903503e40c01501401d40c0300241c402c2400b900603400f0941346c1400a404502c40400c040b044690103603403d5665219807103800302900c10003401786211241c01c1d02c00142140e002074050403036913180d4252002c0c06103500c104045640c9014503e4410031020300c1c0104894100f00c00c5c00d403c500381e00116101401c411003a40b200c0e0f00e5000c80c680e800c04011007041064180045429404078080354010051420952480a039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 685579154 1250 685577904 685577911
    0x108070c03020f01090b18060f04030804050c060d05040b091603020603060a03020613060908010b10030e2e0605060a0f0804030c06020d06091d1b180108010c020d080f 73
    0x40001100521051600070b1200c1a803c411100c02403101c0c1e0500d0400d18031304001030f9240359011220f00c8421070342c503a0103d81d25003c5c120786d1400c00d1340303a02ca540b421910040f0180081e68640030b03141849030103503903640051004041c5400041600d15043c00e10158072640203044098503000031070300301403ca072848106419a981210801d4603600c0f03480104515854a4200940009d0001004031200c030004e0b106204603112076840480c6540c82d18900760982d01400b0f102d81d0058408490540703103e0089d08540c10b490701003400c442c3e01c3c03044000c0948243c40d8040c20341a94400d4071030000c4013000d2601807040900810b0711100d2038285103d000902d0b445942d01040c00308401d107070105040621401c2c1160382650803c0056403596140020a40107050ba0301c00c03040c0151800074030305050400c3c0b04801c1c0c070300b042180180c0f0301501d51403103811000b0350702410b60790301007400b261004a00500c002107034041e04266000040318910040c002e0320f0079800132402000d00900d082002220307a4440e5a0552 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 685580404 1250 685579154 685579157
    0xe0d0302060a110c0703060e0714011205041e0c06030e0a08180105070614010501081f050402090607140607180308030a020d020708070515060d0201020c12070f0b04080105070e010807 80
    0x30203c491880f000018020f11000c03a21078001c0c0b080010074406036422006208c0d110780c09540c0050b90b00d41500c545807809041d00c50100e94034042d40140a1032a501c2281d02a00850202c5103903081c1d88440300c1c0a2004c10300454072400c3d02c1c04203200269040c815101811010350062540d5880d6072504100360181c000d5075100304603640c2241c1c510340d100d401504c070034962000e428011861505952030200400f405900e000541d40d20000b0444c4040c20018210440701107560394000e428001400040c1d0311018501d0f8010780f041103084005419542e8640244000304042d081c40e0822150081c000b00c2c075a40c0c1581c880250720418004030720180d0480380c019880940043e43d031140010b840020b4061035030064071303603030000c5030031340c1881404140310b0b914900c4c05020752034a5881d54200500407050400190060b4811040c030034039400e280002d011001c2c1c60204840c0c403242e4410748200c0749910b0380c03c000b4140c900800d00300b1000109000d0241c1080a9050899050410200090807078400825100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 685581654 1250 685580404 685580411
    0xa110a050f07020301060506030a0501031502030c090d0201090506070c08100203100e060d2001020c040e030f1b0f0f0f0d0c080732070527040c0509040308070e0d0302060a 75
    0x800f1580c4c00d501c60320060030003400440e164540005c40e00010542480143c40343c00d1150200d6030b00c60154401c491064003038210050401120805000d4003100300c5a049041c07015004000c0b031a0355508005c0c003d0603104120f44c1c513091b811300303900b1410040c000309075458a86c0107205021984404000d045c040e9000b00d01c07040c05c2030395082d0000f0112400410003a00c141ca81141058102c030404228001d0354000ba02101c8000311031000340070448149251004254100b80f155041c0503840c1b4009001f0b4850031103032030030085954011355050040d158031062256101408041c1032007002e0252481200304d280107018100b811183c050560000c909000700303842c130001f62503410040c00c0c4902a00111980925641d5241d0351300089080c0540398501054070702c0b0f5104009080e14004444400141a05040260200d0380080d0b10110341781c0904100c41d02007061402051740c0e00c0b40180284102d001e90381d881007605110202410300c10f50390090f05d020b181c0755000301000c66000143c441d00400303001c2000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 685582904 1250 685581654 685581667
    0xd0b1f230d0f0b0c190806040510240c050d02010203060a140f0f01020a060504060e0f120f0304170706090c05061905180405040f020312030f060103020d020c060f0a110a050f 76
    0x4c0d038041c45440d01c146203803a10081c040060941c03099182e480b6440070f4a04110584620307060310b184440034462010b4108c8102d6525460108441011961082038102811000c4290ba600b030308008038080c0890041c0c0d408400c0201074906820388a004010003150028188030520100300380c698002c140c14017904800c003100e407171030b442000b90018181d04000c007046079003043e1078042d0291014840c10684d41c801d050306074810309004981031051391000e0401c0391034900100307080b19541d0030050050b201d0300000000b61220504035801070031403911a2000154545c01498005154000e5801140c000d031020f00ca0f80c206181d44500e244400015410181d856400700b0860003e244030041d45203420904100912041107400d40d95144454400c03800d49260b4400c0c014107006900003201c1405c8145154804604154080d5000340340ca40007241c0c02510780b0540c61025441d00000350759030101d070301c02d5104200f12910280715180c550a0f1040380c0501e4902d24010052460044a546100501300001d02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 685584154 1250 685582904 685582921
    0x809100203041e06060602120c0a0f080708030103081201090912030914120d05060402030f010b030903190f0f0306052d040603030c050607020a020d0b1f230d0f0b 71
    0x451903002c5611105800c2502880d0100c080c0010781b00d0a009441107503240f595018000050701e080712006c000402850640f40c5485540c44c401901c02d8800081c00c12035040130501d8040290301850103207404e955203814130700302c00c540308005a101903952031804140ca0000750812280380d020350f00c00d00c1c000c20019014203200903040c2000c81c0300384151041c030744100030241c0b100c40900266600020300308803e507540400e00c0140d10007294030390240b4080710014401006210040c50f000000c107070880303080c4034140100707505034440d8070716507404a0400320b9034000540d804140854522030300c0c5418003090780b400010030180c0013461111a4000b41130851040a103140d104182c00f4000024414800346580741000b42098499903416a11401031000052950f03000180440d003060740a4445100d640072034498000b80580a032644508aa594000e00401422920358074051700d101911513601d44065980b828401080729020b50003003a003442c2c00c80214505a2072800d420790450000030032070f03403440403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 685585404 1250 685584154 685584173
    0x6013203030d060603110313080a11071d0a270302190606050913020d0b060102010b0a14010207141c0201090806190e06130201050d18060516080910020304 68
    0x52a415100c041204119081280c01c410125025600d00300001440807400301494030003103650703054500d100c1a401e40010500401880c2e040480c1c43e0a2960503e0750001034207040d510303070180d2100e6804654000c407640c000509140c01c1011481c1c2007200708a041d00444100554182c1040004150080c1c001454020b01940542c810307902540c0450340c3d141d16003a40100140d0107600c0c010b040c02e00c0000c48450700306000e04c4502c1d0b0010054002003803140c1d81c06c20400c500170880e03811035499840cac0002030745425040001070300710a040400c1d9030014000081c074001d0154490308205a200d1024021900c0c0c40344481c00c0d404103c40341c0031124002e8001660110345035401441140306210400948030481c8003891040440b603030342400080200003025684800940e460f0000d8542d2086100040d03004d80700038420b11088100218560b00c0d046002581c00360046420341d81580c88008003d1000c4a041d81c0201010150030001884c0c209003422554443c4644213400d401c1d540000401c051101c40d08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 685586654 1250 685585404 685585499
    0xf0c0f061b01020318121c0204091406130606081602010e1203061305060102032d0c01050a0509060106090306020a05041a071721040c0503060408130501020601 70
    0x9050002412500d80a14004e6200b29040406052408014039160602190586240e88821440350409045000c80c403094203020000e100c11940c200700000300441180144002c0010024000d251480e00ca4180400b0010345028181102c2c6030410030700c000c58001d411207400c00f0040009868125400307009030b0050201e000900000e02c20706a0345007150900c00003c0d48604020340d080b100714183ca07407120041e2078040ea00c0c2c90168006004020502e500c404600d45d501c0031684032121456104080111180d0060401c0d0f10180d444004001d50034080d8058140c00c030104074001c20351903241200082080038240001040300d5000503000484501c46d1054034007130135000703140c5403c1e0340c519030002400d030340803040c121400d107440780d60801481c0c003003015a0003041181e100e003100019401e81c0100c0121008108031090140840702146941342001018422031180303c40941c1d134200303418500c00100c9564000b904551105c001404146d04c403110710b21940c500303900501800307021001113640a00c0040f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 685587904 1250 685586654 685586677
    0x307060c0f0b0f040c0605040b040501030e1c03020702090603031603113315011b2406030203120f0d05060d0b040305041503021819170c10020f0c0f06 66
    0x5a09020f10b000d0fa80322014001c03449a00c64a040035500d01c425100c901803841042c920110600040100d540690045100408d4400613290580d81d008848004a00c5444400300000e60108404c03003141400c403030980c2c000c10114003d60911840400c0141064004140101001003c283c06075a440c010000d2005c40e01c4650100c80e203820300c011a109070342e20614504140b00c0d103140003240c119403100d810305415070300607500e46a100c4290074900c000c2622562084851400310b060700003d50b040180410000700e00c1150110f101840d41c01010300d062071402e50340401560401c101c0c00c80c441e400e011101046c408010200341036a641c00010726034a03050002625240c800c00c1000105503102d00100103507500c2c1c8010001c000074140c0e04070202d01031711501d09100a0141e03d0415589014a0011a1808012101c191071034540380742103450b10180d104201184d115920100c09443d0420700c0e05090a082d200034199000042c01541d586c0c858401214000d0742c4404002e2101d4450104803004400c40e03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 685589154 1250 685587904 685587923
    0xa050712020d0e06030601140306010918151d01050415091d010c030905061f2102011b111905060708090f01020313180204120b0601030f02090307060c0f 67
    0x400c0800394560b01c0e000c4507200050302c0c0710381c2805180707480700540340940c806950b01c0d00111040c0e00400410741c03024004a0500018101c0040d000a0201700e4128440c5041c4012802d1441d40c240d88800c2800c0d60406400f80300c01035403104110700c001d104181181c10440380840c1080340f1080111601c10540c000d405001c1c00c00c203400c17100d110006030a1403011000d8008215200c1c0c1984110100c4600701002800c0d40c01c9100418124403141394203501c0c205454403070b003442c26038a03a01c85111120904e0034031061507074000e0700c03004d40d80c00a0303000c9101c1c0080c0341081070103004c9540700c034603c0c1131442030980b18000386040701c50071000000e4190054007010307164580e0343c00b20b0304141e80da5800042e481441a40c610101d0305181d4408000d80f0143d0a80000260410303090070321854006c0c282009400819500b070000140c0d08401c90400343e5184d00420b501211400c01c00001029280c074444403060302c40c010480c4002c96100040c000c02110243d10f440c0c81c0d41141450716440c0003a2a03040a02003460 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 685590404 1250 685589154 685589183
    0x7020f120a020f0301060602030a0e1f02060103120915051c0513060b040c08070c03020a05060a060e131e020d0602030108030a0f0e030c041d0a0308160e150a0507 71
    0x1400c07007066008691406101240404150a880507401102c0058105110a541d100d000d0480410452401003542401401ca20000c200700ba03000d481c06001a40881d0041082c450045401c1221030001c0c0783c03103429107051903852040b006185020008115000460f5814040311074a28408151500303400d1101d400c001c1c08408a1084105041c0d6a1600d048030b202400c6c13400e0b11800e0a00404da440b0100c40790340c0d9100c291a103480c5540d0039010f600403210010700048040c400c480c8110780e0307003900041c40d90600300d91034200e81000780404800d440746d6030072002052440f10200baa440c40e5000200802d18640b0226080704d00009c03004243c903001000100d540311010010b02401c44482d07032110b00c16000018212841c00d0750041150b050f810101106549007001e400c00714250060404c44402c0c0d0220780c5049107083c1d148242600042c8100050112161108502c0c00700294a4a030420f840c0b0711042c0050381d001808a10404510000208611040e002e02e040d554415000f8005404444 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 685591654 1250 685590404 685590439
    0x1409010518010504151e0507033e1c0204080c03060c03041a060402090d0303090308090703081b0a05120301080105010b03040f020d1b1211100f0507020f 67
    0x401070303819811040038044140044403051040e148516080303001c0b5044441d01e000280010415118804541711102c550a5010b0105019250050f8495540081d08401c0508008100584210050038031f038091b1440c00c501c40030806403030441d09103404000d81d4511900c20301000e030400380c040107080140089400030f01d03c078003c140d07018507003010740541d03510340e850f00701d14a810f12044030020f00000040507443c0c1d410001702d80999200001034001481c0040a900040a0030080380c811000252904082e404150344490510340003000c0c1c60041162504542d2002c43c40c1c050b294100081e040b1840c6c58034040b1008000c0f25000a802009680f0500100900686968000d00030034010350b09000002520442050403603100c0c0350018112040340035150308102c0340413440c0c04261100484d001c3c080902c1d81106420500800e40d407004601c4841080c1b03065828020318500481c82003604540c0c0389081604100141c80b403c071075241465aa00340d40c4005001010326242c00b9400ca44616000341c0400c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 685592904 1250 685591654 685591661
    0x40c0323010f06080708010b07030203070804180e01051b030619030b01060801080d0e041a0402040f14040b01090302100507120801050102101505010c06020403050628150b070501140901 81
    0x280c00300001400e1140d26003c043e1078042e4203642d503400061000c001000024a214040c0240520900c10b03249052510b455122040d045034010140c2040e080c0b42e404400400c61050210b0404218028030007454004002c01c0c481286031030a80b16500000b0000702d0702d40c1e03240d4004038044036030303403052040b04c1d204d050620720043d090203144d000c00ca1040010811041c0040d120800c1003866a9902a000c444001e01c4042c00f02140d070070f24805502240451240e03520f001800c0904070302d852001d01340340703407541c03000c016020b10b892680503500d003031407010942c3d9010041d04281c0342c0540b2608200039003801c04036190320070003030041c042c4143c040028440a40c8104400c0c101c44d000d80c21540c07a4030080040d0760444040340b480002161410200f0801540500c00003240325004500060405580c2c1d12424106002221100c4400c0011003208000c42c880d1001035003448002c0c0c0041002540803040300f0122541400f80d400a07040c04200102082025088012212908014101030b400c0c0881c0d224042c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 685594154 1250 685592904 685592909
    0x60603090209130f02131e0b0102010b04091104021b030723150f100803040308190809060f18030c010501150f0e060306190308030402040b090103050c040c032301 71
    0x2d204880c0c0070900c0071080e801003ea80c150421015000451030f982004081d10181c0a400c0826885640c03500701d40c2c40303d0707101c1081ea550000c000b040c00000380000a0071150b200c2d84d0203101d10720740304d800008034564206040c400981074030b00507030384c014100640710400004080310b01c051100003501001c100000420000740d40d0041c04020170360135140c10482e1600d40c40000161000c2c2c1d180c00180507a03110802d83c03500704844450115200d511942d4440c2580c1c482c0c0c00580b551a800078802d03524000d22480104010140e207454001418001c01c89500d560340501500c00c021034500104541011280380c800030100d0403000c40742d0700c0c024202c4583c0072f003400740b1408008070614000f2003461030046a810352004255550910200307900c4d0300304400d0743c102401094010012129548403a011013201d100610b002e05c0942d616482d25104102c2510f18803071104d405a52043c00400001da40014101120b06085a01040380419072504400030402c11110321000300100055010180151100506 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 685595404 1250 685594154 685594159
    0x141f050d0c030209070503010501020316020a0b0c01061403030c0a0609170723010c20070e04080318031809060d020306161e321206010e0909060106050c07090606030902 74
    0xf4617034580c1d0094425000910a09000d81c00405c01081c0c0c0000002e0a07040c4d10f803000705000502501c0c1c00385800103411036114a0324036903540105004040c1140c1403840c3c1c000c01140123518141007001c1260300c03190007500003014591038440c450300b003000203610514010a4100e40079182c80741814005003072554580400b800c083da100da5410326140c180600c0c030790b20000c0e454850303036021009002e8158440d0b54441d00868000d0110101d071001c0c8581c0c00f180101e008078000b5440b4180080c15400410680504400e181c0c401c200312100c40300f019101c0a088402280c49080710303951540031442013060094001d5042c041c403c00c1100e10480c81d69a000c02c6803445e900c04140d0040f00d240b24202c03a13868004100490540821200a21412101d100070b4100020340c4032800300d940750664030786400c00d1014100c10100c82c8200582075070701491081a5013030440b110212400c1c105a8140c0350768041c0212070400a0000310803602c4501000440010040c18900b0060199250001001040031040491 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 685596654 1250 685595404 685595419
    0x10b03010203070f1e091e03020409050c0307080d09231203030a060e040f02090c0d2d0c0806010e0609030304090212100e061309052d01141f050d0c0302 67
    0x40200c0007030f000e06a1700c0c841515030503a00c6040030100810300b01118042070b0400c04900c3c0100050300c40b8020109558030607001007050302d0b214030800d4249405500010150b07030040c3e003032031211580305051104440742001d019804099595110314082500c0386842e81001e42200341c24400140000114072030f40040d00204140c94440c450080e00407020389001d4642d100d210505009840c1184929820010004520707141c88641c0c80d8034030a40e0710400809041140300000340341411501d0100c2e40c031380f00701d144040000e03120107440035007200303000392a0a04008020211402c6500c40700e003145c8a042d00141200d031920b580c1c40760080a54403c0004120400c0c040380031646441c510007104041d940c8002114200395521000d1102c1c600700c4500343d0216940300c03880c0001059040c05460f1130a07001010060000082c1c10401c2000310503003401090903850190041c1403500b140d00000c0d00b040340d4607001190100e4a282da20307134007984c0390000c0348c1c8080f100c4101c03000c01c424051a2000c80c1e10994028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 685597904 1250 685596654 685596677
    0x20a0903140601060f210b27010311010c0b0714040504090602041505040509040303150b0a03020a1805031b0d05010e07290306090a0617030a120515010f02010b03010203070f 76
    0x1146c0c80b0ba07031040660140d10700503c4410700d680c0c468009a506420180c40080c40031910800c41d10001245680e80e03182004810040c4184140100441e0b0707008020b00300343d185441250384016140c8001084182044140b0070b1144c1c0030b00140040318001c00c8001c10074410111607081c140001c1d800b6118036400001f000400c0b07412140a441518200c1d60002c040300840d80d075548017503015016800002c15070b52006200810401810005441492047d030b070b0050b11a841140c029142d0707640e0810414404e42c450004000960f0001038080c40010b003415500b0340c0c0703603422000c030350075224403e0014080d5080000b444550030000544400f01d0700d0491b030320f500035019042c40c11440b80c031071101034169400800026406040c010b0401d6004010071000089181e42c540c4c2070181c07050401d4492032550070001c2c03100c440c241c1c4400e02c5242c0342800300003085142040403848808100040015040c414100101103009000707600c43c0c109000e0240c0259a1b80c40c010000601a0700c0340349440c07004c5169031201 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 685599154 1250 685597904 685597907
    0x409141e0606030304030b090309100e1008100603020a0e030f010b13020f0901030b03030c011e060807080d111501030506010303080f0708040314071a0a14070f03020a0903140601060f 80
    0x101c6000ba00054065460039003903494095010900400045461101300041e15060721400074101355801030740e84a41c924058482000800c8180910300c50410840c0c00078045589220311000040b6265130400580e600e04440007543c905080c1c403210b69141c001c2c40c80900ca00324064000c0c11010700100c4959070340c0e01083c00342d0822030181c0304050011120500418a01713500a40c002c101e059401800c0301c0c10030020050043c01d40319031141004130401a40007811802d0400c0c018080984001d8002d0560142032a8400395944004d280b15000c22880d1100a00080380500448110b404031141d14012981c490411980e10842072000300d00262003030000420703e00e4911030440c024400b030742d6100d565490320b4404846091800003060312801003041000000f075800380c43c000d26013454910b03540c91441e2481d662012944500b214140c100082020059a154000070020091010b0300f00141c40c2ca44020080b40c0103e0a508000d1801070100e079000300720364001802a040300c225644036906280c14040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 685600404 1250 685599154 685599163
    0x40602071a030412170403110c010c0203120702060408030f070318032105271009030320161d01061803171306110601090b01080a05060409141e 63
    0xe8210074000500100b4002141c0f41c0f00c001c2c2c004013504c2c0c5880d803204140500828040199401c80200e0720300042d003601003005008280b200d803401d0800015002031a0007003078950813402c080003034a0341c1c005401021907a61805440c0607003400c1046030380714500004a640103038030443e4241c021480c00300c880300d58400401c3d01030055980c011a0a882110507550041d50517007000d00c0340d000d0210901c42741401415400003040100204200e213403141d4403030b000f40030b0801001680307036041011040741032022907001049803803502e8000340d42d25449086013218a003041c108131100b19100c3e802800000c0e203012244008080c41d06801d2004140d0b9a80710015504001035010184204048101c104007040200e05940e1402e19205920762405080c40c0c40711190080940141003c075a1620000300030803010072000b03003d04110902007081140d2000041c20600340240408201074507030000440da5191600100d2039240e009000e05058811501182c0c0c88203510314410b8000c411011800e02001e50005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 685601654 1250 685600404 685600439
    0x809151306081f0521010e07030317010b040b1c0f020307201002090d12180b2b18110f0f0904060902012109061103040302120306010207050402040b04060207 69
    0x240014609241a0501c405c1680ca50303400b0062000304503074405196020f000e005000362100024003600d03400c514028054810700c5400e0b0402815503001400b400300c0505c03c54081c0c501c0c088099807106000302000d100304c080880210b00352401c007000c40c0001e07000c0d0b801441c040c5400d0f80f80c42c0030f15841040400607641000c040600c0c541e1000c0012410711190b40e00030013041c40e010304071680c0c0480380c1e04e60545030140325031050001103211100d00d0340280e50b1094540900183c0c40c003a4582510030040c07075064084240d01844808005100f054103001503840a8101c0703c00c607940030b10383e03000c6080104807810a51440c2d4000d01880d002540549014400030980d0040106002103a840700e40710300d0002d02034000f04074103010300d00041c0209503441141002001c80d5040700072a82c41e003e0701e44002078800700142d00000d40e00a1003800002174000c030f04100c0e2101070300d101685a41d12000101d241c04550780c4000d80281c40003401040311a04080140b0645110740c080b101c3c10b550344d43d1114007484900c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 685602904 1250 685601654 685601701
    0xf010e280b01090c171306050717040b062805040e0706081f0b0c01091101170402010f030216030504030209090307170a021c020d110706020a080915130608 68
    0x890040c80f21010560000781da0390340038540840a81c0b0415100b8041a100340c82500f59181300e2034080080243e00d000d11607116046240c98148000e981082214801014100403c411003440002c7c1d803c0d202c0c0c50550307022000d10440c0b0791254094803074002000e00c1c03074001c10340510709010851011722030000f13030b650442d10195550000744e41c0d171021001001d61240001007008151040001d171107030022010b040d1810340c420000400c03003810310300a645800700c18003442c1401403400b525801990101c0300240e010b034081c2000c0000b079000380c1045000380300361b210034016600c4904441d414954000c0c054802d6070b109540c0610710b030b260451840c0d40e90003441d03401041c9100920003010340807a4080948144081c0d4011a820396003030300e11141c4484034001e055401640140800c80700b040d841100c0c4004a191840900086401c2610094856205110141c400240092520642e85070032080c034120b00c40500c0e040391900002d42c0000720305a00d030310900001403080000b05404501d1006031041c3d0b02c590 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 685604154 1250 685602904 685602923
    0xc09060309021306060203030f1e130c0504052e080c13020405041a031b0f0409050c0604030308070f02121e071403210c0403030309050f010e28 63
    0x9054046000d0301416074202d03040850b481c042c20342d8062030f00a110190480780c001e076032285051130340039180101c000d1280214800f6801100000c00d901e00d422900000280040701e4003811a0825815400c1d0706c1d84001e400c07030311300300400241450341c1300201c40d9420308041c0007038802e003e2101a10b94000301e001d40b6580382c20608040c00349140c80d21802d0103102d180203015041c1955040054122a045051640c8031300510402c2101440c081c40328040a8140620890b69900d022010401000c0702c0c180240c0120b541e689a101404810002c9242e024401002c41c5da40340c0e12881d00030542001628040040f0303d2490004821a001084201503030382c0d16031205040503100c2503440d003880c69544680c0c9100300204060400704810003028108603061350002c0da610400c116280360604115005106080f095006000307404c12030500300d42c1100c3e05842e006c41c4841c01c9090150510703c00f00d2000d81a5071030103000c151400004183c075184502d040010148a01c5c4580d418111940e001c140142305840 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 685605404 1250 685604154 685604159
    0xf010b090114130311061306110a0606080d030b090c030604050c04080f011d07030c1802040e040309140a29040803070506040c090e031c0212040b190c09 67
    0x16190040d00da032210500d803440c4481d000e0004803415a104032000400e035161400305105001d403088510300d40e24810b031103003440d00c60901480200c90317509000740e9040040c0c54450b4050400c3c00c000641400381c01840420210303139103044407555261010100d4011a080182101251820001c030038480d540d40c490551955032000c0c20480248402040d04045030001e000105aa41013004140900c044001c00056140c500c00c042c080c0201d411105420594007019042c800198071a5074030085498030164503064000c0300e07030148080d0041d0b410a2680c810010100000c0c95881040c41c4d04666411030500c0518250704140403a0305072170701890140b907c2c0c0d9035002c810007802102c401100041d10005c0d50401707032203000d40c504643c0008003c0c0c0b0168014802c2c4005e01106003841001031641020411010070711110300c0e0307100c2c002d000346509200b5040c00000400300305a011992543e54110002c08540f80074030342035814100c10b88180410a10007040301d000d100306441044840341c2e19032152a001807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 685606654 1250 685605404 685605419
    0x606040b0f071e1a160c33050c190503070c12120f0209030a030521010e090f06040201050d0b0310020304080429070f03031506030506030d080f01 64
    0x91007a075814907030903810010b060200c0e1480714040d00c001100c04010418402d079060140c083d03400d00d031071001280c03c074a007801030380c0b425040d10b04404240c0f4102545030103200d00b4902c0551400715468102c401d40143e0042441d61844050550550350400810094869800410190007154074900079000010420501c15005001843d0b0044c00c82c82d1003c42c50445a0b00c907684541100d1052010a070710b60400340d440642d50003228043e0003800c90443c188002c01d400a40e035030f0385800d006010712000080c42d003400b809074145a802209100120960380d6514628030b05c9000c012105101c82d4003c94020551041010070f180380035039016901c1c14245140301c00601c1c0200f01f9550f8031a070602c541180198455880d00155201c0c6000700a09500d8500d840c00381d40900e4074802817544104080725142c1e203010240020f8422060b0001007200500b9128a4142c2c01091081d059400b070702405100041d4403035050304110320414096094440891741d041003178520680c01d0303e200a50008400050044a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 685607904 1250 685606654 685606657
    0x30711011e05090316210320030414010e100501060305100e190504141204060215060402040504021b010b010e330a1806090b030a050702160f1701050606040b 69
    0x840c001139924113100112a04d001c000032034400c0f950142c105c0350700c0742186580d95481c12a01d0260406015201c1031a00c124508021158030081114021003c14140260809002d595004035802002644407103d006036030340c80d0350030048034081e040100205003e4864043c1a0281c0d500300200810700703080650841040000401300c8a824801200e081c0e102007032401801c0c0580c5c011440c1e07a0003d240c190000741001c091001814400b0130400c01046810307800104101000182f041240c55900c1e20780000300a485507070b0001e5840b60000c1000c4000d14206c05c80010304610110003045802c0e0000015140f01d040e5000541e0721024007042d00145005441c00d8115040901e00c0c002c0c031301103420084000f40c1d000701e140300c00082d0365070380380c821401c10f80c0004101502c603909090a150340b404a0310b4076580301c0140012021912400400d181c00c2c020040742004800d5400e0b91842c11352140348140070641c192241d0359419101154107a001d050600c541801100040c2c0701500c1d01342040308084c82c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 685609154 1250 685607904 685607911
    0xc0515160f210f1d0706020c090a090302011b021f1a0108100306020f03041103030f0412051f020c060c120408070c0b0706091118061903050111030711011e05 69
    0x103940360b2104540c803110034031401e034208015130396080400021104d00c602d0000c02e074225106560060420501550314401447da004d61041f1001c107090f9601e1408030b0142c03104403281e0000f4100c0f4030302001c0f071075004030300500310301e10310a4203041c4040300c1001e00040e00c034035400c6a400f42d42d001d418451554072a41d43c1c6680000c440b41805020b6035285d86c3c0104070b910101040002d00404424041008640c0e03400c041c1050b0b0490045040c041c603060244400d104a22440040194240c004410043c0030b2240c4405841c960b1070444954140c01c6c0d09070084e5200300302c0c50f01540034080005841c140c040c2c094030201003000031200c0c2e00c0c0e92995100c03407143c0d000b548140c2d0078a10007000060490981001007000612662020416441d40c3c07400c9888110105405489401c1ca84034009a01c10004a12540110225070f11038055407486040121802c0030780015109508200700c40c0e1a2200e0000210300035003240c0e50382102501181800b90032a01c214800103190100103404010039149500090b80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 685610404 1250 685609154 685609217
    0x60c1101031a100918060f0617010b07020301090b18070509040507090e121c1a030d030b040e0106170f150c09040b09040c0504061a030a0c0c0515160f 66
    0x1032178454400c400312002c2034800c1c0a40a03150b00c0d0a1014039100310a1000401c00d6040c08000da48003401c6401039039405004d0300300001c80100c0c0c41015507800750030802c00541c2000138031105041c056004c000448103c4070441c1c02e031040240000e4039007019084144a95002005009100c0c180030388040a0854003921350300601c41d0100b1b540000f80311100400203081c190513243d22000403101d80e4400d40c0c17111302e00c8035407100103100c43c82c4c420f840c00318010085000514002510040f0f4500103801006082d48038a081c1d0b18218012030682000c4c0408002d8840b40360490700d1407425140110340e180142080781c81000c6041c2d0200d5554840240a000c000074014800308961414001080318800202c03401d88802424100c00c0041781064460b903c00b034440130803203a111400602038592a0b20000d01a4294190b0340e0b4409040c0c24400c1d0003812281780c0c480c05403120610380d44d003031840200302505d0b891240c011250440502c00e004d6440070840801c2511220800e0341143c1e000321860480070301c01078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 685611510 1106 685610404 685610417
    0x5090c0907120c140c0a23070e04050304120303020d06090e0a0f061407021b0a0509061c050304090c03060e04081b0a050304060c1101031a10 62
    0x86a0351400c282c0400d1500128200720790002080604030341c0700384003044500c0c60040115040d10a580503002c8a4110420409140f900b400007030026103055112400800c5050789484400d68418043c0094900b810f13035813034106950484c5600e045001950004600c03102c01c0c450711840c40a0036036200300700700c100b000c03e441d550340c1c1d161f107000a03027400c51521030b140c2044441c3d0080200d1640d003210901d12800d14042c0a5030b034a406404d0365400d084507028082040c02c1164104c401c4035001000d4103841d8980606004085407880381964402c0c1c0c0050f41040402c80410050000701140c603400100a400070000800f16007540d00300c80300c8070051000340008200d0100c02e5582d406190b000c4001e2013406001074a1409194900082c0700d0700000c10000b80840e044803001040341c0c01801401281d540c0c3e02d00450407180c00c0c1140700c144400084209001f81482d0714800708401071b40c10401e = true := by decide +kernel

theorem cover : BRFrame.Cov 685431654 685611510 := by
  have h0 := BRFrame.cov_init 685431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 685431654 ≤ n) (h2 : n < 685611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
