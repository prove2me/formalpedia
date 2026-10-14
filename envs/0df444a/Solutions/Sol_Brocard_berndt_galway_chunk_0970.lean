-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0970
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:34:23.442481+00:00
-- url     : https://prove2.me/submissions/34cb1dd6-90c0-4e23-8d40-b301f5c4e2ab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 174280575 ≤ n < 174460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 174281825 1250 174280575 174280607
    0x1707020c010f050f0a030603150b151315180f060e0904110303070f050106090b0109090c02101e0b061905090607050a08120703140103060e010b040e1b030a0b07 70
    0x184214800c900c4d030340001d0312034210b0684001850900b141400c00403044e520500c0c081c0d0781d051031610040b0380c5400128940d459010002941c035904003c0c00405030200e19041114809101b060005540ea845141e65400d0b9078075140d0716110503103804100c00c8a00042c05480b000c28103580c552003d1707041c581005540035010b070200c8030141c6030b820000380c110727800100103031600503943c10082d092103020321990004002003441004503095a20000c1d01c6120244150041320b0703621482c1e01000750013408400c41003210404200011030b040c10300c4001c040e0b000c900c0e801810345800c00041c0705041c458110b84000c2d88001c4210344103451002c003110b903940403408444d0085000d101c0c00f4002001000001199403050146513150407008202414180004184008050a1521100581b40e4a40303005041d280c00c80804140740f0a50421f05000d40301e10340c0b1f8250018a071240003122500046120504000c1c0102250a00120903040581d6116102000740290101c040071540e03860246011504c28010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 174283075 1250 174281825 174281827
    0x60d06030506010f0501110102040501200f0a08030103060f090503161b121a2a07200a060c0b0105011107031212060830090904050d1707020c010f05 65
    0x36036030748a0900d00d003a0f100c5078407141c81120901003076800c0034185e245044d1000086003890325001c0000c0600352460404001d400700004111402e00050000405d180030140403903040c204245030000e80d950091000f80c87d45031a0018501d0b04941070302070f880ea01a009001141480c00040200451a2074580e041b528401218948910304d0407100105000380521000044480c8242c20684000303a01c090030441846142800c0142007810400c0300d1007035000f01c42c0e104110b200240500191442852809013199060141c0b07010001000b8240512007042511a82006039403445c040c1c942e0b07441e11900400d280c813103000600003944188080f4182e0380e60780c8101c40b0741594a07141e106492843d070300414001959000c0002e05540d042c00b50a009021690040650001c82813a83c0c09800e1002c681030301441e903807140c0441e02c000a4090311865030004040a41c281028a071490b607a40003a00380c2000328400c468013003140742b8070940300c9104400b13507009800050610001140e40302e071800080d2092001c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 174284325 1250 174283075 174283079
    0x10e0913020a0e0703050105010c0f0813090e0d0f14190905211912200d05090a0f03050a03080712050f1b0a12110405060708040f051e060d06 62
    0xc2d03a80c40ca200140a020380c1c0d032181d810800380040c19224141c00c10b030b060050804070840098802504400503d400c060a25150320700c024080300500f603a07074401400c05003042640e8400340008500240d017600e064035501d4891a2009054270310746880c01000011240a012a40c3c0c0a43c540c40c20261441c02454200c03004c2c3d407641c00090f00b44201d040084c2901421207500c070b001a80c20404400f5095a42441281100d0640e8034191600c0c600440082040302d52620024455009420f611030318036514251245044150030050042d00080311051054680d16070020b202e0103d170021906480c0c11a02400c11540c031034a069404e0b510107400c507010001c00300c1c40303110740450501c20780e4010740c80c0340e9106500d4101840e0841c10544101211100014100490b81d0801d400c81481176401c2c5402001154158400c01381d020f0600699101c0303500107200280a5040110107802030007030f281c03c2c028a50f2002d490f00f0a2003910000f01044681c035030075480a0010515200001c4d19880c1e02d84030300820306617 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 174285575 1250 174284325 174284329
    0x307030e0619090305060705030c030a0e21070512070c060f121407030c171302010c050304060207051201090804030f020d020406080f010b0103021305221103041e02010e091302 77
    0x2100070021400162100f00c1441000010310a4030b030010404c3c07500c2411070904400c00d2920344006455402441d81c0e03480340c034515140911030715544401c070100e00c9019419000088020f94420340c0201c84a008065544a1141c41301c01030f41d0039544c1042d11940b0040c18110151996031000340c480b0184050490a11480003841c05006002015121151200d0914406c05415200c405641c4400d0140400d1140506910300e80d60031f40c04041003d07200c0680c2ca0038001070f21010071000300a0040d000009001c00c140c1d80010302c10040f62020f484060000045410f150300f00c907000c4600505440c010081007010851382c130480c0d041103000418102d0440815800501102c3c0c959100c02c1098100c1d03200746800354828030030512510001e003802e52401c5103440848402c0344982c054144107440d0240c15902c641c995101c515804031401604100600f940c0c814410300c3e0b08120b5046640c0c401c4041c0040c10440002258150141e06840d43e8010000c3c4400704100c2d44001000550820841700c9450090303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 174286825 1250 174285575 174285607
    0x3090f15280c05090a050d1511071406040c12080708090105091905090612072102030d110c01090e070809120d0b090603070806010b090a15052a0307030e06 68
    0x1460b442d4031510395480d01241408001032040c0e211500c5540c100c10b122000ca06d003440324080240d803140c400101c08909610206081c0210b00c3c001d03020b000e501a00311000c03c0001212406280102c0c08422501e40c1c0b01d00c00541a402c40c10010941d41c07042c054140010b0304400030307000d400b43c141812401d085a81e40030401f4816542e0340125680d00c800001c0000c1c0c1820018940c02130307401d03140c980c54441601252691004244100c0401030310031940031070350003800c10398401007560083c1500d54500301403000614015020341c2100082c05510400001d80d802042d0540445081540c021080e42d510b200c251107d9200404041e017a000303031045600000e1a0300300410040f0b0140d1000070340d5101080901980c0c1c003004000c0c9000c1d0740700706814400d50700000303200c40c1129600303040540c0d141e09040c0415076418040e0b06c03501d8090a2201b40f07809030742c2c10001500c401d400c440c510030540e030190170485005075104c441c05040c1e40c108002010100e031090000503090880a8401440e10305598809642 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 174288075 1250 174286825 174286841
    0x316030e091312020c100e06040b0f030109060801090309030b070c060e0318100e19080d030608060703150527010e010807080c0f06030405010b040c0503090f1528 71
    0x2e08035141d07020320100070350f4030fa00100350a018801000c1101005012030802d0f0350f0244054107000303007074a0b100700c0c0b5a2414203c8014041d00312003952030311107950f5a21040e80083c01801c00706810042c000c1008d0505100301040c0c2c58250b0780b41e28919203107440c2c102541c00080c5c10b0000304100c0403e018045101ea020704000300c87c021005565410045c100c101c1d8404081c80101e1003100c1c81d2103503003125a448940462142401c44900f440d0000860304082c0078500c2c1c1c0d208942030300030325171600e08440c3c050b8840300031500f8002c152551541c2c2d040c4100c0481e1181081c0011403a0084c80c10302c01c50070034903864084441010058205200f401c03d61003c0718109030300c41d00c010a00e100040c040e451060000c44014201034000b0100b01c2400c000169040301d1801c0300b14020a000300014080c80382c250004800800e01400400003d11302c183c000303213107510854845a180c0700c0c6541c0b0380340c10304000031050381c48061055070034034903110260f036403a510004046034200c60074280c401c3c1001383c1d000d11403480 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 174289325 1250 174288075 174288091
    0x20703020a2102120c1005070903050f0a03030c0302030610030b010201090501021812070803040b0310050d11090114030a0b040503120c030f0a050f0403031104080d030504060b0307080316030e09 85
    0xc40c0e4400e0200c000e1030310030344200844e605a4140311191418000145401100c0030010380400c0c640c0e909802100c3c0c1c04020360002e0107911502d2204143e058004c1480450a030207590300b03200c5a40303000700c141c0a03880260b522030341003087c5c62401d20b4554403079407000e1201c280502c00860284440d031a603d0980c1c02109054040780c041c41c0145016150594200b4040c410f0b20b80a043d01524100c0442d44138040c61141c0007070500c00100180c003040700c6000f10380162800401c0c04c0c02c520018203110103180c0c540160f15004080480000c14403d840030b2002c1400b040042c01048540d03003075901d04040c54030150040380c0b288130500070407264004210a4520480c011710170245c0300e280c00a601d20b5818000340c03400c86004d103070100b8401c2c0c440d201c0903078540c0030ba01030401180140c484451110341e40709580c000001c5024080007821840e90580140340128092a001d100c0c00318000200750b11100c56100c1c0144940c81001410011400311400d4808a8001d05040f80076003020004100b2018048500c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 174290575 1250 174289325 174289373
    0xa051920060a0c020a020102071202060702040f05070e031b0d06020405090717070903170319060807090f1503021207180c020f010b010905010c080f0d090314070c0504020703020a 78
    0x2d00850345204102002040380300510300010240c00107502c031003290094450062807c00ca403003c1d074a41e48100d907007559000c1d03c1003041141c525080f000404094032848001002599005c00740e26000030390801c4411614642034810030348404000c3c420710a100211119074003400001026030b0b820003464404c1450f6100c803044426141d015100d500e0008060805010a040050000c501c0d88904884518100303100d069803512880b4010301410700c850100c80d02107007802c50108016102244030b00482da010300f01485070f080c10034031b5541071315507851a20100749a0320000300051324081a41c042240c6808050714003083e21a0492036501b5507142d10000b06946a00c42c1981255040081c000002400c0c0000c0060384e12480000381013807602c0c407856041040d100b41d0039050040120481c0c140c00040f4250990342e6014005041c090200040240c002c0340043c060261140110012903070541c2e804010080132a003040204002174001180503800c61184445d800d00280720803440c4111351801c40415 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 174291825 1250 174290575 174290581
    0x9060d0320010f020721050708030105010c11123009012706020a030806031c0509060c061003030f0206010e0a020d0b06030403080108010f02090607120e090708100b0a05192006 77
    0x80f1080c800c0c103c6c41030302040400c1105801150441c03040d01d065540034a40b10b405103107641048410541e1309126a54031403140e211b150001f810006444178507960500d90781c42d586600030306c3e88441c22044640c6182102c010424840150b2203911394620402045019402a0f2012403098881000366000600580d001c00e50030418180c02194042c0e02a108030000c04004603c01c2c0388010b0003100140f080c1c24410701040300701c51681c0309425558015400812102580740400710b403220b02c1502d22040e00464030402070904407902c0420800d05031250b81d8180490340c0c40e42d20401e002980041d410420255540d5a281e45550f659401540038601a54502d003003035041465050071a1b046174085c41003248100111105620b803c0b0a5540081e003194000d01d09402d07144040c7d5001e54031150a035800410310301004907140c3c108110740e0203848040b0080c41c00c00e44409154815209030448200411000d00c10114a6030521540e4400400f680c505800c82010510a18040c244c21000c030000e80d030803100070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 174293075 1250 174291825 174291863
    0x30f05030c0712080a080c09030111090f0319030e0303072307170d08090c030102070f0b01060f0e0603100b0a02030c010509210a020a0b0a02030609060d0320010f0207 73
    0x2d01002c0d210300402540a0b214964951200784110784501042c841c41c0800604080244410f0b1100010042c000784802078072400041300690028003494403554000d401328140b42400206080800001c4903405000d96030703500c0544100c1145032109a15110410031500010403644075440b40007500b00c80090706d845405042400e00070075402c0b030180e0352000444401907444c0024005a5142c20b400c207082d16840d69040d00f8117011942c0c034a1501980002002c408001d1740020141c0001d010f004100091390301e9141c1201c5c0452079280c4000003c40002c603540301c500c0d00e8802580c000c424429145586a03441c0c2ca10a80b5802520300350300940c01c0413403040c5481e0000c0c001e0b00e03404007064010b42210a004481c6100409821010550f032410108529602d58001c10420340c0d65604010742660503c0d1039001d05000e50710882d05c032405161802c000c00c1d01810071000341e900190380364891b12a049043c105841100180380706d4145290749460030094102c860380f008029039801159600220001c140d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 174294325 1250 174293075 174293083
    0x9041401210308060d05010b06121b0a020a12180305030901021203100b13210c05180a20040b1e03280b1f02060109090308060d020109030f05030c 64
    0x3100c00100c1d040304200750002680b10b014a5031100c0101c98044100c00305007043c43c010000e80790f1003904a00c0010b2a00d0409880390015441180249070080e01c501550880c14102d004840061016174800e45801d00080d03071600d5054074a881d00c1c544030305034102c440c00204aa002d640c0c0181c0d0f0b1383d000018411600d507030500229282c100f1400400c0e280d8203100b0340c04451600284210007146ca0041020007041a182e0301010090004454036455070070401841501325401d000304aa0700500307004005540d050416083c41103004491903041c0b60340d00c1c4a920380140c05031300d0740c0080e070b42c0600d034000d03003000004000341015000b4140e0720303601d48010120080311503440b0308244074650b0050040181017000c0d40d50400745800076258400e1902c086101040180440c56290b0741d2003003111814a00035900c1800b10800f4150039230854400344d84e01e524600446540c090301900055122000400904088a52000c4c041c81071603c0c08c18940c0da5103e10f012090303004821505c1da000080e8604801c0d200704 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 174295575 1250 174294325 174294359
    0x403080103200a0e06010507080a0e0301140106020c040b12010e15100f090e1903050903011b0c0b100305010507050a0e010906081614130e0a0204030b061509041401 72
    0x800220721003000c00000c6001203d80b08845150440d4000942a47d12039000d0395145540003170034945446c4011000b5100402a85045000398a02810414000c642115042c100c50060b0041c1c107000906c0b0702880702500c000403040e81c01840000c036400d070021092154001e10101040903045502251140969606c4040c003004c280702e04156040c0000400340042804550b0204000180c0c000700b403140c2e900789581ca80070200da6620001002c000d268201000b010f1b0208102c000f004980480540904081d0701c00c410040003030000c4107400e0000e6942845030341c01041d1031000032540c0c1d90340c3da00c1e80d00752541100c50100289000c14603401035030b00a01c406000d0780090a02c454403a0809100402ea16001405451168081892171085c64001d0300e03007003d00c040080d50a40e81d4980100c003d40309240034030403003260340600c2000a0383c03030800744280c5040d42e078004000602619440f00304169002801e540090b001c0c402c02055081c0e0b940e520030500c1c49c010880c00301c0c14640c540b80d401c5000c11601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 174296825 1250 174295575 174295613
    0xd030204140f09061c02041e1d071a0702030a060b0a09061212030b09040c0611010504020d080a02120d0c09050301090320030d02041404060b0a0206010b0703030f050403080103 77
    0x142507181c40030341d1543c0400b42e004d0310580c0d14601c600010400c441c100e2085000c0607400620701602030400c445032010354900341001207024401030709804440350100302056003180c0306400000c8148804c0c86060b81240301c0000d1024618202034403900003030305010030398104540c91903a40030015a24144006d04d07500400c5441020001e15140040c800d051100302c49006003541040b00045409070300950103007a001402801c01817030b81c5040c0c540403100c480d850158a000c65514100e208903884c050141c1407003a94003500d40e03400540c0c99541d070501a0441d1240300c040d401a0012424240d004001400720444408008540e81180c4a00a481300039203802c0140240d0400c100007000c6900601d41c1c1e141c0d003907010380440759209040c03045030031800341091a602080c0002000074101d0459070b01c4840c500c00c219030801411355500282035981c41401d181c00c0150f000180104010320648019220a501a080100304940c90140c64002c0f15021501180880c45810050041c00f600b942e0b50f0264000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 174298075 1250 174296825 174296839
    0x702150304080a03110708031801060f120807111e04050a141603020c160518060306010b0a0201060302150304030e0402090f0f271503060f270d03020414 67
    0x1d52120344241c8209498101415101c00300d08401a26020884560035007058000c3d442c0d08007503801500410408514040c07030742c2403103404600c034000d0344a80c4040314a05c95240c519a46580c0c0c4540719a00f00040903140e00d104407039036400300c3d210034008041011125404107000081142084212007000d004000d08030320309148021041154032481340c02c030030961a00551000b0144044004c3d02c1000201c4415011348141c41140700440c03914802a41c03011642410b50304c0c4800d4030034420120440d00154590310810040040e15520700040561030500c1c4008690551030740c01242c814180d6003c032004007000041004141a48202c504000b210200c5055140600e560000b603110f0b900b00c43c8035071140c086141c42c000180c2e0b659860f4010186402d0300345d0030001e2030320540f446500003107030301440c1c0d0100c15030362400d02d00c2e020911364420350505206c0b44442d00ca508000d00f040100000b0034a9150958405d4400044100007100420810307076005641c075404c0c04100c00940002c000300c14015a8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 174299325 1250 174298075 174298081
    0x40b180d08040807050c0a060507051221092b0e03072d09050901140c0702010c290405070501020705010302040b22090c02032a06070509010309051207021503 69
    0xd40414074503002030b04280c005483d09000e042403803c5c5558074885903800310201c14006000d80d000805450094002c00c181c9469503e210503900c558407601b2031a400307561050080d51035250400004940000110b41150400c00550303c050140b0032442910b80214814020078070760903a4002070a10160301e0035005061035928101801d4a07044180300345070321a14510040126080021001d00010407a81d00244424140034890b18001c05005454000c2c41c0f080100064170520346408407801d050b81030b0345030202100075450741c43d18103602c0070071001d04008856020040c0f40c80c02075001d00860041c40a010103900e400000381c03038040217600250506d801400200002c001d0281954100850325030550280418003100481521842d04508a800d2a0030001c54000764004058804d00c8044007101808200003482c407800f0400c00e001030440c0342d00400006031f01e944254003a0848031030605021914503028bc1d102c1c0d06205141021940080c1e01203103150951401d941d542440101c08a060b81c5181 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 174300575 1250 174299325 174299327
    0x15090302060403030e10060906060e091e04030c050604060f061433041d0a05090d0c17070b040b010905160e1c06090b150105040e0604060905040b180d 66
    0x70014000340c14160f13942c41c0400315580510040c0318840c80480108890394852001d00c0061100707008400004592410389142801c0418166008908541c0000294082d4401c0b04107002c070010000c40c2044103251491002400400215010b03a1146102169038604040450300703d410f20750001c8146155808921042d8030303a06120055542c00700c0d056000c0d0401c02c0800d036601c1104840b40d8022240003d0009072000c1030714540034107090003450034020f6883ea402105c3c1691701c20f07078000b1415003001907001070300c501881c00194031500c0f44614404503c0c0e08010307205c0c01d800604090b01e02c14051401c01c820480c91000440c003400d0042c0f8104240d05025540c040001d0840310303007406200300003144001c0c640c2c0c0c45580404251011518110211b00c41c0341420181c403a900c412140d55558401165010034441e00858040106030f564508191034034242c44248000907040e80e404c42c0d5144008030381c24015019040c850b50148000301d403242840c0121808800c070403001c82da61508003e800142c2a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 174301825 1250 174300575 174300583
    0x4051b060901030207110a06050315010804030f0503060a03150f1d031207020a080d0e010f06050622050301050108030c1510051512101401110a0303020304080f070f15090302 76
    0x1001c000e1030b0040c0c5808007803800100450035041860b51120b103020300000d100da441002984150305c0310206810b00b00700800150340c1540e040d076001740481e500c2540da1403103602c6100550740c4102d0091034001016a0ba440b0469403898085d00000c0a03512486840c20118040c00707041a810b81840b0b0016411060840003500d0380900040d60b03881c1d614580c0421032151007080409007494004e09815030700c40159119400070821030b46524515403d1400710801008a44106021247e014004514040d0302c103110a01c140025110744441507800100451180c80912529010b0800c41000b90364030010f1040306464400d04c2d80c070046000b8007603000c0000407000c08802c541241e07029282e540b800940b2148841701c038092620f07060585a490410000a051010398031422100404105081c4c02801030046a501d18400840365680c1d03c2400c400000130b209070b00466005000310841d509101240b92a41151742c807400c01a207400350140c01da4400d003c240c070400014240004010041e46020747d80294407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 174303075 1250 174301825 174301837
    0x30c060f0c10050903090f010807090611190b0103060605091909080d020c060105010e0a0305150601020c0d060c030f02030115180f0e040b01060201020c10020a14030403050304051b06 80
    0x44220101d809450745004111882401402480c240414030f032140201e5030701c0e005000d200340305210400070096107500484c0030501031061950b9240b046402e08005807400c2c411f09051702c801c0e108003c003c1c0c411141050600b10350521802c145052035245090000a03900940c01c803c1c85240c4a2040c06000e11052050b05526081140081840035040c206000e42c0d006101c4561b00090001907000c00410010034220306903203003600c0388230803900c81034284100320007640002011030380104521424090501400c036401001407049400c800c030300b840032886c200d044c00030465856480303d014400690f018012100ca14040f50800c6055600d030907081e2500b04184c80360107007408041041c0c900c200080d0000c02d8060302030850480d5500b60703070381c58030b1145030401c950585840e840540042280c900c107000326032191700710100501a403116103801000075440340b19490b0611000c0c1210030398003c3c80c507020b5031190f40a6107515440740b41505045081211444408420b1801038010b044641e4400d0f0960324 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 174304325 1250 174303075 174303097
    0x3061003050405010b09011d09060c040501110a05120d05070f05180a0e10090e011401170307050706030608151611070f0e040519050606101707120605030c06 69
    0x240d903151801c3c024018907041e0141c5403c02c06078400072450400d2000f2007052200c0702c12850005644548240b6110101034030b400c140b108040000b003069601c1a40c4004100412505440030f68543ea034078075240c00b5050602a0101d100440d0081c8200024800c09600424a0500019140d480c0c1c000604510590170f00c03076000d4013140c4001440d0303116560720314058125a10501c103603040203132015003e02060301c5000340361410101942d04c51302d8107000d00c4001c4031090303d061596908102c80006942c6030481d09040d0361006000300c501088040001200602c403688000901d94105003540d4141189214a070346c03100803100620807c008014042c2100303d1061a01d2f00c2141c1060f040241001c0701c6500016440c0115540850b81400e0070310b02034001c2d4801d81c00c45104d03048a200002117104040c001806a0300500300081c210f0a100d002826042c1e40740c9009031030002210720003801c00c0400d40e80c1d8000a61825100986440c0c1445018050b03c404c80042400c131000704006a2030340b0035101408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 174305575 1250 174304325 174304331
    0x4030813030c0b070c0507080106150c0510020307050708031f091a0103050c04091a0913030903031803050a0b18070506030402041a060403030518011416031103071a07020303061003 79
    0x40c04113100d081081c1d001540072081d101d00c80c8c1d4442031a80a413000c0d00a407020304451540e0f84100b5805003040e59446940440030700100b041c803403111002500020719000512034104400b10005000d0700056100b00403001031005c0c10014030740d07017401c01851a04218503031454503041c643c2d8801c07000890f1002941c246408135480c4c1d80c2000070750310381c000c56211040440c01c00c458240071401c00c110b05078401900f9954003401e41e5400e0400004001540d02c06004943e8000701400880c0c460341054440d09031188811007400d40e207941e1035283c41040001a1070300c03403140f001d10050003198100011201300300380080c0302d564240703000100075110242c0700034812030303803001d5a0300ca581c040f49003036000d200300800158440350b036400c002d407207030b400485400c07030301c06100c54801150340c000d03d503d040280a060085003807104014007580c03032548804003601441006008640c0ca1102080101101f03840f4410020841d882900c0390302500e0000741404095410510070400345464002c607aa203082480d00e408 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 174306825 1250 174305575 174305581
    0x411090f06040504140a061e0204060f050306190b07030206060303040f0b0309160b130b25050f01020a03090204050604090f2004050c072a12061107030804030813030c0b 74
    0x100032030b8501e45d100c5d49510701030b06401106101a5500c20107000d5500c0200e189031002a142c0e2404a126a0044101040c1100001c114080c0310380d02450340154040c080e20841350072004e0f1000f0f0884641e1110074100c000107860300030558140300850b0084c8003038008509040c104280804504014019104c00e0000400000d41071101005003c05800c9050800e4274617644030140003290350700040301c02c140304107031420006069220008035080300003041c002000100d0000c50300c172110100b904080d1081e100780d02c0b200f441c2000c203100900e1500c9154400244005492041c44280c950052a181c0701e0740c0b808500c400811540752280c5056903014085e00300034004140c200b40340c050160030044e0081d140c00100b02c125401e030350007040a140202e84035400c0c5051182405200c200713131588440204c0c60240100540264a07a00303d03001c0b03100301d9010444400840c84100a6000100c00b40c001500350300500045c5600120640d4215a540003020140c48598402806a2100d4203000b4041560341d000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 174308075 1250 174306825 174306833
    0x21504032906060c150115111b040f29041d06070f020a050d09090e0c0a0302120a0b040c050f09010b1603090302030a051c0e130b03070b0d050411090f06040504 70
    0x3010300715100b10041c80e656103d06c00d500c0314062000017040400c16440e248004c92900190051001c000c109c0d00d0410b0103055420310010b4031492140340c0d08a038560314014a628600014030406101e00c4801150040c205020001502c0c105000518680742000301203124880c04180240d02040d0380c02d00780300340c0f4200b6034201d01d00401004042c5c100e0144100143c0f005610030a460102c54032110140440021074160540340d10f8130700c4c07400341d1000003030323608200504001d100120402c4070700303098820541d410348a0403001213040310102c41c81c1c19603c13028000781c5007900c0b0084280c030013602c0006040d170401d20340c048075220304100d0402614803803542c0d004051003504084040e6501805035048644180b60580c0da03030004c5100755001c0c3c104020858806840340c0c040000282000700b28400031401d20354000001d24122400c15018080c44c0b0000c540d23000751400802068030444000101850142840d290f4126080a400c0c401e410410520210301d81401450360000c1c400c80c9c000495441c0c07450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 174309325 1250 174308075 174308083
    0x705070311060405060c0f3a03021c020306030706020c0607030c06061701090c050915010507060e0d020717060609280c0c02010314090a080d0207021504032906060c 72
    0x84005d5101500040850020300003186100c181005841180c0c010043c51041080049031800c054200030640c3c0070b10403550031740301d005038500403560800610b040d01c0300079810b0782c0449907103c000a4680000502c500c5003800c1000100811403840508045905a40010b505202c0c3c01e60140420840030100010b00849501403001018081200d03500000b400314158060b08002000f500c0010007100d00080c1e900700740d0f0160348200d01810f03d210f500440c14005442d0f0350803d141c25100e99545101d000400001040a201c83c00d000f50020880d0038504003800c043c20074552141241604503000b07000050311140c007540d40181d0401207000c0300303000c10030b1394407941040c0f40141481c150074016103001d0785412003540c3e85028002c0e0390501401c0464242d00705a01420b07190303e81558000325450b4081410000600328111440710b0161414403107030001082120141010b0008100c0064200308000300c20301c001d252152800140e208401c19410403076105440100384a0103078000017004501100140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 174310575 1250 174309325 174309329
    0x160f0e0c031807030c0608160504052101090b010e07050a020a0818030105070305060a05030601150e011107180b0405070e240705070e0601020a050303060d030504090e06060301050a0207050703110604 87
    0x18045681c0f1039640d080046002d04140704140200d00c0403004501e041030b141000710715035500c0e0740b1a0b0789424945801d002d41da000e03103545008841c80c600b0000d00d03403110070f02510761100e006684032a859410658946014203001c0c001500748031007000b00050b09900818800d030100e410600098071201400070084030744000d08012035055180074200065141c1592000f402040c1c255041182d42c0d4071340c014155213180a024441d0b140c10404d900003c51442001c00103443c4a041c504421007041d8a407120b480c05640d50018104c420003000d01d080c01441e5445500c09030b20007240c1c00c1c441828260710260400402c4480d09009030540024194000078810004406800f403446241e655030003130500c07a4032160a400740f0100401c0000c003141d169071000138502c503031541240265155465450401200180c50300c011400d11405000c00074001c54107100310140e001d0100060441c80c03800d00101400c45000400c2e5013403041c818403541d0045000020b842e4203a96104e01c0b8401c01c02c4814000071107600881d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 174311825 1250 174310575 174310621
    0x7080412090e10090b01051e130e0106020609011413060c030e0304030609120201060f12032006070e0316030b06030a020607050a1502090607030c1104050702160f0e0c03 74
    0xc0060008880c0550f40341e07400c40d070502408202c02860040119010300c01c5402d2070190315202041c60301a44000e00040c40090551031141c204296208000c003024402688030342c0158204900300405c403502801003131424620380c0c13503c0010f8a400c0704512410240341c90050891660782101c440b0850007039208800d41c1b44c0101c12240ca135035407840d05101811540004499070010b0030040140b40307005004010607120411070b00340c0c900d401c10103007202e001e007800800d40030005524541c00c1410301c100b00081d001050300e0003500c03041c034064034098104c0a018560500942c0040184084003082c900c0650136241c0c0b10541c4500b0341c855100080c60140c1c00740300030b5800b4100241c010708002000500c0c0d400a84101d4030700303003054001840041240502c1c3c0f202508520308000000c006441a814249080c0c0700e0700411106120050102d8100c1d1000c0f203040016034401407400d400c030700a4800c07050003025449424410799040404032085141c02815540c17100b400440402c00c109604840c0020119007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 174313075 1250 174311825 174311849
    0x20702210c030f0c2b0b0705040302120a03120b030a12090303090f05031504080d0e0106050f19060c0f0b0f0a0609140408130305011803170708041209 66
    0x8000c0c154450400061451091080005074004000086204041c0c400014205241d401140c00c0e218040b0513034810810b90130f6036004070f010010704030510380e6000301c225598482e102e40c1944180201203c5120110744154091300080001a07401a451140e00601c00d9001c0741161070180440c0c90b180b44a48000d040c00a4410b50b484000d034869070181c100ca0290f955102c1080d03035102c148155122034095a03826800030b20002e44a11a4800301c05d03082071241488518084401040320122074800240304040d945441040210b464600828000070004540721380c07104d15604c4400700140014841c513410710110405110a0205201150354065040131040b03070285013040c070700240002c044500c0e002080c0b038820045514034283c4200c0c0b40c03966802d420202035441d61346030031304550000c1c141114050b600701d0f8040f0004e082030040160510b490050b4a503010038501d03000c1c0040d03c40c80044050811514104035485034861159600650042d0700480c00a041c02c0e03003120005202d40041c1e1070303800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 174314325 1250 174313075 174313129
    0x14030c07081b010f0807140f07060b010e0402090a0306090206040302150306011803050a170d0920060c100f09060c080f0f1905090109020a08060a0e030a12020702 71
    0x4008200000c400200301c03107002c2d0880328407005446640104842000081d200d0002070307507441c06000c42000042000403003038107050364020071140c01d9010b0941165595103620100140d0350300458502c4002070201c40c150f05042280001c00c0e01c0240c45d10010f843c0d03a40b1040c0314020b540328401240d02858001d050310400c464458030003081c560058941600041c0b5152843c140c1031400b007103000c2a02d5110025086c1c403d00c50b107a0b03522200f0380500102d0900001c01460b007182e000c5101d0390f00064440c0e0f041c220500c0fa244110201102c1c42d21130540543d00c2000303c600c44190121741c4450745882c074080041c1d969031303210b2042c1c0208030400000701042c0c64210024821508070501d10720500b00c2c20b8003511259101c8025411800302a142d110309204040ca00e4540c6c48130a4004039403007402c3e040006800748064000940098440d44800155004181403001050050040714541042c03c2d0041d840c00c0c2850400805036031000010740082d950101d03805085580348880700c6012001c40620b816040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 174315575 1250 174314325 174314339
    0x2161b0f0608091614040b0406050303041203031503030f0807050702061c05180c040c02030c010212060a0b04060906120b100f020114010f1502070b0a080a06060503040f14030c07 78
    0x84402c0e0384440341485849115150031020500300360940710501e006907145d11094041c070001c1c0c0706010002ea4040c0c2c03038003000301d00b40d201007015000521405a00300429855070030082c0844810f003d24000104c070205051010070b410508400c820200c629102d15665034180080381c80b800380490080d4094000581680c144010340f00d40d10f07484072101d0f4100a207440d0f40451800c2e2611120380194a50441c810b05072961810b81d10800071003c0702c0c010b40f8a003190300d075103039801c903405000d0134400340031a41d040c4891800c1461040303020340800c9810340d14240c24800040d0840141d07103d08000c1109501e40b5844580300c5400c90204640040e00c01d01c00c05111000181442d2591035000006600e001c040c29100e143c90b880c802d04940741c00e0071820b84141003d1001f0322600002400209601c9140303c00a82c8000000061980400350382c0c071407507213040410341d00060301e8080d8001c0040180500c01c0c0030200b01c039140031400fa154442080b02000c00b078040d007030b8214040c0d005807207a94050001d0003e02c003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 174316825 1250 174315575 174315587
    0x90708120901110d0804020609060403140703050c010c08030123060d060e060a030206030610031b0306080607140a1808191505011206020906090d05030d0c0302161b0f06 74
    0x207044240c84104585210002043c0d4804110341413100080308400440e015003046c500425108a0241401e0b00d02901c070388a01c041080c000100982c0c1c0d9000500400c28000140503c84d24078400f442c0502e1440e101d07407100c199600041c0940130020b410b030388000c03d5003e0044c040b4440002d02601d05501c80b00041802c10040000d0310a0b4540d96110b42c0000d4428a000c000e44016264020141400e60b00c4040902402c968078410460500d681c0304c000c2c0f10050103d01c1c80700c42e04082d50781e0204942c3d040007070aa040078005080c113001d02c04410090b21f01ca80d09401a5031488003a480d001442d00c0d1000c040b001e040410368041e0055019400409540b02454126003901e41d0280096002d141000304071041110002d200319803280c80114140e03000170305d0b544c00500e544580104100e06150088001844012465070200e82640c80042c0c0280203001c54024400e2410a88c2800c5003070003100b0828a0305410050130050020b80303040c280c0705600c40c0c441c0300c1102800d4401c024190381502c1302400b0b042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 174318075 1250 174316825 174316837
    0x1d0403020105010e0123060f0301080313080d05042903010f090b0d020102030909040611030c190c02010207050d0312020c0105180309010e01050f09040504110a1e0e09070812 76
    0x5500704000410f13218191200340d1704039017160a11400c1391003810380c481024402154445d038013540070001c4290000303100014501907c000030180d80e958401400270640b808403076104110a0308030b21258108140c02205840032101c0c040d0348030121120000900040b801d031101a0504840040001302d15407403240711502c20740c2c001110400a8003000e604001514003a410000e0050b48100710b402118113011035540e030020310034140422000322001e000b48032030b0001c64400d07600d80000b00b082a080c03c0400e00b0074603505154102801ea88400b900000c1d02c0e94000e000703a40c080d43c10000b0141c105232103109542c001d07054240b4110748490b07132600c003035028dc0001e407206011001030300030940110b04044115004000140c545034441c00544005646070340040e4100c100141040c404c0780c0d055101c0740249071081e489002c00e110488502130420101403070940108600508807030922103a40c04201809080d074198540d84041592000141860103c058200785a6030140030a00d00300550b1003c0a080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 174319325 1250 174318075 174318077
    0x30305160207030f081c0e100c0c050c0f27060109060f050d0515030604030e010816050f03090a2001090603050c030a09050309040c051321110a1d0403 66
    0x45084546141281e444041d400042d0041346184203040c00514110018a400c541120640200c0000c80b000310040380c458008040d002c0c1c2288214000c5081a84540820107589081c07e4101d03034050380784c50f43d40d80c1440000078050319800f0442c20003503842075541407a03201c03280340205450b2030850000044000c00d031034885c04211a1100030544500981c4a050000e116035110390800c072103440b56502074100504001440c0401c05076042070340d2014080140b02c4c0340240c840b450501c8400c4001001c01100500d01840c0101018142c0311140d03000302207410740e203080c107000d9480c0d131070b4190107031304203002014010413003610315030f140e032a002c00a0075079400721400f6291002c461365903010990990b00d040f205074070380141c208002001203460b40e011a00c2c090254044034140034448020074121102d0703400040c08110b01041d024409600c100010000d0800c1100c0743c0241502c03440601c400020034000103001485290300308245455658204e0010140e900c841e40801e6030401860251140070380d4154 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 174320575 1250 174319325 174319351
    0x6020a14010209212b080417040905060a091b0302030c091002060702100b0d031215090b0a09060602030307210f0e15100b130f0f0e0a05060f09150409030305 69
    0x4806100004504c2c1c192a0b20f207000d80094400321783c1110010002001102c2c0b020b07004d041030f50580307074610140016010340c400001d10741c1480b4041007001e028561060080ca801d0429000c004035590a03000000741d80b9040160301da842d4066100550300a49440765041038445a94165607640041d4140c081c01d1982c00741c981c0341203144420020f94542c1005940c0105032604201c000034400c06465000c6104480c002846e0740600c280d4071205d40040c0e010380802525100304030340d245442140800105491501049958070300f03d00a0b44034000100520b040c0410300003021803d0002c0f0460070702100070b10b0010001072450b20004001000407841b00300b114070440142c00a45244281900c0c040c050303c000350b49031103103462008110307680311420b030790248101e03074100080c0c0b1302002e41e465003e44000c5448061060810002c4604610000d28041c2c03428202020311410782c540070305035001c04a0540e0713001820759030100007210440310030312420303005860321071240300780359040d80183c0c05650614160 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 174321825 1250 174320575 174320593
    0xc0d05120109090507060c05030c010509010c0e0607050c0d020d0f060212010e060108041202010b0306040b0703051f090b04140f090c0f010e040c03140f040c0b0406020a1401020921 79
    0xb03104803115880c0c020b0035a4001c40b820701c1080c1c05900141031291060040320300e071188403111030b42566010366481040744c1d1200900219241c0110071280c1000003030ba481c9040201d9900d13150307511180854604e000714403040c01c1d40155220007400104003900b00d8402d004141081c500800290b1042c000c050100070940008210004c1d09240d103801020140d4505000b0780b00c41e11002454801c025145040d5941c071a4405103948040c8040b0744614040c9840440700c0c9002d14004d0283ea500034800c4116040c00828071900c8000da880500c00d4541010f40002c1402420b400309006040c1544201d801c850007200b0001e03c50210725000e07209078145800d403203980382800c09000d002c03c06400464041620310721150140e0520341e1250240d00e841e0b190100312103041c0040d00081d41029245102404500010003061180b41c090f0900200000b988051400b8030340301c0025140d103064400102100100218404900000d4054450300305004141c07011446408207014021840301c0c050050038005c8a1003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 174323075 1250 174321825 174321839
    0xc1a0705060708060a122f090f0604110d0519060602031c090b0405100c080c030a09050c030d050903070803071109040602040801020d02070b09070506041502030c0d051201 75
    0x954024592200040081e034072030310b00954080714000e018a812800280001030200c034010703101c0c08294010440380046103130320034840850005c0e560401c4c2c5503240c07981c001489070301d03a6586103070b0144038039885a4054807446c0024000d4040c150003006482004248000b000025901c00f03406840300e0404004c400820300f004005986042c0b04800140e00280040d040c0f02480d00005040c05192000000b0b00305c2072903a4490110f0000d950607145075003c0e0650341030b030403454400c4030310006550600001c9880c01c281c0c2c500316840000c0c001050581c48402c80f004010080040700c48850004060f148084407001000304140c0080c24036501c20310075034030005501e400100854111981084451071906820014001c1c120400b520480d68543d080000241c0c8203030030f00c0500380c05000c21001507600c00460502c2105078002420403000c9410010b0104896034a0304212011110361440100690b08064001d03811030250718a48081c034000c40c00a000802e134001c0040c80d800d180410618000e9803143c0c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 174324325 1250 174323075 174323077
    0xb090708010602060a0207080712080714070803010603090303020c01061701060e190b030a0b0106030911040e06190908030c030115050a0207091e09050105070807170105040506030a0f0c1a 82
    0x4681c2c0c000d40c20200200b0700c2542650000d00640b07000318113051030302649079104ad181c10355568820000507458801d0081e00d03130740040c00d00c8882c9100c0354414280107294484842234401031282c4000d041c0c0d145080403c141c000e03019a103074402c46100803c074031030740d66901c03503080b0110980c100d203a07528100020400302514440305016409460354184140c00c0049400001c015000090380d00d07204104160001400020f4554060521a5004240003059140c81d07a1070310b000110031407046007042d2800c2c42015000402c1648040d44070b01d00700318010841100b0b80184140140601540c40c00010051a1140c070710096040350810748407407a000114030b84c00c4480340078076860f0a0058203d01010410242180c1200582070ba18801c1c0900000361007006034112510304c81c08640a9440b0400c0003200c5030030040e443d90040207820001074000440c0d5410505400501459110307030780d2800815000d071002c00a04041c0ea902c140c1e0b8012251a909001441c00514070820b80740c0d41c2042052065010010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 174325575 1250 174324325 174324329
    0xd20070b070f1106130323360d0204060b0c06150109050612070509120c090603070609090e0a0b07180501050a050d02090301091b0806010e060d1211100b09070801 71
    0x10300a00303000d0710303440c092824901340b1500030f50800100c1001005041c9007a81c001f42c01249071200a65505404818110305075102071040d0200720111800d00d0004c2460701c410116850115068514902c2901c0004d00900c001c1c1c203c2c510b0407402185010005400244081c058070000d0508001c40c2e00301d500459030300c00c4074050250000f009111400d01600e84e0000e06801100b0f5051550410149001288a4003540300602c41c45510025811500d0b085c40347c9403980260081d8050010340b420310a0190030394140b881052015581d400c0502ca41c840c051000012441e8800c00c0c49030542842500180119924000c000007201030a4001803150300883c11240c0b60410394441c141060445e8840c50b009411150300b140c1c05548440341030000034010081c1c000c040030b03980d01c40800d450500000f41c0c5022016004425480503040c14000907903640103851105e20390241859000820070719044a1201080000030640e01c2200c58201040700c02e60000c2d00b000c030003030311940b500d5511400d0403a200741c000c4c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 174326825 1250 174325575 174325607
    0xf0b0a1703040330121d03030610090e010605031803090306160c0507080102030703060909021507031404090605150304032705190e010f03080d20070b070f 68
    0x104803c000180c8030501d0f00350348811442c020700c0c000251011100d80143d58000000021301d5000400501c0f00c00c51188500601e40030b0a101c1213629008442a9070784405000c40d0b100708040845803028501c2a80500044c0c083c001003001c155075074034000750450700284c407440584100900301602c0d840000043d2030042c08010002c003041e80300c00c100c0340446584040080104050f0703404450128400b0041c0400070500c0c0b0000503920320304485d0003800c41e4800c0e0004144181008221405070340c5182542c102c0103030345010345030344446a1409940d00c0e20000800103c40f075011600284050445d4401d00484400b1f8030032003d4100c03c2501c13a281407200700c900402140b041840310301c40001c0b19071404d1981c0009018400d071035480d0000a1583c3d4001c8000101201c040c40c400e11859140c49030391801003056084080756170f41580c0c0c406680d409220a81003005030780d1108040341007100400c0e980ea80e40d40850061b41c0788503d0078884209101110300c0000b10740c0300e0152500642c07040c03003103141c2c112030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 174328075 1250 174326825 174326827
    0xb03040c05040b1318120903150c0302190903031202040b120c0405130905070b030115180510020606041401080d03020903100e0f0d0c030e100c05010f0b0a1703 70
    0x20001080b00038010f4508154000324820711101c495401e52041c40f0f5004500340b20b5010744a410314101210300300c0602c04500300301c91240c0400c00070303011030b5004c011814401001300f0600c010500c114002d0003041042c0c0c88400080c0c034403601c100d410034000b8056901aa46444941c0c241074069000d0b40b15910031b006a841003000f032481c1421018862942002c4030b404541d162540c0e1340300080d00d42c135014051000140d03403014144100315007000103c0c020100c03081860300b9985041e03c000b0300a003400302580e060200d14410b000b41400303800c20a0303015120040c01c608205d2150b445c02035840c02c04482c4240038a1410301c000b0b0900c004400440e04030741854005044503038401802310041d4000d07529242c0c1510a140034090240c445003d031882c1c5813080307001480d042041046242c0fa16049414920500c0b0540c480381d00881d502c0400301c000307404180c0c0c040082c1d8601080844074000e031104080c02651900c00c0c03c8890031031542005c515204101d469080450311020180d03000c144030301f40b0281681c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 174329325 1250 174328075 174328079
    0xa050105010807030f0b04060f0e1302100c030201151203020114100915031712070e09040209060f04050421020705060a080606160302011d0109121803050709150b03040c 74
    0x3110360801502c1354005038021480c40c01c00b1002c5800da2302560000f20100800c0b0b58144444100400c100c1e6004141d100c4c00e50411005c4c0d008102024101001d490401114203907842c20700d4000d4000400c0d101854403140c21240d640c0171184042841500f049005500340306d00880f0f2000d025040741e00400082a10054481c5030041c0000104002c3d450f0701042e2101017800404103441c112405a8080c81c91106035442c2e0b9283d440034400348008182c4000e200c03000988030701640780c4610056205a0646040c56185c40351070000c0c0100544118031580641000200b2040040d0040005003025455014410004032075005030b86958003401900d4000f43d003840468602403081902c02c0c0c002c1707800350200c0d1401001201306025003540e59025400340c2e44030848401c08548503514040f01c902c00394020066074007581c1d550610715600107401e03410008002040e1041c00e20148081006641c0071048801680d13554080c48042e1850032515901d000455100050400b4031104417841242d001d81f540441c14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 174330575 1250 174329325 174329327
    0xd030906030f06080318010206060d0f0b04080c011505040513050a0605060109080d081626070e040e01090209010504060e0a2a02160503010b060412080c0a1a0a050105010807 76
    0x8903948140840340c607101c1c00c3c0000e110109000800038000b4420750a03a6544004001a203040405081c142c0160703c00e075041000f2680d50f03136440f08142e0340540c005032140c54504250b41d903406071583d035050755442c3c14020550683e00418800880c0d00540301880f1a42c1c1d10344240542a0344440094407540107901c80d800069001e61140343d100701c050400d1030000e80c503501c42528102000202d1404101c113001404a103160342400f0101748001450001020703503d0241c5000e641403086001308901070040c0c08600d0850246551205071040a071040024a080008107070180660000c20386c00740d5183d900206072402d0a000381d405448024007070039442d40b030359841c140003010100680e40b070710070502c200440543d481da488058204217980c018800034490743c45200b170b00003540d449117200b81c0c0351002c104455120340c401e4500320784005010318049003060800030b185100e2031300c00c5c0503e8002c89140000708895240e00510020304003000072955603d00c80d03c041110802c3c02200e020880e1000012030f51 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 174331825 1250 174330575 174330581
    0xa06020702030a0b0408070b1f030809031510091d1e1204182306010309060204170a031106090606090402060d0501081e060c04140d12020307020a050d03090603 70
    0x100784050110360b484551601c030300c918010f00381c4049605220000f07400082c024044031150b0401c0340d40010b0716800c1910103200f044d4500c41e03c0014002400070408002d281d03003d00017001a1146803410500c01e29029401200b03160031402410092440d0200104c80891032010410600c0c903000000e1005041100624080300130b10a002d80c55482420410550602c0700e8000e8401442c801e50740a900540c0c13501e80500b91402c2c0660b107011070a8071000740c80f081c2401d450f442c0e00804203007000524162203007001c502074030442d0001128190b4810480b086107000149041509029540380240c256500381410346405e8141c0d000312880c0d1110000ca556403034010740e4543c100384024441440d01c5046d80f0001700b6150300740c1c4548000c0d00070000041014100c0e048203a00c42100d100909035514110380040769602a80c0549000740660f0501102203485a160034000180c11074120800c980749a10001c5d9a98410700d0100d005a100002c0004c02d4105041451045581501e408001c5410702c6812001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 174333075 1250 174331825 174331837
    0x906030604050414010c080a1103061503060a051f09120b19020702100306081002070308012606090c0103061211010c2d0210050f04120201090b04060806090f090a0602 73
    0xb08040180100ba041300d000d20441074420f0385505c0e10010340c0741c002c40000880d02c89100d91862003004008000c484e03900d086e40000d207459440401034894030340300007040a10001e038101c15000b8903a1041a4004a880d064000311404542e0381c2d10301954681c1c01400c1400c0606100405503032001001c504014410340c100307000000340200c010f007403c0d036940001c2c1d6412858489100460b0383c8a00070301814000303025481c03a400d401c090651911090f5a40101445414410700d501025102d20a10f8940040b4a8641c03910b030009044030b5660411041407600e460110031480e0100e0310704200010302d5aa600d0650380070340d401041011442280e54010354100c561900704940340480e4003146804a010030b241e0300c0d60703c2c441044d41070b9513010a10600202c5001081100240040ce02c103442924015904481c03e580306050900e0803005a4070060b03640042603000004920008180401c80076440b400345ea100d400c0884231800300d03442c0c2121100030180d0035940c41c200d5800031243c03c8086102a0010700d2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 174334325 1250 174333075 174333083
    0x50403061e061403010506040b01021b0d05121312171c05010f0504050c090d080a12021903141023100305060102060f090303060907050c25060509060306040504 70
    0x89107540e1a10003000312030281d00021980e0580340500d9445080911400340c0c4045c023980c08120782d221500020350780750701484c040206d2907441d00300d021003a210800504c0031554002c080700ca40b40c1842011501541080039044000e10000703a0000e5600c50b200201000f4a400c4164104203261016180300190302c071001d010030404801541444148191280300e00a02240c2601da900c10300380410401030790310103401070900d524180320030a110781d1503645008010783d0240e4650f55442e680d80c3c00740e900e170700626088100c0d00d02c0481c150b00c84410800001c20040c665a03410443c1016400d185c0c84000010f854800071001001c42c184400c1139501042030640740c45483c0071141521081c00545030107082da04a0002980329028400103503010080c2e1134201e01c5405c0f200c492440c280e840c480d560f00004140502ca0344144002c240c1840c001c1c01181d1219220034150343c10b000002d1280015541c1c002881420040400c600080103445403003510104580146101e14684071031003000041c11014200355 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 174335575 1250 174334325 174334361
    0x2060c0712020102091207080c04020f04050405180703120809010903020c060d02040807030822180b0402093d12150b0a08040506070c08090d0c2606060a0605040306 72
    0x60160340705030080482506403030040c0307c1241408600707400c101903e540726010301e0051003000881c4040e60180c030b058a05c280c0700002c803540c40031810859850648a240b40d503020384100801400390320f90042403515400c0e01c1e400100d40b548030020342250245c1c0f0340030f03005801c481c2e8036400c140303040002441115440c1c0c2000d030900e0b450b652650705103801c41c1d108907220318000402c1c101d40200242036030b101c2c540348040814098505211440fa48401440345004560b40b0707103400b0b04d1952940d0689406e00c01c090101c881485e4541200890b030f0a4400010b08a402d960200700d461a521005454000f065562400b83d5041d0924680c0080d200d80004007401888001022607400da062002c4c081381c0d07025558149090500d81022030802d01c002d1b2600c002c000d103907078180c0041808503040714600502614000c5880180341005481c0704c249420a010300e14585880c419540c071002403040e001c0c031660341580c0980d20358404024403154580b0510380410001d000400c0807d84691140c82c9007825500f540b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 174336825 1250 174335575 174335587
    0x60f161103010f020c100905280b01031406090304061d0d1704061404031113090b013515090f0d031409010515060a120c1e02060c0712020102 62
    0x603003902e045050241100c0d40c0400ca007980302400f000584051903058500f04804647c64413555240c0c40d42d8141c032042c80c141481000c0d14001c0c0f02442c2800310350004469545540c5031b1608140d1414040c8601c2032500c07400010808644020003114201c80560300c43c601f04004843c81290302031016048142c1c400c1d804103045000ca0103280910703840c1242c81115669490034010050400150002e03500c10f400400e03c801d100003411804020822081140c003a07100d440004512009004450301c018001e400751000010740c0501c44a01c0c21114900c0040911034820311103d800c01c0f0401d000080109a101d10140c034981114501c41e240c22a842d480ad442901c000300014034a025005c6204800081c2d17107070308103408401c1b483c1c031540d00104020001e00c040e003000e01c20060413944e6161801d100d0180020482e600c0d6001e80e0040b00e0030200c5030401c1c0418949000060240300c000184944140005807010003c03500c040b40c2d5600c510f0314298900e04103034030364844e20800206010303078130250b650070040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 174338075 1250 174336825 174336829
    0xf050d050f01050403030e06070309030203030f1f0b180f150f040801060e0103030f0e010e010f091d01030209010f0b0703050a0c0206070c090c0e03070513150e070e060f1611 76
    0x1d65100e54025180891803400c1031007c186041d40080007602050710b840c0b10350000a030701000300d81d0001a4140707005e00a440300c086212240c400510400b058180080000801000300d50151030030700c4122080240318100141405444400b41803050f50020041358482d544203150000780c01007003e042c0c2c00508250f11003400e1421640c05422104512260200420406900406141d1915032a1070281000c86031030b8000f8100c0480603400e1414000c1059406070740d02e1041c007900b0010a211118002c202c184e00000f5032510000380016030007500100008910035451176070000c200e8609d081d00516001300c50320101c07500c1c1c018407581c2041115051048015aa409001d0101e103401441350308401031901070341e6021250000041070030f204680003d01c546c1e0354082800805c40300d040d25062201144100302e10010b11040d2035401100080c45408141681e004900511408158640214401040041181c40e00650024440700c07181000034020000ca440b420b5507113948039240914800c600480 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 174339325 1250 174338075 174338081
    0xd0b0c0403020303030703060503100204051008041704170c1c0308091203070519020f031b010605190f0b03040f140f0607020307020f0604031a09030f0406030204090b04060f050d050f01 81
    0x1b14000041d840d590284003e01d000d000c144000c0391055404c625252800c40420151000d19041c1418003841070009070a024030007003103000e088101d1503050f0380d56885c2c0c82e0401a580303203040c81b41e85502c500b2780b61300014103003030443c0c2d60900120156038110144694045450050003820f2030700c0f50040741c5540d4620400100a14016401911503d0b180e501c01c4001e60200e42141e040d80c4215408805155440c54001c001c5880ca08240c0d0131880c0b82040b0840c006014001540c89103421200201481040100401100c010f480d45421184440b41d42d980710142d4034042554050515190f40c00d1800005400324209010600004243d5002e8003000c40e8030b43c142075085071864056003000030b041045140c0200e4043d0140800c8900c1800c2c030307007103403607484c5000c04a0b03815640c290043d90105100313440070030642d010080c0c480c1203290342d00e40300c5100501a401c07900c514044c4504022072190640f6040c002c0c4000c6d00d41c1180307039054151402c0100302c0161100e000640d518001d15802c42440320703080c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 174340575 1250 174339325 174339331
    0xf0e010806040b0c0d09020301050112060f11030615120c030115030507020706050d18031809060b0304030302130e010f0e07030903020a11061b010207050c0904081204020a0803070303061406090d0b0c040302030303 93
    0x30740013390940d281c1c100708c800e446596840c100c10919010010310907241c0c5e03d050365001030b03056580f90344413903288006200b140b141c0c1c00d409180c203502c0b208101d035030300440c002181680d042d5402d040c03108200310000c0c1d09484081d6071500c050b80243c0c4081c004144030354007500101d00c400202040380c440d050081500c00852040507000038041e00b8080d0000801528850020803c0b481c0400200d4074260260780c0c1c0c0d01018100604040c4c00040c0025031440d1158010050b1407090341703020300780d40d4426400803000c03414412050204178507400251514061700c240300900c1c0e00b40c3c01903c078080065940595640424080ea0f03404003050104268038004c0d0380c0300090001091000581d1400b003030a140d46010b1082c0e0072240302d00c01020800000620000c161020b4040340001e4100302d44a51001134040c1d41903400111662001044000905625801405c01c13141b0501010042200b02400d000c000d1096520b484d4006a1106039800054140c20000e0360140e980d000c113506064699001a0440e8016 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 174341825 1250 174340575 174340589
    0x1d061c060801060503030406232503080a0c0c023708010608010b060f0c100207050102070c050109081b0a0911030f06010806090609060d0b010f0e010806040b0c0d090203010501 77
    0xc0d00d0a001d200024801c02e009400c08600440c10580f80c900028070304c2c0c2c2ca55480a000482078131507040c01c0a42007090345e2590180e109059101105840c11081c0c50f5603914003940001d0515012450f143d0b1f041c400c1c03107180c0704030b0b55460f07035015906d80038810000741d403210900c0b9040c00a01d50207140d80b1807006031b087c070072171444245c1002803034440c049080d81c181da00b054a0b2039141c14281202d9a80e114111500e040042115075152002d402c1c0950900c100311041c54000c030300004101040100c198010808580300f2110103141540310001111454201e01407400150300003054500c68800d083c0104500380c1000b0103c0211540791400c030030554036603040000070180d0200c144041d102014a1807a84090280b078007145528001000405201d40a4030a902030b04ca481c02145a5403a204014607009400901d140d119503524220400d08469901c03a5590384c10014001159101d03001c100b10740070780c1c1c008081d400b90743c60301e1032070029690210348221040c1d9640d20802006031000e0007054020050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 174343075 1250 174341825 174341831
    0x3062b1707061505030717070305070b04090c030b030618010912180605091516060603080301090c1805120f0a0c090506010c0b04060f1e0e0c060a1d061c 67
    0xc1e0b0318180d001d80b040080e5016070042c00c41400e000c00c1c1c80006080e0202d4071201c1505518001d03d0302c0003800c09003640c001601a0007003400104403038040400600494401030820007056100807800c404552085081903456002000030511a01d503000000203161b40c8c0d2000054805510750b116080c00200036150404500d100a4200e40003c03000a0113000b0405030030400c0c903000e044400104840d42000c02c1e05103030100800c01c503048c1d0b24520711100314103500a0f02000080d4480c1040c102d541c00912031869485e081160351248548600307a4004000b629414110449051100f0040c03d0800c0c10010425841945913402458000300294400d140c05100740d81c040605110b0107000303455000b014541405108904040020414255140c0c42604650000b03603078132030080b085001e0201c0c0c00c00c0c03c2e81c0a100240a506101aa42c001059000403508840c402580203041c081240100031801011440103c3c61041010310904803c000a0008092a14008071f01d45c220244c440d800d040c407401596 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 174344325 1250 174343075 174343087
    0xe011103190e0a030507031d1e0f040612020d06020f030709050301140108100c050f0c0606090f010b1602030c09010801090b010503010e120927150603062b17 69
    0x980c5114541148442d94060000522251009800c40c4142c1030010204034141c1c1ca41e21261305100000000100018124904007254840686001850041981c07043c0d0358840410690315141c4542021140c0c1c519a04100c1c81c42e5400300151100407070fa00b07440c00341d0204a85950703440c401d0001c51084040e034403101840c03070802c000d1608540880c2401c10354181d0032401404402000940210003558101c00883c500804a504840c140a0b8074108103000324045040601502c0105070288580c20681c0e4100665580da42050441d003000c1c49041010070b0200f24410078401c0700740791201120b00242c200c5a000d0800c102041041d40c09034000c507030b0b5964407000c201c100044003003000d00405088009001c0c031020448c000f511030714032010303e4069000000301c10183c0d40380c4007080c64007062511217200e1000301e2103c4141505c4c1c5e0440c2c0100f0075a0010040040d1817811b0020349005240190600700000c4e09150403251889001c44c0066402c1140240c0f07500046110b00000075007001c00260a0308e6074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 174345575 1250 174344325 174344371
    0x9041401030b0118020702010e040b010905120a0614070f1407210806040b101d04050a0203060312040e01030821010b04151106040305030408070507060203071110120e011103 76
    0x3104c0040107a80d0041212401503a8800c03449a1501c8040320002041c0c1d24003001a1482c08190b03000a40005c1000803440c180c100129200c10070500400082c031442109942403020048103c030319401060300141081c000c140b00d190102c15100d20042d51918040917a02ca07640c0070b01c01924007540d0700204080c01140d459101c01d00641201c010f8070700340442e111180005100c1e211a0000b0340400c45221001c990f21000c94502c0c1440003009007080200d8240780c0e40d00d001035031044403040d00901c9864000305218544078202d82c110360002e613404405900719520360303003a54030481e00e201e00040d001c2d02c0e2415000e10044450b00070284400c20360b568604d402c08451000d0b400c0414401848600d4201855000000c6142580164940350155403544d403442c100c1410f0007100c102600f1841800c0303020074900c1c2c0010040c4a441d00400308100c0421011040120300780ca06850000040c000d003034030044546a540044c903601e000c400022a0703001d50b1411001180d0070443d8852120000c00c00c10b01500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 174346825 1250 174345575 174345599
    0x70317010b07060e03130e1902030c04080705060301030c0e0c0408031303050106050f0306040807082206090504020a020c09090712060209040b100c03081f03050a0501110a09060509041401030b01 85
    0x445003040145040130105140b060071220359200e00007e6245400001c1c50f15074030001760004440c5828002c40d100c3c141500880e205070840e01401d80a03108001c0e01140605d4402c0c04d17a41200d920640008110341454840010a8800380010311804c0c824000807801d41400d00240016920103144180c80614508004c1d083d00c01d560700c40c0d4006c00c0070b00c80c92000f41d00d0201c1c0c50340d40300e60051401f66544049140080c603512948075500410a04210340240c0704940d040300c2e4044402c0c5d0340d9032105441d01c40080104038810300300080007691001c10341034951b041000e820369225030101c0556140c0c0c0e949540c0d5144501c1010811242c06600140300021441e052103a4030000e001078604c1c4e480d1894003a00504407072464000a81408040340001c1c07440e80100c400444d800001514540c042d99880c07a0242d0b65000140c421501c070350800c0040251200a0000e03110342c180c0700c0c0c0e40c0307044003441d248007515158004001a84c111b0f07160100740c101c01c1e03203190489008510404d43c064443d0725000b010303245 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 174348075 1250 174346825 174346841
    0x80403051606030b03030904050402060706020301080708060f071b020d02040e0f070801060b071e060609050103050f06070905060a050408010606080601120b01050a08150307090c090503060405030f070317010b0706 93
    0x40c18900010501039440006c03c1c0e4400140923100015207465600028025008551005004500000003c5031043d80442c00008440c8400d00310b4606450382c1e01ca6085c2040c1c1103414200041c65104c014040c0010b48a00c1d112081c0060301c000300d880e08640100d02520b541c1882ca180341d0b030000038806030403502007020500401c4448001c000351814007080c01140d208808000e0f0a0030182600e500c8111200c0050403003d41d40050101f154541d40c1c141d0102421092005079840d000320300d074600e8280f04c0846d81c1032245043d0b941b0a607088e410b00e01006035a8000800d20020010180000304042c003003441104003401564a5822a40c58000c000401811242a080048034246007011400c0d9030040d0588014408a0034071086954882c00d49040c1c000421300d60036494884c6500000f0359403010b611011010415070b5541e40c4032034440060564481007038030000d14545c820055580d2504203e0044c2079103600c24034001c400344c00d00d28181c40e06510280c01c54800d600000500b1010801e0074864441 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 174349325 1250 174348075 174348077
    0x150310060203030108120c0f0102041526071b0204061d091501060e130507030506130b180903070b1e1605030613020c030d050f010504061203030c020109080403051606 73
    0xc95581080581c541b2000d0080310048204400704000f101d1003024003101c0300f2100c02c6802152119555403021040114024020021817602038801e9140b8814070f10fa80150350001d18000c8540d2990641242d0207200300740c005500000c01c41016006994a004190040c2090150403000346a0071b01c035160141d602800b80c001d668800040c22080e03511859051f41100d46a09140c05981d1200700840c00b0102ca0041c81903109240c001001110340c0c040d030019001d07280a803001840041101000c0c82103491900f2101d50000e010000391404000128407580d104a801d410703a82410041c0c3d540c0e03c46440180c81101140014a0102404245030003c2961200d0b0112814001c2c4003004000b402521014000310b0103034035007202d5046e03818100c0e0111401c5d0460001143c2d81d4480108050004290640d01000e0120f030a00001905103054080c00043d0b44c1001103e40c040c1c9206d540650013006550038500c20b6549840c41c5001059003c0e018000840c000c0020707000c10407a9032410070704060241c0090b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 174350575 1250 174349325 174349327
    0x1018050618100509030d0c050a0b01180c1d090c07081209011401050901140312041206060801050c1222060902011704110103020c21090109210b04020609150310060203 73
    0x4c08940d400501060b4410f060308217010004070b9420000c1c1060701c4820080c04e030071501d400004003c48111880f60a5204040c401c00c640c0fa00c2070022110411205003041d450782c203c00020300b00341741000c29103030058498000b0a152000780d596040c0d0341c0d0002c01271560150b85880c20418455420f016211800c070300724994840543c180000a1140f240c1802101c0031f101c007011140c01c3d076272410010307613002c1c20002910688655441004285030030b40400c00300c0d8400d040010018103034005015072030082640c201c0341d07428104100f503980c410040c01010351070401d0b00c00040202c41c1c00c0010055100a001e143c0101d0143d031907000160a2200a466144c060602d21003040003140b0b03041120b41c0008401d10340541e5892441500301d19140d0b02207022444420044515100202c0500042104400a0300d40d92021580c0e0b0f8581d0b101c20407031580000302a4148601000051241130205502ca440106a503041880c60030105410100d84000200f08801c004240080fa441902e0148020034451000b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 174351825 1250 174350575 174350587
    0x40506010f05150708091e0315010803040e04081b0705040608030307021e1518061b0414040f0203133c03030603050a080403030e060910180506181005 66
    0xf2030f40000051030000d01c00300c00883d991080000798422210512402072283e0b0400c100c0d5003500c68208006980c052003846184544000d400c1c50741d46146c104d580010140d82480d00e8840302c05084500248101c8000004201c043c0a010481001301d140700d20400040640c0c6040400b030104030307440c1d03421540d0710f64418010446060344c005018007034100745400e61000e009441c11414a00f082107170b5158081d00907201000009442c40c1002c29103416204111200d030784032108282c0003014215101d0f00519400c0100340483c03400c1c5054100302d070300003504c000b5602400d15040d900300c0e0400c1d2a07694041c803c6036041400c3c0004110100301c1500e15245461170040f803204c4115503084001442d60082d81048250010315004e0360065004540060548144562030f03c0c0c1484158020b0004030089000f13440c07184041d050034429510102c0015180c1d032140300207210144c0c4c047c00008003106e08944000000305a036151200502011400c005a003080351100e1010054490240c80305001048003c1c442 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 174353075 1250 174351825 174351829
    0x503010b0a14010e01110703050f010b09010515090102030d0203070809070509130312060332010510030f05160f060e03010203040308130501090f0c050f03211b07060206040506010f05 80
    0x9504070b072202402c001c10100228401070b5110050001d859040c3c0c02400300000900001140c00c242c0b00104d04d0003002203080410800004000c20b004d415004100080910128291900200403034101401140e0804000c5c00c22001641d0017141c129000a041c03006100048400f08081d501511b4100c40101ca00d151002c4441e0420850071006002c11490800892141c0140ea000d803004d0340e00320540050010501140c01101c002103001000c0884880b50040c400a00600c607007030081d4040c00c140c031032140c65900c5200c00d2001030700054445015007001e000c0d0005491081000400707501e22101074003403078000060451002c200c0f180340240d004004000c0065440210241c0c404203000c040310080515042c6940141102d02e801424901001c00060510903007030304800403604211080701402c54828140b40d02e9540c4a501001e445641c03030340c44401d004442000d004003e040a030016041c65584034070078907005180e4402c42c05604040140024010184034240c0903110401207600142d1070140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 174354325 1250 174353075 174353099
    0x906020d020a080d0f0204090212180319051c0501150315150c0c090908040302130216110f0d080c010c05030709060507022d0907020109030813050321010503010b0a 72
    0x4441598a50f17144200d9080842a40c1a02d001d0b1082078021034842c0344050305042c0c4180c042e030b009545141c1054860701040000022202d09408801030300c44880d0b4041e0301a281074018448070b860194942da00c03100e0b1000c2c5031044900904c80d828428000b984d0700e030006001c45000d880e01c4002c82d0006001071001003460800c11044000e286031103101c104440c1400368100700f50341c000031300d00c6007072903900c0e0180141b0401901c00e8078000c40d00c0402d51007941d05030908a00c0340f54503a50818141c5001503002c00c0c00240c0e5552030510203000c034400119918009058801e002408842c803175404030340514810024031980f009103034a800c2462440c1007070503010380f01c0c51052040000f0440e0010f81b050464550b0303425802c924a0a0b020003000c1c1c01d1000308136004170a1510380b01d0140b0f2018001540c000c0c814080c1000198150b11602c0441d02c41400712403040c1044a02902d040c40700b000407042ca2200e03040d4240b80a620715942c0c42072541030000701420b44903050191442143c2c03d03513083c0b240510140e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 174355575 1250 174354325 174354337
    0x507031d0c060c01060305070e060f010c3201020a02060a1b05041503020f0301031203050f060a1809021c060e0313090b0109090e0f1e070506070303090c060906020d020a08 75
    0x846040d00c2c3e1500700c860300e02401c10f9404c02440fa01a110000404001030003455000b400202c4441c0304001e03085004641030700c1c0d215009859401c148101d60701900a801800d450b0fa103019910001c2400c1c2c001485007640e008640c0040140e01c09000c00c54001118450082d0500d00f0340c01d800284049141c0042050140f4003d1075070740d0b216510b254400c14025812511002a040186070312581c2d02c1c20700c90101c01e1840301380d0000c2400d28001581d42920707401220b00c01c00c00148140c800720b003880800e0509484118001c0c00965a440b0002c002d82e481c1c07620151001104541c00c824500e051810106451424001060b642c0c0144841410700788000c0b14030066030213254000a4a540410040f60a100d42d54400c280715440e20160103680b03000400e900c080008014200c4080c04078a00900940f1a280760309035140342c0020301d06006a2a160000741070850003440c000c16403070310f01d403038003188541d20350302000100d102c1d2001000083c2d0180f000c041c00d0300f482d0000c0c1254a49070b0f22980e02510950b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 174356825 1250 174355575 174355579
    0x50703050a030608010504080306010f0201062603090603010b04080f0303070e1c021005130b1303081e0d0203040308071805040b060705241303020309010309081c0507031d0c 76
    0x1041c180301d100e119610643c01490410020700c054101800c5c501c0865000b562a140060340c0041c10a05d49401402140101c5441120094030303d0909504510019100c0c60804040e000030800f40d043c60340d9240196010301948044155514a0030a4507840d09900401e4171503640c005204001c049600600000c50408060343c402030100d40c440040d504500b59502c009502c00010041030040581c000301502c0c09688001014003c47e4884442c0c810714001d154134000c103070901c01c5007032000410200c0034100360082d50741050080160145030348599000104d007881c15503804810032080c1584042919001016070928050107441c0300b0000c0c49a0785117015a5028a8480c2c9945d4420344401007103445040d0070005403410045140c03449480e40342c40100307000081c00480085404a03071504550f15906a154000b5464200c07081c005501424481c1000e0354184400e0006001d02080d0490200c000019030300001414130707050801078112800e407003c105140300303841c0c80404003000c0082c010103c0762007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 174358075 1250 174356825 174356827
    0x31005030601030b1f0b07031106090111030a3c0b0d080711060415110d11030a18150e01090905270109020d0f1401020f040603050a0e0d21050705070305 67
    0x1c180201700c00c020413039110645980b40014480c0915038442050000c80007010192109a1a80c1c41c0032400c0c0d07400c469000140d54070400100d4243c0003264001103c1c550400d00c21041408004204003842004103c41c0c1d02d1049100181c199403035280c490a80318800c1283d80c40710111240c1c07640f44444c080c3c43c000a10154248850041556844080d10010071140d02c3d42c208601c06481c0c001e0440c0901e04031690b082c441c042d151200725001e80304480800140000540c10110f0384142142e059200b0b00a450340307450240d0300850170f100c07400712501098480780c0329a500c0c10021000140b09401c26848007584520741002e111018850410750110719595250302600c114200491900400078020000e6009443e0701c0c400302000341202c00c00c1081c1d80074003030500301105c000d00e09901f42c3c4a03240101c02c1c0058100414818940241d21075500440815800641d0b0003126000500d0003c010725050086040303040900c43e280c94002c4011308040d4098130601c42c6060811002d021800307064001800c4c084 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 174359325 1250 174358075 174358111
    0x6250c02011209020604060c060e2b03090c060504030b06030f0712020301110705070503100510060309031709010204080d0e030d0c020114071110050a021b040f0e0102031005030601030b 81
    0x220b41d000300210b190010070076540c4a5a1300c0010704404420b10045503e01d040141c0c4510329400410698000c0181604602451040a50f00d041c0302046885010a16a5840b86007000c24035030340440000d00b000c1d40740e4541d00c80c01d40c1031428089000a211510a42c4524100513280501103003040845586034206414041030348002030140040040a00142d840890141d0074050000307440030864506800f542d0380394016442000641d041260b010381078002104040260610030384c04025400d019261401c1c1e554904007000702007807001d17111401c6c0341e900400c09000c81070f400d11040c0230460403070030320f0621003109001007500d40c040c00c1109014050303002002c10559000f0075000710528013510700e041c0c0d110480d14180f0700e50901240c03464001c0074025401c08010340501c0450701e900202c0d400625100760030b00c1e4890f292911403210726402036102c2c0b24043c1d0324212401429052030440b4009a00c0307140182e49020040c21036800148a81e00050041001c00c0c0e4170305155820183c01a41440b90030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 174360575 1250 174359325 174359357
    0xb0d030810050603040f0314070309050f0d1e030f110a0b0c0405030a05010c09050d0b0406051b0a030b030f010c1b0201020a0c030501050f1014010c2306250c0201 71
    0x1c00c0c0c0c0c0110f80220000040108200a61101040c0244240c07144e4500a00e01d994401090040810040100303151901c00e10070b62404011079010100004c20154000116a0310f5004004102c0021400d03000e8040c1c841d8200358101c003503c015025030703103000002000c82c103d0f0746a42d191290000b900c020100c10109008420400c1211701810000c0c00300c1d00307241c8583c58128002d254640614000648044000c5200c1c5440402c1c0040103402c4042405d40e0344590711080700230b010141c00220190460760705440c1d5981200003401200d801920001800c820100074103080c0001d154404031a43d00d00076042c50381c507400c03034407005245070030700c00c0144440c0d940e1005070700d010b40000c0c0c0504880f60300d520000030040c05402c488d10034042a501d800103600c0b524a202400740759801405461a8040090140b42d403055a99098190103524017511a01805d44000c14150702c242411f1899002501004258841c04011100c80c051410058030344402c5480010a14204402c000741003004000d2050008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 174361825 1250 174360575 174360601
    0x70807020d0b07020f010f0603150c091e0303031a091f0e01270608061b09060c0d110a0302060105010c02030f01050702010b03010b040912050306030708060c1c0b0d0308 74
    0x9554410b5200300796003000807001e541c40d0f001c1e8400b07090540c00e003040f11144510314000d82088030f90140043c000841d0350200c00d0007038581502407004200c8270140c0003560704040000980114020b00030001da46045017401800d840c1041404a010000e10425410644480080941c03010b410380e5003800c3c00251282d003244444941e401407080303035214000442c403825186d45600100b01100b442519100c0c2c1c401c5903000355040d0f84200b4482d9040395001910000481c01c40c414403860303151440b03291020000004107142c201d540c0000040d03014041842e00d16230401e03010820804501c0c024200d1008982d0002d6440505025050401c0180c190b41000c5484c108460306441030100000e100a1918105c024024266450341c41c0c4203608196190f1514202881400742081d00000b22801d45038030100141d07020b40c00a010700340c00d07201c1c0c40b400054808040c000c40707009118215825030350300719100c1401c0c1100c0b242110b920005242820070305541d6541c20f489020035030706040525103503550701809110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 174363075 1250 174361825 174361849
    0x240702040c050408060702010c08090d09030602090609041d0c0618060d3309090c09020702010c08041d0117150604020d150810020301081915110306040c0e0607080702 73
    0xc20305c103281c2800340d80b607011340241c901e0f1003080d51100c000b59075455200395a580185c85000c0450703403200e03050020651039002082070346405000d403032900001d4804901204d22911500207040f40c003003009006920b051011070704442041355843d042c40c2c10f0756400c041d1054510342c8076105600000c1c0840301c0d08115040749229004241c0c280449283d080508a084d4140301c5c201640c0070f4200070003280c0703060385200e8090b901c0c0d04600000c00d12030034a014003009610103442a410f103c4001009400034a00d5002031005d0680d0031104200801c02011b01144128180c1243e5210454036051130210740000440f24150f10100080600507120440460002e1081f440b0300c03540c0ca820f0040c1e10442c1c0c151241c59004a504050866445040c0740807480304900080c00b83d00c082e9007100180c210501c4118550f80382050248007809402c0c00c491048808031040c4050000d10128080208400c6140c240b00c1d820b0310300b46c5403c2c610a0200ca0900082c40791041800040600c1c1c80414180207546030301d031300d2600c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 174364325 1250 174363075 174363089
    0x2512050304090911040e0109030905011e080411210601050f09040305030403090801020301092a0c0201050c1203070908010b0d0b130503070606030b04020a12030504031502090d030905240702040c0504 87
    0x140d1b0f0760103034041e02800c0c005a05601203401d1600004055100700e1500d81c01005070704241141e0304401030115100078001c1c1003650010f040035260728482d51026100c00c1e8079803202d500062150412000f003070400d00140d10840c4034034444ca80d4004192185112558000c1d40341c07400782d40c1c070754841c9811789815103150003201c02588080004a40c0030310f640d014524020f903c508032000c4401029074420f00900311151400080e40307080012005501030b03001b034041d02805030242c840911120302c0350900d40c4c104076019000901d100f00d0801c690301d406e214141c01c60805450002e03c290582d242c40d400e0580c0079107000400483c010480c010f00505006036100280c2c000014840203035242421051040c041e07409030b1084519403000240c03c10055140c451155043d01c4080c100b0303113142c68034007004c464550392501c41502005400c020b5a0f4400d03107001900d1080d112281442e0038201489040d10740880011120015075031041a04102c80003520412036040360040307a01400400304131014055640014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 174365575 1250 174364325 174364331
    0x170601050715380f0609090705160605010609080604050c0603070c06050f04031407030e061c090506250e1003110307110c0109030b0f090c03251205030409091104 71
    0xe0403000c440384000901069400d10f291548a00070841d500310078000301a0f00040c200301c910b41e81d052241d84141d2040503810030600f0009440d1003120300c04a100c0040307806565500c0188030b00780c1c111845802400c80c0d400144103610302070351602d0307564092090040c8200720100000d03c40e207110b110818103140d405041400740e0f04000c58070365554a001d4408074042a801d03c00030491214040a544106400da5100031400c4003c030b05200c1c482e8400343c41c4009a1881030342d000c2044900f0b0051a2410f40718000414442c50529090000004403000007a800784480010100320355020420b907882c90012500901d0356400017105400a144600c400d0440340004020001d0640e00b003090540d0402c010026100d40c0181d003001103803506030f03c0c04024106800724011031812507012010a82c0003981034110f484e03109188001074a09030f21151080314280d40c5180840d5803207800380ca60070043c4180f2005082008081d81d999480e40618000c04041954500086e410b03c40d050801e00da42d070303201038420 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 174366825 1250 174365575 174365621
    0x903091005090f10020703080913140403030f0209030c0f03010212070207060f03020f070605060a030503041e120b040b0408160609050c10140a140c01020307170601050715 75
    0x41c0080e084812014031075000080c582c820381c208030840100040c220ba001c1c0104500b55928900d85810003107603260406d82c414005005800380348141c402080150528880c03e10f4180340080594950084180d4003c0c01800500f15a4a00091b0f00c0c0d8441030441e9521107200303842020900a001c3c9a140d449608040400e1009903500410420103680503640c030500b01080c5a401a0203910809030303d5140203408004980118040c0d5000d075400c0017005004403e0b185d52a21150700c3c5400c1900b01c40c4c1c8a164940d48904480b4880c6600c400501040003220700190b2180c40c0c21500000c0188090001000304d000a41040302450440d10006450107030000c8030491428081d00814846a0841e030900c5008154000ba140c40d090302e0503a018907a1700c800e414801074190542c0c3e5008203050100b07001000b81c1034403000066038054180c541c10f44000584a1401c21002480b041b000113500344400301c200180206640c1c000c04554045401121380d61251000300c04281c020a440c0e035101c02c1031400d03070001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 174368075 1250 174366825 174366827
    0xc0c1505070809060c25020907030204050f0a1503022203050601050109060315051210050c0c0607050403050c040228121113051c020a030804030c0b0a0c0201030509030910 75
    0x420341c0600615610980e60b07944408a060f5550000d68880000304400e02241c10420805002014001c25041a00900d2003c0d0307800f2404082e02038411300b010a0300403c09010505103603203c0402003204480103442d4900e80150180716441c5602c09504040d00081c01340c1c40e80086813041050440954488041c03c0d5880c1055512a2428090280080c400d011300182184c0700b405140207000c07150524000c454640000c10001003030b14038101040d4022031411141c0c0564522035103105114140001c1c1c1ea51189914403418004024500000d00c04107210070300c0414400250701042510a54005035907002d640081e82c40b0391640081c1040000b00c03541d0a4640c40ea21034000d982d011420503090000c441030315090780d82e5002c7d5a441d408a1400c0080410107480c0007181c4000035050480343d000114641d401284c840001d54005030ba2580c00081c08204012400c0c9003c001003411921980c14540f0000c0c0c007e21903070300b004010f41015100c50100c0d202c40c00c00d2084901e0fa16004190f1a80c1d80c0840b44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 174369325 1250 174368075 174368081
    0x180703050603060c19111e1606090e010905060402091f030b01260c0c0f07030b010603090201050909040c050618180702071701020c0d03061e0506030a0c0c15 69
    0xa4228000e0003540c001c14560104501a102d1000117502041d120150b04036084840180000c512040c0e48280da1240540c644c3d8a43d116000c02004401f9001c1c030406a02c01451042e031943c0500c041115000081250346401500700d8159081500b01095070b846000009001c2c1c00764200035030780302d00851403d00d412070941410781754480f0131307481c14441d011000d0b00544184d003800324000800f44868011408682040c2c02d2a603029038040d034000d080c000c401040074501081206114071560107400e0038400d102c21040c41600604042c41c00f0b000c000542d600080007401466106c3d0302407250800450b040083d215104c0024201c042c0c659500c0c2d0130180c2004c070516881e40b881d640a01e191140440613605044000f51180f03000c0d40080060f645480c2c01505088815a034201047d5820b1000d00503082d006d002802004405039004101329003845007555034003042c030001680b441c0c2d07a00f0080146860f0780050f25404a81c6c0c03a00002c500011840a941100c40010000c26800901e084601c868030a03034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 174370575 1250 174369325 174369331
    0x6020d0b0405250c030c0c0602030903070b030c0706111c06140409231203041a090109020102070902090a090e030414030a030e0d02060c010f050a0c03022718070305 72
    0x22024803141c0c454040700001c02000d401410004540e418400f4101e6000d0800706881e544030380f4094510460719180e0b6082d107401a04502d0041e04005044410345c58100302c0c480107048514811441e40c100400c000c681d038880c00304004d2415840f0000c045581c0c00f17900c2500c4180701001041580d58002900d00c200400300d0f0300801e0010360400084d00f2550a00e403003404215076029080b01e9010f0b010460000001d14500690710b0b40f0f1060a40d15084444c00030051405140325201050b92803841d803c000d03600c11001003005000d84c0c90300d405c0f800580c1e800035400c0f0440b0180c2c10016070390540440803c54009480e000307030750441d040c80111341045030000300a104030742000000c140d0340051031080507224000d07102e010300025404880490207107001d01e0451b0411703200501e81c078500312400308032a00b550144030300e00b40c0460780c48080284542d01030280c04100100c0345811850241ca215041c09204c00140194080101001a03084682c0750b044040c122090b680e40e00410074600900000c1c0900811 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 174371825 1250 174370575 174370579
    0x614040615030b0a0f0204051c0317040503090907030e030c030d0606020c0105042c0906070e060c07090b03030c1501031106070816061401090c0e0a1a0703030906020d0b 74
    0x11041e09940500c0806000d41900c1c1d1201d0303045203075251900c84601520346880c100d02d00a500308000503880d0749151242035059046440301c00d0500c450304014008244000c0da200c2305001d40c10811000800c040101c2d2410001100c090b50305450b40c04040300104000d1842c0142440002580340d40041c0000207403840c8a086402405403d4556500b01c2e25002c0420007140070400c184000c2c4480340001d200140080c079800d00407032440000c082c884825900903162808a43c001d00c05210603164002c0c0e95003802c850a0303d0b00c91614490b8818a039403414070f8400c05d038803517a64100c100025034040c000c641c01161440304503a1003681c103107241400110b0a2108943e010501d11042d0301c603007000c50a1702e80f0070350480031081c02c089400e075060400210072841140c0041e940c01d40d006c0b55451a40c01280601700a074000030b008400c61401405030b001710306489100307143204201040340c82d030741070000f0703062130001400c0030b46032080c0340b505501400c00c4c1c03c03004001c0c0d03001180d008401a142c0c1d0181010042c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 174373075 1250 174371825 174371831
    0x2040c03060329150a05150c010606080a0c03050403050f0a0309020307060f080907060c08090f0d0821370507050d0606050c1c0905030303010905070806010203030f130204060306140406 81
    0x10f1061850b0b81d01c09240c400b1364100f00300c3c500070000ca00d000341035810042c0c41c0030030076442c1100d540c0c80c2e0750840700a0740202c4045079445041c8501840301d8030841040e10050f06007008035041c06d44001d0154084d00b250700c0d546003400101d60119611907003002d101e9540c00307000c986100d0384900010303004824590002000850f46400074071840e00c0000c085046508940701c00c01c107250141ca50407500e40c050030b00a81c100c2d020040940990700c5000105015500a1054a8840d83c5800450010000c00c184254910a908042c400e00c1d00e1940042e0203601e1000d0030000701e8220010b403210800c030590204901c0240345c0020000b0082c0c020008281d500c980900403c4400c1c0c5404040e207440c0580741884600b03034807070744006501150006407040410740030b00b0030314682a03554000074a1035009030440704815440342d062002e502e410801194001d1000d00142d0b08516250400450b00080100590403034007100301841c0030b6403aa80e000001950f0028018401034001c200c1a6040280690307084035080c2c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 174374325 1250 174373075 174373081
    0x15060f0c0f0c090f1306020f0c1c0305100f0b0307030603150c03060e010303050a031a0a06030f0f0506031b0f0a03030804021002030c120319060305150901090f02040c03060329 77
    0x1085048183c070417081d501e0b9541c0962000c0d101c10000713400c4090040c0c444001004102c03a106810030240c5401010016540c14014072800002c00760344015000f91000b41107035205004061080e06284150340ca60b5049546070380c5c0d1513200700c020b09082d0f400941404604900c100e1840d044d40c21130000f107400d07904c0c20300200d565005035603a8140244000b43c00a88284451401c00c0d100c2d8010850200e079440c1080801580c0800040300208154480c002103945c90816000c41020f602a5040304c0c2c861400401003443d2840110f034480324000c0440d550070010540742400d60361152480b040e0501e014003030003481522840d02412012050385c007a480349480801d05685c551000040b6508607401f64042c000200540d00e20985681010b040b0f00201220301c003c080d0a284984140c40080d8040d01c02040980c0c0d04102c034a00d41300000d80200d025904202c1020040f400c00890240940d074152400a02540c5058040703004000c46d800040600e44105d0382e2800c00751020b16080c90304401c08250120b152 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 174375575 1250 174374325 174374341
    0x7021c0c06080c07021002010b060f0d05060616120207030b0f04030206090c030309240c032208030403030c020103180605090c030303090a030804031110150e15060f0c0f0c09 76
    0x16200303c902880301e002c104501001401d000d48044040b80217800041100540740300015800e41010b4a020400f00c0041501c0000380031500646411840a5481901d040010210342c1c00d14031641c100907081c820001c00d844942407007000520011504100940201d01700704001e0380e0f1200054906900500c1030704041004e00f4404110640c0071003000f4021840c045a180070301000380c0c04240e81c40403803000b500300c0302010f1848000400000e0f113031a010b15070b103003e0324603514030340701c0c0811010808c12810032090200000010440e41501d800d814020524091880100c1c0a8503a54605000e04503420895200300b20045e00b000d8001c4803a00c0a80d001270510206066490000300d07501d52095004036189404039019904540c0c02500a1400b001005081c00b0194a426101d40d0f6030440c482d91101405204a450040b00c0003602802424045a081c5840b01085040780b480c803051240c4400141841c010940b403044940048030002070382c0c0660132280b042e07607c61100301e2007207020340f8030840010002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 174376825 1250 174375575 174375587
    0x30105100509060d0f050a020316060f030b06040909050c040f2304060e0a110a17100f06051003020d110306060406030e03120c0310061e030e0307021c0c06 68
    0x65000055060345280703000100514600003415690b00101c900f80014046011610021081c40c0158000c0200020301d02c1410700d0165000c0486c40806c007003900510100d640300585a5000c90f89150200300300800300c00082c00c41c4101d500440c42c0a2402841800304140803910050602c0105d40801480c0300e0701003034000b6503001c0b20002442121900c0100c99022606002e2a00f09020b00f000040700302c1c8003e200d900c1c0103100070058658000d801000507031442c18200d07680150809408400301c02c81a620901d0b65500e81158440c40c194444420050411080d403101c801403100401440f421042010064029407154030f00713690076403d084400005007582c200712030140a01400103403404d49026800c070b00030001c080c0705c64178a0104229210080c0655002c003409989103071000c5a503421f1601c14180b030203203240c0c03000040c8080414803040c212200041003c544440e418041914459088034608610410340d0080d84084810810301065a84950300031605115100c1e12034103d413189420b1381c0fa = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 174378075 1250 174376825 174376831
    0x30605100809070b040e01030506010b090907030b1f050408060606090a051003020f070309140d05060705070c170106080d0503060618030c0a1e06030608030409110d110a0806030105 79
    0x20254500030421503224404032035202e0642d200380e80c01c2a40701c2c208084907030722942c05044240b1403c4010b1051160038094a401440c1402c0081c0c0342a401002040c0e10810050080b000d00d41d42d80c406809545a403865161440d1040311065210190944013824580190040d00344500c203042c002850340c10020100c59058000414400c0d000d0714160800192001c40380c440c0041680a001c903015440c0d4140152650318481d031190000c03d030a10003146656800401b40c24822008a0140000300300e001c00d50f00d400103118a011a5180010b00702081144015400780708020300136041c9004000381035000c002030720f0112080e031320250341c00c0c0740072a058003040c0c2308581e00000c10005c038001001d0082e421280c803c1e004d401e80700300244540010340110311580c80a40340c403440c01a046283c00c0000d80b02000744c403150400700322003810244819501c1c01240584c2e900c41d81d80307a45000d9040c2c00c0009607000c004455a0501008043c4010000c45d500b10400c010701154104010030b01614040c020548 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 174379325 1250 174378075 174378079
    0x61403190c0206090d02060613110f0d060510030902091611072d03030807030b0f04050a09060e0304081203250207030201090f060807030b04111206131e05060a260706030605 76
    0x120b0050003507480c0020240703181c418180103020015200c0e44a00800900258cd1100c040061038a140c401800800108500c044040514104007140166030307070710300143c10080c4454000610510808151522440452030003003c0c1f160600004076800c0c0c456540d00482200b004100c1ea01241080c0001c0b82c0c0a24040200403d401800054905100358002c500311030005048418141c40c80c0301044c1112019034003060943d445e590311609001c460b00540b110301c6031080085140510b03009800762281e09081901c06851000008560b9a4008110203000c0120b00643c1c01100024008003030355803010380c4001c90104200000000d060420700070040200c030310ba0345400c400d66a41e01001c0f40100450000e10750302c981d842440d13034104001d4030302501400034400209010b0741860340800180704265111428003030309000074200080440a50078454441c55000440c082e142c140000740f050f00281c12079441c0c2008a41c880321a004c929180c2004803005c84291840300e516818110292085400740325 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 174380575 1250 174379325 174379339
    0x2010801030b0603030706090303020901021e031602041b0c0b070302070c170f100c09080a020307120501090b0a0b1e09240603070e12010501061403190c0206090d020606 74
    0x80802d510422490f072106004080d00d2801e01543d0710b54007101d40210081d000a9400710f00b400c21540c0400241e000040c0c00001d072a41604801c81040d900e100700800f00325036501d0f4180c54001c645481c0c001029010192802c1401c504003c2c5008000386102607046d5410030198000c946042e02030300c202c6d0400c0d0b80080d010305038941050442210500c40c1f074114007c2d40b082e0400094018014842c14001c40b101d0781021035001d101c594010590800d0790007056403a0803407820070006a034000740c100125881d015162a80c0d0200341003407070051002443c003412182c10740d400c20242d000b566201c1c034541e98044900c01541d0005804100d1888500854650440007140c0030aa501104211007491801c1000301c082005a00d480428084d80082e01c504020445a010803010f6240685807864003840d100c00030000d0350300d0020f00030034401c403a202c0300d20b07900c00c008042441000720f0450580e840c107a03004284421800c01000035601e40089070f0844880c0220a42301205610100d030040c02904014824 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 174381825 1250 174380575 174380579
    0x203041203020f091f0e0307080c010c1707050c04180c030b0c0705150f01081c05460f050906090a030f0605090c0a15030905031c05150103020702010801 67
    0x6600035070100c40180c0c203c0700184640d441d81d9031040e40001c004249819440c4e040c520301c01c805462180c070a400390f482908026003c0c04407490010b0700040c40da5003440c0205051303c06081804844105402001241c1d20001c0c24209120340043c031b210000d00c05070f80810801150140d40e0030400784c2c0c24801401c0c020101d404002007444540d40e0394100c485800d5251074662140e880703500d0700a05100b504100d04200e4200309007404000308103401400f002010709000d501c1d25180b86405600f140700706040c818041030401403690b50004454140d01d0aa0480e0302e201c035500000e445c4501028521030f51102e141510341952441001484405483e9442e03a60601e180c210804c0301030341240c0d400036002002d0890000c040750503500c0d410103250080c04000f031242402c1c0000342c200508403951900401d00c05070100044520081c050350055801c0c540012281010b01e081030440c89100003603c45900c004201005108569000c1802641845000c0305085007000040d0168094140c0103404601d0751001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 174383075 1250 174381825 174381827
    0xe01030504060e16170703021f0311032401031104140310110a08100b070f140607020321010e0c0a02030c0a0c05031e060c0a110d0c031202030412 64
    0x8241d8010b4811000441e003109010750762850080d00c546032400e0401004810803914000c0da1690750381c0038484c03000d840301a0554012a180b0540050351551080b03458242d010503a210f540102e00d0001d840340943d44e2400c0208442c07400c0d543c1c49901d102c2c48240f40c5951411580a0b110308540c21070425201410a807800c180500c0040381d40d004030303400d805019500c000318061032080c500008100c84c1441d44400b152100200f0311a401051141506c3d5442024491042d1007c16181c02c02d9105003203441d03c090030702c0d2560500e80040300b403540e00d208880c14808801d030040040c000f02d00d0003030108166150002c0321101c9901080c840d00554241c8040031034001000b100080c0800f034050300459180c07581c1004500c3c0341111550f000e82d10726802c0103041c44103150511604004041041e030142d4106841e9200540390340f405096011702040c006801100540915402d40300021800140c8554a0b91580c0241c05800361800442c00030320a08a031250000c010b1003924003943d001030300850740c9005000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 174384325 1250 174383075 174383081
    0x11060702100902041e09031206050105070b070315080d020d0215060607080c0d030603060b090610050a180803030a0e0601150c030e061c05060d020f0f15040320010309030e0103 77
    0x90990700a511201054458500017901e000d503409401c4000944c00c0080c10000e0032000352010042d000c505051042146030b0344103060301d00950b080303041e4046a483d40c3d48154002c011042c00840341c41180600001c83c001c002c21100c001503640c0d0290b40504039286000c9072160616443c3c1d9481400c02d00c04100c150400c107000d8494184190012460000c4040789149006480040500000e80325501401003141030700504003c1001a43c401000d81405400101d602c030b4900071907420080f01203455880305d44100765101c1408608002c803018991071351030340380c0c03250320445101100c2400e01461491014000900c541220609080011004c8140804450f2240c1c105001d404000c101040d00741f00c2d50740c110007484c25247c0110b211481c144901c50b440709842000f442c9034458031100d04070002585502c011003540e01800c840035140644c0346000a10054a8490500c0c0b1620003c9030100030000c040b211501130341501082c42e218041c00c6001103003a10b640381401000240e00280c500c600d940650 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 174385575 1250 174384325 174384341
    0x2b050f010b0a1217031006030c030506092e030311010e070303020a0b1005091f0506090a0b0304080c0d0f03061401092102130603150501030512030411030118031106070210 75
    0x3c01402902c244d0814485003604140c3d008001d603030312458100b26080d0188180d1003c81c086060510045c0707000700c001078803100024083c0c1c0700d000701908000400340f0b01c5460001c88560241c1061015910303420000c2200e8406483c141c01586481005100c1c00c0d40010303101c0480f036150340200800200755941010219000d03010042050340c0a80104040e52170100c12441030700c7c1004101c490520389406103001c1e01c12036110500074407080102108a80361404190269036a0081c00d96503501c072894032404078031500390041c45c54025420183c6510368800700399405c00c5001d07074081c020181c07580b012051822400704040e01117114440c08010501a1110f030300b004404084005444400c6074010982c11580b03103c559103071584e070b01c20070b104200e0707148090811031a400d88200300e59070440d6240c55035070700e52078008650300714084002030400c008941c941c0029000a4000d00c00b55010034054040a03040c00c00c102c0109155070303650030304c1a90010700c3e02d00c1480c842e8020038040c0600e1020740d004100032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 174386825 1250 174385575 174385583
    0x80c0d030512010312020d0306141009120c052b0b04050a0507031514010305120906040330020a030804110307050303030c04170307080a030203062b050f010b0a12 71
    0x2d11118051805070741005000394011440c06040404e0741000908150300380a51500341480c080e400d1000582d100d400120f01d2308145c0d500c1e40f210410510640d05060154002031080180307844520801c0000d4001400715001501c0c400d40070305050044902d9070300ca00484c500c8075040d5030300960216840e020040c0d00705014905a0750186481e456843c1020659002550f00c04e04004003481d1440c424850500359104148200c0f21f10350543d0b4503da141c2d8400d030b60608691202184810550b0b5a0000304d900a5900ca040b90800061040303a11048281c824a803859800d804c0041e44180c43c00411351006142c0d242d9a041c49980d5559500104000b0a01e90079402d0b01c1010f5012400c1d40b030802c0114061201c00400548403132030058818002c00914031070744450340080c400040000c4042d0700b40c910f085014180942c0b2507683c18045200c0000e040041da00304042d03900b44070380b00700e2403900d43d240c00c501403015508000e80c4484028281d07240d0004054014070950400c0002c1c60303007038460500c8144a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 174388075 1250 174386825 174386827
    0x1020d0e1c020604050316210c02100c0209010911040b0c070503060a09020117072006101a0703050a020109020607110301050c090a030b06040b0603040302060f090d0503061036050a080c0d0305 84
    0xc9203564100010b00004041c0400c00e00844001035103030140040072144414a0807000d80400c379030100303070380c04010301c14582c04079290032003401000e01031020740c2e000c0c040707000825407511440e400b00f030359800c4140302d210b001e400307000302280030650640540180190117031200d40c000f8004183c803140340031009100c101084614811982ca0404842c030000318100b032907004210300d0501d071040c0c0382d4101c2640d01c8200040400c146040c41e0900450983d2021a0107081a58480ca08001c040c3e000d03044040d002035120200187e0002000110121610706100c160000c02a50f950000c0e96807840c172400c032600d944103101c10010000540c05090f640e901c4000500040303440314002011409903042070718112b0243c0c004108001034034001c00003440c5e101e4070245c0142450381420102900303920002c1c117042c1c018580031790002c1085006400c1515101d030a080300d0007018464402c801240e6000280403450304004120015082c0303000c900410a80751207001800300c9201c000208641d960300140101d00f8060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 174389325 1250 174388075 174388103
    0x71a16030f0905030105070c140303131217010e0108060a0c1e020a02040906330512030909010902030108160305070e280f050903030f160201020d0e1c020604050316 72
    0x1000c6c040d00d8000d0245480e0443c0c202c0d031918100c4100e400d110207050b02c5a10070301c100030134500103c1485040f160000750f402100d20701c4e420201c0f603250112550322003510b243d000019480f231044d50094101d49032102a034105d0703140c008001c0140d508000750540010341700c0c644081e007800b11680607180ca02c000d00441d02c41d00e0581c1d020605680b280d0000351402603071928541883d07a040388070044007800340303014a4080081803140207032200c0716004250264110301b4100000d80002c0044886c42200140005038561b5139840102c040e500074080e5081500821510807590312140b480c003070071340360300c500500f15180c140000640002802400301c139810b035010540b06022a10642c2084101a4800011501464182e407000c00d43e08060302d4800154410000c00100501010810340c0203052040004003d159840f000c0380a409070740c00d01d40c011450103008200504c0c00040007590380c90700000100c410900340300c00360b8841d141120040d0080d0020081800ba02c820388291103400b9228000310708240b4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 174390575 1250 174389325 174389329
    0xc0804080319110903190f0b1023030c0a03081e0f04080c030601170c0d1407090618020a050a0c0804030c0e1503191112010509071a16030f0905 63
    0x550040b03035042c1c3d064400110310078076003000e10001408603092032140710300e03561030b0341c8a20300100002800341c0b6081c0c00201280c151003c0c90901001004021844d07000c100d9100307080b00b0494001c08115200b84628000c034001c909146c2e0352042101c0d0040c1000d414080c4803a00092001041c0010520b41c400c00c2081c802d031501810050000303840100014000b510200d001c0c18540003060308440700c86100012225010305000500020350300e010b580054504d650351501c41401c66142c11054258001d0340800700301982d40c0c3e03020000319981074040300030004181402c02d0480c8210402d5200148080002c040c3c147c4c01014000c03903461044908601e0326660781c0b00c00303030804da4507001100480c0529040c0705040c10311481003403030900708034003401c091040c03a001440e0581030200020a803c1880b00041d820f03541d2030008200714017182c4001d124514142d86415240d40c120300034003840c0e40243d80030300c03281c0c0652015502000d00c14031014441c95220784040d00d0751104810080100f0500340c0b8041200d13 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 174391825 1250 174390575 174390581
    0x6050f0607080c0a1407090608070b0919030213020a120c05030414150a02120a1a040f02070b010f080607030b0f12010906151a0f0304020121021812010c0804080319 72
    0x420741400034103c0b80d1f0030419080e041e40d0940d401900c2c2380d8400082440b680012404980c50f20100321102c0000c1010445101c022080d6640080e5104190346a404101d58054000307041e10b245680d60a84290146504002203894034920f9000040083c800a00011040c074a222006103445080721000b40600744441c603074080484150b591240c010800780800548101d000c1d0b00140340a605101e00c0c0d14100102114001c10310300240329036210001072841503400c3d070454511540004c0703d45001d44c0c4845c02c1c1c1c000c0340380034800c0f80018445c000c0040e60b10f81c8280302e2469100720042040f81040c1c0030758200a803204424005410385c1d50b8881c3c080001400350b1284212090381305421000b500d1601d080000c88020041c0a4409414104030082c0300c1421202145d0384150f090030050201014008012102d1214070040046a44001031409480c0703500c0b0201000300c8030403a07221100401d0441141c0c245c51243c1c03004004118900c0c045000a545200a1940714901e40302e56840300c0f0340c0d0003606007a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 174393075 1250 174391825 174391853
    0x1103010e0606071b090506010e1f090f03060c140301120f1406040308040201080c0a090b030a0204030b0106030603060b040e0319020c18160e1f0e1008060406050f0607080c0a 76
    0x144804d03900042002201d20f01846500600034240b50712681030b48400704004a019150440701584000030f26450a4042c42940b8050401100301e00c905a44a01d4568000d1001840000100c2c6800c06041030802400017140d05a50301044414003d04491340d035042e1042405d40205c820125103242c9042e03020040203010301c9240a6a5a5491810640009003103a00050720011030141e04001c2c00649076042014002110413101c4450383e03a644806c3c024000303000d03c0d00000c00c1c0e03090a100000318241c1c903070040401e80340516000c12000c600c0008200c2110041900f64005030805e010140e004680c0311000f241c082541c3c0191009140303040000303180035042100301c1412003c1c41080c8041d80c005101c09180e00d03401400d10109401c0c05000240d0011602c009a031101d101070300e240512144603894401c0700103c05400e40e0491403001038080e000320001ca1f8014003540c90300d03030001110301c0d19915004100c3c40c0034000f285842c002d03880b4451140d00002919102d0310034101c2030f000040386030b80e8402e2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 174394325 1250 174393075 174393113
    0x4030b090c010f0521041e080a03150e010e060406030b100810091e0c0b0301120302010e150612010b131b0806010503010909231e011103010e060607 65
    0x124910040000340454408580c3d070020004244449484c500e500da0002d08009080120108141d64071f01c0c020032412900800d102e086c1800e8940c02c030800c14804003030300b090700b4181ca00748004180b052a15071409100d1080c40e0300089101c3c01003095090111119030000005003000c01d44a4594503112000ba01c01c1d1109131060901c4081040342c01028400035072604106041401082d0468903004400000d00d40d4041d9010f1088400340100460100ca80b40101018400c0d07681303035030f56088404030130203d00c54280c008d542800d011000c0d004010601c58032502403101c2128113601d4040601004560843c900361b215960749044640c41d5840005d80c0700100c80290000c914032078100c0c0158000206028a40c062042c1c09003030101c207a8101c400e49064801558000032107290504049540840030340003500030303200c85041c81d0100f400100b403103040f0b846105040a58000000791680c05c070340c143c800132100f001041c0010b0003410f4a00f007800380c000130018082810850942c0300c410201143c0742c4080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 174395575 1250 174394325 174394333
    0x30f0c010f111c02070501030b15040311121005041a041208070917061e090c130b040513060501060504050a1502011b08092b08060411131a0301050307090c030204030b09 74
    0x3c02903a05010f6002c0800080d120ac0030f18034142501c1142034000d60000030080180c2c8060f121941e26188407004150700103000701c03a45001c3c403509200007000141c4d000c2e2043c80e4205201a2600300700420b09002d550b200000c004103001c004012034240c08081c04110402c0000000002c1c9010b41d2517000400005034400340c6240e09040d6441e6000000741e2004d540c84d80000c40400000c1c9001203214902d140342a540c90750100342c83c0781800010101d4024603540245002d051125403045001d903544481c0c4200020800d590b2254016200ea008a2244540c40343d02709806103c8100446500702010f69540008102c0c0800036442ea10458524003506000541003000c0007103294041040c10329811100f02c25220103807a0800046480e660485032005001e040c0d4046400b644956110120b0700381c2e0112411f4490810b041c03005900b0300f142c49030309428000c2041c5c090b528100641268100c0e94003c00a00b4807514040390600503140420031041072540c02c0c0000000310340300a0300310740f0601282001e8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 174396825 1250 174395575 174395579
    0x6051203030a1e14100914070804020607080d0203040201080a050622020c0303010605210f07030b0f0909010b120c0108070f1404061e021605040209040204150e030f0c010f111c0207 79
    0x102500b200329071b0210708620b04040420700703211410360419412002e2480c0290842d43c42d80042065845003080081850800081144000071503502450049101766518440e980300c3c0c4182a041d103000351292588411b001880f184441e0000361005c042d42d11010000d0308041b402c0301801d0668109900030380100310001100c140468115000b8a003101407428099141d043c03824046440383c20042000c1d01b85690b038801003003a56202e40104190b000020682505454580781c018041c10350103a00500a034481c00303040c0388100c0702043c42005000180c0d6513810b190b6851204540a6601030030000c180b02c0380016000c0c04946440041c4043d160302c1c1c5541c29107030032100d6103140000ba8a03225204541016104d2000321134274183c11011940c00710b81c09a150481000024000d200310b82c4044003001c00303031215940081d0404030300660309400710300307850091030050311543c1c8481030f40b80740c03d00140b07160300e40030481c60241c06080e4854040400320f6200c20b88400004010101140d040c002680c405201 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 174398075 1250 174396825 174396841
    0x1150f0e010f060f03090f0b0408040609080604050303130309150e090108030a080a020d060e130507080303040302060a0207061103040309150f05160201180f030606051203030a1e14 79
    0x6560040c1000b48400040501e40703a070040c51034020201050400d40c0301c1e030b00342c020f020a10b1082069142c010100c205039042900e0044242d501c1489028082034103c480051440c5010400c54071940c0c100d40078500e107903680d10942c6c4e540c0c040c00c88120148082031502241080702d095000c01c0d803040395204e11581160420821a00f41c82c140c0c07041403170754010000300c1d01d01c50f488489560020700b1f004015171a02d83d101d2024001d401d40303820080440c0241c40800200c036040b6260b15010a0143c01941c0384582c0360704403107031a8402120b004d005a4000300226100c440c81d60700400d80305020b44030000c1d031a04034078000c803015030042c2d07401d4000500248040c0008900c2c00140031035000300b41401d54083c0030b00300d8007070003d02520703942c02204d980e10724000e000e40e4010b03204000d00981050211440384c0e258079404088401a001c1610f02d545801004034413810607108481c440b500300b6005608641d18450710341c0c042c140a40b11803070f0500300030401c0c05025449026600780750a85000c0f1100314030703000c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 174399325 1250 174398075 174398099
    0x60703090209060d02010e0f01021f05041104060f06050f0d0f0203181f0e100606050417030a0804020d050705041d06060a03020a0308160f0b040203190506060d0501150f 74
    0x4560352003044c10710110b200503038000f0161070030818269103181c000200100180c0c10301c200c0140c040c1c98001401c4a401442285610051045106103903d116102c0850701303010858450f0300403124080c0103000103001581c01400606030794241064880e281400200030102568511a0700c40150b540220a000640c41c46200f5001840708000080c90b04000c1600210300312109110712402a5075120b503081068841846081c6a00000d10403d0000555239100200385034481c1c82030500001c0f81620103520800b012085a414802c1b5a44038210354485408000400000050856a0b441344200000f50741d2194043c1000030349601d2105106009003400403800e203240201400d101c0d011103107082c80181d03a2142c20a09490700100d400d80c0b0f5859144d00c11a000b040480c002d000201801007940810078550140d0748110f10039000d4078403011092508102d80300d886a0010805d4103c0c0d07002a490381004021114003e0090f800171a00c245515581611111260041a10001004014401601a48 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 174400575 1250 174399325 174399331
    0xc030201120902060f090301060806010602030c070807080a060b030c031b1c050d0302030717040c06030b040b03120309120d1a0d1109070509060a0305070305010f23040e060703090209 80
    0x105090005140b1680011030522903104c14452a0b5804038104040303803025031140340688280b9007260341d156112007020307549070085105229a8400e050021078500d00c0420040c0c04c40d000c19008040358017865840801400001b81050303094403984850340e1081d6010086803107100c05944060700d03c511b41c40180241c7ca4100d601c103498210381041c2840015000058086449841e49401078a903250000c04071000803115049800f200a10010700c014030044800250840350341f0348040281302d203044107100c259092100c1d0300e640340d02300000c1040428000002141d1200703400c0300b43c442d00d421803a8240c055411290110035000d6540e800c0165001d0138090080142c40c0032581d52405411996817000101d20502e81d00e806040c50b4004204010b00600c01e4035801c1c8001070807551034401d40140100140012920500003070306040c00082d002d171601d02151706484040b8840141926500c07040000010508611604155034041818403841d0601060380101c0340c0d0780d004113141c81d641c0104042a0800307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 174401825 1250 174400575 174400607
    0xa0e010c0c020a170304140a0506030a0e070e0705070f14030a0302120f10031203060504020a0305100e010503101d120a030c05040b0301121a09151b0f160f0c030201 72
    0x4c0100e03a007100000105503000c40f60800401301c3d82188490100e400e800480e0320058003d00080300340074044209400036504e641140c0100c84c0181e0383c42c041d01c0310700706050310560045202000400041011200d440300032500070350400c81d50451540c0b17124a59440340d007405000940c0450b40707030020280d48544d9500560841181441070515000c0c0021a003080c0c48014020810b0038450706e0064001e8100c180200002030085446604110002c1c1c040c14049032400365155031500c0100c0c1901e40a40010f042c0d800c05030090100320306844444000f03010043c0007411011360442c0205049038208910901da41d10910700940701c0300c007500007070152040c49c0c5d2140d091000600080c0031510140054a04541a544000c81c940d0a82e04000a5400c1314400903006100d003641008042480042e440e41b94141c00802100d2903030302c18003070880b25441c0c1001c61003083c03810425004a40800c03c081d000604084030b8804005440e517030740010500194100311380081090404109640e04049803035007040311 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 174403075 1250 174401825 174401849
    0x90306051b1c11031306050f1902070f020604060203130b0f090405040221030405030d03050f01030209061206100e0702010b0a092403140d0f0c08030a0e010c0c020a 72
    0x1501c25a0003690041c4036081ca60710000010702e00c403903241d640007901000b0000200725501d080018904142d240c2401c402d682e15070910000c0385400b01407041103032051400c10030407a840070345c0c403203031901a5018482c00d03508075107040c0001016944a5000b80020442c680007940e443c0c10070746070a11000f20690108a14a100f8010711000041a504036206502c1c122400502540c651000034140d50040c910b5190700f101e118041c0400510000092003514412030440720f0b28000d260040381600c0b0102c4609500c450007400410041c00c0c04030003141c20513001417138002c0d16034560303032114a041c404407140440401030020400c01400f80d10801c0d50400e08500c001d10280d402c420120708181403034801c0e050808c0c0d85044403041402c1c000354a4a5040c3d40005100e1415640e0030031640c02c0100300a0031003280545111244014000c1c0741507000101710381c80d810080d200701e80b2164901c0e0001070610405175122030b456485c940c030a100d4041400f541c1d0f19040725050342401070014089590308450001d11fa = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 174404325 1250 174403075 174403111
    0x2030705030f0c090a1d0a0b010f0605090613081c081023030f1902030105010608090a060c02010b040c0c03020c01050c12070f080705070311040207020d030e0f1009030605 75
    0x80b010803840007030341c815100c04400b038880300817482c014004210301041c0c1c2c0800c104d41c41c101107400b041c585000c1e07004640c90444ca90302c402001e404400d10303124840100e0002c011130450383c00d101001e0013417441d0800006180301e0b0f98034041e07400d1982c0c0e0a900c9002080c40600e00c82400d4201100980120b944100114210b0402d03078084910102081c50390124046071001c4900c0380c0d420000307404030b07a00c02c41c15940c00c0700111020b000280d0041744124801e50034100080742c104d0bca100c2c694401c0c080f15004010703500068550000a18410311808115525403804000c1a141c6000700d0324014020380e00c0c404c020800d810001e051000d0001c44604001d01004498520500041c440046c9002140030039a900c1d800e29180c1499021000000c001002c04a45a0107002d40856094100c80c0950780d030004c010041410030040f84150740e03000790301181e1a028040860304c0780c2c42c015105a00030f00300d072102c0712040c400602216003120000f00010054441881008090702070b464206000801a48542d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 174405575 1250 174404325 174404353
    0x9010501090b150c0715030e071e150302070206070b09100b01050a031a03010908090a0602070536090f010b09060f060f04090c0e1002031c050c0903030f070203070503 73
    0x1280390580c8a14071a0100700e210b0384d04c0d81409041c0c01400f504006041408030340001030080e04a65031400b00c14003460710001210704400c0034040e40c0c10540b990140c007060400301450180ea007a8a8070303104059090041c0c0e00141c840c0385c01000360354094401c65900380380911220385050f0103d03954800aa003803000040b402c2e6000310544480b020b0303074100414640c0a1280c3c0311010417621400c15410760070100c1417014440050007c00541d61b007605c0050100f030300c81c1c40a90b940d1300326201e01c40d005822080c4079034070201d03101c256400c640d40351b10350401c0204a003010a0700304102560607141c907402c00c241030021000300344a081c21141d41599200145d190400004ea0f0178803501c040b0030b0007010000340740c00a4004020464020b402d1a0780100444110300100500b075095885440c0e000b40c00100c80018018000000e03502620320a000400300f03c64140000c00241002810030840080140f041a4980d81d0502c064604a44140c0800c2d8849803580101483d10742242d01030390003900070b080174000761 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 174406825 1250 174405575 174405589
    0x7150c030806060a030f0906020c01200a080a0b030a06060608100812090102150709060210061809082b0b0a0303020a030c05030d060b0309100e0307141009080309010501090b 76
    0x810b00484141e03403600910001a00035090052807a8607081c94040c040c02046075a43c050081201180000c00c109a0151a0100c800200c405882d00104080c060301394424170070074286074426140380c80441e87d81404800700b0329180782c00804440050b02c0d0003003400159801903c0a80c17091810301406052890b00300520b07240c442105a0007540d50f400201c92569900070040143c03030700b640c441c101135a460322ba03200a04080d0b00b0f0040c980140202c00e04100311340c106004880c1031300c10b0b007003034010050a2001140c0040a21890840c0c0001d41400070300035403081000c49499813540b80d8650039110300781e60403103000c45422143c424414082c182c400c1c03012a6000915120346685828611201482410124558050803011124680c203000c0081510b44e604000396016850040031150941d112942400941c0c200003217035900359005010b03803800300707881c00d0003240040c100c401a2010072070f841c0406015903144881c1a5100d04000080c019589424419580144075103403081104e01c0143e4001444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 174408075 1250 174406825 174406831
    0x2040b12040615030b01090509240601020f01020310050a051804030f140f0403050c03060f130807050f010203061914120c0306161d090a020a0216030507150c0308 71
    0x80e00040380c00202040703080d030f101c1ca5002c0d08a1469120300da5403413800f20344103403090003072012190400d8007240e03402c2c000143c082d40c851903201c4114a4010000c400840e41403004003114114400c840c0c441c03190f4a400e100450203a001c9800350801c080c1040140400b1541075445180942d501080c94003a80101205042e0041da06213081041d400c51802d00311002c5250526140a800b00020314100701d002e548001d01c1120b100e0415200900d290300c08040d1a000101d17a2180c15024000015148000740445945902c0c840c0d001c560a14909454951401a0722200e10200c1d83d40007040c0000d80c50502001010030050201c5060070a0400700d8024615a00e001d280d802820305203425880c0b003000b40071034602c90030302a0840b06945071402c94003205031920030303650b070104080c0c01d4000d0607042d08034200219520040c0c8a600940c4580c2d810764000d40c0a040d82004501030f01c0f152a20007a00054050000c42c000c1004145050038040e50751050b040d28000c450070b102c04ca01e540d4000941140d00564 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 174409325 1250 174408075 174408097
    0x4050601030618080c030406030614030601060e01171806100303170406090b0708060906060a1704050a021002160e06010f0e030c03030d0e0d090305100507180602011e02040b 76
    0x10140e0503030510000300080164014490b00d40805c0303491034802c00001900488480d990140035840d46c524482d121007500701540e80c0c05401100c01030105a0140c04405040c035410701d000c00a40b5100e6040e8640c840099860000901210301e00500f501000c100d00d0343c2045100080c001e401d40783d55405008200c00c40394001030794000d00d00050522150b64895a061a00142120030350f140280008005450480d402d80c414001c4001151070b0782004e00607180604e04a45036030851140c41030104012900041c012203080c416903550f600161034800d40788201c40c0c5c540c0c000305000400f859076107000854541000d0032810140c400c001250b030b48a040d08100d06000d0501d284040400c07408281405240201e4a4051100064218800c1c0195009003c040c0070001a100300b482806411071b40740c00d036444080c015610002241064600f16031040c0c0d000045400c00c51139800760490300a0840380650b101c003001d40d548030500a031020261108001d01070411100b103203041d0401c0340d1511140600070442e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 174410575 1250 174409325 174409331
    0xd2a081e0309010c120c08030403020606010305150109031b08030708070b060306130b0405070807060914062d13060f0206060409020907050a110307050d020f15010909050309100509010f08040506010306 88
    0x5e400c02d03010703184c40080103800000d016a0ba10700707402c010b941c403030054800714002032402d4002140650402503010f120138059640c1e08aa034919200e0704040c0c0c505054030203908500f4070700050188000c00c02881035510901d0f101391038140d04e0502049040e001846d49000f501b01e481080071007940008100f0581e584541900c2558581d8104640760010507000074050344201303140400c1c1c250304001141d048880021800c0c81c0e183e128170500c0660b0041036501100141400c400403070358034001041c1c503000d403044d5903090f0801100620038203480d80c641e030200e00811040c046c041031041d41070042e40d51058040c0c1e03080c001941e0070740c04a091824003c3c080380402101068007454148100ca0404240d00070500700d98455180c0d08156407140322500b01c0b000503103e108420b1202c0130020954100b101000a0609000c1c7e00e4058103034058130300c1002c205c810380010080b03100b050b6202c1164a90181c82d55403059114603503500050050b56003e030070722051040813020400002d84c00100581541e500c40c0001c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 174411825 1250 174410575 174410603
    0x2030105032814010510060314060103110f0a08040b01090e120306040f060308041706010b07060c0504050303030f0103110301021602040b01030e0d03020c0c06090d2a081e0309010c 79
    0x11540030564000e0081c12010320f00c900108080c41504424010b007a40082c0c1c4c0e2030301d991018282c0403104000c0b40c21400b0303144500040c9880d8040da111281c804050103905250030380007032941026920824214001c0f1b0001c4043c8424003510300d04440c0980310401d4104080d510305c0c40c480f030b900d44092400c010703600d20010004140e612542c000c0740320300000d80024801c0d0341e12490700b001c241d0040e00518602d60000842003480ca0f600243c568100c0f04403a14407454074200c1d441c1c2d5000b624440303420006001d010440000c554400b080210b210703140051000d0b600d9411464030b0010780c140d00d40c000e4403d03801403109100b03481560065408283d41180c0c0012100c07050f1006034040c0071134100d00e1182e809601100c0020f150140c00400408001a0075110740480b08010401c2c2d90060680840d0401c1d600c1084000003040c0400030355000e0292181d001c090100384091849101403500803010507000403640c000c81c1006400303403c0000c044000034508154071a00000e2011000702c80141940c2d0b8a0380003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 174413075 1250 174411825 174411883
    0x18050c04080f03040e070e0114071a09030307030f0615030b030703050d050a020d0c03050304020d0c090f060504060b0901051219091a0702070806070f0327020307090203010503 77
    0x121802411144180e40c48007042c0e0041a803030390444e10800c0403100300a00080c0036148034102a62034007405071205441c83c090031107100d0603600b0203002261202281c8003901c1900d10782041c40da225440f03c80c0150f90300c0c90591801070559845c042656502424040c0c01e1040d0f030411200482004800c1c80d000901d18103101c00a0705c1c2083c1e03a07002616900548180b0594158068010130b007903c0079400b140d0180300624011554241c00c024040c0c00140203102060044c5008210b01c400c650040b6a140da400e911442d03d901194145109856000c0d40e4400800c040e0505014010040900c22609828183c0010019080f445080100b00b000d1240310000b50b10b40528295600c1e041c001d81d44104680c041601d01007828030000070000f20103910540004211078400107040d02502d103e6406000e103511015800d42d01d04060b03208440916440c3c10b9000c08800200700b059034040c03801448040300346810700606040c8805034102d00101c030300420051040303881c0024407204051140045d04525440844 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 174414325 1250 174413075 174413077
    0x908040501030c0233010803040f0b0a0309050f1c0305061f0c1209140306062d1503011a03040f0305090402270405010b162604031a07050418050c 64
    0x140d00300404071128021703801400c034800201c000c17640241d00c0340e1343d80b0392a103195240900d203d440300302da103092070a2241a4648002e4001a41e0360b01700411000b0040d615913051241014109009501020f58000c40140c44210280781c0c01940c1020070150130103202040c1e1819004803d900c40380003040c0c00030410303881820301000315a040600d41c56030040116000305811103078030401d104040d8141401e5400d11380810f034503004040003400143c03140c442c0b9036010812607140c2c0140f4180000041d000b03115032640c1000d110041c4035041011307580d40c10b10900c2c422202d203007400800303001c03010f01c02c010010b16030b1100750309106c4e01818245e450300d002200260292041502050340c03100003020755107c001c00c070600c100e284601142c040c0540e07a25803981c9110b030b000320400900080d25400245011607901350103002d410030848d0316048004c20b01c41203000039510030350084481764498082c82d918818001555500b042451922600d0a441c00c0c18103c0112080821200107a03911070208030458901c02c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 174415575 1250 174414325 174414343
    0x60910030b010b070c0902030f04020d1b060216060906050a031a060c0c0301112a0a06050f0403080c040b03220c0801061802211503010203040b01030210030908040501030c02 76
    0x760115a668503140c00c01c207540c0148404440ca000713600c001203410f0015000392413042c15000e0036140c841d0344640800042c0c00c6107010a44289085110300c0f411001a0300050002c0c0402d600203102140b4020620403161800c0d41c04801000b050700c600b884203a510404413035810405103800b007020b441c02085c5200030903007420750580c4034800080c0d4100c441c00c045400300c0c103810214001c20500d8800004c1c08124400e01d640a86451500707800e850601860001c21080c0300d01007003c8900600481c0c0d208400c5036000c0d1101d040d104113000411007010380c802ca005904c801d500c4080c1e400e00c0d00d0703c1680d03442404040d1800311140c15483c00000117011030780c142d40100c0d4026039007092550707031490300d6402800507004a1030081544810024180d09900884108080117170f80154020700b0310012100e0884090405000094080600b540075a002d002450007280210074460b03440d4954410416160301143c1154103142c1044042b101040410094a00701c560078203000c242428000f4049082c10190 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 174416825 1250 174415575 174415583
    0x31704030c1b1e0b0417190b2505090d03120f051603060305030f030405150a06140103020c150615040906050a05120709180b0a0b040b1e040b041118210606091003 71
    0xd04401703403c1c030200b0508c0d07074002d003041c1e4149503640e001c520134824040e600903003140c0818000c1016000070b04018074246c06441c02031a00c960642211891402940ea000d694482419290014040486e22600010402d01c00c80c5c00d007040208d286598280e240d00800a56056850022001805118040c004824518004032000700035203400d00101d0028100c40c06110203035044075200d95925400b0340300722186015030000400c2ea1206040eaa0107244c90300410b125001a04507541c4803d500190300a4401707450280d0001c18010700301401d01490740b002d644400d1141003820030f941154900030541e00140c40d01c085020030003842000c1c23540a091020800200700000040c10031108541952004006950845060080c4000c43c42000b2402e000c440bc0d011400381550b06031107040c501903000c180d41c140060000304009848101840c01c50304007003106180c00b00c444004960300e182100020303003030082801d20f1062480070075a403290b0340c820007089540600c10b903001054103001c004012200443d80 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 174418075 1250 174416825 174416863
    0xe1e150f1c03020f060702011a060a03020408071401020132040201020304080f0a0209160504180b060a03020a080612030702010507020f060331031704030c1b1e0b0417 73
    0x1d94074009642d0703450315507001070798010382c00445c5800c1d206002d160202c0020260070035044502d902004066031000500005042d400c010008480d4014007a80000f040c100104003d20b110400002e800e4481d8444040b40f001c03840d50a072032461140c21442c0b81c410fa5240c0d90f50099a4541c40141d180d4400c0d9040340c81184203500400f201c030000000d00c81c2d00c007032081e0b41e04d075016110b0903d04071020040e0110400032885c148018086000f160605006248004c1d0021486940e480c010668940c0141b10000c0000d4001480c0c4882c3c64002054070340001c01035841c0d007100ca0300720f00d080c0e0302e034001d11f080241006170026004095550301000c22005c5c082c024021540d070b081c02045d401d41c4520014103900b00031400500404c9403145003603030b02501038164544180391003900e80c07004a1014000c00c101e0500c060713000041d0124240010341170340042021912142182005090103101080c04c3c0780e00064824081c05000140c5044140d40854500c14004100100341f00300b541c0c10302c46507105141005103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 174419325 1250 174418075 174418129
    0xe1302030c22032d1a0a0b01020601060504090b06070b0c03040302070b070b01062001050106020c0301150506090402030402010c17030417030708010612020c0105010e1e150f 76
    0x2081001000070807107141850a01c50382c0031681c1d8040d101240301c0a05040d11803c0c440d05103040e03407504a138000122142e42120550103a9410300e0661100e5810600f08030034908110340480c1c14420400c0b003140900090119615100009007248910b006440e1000d0315030020a0484d10b0310001c1e90741099020350039905ca80b0b0503c2c440340f6660800c40c0c0940062180040000704040d0394002c440716030b904000740c00300907820300300e09490b60300c2c1782d1803001c1039004045400c040c4561b0030700c00c2e1406022294060450000030b44105829216a04820100e42020000c00c0019540f01e4049500c42801590007507107d0780c8074001a030782c0c5106017030301a0040c2d044504c818142994400114403403840b030910850004402c28100940780000c48414010a850307500500c4200d005815001c2d50034038201e0054501104800060f0943d030081c4c0c04540102d1450341405008540045090348801e08040b00f600640340c840c0d4a000094011182d150059100184000f01c030b07119100d44001d001f01080c104085a4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 174420575 1250 174419325 174419341
    0x1926030c03092403041b05040e1b030f0303160c020d1101081806191b0e0f03150a05060a1706040b10060c0b090709140405010f0203010f060e130203 65
    0x1a102801c1c0501c1140a08003504520740d29148803602205040180da00395907903592034408400d0034016180106c821068001010341e114091000e41460300000b13060010800003012800740b54451549102c0c0c3c000e0050485220800001c1d00d40c40700070f40b01c1c0108030586041c02990020718400c0f010707400c0301c41550180c0501142c0c02d03200c800a5000e80c2c40c002e2a0307480110400100b01f10210700301c016002200803400e280c1409448004441840c10000744001086204490f1142e005164402203403141c0707048000d074500803038480301c05c000903000b070309070003501c1ca00c001180100104028031447c1e980010600c1078845a0502003d030005510301c03d11800c1e034144840e03880ca0111000c85e8400301148c00664164090850b0740b0840b00c01e5122130490410035590281e0300e0300000c14500c01c61090b08070000360600e050241035000200e512540c0c1c0541814103095082d614a524081d1030ba03401000100029154214100c044074224034103030003910030100009010700d10495001c01003c7c0084244100c1d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 174421825 1250 174420575 174420577
    0xc040f0e0303011511060103030c0303050601020c1e01080f0603030a2007030c080f0114070e06070f0c05090a02070b040f0206281211090d051009030c020108061926030c03 75
    0x710300c2038031070300a0864403d000d06da840300d090000070000348a090310000000d0207070f004079400c060140160741c5040031200108442148040000013440c5400d500080c0558110b4496500070010701e60b00c458500d46000480c5e5644588044101001642110b11109680e15228008241000419251103503a6403d2090b4050042c0c0030b40c00c0e032070240c030404c0340442c0710510401c071001645a19558040c8da030303d202035407078804d90500da98000d4410040880021501201d580000e0b214200642080c0c0c10401070201c20b94000b400041928030410100e4041511207116940c040c0d0f100300d40b1001501da0f03101042044c042c9100702d88405080c0c0380c00381c0c040c2c440f521070841c0d401915541c0004a2010f503072603400fa07400e01d40d8400d140c00c204109440050500408045456020703104032101028503c813001c04540d9046ca00350300003480100f070383c800c569014941c0c81e08102d04844003162178101d034030070416041c1544200c81d110200d01e500c400070098240404141e0100c0c42044d2629110611421522 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 174423075 1250 174421825 174421859
    0x907110102070506160f020d050903011d03030901180809100c0510051609180b0409050307052d03030a090606150503100803040e282f09030c040f0e030301 68
    0x48010304444001015111b00183c100208031507004101844819405a07441da010420b500d4055482c1c00700300d0035200d0b8000c010302968102c58000d654a01d040070b011030840d5030900303000b160303821001a050040b42d4850240c445400e812a1140c2c17104881c0310068401c1014a45c0081941c081c0346910842030000d64069403085c4240b042107500c42d00303d0322017100c0c81d810714002d07240f180d01c10140c10300c0c80c10701551041205000c06880001c1022494503000d103550804403049510354010307418003582204c00011105801c7e990089510003c40001d001900ca000052102c140190f9882c0203801b4800e60381c101c5802040844280680d07050003d000803c0b44d407046440600c4a02e02e0240010b5682c0c2c000116000c44001d103901d0005503c60160f81d00000c45852000001d44103200003920402605216445c00f07802141050b142051017000680310a00034280050702d810018411608540c0300440c5503070500b0811140050313005442440030004100740d095041041c800400089101d00d40c0e40e03c0b01d84 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 174424325 1250 174423075 174423091
    0x90b0612100e09010b1e0123160b2a07030c0c031b0303030b0612010302060a02030d0c030c0e0301060e06061c0c05030702061b040324091110020703020f0907110102070506 75
    0x7040c0081241140e041b06044100c550015404459501840c40004501c0b036145854028440c500000b119841141d60b82110065802100840c14081c0d0712030300e005125085500c0c6080003078040001068010b9502819401406020600e28010100304968400201859004440c0d020b0401c140c0820036a1049074003044001c40c0c6000c0700f18035546490000d541090100059084060382141d081c07220f250041d2410406520090051902e60038483c003a0080400d00d80e50300090580c0d5008005004031903d0300780134003e9160100030310a01c41003a9071142d001106075821356503019146071000003020030407440945507140400110782254001d00460207039449508688e62502c8004060154801d10440b040700c0c901c1c204000c000061617420400c503c00c401e11448402c031555540301c00700741c0d00e40301d5007100d144098000303800f01482e0094801011150350b00c020040d250840d80851050441c80380f01510881c0e41074006200c4501c01c0300c009244d0440f1400a644540191034019503564064586403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 174425575 1250 174424325 174424339
    0xc030c0d0f0b041d070311060d06120b060409030206011a0904050406090b092b090306151a0c0303010b0c01090c031104050112020d1214160c090b0612100e09010b 71
    0x10f00b11340e54001d5880310703841d40c80203010080e1844d83c803a490301d0742201419401c80000c3c003031440d010f184c610400703009042d480440810603580d0710784000394440c01840071b8400c80c03a010703004000c41c3d40000c3c8035054a441e646e940e60401c00311a1040446d020b1046166441400c10013003108125958019034000d80c42a4040511506d64103000340d1102440d0b14408005102c004044e0100c1030700d036541c40414001c2d82030a00074580c4035103c032426219407100c0310240500d409001c2140d01c00c40308051080441c01c0302e5041c20300c00d10a4113603440748418031480002c2c12021402164080d000c0d4042081241d00085031b03600c1c0c42e52403030b28804000c0c07a0342001d4070aa1402c0c0000442d4050b000100070803a138002c0000002e03a04c1f40ea94000003007216100903040112141c0394504000340e01d40284000210454090403101051400030390640e0603800c4070260701c2c01c002d91880542c0f0b0304029525140c110844542080c1d0f50410709540d0460741d948035a030314a61607014419861320650081c02c010303200b90340715 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 174426825 1250 174425575 174425591
    0x1d0108091f0e19030c080f04030b0c07120801151223160e0a060809010e0d0e030601050a06020613060e0d260105090118020d0903050408061305060c030c0d0f0b04 71
    0x250f04071594040182c04115011003440c0000c40390002407251405c082a49410703e41c80391100ca1000c1800c0700e202044001c00210f00c014410400c40e032602000c61440c003003030030b5810100310f101300192150446061002c20032000300c00c85c0241d00084030f000f2074804401d0080d43c1d400901c0a240c2c0c000d88041d1030344001600384000440c030a07100381715000800307407007030250a10b001d1003100d86000040100e1320300e56850107039400c044414000c58052031b03c141e0b01c0c184402c150f1802c041c00d088044c1d0109110703a1001d0010081d89402040d920b81c80061b8100011030220310b0f09050700035141050410405010350b42d801015960400da00502d4400c0304a540c09590f0105070a00d0749030034080c002e4561008034540108010300313033028030160824450101600b0041004840415900c0f005011000b007000414140030241040000030b62003005038504510001207601e03200e8445402524401c0240f41c0000000e81201c800c1c03085403c940141c51040103003042c440e0304100140301c80d08400b84528245010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 174428075 1250 174426825 174426853
    0xf0c1e0c0a0f0210110705060a03020c0a0b010f080601080c040b01020f0f0a062304060b0604030c03060203150307033804061b03020403030509090a090807050d0305071d0108091f0e 79
    0x400e00e41c103203174004c00029050104000054100300d081a04068081024588940b001d1203072805251150001d0305031941080c900c4070680c122508420170550006004120a00001030880101071054600240d40417081c00103d00740154600d0f0b5910f113125443c43c0c0c0481e984000f85c2e03c1c503414001c03a400c0012002452055514030001e04140030400562400300e00070070550b0340402403901c0d0040601c2d1620380d0b03a81d2952442881a8020381d0b00c55804010020244040355100300c20344070480240680608540d603060700e8016107076242c0368014034510200c0e91101040d0300842c074410604150350451030b00b0700d00100030b8440340c440b5078030341e59600079460502e81c00780c003d80d01520342c1515030f2410030300001e0500003100b40c001e00c40c90095880b64640c5010920450050a0290050015040b04050b0000c00380c1524005404002080f03021442071513540c403200b01105400c0003d18104d0b0441e1030f0f02d810189016024032540e40307200000390040418200d2503000034a081c04890a03950b810360302c1c0003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 174429325 1250 174428075 174428087
    0x9050f0603061f05040f09051008120304081602040e0109140d020c090c0405120d0801140604030209040302011103090102040e0f060d08030a060f030f06050f0c1e0c0a0f0210 76
    0x192241c01c080c003c1d201c2e01d22092095a0800104503030302c0c1280c141030b6114110021000264080803509540c2d00500c200c0055207085a405440301100420101072526103101c2c0d03600c0024005000e828000c00e0600194100700d0012040f190006c0080c403500b540b0341e00f12402407011450071100304080d400d2000c009100403418159603441c9801134035610175030f8020b0140c080c40040c52007150250400011800b50366142c000c1c014031000c071000b81080c07102103001401010060b045004603090604c90814581d6905080303405483c1d0584038440c680d1290315041c2d0140088003201c0e100c280021080002841055000c1d0046500b503200c44403441d206e103012391380e004e003041d1600f640044030840003002040b0315200540e04142145000a04207548900a14481c00c054004070307000d00d11041200705101d0a4000d207504401045100c01c15070802c440048200d100701d207443c6400e007611038281004481c114086d5103c03000e0540a840b0160b04500d01710b0500141164102d1181d1a0140d8051070a84920 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 174430575 1250 174429325 174429331
    0x42301030f0c021c020a0b04050703150e0a0305070f170c07061403040b0403110a080307030606031a12070302060304080a02010c1b17040909030306050f0d0305040b0717040609050f0603 81
    0x14000d019410313040c5002070a00841c804d400815031155220004c0024142e5042c40c1c40303140100b01802e445030861902040041e104124804540d052521020070b020001c90003c0603947d1506240740e07501c41a29100900c81d10105000c5c10701c140c1081c5001241207450000c02d640d411510030b5a040340c2e01c0740802c2d100315254400032a071581c1e091000600040085407070710f41081c000e04102c05080500d404440c500400701804170b407001e1021050041d1150140103e00240840d03007028402d50342d22000c013401c04180d41481e984540d06901e568890504280200d002031178019200550b6460b00342000d44003a440180310340e00544c0381050301d101040c492012141642c0c665804404610107940390f142c0201c410308019102c505007004001202071161140328003803882038401040c41458002041110100b4a00c0d06001c1e000310380c003a0340084d500004890a85821903007043c1c0b0b0b96100d05100050a0300d101000e541000f0010b00440c015811140360340840e84116481010b01e003c1d40148000c6003c19 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 174431825 1250 174430575 174430577
    0x607020714030a110d0c08030307050901020114090a06051504021b06090d14030402180f040c0f1d0c09060a09090b0a1d07180626070e120102042301030f0c 68
    0x2420300c1c075900d4050280c0740704d103010703140c01c251b07060316a09024103550060301e841c40801c5001400070601d50302170164940e180520803064005240ca105455100e0b070b9403840040030030303a58800144548403600110300420704058400c644603040c20760501d118801400004c01544603090001349401c2002a105900e17003010f07503404074007080340038200015400c040d104a9008680120800c9284c0428101a1003180150210241d40c185410842600507154101c102c509600b40c109111090842c0d41d44600b410381c2c05440341480e03507216a00e030014013813403603a254040780005010410303941c88074282003034400c041002c110400b1610104968100d0038410b03e4122076011192011340900030f00307420741c09050390034000b140241d204a02d00d40c0d490385030040c00c0429400440c0a15a8010100710b40341c13084030348c0140f115410448006030003544810681481400c0211011203601d000390141d03002460703404503140741241400901d007076201d188810a0300003440c10080c50441005405103090910807 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 174433075 1250 174431825 174431843
    0x302120301061b030311030c03040b090c0f0f010c0203101413030c060915110c0c0315010909051c0909050a090c21080f0406030507050301060206190e0607020714030a 73
    0x684003209070940f0300482903007419520078401c000c2034141802184910641c541907076481c5401d29006580c50b40280c290b0030642e0048107003035680c0d1984084606094400c89002002d81e418500480740901c8695009400d1b00030640003200000700c1d60003608440000044442040d5140b0001404580d00c4080140000b0f601850703410105680b80e001d01c1c0e07598010403006803407000c4d0740021015650030000f04000302d900014a1043d501090007a04c005440c1280a001c854521020612040700103000304808140d03198004410084100603075007840c64100d030300c8150420f24480c082c0800b9170300c0c030072802064100800070702a0200e03031141b2840c1c1a40005c08110690501021070314008219524601844020500324045a0000081c003024154500299034035400c15000405803200545401c090120500041c402c20f0340220380d9640c030022041c80705a0403200320311070b40c0103040d410b0803800c13036406810705101130141e0118150083e1941c2c654244070494041c4289680c6140e100005018403107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 174434325 1250 174433075 174433097
    0xf02061f0e07120e03130b0d060305161d010501210b0a0e0a060b1207050702010c08040801140c0406022d01020a18150813030c1e030212030106 63
    0xd248104400303080114119001031644401034000340c04001d0b503580000c5022122100340c200070034010b04030114001c0000c0d50500700d9082c00b0040101c40c9010f003090701400400e0b08010340b0700c00e9204000454000f0100c0b04400310030000499081c244c3d010f0b91806c0d000016516070050819040e440c12100f041c1d51f01030803a441580d50004000300300040c010b070181c649103040e903660703542e440c00d0703024040144c40011141407901c0c03280f04444070384c0d0140c00882c005000700c5292a580d13031541944141d060806558501451004030350009442000902840b40800e0204001c001540014041c1070000c00054250f1504000a15540901d109100c0141d014125a4074096440300e000b5514011061079165142c0b100f46c0011300303980204010000240716200d1158402e070a00f016400148128100c101070380004060043c050b0800802002010705052100350816126840482d0956000040e074403120307401c0300c01054402088603080e80144038024503440e034092404100c034100ca100343c64080610f0703 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 174435575 1250 174434325 174434341
    0x30607122f031b0307110601050306090c060a14030a0b03210901030b15030406050916060e01140903010603050601080f340b0a03020304020a09051605090f030a110306070f0206 77
    0x3520043c080c0c01c01110b55603a26001c82004000743d8060f50042e2584003070300321401e04241ca0b0800581c0660f01c43d41c00041404201c0101003600b0070484405d8070865070301c01c3c885c4820341e545014020800c603200000410420040b2096004240944080302a0350548000c407660070748101c180f02c01079449140400c00c82000f50701a52044031a5900540151058800c80214041030b40049030242c2c1c6030744c0c40c0e00400483c4101440300d0081c1000c2020007031b00060420400920030080428800e05104026080113014504e0000ba1140800c00500a11a181d103a1500b207403128028462082e540c0700380780c46580c05003c00700d044004107081c000300c05141c802c4c504681801d101558082011084030301d41c04518000527000070003158100341c40140c0c5c1c3e82440c0c8144135207150fa81c1c1c001d8542c28030307090510407010314903000348104604514120307440701c1d10300000400e4100103904841d8913104005d00882008a00c00440154401c214143d903d2540c030cc0400f66940001240070341c00503080342002841c41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 174436825 1250 174435575 174435577
    0x80903070c150c0204050a0203090706050a1e0c02061b0601050103060509040f170c010606180e060d050c03030a080103110a1d0c210603010f18021509030607122f 71
    0x41840c0007143e410a81d00401c0484e00d042d14000100c64000081140c0807900b0040900201220328100d881c0004c0004001c000782e070f908400100c0f120b0455041c806191059010f182c2c080e030001c0046507078015844015034000c0f04010803c582c0c1c01607000000c0c1a40c001d01c40d100488030040c0240781d803035444d90345240604c0c0c240c1c4411160031956074201c503050a001d801410441c0d44060001406a0802c50040c2528048408488440b108420244000012224002c5c0c0003982600d4102c2100458584242420308092406406120204041c41a1503111100038101c03800780701c4080030540e90400303000702c1f81200d0003124a0311246140700030300c03110810003041d4002c080c2c1480300d040c101d0500d040341002c2c0d000075209040c00210000c0c40042d103420721554000340500001041002c002d0000c26004005107240a8490310111407224102c0c500081103d100c0d04004054508900c2c0010029000803400082000200e290481c044c04081d405020070800204c910010702032003503008810301d42 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 174438075 1250 174436825 174436859
    0x60b0f0c0106080607021b0d170d181a190f020405010e06040e0c031902030a0b01021b0109050112020c07080303100902030402090615090901030302010e30030711030c030a080903070c 80
    0x4040c508242c800800c406909c021684210303281015620080a158401962541c245410401411410700000101e440b001c5459219540c5c2c40c2072241d9031000004102110040040c1c072400b0308040324800d6100c0d4980c01017003564400d803110480f403500c03034081c004640202d01403640010060030114941003c4000907581c0035180a0b06090604a5102d21600707a0704192103c80300c4a490b17650081c00c56805000881100d001018200d450701c600c40e0000708058014031810341805114400d00da0050f03190380444031544600812146602c0e500c4586e25641d074401c4680c421800308a003c041416003081c000c803802540c000b4003121960b100c100400509081c00521081d05400400c0145c01175100c16801e075008500030f80000a20980d0b2107291420841d1580100d40c03101661000c2c05412322483e0081035000704001c242e01d032681e940c01006c0d5288048021411400d100114021503061000801010141450355810b240d41c1c698607034141d5207018600e0014101c0402c69014814842d0030800c20b40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 174439325 1250 174438075 174438079
    0xa03080c16050c040617100b1207080d260c0d1815060f03051b01030b090f0714032203270f050a0302090a090303060b0f0c0106080607021b 61
    0x494804512071412181c0581c00c030448054000c0345000102c0e18180c81100d0090600032004107003d800d08001544501c1100c5d054181141d070f8a101e0300c0146c55803140d2240d46500001154405a1101165551000248690000104804181c25108141744500d18550f510403800200384e441e459040ea103527402c1148404120307aa0394018101140e03080c412040d4250181d4050840000416043e0060380c0703064200c0310340042013031001c0000031030020b03140103040c3c4404a000c01c245101c01c0120054496100d02d10b5010392541d061181d00718440c030909029200d0790f151455001060000c0607007074001101c00002d4207511301c80c0c0c04044413002c100d4031051442440d02c041c1607868159070002158550301c1030038000c481d19005001c100ea240381204e016020884030580c01510b1540050009200180b0084129444606020415010b070708000d0107414a902400d480f220301c0b1210039410303000442c0c000115800c00500007042200850114065201c540c080c2007006c03e107194156110007050b000d69 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 174440575 1250 174439325 174439327
    0x80d05070203490b010e01030209010207090504020402040b030702071706040c05100c061118040501140607050a02030a1a07031e090516120b070201050609160302160303050a0c09080a03080c 83
    0x2c0011010440200c44a200e0303c0c500240340300d43d2030001001d590080c1141360501d8410001181180c1c0c0009891003283d40c508030108280e0794920100700a03004590104141103804401e1114058010603000c0c20f03035100e1180081c8508503040095039805d0300b41e4010741141250303501032202d8113004c1ba000c8020703a21400e048075241038695403441140d40489044290b1900400e0400c0c01c41d42a200600d107450b03080740c060100b0b50400000101c841e0000f480c0e10301c600300000d104070400006005101c02241c00401f5654540c090f410181701200c01c545038501c4040c003140000310f11318000e114400c020741060011b80003222070702c0641002071940607810b8901e44600503c2188602051761404d002e4448101d00c4001c0b016a40703803261003010040c2410096905020402c0103c3d200c407100303140e0080c41c620030341e410800c2400080d8000e11907481d0360281d070480d44950209064240e0810760080480702020403100e0405c41088400050034090700401e500520014808648900c964070b4029640385d07086 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 174441825 1250 174440575 174440677
    0x902090a020a021606110f060108030d020310090c080a05091f151205030d060b1206100302070605070306240c080d0e06040f06060f0503030d0522080d05070203 70
    0x500d103000550701c134a000620200840102410a2081400500000005000d65410054ad03ea103034010f0264040310558040001203905110f01c060fa00180a00ba10400c1003802d0f40303d008280980481d80489d200e0f060601244126100041e000c0442100d074181c0764440344500100e2014101ca111240903041135181e020440c01c0e400804005014421402035603280c00e00a09001541e01e507901a802c0b5910a2242d841888407071840325600000440e1008100070542c5003d60080c040c4640c081c007128540000c10184030f0b00366106806541d202e007030064510000f99050b44200c40312040c2d4000154a0800500000711824081e01c200c1e141c0f40350200b446c455a88041d4a0500125029a040e0000312120001e0001e9441041c010b440c0c09400e01e00f0700780c14000400e5903841540e40f00d68069980358001112a958404c0c1002a140e102c030303050741002158107050400d60401c1e29404900e514080100702c2c83c5000100716400200c0000e03021401083c1c0d10021808980f400b1200407000d5001800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 174443075 1250 174441825 174441853
    0xd120609020a020105010e0709050a03081309021902210d02030901020f030405061008062715150f192705040b16181401050702130b01080a0902090a020a02 68
    0x2d0101c0428590001590350714001c008a0148005840e100c00d1100640c03090080b0f4507900c410605890300142a9581d07214030801c0d5404420465101d40381c0544040b922090000f0701c210401c1500449a00f150303040c034803411003d1440038901e0300c0d000070709104201441074000140c000e140e125203070800060030058040380c0400b040d03004440c111019007100c070402c6240862520036501808211000f89070038501704c56100320a100e2800000c80c04407004ea0030201819040001003e80046400300d01028108010000128140e01b4102449003510b607403840048d0034201c0006405d0488840900403a40c078000d0100300101102c11840b41d18200c0c46442e81c4c15142034090140a24840d041007103442c0f9100301e4803021040303000a42020803150300642840286665800d0041d0765404400705061401580160340c24814071314001e40110f00703040100c4000d900e640c4213520007031080c1c80b40e03100b070380d55402d83d40300701c82102a000398040c840c1004164801d80c1603004d4641203103240114bc0548140b400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 174444325 1250 174443075 174443077
    0x5250f0c060906240e01050901061b02040e1e0f06130f0b0709051806032a0901170706020609030f030403030605120706031107030504031205040b040b030f180d12060902 74
    0x82c019150400601240ea0020b412502c0d000b17240c00020407803294184400107800800600c2101c00700300c01c000c48103d40004070b29080001a50091040000c0c14500820b1500e410b01554007c8044e54281b103d00700080340891100350185801000d8820307940c4980340c24040f000000016640d1007070344e0030fa00c400900303c0800d1030b000d502ca83cac0b240c0060314903000c1000440e400c40d200e0207031050302440500080f0345000488411009840f500c0c00300158002c0f5254000c500c0494030700b03600c00381000001071341c2d203440c0d40741e01d00304040c2005440030f5135102c00d01a070780e444d81a966108280c0c807c00c4400d4074206031501446c6c0040c807910b80031a8450342c0d100042c081d4a01801c500c000398001d400104900c540600c15041001c0c1740c03003a0b15082420944019195010b1031002500c40300c0f13605402c00c003582c4223000700c5000e400001c0d41d043d10b40381c668000202d180c008a80010ec1c900c24500403901426911a1141d9410300f0b94008117900080d651044464010700c1403106001600c030140841c8207401c41c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 174445575 1250 174444325 174444341
    0x1a2107081504090308181002040b120108060c1611040903050a08090d0903021e0d0506040302061005060307030c09090f020a1803080304020603070507050d0305250f0c060906 76
    0xd65800018180300c5411000459440d0819114928242c1d9400000c0e03008500301e94010403902c0c81002d034090f0f00d180c15041504240301000b01c14800a80071481441c1480a03200c0001080168019681c80d040e100b40d071120140e41a41102109200b660302c40d6048803140c0d8402807207052000009a44038020905485405c1c0c011404645c0100c1d200804076030208445078801600350043c84484031980c0050540402400003900515860f250034020043d003600710084900c001d0850b40c08001503081043d145c0500740c408400502500380420011980c064040c3c00f0342c0d000401003459500c41d40001d400030030104e41240d09003e0078050000302c04101d4030130810302c95484540960344200c46c42d130061108840400385040030194000500220703000304243c4e9407056058031029035035200c0401c00e4901c5e008140000384039205401081804c5585600490300541c0030822005080007002600c0318081c400d036400c80000742d80e6035105110b0921440644202d64002c19001a16000701d445840651f03c81d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 174446825 1250 174445575 174445577
    0x705060f040b1e01050d020a030512031b120a0905010e0d0201020c010f0e030406110304030f0c0312020303062b211e020d0309020411031003060b0a1a2107 68
    0x30800080c40030705914541e004524103404280c0d000e0407052a0040001802024000c2c2001000e0000b15101c91603407074060354119080342c02110309405610150344c8105da400d519200b00f04002224441400142c4440500c00128640c8a40c0c030b9900550080403408020ba801e0342d241c07400380740a454180300f41840041e02e5030001d03030346280c50110b80d400d42e0f14032419403010718603107075803402840c0010041d6000e55410b031828001080d0b90301c041510f540120b41000d0070140c580c2c40390600304003500b82c100c000c0341c1c410751410b0007140d010a400da8584c00200e4107503402400034440c40610980c6821003414804001e08615a001115120707203103d035124280d00300d08280d120038030200b45600301e404100030100d100b14800f000d00341a01c00946507510300c800319040c0341d220000001196a2900801720300d2000200c402d803240780c00045150090b841d0301c02a2041031620407070214078104451068265a440407034903501210401d02c009140c0c0c4032075100402e801c503500c00c00c405091440702d518011400c4d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 174448075 1250 174446825 174446851
    0x3091501050a0302180a02040f060512010e010321140a030209030601120512030a110a030c0f03060f0501080a09050102040e0405101e0b0415080109030e040b03061b070506 75
    0x11482288001141a00514401c0b40854010801a82d0346422002d4541741c510700d0f1109034a84142000c003a00444c0c00c6420440c100c2c9d4404520329510074098805540d00c2400304002c0e076600c415a0595900c20302020b410980004040040b0018058200d01d010417946010801c254080c0d2421019404c0b48240034002500012013076002e2a0401459014181d0a110380c032020615960f07086c0c0c0d49032440c548850481c00800040d840510560000c3c003074001103201280c0da100d0000c030080082041c074500c200824440210b01400d14803a2103881c0030341c1c49541d00340140c0f9060600545000d00010031030b580c81525414201c00040080c0043d2005200c090703074403040d9042c10718045080c15648070842d4402d07841c0180349501c0c407030704e00d0402c909904454000565885802e000c900034011500b0944c5009030742030030000700040c0550100032041d010380d071203400407070f00c901c100b0003580ca40f100495459441a004226820048442004046070100640303181540680d20242007a130304403180d504900d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 174449325 1250 174448075 174448093
    0x9060a092c0906092a0d0b09010e06010b090f0319060209010f03020a0207060c030c06090b06040c030912080613090309050f0d020306072001021303050c01021504020906040f020309 79
    0x140e08076225400280d07081c050a420b150120540fa596180c0800c00b100e80000e5621003842d10803030400e619003208000e0014403011083e42030170041c0d04416518200103611300420003c0d40a40850f01c0ea060b40c800301540d038a4840c59004100b041000c45240546c10b00032903039262200c00c858074440591911541c00540c8030358142c070001d055114107002280c2030600410192a5440e0f02180d01001d42c2c15904203544c0386003041c181210300c00d80d21500102240d290036103800601c00d18018940c81484200ca09110258031003600b00d095035081040188039a8078101c800c6459030040546075881341001e0302d40301c500300081c01d82006903091403105801242141000303004a00f003540f002d0a030341070103540c141d44d104090b07808240c0d1900010141d0313007046044202a11010003640215461540c0c1e88000e40d04c40714220340050b1383c0681488200c2c0d0070311031448a90359a5002254881c07010a42c52031091403542c0d0750302400919400207184030381c000e81d0780c001d9848421051000c0d5024044120003885060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 174450575 1250 174449325 174449399
    0x3100b0706090204061a09040f0902041503050d0f0507350d050a022701200708100c080f09010219031a12030406030e1603080310090b0609060a09 64
    0x2245c94020004805900c0c402000a40c201000c0350a503400548000441c490100e045034010315868030001e600c80d082508031b1490800b89040351054034021801d0b15410020001c0c1a90895090f03500701c40440c006110340b0010403400c00701c48401c0400d00201d545141d4220b02e0418550a58a403240c0f0380c03090201f014002d0721030ba4400c0aa2001000101b103181141043c1c0c4050654401c1e8241d02501c0d40d02c86900480303903ca0000000308004048880543c030b6120107409859803268046c0c0065845011140391045034240600c05600240d0385500f4919101d00200712074001e00188200142d40d0200700760411020201c01444145010343c0e00050180b61551100800c50041d2a0b060301c01c540e84144401036030000b100b01c03421500c02e800c0010300d200d6000c0500d41448403009003081a49400741002052048000085114040440d400841c8503140d045100440340318904154001c40305020b150303080c0c209030b0000c1503d0411420624940d958a41600c01100c5503402039001060700e03c030741d030a001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 174451825 1250 174450575 174450581
    0x1503080301170a11040506030106030204050c0d0b0f0f0d0305040e0103080a030c0f1b03090306020307020102030402090a0c170a020c1006050102010e01060302030d051b0105040f0c0e070804020603100b0706090204 93
    0x40b4400307102420030a030613922105005056450194801c55840000c94281c0d903095203c0d400559018000340454504120700e60745641140e90b440080d5814900030f10600c8c40c0540c9460b41c010801040c41681c80b400b17100b17004039880c180b5001c405001040002050036503c1c1d06c2d03814002c0d842105051354414100750300030b041c2d5911107107400500042c0c1d0711002030707180c00c0210440d02401174403083c1500070711810103c40e4880541e0014203468400020b0190060741900154401c42c029180750070700d40c0f01d403c0070004603280200840d0008a0181103d180b00403500d0751250032035034202c0054182000714958909040d0101000105545e881ea0200a02d58081c05142200600c10000b006821301d10b4020079120209442550b003000800210307842c1c0241c4800141e070100e030140d4020043d900d0302c2d2503c3d181a40a408064800700f203070741e400288007900441401c0c81029165181400c0341c4441d800d0043c503400c00b43c00d00000c10740100b00850f241c1c072100043d100007405540c02069180702c60042c4411 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 174453075 1250 174451825 174451859
    0x60a08100605101b0305090301112212050606010302071a09010b03060615090d060e0f010c120207050a140708240c0406080121062f2b1503080301 64
    0xc1c4014070580c05521031304001902c134a590142000355446210350000382c014400504403101080e80800e041c0901e045804c11851010010414079081a4903010264140120014020705a92100c40065503e52098001c0c05c00d003072140c24107110801a4546542107000f08407080c6010341c1d540d66400e0510b19080000c030341c000a0558426001020461102c4010300c01e04011500030610a00504104103195021120000381402034a810b0340214003054064030341002103400164104001c2c440d007411920848142c0e503407000c003c0030901425540d01807010010020a8014025040f0000301d003072003441450092110380440d854074001d40b00c800e040300c50024000030500e4109000c00c0c0300581d0400c0301c10741940d200322a501c90590814001261001d081c0790010301603820600d244001407504c0d120032103446020006203109040500b1169954050004c0070480d40c1c00648000391840b000041200003030740c44d40c0700030401015a07903082481c4000ba0b44211040d860000041044246460202003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 174454325 1250 174453075 174453077
    0x2001030501060e0f010e0a08010504123009060b03161a09090f19020d0b040e01091721090c0111060c0703030c0203091002010f0b04020906070b060a0810060510 70
    0x243c60000003080703210400301d144074144411600c1c035502d660754000808004042200c02440310b0700d01031506603125480043d01101040300d00071010030384000c0484a580d0b101310698a8203d240103120131001808000e4004e8829aa8402110140d51824001c81200a907011049a079151030810501c0b4185016461507580b41002d116102559031130410740742d005000700141d10f1194461020b001b40c0440300b0301c00c0c880d24034800250381006002c15041048014170856040102510038010710b82030b100e111400811110300c215488203000c203810040d10010601d0780b00b911000c01d4410700208800070030b8901c0d44040e4803410604003d1769120803111100403148002e000681070414007100c8a0152450003003d0645402c00418064400c000b601d01100c00208488001600e042c0047d00134803140030002455400e00014000c1814603000300c840031070029001501e403020740d03140c0c40440c2401800f42c90b40031000c9040005c40001c01c02c4000510040b03403030f000600910742810007040d1038400a40030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 174455575 1250 174454325 174454337
    0xa0905011b03080c0f030702150f0403090e0709030b010914180714010c050109120f0e0a1202040b03100f050105100507020f1c030c0c06030501080d03020a0c200103050106 75
    0x100c0058240e032200c01000e0b450b08000c0b20580310189100a24091245d0200449201104204142d0b900040828404407204404442070707d6000d60490200b00803103028001c9010b8030000c1004c1400514002c0d8040010b14208086c0c0d6141d80c0c400d1201642030340803800f599116803a48200c10b240c030600e40e030401c80c041c90070400c520b04103140b0354a1702c950340308042c0205881503034080079034050005585265407040080191810794a000d10101010701000c1000600c0024004c4149008000d549200240101a240d43d24a080f211040041d9411030490b00300e500e454044010b41c40400216032208076009003c40e0400d000242c05c012a5016401984600a11100f40904942207000ca80d130300e9405951600e800c1d0721000100c0c1e02d8108003500600300102071741165040c107501c10b2440070554850200c5070303103482e84e4040880948000380114801500b201e800707400c0c0d0034020380c0104605070315410702001c15841c64072040c0c030940300625200484039200e1528a110b6926201d4580134000e141000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 174456825 1250 174455575 174455597
    0x10201020a1209020604030f03030207110604061407051501080f1501060e090a090212011401150801050d03030e0d031d12030a0207031106130201021207150b041d01020a090501 77
    0x5042d410101c0c004030465990780701007810340d201c00c4122000396411048602442005180c001c009501c4000191005040401c401c00140351080880b400c444032a9969907040303282400c051b81030780c81034908545500c40c01340e00c509110320703202e040c2d4001e0940030050690391380781000181c04c00c061400f820850111a40060140503005684400c1c1e020099807044025a03c2540c424014a5102000307035100c40b28000780045904150080b521011501c80e920390300c0d99807601a000001c0c1490010004503400f03200501c401d05100e840907450074042d00d8007003035100c0c1845485060440c08103081c80025107a081a403036500b484410040c084030f84d180100460968404102180d01000c1d10f2500d01c29000144403052500c80c44030200c003024010181c50480c108000ea00c4824a8050012405070044441000104170188180c0d0889074116004640b0b281e68103a01ca0014601c000c43ca40d4080da86091100e40d41c8207001e150418030194000050355541403040113810821994440d0b070400c40701c403127a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 174458075 1250 174456825 174456827
    0x3090812040617090109020d08030a0e010509060f0601093809010804030f120204090518030415030902040e16080f01020f0706020717030c0910030b060304260408010501090b010201020a 81
    0x550281d100744250b0310441340c9031207640901500e4582e6000c3c0d40070faa02c404000501c0742d0b1f1002540a0500b900c002c000401800d0710700c42c2600d8048032103035a00d800590010390014140100c1607400f440516052880503203560b0600700315404012102d5482e940440f00d2a4072980283c0550600032585440d1401c10003050002403040c00b0040004040101c00c2d00501c6d07016010700395a5540ca0445141951915212501c0b00014034080701c00ea0b113004180003100006c0640442210140e503000e440d046030fa1980b00a098000e000042022a04950703940014046d0341010700001c1030f2031180300c8000380320902c0d00940360b00e801280c1c01c01005592040086114400f000b40444824651201700540c4581683c103007841001070b0070b007003003501380400020000c020301c04100510303202d4030407240304c00c19030144a4100c0450b0548000141c0080f8100b001c1404900c00800c48580000000506446003483c00390001c402c2e0440d80c060150baa445600501400300f4600407022800000e10086050ac041020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 174459325 1250 174458075 174458087
    0xf14070509130f022202040b03090106090605010210050603031b0c1807020d030f0e070803040f06140319060b0c102f0c28031701050a090c050c060103030908120406 72
    0xd00207101e840c100c82504210000e01000300c3c851700c0c00c01421500c465498080520702d030b00803180d90019520b0000e003c1040f031a14800c620980d841a4014400c443c143c0d0000402400054109a410b21083c0807050034078501da0700003140c090360a00585a5545903205020020100d90200c0040319924401c00c180e031680003d42c50303030003240b603d00030170541c0c5501c5400b0020141992000418000c0990103e4007000020040084421605891081c2c03a60703907504680604510319285103403001040441d02100a80c00d04414050300d604c2e000400c5503a850041c00d00c0c2d130002c0112400d0781c0207040c803200300b41007601c52243c040e0650600d44902d00384044042c94041a800005070710380002042c51040301c5000c212404485111021594038062101d201e50f0000c0da1581c02140007800000740040480b003a480f91504a40300030348080107131030038004d03408050a111400300c000c2040074012a500103008000e4580298000e07281c012081d804d10101d82e0502c0e00440c149181ca00c400c1101304580b0340d21071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 174460431 1106 174459325 174459353
    0x8160302071805090a02060c030c011a040e0106050d0f050f0304060909060503030702010c020603090c060313020102010e060f0621010c0e010e010201110706090f1407050913 76
    0x35030401642c401315819006600302000b0000141404009015404041c1c01a01d080c600018802400c49162281000072800d01d081c000402d42071512411070b1107102e107030007030000301c0c01d280c0410500008088002e101c14421990103003030060502c01d001052001500b0350740c3d60790751100002c100c0d0499004d48540d55140000c0081c003450700208035039a159042e101c072a4000019004c21503160001000c2c0c048c03a00403a028041c0503918407000318030130760449600590045140c000242101d010300714542080c4d00281c14403200720002126254808812510b1141c103000c014080b050340040c10880c0d2203d03600f480c01501440750030429819840344207076a002150f01d42c45004a0980d103030304d0f41d4019025002c120040c086141a00700b9450a40a0300020440340c2070741c2e5402e858241c1c01c4a02c1400346d0018441400240b810b4501c1680004001c166250031b00c1d0207441c0c4214440000b = true := by decide +kernel

theorem cover : BRFrame.Cov 174280575 174460431 := by
  have h0 := BRFrame.cov_init 174280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 174280575 ≤ n) (h2 : n < 174460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
