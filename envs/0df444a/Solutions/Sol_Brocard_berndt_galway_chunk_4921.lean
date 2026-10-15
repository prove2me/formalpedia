-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4921
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:09:52.455519+00:00
-- url     : https://prove2.me/submissions/76450fb1-980c-4aa6-8296-9018543edeab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 884892086 ≤ n < 885071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 884893336 1250 884892086 884892101
    0xe090601060c060b0f190504180305120702070509040b15100c03031509090b04060e2a010507150207020a0e06010905090a1103090a150c050a120f050c090103050109 72
    0x584505070307201119600c0f18090f08030340e40c044c0e0300508906107449450b62402c266035074005503070f00340c01030f0a8201001d01042d9181c081c000400b41814403040c02c00241d01901715480c100308400c20b60b5840e12441d10481c00d000c52079111a60003400c40041c0070500030383d070401c24050ba03c60100c4040c2d000100c42486609150b1045440100d080203041c02c0c0406e010b6040580800340c41c0c0000e884c620f8440c05d00001300d401c080030556018041ba4200810003100c0d2250080307407240d2000170408007010040710192a403e5103003c0c1030b03000440d5036140d00d43c0d01480c1038074255680601402c4511000f03445140080d0041e00c4281d1068207400300000c1c000f8514035065009640680d50014841c0c14507060200170301340504a888055a211a401600640d1401860080c002c0902801c01d00d903c600b486c549001400901e581c605242000c804071545c2c22100701c9803581c1c0a42001c290a6901c0e00626005146010340c21711810306013000c10020000039002003051003c01d8a007009940d8803640c40308220307102d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 884894586 1250 884893336 884893349
    0xc0f030c1501051c060f0b0301182d021002160321080c030a020c070308030702060615090a0e0405010b030114060a06030b03030d020f0f2a211b0a0803010e090601 71
    0xa49030884c010032102e80140080b03205214012403441000030100303007161850016401d038612940c4d4402c040040c080c0003021082141a00701103c02c0d181d40f030a030f81e14101860024400e40300905100040c500900000281c141c407909415280740c0c4c0c900300040ca2403800307031010b100790002d420030400180c0949207150065640030415419681e40c1d900c080c009511121541020380304082d0008005505000158032620301c95003c0c0c4201e060100078000704840c500f540d803444440c1848407042030784070300f60700c142107610b254003000c5561900d08081c0d0040028040d600d03019420301c0031400a0988ea104880d02506060f540e4920040d41c441c022002c8804032820184d00d074000308032018080181360003512443c201419228170304011440d000758143d01124141c011b44803c800d100400300c01c03894000c0c01d6884444064101001e0900c1258840490440f0801d004a00855001c038250350603540900303122281030031168400f405041015140e0030901c84c3c00285c2c00c11030009000280c0102d00c030b0f41200c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 884895836 1250 884894586 884894629
    0x90c03040b15030a0c0b090a1a070f031b1a060a050a0b030403090b0d0e12180915060406020c0907020c01080403030e120301030f141b060c0f030c150105 67
    0x55541c2d01e1000405085086541440b42c000b400c00840c9680e412040188520a0743d5a42ca000f01c00a2190700310161784002680c0c48018071006550720a64102c803150765021803003111080f09c1d03103000d4810703c0f0444555000309444020607000c02c40e650b80000c04100c3d21618982e2240d840c0000c009c4048414000da641000301210100011030a074409950024801d04003188001d884030050b2920303420001008048640311318146100d00000c1c403948103000c100d002075526285d10548144a607501a0701128095040c00c0000b801c41c0d1040541120001c10040c0807540d03956031444007d50714012005614400c00b060800b240803a80001041c010380b44041c0c4946000d5610381e1410307401800c0024415115008503c09484050603000042d07029500c2071111908155040c20001400c214400c15128980d1040c030002c1d5000c010020302c07548904045900d40c1e42c0340888900c41e4180058080316002900c00400c1d40e8043c010081151603401d4000344492046a03a241c0c1000714901000010000406 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 884897086 1250 884895836 884895841
    0x1c11090f09060a0e0c09060a02070608100303090b1b0706090f0b0310060f09090c0512090f1209030304120804170d05030726040b09150c0a031e0e010b090c03040b 71
    0x4075080001039100103040421428841d046c1e0100e500b0f64070480345180180c02030b10341880126000038005030000069202106400d0541d50050417a01e81800f03824140d143c04100303a01c2032038200180c882d0382883c00c07007a81d13203503651854060094005800b030b06401c000550404a1200050f030309a030f01c101400203070002c2c0b8501d8000241c48202e1001d8600e420803840c071078082081c80c0c0601440300382c1496640c0c0d041e80d80030300404141c00110301a01000703190304081464a0246400600b0403103407052011229621280e407000a49107100e1a408503103078100490440050003025000f800032100ca42142c240f200000e080e0842d00c440520100c41d0200d8001d1021407070451040c6050300314408510f00850240034072100e8035035488804c5170122800b00044e0100859440305001d080074400603c4140b4281d410080c040d82d4241c02403c580c5000c059980d0f600304a100102e0580e10380c2c940c000c120400411446800d8540a04141c8900501070700380c440110b5400c482d40e5003120b11a90b04072a104000c1d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 884898336 1250 884897086 884897099
    0x60f01180302061308061e13020904140708060a0b10081006120902030f01090507090b0114070501060b04060c060501051819021908060a05010903050a081c11090f09060a 74
    0x41d0800c11300a1140714010300c0115014204015003170050b030a2460100c144100440c0094509800800f001c1c000703840080020016105e210030103401940c4400c003990310760804c503802442c20b12958428040c621a0178180310055001d0740c4204031040080d140306000390400310065034142c805032640c1f20b0b50000700008200d000e115209481070118190408145d000954000a00c3d0250122589903140d540c0d01d9a20300b00b140401a450007043c01000c180001002c480000e0304190703120680040a8000007003400800100f075008501510388151102c2c0ca9079282c040003450b00350114021030307205243c4000031501d842c101314622410901403001501035038035032410020011b6086444224aa0240482c2010b0440d809658590381060382d145145454031504102c5241c5140d03014038144a1918420300114401258900500d50022400f0fa60381d07545c01500c84100c0d02603035a01640d54a8020040d5400c0c0400c0c000340b006640c220f03900c0c10964099010400c0c019415208039900c49403006080011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 884899586 1250 884898336 884898349
    0xf0c1e030c0203180d0c08032206020d0309110a060807090905060603060d030c08030a09150902010512071403010b0403151a10090302041a18060f1210090b060f01180302 74
    0x800101924085d03680b200c5568010512001e40c014401c541c1000c070380812580d000114840c0e030f00740251040c019880c03900102070b486500c8030415008240d242c4102c8000d0000002d4056003440e4090070481180b40c0c1c511000306824810380f13590000a2a490000070042c00034010380c3e0103034200800591860300c48400b08021a5003a00c011014400030b00d070100c020030b0781d4002447c41009103c0c0c001c51281c0040ca40740214cc420f0448403640e0310314040808000d41d034000d0650350021905a0200e04603140c80700c080da54080c9a200100c44120300000104070f0440420141088a01c1001101048014000c0f880d09880089201d40000703900b54480f00242c0c602990300c000c07880340c281804a40780d80c40e500441c00743c0d9500170841c8020511758100444d141001000c80c10f500c0c0d60130046150303600704480041c684004071400f00d4841c42d03003031121004000c014480d212251a1401080115150620308140c0300750b030403a02e292107a101c4146000095000301295100c2c80480040f00d2500740c119400c000e007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 884900836 1250 884899586 884899627
    0x5120f070e0609130c030c020d021b0409020d0609051e0c0d03050d020c0f0313080a17070309150e15210c190305011809021011010f0c1e030c0203 64
    0x50240f19213500c4003802800340b040000303680190381c01051601c18818003a2a05000c10041400c660111134001c0703200c0c1070003034600c41c00c050888000c00d03000458000981d501084010241c0f0081c9070038010002c21030300044e604281c1c034004850b000c01804030103890b0f850710310403255a07400400101251002920590051010401085006007440000c1c1b15491900f0304c8002e003801580c0c00043c0c444a902101c2001800500e02200204218081903440341480160b401e0100700c1d41c04c000c5001c008060003240d00b0b501802c04600054180c200030036000342258215100a401500040b541e42d20a0502c5e4040300c0006944c1804801c82d24140288941d00d22402040359a038200184008040400e07400b12240600e403c075540410710303504100a100c059111302030b100c6410ba1034030303c0c1040180c46035165100600c20a08042940c0704003404031038050841001c244090b117140161440d40113030805400070280e0300c994446c01c2481407030301d4250111440c0e1126031015074800d01c0004c03411820703828041ca = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 884902086 1250 884900836 884900839
    0x30206070309230619111903110d02120708130b0a060305030a051803010915050402190b0a090b0a1710030209040b16021c0302070206040302030d05120f070e0609 71
    0xf111000003104807805107910251240c6422141c20b004003601c0d429502d61060091075020003c1441940f03000901d4030076208a1b0942c0080007000c016154040d900c010324000708030100507a60071a5102c0c0304000c0d8468048012650003800105010a00c01c012007403260701c441100704281082d5803100c0050002c01003e0380b0006032540707000b100084051000e000d004407651030380c5885840700d02005600c2400f003c00540a60703d0212440c01040070b25807444080c0510400000302500c3c3c0b800481c5a0090390a1030a015203202c03480010380814900042660020954405a40ca612103807200b0003449035100b000c1c00a203240584080340d040d0801c0c0c81e44c2208401c903c0c85141d40e52035020a2403114120707410350f40c3c0840c01c0d0800100e480b11100c3c0060341401d81c4058011140319020515166032460b03011010190302050080441d00e510041f00c02860300202206e0712120705803001002a80705841446440040742c0105000f021600d409034002c028549414058140480c140115a0403444029 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 884903336 1250 884902086 884902103
    0x718020c0a2a090506060403291036020f0412080405090702150103081c06030f1713030b070c080c1b030a17030a09050f061012030206070309 62
    0x2400150300803689200c100303804040c403142c2555070300001403a1000e03034042c4101c07508240030060242e1310041110305403907025098850070002d43c074503071010034050300e108040d4450000038000b411850340010300442e142c0340e13041902c081a1142c0482803404c2404401d0041140b0001c00141d0070803500030346800400c0c1c0038043e05159440d801c1d4100c88100080664200d08001230501941c24103541481d030000d101e000a10b61074100100e41b020b0b4060520000e00803000c0800c1481807a03c5090100d0301000840c2028040d03640c40e4101000c006200701411500d2000300707800704601c09200815505852407104401030320307a00d151a40d9110103c0285804100904800c0000000f030010015000c1d186d101002131000c40ca07014803c8680008001655100382c0c0103150602c0040e1650310010601080989242d48a4682940071b00107404c0b0380100400a0140804090240700005403180c85060411500300710b140d50f0f9800150f50560b0940c0c080d0040e0084400074045034001d810084000c0d1080100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 884904586 1250 884903336 884903353
    0xc1b0f1a010303170c030c1902120d0e1c090612141e060306060d06090831060c0c061d1002030d0506060306010206040201120207080d050412020718020c 67
    0x6602040c4400d0300100c01203107469100e480c60a01110003554010941002c89181d420403044e08071007401960441481020300c0c0c4080203101c0d100f4410644d0803c0780c0b0540c0364940c40304d1400350000d03200c0300588605a00c2554108541c0d601c50f080316802d0140d07151100e40c442410b0440441d11015031200b042041900d480c4101250808030042138810f014009902035030014160030b462891001034a0540300f903100005009441e40c80f01282070304d050b44008000381c402064907010341d09025644140d0210b07030317042d000103040c0104840c140b40e409155080100169854031410f1700c424002d0880a0843c0c0c1d04003a0a02115004d182031400d280040e08501180d2540000010340d60002e5210560041e003022035002007a220754003400d0b410404c01c58200c0e00707614103800000d5a8a80c01080030f070401c81c0709012040401c07031a6040b20b400942000490741d6624241400750081e020030307981220326500000035519814404514034080c0e905031904001e80c000c0d141a104080d41040514082c02c3c00744004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 884905836 1250 884904586 884904623
    0x140112150e043012091e020102120f03071704030c06020c0a02190603061202030d300617011b0e120109050a020103061502030d1a09040f060c1b0f 64
    0x41d0403030352108960344108000b08200020800d0300c1410f13864240b10b0802d560300000030782c40e0314040c3c0000c000100810500381d280c00102e140c1007622054100c4094001406500c40000800039031148070251950307a58948001c4109010100c1190003500080902c0f03044000586075030020100010316800301c446c1102c241e0002003511011005014030030103810001c000d800e4050041d00c00a00c043c501c5100250f450b0b80201e502d80c501c0c001c1810801c2240d882c401055140407d065800100c000007400d44517062442c1200148101d008402c00000c05111400c0708000502545c0380d10040c03001070032203201c403405003500d0f8865000030103603000c0e501038840c11962000b44a10880a402640201030300d8a4a000240440e1400e80200030030b003440800b0784910540020490b603406900080000704d0040c0e100c164148030707850f1000e1039403203046401400b042c0300c0c5410000f40460b01a500400402d240e90700103645e50101c02000e5000d400c581e5000e1000320f00140481842d49000c1c0c140000030010581c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 884907086 1250 884905836 884905883
    0xd0f0b070305071806020a0b1f08030705070905070203160203120d050a0b011b0b060a030605270f07031b2103090b03060d020402030a06080601140112150e04 69
    0x140d00e180007903a25401c02401c507602c03001c40340342c4054128182d082c260800900a46849403031401404014088000c0b41c1185040b0074511a00107a100c2c105100c20303264043c044e140d40c4645400c0d202840340c40000724110303441d07103e000e0203030321950015440c000518070202d0152034403040a0760f25000b1419903500b00e107206001400a40510140000e840c500440324008480c200000749041005980420300d60b9103240c402c0c03000c01c58200503040c41a55940c00090343d400141d80004208506150034406940c0d080300b00d05441103203062010b03000e40201d40c42c3c15a51032103281581e01070780c42100c1c1040810341d4090010103080030040c10380c02464441060000c010f66403008540c1105e018000c48040c1035001c501c0501402c4030603102450750a020300010495a01e9440180c41142d002010401c4c402c43c0390700020040015100360361507982d45900b8080c0340d401c503440785030200d82c46540034441c840c01881540c100c02c5048410742013807418905034141807840100121401401c54400c09400c2c034126 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 884908336 1250 884907086 884907091
    0xa090905151003061b090612020c0703030c02010f1d010f02100219020f0604050709051509101701050609011710110a0f020316120e091005030115140d0f0b 68
    0xc00002c00d0040c914500441260340b0301e601c0b0707409003200c4401484600d601c091314404071a560300d005251081c11043c2030000b4850866116614032410200204064102c4122045113000b602da0700d194250002c4140c0340304401d44c000140d02034482010790440e42c090b411140410819104a80075001d482443c2400c9030300180e002c20302d240b8049a403e0520f541005100d5a81010001605650a01303540310303a41c030b5582e4000c20a590b91520001800340284000303000069000420002c1d0504007a14904a201c6003030140d0031100d202ca90b51070b6190780050142601654010301880d201e41c1c60100199101340c00c4a15103000341c081c0c041e081084000c2809088070150080c00d08681d20508000007074584000100c028043d904184200e43c0088280900000030075040100011660320041048030203019100340341c1ea009151605102038100c10051030801c2c0c680c2500200315a4042080107184c010540c0314a0081c6256100d9074035542c1040c0c45043da0091288484400540841e51280400c0908 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 884909586 1250 884908336 884908351
    0x70e0d15060b03041b15020c090712021c0c030606021009030e190510080402011b021f21020c100f110c03091809030d1d0601031406010b090a09090515 66
    0x20140207200fa011154054004000c5446e010802c84a004000781d21741445104080c0b02e010602c0c006036565004103036180401c0c41d43d0b80219524040614807111644e0195003121a0358a81507104c02d815000384184815590070350018454202190b10380c40140071800f2048041000010903000c864035003603501007285040d0004c01c0400c9040c4000d20002e456010488410001b014060101507600400141e13042c82c031100d10021030300641d0011031040c070b0034041c01900c01c40845181c000000c1d80241d00d04c01c5858083c40c0f071ba10804004000b8010b80c0201140021030360404c400c40d0401401079488a032840360030390008210701ca000b507511009a0440c8400e44400d0700005000c10151408a11401c1d2041101a00b032800d0f0500c0c600c2283d49000f21051010401d98803648180c1c07100c0a100b5010000d40340d5000c489503503840386850302c4103008050031048944510000450392005a40c195a1691710203821206050b107046881c1e0050700f10200c0c00d0315203000701460f1401d910400043c40b88038408 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 884910836 1250 884909586 884909603
    0xf161407080c06030f1503150703090212011a01120609020d091e0c120c050a120521070f02011101111b03030c12180d080f070e0d15060b0304 62
    0x3400c07400a041c1036a242589209041c00c00070800c600301c00a02c10343d000349004042c082c074100d00c1d0011031b203807078501076249041280c080100001c542c1c2c5a084a41c0c603d04c25100c95034012410400030f800d8580030000603080003005c4d41240600c1d40314060344541c840d40090081840d55a45450000702d9011185060145840e1419101404014084280c0310081d040c01c0c122a049261150703180040140503000f019252503100c03009010009540002611004062020503662075010401d11044c0317550450b8580183d2a40064030090b0103041c00c00030f003c1c402d05034070b04002c954455a0144910004906002002400030207603c002d2140381c040400101340181d490030f61960710046001c104420100503842042009000c240c0001551281c03c0c0e02403110419490b02c800304c002c1d5a002904500f11407090740c62000801e540465220300030040000300140984440b10f040b2000c1d8404045180c1052400c0300c040001010020020b600d240942d2000034001d4031010404512360058506840210 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 884912086 1250 884910836 884910839
    0x1a09040c121b14150a0e210d17060d17160c090902010e120f0f0303060f01110d11030c03070515060a120b0a1d0a0506011502030f161407 60
    0x3600528581d01510325006403c2c40f01d09004009007800326107100b06841d56201103170b211080b81c0a403107a01c000300c200500d01e912400682104280f0701000710340c205d81c1c3c1e100e050304600b1101d00071a0100105445000400c1d21a601c2c60148801c485031a2400c842d180090384251006544600180034840c2c0c041107907140402090601903882c01403908040a032501d08008400140c0c0c00c60411448400c003070790380b0f0041c1904259001d0404c2e41843c19007640e4007078041103040140d00400210f02c11079003101d0062034924080700441d0341c00e127110550b4a0079407000f184100b840d40184000003900f040581240d1408480e02d01c56411a00400130803281d0b076001d892280246016058031950011064a1502000c0d2514403600b0b41c0361481d040241502260002240780c105003134118805485280c0300014002a02030b407200d41c0d801e420b000031349140c003540700081000e00c0c51059800c80b052690380154140603d8000118255010154841c01c202241660741d0003ea4a401c000304070181e000e0107420b409 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 884913336 1250 884912086 884912123
    0x80304110112140f07051c0b1302030106050d18151e0c05090102010e0f0a02120c061602040c0e030d0e04090c09090b1f0909230102030a0f1a09040c12 66
    0x107001742100d000c0c041d00b0300003090081040d6801e01010400c686020442580d18404a1400d510780325480145038000000030032810340100040180e408860400c202c001c3c603011030304480807024400200703c44030b00862020109810781261041e043c60326070125100c51003070120821105019030b20320100b000030813a804150b07020701c21240c100011a01402103001207089032500e034041407000074032406220042d00e901c507000300400c44412401030505a0340789851456512959401c0d24100d11840c10616032000680c80346040380e100c0d40002c1d00034031141c0c02e10b640a94643c200d0901c4107030000e03621208100030610aa03502002005648000203e420706810b01c600004d10040c407000c600c0110101070b0340d0030809082c7c1c0c44111a4801c2001651845c0781c40c1c0004003040e510044402010000003e884001040d4011401120814010400e00c209c09c02d80c401603030404030010f41c3d039101d9240104141e040c03141055602520a4042040407901d4030207001564000d90700c2174490ac0102d03841d190302c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 884914586 1250 884913336 884913361
    0x1207090c0201020414060f1b0703021e0906011b0b190608120f0a050d020d06060e03070e0a0203090a170324090a0b0a0b071b1208030411011214 63
    0x2103400d84001d514050500c00304c5130f00d00003c555080d004020015041c02d0b40c0142e001640c0b803c1040c54004403161000d50340b4a41e0750304440c04240e20400e03c2107500d0240c00881d9070301551580001d003081c109582c40100640e000c038410f8420b00f520440003501c00300086d48095046100d01107040c10700098040c0b00e1300040899180d40c1103a0030b0380d8843c0c4800000300c3c4505050340c0605040c19580c0ba902c0c1903900007210320b8090310483c08040d60000c00c078004028813642100d41034070159a102905120031408040c0c3e500520b2040c00109020f4030041840005690002e50f0f1107510b007411181206401d566050424103404030380d0071072810100070311031652030032104400704020100113549038110000c00680822030207454140700036903d00c01008582c0710b8a100c1e030000c0c040816107d84031042c0c0c0c204282d01c0d90802c4242c110700204144045120800d03611090f24094020502070306594403596160345a000341e508840c18003039081e0400a60302c0b8240100d0110482c0d0000801c218101421100d40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 884915836 1250 884914586 884914601
    0xe180f0f01050307030b061305070c02040e0d210e03040e180102072d0503130807080307050304180f05010b0d1d0606010f050702060d05180a240b120709 67
    0x86490030314004005507600001c0013800d498115030110002e80383c1000103200a9282a01c400106040c0010001c1d80768104009085250082c2e605114000001c54000e484545000001001c6800e110380e40401a01c050a4850b5050410a00040c40d40e01d210f026460350b0882d074040b00c0020350300c008003c080e540560100d14a040312900941c01d0040940c0c0303070f402c0c5165110079240c41040a00004c01c01c0000c004407890280e40182c2941c0d82c507078510141d4051401140201c60b030901c035900000809000000072203c0d4140c00c5000f5600f02424005d011340c030103100c05001da00098654400c640b07150020b02c240b5008200d0301c42082c0d580c01004e918282520f08000302c0b42483d0010a261000c45080411050b80c0404240b078032600e00c01006000740d6150158803c082c2d0046000b0032920510315256110303900a0042d402c0440710701c40e449113141e95174954040010b10348941d00506603d070340e116461f642100700e9220004900c20314842c0104a2910658031019250341c080c10040205880b035106031a07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 884917086 1250 884915836 884915851
    0xc0301061b0201140918010603050a18080d1e0e07030201120c091a0d050f0703140405300d06060305010611030906370210051509070e180f 61
    0x4003080803500041c4c25108406040030312500c0000c5c1510480d515078209120a044400c0d010f4240e50710780710014010b207030407219590070500d0300c40103600c41c2c01e4403955800c1055015000c0e5107000b0ba682c0d0850050102083d040c030301c10310b100c0d02c2c01c1d400342098058150764800210040034814518000104a0000303000495130403031a060342d8602c0319034003000000035030340c0d20b816501e052110400512003a10500c0181d0030910320b00401d01a0215160304003038099a03540c0da051003640d403415000070030101c1c02d940050803a840401d9080c44264620301441c151440301c44c50750060202c12003001e925030301c03043c0300c10b40156032100140142d0303415228043c00343c40d1380d240c0020240420160320b0350324410b580c0b88a01c660700c0803c0180c0700d541e0821500015600f17003507041203104814100c152800410050050142c0944214903214000314855a841202c0c070000c0265003140c0f403070900019001c0908200200012501030003141d032903808040d58040818901b100a51600030b0b031584071940c028040b007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 884918336 1250 884917086 884917127
    0x2e050f010e1c1b050906010e0a33020619051017010207050114070e0f0a0306090f030806010c0b040b0907080601080f07050f03060412030b130608061602120c0a0602030c030106 77
    0x134007043d25003400485d4014403c0c20710a1910095400180303000f485640242010b00300f501207449100d0041c4001d0354214004811002c44004aa07800d90f122481120f040141d40d00700b8400041741525a08525080b801855074002c18549618000c4000c207500300c2504056174000520004114007446440b41405182c1d544420a040424000b0b10850140d03168a104496180100b070780303030780c40c0e45000300110b42c0b02000700001e40603440c00318035020f9034107030507804a101d8200040e41d55008020160725903502050b980c045942c1d80c0c1d107804080340090700740f0069101d5442e01180b00e003420402c06018100c0200180030241d100010185485500d4114034000c804031404041281c0b000030795603070050740c0100c00c004440c8a00c10b00701c004061300e02c4504d5010704148040300c0e09500070360084040d2000d080c141c0703003940d95109aa0381040300f1840103000503440000e02c0a80b0136100710217080d007900004251101080b0302d1710380c841644c00075107841e81c092100000400c80d00e40c01120084d009101603102 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 884919586 1250 884918336 884918339
    0x31410030b0a091109090d090609030206030a05090c090a1b0509060f0a020a0516030c170c0603150402072009090c0f0f040e062e050f010e1c1b 63
    0x40380c484041c003601c420b2410b5240c10303100c010003488110400c11000c000e0041442440c1480001c0d80d03401080c41da0001058503035402040951107000c5181c2900c1c1c01416a03840c40c0c40d014a0300000340002000c142260107251000800c50f916003140d9405050b5444001c981c00038041c001c07a000e0100302c600802400002c2100548903101e0342e0036100c050b150105040d80311a12050140d0619400030002442ca0240c80d078410050b21000c3c800209076401005220b208546685190007620354842810000750321940488900307141c80c100850f48032a414440e5120300410f000401e050340c000d90000c4451008111003420302401d4151b4822003000c04480b42402810042802c50b01c8110750b215407030007008402c04030119500c442081d901d4280028000f00114612928641d482e94426103241d08040031140b90401c2c005400c1001000350420b044000d000903140c03004101307405915103003050610a6407404090203030b0700c000c25520140500c0d2240c0a071000d640c609484403003a000d1145400c04d406810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 884920836 1250 884919586 884919593
    0xb03060a0b130b01030b131b030b0616020114120a0c05070b13021903050c03010f020f041211090108030d0f02041409040f0501020d060f0b030609040f110303030703141003 75
    0x81c2c2d039840c1d006100300090140340220040300a480d0710005142c000401072091450b51880341d10245900c005500101c00c12400004100c041d02c2c055a14164012010302c600489920304001c142203541c814142840d4601c05089101260341100d02c88880b14005078040041e0100381d4010303203401c1c0d001032400030710b801040c0c0e56540c8007402c05484482002800b100040854641e10181290504000002d0343c0c1c0070380c1d07443d02d02d41e1154801e8a143c02035003080034840d00b202d0384d40241d9024084000e0031504060a040000400c0d10060006540b127012090403003a403512a02d5149002c1d15251024543d5200c4010544040e982e400c0013461003244100401c104000b00c0e10360000c0c1d240785c100d41680c0c96485908011034044842440034049500c001100a03102003c0ea00c01e504490342404a80600e9682c4c003650000c2c1e0000325807064208100380d0001d00014903c00084035a01d11840e202e10007a84501c01083ca1a003044a181c80400d541e802003904081c1c1c00c1f03c2450b40100003101880c04581140d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 884922086 1250 884920836 884920849
    0x215060607170a03090213050603150f010b1602040207080c160e0103020105070f21020c0103090c0e1b070309050f030a0c0e0703020409091b06090f061b080a030b03060a0b 75
    0x20882c55840400300320011080c1c4207401601c186031700201040d9610200b2100e2800410302a12118820310035020411540904203000e2071140381e459110303100580c40c060301600e290f40085006900308000c1080680113a54038400380039400e02685101e619029000e641a19004151201c510010b610310302c100043d42d0460303080b60660354207103030041d141c03c820b24040350707440c0710108003d05e005005d00b81100608040d240841c040c40c03d40d800c84441c9100400103400300c1c0c0300400c2c0603000d0142c009051040030990700c2c0442e0800081118030b12030142c000302196503a003200e001180050a45982000346103000c10301400102e800314007030b24401da401d90381c0e0101140c1d6481848a20718800000894590217941074a00500e2000703401e1281a44a1520000c903030045080015504942900451543e00c91400c02d0140d5280c10002c2e20882c0c1491825540c4c042c503d0b80356280e10031045202030002d038000c1c000d080d0038022601c0205001446101b09803c0c8100100b0041d802850220080c0c0300c2c1d514074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 884923336 1250 884922086 884922113
    0x4060e030c101503080c370b0c040b0d020a0f030e1515060a02070e0a0507090b0921010506040609050c1209030d020a08040b060103060f0302101e0215060607 69
    0x1d12000800340200c3c038030191203050b81c1d031001e440202d010404041c80300000c0703a00c030760341c1c003083d030b50f1601050035404851442c00803424044156000507410308001800d00030515000100309412078106a501c42c03040609500c28400c0845040e008984044c02e103420a16801440c4d80c0760500380a007824400c042039952089005014080315800302040c000e0780d403001c102d40b05080213031a050780c441c0b0403003010b550380b166813255100e948842c40000302c400d0001e1003000e020702c01e55590454414a8034007242265042000c046a100e20403800c2c5529019503a0360098003401481e0000c0b5803440c000f010071086a0050741303c1c440080c03c0c03d040080340d0144200b201c04204815005102d140c0307401c0c0d0b0301803031400341d00c0c00d9221440c0700040e8510300d181c005510318441d612400c0044c1c1c4a541c0c0100450580d000c82c4512110503100308800d00062030214102d0219801c249002c5244c072400105c1d030449801e0601040015070040301800c0d170000d940c811a00d5001d0010780300d80c1c0c9050f0880d0303240c6003440700c3c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 884924586 1250 884923336 884923363
    0x50c0f09162705180c2704061706161e020c1003051b090d11010e0d121202030f0711030d020f04050a0509060f10020a0f060504060e030c 60
    0xc14010620a0740260302c00e8540000451602680c0014030080c2800342c031250140038400c91502e040080050800d8076100d21401008001c079040c44c0a4054807248a41030f1940200740900a41c0002110f486510485000f003804a1812000d0382c580302c44103041c1023016090981004060602d07a1600c4d400c00c4500d44211010506618007880d5004100e0411000b041a141c0c0440c01c80344d2469066455044030b80100d0200c003070301c1041400801c40d061a4071030700c3d0b2110307040f0b5071803105100410076411042c20b040f007040c1401d1000b010f034000041e120080400040740c5501104581c450031030352250070340081d240c4203c000c500d5810411a0280401001801c0a08100d07444841c1c40c0c402e5410700c00d0301c0365908100740075512a0b80004d50904250068019580100301003040014507103080440103015450240119250b101c140d4140000d41a20181d120250f201d4000d604002500400011a50500407a00024141028a0014151064512401d510381c0c02400082c03640440071403030300711a154 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 884925836 1250 884924586 884924611
    0xb0f1e07091511010e011a0612040201030b010c050a03020d08091b0904020a0b041502010f0507081b040f061707020c0603010b0c0c0a093606022d0403050c0f09 70
    0x16850011520183c2001c201c01055007008440d11103100b054001d0403d0508000300c2e062200166814000903018400e2280005110000800c0155000b54030207000802c045c901203c030007000c1d4032540d240c581c1a0307a044005a108000c038503e100d0380030140c0c9801460302d02c040d02c080c040710510519000c0000c100d072407250034176001050840d03464150200080c41c0100300070745c0b11555032403c420125000503c50000d5400c01021541da10250310400c0c0c070a800b20384481031540c80b210001c0d4180b1510042e030042d294402c01003c103400d060050083c0041ca003a41c0d4845034288449440d403021036010380342806540c010361208900703030b64030030035030341928241a82c0320384421941d6030083c40d1000041e565600003c0320710000c101d400d1160011001d5001038481d5621042051540419145892401340e004545a0307581c0400140a5002007500d40391016074054140300880c031036209511503441c116942080028100108101440031030002d85003124103000d18035141c004664a618001d01c115149030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 884927086 1250 884925836 884925869
    0x30d0c0203310e0c0f0313050105100303090503070e1807030b0a0c0e09070203090d030c0204050c0d15050604050609190609080d03140c0903240709080c0609060310030b0f1e0709 78
    0x7c1d001840003e500600244801c0c00d201c010303500940a640000d07000214240404100c40c100094128110303003141900c00174a41c0e803030109a0704841c0904c043c8155008004001021032900500103000300c03110000005c441c03040a030058280841c20050500650842c401c0140c200d03004400e413080100d0542e41420120000d28048421351172482000303511602d081c0500800d52000000b800c10604142c10030060b00340c0e51500007400914510409a006d20104010702c45030501c1d038094510301002810b03002d090080701c4840d902d82000b5412503c00181c072040c0801803280204400300b150003040c24104000300ca51422a034910000401c003100e018000660384401d41c40030000c02c60b51041c2045d4459190003035210401000e281a1890000283c0301d08021804a901244500640c10000c1079a0701e0703e8500d5041c00000d40000740030100504e060308000010600c83d4070028032504000c091071180c2c1c07511121258144c44100040002d2a52030820062525044031410083d116105040403e14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 884928336 1250 884927086 884927101
    0x15030b0622080a050c010806041419200306040b150a0309021c060e07210209090115120201030507090e04060906110a0201060f080f030d0c0203310e0c0f03 68
    0x414940c00410103203d00c440c4441442004030709844c10b104266655040c40e00c800c0300300800d42d4229201043d0031094000401c0c442c4141000480d170100c440c48002c10040c00c104e00041780d02c984000514401c030f07000020032a06140c40c1c428540d03640400c8888821880316185c0c520380502030500f01c10300b411b83d2040c80d48103540d10088040d8400e00d0b010f50301c40c001c40152404c42c02410004000c656580b1400c800441c480d044011900c044020802d81c22042e08003540030052407080240600b5600d5589401c10240c1800240c0024040d25003015408124001807000408492005140d041001a8203005003c00c12100844c50303000760300407001199528490810304c008148010070750b00038401c0041d0354584560190400c0d0b0032111080d0900c0308181da00d07080107844407140c0d9000300385c0742c00401c0102c000030500d510030300c3c00600c613104907070926035800201d030850310b041c140d501c2e8002c0700f440109445106203005200600741c0c3c00a1008241000200b0034014010300103202000c020200004400303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 884929586 1250 884928336 884928397
    0x5030f0a020d020304080a140901050d05060402090406060f0801080303060f01030b0118171006030803161e081f14040e150a060617190b0f0406030b0115030b06 70
    0x310182403504542c4d0f07040a280c104e1256000d410540003080d07440c00c009000c0320420047e91031407003060311014a030911801c0300030000d1600824840c0c1c400e609101c405216111841020094005510341c814404003124000d05000416801106503034010170800041d91030f218540e0100040a007008158081e0f400f0042c1c4003000300c000e81e04e4440d00c0340d02c0000303202e4090b00411240000504282d80310309200b2900c940946001b40005083c408042000c280800310401201c50005807a02d40710903400c8050200d00c09486a1004220001e45403005000022105d600c2e40030081d80c604034441c0b02c240c5071104015200c10b4100c88944950f640b0941300d0f000440c10b10102500c062281600303003c900d400020f00e4001c00442c00f404000807086e00c031030071401c10b0160100c0d014082c801c0c0b01030b1318200030000a030041d04a1840242c0c12040c00302412815803071324091000075510407081200d241d070400007404080048842045e04140c1401c0381c1c1e80341038540c40d0844156030441138500c10140d80b4003401010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 884930836 1250 884929586 884929597
    0x406020d05090304061218020d05030c07140a0602010b0123090603090109030806031203060411040302060c070e07140708130305070b1c050603150402040b100810120305030f0a02 78
    0x20345418501045032051011000700f051300c0560700c92004500c0600e074494110b58000940d500303048000800403000d4a400c0b204003d00b00c4c45034003203070305e400802840f40b03044c03a40940c05559100c00c80c1c58984d110b85404e60021015001d00d100810044020300c0c0001d02070002d0540e080c14614201b8044140a080b110807101140000380c44150b8034141426168024013510030180c00040010f00860361624000c074001036007030304102001c0d040d0f8981c113041000a10215019440108041000000503262100500301d00400c0b80080c095031490251310420265004119004004e146881c0000102d60001070354241034220030301d15101c0ca0000501110154144c01c00303000c030b00c50020000b440c22110002400c040c002c0c120414915460f12070184141c9006a507040c0e4581c01072030f00b440840e400000c0d4141d100d4002000443c0c64040c01000c102441130f00820703240001c0d440010040301d0403109803124000c158460451642c161280c074001c0541c040681000200b0f00680c0104600c46003a405030741 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 884932086 1250 884930836 884930857
    0x1110c220510150f030204030b04030e1f020a060b031207080c1b06070618021314010b0a05160302150a020a0e0f0604120c0b0a0f12061d040602 63
    0x500c1281011111000c01010015410000742071000281079040754101e0b150854890201c0480000e0319808252071646140c0508401c0681c00c2c000000418064440c1c14002c5010b0385038490134400311030502c08006c2102218000588102801d00b403a550b0020311040400d4020500041000341e010000b0f0400c0303e241c1c103442da8008080742d00c03414403002c0c400800400c2010401c844075464000c8182001815425040b540000c0c00d04c018030225007103401107038259078140403d4075180e14035400104c107003c0104c3d087c081680c0d94000c007544c2c0c040c10f2113200d000d04505c0a0282c00e0200b9014000c00c40d20440703000200c03501081e4440b00030107000f00201000489540c032110700c02c1c030b05040c51000a4000c0c00d008400200c440410061038202014241020000585001e2030075007420000c1d0036502d0903c000310350703200c3c1350b50001414160110180412017041d07030b60501c0803096410020f085006060034845403034548401003084e0f1240d000082c14445000e07641054507070341d0342800c0e4024000d0001c0c06 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 884933336 1250 884932086 884932099
    0x50a12020d0809010902010813110306070e0f06090a030f0c0902220e0f15060903010906020d1139010f090c08010e060c0c070f0909031209020f01110c 66
    0x485825401080c420088001c03039440a01c2503440f01c180b5800d8031880c85020740810b02400124a40c1a4400070354910280542c18080d0319182e1240800d203400c80403604070000445013114511549400303401c2540d0700c41e0464045050410160005c0c40d00d10306880300501031003409640d031081100709019400100380742c4804544400c402400c4001f0010807040c14051104400800f103542e0707500070034050060600810b81040f69554a420061200d522002903600100c2481840b0060b6000d0041ca803000b4405c11000d604c0f50158520241680d84550000f0103524050101108282c3c21469070101c51303525441b0082e0a40c8500c85c0300c1720a07404059151810b508000c04408020480d03001071100b0351080075191201962044031908070390003090b0080300c0390003000100382e5a50500e000f51009410341e405845c030355591106c07001c8900704141d02c40c00f09203449800605c28513812548070401030883e9281800320170750550028600200a01c4194140080c001440c0301c0001d0400042c001a00c02401c0d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 884934586 1250 884933336 884933363
    0xf141023090316062c0307080a0b070306060f0e011704081b191407080609071404020406051c090213020717090906370302031b130207050a 61
    0x1039201981c0001c070348038001c2c4510303125a150010b00d4000c403400c45000366a600f52220f00400792541c21601ca5914640d0240c4090310f0070b00603a02402000c004154110051406403001d151180300c0b40c0005001100345858440308200240c2c00a5581100200ee4901900c0410740c050059074001c01c200060038500740c22004020401c4400c0c1d00170040071404140183d28110a0f0701c005540300c0003500004401d2501102000c0058411415a0141c00c024029101c1c2c850b103030701000e4034144003180e0314500d96015001c02c002c0302d240c4080c1000b400300c1c02d403019403510382040f1003d0801e1280c040742c0c036403888a1a140110015140c1c2c4110300c9160700401008010b034021001f40c0c003a42200c402581c8020140c40d40080440341d04088442c0b14902038440f505540d070301c01c00c00c80c02d080085408a043d04c1035028020707500041541800304e400c000e90074912042c0c21b60043c1454100b1150000403064510b00030460f8940e40c040702200e840300300b1400542e80b8000da1404605010b0450b6001700803a094851 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 884935836 1250 884934586 884934647
    0xa05120c0903210405040216021005070b09030f04170f121c0b030d051e0a020601150521060301060b0408011d0d080408090a05090906070305010f1410 66
    0xa1407041d1003102155886030045001e04119030716102d00c0c05150070204410007403402c043d001f4104c94000710400000c113902c0b40c1c0101c1c04414550105000141000540900f08070502c0300c2160005003000066082c501e072020f40700c42e1481580110718081069052401c9500c0c000c00085965410700c4081e82c0c114030000d0300d07143c203c0d000301d150070030f2010b0b180e04086a910864031070610540c00c000d000b84441d00441c0da00340c8165010b8485d1441299101400c1d00803042d03450001c2240c3d5410398000c1c04d9940c50400400020101c00300f11a00f040b81c1041200e904c859003440c41c0082040d17814901151b500d51400082c0184840d900c241003054020900060030390040d0b2024028550400100e00d020041020303054440c8803032694800843c00210220b000700c0d1071540603015020300504050340c2581c41c0c80c001101c503e41156091100d0340184100700c0f429a042c02030ba80180b6100f41d1a21589040c44103c80c8180b000301b40742405a024400700ca00326a00c900c25009a080f00c00c0708407850185080d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 884937086 1250 884935836 884935861
    0x40507081e1015090303080603120f090109030b01080a0201020c040b0303030a1d1204090b0111190c09050a020c0d0206010f0e06062a01110724061512060509100302060a0512 76
    0x5c4217401180c01040080c0003400c0200f05440807481c4400074a00e44500707840f91011580107854180c0c1042001c0700007000091803440540d018180c42c0d00100050b0b03d00b4800289000f04054a21340620300f0a41c0c1c05166440000a80b904205100404544a07008070074030b016800c0c1200c4050040d1280001c0c54078182c040400801c2a115404c1e01071144082440054400420f88000300c0c01e0fa41c01146e851844400003812034400ca4800d038034030f00480740c0e190f1032807007658010351740e460510ba400160380080c80c10400c00e1040d403507000e0014118541c9000060300c40c101e568401d1542540d0b840f00040c0075a610340c0111010b402000380740c031004418020001c5800415000072040d030b50700c0c2403040e12500d0441c0013540c94a940c010100200710b811804151060340f600000e035904903807900300120b103540d461004200380002c04d60341d4070101e01345180c018065403550780c0701d0790190f1020014841002c210000e02015642c0654034240d039003500201c1141d02c1e11500b440b03c2c0c0e07030000420510a03400800c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 884938336 1250 884937086 884937089
    0xb100c05010513020904120e04110a0f14040504021608040e04140708030a0e03150411010e0d050a060e07090c0f20061f0902070b06040507081e101509 66
    0x40008005035650080304142c000f28641020790710580103400280010111b41c0d8000c03400c0454035144490340c0144000c101611340001d02c118003c1e0001c076844034000d5100340354a080800b81d05e020713000e0a090200900c0c1da40b2a50160500590300020035841c80f00e28403c090510541c0a07240582d503540d14003c07021384045c1903c0c210ae29244519030001d003a000003425900b940c0c0854013451805412880030b841d104c002c4429113416003d428480e220300d000c0c0c2c9480c544690301810b144c105000288000600c400900212107100e034140e41c0f102ca001c124002098008d10b988208001090820162140d2070103401e40d0040645504040382c8002c026403010440c0280b19054403040301c5030b017503050744007851988201c007500d40d50300c00c80024990314010740c0030206200f41925000c0b2120386506410040ea444080c055445c120041b05100c060708162090643c0710200c1e1400c80da0718101140d180203103503000c0b0460300d850710004e808680340e0100c0ea014040240b943e82600c035262484104050b0180945 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 884939586 1250 884938336 884938343
    0x91b0c01020729131a0a0501090e01060e1b13030c1e12030825110c040b0105030f100b030702010f06170a0f14061008010507091d0a0b100c 61
    0x2411880020001c0510001c16080c100103480680343e482c1072182c0d1100d044d0f043c040e5038400702003000b448442d100b41241030041880060225003503051103e06015a007219080004580c5052030800400c0b0000f5916031700300700420545c091400b00f11003107040501802490110004400d80c0000030061443c2e0024201c4144c4011017483e1b5aa0f0520740c00c40c00002c2c0320305180400c042c01c0007000240708103070380c40e40306110840c400e002a10414410199070303000c80800e000b01d5100031000368440400c1140344203004040b10300b44203840804000820b039000107040260f1150310303100410350141c0140e218502500041c00510303180d103400301c8020b000c2d100c410310170340350b05145c02c0d000f00303e21103400c0c20585000ca03100c005150f0100c25955001203550341031801d55240d030302c1c100f4903002c500003030015600400380c141003201500d040440340d03400c40e8005040803050100e445403c000c0c01180b2200741850b00d5800703c0c40d004170f40c2c402648402905400e80c250768009213642450700361030340014181081601 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 884940836 1250 884939586 884939603
    0xb03270a1b0f0e0f010311031513050c03030c0304060c0c03053c032a0a080307110c03100b04020909070305090106080615060307170906181605091b0c010207 69
    0x5452283c20f400c00001c1d915041d5082141c40140302141e00310b240514048006411200a1616a40d00f042c0444007683c1303400ca404000e031440414000f08006c85401060120080e5103042e041103045651b81c803440c0300398000d001005014506000c46140150011074119040d16685c101201c0c01c0100b03601084210000ea400850720b4550101201915020881c03d42c00218a4070295030f142002e5a00c00716448005040003520a059104c003e01c640528503100d4a04d0039140d0600030005444421000c104040701ea010b86007003155550300048810f4001040100003807224190404200603200c4d40741d03141d802600c03000910181e16815400385e842005a04001c1141ca81c58805650b01d420f02581d81321044900e01030210041e103440350007540c204205d8280391410301080145042c1e003000480307180c000f40d0803801c204290380c240405065080d00300719001d00a031024031651092442040c1c0651070141e442e000020b40f0b82100103080381880785050380f03841d0300c0310344000c100c03400303503004400441d081003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 884942086 1250 884940836 884940839
    0x30708070309090c05070507031e0c2903220c090507020604110414012d080a030806040504050a1709130209040b0a0509040f0807020405130c0b03270a1b0f 68
    0x280311764151142c080e40100a00038040c80c60300c4034840300d1603407034aa540b248000b064031400a4000c40e813110080900140030205010003900d441c071b40c1c01140500895201c0100104031010720072056403100e0354281c038100410940982403e01d0160490303000108501d01e81010302500980001d886480366124002510000b036088061005580000b90030303408100b590340c010301403000024030448412190075001420b40c00c698000d422400125407083c02590000d1000e00185540000c00680c0007030103032014051810b02c1d81c0c41a036200f241d100064804600e15042801c082081d404661201c500100030520350450703880b80d0802940140250341c851807a044d880041414a040580d040b908000c00c02c00150341c1c0c80d11340c0034a007007481400b00c1e07014208101d668010380c0d80d0b100b000d00844518845000350b0007649011188055a604852700c55a418006c100b100c43c1075060b0700607d881030000c1070f44400c900c1684503203000c0360f80b5001444041100310302000b000002001c40c04030740e0300710704080c90513 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 884943336 1250 884942086 884942111
    0x1d060f040f0f05211809090102070f0b0703050a021305040b12060108030903160b1606090f150c0903050d0e0d12170f0c0406210603060614012d0203070807030909 71
    0x41c0705410700c03090103984290100c0d0340c9140038106158440d00c0707031001500d040c88660b80c40d222f0141d154000c40c0c003051420f00703003d0b071143e01d44901540102c64101c111315284e4040300401c80c0304910700c140ca200b2501c85106e000700d61500f900d80d1148a4910701242c819503102c07040941c42760007442074140a445158182498801d0040b441c10403a601103c1c014a080e20102c00c5402e21014032a01740c5079281c03180c10700f4000070000444440d03581d0040605410626850b03040405866060460320b08101c2e2500301400441d40200b42c0c40281112410000900c0300c401012404050300e20380c0140c20f40301d03141c1c1c03901d00054200700178521290300d626040c40140c2e298440346c4400003054a120074a20001c0c003080c0202e0b1f0003100342d40c2920380101022003492440c0001c22064034126081166400d40320380c0100a0450590807041c09080d090070320701c0318030130312000142c0c074601482e1030008444208116080b100c0d0083c01102d040c03a4105102700d599590300d0401400300740c0d1724070401c16590328115a03030400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 884944586 1250 884943336 884943403
    0x10c0e0f0a0302240c0a060e010504120518030f0c102111040e16020606040903080613110304110f060a02031803030f0714011d060f040f0f05 62
    0x855500070450600941183c080c000104075200180d00401da03118011200c1c031000740054400d940b040401404e59040500c7e1660585020103d050b0f01781e81400e00340030000c0c60038806668458401c3c645035440d1590040d005202c0c0303401c450f04a0b0103020304040e09810b15030115840c80342c84800e44011440b90030000040318100348030307407041c3e02c0014848520720030f0402640103519203900c02d854207803d00303031100195400f038082034820b0000001d8000503540b9554051108a40c40307041100c040242410700d03100a80780550007003407544030712210007004000e50301e00c0c1e0020b030200d0311071041140c4034030300b61038041d1030700078840c1400384141c00b15400720090380350800859050084650181d03003080307440414280d5418480e080c00d40e1600040c130840800040101c00350080a0141102c2520750790ba4407001800c40f4060100b00030401303c00703c47c2c2e000031200003030100d40040764400c1070881c941e120b00b4126102a40143d005003d03828441e40b82050050001d01d4210700869005507000165012005c2040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 884945836 1250 884944586 884944609
    0x60b12010504300302030a090b0c0c10051b07020a09091b050301180803060a05031606031a2206051f030507020f0d030b030f01021926010510030b0909010c0e 69
    0x890700700550141d00210300c03c0c5c01543e0882c3e1415404641c03441640e0343d070022050221099010880c4c080340d4011010320030040186101b03c02a01000f0710300341400003181d00c81146845c040c0412000800c0411522100349510081a10140c1004a0026440d2001003034100307034280b1071500c441003c04100c51a06201e00601054201d006d01250b00990341d803c8010740000380440e07031141e08110005403584040c0458001c1c4503144030180c8115062a00140454a41030b011810030f40b40c8000c42c1c00c82e6140c0c102c2403010145106407507050307038840100344009000c0c82c0e08040e410182c20002c0c0c800360104088440701e103145a440520580d55800e004070b90b11030540c81d42d1140b0743e00082d08101d031135010398810040440080d043d144048030714601c0a0aa81c0001742002181d1012a80d6842082d0700c2401c8190070290303507010660401e011019040d000e88180540b81c4640003010711442d02d00c0c02a03202d2268030030058415101c0340b6128255034002d0003c107890202040029640c01143d140c1040401d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 884947086 1250 884945836 884945903
    0x450103021207180e0a15020d1503111909090303090308010501230903030403020d151401120b1302040f0501030b06060403020a0e0a020c1515100e0d060b12010504 71
    0x1400f83c154203982002400e8002d030119490b0280d1070040d40403d03094402c440f0030140201005d661181052001070131101040d091032008041c568041c000905541081d4920b400b01315922901001c0c1010000d45820041d8004078146291803406010160160094845140691640d04242c0e030713118015200074041c060b0140300c00c1c0401d03440302c02c1c12075070401078405100d0140490381015203980c0402c2d6401d2f400f1030140c4961651001c103440ea41030034020030b00d5030755071804284a65490508451801e8500c04001000d4015040000b01c601d40780c012881003681d0000d0003404040010f4004c400149420300040d182030441c1d90000c6d405091041c120340441c0e038058005c941007442c10399002e00c4808080d140b0300515400300603607214200100b00800f050880011805203500700600f90441508006030304900440c031500c0c9002d000e80c0c20401c0c03c0200c04c4144c03150500b40c4403c0c9002c0009004110003168001c0c00b004074074030a80f1056118505c95032040d901c01d2602d002c1c80400302e60bc0303100140c004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 884948336 1250 884947086 884947109
    0xf06090601030c030b03071d0702010b030d0e030120070611031e040203030d05040c060801060305060109090e0c03100608060a091101140c03180405060a05450103021207 74
    0xc0c2903500c00c0d403010b50030822501c0e0018003691040002824031a2960007004005404500515099250070500d5007009560000304959000440401d4441d001ca16000c0140b04004a407016141c07420f420202500c0d0798140002d240215540f4054616045001c0581c1c07072524003640242c01c809500704480c0980f5940340c0b440d40745400a560020000001442203806004c2401806800440e074003407103014a101b540e40c8840d0b1803d00b2002000b140d0140c0c40507080500340390601c20f450360400d8103032003502c46207180815001c607240845072030a0b004601d56500f5210300d1103032144451045d40300c04103992000d4152011503c07000d4052041c2c4510000161002c030b8000646c519560103030680988005248180310b040c01c00701d04440f82140c0040400284030b01004a0103c00d9240c248500e0790710050468400c1240c0e0b040002040e80410110500400142030504c002900e1804030824a12954071382846118a0410510103501000070301c0304a0040c041c1d8000d9031240200400c0a40980700303540d405 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 884949586 1250 884948336 884948341
    0x9081c06081f061e050306100e0f0c1b06010501031401081c020f01060b090a0909150513051006030320030904020d0209060307020c12031e0307090509040b07080f0609 73
    0x401803500a07010766009150b9071442c000507243d2203012400d52001302060100420340c540030905060410080c080381e4050407070031040c00002c160003140c940106c2c441c0c90a440d50395036142159220321507800d0015940610b40c141c025401d00002e245410b0701c4081e60f0610050b100c040000156030310a00810f01c7c40c0c4c10041e513210700603e0016510303415103a10320484240404038250242124201d0308031100b202d4000462440c2400c2000c02c0b80000d0950500400212160b51a40c010115143c5000300500f601c9202003910b80e550181000906604401910100030b401081400102007138882140810143e9018613811007a907000c8000700e02050001d1031400109004100007540301c0701142e0940d541c24404401c071034903020040c0d486507605400070040010140100030000d0304000c000600e41d4010003001050b003110507408140000b81002c03041e00c3c0d40320b4040c03e440c070080f66045180c000794650304000a02000710400c50241805441c0c1517a90f495041c4050b0040100703c603443e80280c0760002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 884950836 1250 884949586 884949613
    0x3060f0606020c0d17130806161d060f1201090f02030c0714030d09120e12030a1b0b041a0c04031101120603080408030c0f0d021e07080109081c0608 65
    0x1c440c00d940d03101e4000340540b140f00100c03010030b64200d040801b10656000405002d550030400c80c0c160440e80e0503900f05007000c01084001d2003000310307103000019400d00c98140760144c0c031940103403065008002c000645644807012074010b114804d114100c102e909010290300a00301714801c40780034540710b0305100d1908207280c4039508034480c069541c90452004005a408043c010301c40c400c0d849101b1031710003510200f032442c02030035148890080e078861010106080b180d80300c00070444107928a0b9090140c02c40240c6850185840c02400018250800c01001c00c01040700c140c112200021002d0146403058582d012903000d940100c0c08000d01d01050210b0b03140d2039600500100ea45282e0124020400c20f45980e50607421b904507611059075a4800308129a009030f0a012042c082c0441c407004040001d09208001d50342c815444183c0841c07100800054140030041c44070b0405003015400030f020304a003602d419080c50740070b1800380c10070060041e40d122030003140d0300403041110320400013440501d0b081003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 884952086 1250 884950836 884950849
    0x171c051617130b0c07031e1e1e020703121b03141b1b0402030c1812010203041101030b040b030601182301080706050c060c0703030902031603060f0606020c 68
    0x41504010ba4032003100d00d4001500d088003070b881990340307040da2510f8042615001c1c14102c0c000d034410030401a11300d401c8010395840f0280105c2d2040d00f14104203d0401c406040e50341415407890039a4104001402408164000030380801701da200e0500365191802a4908071a2000d000401a108541e4100c07030b000480e04c81c0404980b00101c100e4450300d084100280309111055080301e00069420000e440025250840281102c0c401d040c0c0b825840c5242005105011b48a0740c0750f43c80441c0402d0282d8082d5449606640a802d064200219039a04240c2007003180c85a032403007624002800e00b80d1020f054249030059039841d078000342c000c0c000c507400d14000c801d09001c503c0d084a460380c0d840e181c0398214a40d040c4618076102002410408550520149505082c0b282d08654188613042003a120806c0d40001d6855128160040c003948510862400304c0c00f402c248400654980710b040c000701541c060100289080300e108040400c413008150058205940e40c80c400c010240c0c00590300342116003040b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 884953336 1250 884952086 884952091
    0x7090c05040b070507150318060507020312010e06091e070806060c0a0b0f0c0703020a03121524021906020d06030b091e0a02060412171c051617 63
    0x10300345141019110780c1a14125081a01c040da4954494841000a0b41882c004140d01e429185006d12411750f4201032103102400c03040005090542e14800640b54600c01c1c801d4403410350001350b2500380c55035921759101c1d1072103095540501c51030002001c511101507440f52920781c51100d11132441c0e240e48001c000c2e140300b41d000300059000581044180d40761071043c0800da066900c56003040e8458107000807080101c503c018044007540b8010400c407004039070009168a45207506203401001105269070480290012010607150b1031074001c0049000ca0341805404425440d443c4281210500c20f001260f03280d1303031421070101039005500ca103804544250018151100c2410703004c5504c0b070380d03a0784444402c542100c241015401c00d01c4014007c05803402d98980200084004007900300c45c03500092070302c3c811481032070170840c1c650014908000c142c090304407030300c244104050b0706d82d20880305103140c0c0340c0b400038030003080b5141a00040178041180707018091419542c0c2d501901104540ba55268034101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 884954586 1250 884953336 884953361
    0x60301090204020d06031505040c03150e03070b010509060d03120c03021b06010614071104052205030c010e03030f04030509011101052505070203060703150f03050f060606040303020709 81
    0x20341408901580b101c1c0010034a072001d0000018846142d420001d0a13075090710703003c6140302e040005200c0429800003508040e290010005514408004100c800030240706107091600e000106419017440342004249040350403e64030074030195940010840b1004418074000e011501d540d0b500151003245900c03030003078819075060051900810718880203214205400c000102c0c2d100341e0044c030985d94803440d0110150050309600e410a15156503441c003440c00020b00314081c42d51440022039200d0184001600a0f407010b1100781d280700701d421b0660b00c2e03034401c010051096080c50844428031000204403407003510b0500700e007122902c86a13400c99090307020300c007001c0c10024074a042c0ba40ca04802e1003140e0140548035070000c00d00c4410160b440c0006800301041051102c2485070304d02585003c20348581c00b440a02e0009a49568217071001d42c5070700140c201900032418130303102004002e00081c3c0b110090410038115240713a03130381d0340401c9020f11540c080180144c10841c403c01540c0c461790400c0590624 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 884955836 1250 884954586 884954591
    0x91509260c16080706050a0c0204181509021935030d060312110307060e01061527030f0609030e090a090c0501021914010209180a0b0324060301 63
    0x50840803280380410311844060070707450b5120100302a1070308005400042249092036130610607025001351825003a0380000e4001c580700d40441c02c2c0520120a4014500e50204000c6004081607c4020003800001b004900503481c0b00700407903c03412a082c04400301d588940107600c1e02c518030305900c0c054550044091001c119131000702d9100078000d20280c91501e5100000013800d03840c40c01c0001d89a80003442000030302c880820142da520101004555450345c0103d80441c016283d6611540100340651007000c00100105144480f158071070120703611000c0c1d04c4003070f0010260006080011501620000b08500802c408200008010b90008103136036000f424201404040c440104000c0d80080f40c1a88580f95136000140400c205a03060f000981401c0c8028a882c034a10740040429940314000070f4840c0c0e01400f120240c80c00250112409840c0c060003899031044544800c600c2c101040d034010540d14244041c01c1840d003000140c1d40201c4004183c00c0d00c051880c40040d880388a00900344070f40654 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 884957086 1250 884955836 884955847
    0xa02040f03080715090327060914030a08041d010e0105010e1002010204120c03020945100e06010801020307080609070c0209010b1b070506040b030c1b0109150926 71
    0x413091141c1c50815000b81c6900ca14448160b80b0b814000100f100c1211010340d8810302441115446640c85c42541c600b80b01251140204000003071410314140c600070400f0130b002174041110103120207402c1c1c40020601e491015641c07034107105c00000500340a0b150020300400c0340301506143c00c441d400340c800458000185440c0e1940c400002d5031200712826248440006401c00031030510741090395201082076144408401040c111101c8030941c446045044c6215100302c8400c1040e0a10100d00304001c44c08403040f60107590b15042c060400709460034014040c0d030000141c40c3c1010b008072481058960741c0d01d005640d072581041807440e40540841c041011400c01d250042e01c9081a080c00f1f4401014802d03140c62045e07030410f484d07070011408546c0c96001740c2020400ba817a03903015038055800710401940c4030342c1e801c4d500d00c000c0d0003600c2e00e980300d96006110304880c0c03080c10b610401d04240141e0860f250402038140e40c8007581d00c06100108404590081c0b0341341501c1d440214040079580020843c03520 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 884958336 1250 884957086 884957123
    0x8030d020a0c080c1b090f04030f0302042607360b13090c05030c03070b0a030b0d0609110a0608040b100816050301060806010807170c180f0a02040f030807 68
    0x190009020404c0c140d10109920446842611540514050441b0351260518042c241c2054040c4082d0006040c4280018401d000a019405490180c03000c0b9101c440245040c4000103842e003e07403482e81040f401150000b255000178444440018408040324141c11040e90703080c0c1e012008141090701140f039560700b4105195070b8070040c1d03000c0c2d817881640104512000303040a00001910341d01861017503101070f020b00300c561000300305502243d40b240c44041d02c46030107a10681c06060f104c05c500c0c0d030058840111004024803a808401e2280c0030340d0004e50058038500601c050785010303002c0c4002080d441c60004000413103d900d06070740180c10a40d406e854035605c61865143c80e001010114488000001c280841e09092203003500605920000740019498001c049072200c0f002d0007941c001c01c4400f041000d11381e10030000b10023104006840c100e14480002c07604550018241c842e084040d040c0000b140555000c0d00030f40c3c0c180c440203844c4548072803440d83d5020540d4001075080312405111008421036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 884959586 1250 884958336 884958353
    0x313020f0405070329011b0516030305130b0307050714122b0204050607141609020c0c040507020d0c0519060e06010905042f09070306080f0708030d020a0c 68
    0x30700d0190701d01140190040c05c40195107480c100308030460b01c2c622421803602c0e80c3d00000309510b000c100c02d520b1054284d203003031030360900350840248000109010000003c0640c0310004048650f040c03042141040e4651402d601d1038132055a40a000800a00c184008120508442c1c00001d0704d81c4200d0341d40100c0300c0ca540c0300d10341000e0b40c9a26000c610041782c1030901400380483d2110310b5140b50440c40e02d07043c100061420700602201520200c41d214403c00283e20402100321040d080c10b440680b4070b5510003000000c1e40c460f00d140441c070b00a0b202a1030090030b00c2d0240c14000d41154010740f0b440d80014808982010245c0d90a0b01d081c401c0e4280c140c6074040c000280703030b4000e004000114041da441252940b80c83c5041c0d100c0c00c86c0038a04010003021855030220344860400c080c1000c40040a00801082ca401240cbe442a91010700ca409014020350145e10106c2194190010340f0035002c070008015458064910a4040a800c00c000f02c000740002c0d94010f041c0142070341800321070329500740c0319000d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 884960836 1250 884959586 884959591
    0xf0f020d0f0e1f2a0c090213090509010b0f120d03020d06120804030201020601120308040b040c1e050f0105120c0306060c15192901020c060703021506060f0313020f0405 74
    0x45210141e044000d00c00c03a90314004d402c00b0405108441c0d90542e62902150240c071b03c181321105038041101c005041c2011006002032130a07600900c818201650074074003c0440800040c42810030488180311070905460440030b19040c3c202070040040040011b5010754414484d12444580d688c001092040d000ac100560041c05000c2e001c0e16181140f0000e40303400c2c01030f04600700750010000c080c3c0020350702ca40313120f900603032110010300709403102d19140800d040c4a401030a00c050b422802051400407142c82c110442c0d4086410800c280c8404005503500d11500e1200a81080200c0014500c103400da002990049805884646000812409a400d214203541c464040040078030910034044419100952507004403803080120300700f000d00c004c600010302c0c1003000300c040030455401c9203a80280b02400900c07a010748025552011440d00946a0054460400404200c1c00108001d414a001031310f41740c0d030b5051020ba10b0358441005880d60b5022403d8100c2e4000d10131102141c41c1c1d00e49014550 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 884962086 1250 884960836 884960899
    0x409052505040c050403060c210c05070b131703090a02060309210c0622020405040c090203090d17060a0509041103100524090106030b1c030f0f020d0f0e 67
    0x64179103040d850501d05039407140030201c0800901555191100c003054550005044084000069210012006a80c10b00405501a00302441714040005480c09000000340700c61190310b98054001401a2030f00c039070300054500301a6903020035a901e0050a10000454001d01c00c0400c585980b80416030f0a40503607072001c0a110581c202044014400304c0c20070400340c001005031460300600406501e04500703204610780c064030503038030350020405000e22070441d540a406d06a109542e24a0820300c1c032a500d41d80a4000130000d0302c1c07141c00503056400f04500e60700801c0c0040042c0c1900d0f00d4030341080701c102130152003a07a1703140b8506203411455408001d1500420003031607012865203007201c00761408059403501c80c0b8982d009191640b100e07a54003001c1ea0706460f21820300003140c50020011490440c0180325642c00e207140b0001354014160031079401450101e2581c0c4d03080c90803103445001c98442e0a0310017003a007c42c0c8201e07802d40e00b46009030281d10903541c000c0c00110180030340c4440c68070080102000035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 884963336 1250 884962086 884962097
    0x3030801180f050a2403083009030406020f0601050a0504021b06240306160810050a0b03060405060118052202160c060203071a0a0605100806040b0409052505040c 71
    0x404100494641c5885c150701a17504882c8420b20310744039400c0e07038803480da460300d04880c950348020b2440008229203070350108421190001840c0040d070b1141d40f80d016024040240c0710302e40180b20600c800141c0181a6400903200a42080c0340000703210281d00410408440c02c01c0100784403020a10030841c8034403038200084802007440e1400491800040241d200a0103604042c00b0894003445c40805000103000a01d01110385d5621140480c022080c5900100d612001103a00000d218150102450142404407410801c5481d2040150b481b80300305415100d02c86800e003020001e61402604584607551038002003040e440e800c15021080b640200038112665014000c4075041c010300d400980e01600c2070340010362800c1d68580320500003554015400409140c0344000a10b460104e0704214000c0502510b11551443c502002401200e82101e0040c080c1d894401d0281c014036060180349a000e41210151040b620000030001d5480d00003148041017203921117002400b80c80d103114078204103030300e81d442 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 884964586 1250 884963336 884963351
    0x1309020405160503041b05120a0614011503090503070827010f02030417210c0d03060e0106030b1f030605090c04080d05030a1b1101140103030801180f050a 68
    0x1004221840540541c00303440b102c041c5620120341040071a90020741000e03903101c21507030600d030a480c440b070603030855604407895191000c15000001203c90805200e00c030300f40b01c524018039840b080c6510034450f20b50480022148020300900940c081141c4070b00032810390381b80a1542c0c0710140940d0151480100c2040c1c20445c40e000e40045550b01c01d49030030246040d01d00c01040c070000035a41e00030350144114000c0800381d402d0469400304103c01249007038540c00e1043c80c4565820142d0358003c00c0c417800c883d0084014000e00d40c1d10030711905c01680c0403110381c14181d17400c1c490210000e16504100340e40100010410401c1c9045a000700b18050040c1d03540420000e0034a400e012807a01c02a0481f003681000b4002442104000704904d05480b09618226480c1d079202c402e0000506124080080c1d600500300c18812515403001d50740380c1030200c02e0000e1080600547c2848132030282403001800003040070005101500d043c1d00420910002444007040c40d00c55050030f1070480d030045d00c0c0104503a42d078549 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 884965836 1250 884964586 884964589
    0xd080705120411040e071406090102070320010915090911070507150e060f03041e0c1508090604120f12050c2203030c03054b04060c06020703030b130902 67
    0x461340950100301c01b4005241c03620b0f14480c0d58180c0920305610030035006c580a24141d00c00c104990066400500c205c46a0190788103414007103203480720f0180010b03440080480d07a280e9980044040322095614042c0003071400085500a002c10514107101c00000c100c1100407800810044002d4a000540d46003141186500a0550f10701c451109004c1d0800340400280d2803e580c0c1070701d5225130062410030710000300c0091001d6204651000408078110703020042815a03042455280c10461600c401e00e142c0ca4098005548040c00c40b4010020b800020607541c0c0707030b44910011040c03a01642001020340035400304100c10b58100300e0310b40b8444000422482d0541c925604c403200c030342c0d9400fa080b502460079524024041810618007078240701001403a090120800a107400c03020360072202d0300b0380764000c0c03030087c0714482d80d400030503c40c03c14007600312414501d41d24100c500b1103280b074884071000c0e0a541d403031601075001203505501f41030780c44070101c0e9141c81c0c0035601056200c00701070015850b52180f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 884967086 1250 884965836 884965841
    0x804030c0f1106390316240b0103050106210b1302041403070909050d140405060301170105090d2304081c1202070b0a0e0c060a0f08090f0d08070512041104 68
    0x31101001d4440804d8542580c0f4007100b20f401c0e0000c204a9442c048400c5e050046400507542d01d84040d24800003ea0f03007003150f6507031011800e2031090b03a0500690743e98940c101c8810f100c502d801081c051000c003102040350010303841800c02c7c0c44090520304210440c2c0c0741e480200d030026031108012501480d06009140b4050040002074504004200209889c9458081c4d40780c200b50b031080309000018202c0d0040c0039140703042d100241001000e05981b503840350110a0071520501140d000380d03081001085c00014007264546240045a44050104001034100b601c0c09032460809408154204004140b6040c18001c90000c0c0d11402d840d4580703ca4607244c01400755001c10780c085901803040c00117030002a81549030300c1c0c0002030f101c40815400490201c007410904105c4034964071880006e14900c00e103030413007920840c07103400c2d80700c06070b03103507118030034692101841c8507940340a81014140461141c020301d15946c00c0f0201e490110b0408503800008100040142d0b010389450380590039100092070f090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 884968336 1250 884967086 884967157
    0x20111070e010e0901060315060501390f0c03120f08040c05061c050a050709080c1011070306380a050103110702220c0804030c0f1106 59
    0x240080081914003401541510810b018041c6110440b4000c101910700c00d40200380590b42160441d1041c0101d0b2141c3d400403c95441601c3c00300703081c0b88030000004d903501c019200d4000c1d040c407030410340592200211441d0a1a0508503444000c6200220210303110503800000b551080010491000100c0b0028080c2c00b41203220504004940007040000365003d0200700848000b915481e0b01c413500351010305040100e40e94428003480c6081c0401407a601503400031409180c00d1b1f00c03441c0b5090340350040103843c1c2c10340000550300b190050b00c0d882c41c454404d8401364400b05800003a14810740d140e5840c4001d460410118012600b2806000d80008481101c1142402040c5640b2031646c881c1c070010420040c1148102818981d0340e64102054a42d020111800c0980c0200392061441d201c09100c50001d20407003042d42080c2c500030980b8102c2e0b000d2110035008030b4060301e400c102002250b9400004542440c1d0454600382c04410f443c15648400c0c000e4841259883c5030803d55007a000c0c0303104006c1025 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 884969586 1250 884968336 884968367
    0x9010f05010519060c0f050f070501030b0111060f04140a05010209010e010503010e070e030708030a080115050304261306111006050a0501031508060108030406020d020606180403140a0c0201 83
    0x2507002c3c80f102041d1100000455150f420503440d1200b00d03040001d4a102c2440001d001d500680d80e0a40007514003050700d809403402607c00f000041c0703c0c4001102c03100300f01016594030b40d12178004250465000c40d03502c0d034003510500100b084101c29a50541c01e050071480201c40c0743c1e4011410f962030f50307003210550b5044042842c1881c295032414040c07860b548030150080061200006648032035031818422030010700103850031250b540052250091a8050074400d10381d004411003108111a4443c42c00c80340111f400c0b18a00d04c0114a214080c0c5030070750f0316843c54804240c00c024250f002090302084000070401504c8600d0704d10580740865042600072a040c1c41080c2c6000e0b4240110384c1d030148914140d440038600066400380c8111a0382c00b6030003a8204130341e144a148000142090000010400d454156095451200d54500d041c0ea80b1501034442d10343c0000c1c0038502c01101c800b181d49941c0d025009207000e1381103005000d2003154075404030350031200055802c1e4681c415942c01035000040b4110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 884970836 1250 884969586 884969599
    0x8030a0f1419090b0402040506040f0e3004050613080d031d010501030305040b21161404081e16030309260a060207140f01090c0618050f13020309010f050105 69
    0x115071381c83c1c1d550075038000d0009108a541d42c01140032500c40340d000203070800c0326020400040d42c0311180d0f69580e442d8401c506404070000c10307400c03451131605644008045201080c0c9420319041030300704091500b101c0c000c00000241d1140c001600380e000c0000d040402d2303442d180000d003000d9100d5010b1911251226400103617040c4401000000c1c2d1100444040380e40729034240c0d417a09001100a90620301c200720315010f107442503003401144076004819920420340740d1a0b0f07200e1252003081d50743c4140594428081c840d0003a54460f41243c48d11519104101c075100141c3c0c1d80120540c101500c40450f0f074200381e0002d140c0080902800c9014500481d00d60b00e504041c1002d103000c03000450384c803030801c60014100e40d000704140041007180c400c0c0c100e00102c4041960820890841c1d880d00030108140142c0780c03c0c071002000503403140107a6030240780108003c1a003042600700020b1004906030a070b8070b150401c010444c810041940d5101850090280100104014100c84514000e031041038000c12310400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 884972086 1250 884970836 884970851
    0x1207090b0903100507030e1b01021c0c150608010f0506030c22090203030903070303030207030f0e0913080f0c01090c14060d150b21090f0a08030a0f1419 67
    0x64001076030200a03c225140410305603105081140908100f400096591207680321000c15001c05840c0d001c040c100aa003201d802c1c04410402666240d0711000c0400401d603004952008105510380c1850260130036035020036569940c0c3c0e483c03402c54400345440c07c1b4055a07442400b160f80b8050003010083c1804a6140400b07520200c0010503040d250410440000d07605d2501600b151410300075a007110798014143c0350f10550380c1c03e01801030350121104400040c0000d01c02c0d2050b601664440b03ca07210b002d080d001c003590300c0c030403410100f05c400401038905000501014403020b200704002c000403c0024004030380d501092901b0b01c03104200b0f802001c4907072104e0018130010b031180001c3c0d858a00075408007140e0703811300b00c10703010442d00b49801071003084a0000d0740d0b405000d1509044211840c000000e0304680d603c0c030030b40c0b40e01c801001c0c5914003590040302d00c2c100401c8890700a580c201c2e03104100040c1058204041d00304607601d170703900c020f00c0e211604100104031400740c62841c41d54020344024040b10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 884973336 1250 884972086 884972089
    0x21204052d07090f0605030f0d0e04151412010c110714150703050d0501380a030f060b0304060914030304020a1815140411130603050405121207090b09 66
    0x2c420900422418a50312442c03e800c4000641100e002850050103840201e0400e145498843d50090000f9020521040150300d00741050b100f1460030050b5003415541c5141420a8000c10b0022209580c0d482504072500b402e0300c01c000e02c1010001c10007500e070321608032150102c1c0d03824075019510040c030304941050307909007030b880350481104140c1c1a4100584d80b00726601d01a103943c06100c13180745103940b070500045080c603500d1702004022120394003001482642010114070255140c0703031501010b0410f10901980500076002061062882c0c840460401d48400ea90b005941040b9010b41e00b168548001d4001c0c88019100b9514000c00304002d0b500e545015000300b80312011611526100005408035080071566581c041034845882441e920111641c0b84852400c00d0b000e08101e42c455460003100b0103036000c840e8100c881501aa8004e10780543c5440d10944c001c004c001c000741c645018010019110055580050030f4421940c01030401c00d081144c8001c205440981152400b50420002480c1c3c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 884974586 1250 884973336 884973343
    0x1909050618030c060106021006051c140703080c100e0604050601030803071101020a1e05120402060702040e0303090708010c0e01050d150b0f040503011103130f06021204052d 76
    0x10204000034446804803010640b540c81014100003ca000d45400031440550100304403000310322140003030280da9294820000100d4040f8408824004450605400101e40008080400d481003050f215216031313a4940010350ba10228141d030154104686110001a19110700745045040600425151509a90b050380c2c40c80103000c0035010020110001ea012840b0325a00c1038291a03810003903403102181c0c800075041a04119115150046000e0700064262044003034030090440114070007002c0d1521b80138416594010f0300c085c0d030004d403034502007411040e0400c000c2d402000d02c0e4000f0300d000c80c0341c891482e003140c1f0600e4448041211b0290a031040e6a44401503420010702c0d0b65000568204900c1d0202c0050000d0f8800d1058880104040d10400b228801074811144240c009000c8001c030b5500d0b40140c0c1c03004560016003503c5450b20003012446234440c40441d60700c180303001480c06040820b0750b042480e0407107003200c0030740c003840c1000c4d002d649440c00c03845620107520554507031002c1c031001d5a44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 884975836 1250 884974586 884974591
    0x8060709032d0302150c1312050307170409050a02120f070309140d0e06040617040305040315050901140c0405151902010204050108070e030c0405070309170319090506 73
    0x4100380e01c1003204000c5030741c2e910004a401000103142400c2d07058603000c1d44170755840c400e80024140180004402c0c0400313404850400c2c009a2a00000f18104828040c0100b901c04e4152600e1000740708150000754002070001c030030480000026200c2c0d00c1c140c9244141c2e42c0040416007254018080006d40c0021050384507082011400d0481d500d6584000c101e0003800100c40203010000188140c0107501c10101300a81e1198442d52400950710341c0b032007440400e106502c203540000740ca10001c680c1d45160842c51a400034840d00c1c245140c560b0300c1d25810800c9284164a14dc40f41d174030b030f062000c600740074400d60343e0344e10450080c00c2c02c03454400d00c8030400b80214400c05000710810061021111004001c50749510151071040818201c8060024002e410034051a4040f440400119a0312409484071040b9544005c0050441703001c10f000740005003801520400a041e01c0340300903800100c0c034201030844100c444c2c400c65103900c1d0034802d038009124200c100301d9505151056501c0406e2000c6081507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 884977086 1250 884975836 884975843
    0x3190e0604030c020d050a12030b19030f15020a1d030a0c090b0301020d050a06090b01020a0f11060903100e0d03020906030408070f021c0b0612100509010f060605130806070903 77
    0x50300e071404e0003c1600c021401900402c24061250308004000c2c2154840e2203010280d60708028400240080c80042a5040303072000d100b43c0c1c031544c100000703064030a101403224454091584548100115401070f60001460b00012a0791001d11050030190448500e0081d40210000c0c00301c86250307102c000c10300c032050003600381494891480c110f541d1001d404840002c1c1d0428003c110b02d02e03005007098001d01071800b400c180982040e50022081d88000303075489100d40c01500440000842e559001501d9540006040d041030092081020f155000d000e80b1000000420002c5010101c0c916901e00b41403401041c8801d0510600240c045511840700b40c0f0740c400d5000e0400c03039a0300c80508041040680c8000f0003544145804040c1941140c4221242c6500d403244104c8601e03601e4007801c0000600c092a42410968005007030828420040d0704400e40103070341980002200d031550203140c1c0540d03410b50000c10101d0000a54400f0240102c82184010a8900c010b4441403c042c500100922900d12028 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 884978336 1250 884977086 884977097
    0x3110a05150c010c0519030b1912140a0308241206091501080a0201050f090a03080a03060b0333092a0405060909102301110607090506070501060f060503190e060403 72
    0x103600c1e912039009d266850380000d1800c0700025514440039040d041040d00889000c080450260003000b0000b604405680d41501c88403e50703906e00000f00d1a101202c250702013550710410301003401d0784610f034a80c5658607110002e0406850310380c040740c0ca4058800030710b01075520980c00410841001003415000294246001503980c200841041304e1400f42c0c01071240e0010f1000c1d0000704000000c0018010064251030500a655848241c01258002110000b058450034018080700c00203031003910107140c030081c80e036040c0c41c00400c01041c6600800c8450300d01c80c00810001150200404941c00c80c40280d079980d803864241040082441c50107100c0540b80580116008101e03090030424503a0b015020121071980d002d076020102d00701c0c0b001c130002c503103020941c4032140820710040418000d105100c944c4a0805580ca403105200203607004040941e0b4a558405000c544666402442002017483d55982a201c2c02c042e24201000740003100480c62851802e0821511800301080322a803058050805 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 884979586 1250 884978336 884978351
    0x5182e02210d1413050f010902011d0103021b160b030105180919080301030218060f09090f011503023d12230603010e060103110a05150c010c051903 65
    0x1141c0a81a042c0d5403200d5820f0800800c41034582d00300300c2030b1a65008a00b01c0704c1e960780c58017842e402c80e400d20101030700040d22040901034030000108400084501803400500d44003440c00e221440ca000d910f0104482d03001540b202e081c101054009801030807108501d280345500d418005041e41c03c1c0c0d03107a27180401e01540d000612a0b041400307030031409440100c2c132070031541240c80c0103d0941d00901040f8031851a00800c400078059258026104e10400b8181d400c85c2c903611420094101001043c0307081604c902804504445002e00421504c444030540b02c2e0340302c0c2c0c110300c10040c032105490911400c50907242d04440c0004486101581725003200a90300f40d070300860246c11a00080c0004194a5080c20407415224075400b010400a0f00c0301454001a0b01d40c60300820142610b61140450343c00394840e030014000b2680080501e91941030007402c2c148501d50b200301041d4a18504611010403040c0400d07030208242c0280500c1c8a031848620382742d0714020003542682441d0b02c00c0350502c0101a550501d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 884980836 1250 884979586 884979607
    0x609021c0903180611011401050303090d020f060c0a110102031306030c0c02040e060906070f0504061d150a12090b13050106031502070218010e010605182e0221 70
    0x32000c80c001c10f1411a0280c40d529220701415218081c5aa60095072030440c040401c0c603070320704640b070589100a0203545403040404c10003090074407a04081e6401031031070342c9242c190364407a402010f42d04000300241c000303090242010300150218038034081c1990401c000b40b4580340d0000c1201015203034541000100d4150144084450f9032900300025049494040c848003000000176406106d54600001c50380590340c2c2510445541c00d0346880c00c0c0c0420b405200c280103541c051161160403545100c240b0041c0d54880d40010203a80c00c00d610707044081d000107402c3c2540f41e44442d00e041a102c4c00e1000b80032000143d84c41c01d0704c400340101240040f150b40d403c410200b044c01e4100034000d580180b18600307001d0160b00750b10025800410128842d4245000c111240407090040904031403607840c2c50b0324030f60710340072050b01c8a030b01141d60405c004680c02000760299403000c014000c1c0100030381071600910382c005110042c28082c90b25280541d48004402d106020010b01840032408846107035584a80e8083c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 884982086 1250 884980836 884980847
    0xc0a050417150403031d0a0201020d12150b04080709060f030f02010c0b0907140103110909130503030405030307090b0325030e1c0201060e130816060203070c02040609021c0903 77
    0xb1481141100400c007444203256040e0011384034440801c0700700307041140201c0d019a4407201c281000b405a0000c14010400320301803070400002001ea41d201244c0180c080c800022040034940003080c2080004c1801d203c01581044460050041d9032000c01c030751402c00030024030801c0c440c400140318400003030003201164400c460040c001a40a00c550341705091407600035450312582d0055000250041c030700c8070075640c400e024121300c80100e044840c2c603100040e414091003200040c10f101c10704114201c94170000d681007006610a602503005103860b4100800d00800e5210300d680001400d603414002d205100000422040c0008203840f0800b0002801c000250b01a01048580010a0003000c0380120311615141d04070001100c95402000101e03119681120015001e86082e8000c000601d08540001c000800030140306641518004500301d070303a9904801d1707031300440b4036a000a2242500004600702401410041d00c48044d055044c014010381c400c045501c0701041080103520756040906042c09507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 884983336 1250 884982086 884982103
    0x100b160812100e06030a0218180a08030912040305030a03050a060807080f15010602120702011808010e0106090c170612030f1c09030c02011d1306030204050c0a050417 73
    0x84140d500a4035000500c0d004802c45407040151826400d00043c3c400d24010900c800a250b00420000f9100d084240380105c1c0000101110070881480140009a0000308130401d040e61148140a03507030700e0400c8041e130401c0207410001e400d0078002c0c042440090340110030365101050500d00040c8665440190350050440c0d60701010850041500c0800c0c0050b0124503d40c0410b010012035450280310555441c0c605401d01c2424016041141703101d070a410301e0750040070702a00514013410040c0c3d10940201807441150300406143e0742d140e84041c5154000e0088600402c42c40d14208041c444c540b4001d044074aa52510340c02800340f0782c0015a180d903ca145450f221041d050840361035406c42075121515500841124048a405011341c1c04901800d009241d900c0f0f0745541d0301d1203107203010b6006480d40e42004044d9803c0c00d4440b003644a091703d8840d09000c0718042003601041031032850040c44200c58015000400150301004003950702c6400c41c04850840d907401c081e00070b041140d05141401e00850 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 884984586 1250 884983336 884983357
    0x614040c030809150a020a05240105090406090b070801060f02061501030c02191b091109010c14010e100e1b10140d0203041203051302010509030f0304030614100b1608 73
    0x417510302c2e90b04c1e0780000c410045031300c82c00485009400381c62000c8003805000810800d1084041b00600282c02c08c00b48158020344621300101d03000c0360311350f260207040808035801000100c00000420085c2e43c010410b2031007481074000341c8581c0c208420760b000d031000c0d040019411b0580b034250030f0307042c0c4c2d1081002d0200300f620311150070035a640342d01c0c0c00b0110250801c02c01401c194602c1012800705800d10491504c020031002080c40d01200b4401075680e814190801c0e9507120184140010500d0b0078014803c580201d1005400312641c0300340090122200302d180c3c24030580c02034203980700d80f03e802036250003a60341c12114082503007080213046911525802c80c0c0f02c0d42950205000d22080040d0f0040d50245204446407400031503d1241181240d40c12524401540309100d1000099406000101001c110103400e6522a50300c0e02ca14519561065104a03400d55680b000343c0070b00c038401120305402c100540242c0c14041c0c80e2058100460241c07003281e0140e02c484d41000340410201604072161101d9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 884985836 1250 884984586 884984629
    0xc0102131d24090103080406030b0a080304060c1515030302251a0415050301030c060309020102060604150506040b03060f0a081c0e090720010506062703030c0a0614040c030809 77
    0x2124079006c0d16542141c4110000f080c1418803809061a14066010039140600000c0d405d05250450490740520100300580344c0780311014402d00c20400034007440c02c610051118040d002807461034000d1070800381241045074101498010344015844004200442d4030402038070788111070010380a43c47d44599405801d641d840c00c000900d0180d040000f4504807401041122403460350798005805543c030341e43e4020f0041e04140002109031400350700180032415400301a180445d20b4001259455000b80c1101c07280040c0401009054a003005041c1801d0400740c1d680140c00345000c00860b034400e440301c00c40264028089840d029203211701c02e03456841000801203a181c0c1460b9201505007801680f905904e942d15000d02c20248105009190041401508103450040b008070100812070880450440d03880e202a580d9002da81d0810140005600e01009003501075a83d107000401c4031403180d03400203101015030410021844060940c42140c0d04020080d0317440c120f510004000d00b1038003c07420304100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 884987086 1250 884985836 884985839
    0x17220512040815071716020c0307061d0d022209020a12032003040b0d060b0f1b06130602090f10090918020607060e030d020c0102131d240901 62
    0x300000d203d03100d04040408001198840560440d900c4101900900c411013142c030200309000401480e02100b0009481900c8044d1050340010f4107000080e4004000900e034040c0b91501192145540e000700303a822075503645001000e5010429081408100401c43c05051044d00c1024880360042c9210990041c03c408400c1d0301ca04a6100f032000303a40068000662403003440000d280d08622512030500074000440c00d052914a680c1c1c80c07070307000260300c0440d030b61907143c00551810402c028004890000041607110b03807040c500300100703048007411104a80d01003400c0c000b000709103c64040000e60450805690344481030701280c849140b0034241d50300114469113000c0b0065100c0c2c5a4425100e0f120000e02188025140c24200186030a0000e50321038010041c03840050f10341e03404a207000c80301070142d900b0030b00c0e1401100304903003105c04c40c2002d076500029182441c080e4140801d000c1d186d1090072410140722107140c00c0c4d1440000b420001c0c440143da003603000440b003101094003010801407039000d096 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 884988336 1250 884987086 884987099
    0x11240406020a2906130f05010e090f0a080f16020d030c0b0a0902060316030e030304062f22080d022d06070806060712030504031722051204 61
    0x124000c02060b90b095069a000700d280750718900032081e040e40000400030880e1130322410001c0000d0b41007800460150f80c0c51061301c4031402c90140714002c006d1404a501c607881d100c80501e05140c1b02d00035041030ba80102100314001400101074640899803042c80d0750f120311511000171520107008034065030000ca2000f06108040d0300240140745548103505e2a02c05440e03010804007540e0925100a44c448414030001d40d00300c4000171881d492070850728010407030f0040d0242d01415079000b03070740580b039031a01c800c4814032070901942d204c210018154204020100c0c0710442c404507025501116640350484049511150a5110340390b000c1c01d1820240c60f1881d01ba42d40282d500d90b100e4174040c4001840346c04c16041241010240340c2100b40100c05403030303590356080b021200a44018092130b400601400700300045a1512084038901d012074900040c581400d0901400d002d0040480503035a1264400300068a00c0704070b80d030610414243c0c2550030307580142c0f42c040d051420061030903d8a010105002400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 884989586 1250 884988336 884988343
    0x1a062502210a0c0e0907090e0325120e011d042c010b03030901020c06251208090d090b07050709050c030f0f0420130c020106050a0803071124040602 65
    0x4140c401e40300e500000d41e40300202209440c08440010040c0c0003080c08200e840201c0c0c00c203000000300c1c88c084d40d1414401d80c401c80701c2c0c00388030301400c000940c40325200700401c42001800301c040101418a01421001d03a40028102c8643c540035245514100b014000b50781c490341c11911641c152400440b014201014031200414407000c10480e2545c2410203100b07d605003c41201d01ca40010b0b400b5100780c00c4100281700c00c80c1c0c030102c100c40d0702c0d841d180c91401015046000400102e0700c65100901c4118903603030300406401d40a4910105c64004003841401140c1000490040340c010700701c3c042d20b484860078901d003002da40d6806000d80350300701000c115030442c422000354400c489001000c40d00352204600a01e00c030a088500500c40e080100586152000e11130749010200c40c002c02e0805100740b8001c000c1e0030fa45200b00341e0320150b034440c5001d1001c0d260940c0c1c0e041c0a454900019810b0a0f0651a500049240c04000c2c03400360740c100c55036404d614024100f070814441403480b00703699075681e200001e42c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 884990836 1250 884989586 884989603
    0x2010e01140a29010309020d0807050a02180907060807020c061308120a09030204180f060605121218030f0a081305090103050c040e030903101a06250221 67
    0x204910704901030350a0402d000704085800c600c0c0b02d4283c090115040194020b0580c12400da0340010910380000c0028000310040206602c500c001e003081108920500003103200f240c0c90760b5546030804081205111380010312508030350721071030128015241d00500342e0902e00081001e030b0300b10710001100d43c001d031000c181110803509981e080b602080074103a185115409015038680016518940030005440c060b04403101c0c040400c00000200e64040d9546180c00480c0c1d85d0843e01d0548a100c01c0009240410140300410301140c0541740240940c1d0b5028100d125844a946080b21b009071004455181080014074941080e803c0f0340182010382840c0c5d035030f81c20000a600000c400d145001c586400d045500c00d0489900000030008941c143c0c0c200809040e040e9800c0002e448240805481da540410542c204038000c07c00024949075552000c07218103511209080c02040c04000b401c2c400070401040c4c0c1289911000810042117040c80003601c10804a011008078200a40c010000007401040035030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 884992086 1250 884990836 884990851
    0x20d060308031b0f0412020f040f09020907140d091e0803090d23160b0c0904050112230a0f081c0b0a0902070c03080a0f1710030f0302010e0114 63
    0x100f9288500700e035000700e48200041040c0d2603005000070050741060207020f80c0114070040c081c03011a010540890129042c40c00700c0030710107803030344001020760901062041d04610140b174184a82c100071300510b00c0034407404c1184400345566080c40c400748040c040c0d1012031070121244030070f021034940c240300c1180d1b0000d544100d03032401102cbd64a10403500400c1c0d58504104845040103032503401107003a007a950014010403010041c02a40003000a507181d45840c403c4c04807014032511155420705200c100e9a05030000560001040c2d910400310790300b41050710328a00c88100400d50103044034840d9041a02d00000140385600003401c6a0420080348084c242481d90345525804e129031340032180040d54504000740390007840d104028072501207290018116140603901100786580c3c0c80c0e40e8a803140e0b000c0c83c0381c540005c8a00e031020300e00c103600005030001441070903241155424000100c458a54483c0320040040542c4484082007500030740100e201440b10000801c01015241e015400c582402c4070020f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 884993336 1250 884992086 884992111
    0x5160c06020c13270615080321040b0105040c091a0316020c0a09020f1608030a05010b0c0d051c0c030b0f010f170408090d0f0b0c0405030c13020d06030803 68
    0x5140d01c059510801e0f1960540c480001044481c0b0f00d24041800c0c40790001751182c81c0c840072180051843e10041c00000d040c80c0300155528402800390004a0302e2551070040402c51101c107110100c3c800c0300300d06041d5081110001a80000c0d010141c0d00c144095006a4a1881070010301c0c090904000182d44544850702941015080b4071130200c1e140d04421800c1c0c2c3e03002544031010710240c0c0c0ba80e8050540b0400d1000f056141408110410021100700c0c001110a003030f001041105003002c5009080c01024601509410280840e181549408040201900b000404285603400300b01c407006c084100d4040040c01c20010740381c4140200601900112180511030f05032074070392203503c10001028124859614911000e0408580d420b0441020340150707504a420f1055031640c2d5a1440942100c034404c021801c7e00c10005d00d08109913010041c40c244003a41c0500c000c0100b610003007a0141d000300220780309e42600340245400b8000b4000c01d100ca4000618100c001310400c1400d0300118040d00204081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 884994586 1250 884993336 884993359
    0x3030a0b0d1203060f1220010e060f07060c110a1e0f06090b07080c12100503060906150d0b040f02010c080d0b12030a140703111606030b01180605160c06020c 69
    0x181401c5911554000c07d4203842c116055400035512400d9400c45c0070500d080c0100440490019200d600f0448851201d044c0004000b0100041ca11a0231804500c5003411031302c1c0103609411580324506902c01409041c070080301460090001c01da140d9000754003906040c142040c40c14560002c10b0001c00854034000100c000c102544c1c0038011882c820303004078003640c0c94190a16411416079a0140c030b00622031015020104032503a007030007100e12444200008100c1031070101c02c00c5d4031b190102500701340100c0700e4800c4074020401c2070000c1d0f43d200b500906140103088440c0300480791220100c4014224020115003004c5100b5140c200c80c0e4143c00440301e6041029000d40ca05803644101e510b08004505050742e0390030b01d041e28001034000c2c540a070500c181c4815100f144070b400c2c1000400400c6421440c003a0a00101c0c0c3c0600c160322003007000b031a0040351510010400c050743c06040c0591701c14003070081281c03c0300041c10301c14140c981c0d42c440041208140d807520b000e95900100440c44e0301c0391004801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 884995836 1250 884994586 884994599
    0x307290d0507110c0f060f0c0708120909010b0a020a0803090c10120f0218041805010f1d0f060c0309070f080c0a0509040b0606090109082b0f0203030a0b0d1203060f 72
    0x203c405d07440e80010040e5140c0f42d01980704501c0c5a20501d080c01e06070186900005044c0404e000807911415064007050707071840c500c0100440c80da0705030007607045030405000030301e561540024440310256001e60322540d65140e1251040c941040c0f41c607410390102c0010790401a0952100304480500000700e0180245c070001126103080e0b000d92008002e244c0d82d6801240080c1c5031a4000190503150075050445800c5c1a456050075a60403904101030f40340c03540ca0361007011180080355a040c040410240c40b2241c4580e540075140c41e0041c001d08010b00c0c0110109000c00000c4c414080140090400070302c01c41c0d9580d1095880c2e514204540740702e000240fa0004190030421415441254003107c41f810700d6540a08008694020001540c1080160034021881b03250401c000752510100c0741003824000d124a144010404050001e5410071481c12501101160000141d9812400d00d0202207040501c1c0004900ca40020000181140b00b001c4210002c1a81580c400d030182c94809500c080c20584402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 884997086 1250 884995836 884995849
    0xf13081015150e1c0816020f09060904030c03050d061d0a090804091e09060207120509030c1c080f0318011406060d0609020f0c0c0307290d0507110c 65
    0x4241030215440e6241841d5038076240c1c84c100301500f15802410201481c584907600070340c00040c1ca211018200190040644c0307090725100000c5542119a05217078a0813601140700454054001000c5c0100040c035003081502400c113440d20009041010018030769507541103080f0303020003500c40c0407602900e40452000000c078041c4400300c82d000b0340c0c0145094502003004000346640b0700702e0084800f2000500304108118080d10820501a540141e02c685e10350920f0080c81e00f90148420a100040024003842d031804100700880302c004540700300002100030b04050b52419004401058644006100d500c0954403c010f5801049011001c501115103c946a800c075000581840e14140035040020750b18a05071006290380094443c01143ea80c0d07982030000180d030450008000340341c201240700015100e00700452202c1c107104400a202c160719002c410106403128800c03005400c501c541340000030584d41011240e100d00c0403041000399251001d4000c0c024070780c9414148441c002ca031000c0c4054501380 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 884998336 1250 884997086 884997119
    0x100617070f03150f021611040b03100b0301140a050714040f14040209090108030a12060e0106030203071b050a03080a0b010207060513080105010e10080d050f13081015 73
    0xa90110355894190b072501501d078800314039100c0102c0d85406139803052030014000b43ca02c0c284100a481d174281c08078038080211001c1d103103c85006034608001c00c00c055800003106204030103c40d01c0040d0a8644401180c0549a09046111118901e13824803000c5591039004512403a070036900e494841c00760010b42405407042c2d201d52150170401100a20190451100d00344c5078540051006281c0740c020700106280540991000c201e80c1c00c00f01d104060540c1180a00e107052009074410802c035070401c03143d0b42d10920180a05400c01d540400004d14150044a20301c04d088000d50362000b507403080c1c0c9003869407040070010072000600c960b8003245510031140114007180c1416005041110705014046841e5000036008503000e1544c042c000948080a2258602811540580d07421924200c21091f0400c030741a48090340c5a40700892952050358040282c07849500910712146d0307a10107074800310010005542000602c0c1c000d480c1d10b004c8400c00340e408480390b41d1105004400d00f41d510b00007080d8030001c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 884999586 1250 884998336 884998349
    0x1180c060207050d0f1716140105060a030b0f0402180c031611150405011104140301150f090b060426071403030a030905030d060f060212041406031810061707 69
    0x140f24000440d00c4851840c2191a11205407c0410301c80614058981c2d210003a00c02c4c092501c102c0390f42c15000c2c01401d910103000c3d1181481149199a8041c05040060004221512800215085685401009043c41e44146440000382801d241400c0e0603031081d14041802000401d409200500a40340423100020a40181601031003500181801e24001001102c1a5681c3c00c0540c0d80d403007100c0301034406004c400c46c0310424601d0800c1070508450038110b03102101030700007000300103103415a040402503034038600010404e1452000410201e0040e074005003001140d110141c0c0d402990110000440302e910001c039a03c40e0395030100b42c0f00c884a58503885400d5042004050a043e0290f003120380001d10076812645804080c548000c00c4480541011241c110301d40070422419504018081001a40c00d40003031400b490300c41160319100704040098001d02001c00001c1c01080c44583c20940384a25100380d0307011094502d03131b180090840740528034403448841c6244084440001d0000145e40310f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 885000836 1250 884999586 884999603
    0x3120501052205090c03160e010b03010e0c0f0906070f060f050601050f0a0509032b0809070909020d06090c051903080d240303021e0c0a031401180c060207050d 70
    0x201c0500c2d102400300200000d0592140415550fa00d45041100a072004490070115007418104600c040d040001a4440c80c110b410a10041c0031138455a800d03107030071024a440c1c1317554030800b02da0100554010811183d61004002c14100248113407507215044041c0705000810034801030704101c80446c1c1c015640280050303018450647d40c4881c05e002403040b4169814070904041c40440028540102c00c18203105600c80a4014a8000c0b0407104c40c2002c2105420a1101c83c82d24032032055a950680c0b003003000c80c1d91508103240c15903e1705003561005e250020000d01c0201101d0501e821403100034441d40c1e0107914044000401c4401c03070080d130000d5030707400881d00749402c03245892000070380050b1040d240010201031461620305503080c500350003588030350090000a0207440f031030580c031942c0d51542101500420b000140a60b181010384050342e6009080051012204890a00412006180c80d221440c002e4140c418402402e44003c2120169070803902c0d05901ca80522540c1c2040345402005100e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 885002086 1250 885000836 885000889
    0x120711012f0a020a02041e02030109020703480b0f0702120a0c0f1e05010b03010c030506093105070801061a040909021c1a010501020c10080c0906070312050105 70
    0x50590803001c4807001a11844440002803a00c2134109c1c0c5c001c5c0d202e14091503000802004168126440001085040402043c44001a103400c840c24544694008251000e08088070821410140c1264495041200d0f00d01c0c61401310424621000c080d01c3e194098840c2c00d1002d05582c44410845001c0907042d0f072420991000395441c4000300c5071061007141d00501101c8085080385462442ca40c40900400020402940b10010306007140c07208045d150416041c4070401032181c44014040307800420342e030700c100d904150402e4600780d1100c0300980621006050b00001c0b041c010005203e400b0f86039604001c01485a4840d40c1180100c880410b5080c80c035800d0204001d01521030388280101d81c0042d104910821104c0440d001d420004681240d41504024030074142c2100c074002580540802e000a244104a0a0000e01404042184c1c0340410812100040c01c4092000a03111002000303002c8540f03e241924000d4550041607000316a054a08800001c05140c421112110103914040b041549c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 885003336 1250 885002086 885002089
    0x304050109141509071d060d0b04030c030806091501110a051e0114010503061f03060c080a05100602120717030906071404030f0b13020901030b011409060303120711012f0a020a02 78
    0x103071000346515482390484590502080c00005000e12070b501c40d03581c0b072820142d40d03d03015040c41005000390b4090600c40d070820481c0062010160402502400c0c5910b0055481000310f140113000c0070018020301038130818090615001e6404c514194012009200b00c8030700f5005185840c00074841d0302d526910101c0424006600180760700300d40c2210708601041c5a40703a8a900e015181158403440005507a081000710b002040c5c440e4603040302130304541c86901e0f0f00d000002903071a040001101c050302d1000a4a00410800d100c040c50220044030b80141c5078036141e04225190391084603540e001c00c1c00301c40c455409c8030315102203800f5a6400a64005020381c82e8072401d8024030300804140350b015004450030056640c00e140310303000798441e103d016030941c18004050083d0009504940c080e007034140502640b580c010040d03890038a92000c151945598050701100c401e0700d80c002629a9510b494048502100503840d5030f62040c4008204481d42c9082c2d028182143c0b00d40021607005030002960080107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 885004586 1250 885003336 885003389
    0xf251425060f05040b041203031803231c0507090e0f070305190e0706110703030e0603070903021e18070f08060609120106050f040b0607030302030405010914150907 72
    0x2558003858290f00b02511810114540d078007680000005000c4507000d40c7c2096414043c16031101c0c9980d0403514000310560b8003130401e05d1014031071221503449400a060326210b00050350300d445a880c0c8148000380151600c1c600401080d80c9990024101203008540a82030a050901500345052081a10303500c0d141c085004140140081040031510003c2190143c0c1d1030003641004103580b005403040c02e181140c040c0400501c0400c00040d81c119450800101e600585850403468058400690725562181c08849079411901700039400307038200c1584044900d140441d03d01011040d1135070809078142c11800540200300700c6082c1c001030300c115540c1c01054401c0c0929a005800034200b42d00340440703800042c1088040c0c070140411a075490008220901d49800c0454218105807420850f00c000003001c0b41c0381d0700c901d51010382810340020200301044000d40c0030014550304944680540181d8946040d150528845805200140203000c10354200c400b003017800480302c07500c407680e4100c082004942d18 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 885005836 1250 885004586 885004607
    0xb06131406040f090f091406061f0c02012114040c0506070809010509182a0306242a060603060f07030c0207080601060509030f01020903030f25142506 66
    0x81d000d1b182c40005000a1121803880b0044200f14050007040c44c15000340081c400054000490120070300c110191065040030855a4098080c40c100900c4560707209002d84140c540d250002702c0301d02d800182c044581403071030b50a0203188502c0b80c2c490016501c008018484c001d684c1c024091200c10444852250b0003240100040000644041c1c14182046000e480700c10080b68500040c00842140d07401c010725000f4800c1c101107000c0d541d40c2c01c60814001140380005801c0c070f0408120722140d409141d40f5503c006460000c8110381250709140003016001c02c20035000d14201c015403081c100491807501d0080f511600c50040307189041002d0341c4449040303011341410800201035004503200460365440c2030002601a14072600c81550341e010030030515240c845520000041a481802408010340d0080704540031f001c00c40382441c5e00c0b1896081050340c90810400345401d02600c080054003081020303003044001c5141e0320241c9580c901501d81c0e400030140c082c02030604508a5142c1800207a00502c14880b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 885007086 1250 885005836 885005861
    0x70812031e04060209040633021507020a020909061504020307030b04020c0f060c070305030c0d02040510080610050f090603071103070b0415020403081603030b06131406040f09 77
    0x26441d903104128694580050750705582540c0c00080c404a03078106409004000c1401c5540c0402240410356180c142528100d25000c980769080030701c01c03100c4e1007001440e100c0c1040440721500344c14045d0020b9a100040d01080307008134444400101c840700080b072801d115020b07019036610906802001c000c0254001070941e4241555484425840d460350f1001c2e1551000c4140104151140b0074001803803ca8001c01400c11050200316013000a680038059039008400320805a44a904401114003c1d01440e00165008a492001e0405642d401102c0a001d4002612401d180307211a00c000c039000d2141c0200e07010544d108002c3c1d48000d007014402154080d43e185405842c144078080406c2c203651020b0030030745140c0340301d40510040c003810003415031030320b405401d04510703083c40d56845500a004003003440314211483c0f50b00e4401e05020342c00824040d0030041c00740d0b650b11b2450074104081d03821400380c028a0003000d0780a50980c240b08044405032602a050002518078001e10340018004940844 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 885008336 1250 885007086 885007111
    0x5040603061a030a15120c17010203060d03030507090b07081308030a0f050d150b070515100302210f01020a02070902040f0b030a0f0f020706050a541407081203 70
    0x784c3c02c9031480080203040c410901880307c00d01d004400707030364800c604180404691040061001e69514002440c0b807407075040c140402d40b6620355805442410990740124452500050a20700704000710004241103804428442c00e03103038a50004c241d036805400c10f1240401d410b0150200d15070301a50242c1002c0c0d01f07842e804034941035841003221300c01020f40d000907500e0344081400c0342000414400c814818101000d2801a850b080341082641c800e944070182c01030010301c9000c1003941000c3e030074480101c0100201e840100505c2c009900070b52080208070010f000e101d4020030740d030165008580480d684181d880f00042c1c1021160190340d0b1000d800c03040312942d5680c041004d04004d000c1c080492600c46001030316151079061460549000405407070701c140c98144034950340100080c84400c2e007648034907445200100460366440010700d10b03281c032900c1400d000001d542c80c0d102c03800960045118034041c05000c001540103582e60f000c6030150710496040500c08071025408a0040c542c444000c0307094 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 885009586 1250 885008336 885008339
    0x19060e130b030a0302160603020a090515070501050c3408091c0803060f041803030e030903011407090510091202010509040e0601060e15040302040b0102071505040603061a030a15 78
    0x2860f0400b00242240075030040303440310720614107828004004002c0d905042d4941b541080b0020000300e01401007910620a410740b031500e0b081800152614a5031040003000b171420884062041030b0403012440300651040e0515102c001c03082040c282110340220040703241c2032201d035101c44c41500554401c0750009607940320105400c0c494240000014010403556907241010810710140124185840d80654240340c0400318422071220b40d51021601441d001400300e10f440001801c40c4521058181c0c59030a0070030004845042c02c1d0b11303a020f000300e0f1700d85250305a07665052040c40d4125000711400300c0c402103810460589111501d8040510503d0101c1c179101c804400542100d20a40096149902030f40c01401215001541c212007071108451701802c0e42c00003010f03a0160f10541c040240595155a201c011503402042001d01810280e41001d20800701d00000a2942d0042d00c102e4000a060490025406000c8000040c901d640c000000389195558032150020300030110f4007010990782c03141c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 885010836 1250 885009586 885009589
    0xb04050f07060f08070305060d02040911061b07170304031b0906030b1501031a060d09060501170c0a12081c1e061703040e0405071a0919060e130b 64
    0x1c041c0540282e0b1507958821000c4103008046100c02400320301410310f000d083c8402e035613440300760250f880c0e412103000c00c021100303151050800c00c4c0d80000c15000100070443c130006c103024101c06004038403000300f03e40149595244007007408031010312005280e0400c0109101003180711b0400310043e0785451801d000140d4601ca480102c41090307100f52984c1e80f40c0c1081c000301c0c0785500d0348502c1e005000d01c0c00f8401e0640a04100006103162808184a4200014203914036500c030b4212000d941d070016020401ca607500c14480716800690140200d160080c0200c3d03038058a04080e00700c081d1030190000808400c10b80d61030a150f17501030f250300842e1081480f1405103c850718041c500c4400700300c0c203c28a0300302d0030213281c0d4141d42c560380090404101a100414032110000180c504035026528959000d0b107450030101d042041942003c0d1710000c000003460300302403510000305030301034040d14040704000c01200f6440e1f8041a40c040c0d400005c4403c0d82d4075906207016103420501600f803030f10008840701e040d170 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 885012086 1250 885010836 885010843
    0x18030f07060c030e3405030d0f0f05070b0408090102030c1024210c0f081e06090a0312022803060f0f1a0403120305061003180b04050f 59
    0x30310880d0400d88540500081603410300824031854141e200078444000e0840e8440401c01c0d0340104041030754404078000701c40341c1c910440d0800602c13019003643e0100b006035a00400f4009880c0454001c241d000154941403441202182c102d550880d044208907207565840321140c1c0d00011059046101c24001c00880307a406002c0801c240e1780c2100d0003e10050031316008501501c0c928149000004040d404100e84120031b02290061542c00495141c034500c50715010b050040d0705c3d00030303064035400740ca40403d41100000b007040035074103c031044801084100c2e8070303241c0c1d03240110303007510300d5800400700180007a00441880d55426181c0da000350030640d00c2e10404a048114503404022038094083e801d210301c1c0c05d0b20811005e80303040d501c0381d4a13950a000110b042030010780315a01c1182140c210740c5071240c4401c01501c024583c0300c50680d011685441c8020058641038410502c1a0703c81842541800c2c0a4446c03022042c030250001c201194140e158012144001401900d00d8012081015654142407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 885013336 1250 885012086 885012097
    0xd0609061a03010b060a080a0b06041502010605030c1e04380405071707050c1204091e06050319080c0f0604110d151a1507020108150918030f 62
    0x10801c48415070004101400e503640c0841c3c00d4052201044038a03070031030780700036800d03403000e182040880c0c401c3d507a40c007107291442180c0c06240343c1e812031128400019819000101196400c504982e000c1c0503000810045014038420304e9901c1c0ea031560f4985041c109074010035269082c0b030300d0a40000505000c2c0c6581540641c04804058000007540c0080c2c1c40c1c28814180c1012480c40c4c542142d0341004020500444081c2104040c4140803407400d07151070007003003001784e0040054480380d110340d88c4020a80103404814400305095000d0980c0c620441a11300c1100304590001f40100040f0000c8140e10070010300045059402603c10840008001c1c0100400d48814120200500c000e00e000d0800c40030942c54480d8951058209051502c00701d0090010b00b140307403034104400640404c00d00f0307040701405a1262500c0e0011307003110f0094841e040450241420074000c0c1c0350240c10341d6600e081c86081d091500b401a62200d403010204091141490006030107080243c00c903071919941180100d00f41c0c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 885014586 1250 885013336 885013361
    0xd0c0602030c070b0f07080f1306090e1f270e0a03120614040509010213080715090f14120604060902040609020a120e010b120607090b0412020d060906 66
    0x80c05641e402c600b080050f00604040b1411070400000c1620b006551054000260007100045141c0300042c82181c11901032001100c040c144d540e075100000f6090100c0e62140a0b01201c1060015207200e0389101e00ca0001c088016105940c2800e02015445401440c00d0303200da00008500004141c0090744130355481c0007540001010003000ca8500244581c5403503907201101414401e0030426001c40340038400f11150112000300301507890203130300c0b402402040d008041e0008080d00014000c0400704000d0159912401501c1d40c41070000ca0688664155120f01800a100c240c400c000b0704564900f410003140700145407108025180889614040c410f503020348030a0369848041046152522440c002014015815403d04406c0c010281c01a11301810004010362201348501c2e01081c29807015000e4180105096101c0d135210400c3d943d1450300f214040007064234042c000c98440071000a940c1118000091007511110a41c02e1104910340e10030226050f0b502c172505400012030134010031085920 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 885015836 1250 885014586 885014593
    0x1817010b040e19020904060b0301020711150a08130f08030a06180e0a14191a01060306030c170c120d14031506031b13090e0c0607060b0d0c0602 63
    0x180344104012100344401c030b0706160740300c900b1080a46002405042c8a00d404a9248542da551424040042d207980c001c1d20794036503c005248401c12106400301c03000d0b07105c00c0d14030742200688030078070000d140b04220084002c0788110000608403a40035a22210003407140007003d05268040d80c0c4c400c0d40360010782d2840d041507101c01c81480400700301088010140c0c000d2205006c0c1039442c98241d92605003088014102e28030a4118040ca140700300150b2444011700380304440c50003107034200601031080d141c0d01c0800e0b1106101c00000c0c0c01d032107070040c40290383d0403502d43c0391024a03100c95441c01c0c410840c2c07145882d00402d8902540d940d14410b90310030034012403002e000842107e5400406900f0400c613889202071043c400d0001312103c0d45281c10151800362009a80c03030722190100d03505101130a45110070090001000c03503980407010b0b1980304075111103106000a82000d0f074030a44603034854603100d070402c5060220704003145d201d0308501c40b81000078151103101c00d0303644c0303405444441c990010b002580c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 885017086 1250 885015836 885015851
    0x17090301060602151e061201091509062012040f0209010308030103050120030112050111040f0509090111300a05160c021509031002120103060501080c01080106181701 73
    0x30050040c05078410f241440c0705c12580f02150021985002c080c00c03190040000c56140d5186200951020440a03080241c2e25000404518490094402301500300c60050801c0c0a0300e902d075400e00300840c1d00901c2c0e80d40b95410444030071565025000020000c0e42c061081072041d00c0036890311440540a10b0050b1441941c03903045090090035514110407041d402e0801903140410380390300f14192415603012440041c28421903040c9a409840c400e10038051604002400007181644003001c08200c0fa800d48501d070150b07607081d4031075081740c00880384012564810403000703d9a0f114140c0381c82042582140b001d942495034031f004102c40c01d0403580d1201091380c030130900008110818001c1241d2003a03140040b0852500d9000c141c0708458074030160b15460020425054075034003444000f00c009003003002103440300744014400b90112001c1c40184c4400f880d00c00042344800c404100008011810384400d8101d074607000d000c45020741d10072040d0000c4880d410000c41c038001e031119054400c880f484004100103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 885018336 1250 885017086 885017113
    0x18150d090602041d1b09010210021315080705030a0b060421110a0602100510050d0615141807090b12091612121202040303020f0c06031317090301060602 67
    0x24103500240400c2a500b80c01c00c0600c209005400c2005045c0044460700d40c0d41900050349048480e0744071500701400030030f800b8030400803d28200d040314180d500540d03a4034804013081c0c0e402041580c8a800103001080066005c200c0f5400c003a5821002820040c038059482201145402c1c0d049215214104182c60000a200d11000103518212041f15004c05107450650042e40d1240c074060848905512000040c54011800034043c000301006440d06281c85c1491808030010541c80547c40300c02e1000314404a9040d101c0382ea01c1107040b0b0040d010803400c01c000c00d10950305280c014000e00130418215030110310445100041c211024100c58904400d042641e51399060270b0307c03801b0b42420805e403150204190b11080080c1d40c1c2d00c170341107100c030800d03c444464200c5020001195000764075000040002c00c1603800100c1a146c0c06079402590091645141080150312080d00c40c4036405603031440a2003c1074191200c3c4000c41c1c14820214500404580840d0075181c26600c02800368000082d0761001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 885019586 1250 885018336 885018359
    0xc0703140a031a04020406020a030e030a05010903050c06010e0c0306010c150216210804030c1716050c041505010e030c1923061602030321010501030b0618150d09060204 74
    0x840c3c1c0304660543c2880e003002d400030360314a080c60f00501000b0361040352000a8900344210b104071600304000344170036261814040c016a0142c8141c0b1810300c81da82c00002e0131000304007554051a0246e20300d5155490318001140c50981790903055600c0420500c010a941070b65100070700900b601c591400070a1100c90030b141c451119280b022501c18100356140b820700960240145502980c035040c00342864840341001c0301d100303141c400700f2419038400203401015040714810041c6118070580884048000d107000340300030b58040c20f01c4001d5040c0c03044414003a0758000d00404151060103000c0312505004080000e10a55441d00245064584031100f40501440c124107043e030148656201c001c0900c441010a01c503228181d0b40405500070805041c0440d5814401c0381d541c03401c0144410080c004c4a00e044180d00c00a200d6240460f28107400d078552401c00506a42c102400208010b51107a52801840032450000d10f004182410030001081c00d55018400d1b200e00c0740c000d0400603103850401510011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 885020836 1250 885019586 885019631
    0x19081603060e07081b070b10080a03020d050c19060b040b03060f06041119080105100905012001151401030c3b130506091e0c0703140a03 60
    0x8240c14008240012480c000701c0365000314841c1350004841d0f448001c1d4000d0100409010914000c0c0082c01c8024400498400b9004e010140b44040c40e003560f07081040c0d03452100c2c0070000c2c0580c021103034808081d40203001828101145000303690201c440d441013000c90395407540d021034040d6641e1030034034980e050900c0751252803e0b0a03001041d25040281000f0309003200142142e200c0ca44807001c6910305019082651070056020165014034020240090404d5000b4003419008a0900d0007e01d4903510500c02d0380c2c100c80041e10b900101090405c0540c0b0240e100180007000c540d200d814824144020541003c010b10950380304a0342c40c0ba29000040941e240ba0303080f0f000300a450045004040d0061000d070414051210b4602012002a810040383c0a1040c03c0c03654081c04515140d0f4003140c66800940c4503130401c491903440c80da110480340005d07180300e00c3d01191560154002490b400510300c001c0c032542c0d0003428551130701e409100102030b042e03015800d450300103030b101c41a18034107201d100728950 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 885022086 1250 885020836 885020881
    0x309040c091502150c07170403030c17030106050f0c01201305100e0f130e0102040614030c0a0c05101d0f0f0619110a0e0907031a090c1908 61
    0xa90b44d01c0444000100e020080c2401450340d100107000760130850030043ea0759003010304441164856959050242001d0079548007910300c00070480104040100f0b06086074141c0e815600c8960034200c00402da4489600071627850b80c0309650300c00c0ca18020008080c810f00d1407512081205680ba021010388110a00d03856005034064568000803004076500048181c00b050003e561440340101803c0014144d9912201c41c07840251404410041041041d002001a100d4540701c0c188548140458424548412106070381c41040500c030306521b40303104646000e0b08500841c1120b6680015404940c110f41e00200c0c0c00c4d581d6548400ca0321440c41061210b10901d20f030400c040c00c5005000640f10f038488400606000d10060100d4800541d4803842d0b000740e0080700c502c0603864959100400c054035100b03c0c809850710500c5034400180401c1c0c4240182d0308544200d03c0202800c2c0000c1d41271100410025013500c560100501c414100342c4250718003000c2600d100e81c2d81818605007035040c260b4005181c8440d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 885023336 1250 885022086 885022093
    0x130c0e0105010c02120115150e0612040f08360f0d1b030804090209180c0d052508070e03012a0e0d0317060f1e030309040c091502 57
    0x4108a0780c0020312503495a8043d10543c00030125200345d81e00400c102044d181001c1c5031000c020860030540e44001406203501e4858110359042442000035501816a0171154008108000f40c00120100440b07041c0d24403031600c0f5810301d604401e040c20100004001e25007403012042d420210219a0033301e0340c0c040c43e82620542c6c461842d881c04112804800071000e850484039200b90416584c08240b45001075400032415901c480e00c601d80040a9403020030b045200e040314050507010042034401080c0110383c0049814681902c924240001d040020518640002c880307680072072008100c240c80145c00a1503440e80014989040060080e12103985070501980c07425144c1030740400071010030110031444062450148561040455662503c0b83e6020f81111441c0d44840405812655061880c0c2500309681003d13030f2004240103401711109511a40700040c0c80c0e4441c283c81c0600010710b501c03580a800e49103409001800729060760585656040001d802c1e031004c01014002d4084000f5490062000d07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 885024586 1250 885023336 885023339
    0x1062703021309141002130b09010c0308100e09010c0306060305061c02152a030a14030601120e1b18010608100e0c0c1519150e130c0e01 60
    0x1c00c000c49441c03800c4070b400594078a0100c06004c882d9050701c040902c41012114101c96503c01d0b8000794011042180360013010650210781450600d0030380301100410781d255511965036440844401e1005130400c240c4e601804001300708110600d0806204a045c0070002c5451341819000404643c003035408002054600030034403516030780b686034000c03034083d00451400c0034907520b000007070b982c0b00304406071812240006458000400c0246014070700001703d243d5501c1d000140b0f80c25545a00c2844c0d140c10010b030034406202803030f0700b41e1005550411018034050315885140e0003128200d030004102c0c00f08561001c69040410750042c0c3c0351000b41c84d015207010001c050001d80240c41040b041c004d940030301c4505d90000c0d6185806418250040c04170100da2405424a03c00d0110b00780c1c8803558210241c050012004407180c422040c49010b0380c0c001c6a40310a078402c01d05032070003c1001d54841c0d85018040d240003d04081220651030107905103920b9001011481d103000803001445510032000b05012500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 885025836 1250 885024586 885024589
    0x51f06050d03031d070b0d0f0e01090c17030c06010905090a140102040f0f0e04030f050d060e10170c0f01050702041b110d12020304020f1c06051f090b030f060106270302 74
    0x80c0d50208084403404250165990002000b400809d890201a503181c1403501041c08015070300c3c4030442d01450300d003030084000c0c41585030700c81c421075104d0640c03a070145004010750003003688025444208001640c20010f101e540d950090005080341e0701c4969008a4240951200f000c203c900409240b6010b101842c41d09068503120b0310003e1000d000c5c800b0826841c0100c50080b03040f10007160205074104412502c9109110400c0010755040c00e083c5030f04503000c2070b80c0650700c40d06c58482045400500e00184640100700031b0400b1443d106040000c240200740050326039004e44c82d4040c8500321550750021100c100103100102c8102010171503070200c803544011a80008003150560803000d0f01580d256103a001041020746040c90107504a11114508101a0717130340150030790300b50721500d024001600c85203803400a41310128401006c68500082c00c00803183c0e40d0b80101d0205170090305880e100c0ca089031901d42800030036405000450444a203001075080402210713441901020303020141c20781140c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 885027086 1250 885025836 885025859
    0x130303090f3f050601060f030e0606120f0102040b1c1103040f03050906190807021612020409061503050f01051e060f030f010c0813051f06050d03031d07 67
    0x4160000d0421980721082c244030303074081d14190050302001c0d18035900b161821075515030003403143c540090283d50300954024031a0081201162041c801440f407910b030041088240c00b107201c56486584a0084803410010080c0003800c010885d1141d0f05032524111940301e041e81c0b00044080364043e02e0b10002816400581050303075009504409025210038117440c09995601c680b0f0403840d031090012950342d041e64043c00301409c20200c10b645801143d00d410301c050ba40c1e0312500c0d1032031074082e2a81105010401c420307102012241c0c001800862904010389500d02107602114440034542e1039914181b050250402150050905141c000c00c031a2030458034500c0114403245e46215054231078000304070181e85d000e8402c2d201c0c1070010141e03000c419010803103c0c002e018070045440410141800608903a450030f01c194003a0340c001c00074041c00e0042076034000d10355002c1031101c640c00780d403510085090b4680030100170582c2e20980f00011a0b01c01d000c80a80083d140440c840704542c00528144130b04000c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 885028336 1250 885027086 885027119
    0x1011060610020a170c1002041809020a060302090f090a090c0b0a0e0d081308030901180b0a050c0a060903021f020306010909020d29180f071b0206130303090f 69
    0x101901c2c1010780f42c02e200200e1882800030309180c912500c03104004034846d550042c0f0446403811146010701d0501048081907400390000071754000ca4605e420880140a500100351903080101280384160981b000181322040540302172080c41d980d189c4110400415070b10000140c005490301a0810803001801403024100300a1240a850380104200401000b4000c1e500381400c412154200151250a030f5a52600401c003c41c2c0000d401c02220325010a1104100e400c2e6002050a0751505c0484081954140d000410a201e58800c2442c182c0118140e44101d4510f42e11a5014000350385a1b8800c00401003504c0b00d030041424810010712806a0b0801c100c03c080350ba81c0c80000d42c94400300c808410042c4403c0c1003c82512110b0000b00940015019080350844812550b400440f03103500381d003007180542294040001c524110126030201d010710b401ca10001000c402041020600d039001c61606c1c1c1120800ca06111840d51060007019041000d01c80136140c0210214070151404e8500c8880c40101c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 885029586 1250 885028336 885028343
    0x8010e0c0117073b010305010f0b071704120b042003061302040e01020f04051203040e0a0911061204050d030c020307231603170301060c110406051011060610020a 71
    0x4003000c200c0510544c0302c540001e020003103d801d02100d264102d020203401d070300c02c0c80c0080d207000300100c1d1919080807408191481d1558250a243c05036031400741c60710340d0b2801e001c44a10700388000190a00144140103036640304000c840c0103400c0501e46203480343c1c003000d001d00e0281010f5180950301e031400110030b41d01021821100722152442e001040040400d81c122030183c1d400000c503958242c580030010805ca44058078030000001c4410b840030744034001c3d406480c00074a0704001292802513560041c1c00707901e0107203401e025002d56420020300350b035001d500f41194248104003040180002809214030240716414188545105075500a44070b1251840c0109550350081441c032106d100603461000b0010101d003180c441c1204552550750582a0748422900140da003070b000c01900400c8030603a4100c500c0e5860381039100907541d440c13000c00d03109011426002983d51900190a5950191420120700651034880c0f00741540394080d820800b0080449000340c0f8590310041e0305640c0001c0c001d011a40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 885030836 1250 885029586 885029597
    0xc0602031e0702090a1a040e0f07050301090305091005091806010e09070f120605040c18140a06030c120914010e010902030c04090f0803010303020706110f12180a08010e0c011707 78
    0x70141c0c10000701031b010070440d40d08a8505801c0203d4281c001984c6c616540200d01242c6500c2d81c0d0b14101401d860310100005c00140c3c0c28801340d40d250402c4a0003542400c240c1c28010705294440c030120344c43c400321a1449050030000d01c184152075030001d17015441881c00707840b02e400600d00350a0203016103079200080c50811080c410a00c5005132943e000c0009010002d02c02e03c0500d21111006101c004d8004005212007421040001d003140c1c20821490344200181890415900e40841540101a0820340e10103006c4c003005090a40d24451003401011032041035011a07845003130302c0040c21644a04500a210f030b140918600141e0b40c0040c000c10700c3c4400b100c01140c2002c161901d02c050b0381c18150018000c1c8400710000c810190080b82c0801036682940d903444851201c0c032a0540e50340154a200c9943da007001e2010500b91310460000d140200b12107c003000306101c04c0380800ca514859511101299560b003806552102040c810410411000d10b06a06e061344850707498002050060501020b001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 885032086 1250 885030836 885030851
    0x1060f02160614130b04060f0c0b060112020d0c0201090309090b0603190b090c031e0402090619050a0305100f02250f15090c0f1a160c0602031e0702090a 67
    0x40b850800c507801290310b102c118100313607681d0400f00d505821501451000c00c00c9007015950b05881038550490b0203800266500e0191900401540c44043c02c001d4a03a245408008a05281020303024000c049001640001510342c02401e00030079641044e080010450305244c075000040e960b40c0184d94105490300d4400c960034403004241b00003407000241c901d4201140c1000c000c48020618051842048907810003460000e120f080d00c20003480c104d4000758090405008511641030078610540454002101c1104a644840000d11142120751007255242d04c4006080d80007001c9000e080a00e201040c029828903000710489001e500150162031013300201c49428144501d543c0124411a001210380510f0480c800380310001e454a020192101c2080c030900080c07506101c07590504a030114100e80c02d2000f0980320603902c540c05044516443c203200100100400e20103110300000f001e46400540c1e950b104500000c1010286003c1d0b1800d05405002640141c1c540701a45680701940c4d8500082d800d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 885033336 1250 885032086 885032117
    0x1e0a05390301020c0604050601180b0d0803070306081c03060e061f030204091805011401030209070e01180807031703070c0210023c01021612170f01060f021606 70
    0x9000d8401013a00912810090000b40000401c4030b03410b9402c3e0b0851100300300558900003050714080c0d030f8441d40109515280070301141a5402035504582c1d580390118429540d41c007071a00d401c5e5009618602400b40601104402e41c061003088000d10784000e10040c64648480026250725181c02c1d00240b11401a40201c240752195045502410341c0010821034100700070560f1001160340382c400c407659868803083c94104501400803904a07030307000700006126903419108a03607280d12402d030035050007540510050205038500400014007401070081000300d00c1c0d03041100d8031000407901d50307005d030a0030020b00c031030140e0002c0c00d46009901a0358942d1810b01d403070400c03441c012024450500c040c0307520403020880c41400e00749040700380c0701909003001031250b641070328200e103d00b82d607800858114042d401c0014440401100c1341e10b40b90b0804d15920000c5206054080d035040700d03044a1900e105005000d40c40e04046000031300103a51000b843c000c074603140040000005e90041605000790700c0c110074a0b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 885034586 1250 885033336 885033341
    0x90d2303060a180207110301020c250f0e0a0510031106031008060420040204050109050409020a03020303030f16080103031d032406210307060c021e0a05390301 70
    0x80103ca1001e14140b4a00301011000703400a1401700d0f0b800e00f00382c03c0d8803401d18050081e100c040080c2c070040d1244080341d08120360384103049c150904401201e00d000191501d05041343c0001040b4450300600c0524000c07400b0303802c903440280301c044001c2102c2414008030b69690340c0745c0d138050002c0d03a1090362030311285240005541c02d0b60101545103d038808106c20000e27281c10300010340448001d80c0d41500b0207401080301740d00a40c05032a00045070580200018a4507070480701d41280094115480765440ea0046801c40c1d004858601002c0c0e0b070007081c01100c1400c060840d4084e5150310f424405541541e40007000e0324805182c10b40c54140c460b8442902d590107103c2000d089082035103a40f0310100d04001c0742c030002012168a0b01c21050074405d0110200081c0e000d4240d03012000c0554903b1b5400e540302d0703004140400005046115018080e019402614007071006c1001d254020301402010345005803420300851044514400e56070001400c4130204003854ac28201c0c0d91449442c007041d1040401d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 885035836 1250 885034586 885034589
    0x3030a050301511d1909050408120c07082d0c010e0705040b01020a030c0615090218040c0f1b02030a1b061b120c1a090d2303060a 57
    0x10402a140e11000c984a15005000c003201c00000d80042086401d90241c4d03060070401c01c111608400b0b9602c040480ca000c1004100701030404030300e2001036894040307510856000711740844003100d0025015012184110910340d100480320105458106c00e560f64102e1401000e13040d104016407103d08250080712881c8081c840503034890415282d908440f00d041c060907100303d10034100d02400d08003155a04060060100c07460042e0002c4c4207010996600706d6259840c20310031390380300e6038840300e501707030200d03000b44290042188800150b2100c03442400e40440c07040b9032060a2140d4a016010b284580d0410448901c4110900b40561603a000e001450303843c1480b01d4000354107008440412007000400c076503414a0308110350580d000c6541761141520b854106548480c3c1036400312a102d0000340411404012508240c0f0701000ca24180d591050b21260620014281041d0500700300010380c203003040030307100c01c900c5480d04240343d09008002c804081039000d03105040c2c03800000010b8450b191842c0356030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 885037086 1250 885035836 885035909
    0xc0d0e01020a030b01080f041415040309030c120b011e080115090501050307060504031209120606051017060402071103030711010212041805060111031606050603030a050301 76
    0x610444a0214002c1d481441c050003c640713040d0229540d9481030070380d20712651040c01d4030070464a0701d440d04190a00c034800300444030b204100d541051546000d000901aa03c82d0310f4032068142145050004030329582c2000b200703040f001010401042c6103180f8681160720300031001080502c1c1030703c00b100300c9025401800341e647c244516a250310101050841c104da654220401a69881c0c6d010140c41d080e03540314200010b9400d001c1030020030480c54081405c0f1080781846868180d480e8034403014a003070100c058440c0e40e0b071504e04000070f080800880000d0a428a004200e0088501d8070392100356010b440035000742c0d0b02088a06c200501d480000411120040441e910b178001464502c1c0d400c1d04004245005010301a0b14440ea00251000e882c15100f5800d26070007200c81140401c1c00411000780700307038100034420300300c0c101c22034043c40200050192802440d00c5102da9080c11070555002408050180d80f0400007190959400340650781500d01c0c00540c00c4003056845001800790fa400360885 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 885038336 1250 885037086 885037091
    0x1020106120803040c060509031005061801030b2a1c06030c170f0a0816151104091b0e011b021005040305010c1e11010e0303070e011706030c06030c0d 66
    0x2641030001600c00f451040c1e100341d0324648407680750042110035014000c0d10a4066100151030481c0d009660840356000b10050b00c0c1c1488914015101050420700380d005440c0c581d800300601ca00c9407900d50760300351a440441e05130300e0300c9592021081c1d01c40c4035001058000c000800050310300c180e0580c101a004580142000030465187d10f03080014500c801c1d102c000c18840c03070034420705000020522048450300907807501e08000c64a0840318503640c04400c110740001c0d000018040500051140c200400c03a2800d03078507185d07400c0480e44c0c070840780290300104405000820b61004aa84501c0480350700000303203485c99000050b02811801c1d8080c005000751320028040603910310640c050003800c04c0300e0080c0000c3c07291400050059a688480040d81100d411240b0440c400f1366018002100070190034000000e0300b0561501c4050454000b40c40c51800210480d0101c9107943e4070400d00390300d10607200c44540c0d85041442c00a80d8803e0120340450050801100050440d10f042080d1000015803003402e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 885039586 1250 885038336 885038369
    0x510030605040e070501110d140c0a02030109200a03050a03210e03070303050c0c060601030c18080c030705031b150c060a051012050c040e011803020d0f08220201020106 74
    0x80c2c035220140d80c0a01400204001c44501c010040001c010000c000c1e1070f00c41c0030000b450342c421202030358422402072400d80718030602d034bd0058a092250902a034010060070007204180d002c0d8032032140d40280c6881c440c85540d60300741b001c078902240038113007158141040241c0c8803c031108511303202c0340c030300d110840c0e90700d00a04030000d00004001032040a02c0b0380e40c00c0000b9980c90171644200e0080d8010300e042503000038005103480d4060f0b801201020300300d0500d080103078000440c4034504181600008410740000c1c488084030b060821020014000403030281c4080f42e0704030300c004058407c1c1c1c90010300c1080c941d070034106004400030481d0012101d05082d100189400c4040c0740c05080700381c4810071041038144000400225600c0702c0907806074000041c060000340d0f5000c03c0082c01c40c1c1e10140d0b18555840c00030f0440181d01c1074080c81024842d40141c5180081c080c800341160f1244444001804101010010030400041c1d10702244030050030541003000050004034010612504408403840e05c03140d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 885040836 1250 885039586 885039611
    0x1b01090e0a09051509300c03090301050604020c0a060c09051206150f060d0f150303170916062303090c04110c0628050a020702040e010506060301051003060504 70
    0xc08400540103404543c1020000d1000858900045a588074550031540c40c084c10070400401b81403c0040c144030f03000c4800c000000c40b1465600511810301035500000340c043c1142800e00429500c628110b40443c10240850819034550040c80d90050410341e840c1011224980907480980141c6805001c80c2c0d8200a44c416465540400340d0703010040254080d1000d0180c81d1151444030385c0c140251086040506400d250700241560b84059030310340762101020010021008031190040d03000b0360350b034120039800e503080c842c80761009040782d40f840d00607114500301e00c10100902c100325425881c01c2c4400603199410080611b00210017190b8090000060003456a0001003003074100c0070072201040303a03039000004a00e0500c2940c0703168030030381c10403400510303185140b0001408850183c6034004894210241810031900c084400079072280e03001c24008194101445138401e4030075151f008110300d090010014246010512409100b103c0b614085040c062003a080f890017440007a0050010448110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 885042086 1250 885040836 885040841
    0x40312020a05011a192d120b101a0405090712050702061005120c1c17071707030c1502040f0f0314160b090609130609110a021b01090e0a 60
    0x3034040d445500c00900e51179040100c0066031044030032146c050040282404120600c0b03060361110842c1d44414101e0014003900329902e02e2150314030070802c544a600c0c02910b5241e58144640054180f0780c00042d01d000f011042c3c0c8100d6041d50300c12503080c0c00c540d1302c0d0142100da4101004482007030500340001d1202180c0c0000e2114000c42201d030101421944900a1000140c6803460350b400a038440c01c0501043c2c20400e440000611501c1030322001c81881ea114591070104040e910b00341b11000140d52418420250460303a01ca40900d4583c61500c18291001403040460420103001c9114074038028a4901c2c00713a04440c000e145001c060110141d448540d071403443c2c824482a52700041203c5003840112000c21603d4400361007582c1000280d04000c01c5c40040d0300001c520baa081001081010303060390710103140e001c000380c1810700801c0311814404102c0a172407208241c01c14035401407003003620390b0b900410b43d02c4981c2d0200000220300c070500c400481d840c0416500c44518112940107010050800c0e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 885043336 1250 885042086 885042131
    0x2040f0f06060206060301090f02090417040f140409050a0221070306020c0f010902100c020604030803090a02030c0301291302070305032a1c1b052805040312020a0501 73
    0x50f001c1d42c009648140c2490700740c0e400c15070007c21412032082c402e4011f10f05000540d030814000d402809048032030000f001c2442d0f106030400d130049011b68070200440002004800070001c010b40e03050012005640e034080d6166108200203120325135950044c0004010420120b078440500c508480e0300030323075a0a042c002980208540b0070300340110070409510382014000d01c49100d030702030f01440075000c2d0304008513840c103010702d012648407904100000103e0140c00240d03005480f144003400083c600c0788109490101c17200b50440c040c1c3d0400000c1000080c5000c0c0103480c4004603150341c3d208130400b40020381940000d00395400c0c4240301098101c14036038044003445c40b0708c52105074404220054946040b01181600300e9204044c0104142c00001c03004006d040300c407114824004c03034500d0080d4601d00c03d180390880d036800003c1300441e543e0342941c0d403044451030a223074044040c0c04110715103500038810f2142d4000600070040855981520314400c01c00100c0c5981c00400800180223441d200d4000750b00a03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 885044586 1250 885043336 885043349
    0x4030b0109060335190210090b0a0b0103020906031512150106120216050c1e3006010905040b07021c1101060e1003050f07060903080702040f0f06 64
    0x5210011900d0001e920840d001c0d280c108804441d00300f80c0d11080080f0080040034101c092802c190b142c140301000d031028016036030000400040301e00c1a000b0091400c940b107004025094100801c07400412032416250341c12143c40400418110344a4006802a100321028140c02c071a0000421008501a4145190400e800c56400d002d10008004041c0c2d19815203443c0c5003080607200041003680d0103140045c1400d88954009400c00014030140c1111500304001aa00390b0021140f4544518001c400c106407061900038803140800501d02103901c1d19654145040c10185141410400d00800c4400d00c98002c58030007250050341e1101c020001902041d07a0441d254142032020410a500110307013011282c0b40c03c1b124400c07041a0310b000711031003803102c2c80018955680d880040743d0100000c030300d00c0c0700d442d011010822491551074120f242090444161103d500141d0b01401129402103241040700c1d00008540e4890340c1c01e00001f0b00501d540c1c0154009245459410100f1400300d4220340c080306c48 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 885045836 1250 885044586 885044603
    0x4020f0432100b0a2a060f0e0115080c131b12060b0a120522140c0a0f0b0a0302131d0106081509040c03021c06111215150d020403 57
    0x590749100e581c68000c401e6400d000c50f8801106490140b680342c1c4c040c010041c0784017204600340c0180ca41c0740459001780740c642d8600780c0b60600c2d1400c3c0d00b802d014007203403042001da40120031454400c03072540b10342c1c245172035a1044e0381d45044000341050940141511540d9041012031411510a000d8191490010300318081810240c0014a0200800c2510b100306216200d000749094900d036200c00520b0000e000c24200502d0050030b05c1c180c40c144039481da031244682c05001e041101c020300140b030110605550362040907456010300c04003040003089011549030312012504c40d0ba401e581603003e4016030b00e140d0b00103089854001201943c0d078090020194007210200b1070790741c8888089501000884042903c48000c0607040698207001042641c010b001d015100300054403540003031400100e1244020346420a56452000d005040c4a00603003040a203003040d01d050000d6074071800c5c0140017080c5004400c0d41c0c482400c0151240700e071820882880e803829039a540d91209140b0001d40081c0402d0b5400d06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 885047086 1250 885045836 885045839
    0x90e010605120c070303150b0901080c032701090203150a05180d111501060503040b071706090a090b0f01090f06050604030809060d0504060b010e030604020f043210 72
    0x50041003102c14040c180b14003184603035251040c02d0926480f02c001202015510001f0800c039180020b0000d000d44801d001c41035a85c0703034074400102198005002c491004c0d400b041400001e5403030701038080354020000b103040003820750811010b00421800c02c000e501802103000001801034240c0340c29200d12000a0200680d0321101c00c13161807164411190394056000d4880c1c55011405155403540040c1d003503003241e290f648059141c03000e01d80282c2c04180840c8002c0103000c200086d14010603445a6603240c040310240c2c01401e4140c03a0400075050302d024880450118881030015080000002d400800c2c80400742808511014055001d2060700009860018501040c150500503102100c0700140b0590400b0b0468452207040d6000c4d8510310b81c0300d4405c004200803041140a4248590b0140700009000d05402c03002400005400c2c4159200c2d4208030100401a50303002144030f52040c0541e40000c50781d50040c03c4008919140c280c01543c010164500b9018800b10080d051180f9200c05001c0b41d610b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 885048336 1250 885047086 885047099
    0x60b040c0302070506041106040801060906090e030a05070b0c0d1a091302280510050a120c2309120c1e06030a0f020403020a090f0c08101205120307090e01 68
    0x1e00031500004c100b0b40021000c20049122424042c0c1d1000004001c44d03d025600c2407480c2c21109258400790009444020401140000e48645204601d00901442c07400c8040ba01c010700754428100002c0004002c54041049060b40906489103034024240c00c10606015040d188480041c4d4113560348135114100001c0d2103032034030138020024680d010340030070941000b0b00b449209440b0700700700b0350300540303120540003ca59484408681241c445900d0b6542d1310340900500030103101c806110602058109101803140c2035124450542036480b4140b03145a16070318500d42130440c850350488607880b081d5080740b8102d155010845031a108811200081c1000000f011a4030b020f400d040c40980c007980074800541ca04640b60008a41101e40740401450281c0343c1c0d0000e100504560026420f10366541400c203444100c520a00c3c0080300c650501d0101c500c0c3c42466041120554000c000d5032003000028042000720420103d140d403040c0003982a01d07890105002046c428561007051300c080d0070380c070000445 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 885049586 1250 885048336 885048341
    0x3220f0212160909060f05250302120a0c02010e16050901140d1b05030a031d0301270201030f02041415091c0317010303080a15081b060412060b040c03 66
    0x1074a000b1408444a80c60404802d0041242e04400d03140c09444090740c084181492240741c0c416600c995100440e4481c444282c0f0700107a820a41909240c8104008000b0700d001c3d1081c20340c4000e41c0d03000840d4a50f41c15008034003600343c90350888443e1154045403040040f4030401c40054483c00d64480800b40c0c2c0c0da50f03400f091698503100650b046082240c07410041409a004032025540480b41c11020540d02c03002300c3d01e05442007000350000703080a1107031440300380000581c0c040341c071084001f8131a28220315a210135014015180a0283d800036640d8411039010781c21148041100480840d1600d988514154101c000540158425021050f00c0c41182100c1c0c41911800c5201800c5d04003000840600e981805030030302026420300c502d200d52007032807030351803041140a10b100759220010740c20034a2070701d01500c014404a910740380e0361030001d021807440080c0b41c0b0100c0503001c0c1e0000d40c580344540441d00314452a00300d015030101e030ac908901448940c1d00712980d0500b05071420022140959011000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 885050836 1250 885049586 885049603
    0x30615020111040e04051501090c0e0d030f0f12060909020a1203090b0304031b050c0907111002030c130806011d0c030a0e011d01060e0702070b0f03220f0212 69
    0x105500f0710052007041070710720300154000d120710f04980f0407603610940305905001c00d80c0300703003101e503180c00c1c50180440d030000f540c2107151409d030b4680314080c3d415503015010030710500000042003030026020909502c20bc100031036991405008106503070700d03a09640080c1545110036070040d00f8600780060a148084494445c69825944109a85e810001c0000c0643d00150091b81000810b0042c0a0980341c4076011014051042e00245905001c460502410700001440e8900f0301001d452002d0468034045020714150108105c01a629501d149119115020b90a021000b44022440200d4000800112281a140040922045901d540700e5040d82d00c0c03421607881c034648101b070000c0394072050540c11250301c11040318008651480304e80d0040a88401001555a950391180d00822800d01100420740d0800614400f60412509100c01d00c40d85115004201421081c0000020300c0500030441150381c00070752909446007136000e030078002810201150180d115a44008039000f001400181208 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 885052086 1250 885050836 885050861
    0x15080303070c0501060b0f0325020c0127171005060f040c27051c02090105011b0b0a1d0c10120b03070e0117010506011b1a01060306150201 61
    0x500d107645600c01281d03084a0110300b101c5640d01d40340085941c107031000103405014400000c01d901ca20302881040255240180240c9aa4009003070818031140d001c243e208800741e0071708118000c2400182c0700b400d140c031249140004103200340404180490012001161218a40112062840703104a202d044842c290341490b880207000000101906003034200100c15100c5040443c404070302244400040203e1900a0100c0ca5441009020303924010350711328070170105400080003030a641d5021640112060050030305201c05c2400c690089911021a91041603201000300c806050105060000d4194088100c0005101c6000d03401481c074005445110100002c108030180e540f00c28083d030b080d807e41e000081100b030300c4503219106900c0410084005107050300e80c48040d90314140000000000202c1840d00c00c3c0d041c103061000d582ea00898040d0520400700b01844204c1b4245041c0d0b1680d140440c0024060803e0000081c13127940551150040366116070803000c1c00740070110f040342202c1c1c7e06100e08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 885053336 1250 885052086 885052093
    0x2817100e01030b071209080a2c060c0f01090302060f15030d030507030906020f0c150408040e1e04030c03081303050d0908041d04020109170c010810090e030403061508 73
    0x40020601c03001070940c0008645c00d11040f10a100b00c00c0f030065401d40841611540000a080780702507901015058a824041c6440031640c50760350a01584c0f5042c3c0b8108a22840c1e02055110042000703019224001d1400741c001c0240c501b061030043e445207401c648100d026802c0b44000781180b83c2031241c00d5800c10b0010b000d4031800100303042c213900415020701b14204040c2c1c0c80c04a000018040d1004206036000030030210b4403101c4100c4442d103030660074280c50321404001414000041c42940544d0250340e5603003c0c00b5415035503066030000b040c4140c020740c580d2500314030911003803640283c0c10761101c0740665604506642c480b8150361214481120060006008016100c01c15490744c0c410814603100741e60f82880d0a0381c4801040100c00d013851030b09100307507050040c1f10456811521f118010721242002c4080e00c603c0340e8160380c8a0705680b035014103200000c0c00050920070030060304d002a04001030b0822071200904180c030340e25001400121074080c984044c05100303600e96007452040311244dc004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 885054586 1250 885053336 885053339
    0x2d0d08030f100506220501030204080d0c1b0e1005090603151504050103050d02010b031f09030c080c03070611030103120507050f011805012a052817100e01 68
    0x12240c40703420041802501c2d0080c1e120225840c3c2d02c0000401c07560340302141e210030b80d28002810040e0003400b60b010a041c14810002001620b2004c680c542a01281d801d1680c03004034107040c58122050004c03100c4c0d980c0011000c1c007286080c0c074204081d0290342c111011a400740e40791024001e0341002030307541940c982c3c03005020070300c0c0e0f08a00e620304d58000030000b0000b036155045400b0406a49017a04200c40981040030b51050f000e40c2481010302c0e04030300710020544583c9840c040c40d020318000008012403500c81c8507c0c8203250082270566001640603c1c100da80d9608031408903100c0d0803129046400a003002c000f0329000550005403410390341c20503455001c4107200031003940c3c5a0310600e81240c15024001d00000100c00c20b00c0380c860740b1800e200c245188290b80307142032400c4401102c0540d070400400c02c2c604a079400388440c102d0446185051141d40c9403d5140010107940703800c00c3c0c0985558180f0030384003d2a40c0b0190f00c1540c9481034046403040c5c1c94445402c3c00401483c001c007140c21104000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 885055836 1250 885054586 885054601
    0xf0603060d060b180f07050a21090203070b0a0909090804120f0605090106030b0106050a0906200f010903090b0304080901050d020403051e210711040204052d0d0803 72
    0x100c0d1100d03030740b0450b0002a4107000c203010031081180b041400c8007400c0c1e0107040002071010100c04540c01000c2d450542c0c6030210244014007240d030458680040761103034518407040c03500c90f9408251800d1b00202101d4403681d68580e150f00341e510101d215070005400350000502020b140c00f540c5071803644144014286404c2070710314103440c002c0340015074000d544082001c010501c284255402240c244001080043c11800d28941d41c02040e40001c08000c0c00b0410220030396071005400040c1c41e61407800c036101e403444c585403c80d4108411074128641c0600d00d0301102c22081540325800c40c3d4800c2e01c0341c0400d80e99651240314035020480c2d01030b01031030040281c4075840d817080000b803c4640c800c070b02c0181025140d40302c944c98411100005980390300d00c03041c0b1100ca900100010104c1820110301c581001c0100e140da00d40711f0190441c02800f000d0700c46890301840d6074540541d0040d10016100c0e503008042001c40003104850351910040d036800c00300f900809070801c0000c084150b43c1203205540386855022 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 885057086 1250 885055836 885055849
    0x140d0504141203041a0d0606050a020a0210020715110708010b240d1a03010f02040510050d0f0c02071503050c270a0602030a110c0102060f100b04230f060306 69
    0x80c00100740f030000700310202e050310307074200807410603060300310540d0725003445c000d150080303952541004050103021711180100360b900040383d411459060f540030005c0840440242e1401501da0000c0c0d03205803804203d6241c541d48504003000840d8040100c51056035981c001900326036000800c0c54025805042c00303c0e60b00d00956010b48a40b0350070b84a84d01e41408040c00004458101c1d407001c1c103001c4103d00c800d0684c6400d000301070f035003203d80a00b1441c05261200203003180740000801802d10401250401e02c100e402e070311501c60014a03c4040c41210600d283c0292a02341c10301504002c0b240e41050255003521a1085612409502d0641d6144c90038203890706110040132880600881800d891100241d00d82e103c00e100180650780080d515104001006000c004002060710410350000c070150b446a0303800242c1035000030018110a07030a0721068021501911180c2000034410000900050303807602c01c40d000c020072203d03910484460042c02c1c0803c445411035400c8242c0c00f00050000c112145403c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 885058336 1250 885057086 885057109
    0xc0414070203071b031a01080c0108150f01020316140f01150603020d2d2307030207020102150f07091401080a0c03180605090705010918020307110a140d050414 70
    0x1400d4500c803140c0d40b030303690902c2e8030003009006c010312090380010416107004100c00b0107805400d0a00302240e1a1040c0342c04402e1602c0240300b8469410403120611a9000b4802c50f2400d107040a50b500452460b0305049404030112540c0080302e1240714503500b64034506109c1c0c00600c03084110062000e03854213100718081e40103d02c0c08070800340d0701c18548461105200420fa030204012303801401c901d140c40901d4049410340034482c51412141c00d19444a4061904880d91100e41c50400585410503800100e1900d412800784140000b03102e0240060780384240c403110300c594502c0c3e8400119940340e005c04004c11207034103074070f501107801c160102e11042c1315030300003160851040ca0b0000c0c080728030141f82c000c1c101c1b00b4034050301c01d00d07543e0050000c0601c041c400003000d40703400c1c20050030740c0d80350880003d212580000c01c000c40f02c2d400320100315018480d1503203c021070382e4a4200d40080e0740d02d08050400d002048240d603000c0c8240042c54139454060704c2034600325000058000c0412401e41c00344000b108070b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 885059586 1250 885058336 885058373
    0xa0806010c0309090515030a030f02070512030f030c0c0615030105070521062701030210030b010c06090614090105090f07080706031e020c0a030e09010b0d150b0a020c041407020307 79
    0x20340441045031f85042110800e01402941ca4101d04850941c0103410008250040c0c0d0165600508444803c040001180d90380480070324050b40e80d83d00e08001d800c49024400d900e4085002c3c4a0502008444003480c0a0220b0380c124000c02190322049400d42d218800e0070003e18292540c08103000038400a051416801940601100c0f040030b206800308034500e05040000d9103402c51803005205608007141004802c0115003400c0122204400000c0e0a039001040000c01107134440c80041c0410019070000e550304c03169200e0502060400030981806060101e482044522600a100c1c0c440782000605004507190500a40342c41400d12500b1000f410500c1c104840c80b0a40c980744402e19902480100611075a480c06044420118034000301012030210000b40314501070001440b4481480f002c41b1286035445400041003049140040c0946d6000c1c0d006403550f040104000c3c1d60b082e004640c07c20b4028003103400b0402558440f01d103c12101e015580d1200690041c0001c0c4001000d0048500300c107080d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 885060836 1250 885059586 885059611
    0x60712050121244109100219031a0a0501112b020714060a0e1c1119081203131403040905070309120f090302090a020a0806010c03090905 60
    0xc05005600500c000c11000c04980b070341d40c03201503c0940100070f80c02c0e4803c0080f01d080b08040444d403144281c40031500c08000c1c541c544080400c120b09420842850900c16100080d920740400000000d0510f5514000002003810011403964900020000c000501d40040486034020700b4100110b400001c0c81c0141034881c0300c0c21140202c60400a100c1d20390014207850781307082d102d402000080c1440d806030301042c001d4031018100f0719180e9902d41600c82c0d03d01710349480b5a60320200070000d0340311081d0080d10551040c4c0d005128040c090380c982c012414502c2a03e00d050640030b00d0b40c40f104041000c0c42801201d4102e000109646c001176001541c00c01100b0070401c40f0302d001511554880070116518103200d0303000050030010850103001c1d407580424581400c01050045031505103900100c00a043e081184410461500b180240c1c8200042c580240c0044036a01d842202c4800940c010344d040d402080302c440c00a00950300c6541030029095041d0350310300016180440703000c05070001801d0f1059005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 885062086 1250 885060836 885060863
    0x1050c1005130f051011030106020a080304030519020a14030c0705060d060305061504292b0303090209130c0b09210d09051507150605030708060712050121 68
    0x45050300030f00394040c000c5001d0084242100d01702800c942c2141580c0c3d20104092004100c82e40e0003080d500405600010441d580e50f586150440b230302d1280581c09142e800c00c41c00480c01142d4002910801e840c889d0341681c03140d0109000050b035030301508401d00c8648e8000401800035007000e40180204403070794203010488039100d07540d003410041c0413030388a0080301e65125070341405c0c586400350412441020a465950000888011010107079414500c0d0048801990070705409481c0c00a00c45c3c9400f0280d1000102101454014090000100d00707030304c80c0d8400c1c40440c003002540101e1741101944014040b40040c40c200140308241c0002030200d90110b00e01c2c216150585240344040817006000d000350800c00b07002040a000c030310444e040940161200d092010183d06600101d903140d513086100b501420202400c0d031006000d031170708070355018001d4007400200045c000800314024900e036120302541005a01005c81111402d02c1889030201c0c82c550095809420300340b00403480382c010700c1c4440c1003c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 885063336 1250 885062086 885062093
    0x5011209020405070c211205070c060606020307020111070b0a1209050303101d010302090c07020a03020604080a0312110a0509060d060803301807171005010501050c100513 75
    0x70341c81240c2035008600340c00d80110401a01c031407446000e086e112514000c08a408a0050582444c3c158154049549a02186002e802580380c55655039200e01d0a00036561280d400948035001003100328085002880d901c0e541000110ba0340c01078411040480307050215280046881d181066402400b299880b440c0101160013072004610a00420017a810751a24114110f001042c8048403500110000001400140d547c003901a0b08130b485906a2903e03400140001204044a075200079482140050002482c107c007003120750485000780c8500141d2008850b0440c06d50325014100b0705007460030041000308600907005000681005820340342404201c00c100b10854078180c014050303940c80072482800e86170b594444103450070440c00d0250400341020310041c2042401a1180700c1141d00140302c04a4050100100d90060003211008500302030020001031325050b00a02d82320b40281860008100d0f035001d141140d9940400c034005003c0d0540c400400b0008241c05000000050344007007103000070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 885064586 1250 885063336 885063341
    0x904170c0d09050a0b07320a050105160c0503030105090c04152109080f1605030712021615080c0c0a21141c0209180f0718050112090204 60
    0x20700400d0319007000c15403c1904005041d51542c0c00105000c40070070030000081c1c521041c2c206412030406c0904d1904413201100c00c154804510841c80754030403040b180302444030541003117002c0c40340c4010840031000c43ca0030454810303580110141c000e038410401082076003080d4007040d501c503400700c910754142034468180080000c107242c0c0e007000143d5000c282c40000100711071883c50009000404001070016603690048034000c1c800c15100c9100080303500c403880c11039421030354040c079407050650b9918901c80c44c2280c10b44080314030140042c0708811481002d04410114082601c0a4152045110b102200c044400d040c00a00c100c03d6500c0074043c500e00d0503c01c00803508040c0c07140d50840d000c0c888642d0000420002c0350244010000382c540071482042040b01220101c1c1c0d0f0617468400d40003001620403001e0300c1000015900800394415250320003480e034440f140540d41203405141551200ea8046a44440a4810881001e00068101304a42c01100b00c010480c14407040454049000d0300001d04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 885065836 1250 885064586 885064603
    0xb100302100f08091b04270c14030303190b010e03240a0506010903170f130303030506120319020f030c06062b1709030105101806050904170c 62
    0x2142650009419050300008060740c08100c0304c00409800d4014404444071341c4480c084180560740e590007101201118101c1c80071040300305066006042c410f0302c0c10100c0364005109c2c003008030f0041446400c16213408401c507030180100e4100c820382c501105031140300805c0301c100760a05220524440c083d1588081c004940039400300c16824440464030b100c4642c03100002009881054070302410040c007603821103046816607410140101040b1545440540148558a50a144e0650200d81e41c6015201602800b0139207200382e40c14080c0707444000c240050510715181c01c00f40e03074109012003104001e0821001c185542039104403100c410260300c0780350843c1c0c4089404252904001d08204443c24040345c004030403c21a20301100000030912144520526490000c1403000012071030b040e02c4216400f40c074481e040c0103000b0000d40c01c0052001010500d98410345041200e40100083c3c3c0d103016203d80011604050840411a501d650313030182010780d6141001c030340b010705006258051004101014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 885067086 1250 885065836 885065869
    0x608030a03051302120d030e010b0d0305030405070b0c010b0a09021606020f0f0d0902030f06520e0409050303060d02010201110c01050f0105060712110c121e0f06040b100302 76
    0x103c6e0382480c43d0040603615010041e41c29030381001443d070041d07242c80e00c08240003901031030b01c15240d880c0c518001b414100550b0104802d290080384811038110b041d4021282c2c09d0080b1007004120396207805120030f901450301600c44003001071181c2004103049400509400c0890810980350000d020196401354101d080700001080d80d8080000442c00c003045641003000d420001461a4a400e00c2e90801f00301000c41481ca903e001c80b80c5441300c0c85183d850202c5c403401c40c0d610040f001c40001c0e0303400e40e01c1c842040034074001032007800c4100c15a0805206a06480d034200d0302643c43e41d510b503410f02840d03001d640700480c115960390b10000d031040d0100c406404001d290740004202800d1a80c86c820754480181c11441c031a810421200000942d070300b040c100c4400040c20aa081154885045400c1c050540c0e04560040741ca1003070f04180c29404101211150b2038000102c0910b209182865621210f045101805621900100d8049a243c0c4d1003154401a842c0e800c580454580d4040b817100c1c07a000c980c45 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 885068336 1250 885067086 885067093
    0x20d0c060b1e0f03011118150408030703080c030108070b07020f040e0a14010c0503180c090109020c010509030403030e1c060204060c020f100e12100510180608030a0305130212 77
    0x1003a545821030f0303648402c12044000344011a40113240305124407c0324403070a1880c0d0704008290060315940c402200c682c0110141940707440e5220b01203601c03603221a0742200003424500004140303001e0003056078183c815800003400b50a00304a2210b0b1258001d40c0c0c01e80e0700c42c06a20050070b1a940382c0c0a0441b0200202c00503140740c07282803609116540c5d03580c000b014264100640080c80c0b9a0110585c2e9010950a607405240306410400c035040000c11620290400590310002c105040309800a140880304403008003e40c2d500d030b0199075128000c0b800005c00113403a803031910034686042503800c1c5144c0c00b41c44498a89001c99682c980803a8040d6002e200030400d00f800c41c9055142c00038040c4003040040d2001c3e940c082e04400002c0451500c8000c4611440b480d081140d10300c90f007040320040341d400c0000200450f0a00742c0151f40001003034441da010000088040700000e41d09402040b00704c1d03a1140003942441241e80003030f0050180180080c60400902c0071010150780e03441d01c8460b40803806000b8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 885069586 1250 885068336 885068389
    0x309051521010506030a0c1e020105060a0501080103080a1103220f0501080613051302060705010e072c06040f15030b01170703111f0e03160501020d0c060b 68
    0xa1507400c91410030414540100402c655114001240d500020854001441c855903000580348807260303100300641d091000e1a119465901503000b1342c00b0b8401140c1c0068000da490300111070740b4409010090040105000d15103841d4020603108580042040031303a41400c08001d11b102c1c002c42201d1a61481c55001041001048821261000544020701e4098001d00d800c50120b0307142c55400c1e20704101c503a911800103030a103030803540d40186198001c100680d01e145504115019248030703951609240604000040c10350449d81001c40e86507903601007908031200c80c01d03030548000b0008021581142d203604c0ca4243e03054103840303010101c81e03820080c024900e0031410448080b200c1600b0041c06500844201130a04100080c0d000c102d0f588005140100140c00000c07a8800c80300b901104c1920000c1c1e1210b154075604100030300856401a005c490440d0007801440030300780354620507a409a0003110725002444d2280d01c24500c0140030b40c07804500c030008103000c64000c20b94400c039100840c00e4002c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 885070836 1250 885069586 885069607
    0x411180a0501050d050d0e01090b040801050f07030c080f061f1101060602211605060c0304050d020a0c17070e071110020301030308130606081911120c040903090515 72
    0x20309405060f055908440d000d0895584030390300c166078a8944140207c01080c440160b100b480898058031240028036211035403220014060441994407082c40410400040c400718824440d02034501b015540c0e80070030762210485a281900003401c995081440c004101c03203041c03141c0c0146450f00324196160582000400e0000342126500e4200100b15000708194242c41500240104140a00528032542e603038a41c924401e44408113000040c003a008010030000381800c141c0c003444c8998003d5040c4d52140910b0a0100e0319203241040040c12000000701c1403141d08400f00c1c05120b2081d021040301c10359601e810403000111170071140c2c500000c00e94003140f0091641840844d0842d0210101541154115a0007628000000b804501d8043c0c207840840148101500721400070003030001030b9446080844541012884007100c2070b0b808000e00d001e107070501e0904c401c400c007112000d14058019080f01d400bc10024107013081095040010400b00410035542c1d4484802c101000401d217250355100460 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 885071942 1106 885070836 885070841
    0x4330c020c0406121b030b0106140903010e0606030c0a0e0105010309020303040312051e0901080109020d1416030e03040b0403030e06070f230d0210050411180a 70
    0x140000d95150302040401e0450064200c0981c02281091105d000c45880c84020841181c10004000321840340c141040500c2068846500c0c22401c0800a825290404030003d02c1d5080b40d4188005403504004603010b50409883c8203003214a4564181210001441120b061640702c004480071550180100c0e80a164421a000b00e44d038001c02c0001e0407900041e449005410130320010314401c60514003902c03140c2c030050b900e414050382045508406504081c100d184090f03212003248128042d61200b441c41f031a111016100c00e455240702c0281a90003081e09000250010013091081030801006c40e02925014148034211075103083c04903045100302580680710600008850741003000b4003e0702d4071034110f0310740116420070480192903101c2e184004102c0140c1c2c4091f0103030540021035002a9841800b0740244004036080901064009280f12009402c5400d040100b0026000303e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 884892086 885071942 := by
  have h0 := BRFrame.cov_init 884892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 884892086 ≤ n) (h2 : n < 885071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
