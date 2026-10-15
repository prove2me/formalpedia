-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4689
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:25:14.315466+00:00
-- url     : https://prove2.me/submissions/e7fb71a6-6961-456c-8f73-25a7b83a6ddb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 843165467 ≤ n < 843345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 843166717 1250 843165467 843165481
    0x516120b040c030206030a0b01030e0312160306090f061409010b0405060a022d0601060302041a0702030307050703050c040f020405030c0f0a09110307080711120a0c06060b040801060815 81
    0xd806a002803003400080d03141a5240c0004401c0d40043d02c240641c05c0c4e03100590780b0b40351380600c6940c1c1010140005541451403a0698421845000b0300b10300681084190b9155454420b1f80f01601800b414401003010786c200c001c0c040002c051364000c2100602180c00c1c0b5007101c4c60981d500604848003070038010701d03003420a020b100480c0c02001c1c2007402d520611044d46080b04503020403c071618006881040020300c2d6103041c40c070700309060703002005041c4100410300c4024210b4405000f0305186850b19a5205201d10102e85580b16000014140703010340071011003002004179030040c00820455041c8400021140c05008900c02d62082d02d03032543c0b0810100d0100d0400d0020a032200400402196082c1d50b500780100555082d6070560a0341e01d400020005047d40111b200c54009540c1d2424400c217824442d809540e600690b0360095040001045880c0305034414218950745951010f414080f1030b40d81c0d0802c040c50f80243c00b6241180d420888081340c00480000c251808680d843c0c0008060b4070380030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 843167967 1250 843166717 843166733
    0x16050f1014040506040905040c051504031e0516061d181512010509013606020c0304090501030606091b110102070606060c0201030b15070627030507051612 68
    0x101c184114070244000129aa6644061700003011950f00c0802c080c5001c0c81c102501ca58183c2245129051000007515100c0f244c40981d419070798070400f00780c01160343d4030314561122109000241203204041441000441014000302110083e450b01c0000d80050408000000406030205400070410b11140d100311200b41d0107a9000484079400741e100f4090940822000c982c1d660041c0c0d0180e4590090200040c000d01c65800c0c1e203c80800c4184889464240800d81030041840480002c14950404000d2003d550704444401f811a130443c2d43c0c540d038450928018080901c8103a81043c904480050840441d0007040507440b00320040d1107031340e66040c8050301ca1040702d61240e14150b4ac24070042000400070310886019144980f55010b200f0700e6803000409a40c1043c1e5524010b54569580c40c000c500d480055841131980b16602040305041d084022042c401b450600c41e8006000112030014150403400030311070f082c0184141c5445401c0c408100180f500140300702d07110300c15940e0221000c0381c101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 843169217 1250 843167967 843167987
    0x140901090509752101030809010c0317100609050a0e070f03020903060c091c0c211a0106090b0307020601060c0213050a020c0d020c0916170916050f10 66
    0x15580c10002e02180f4200c3e56900704101c2104070781c0e00c2d0024010034014014209924040741c141e80f1440558156681c0c4007260045880150601000542080415010710101e424000d0291104021890040d413840d002d1000d0380b0600f40450809100031540e400d01c840300d94240c480d03100c80480b0a48a640e0304075020400c3c500c0704000c06a00b40300b110890341c0c00740b003918050045075445580320001501000080c05c415909803080e444030a03000e6001a00441d03451048621803070704003101e600000c0206045411040703000300f81081804e505070700ca52184401d00d050720100d956013105285c40da8a4200700b44826250403001d680042e0042007014850b0b560340403a01e1000d826002d0052401d91440300b1385000341c0d5a415084d8010600d0100c40404101c0d03c1d080b005684001c000026420020480c401400b80100002c007454a003a0740c99036000780d2800000201b132150b04281440e18980c000d8072101c1184042c0c03019107407005c0006a0345040c69038400e000100a0518070f0180024806803100911 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 843170467 1250 843169217 843169381
    0x7230306090601170702030a140c0607032705030705190f0206090a03061b180617060a05030d052205010827010e010e070b0a140901090509 61
    0x40340c060b903685104040700701307406001d01d0340040d9220700749081e000d07044410050003070207130710400d004c2c0103a404400521a90402d04a0400240c2c40c5c4219000500b142100d1200b01080c003680103c01c0c00b000400001810290701a0003034034080d851940b1103003a04005482701038002402e00c1e25510240c07600703d005040d001c00080c1050341203a5243e50342019141d40310310001300000c49064001e210380d0480031250303880d842c10849045c0d460501d6009401200900030007501c03844120002a80c0c0e480349070740e80c0007900c0c004080b0340940180240c010030341c1c0d00109401811001860401c0c03c000b0100da0108103030352050312691140d50b03c010b40741c0b141e500d400c0c010710950452180070b420a80000c0c428003222048900000c10092401410710f858091694000c100d029000c100220603558040b00c9041c0800d40403005603500c441d81c00048841c5202c640059900068007000c0c0491410814501c0c40340a0b80010035550104a00c0507810f121841c090200380f851100c660312000d11a4088569041c0e020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 843171717 1250 843170467 843170477
    0x102708030a050c011b18090e100f230a0f02190c0204061a07140601061e0311030f060907020604213513020f01050c101407230306090601 60
    0x4000c403c805880701c0d2030b80c6a17000c2900444c90f545540351350182c2070081c20b20f1400a018106054044995a00c0b44018a103580c9903075402c0e0843c11a6550010403640448189180403205071031030500e01c074801a2011060a0310f86128030706014018020b6400f460242c9290701c07010b01f0091400e8620115a600c126840395651401107403014110400c3c19107170541804084c0c6650580c41c02140c4501c810701401800c0e881200100312240d440902040401d9452102c200410170014003680540b00907003081c10205e40101c10480344c810b5402034240f055004540d40c1c401a1074102040c1e0b21894141c9000c2d0014040c0c54403811000b95614540e10f5070300c4d4034076001a24032603c42e54004226450a950818a9071001608460021104076650091607490040303c4800036035001038190181c0c1d40109040c4000441e25044c4c0301014010141e17016905c6a050100d401c1c1e40282c2264860111032100c007080b20400d40200f01140e01102c4c0040c801600000f82c07850b00c42000300403441500600582c1044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 843172967 1250 843171717 843171731
    0x60d0f0501080d110f0712081c0c03060b07020109061404050a0b07020a05030d0e09191a1302040b09152803050601170a05090c102708030a050c01 64
    0x156091050600a0451001030200f12001e114020305001800c021241264000040044901004039220f41107402c42c1044400b111002d00c0d00001c14014030401c4804c0c060120020400000c090308011060743e000d507020007181ea182c05041c00d16001d8058041e0004601207024020a4082c0480004280700e5555960503e6038580000f000394103607070001c5c0341403800840c0d144210304040b2205d50241c14100d014101720303e44c103900208440c004408140c854914200851242581015000c81100c20b01d41c00317002c040c0c0c0c10800b1481010b1201c8005e130094070600d021501004940c400d607416a41c22003040782ca040800c108010740180e410400f40001c0c901003000c1d03603001440b000c1c004021600308032500000354440f080507007141c5004000354140171a00a0a141410110400a84c841a1900d001030b45403102c207142407078120069249030308034200d4146000016042802d800040c81c2c1100030f03907030050300040c4034840c928003132049682551090003d03d0381c4600031300141a901a11800000d604 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 843174217 1250 843172967 843172991
    0xe0103050403021e070306050c03091b061308030912031e0c0106121505060609100513032a1202031903050919030605060108090601150c080705150106090308030105060d 74
    0x403080148044c1e540d032100d041002041824000c01c1d6114852960b96030862904110301c1e900c0e0b441c0744003815011035044403582201e940d40c201342c405101c0c054014051b0740d600d840e2407941d60b82c010345180f0b114810a1042025191000040780c903447c0400c41d1490048001404d0941e49401002c00d00205548031000170500d151003217a074139003080c047c400c1c440c51100210001401c468024000f180a69810440e0900075203511410922035100c40ca011561013101134070494661400e03400041111140322400980c035080021040801c018002002c4c0c10700365181d0b4410907070f11003500001c2d050f401000b03490380c80d640c606003c02c1206010342800c270310f0400601300144522208030b0b922070044036415028410700c0f200b8860560b0040d000e0034103d4075420310b541c02d039565030030504c02c0d1108010080c9810340030038404c041901e1001d42c058141030704c80c41286089502e40408145400000c900c64000045a9205900040460b90481c03602071941e424101408541c2d40501000d01301243c80701031050072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 843175467 1250 843174217 843174253
    0xf0504211e03060501140310140f1005090427080c15090d0f0813113c03060c0d0506150a0c020f06090f0405060d020306150f0904030e010305040302 65
    0x2949a4542e00041c4290500001402c64820301d0300300c0b07441c208103008100002518546c08004d40e0480c01889411600510008881d542054503094000900d0390713070105001e03000000780c920403500303c8052000d100c1e1211082c1c4454642e02250a05040080d00300d0701255070540100601c0d0210016915640c8055081e4225180251410407080d440f09186135805544198844450645031504c81c195080040070745081c10150103000d4581c140f0103031101c055503100c98170340c5141d0a0799621a8411240044298905c0014203031145040480c981e42c46094500071036298490600e0003070306410521110f020307000034200101541d400c2041075080001243e0510007030240b0644980c2c400070008071a206101892100b845018051103060081c0001c0f81d480f401000100036013904d00091a9643d030300091640203510101075014000c031001c1c4101c0c480045c03440c1141c0300707051b16800c07a401440014080c448200722009800543c2071031500c4000c2d0302c030b41c1050750814013910441d540d107820101d48840c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 843176717 1250 843175467 843175517
    0x1e0216050f060601183204180507050a03021513050604150f020705060d0f18050601060305090a0b0601230408010606080901061202060f040b0d02030a0f050421 70
    0x101e680d22681c00c0200641e4898582c070b26803c00b44110150040c40c2c0080d041c00061044504030384000c8200403424403454046040d0244900100240704890f4520380c0f8480750001041c00355402c1c000d007000401d07103060000a400c101d90380603014138201d80041208660baa044041840f401d0301070a0000103082d516100588080c10b402040703c5403c4000e03600140c00030115000d08401d641003020b0400035a61a2000d440c800b0184100101d20389002d50322520080400110500c104004014520305210300002c205050341c0440c6c804001039143d8014065441544250060040c14140e00151255104080079403604020521111114448040c4980b0710b400580186909030f54070303441000080d50200c0d0064005030200005c2082500f001d02c04100e4006e0361802a0090400058244481001d50102c0b030080444411140c0c071a110701d480c50010350310540b4082e1f21941480b41081d071149151040d203000360b41c0407000817180640050042400321240110300140070b07104010140300304606901c08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 843177967 1250 843176717 843176743
    0x80c120f0114090c042f0f0f071406041e021f0e180112110303131e05042f0d14010501020706080c030601181205060105040506041e021605 61
    0x744843c42c00a0005140012483c0b803e40300b1803c001a00303044100007044400d0320000d2120079001c0100304004404c4611611030700e14102c05001075401180010240607101152043d2500740d03550341076001e229a90b803819940a40100300907402882000008940d07007103036600c00381241922210802c10300b51195030080c0c4c0700e80440e0407420150a00c0c0f4000c581c1804403444c200a0360103075410444c0712003000c43d00c100010b00f604d0325588880101e9400300300f076a1884017a0b034824040c458a400e400d2001c80c0140796119104440c01001255a02d014010300310359171101d8410100c2800340c4045048541d4880881100e4070f00100b040d40c20303981d081e0085080d21414582c8010306035141c4000249000401d900c2135040045080910460382403100032a90800000d180c5070110001f040c3d0344406254042d802030502c3e90b680340300c901c100500807400904a4800301c5040110b0b03030fa80e8040c081038030320b4042c00c1e035134061402e0806030319010b03180d02800b45070340403002019050720142d80b81e501e019180e5a0903 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 843179217 1250 843177967 843178001
    0xe0414070315050418060510080a0c031e05030d0504020f120a120e06030106030e150f09070515220509250504030f0809040e010507050c0c0307080c120f01 68
    0x1078190003014038070b490007000c055608020f84480040101e00c941c01c11a0020b02d05a164000308224620f18500311020701220703401c6d0303040d600081ca040c0e03960030300b03904c012100803881204003550101c0d8103071a00107c9401c90051031503c1000b00d40c4000500000700704036030054a24081d0441500c43d0f6810000e00d9944038010002071580b03080c20002c4400400c0340c4e00c10404032140c80011340e204e03601a01c0c11102941404501d40054601d4181092001ca2004402d84446030400000d400c2e00c0c046180544800e8003602e01454580d018807100b882c0300d101c0c101030510300b0001000790038080800c41140300101041d03442880d072100e0000f40200d8090710105051040141c49105100707050745900044807250401910b003e01e1565802601c401211005d032020b600407819080303079211074010710708440034800204014504407130050b00c20380180480744201d00c09d50080c1c3d11181000144da80075a0940001800f8031300c3d10728108680c1d08080311807034140740030342c9081d0b5100101c00d0007111a800444065 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 843180467 1250 843179217 843179231
    0x601081203360313090207030e0904050c041b031503030503011809050109060902090a0b090a0203040609020d0b090f0f0c0904051213170d170c040f12030908030a020705010e04140703 80
    0x410344d00303c1d03140c0e041640e07010710402c803000010342c000e00400e80e00e401c20780f840c02032540e841c140107050418202e1203a8000d807d107000c1c14403e040301450754003204d410f2b841c10041d06000007140c2a0100309808001c0206e0340c00c00c010300c040c410351580f001030f0000502c0017082c9088155207690a403940120200d464036155807a50003145440f00700c182e802180a4010080c10030010300103205410007900585d19140e0000100c5c0030b02020383c0012541a402500b2450034482d289040c040c0c4400c100c604070354900a001250b2000c52001c205003000b031041c41e001788061100c68082000026018100b16054800c15280e4007a00709a640a00b03030410484490022003403915035066541c0c9406a241082900520794801103c1d0f0004075034100b14201c01e64518295a8100440c0316501c01c0303420000c06012130301000104c484828140c003080c00d22a9446021442c0e650390445d69030300448100300003580000d00c0c14007c5505c41c03001d500c083c4400400200d483d02d0b0201203440d02500607225000000c1e10340c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 843181717 1250 843180467 843180487
    0xc07210c06180b030705090415051302090a09151e14060c100b120717011109030a03080901060e0a0b0301110f040603050a200a0206010812033603 64
    0x2500c00e00524450400b1110141000b03404482105180a5a40c8140000c404201e0b1144580180c2ea00a080640304100314102d400c2d044056181a00c40c15114080030721040303280090a0003078600d480d0014041c007008506000c2c00b035018101c600d080c1882240c04940000342c0842040c01c110070301d042c9500054200d403c1201c03101c0c117001000800f40c0691002c210012644a00150085064601440000e4a1000c2000088100101e40d105c0e10f000e2003589408038258041090850310b00103401d0080004444203100b941d418050046045d5060704800310350804240944941c540c400408000021000d40b10200e02c104883c0940d003600c030155031340e5801b441c2030900740700d100100306400100c107062802014042c0814459409060201512500801c004809540042e40c80c5035810354204031032000a0b41070000764028006180051082030000201c2d0100030a294074616820001140b461360790450081407000d001a044d01c07910700d07120300d0b4842181400b0b0140041c2d99030402841d6100d01d141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 843182967 1250 843181717 843181733
    0x120e06040303091404091b0e0f060307120501241701050907060f110d0e01081b03131b06080709090212060d050709020d0b0a06020303070c0201050c0721 67
    0x40001801860100000d00219070080940707021a0203004813202401ca00c0c0011801030209001c00500d0b10b080f03c9980b074201d132003040c0e491082d16a0301030442d070b240d40e8240c401e08440b0401d84006070180c10201003807080f60105045d6840ca1409800081079a187e0f014210729540044805c0f030b94003000d608818484500b448003801840ca00307180007403040381001080140c0f07441e858410349080c011103e40d01101e060217003540310ba18001741801e0342c54144901d2001392030003d20000381c1d40050000740000e22040900c82c4244025091401410b0031503a400e451007052080361a402d89070302c803070042c4204500484040000180c0560f40d40c1d19854204164054040601900440d00d040c0c0140011410b2590b01a6040e0b8440c00850f40313015901214246141001ca480d007180d4090390000409800b0144150080302e043e41003070b15244040c130361380d820483e220f000540303030300c80003405a02a10300590311500c00744c2850790019094488603a07440005075444810702c0707440f046000d401401c1c101401040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 843184217 1250 843182967 843182987
    0x80d0c0f08071706030a020d061b0f0e0409030c0203030307030b1002011812030e031204110108130f02060f22050102070609060809120a020c03010506041a270412 71
    0x2800c0c105620b0511400103802c200c1c103500c880c001e80c0300b03001c0040c11641c2c0422401e40d4294000e04040090402c50a0100c09007602c0e036030410016907240c0344c550b00c0922035001280018031994510191020b404d04000140c5a80c070300070f0b801c208140c801100035903030920046009401c282c400240340c01801c810b000d00c09000501440559151505240305e50b9220000b40e41c4440d0300548100c9c682001c0c080a400030404004070602c1c3e0720012410b05900c08015502500840c05010031300b03400740c4044011034010f60704464030080a02030303854010004162240112403184002c2c038413410188481203c8100340c00141c0101e00c1000c2480034140302d0b5400303c40c00c90161000f88064101c203401c00c48050b181c075102e44950320420050300002120000d0500030000c0701340c3c65030002a41e90100000003552865280000386c40b951030700022403090710b00b82c8114201e608a010070300011002d02010032004a42c00841c401c002030a44104a0181d03e01040c0d56200314400c0c52014010a10001c0040c109505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 843185467 1250 843184217 843184247
    0xa020906091c051b101101110403030903140615040207210c06051e060d0503070c0311191401030b0a0f0605031f030206070605040f020927071d0c0403080d0c 69
    0x40482907400c1130b141c0420b094803442c82401c0c444406c040450b00c0703d0050000841d04052000041408010158070100007421070b80103024110400340c500505c80d0300d070b50b81914103403600c5804003c2c0000c54141340d0040c02a00340a4580301c0000300000311800303a0b82c55410400d030001030f43c00d24030004200c428031480703420007602402c0407140c3c1d1520701800c0000e68041c052622408039035001804000b0104115202d41d80c1c040d100d441d00c166130385418a2104d28060403180308041440220317081640d0b6541001c00c035030700038079600c81115410006400800544c4042034001c09811300220702040c2141c44600100307559030b20740c2d0342c030b20706240344600459a02201c1031144d030a0010070000342e95408155002980c01402c0041d00d62294a08200c0300600320034000e4006444030104080030141d41040807103550400024003010f48903914468650025000d03a5003852260101102400c088003000350f4441c403008000c030301d02516134984041c217810401c0d80d499059205c040407520140e100451010f0b040c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 843186717 1250 843185467 843185503
    0x31b13080d0917032b0e07030614070f110f1f11161b030605070206091e0304030b2a0903010605040c1d152a030903060a020906091c05 59
    0x2c1c5034040c1612131050340b0701040e10004000005d1490b005201c1c005401d030012a0042140403924581140c854034280700a4030918580800d420b0a01100305c081442843c06039281c0a03158900c090948009052000c02e50240c450321079618034442d010031106851003002d0a013410200401d01120090324540c40d030a00031021b05202c02820940009602080351380c1c400b0f01c0c41c50020329980c40440e0302190340e00c05011541418144001e0a40205400340501415010b4071089844400f284011000e0155480c0c026441004100042000f0540158020031101c500c0e00020a281c2d046d40950141e180348e9441e84900000d48400754a4241710b500300810060350f080c054242a40c002900036010794101d16034003100509807034001d0340c5038170800f80c5000d03101d40031a031074074070f508110040080b41009141c102d176a541c4549416510000c242d40740848024010321003640c49190702e80c013075040016507503040326007408094865602c042c10300c1d131183c2025202d282540b0003424014a0405000f40d003450f100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 843187967 1250 843186717 843186749
    0x5150103060e161404030609020901091808031008070618060e0d02010c0606181409060405030702100c080720493005031b13080d09 58
    0x2424800485600c811215412009503a030f8002c00e551100302c15405105401c030000c1c005c41000f000303a210740d40442c0241d40d07404407683c0320502c41d001c031040507460102030100e0b107400300300142e008001598070245000c401400c07550f0311180395140a8094100e6804513450600c50500e05050b010b4030f0700102140d1034520000d8000c0320105404401e8480060b0412824000e59818018250130080090400742c0101600090500004004161030081041c01215030000b240349118006007043c0a0303904800175500d401c2d500da00304a581540c0b00350800902c0303c1d40c03540502048800c0702510a2074050106480300c40256080d40046091a1150f6407160304046401c10602c01d08100c61031840c0011100740c0304070302d050361502d641c145401006080d40d0f103031481100204200524a450021084c0c1c1001d1410148442091102d54054180a000510500004468040540b54070645041c50540d00349031296001114080c4c080980140c0070551201160b01d03d010303401a0044001c5c0311401a4a00c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 843189217 1250 843187967 843187979
    0x1008040f03140705060a0b01020d09140423250c030f1d0d0f05070e040f1106071b0609060c05030706050907150906120203160c150608010515010306 65
    0x241034591000e020801c2c01c04140710503450300400c0354403040e04082200c40b186170580c4004003130000390720082e0050058144d8000902e02468213074081da00e103101001c5043c08900c0a101c02004640d1803142413440c00354030025038403411b440b01d502622407404000c041d90b03c00005100b0031000351240100700015944038502080d40941418803d4080b440e14030611201110114105088180001e50080740c05621008001c1141422180103200c2c1c4c0c281d40c84584c2c1c801940d640b80303008a8000d011412181004000070301c0c0807803203120030b103c000c10640c1082265100d402d1a90841d04c5018110101c1d0801030015581000c00c1da070091174285007403041c0014a82d986a180c1c0200c0c00014091521400490f00c2c2e050103202801c090f120f4109001078040c002c00c802014025203103d4140800d420040d2901d02c82c086000312442040407810881a10a4801d03040758441c0342c1c100140c690a01829660400303601c0c030b000e000c009080c22000400d650400e0306149a030420300310f100034141881e01c1d9041010f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 843190467 1250 843189217 843189233
    0x30b01170705090904230a05010c08060d1e08030103200307050d06091103330105180a0b06130f0e10060804080409020d1e11031f08060703050105100804 67
    0xd0f0401a150218540c517103180c04c001000c52151402c0b0401d601e281c10403c1d501d400101251454014002440b504200348410788503c90160342540c4c2010f840c3d04107502065218440060f14114458101421103032503e803468035030020382007240c3c401001413a400340301e00305040f401040b107012005030a45615001c00039080b070791113000c01032030b0035120020174080c851701d45000742004c180507082d07481e6200b8148940ca117010303c0d01c0e12840140e0709402c6650030101d01100d414141c80e000307404144000000c01101c5441d14005001d41e00403074030703105030900f551204e602401c52080b00758050444182044242124452203400400c00b4030018410010440e000c0b1000c4001c94200d4180000d158907142402c0b111407050f9003080100b6400024400785244e41e41c0c2c060480d2040c403142d88146144120545c1060741c03070041c110019070344180007081c03840441d401404180c51184200c00c90244d51100c9071402c10780100c451170042a620350040249040c00d0800c080c1500c5149401c0c1c4583c0f5282d65054a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 843191717 1250 843190467 843190477
    0x72601060f0e0f0d02060f0d05041407030b0414030d0c0f230301030210090909050c101e03050a09020d050d020111040b07030f031e0c021903020601120804030b0403030b01170705 78
    0x449132040081040954503a001210840804001400da840003204d0201000d0720041d0b4048a0041c04521085108070300400d0030000d982c1c0c40f061003c41030301c0319120407a12a000404160f01d43c0070401c45990a402944960a00c030035107501e84a04581d10b0300300140582c0072039a00d40700c03414030a21a81d05e030f07910044200c0f4190303941200c031081d2035000d442d0102c0d030a1840e90020004549004081400e0100000ea07a01202504a900d0440d03240b50f80d10031516101d60310020400383e40c0ea01034139805203002c0e030010380d84821002c00000b0064074540004450f80b40500381581d150b0005980e45020590a0280140035502d0404443c0390070714003114031519100d0207030043c0401c01600b01c002d805038800c3d0031000c04004016200140106034060702d42c0100700309180400988205000e0305040c0b45c5050a00488a4040d00039081d940c1c40c04900f60126007800100711a0040104008000980c411103100d010350f0090390002140760101b070001d064560105444c02201010348200307c0016805400c0351 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 843192967 1250 843191717 843191719
    0xc0302040e1f15051804110f0303030a0e19030314070207050607061509060b0a0f02190b0c0708030c0a0e0f1c02010c21120212040b072601060f0e0f 65
    0x20b203070844680c80094403900f68104990282110085039070300203d52541c076004600401c0131070390102e040c1c81040b10803c05800380f0358064000f8000505221290b5201c5e02d800c010003026501001c0400032464030030794000d14110007003641c4004d501c1c00406000a4030782e004c0c00a00050030280d007064001201800340010050001d51165280d80c80a00d201c00b00000404074a0020321003641c65150080d20754200f02c40c00f0002640b10a002c0c000503100194220040703000c0c40c4007810401c007549500c0c1c0309a4000300740d00085841080b59000182000e00214800c0485908050300d031010620001c0a40300b800107464401d10721a0010840f0f80d40d48007a46100c0c1d007166a0712040b4004a100583d41390722080000b50524051103181000890086440448520b455440100b48091540d10004a000c0d0340034031500810030800040c00116041c041682006031801c1111042d1190040ea4110080780d110600e41048280010070110b0342100d84004110031038140300755500c07001c0c030214030940604070017a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 843194217 1250 843192967 843192971
    0x60e100f06050a0b161403041212170121140312100305340b040612060f090e03070c0f0f08150a0b0f120309121501030b0712090c0302040e1f 62
    0x808014106e10103038100c4000c0f07010750b501d0b190343d5100d2001e45041e48201741c51150112031050314551103110800d041020880d030f0701c40349908041d600c025140c0303d480084890314040e884407005c101c0c490549510301c4c241e40025695040340040707181413003502820340c41c00d42c00c03069014000503001040c2500c0c903c05c0e502a16079400401301026030103000c5842030200c0001d2803600400d50b60000790041056070450f403141008100c40e05a2001150317410321a140b410658154180035030001900301050214601c0226400d103500c940f944017040403941e01106020211100421151300c400d0122001004488040c219001ca02c0141e030349126030080521103450f07610030a0b4100c5541d8110302134403a40300540101521070b00310005660b658014444c00b44541010803032800803240c0003603840c400d00100004110142d280d50b44100b4800c10151000c0103101070110010100d20f07242c410001030314011110700108a107103005010481d0300d4024851250b801103520712091030b000d509405002d01040d080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 843195467 1250 843194217 843194257
    0xd02070519210e0904060903030b031929130203060105120a1b0b0c070806100807030b04060f020a050d14070207050111070e091e0102030112020904060e100f06050a0b 73
    0x1102d2840c0307201002a4004e400c10180400c1c400d20340d214101d2030b0301c00c1c1c80422490042104041d038440d103107401000c00c0504000c4c1c00d40041c01e80d01080c118031408c07070381030ac104103451144003c000000700d4032a1907001445080d00190303d010040e0a005020070340b03e0003000a1040c3e401511080a45000352a5040c001200c60040c00e2403620640144401600e0340e444204156850340c07903a109208001e40c40c80b0b40404a80900c50341d66521040311040c00041801a141d03907150054098010000d41c1c0480c0e81d003268561560b070350300041801700c509603a0141d4940002049104a81c810400c160780e5400c500c040003842900054100165402400e0070b020543e40c0203810f51900d02150000c80020320840b003881b190550000300c0391484444041030381103070030912020600300d0000344608500070403070000342405410881e4245420500900c1d01040c405074945640b494610030207200485640d07030700e00b0134200d510300b40714100181c101290000780e0b2601d0300d0484100c0c3e005064030050100c180c403003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 843196717 1250 843195467 843195533
    0x140f0a0302090a1a060a0512070903050a0c060807030506060a2709090312090317040519230606090604021b1204030317060904030e03010b060d02070519 67
    0x10900159402000c0d40807a1610200510140c91400011851080b00098014040ca40003042e0b0344414525504c10b801c00411f95001c4010941c09480081408000c00d004804240d051002da500c01c4e0060b020545101e183c0340c0002d080301001480c08040500d0b00381406907da455104076100c4c0741e05c525150464a070814890303095103c10072500008104101c0d000540142c00c0c0d005404003900030789a400c009100900f0304000d907501c0c00300080000b140c961000d4840c01086c6a030b107400c24002c508940030071000f1160082000501d14044e04c4c560039401956580b0440c51181c0b550382d401d40c82c00b41040b801c0140201d80a08405000180f01c0c98010401c00b01070700c0c1980001c0203541c3c020b41100c1601d80081402000c5a101d40425000642c220300703080a815115840a070040c42c4c00741c81b170205ea0b9141d0f00c084800080c1d4192003541035403500164841940c0c3c1401818514455010040e1341c0d82031031130450b180601035841c0140799181813a1a00104420003401011000b21010841c1082d01240d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 843197967 1250 843196717 843196729
    0x20a150212072d05060609250305090d0207320a1205060a090b0711030d020c060610110304060c0f062406020c0f3a0c050a140f 56
    0x80301c0100c806030302051403000c0c000c1c00d40d036140d61000c29a1036000081c401c6001c3c101e03800441200038200d42e2021001c584542442c2180c550710150080a0704032440c2480241b44020742c10252000c0040d03103402c02d2180500e0180b18441515180d40024816586000307015900355140c46412449080501d40380354000c8000c42c030b01d80b11031100a24408419440d007405480c0340030516010340b180c0c41203400142c1034185a1281d0603556402034134007140c50340c0d1043c040b80c42d03603c030b9032980c42180010312920340041c05d2800a485045401d0015007414074100c014089850481c401d050204a1008408c1140c180d002c012141030354128540300401070b001c0d0074040b404410305100200306030301c2c14956601003012101035018482105408110140d03945404aa07270f10b0074040d820740d200c41e80d40c550185610303000b44058200304440c0900070b400c01340704592202c031a411a000a0311075000d070044404203c40540300710302a10301110240031240c01c04492401c82840f081650740104109505101503544078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 843199217 1250 843197967 843197983
    0x2060f0112170c010903021c080411061602040f0606020c09040b01170c0a0b0d0b0d050c06090102010e07030506010501200d03020a030b0d03090503160b030f1b031015020109020a1502 80
    0x80c0e0001c0c40303032003154030b030080d0342c3d60000d0b01c40d1503c042842e504200c8d10b482818510700550300710003416040791072007003040890b5015042d1483c404600a415600580b00d9014480c078610416500160710351500d0400ba007414030521565201c0d5411108110020b071744003161905450303144003001c00c0001078011051402c040810080d500100782c060014031102c88000420840062103000c0c8070500402d0140b002520029800500d541c101000c220480d06182c00a040c0c0c2031014030000c2405060010441e0030040950415281c54003e000140300b00e581090107480c1c00b0207004011031212a5804038141c40e0b04042800c0c0302090b40008801110f544030360802c3c500000028a00307080c0484524002d41103074600e1041700d000740500c0024240020f500b4514500701d0300811951b0f441c42c5c0d50b1918810201d4002800e1800001c42c0004443c4565010303c059403041001007400056103003080c1c00035240c0340000c104102168106000e0100584480815404a511410462404c03000200080c1c0c04e210034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 843200467 1250 843199217 843199237
    0x31060311070f021314241e040f0603060e0d050a0804120507051006031718060d23040c050d050a0f050c030d03060306050f010e0f0603190303020a02060f011217 70
    0x410a0003480341c02807051286c046c403485054106ca010042044450742e0a4029400358410001d80c20300051543e078040500a82d02d0061002070704030032006030f40d01100c0c00c03a08280c0d0a03d80c0c1d452400c07244401000404400035150400c1c50a081403c8002401c80340300500c01800c4e00c85030001c40b500c140c052410795018a51000543d0b82c9400000d4811000300410311007540e00d100020303e40c1c40544219001c0340c0c1041d0300850542203203000c80003802070b9a0303c10764815400c0b5907039100c504000e003000c0030200c4003113801c0807120465081504003025406a80d4102510034091070341c64400040002030341e18900c6500c1020f403084440682003450410922060881d01400340c2e190782c020709603040d8407003425a4462101048136803100180341032551000d000342c503100e29110011481c10074a01100a0780904010201c0b1024284c49080011000480340c0880c0402e0300070450031689034041c01031030b6005d0b1400c00c1d504041d61402c1003815407034010b22009010b030000a03964442c128036540803a035401e41 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 843201717 1250 843200467 843200471
    0x31d0603070305060102070f06170402130507021005060405281506020d0207080615130213270911061b151015020c04020f31060311070f0213 62
    0x1c1c00080c0580589000c1380c1240c010300a00002141c0d80d000705046000380c800580e0751104c0d00c80d60700d203110440b010190040ea03010751041494030100e03c2c07500550f0720564090340a8100058502c80180036118050040c51180d4200800c200900c0200307203a80b4481c00d03845500c18544020110318600504045205603a64030b00c03013034003080560300040c00f44035990007582150145566260201c0c3c94070380544901c80c1190b150fa02e42c020303503d4005151010000c281000610b44001241c50400141c80c0e50712251070402c0390400c0c0380701031000c80000500400e0094050206a140d540c44483d802569003d040c801c0101140c1c00b44141c2209282440c0100c2800071516914100c80c00f41c00c03400011140150585941d03400412074103a40c1d8111510041c0303540041c002c070300341181000040c0d0072003194000d00d602d080c050012a401000d0414808058010440100800156082e0040c07010b6030070280c00c1c0340c10a0b0310b400050706c03104102d500464005080c1c845034400c1d4070000b50301c0c80c0d42100b0780711654 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 843202967 1250 843201717 843201721
    0xc0c07060807020c040203100e1b12040606050d0b0105061332150306060d0b0d0312050c0403030c02040b12030705060f180a110303040b070606050a0902120103031d0603 74
    0x59040300d4601c0c0200c0b0385800701d40b020f41d24882000240d1108a0341c1214682040070f003000a07501c071920b400d4111071003451f080fa24607171030b03c3c6000c000d40000001e08050394145041c002403140a201d1100a014192020350902071241c50704807401c4c0c0103100e41402100700081c0340030f0f0400c21400800291030000c418040d41c0d540e8404100b034841d50002040484003071011f0500d103178900b200c400c1c10340008424030142190759207820051560000c42c2072103140340e21450810b86075511000c100a2036403181d201c280790340781202020310490f00010503200b5661000c11041c00400d800c00c620012190b8100c8012404a40e9103000c288514414100b40d04284030104445041103804600316204209a0072903030b140c0d03640c00c210044602e02011708000700f40c004018450105548070f224601a50001c0c0450386056510070707040103288d110500984085a45500c00c2c0524a44561501e0041561800560400004070002141d18006210040c14407220314071047c1040101d43c0d6161059200400c0c1075201c4c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 843204217 1250 843202967 843202979
    0x11030405030d051804140103032f0303100e0121060207020918010506010201020f0f0c15010f0305060609041208101d070f0309050309010f0504090501080309210d080c0c07 75
    0x10b800500854201c00408004c000c018145445040e500030300f175243c00b00304c1380d107140c6041d508010101503540300010201c000c0c1740442180280a00c0d140a090015640ca24001004a05020140d00240035000076103004102240e00182402e09407410741110483d18946494140001c0c89141d000941041d541e504200c1c03241030600b591040710300d4000c000d010964520004900701d119003c90401c0010092000306109d0780d441c805420482007460855441d4030141980035007040c2d090344800c800050a0106008010701071001c681c1088050b540c0c070205083c83ea4503207006210022004c010000e0307441c0040c4815041107100e030010555040702c03c01140b51441882e40451040300e8140200e0428075411080318482c2c030501ea0582c1c0c101e03000d54148580600110344e5043d606410100300f00c814000414092a1407040b1340c001c1c50200c005641e295000800c0c000011f84260382c0c040740c0ca008220200c07000d0700110b5401c7c842c4c00d151030840f900d0307a54004007103014000d54400c20310314807800d0004941 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 843205467 1250 843204217 843204227
    0x1101060b07021e09070c020616150e06040506010e0712020406020109020901060f0804080d0e1006060905010c050d051c0e0d0905150909040f020303031e16050a11030405030d 76
    0x1c8240241c4031010328220510702c04012581c0c02d036800350410580c0c000513008921078014910040d01c001d0010340f130700040010b61a880c00290100382c58118400300d51900d0003000c2d110f51410509194007404051030305844881d254007051007010241d02e960700014403060b10a22001940040c00c0504644031038980308001d0003000201c40407409520382c4400450a1800b84000a4074012981c1d6101c42e1a569555145c1c0943c101034100c214207501d41c0b00c40100c8182c18001c4032038813101c1000000c3c0325460001d00070308400340d47d031009042c41410380389600841c0300071a241990501c0c0d810415610103140f040d000c40da0149a464904052909650b03450503c0b01051403413125095035204103c05072180c0c100040303001501d401154002c4100980101801d0058039194018002c541e4003201d1540350b0042030856008540120005016648101180036460315a41d04408003101140c1c80640407a00a00b55125950200b014084000b002c13031003d6500300111405000003030280d85551101a0000d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 843206717 1250 843205467 843205477
    0x5250302070b09130c0e0301020a0e0a092924030403140301060f082e06020609010b010507200604180b1903080f1e03160e0901151101060b 61
    0x1005009460000901c4401003042e0b80703901000400e00d4203040202040d020050605c0b258000a1083d01e088030015a41c0030701c050140b503015522407100d140e520200b0402a4500f41d004820b40d40c1c070b81151400c044200d00d6581000c0700d20360a0101100c1442e40000c1c00741558048015001c0180340c94180641941502940c0250b11075140d90040d403009101c01d8006002c03d0141900244c05580d14062040c400c420b40ca8001902600000c13120f0881030143c0848211180100d04c0101d04143c204000350303040203040d42c0404a03900030850001d60a00080051199440150001e0808a40c0c1c084441c6198503501081c50010f1050784d0321540c9444114880b8900c1c5050800f480c0707025569086070034440c0c161020340c2d03640b19181881d1410766444070140d403c10381c044510414140010200c0c0c0990f849424540210a0111038892070308c02410001000d21102d42d40400c042c0c084840c0e0796484488103a0705641002c082182115554107003250f814503210783c501c10642c20000b000841d00c08500c0104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 843207967 1250 843206717 843206723
    0xc06020c060c1801110607050d110f0703141804090201030b09070e03010e0a05030304080a0212040b090406330c0b010e060f0907050a08060406080105070306060809070b0d05070525 79
    0xe0704203030b0002d005580b05c13003010041c0001d9403ca003001840c0e41e40710341d0042202c80c1209200140704a1030081180b01c0b500020100344842c2d2000130104103254201310700c2e500d0030701030060381e0740b4008004410b1003200b4240c4606901940d01c3d28810811603000e504104407800010385032102e50726003003000420984141c0f404038000d52034984405014100450030b00350140d04000118030310748865079603007202e80c031810381d910071402072100403e20b103000b000042004240200c9000c2d19010500c0400045503040c1d0b001000391f980b40e950701c1070001c50a024920004e00000029007241c0400e41040d511400d0071b20340145403408050003c255800d1211059004000c02e540b8644000341e048103102c0401019194200810802d0002080a52080414641c0042d0103000400c040782d45201c564290f5005503142c1c404a83c8814042c48101d5010340350680c070805400040603403e1812070142100d03c00c068981402544840001e48103a00400460380c0318440b0745070901c80034031440c00c200c0300c901c0042821 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 843209217 1250 843207967 843207997
    0x2130b070308151017040201090b03180709021903050721020c1009030801140102071d150f1302070c0803030705030403020c0301051519030503190921030c06020c060c 73
    0x10300c0f40da003403480483e070951003584c456451202c003170783d001448044010412030401c031400b41d010600881036009140a80e420f916051404159a01e40030304001a5400c140700c0c41c3d00c1406800080d820b01144440742c82c4960400090a8482610884074100d00c642d5409410103101040c408a6605500400315040140c0a451003051072200c02d5080d40c50240e000350014548a0052082c103030300c45114860042c05004846d0000c2e90358004043d000b28140301e000c0a9070204041082e859541e45100082143c2100d010850501e4800091020ba52810464610541c04107a00c001c20032401d680c2e4025000c00011245c40345407010000f0160f600450b402c80c014042c03c210301c01e031424140503c074014280011901909290b04043c00300394495081c09815070101640000080b5506100504880c10303d91070382d0200780c0c0c6003507028000c00923035846488113240c0c0702005801420802c4181e5881c0343e0603e0040c400c100d2f1820150040d020f0314015a140d4018202888182c41d06103000f007689070788001e46 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 843210467 1250 843209217 843209251
    0x1150207090b360c030106023904090f0c08210702090402010203160b0105030c011d0d081c050103020f0301021608031911040305010608070f03020402130b070308 71
    0x203035002c2e2804900250b0704000c40c1001280407414082c040b0440011054129818000710340480030114070694203542081030020040c840568140010480c0c51100084494280b44030388080ca100c1c0c040f070003a1448402540282940c5545a4200413071003500100b0b505030f0a5400c1c00d11540d4147c9a104148451080d080b810701003030100908010268580e51025051861702e8080c01201403006000b2411800104000c016030500010040b1000e4090644c1d03130780a60401c0e00f030503c0c06140c07110326070520600600c0c1100c0d110b03038004081c9072400151a10380d0000443d1030f11803118040d00b55100d168070301f18114040800c0003948164122402110f00c041c0005204c0145400c03032058000410001e107400110102041010008640140b0291040101001000c1e80c0c601100c00c2c040201e61040c0c03001030700b0000d1110900660001d001c469002e00102ea1603c0098904205075101c028061078000c2036600c840c3c01d803500c001004108001e80d55941b440b00345001000d454045403409411025442 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 843211717 1250 843210467 843210479
    0x11104180510301b0e060111100c020705060a020f0c060a02060f060a0522050601030b031c0c06021902010e031603030f02090a03030f030b01140901120e0601150207 72
    0x80c0701d10894549400740c0c50782000c600c00e04501e83c5030010305404144030608201e800140c1c03205480407240310003005422418203004240e1000c1d200504081d04002c4400c115400304000410855640c40030810300207a00c90a44d4800d90508586e6030007241e00400205503161900c0e0046011000c466000e000d861180c2400410842039000700510080143c0c084000a17090744541c0420030307044000205050240d03a40c40380015580c45458009945007410030501100c0c0c41024000c40d40c200c80242010b1000f50403a0300440e54075214100d49034034072180f40b0140b00c030940c050001c1d00e0007260001010755680d007041e4090149202600a508015803910f480300342c0b0142c01006031028111a50380c008200071a545088024040100c40c5a5030303203508000792269540c0e52040c3c0c2004500c80c0c0c68000b4691241000542214268412981880b040800c04075040500c0c50480c1c502342d009080041504040c500900c00501076070140411a104160020607450103c1c10042c03281d01965003101e00c02d9032a08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 843212967 1250 843211717 843211741
    0x4030206091c0801090518010e010c080a09020303120a020d09030c050607140d0e0f160608100b0306061b0a080912030c031e16110a0611100e0111041805 67
    0x80e4407400007860141c01442204817540041d50481c0f12105942c20200e000c828460071a942c0103250000e0340c1d902e01e0b000c89041d40049400e80e00c00d140be10100441c4000c1e80100f600c80c82294078489403d10244005001d009155065460103180e0010810200b00c203490084c1041c0070150095881c0e10541c000034465030320502d00200c13095a5009000d05014900c5001409041b0f88280860980543c52010020302c40c02c101d18500b500c030201c16149482e1800708050f1108001070300c0c1c0c503c51594801c003404142c0b00c5c074040f80d40100d0b054407801e59400c0c044a1500e402e00144003102c1140c0901c440490a00c5544405090310540031508a890266500031003a0b803403081c10104141500184a4103e61518000040e1440d04c5110085031070085040d80e0b56000f03100f03005007100c194180300e040402609042c0c174404003404003400c020003407100c02c020407070741e030b281a909401030941c9071081e4400c001400e41192404584441a1300c0d01e842c1c03a003000042200b201c4800480c01440c12001030724400440b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 843214217 1250 843212967 843213013
    0xc021513050913030c02190806250504060c081c0f0e010b03070f050f010507080a08070201060e3d030818030601320a180c0e0109051c08030403020609 66
    0x16211000c28003611b0f030a108031220105103401030907074103c0d00000c1007003040c00703213902c21000c841d000c2540d410400f04000c821000d00c2c45000070824140403c0c01907903000f0b070201e00740700d0f004030160b9101c01051b0707090f200c4a03140d00b18408940e0f05044640d03030307000c819420404155800000a000f19101d8009166403001e0910a9806500305603508010605010102d084000010b1410034039141c003e484c1d401c45035124100c04800140b0714403c0052155081c402c0201601001d000c2aa440c20003900c5070040606c40090450701314800c103400640300120300a20701c6070403240703038802c1c0000c5e07640e0600001e103030040e0b000c402c00495180d151520a140100e02603050301c00d90020b40740560556090b8002d203020f910003498000c4811040c11640d07075164000d032001000f41a6600c1001c020707040f0b800094881210001c0d00380802400203400b1a82c0041b542c40551364252040c20381d00030a0000c1d404c0c581c640247c05130010343d0001c148414990301050292007202954116500502450701c10b0f0700803060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 843215467 1250 843214217 843214223
    0x1090608160503130602040e040c0f03030e0f010e090a0b19030201021c171305010e070b030118060e0a020301080d1103090904020d021504090c021c0c021513050913 72
    0x1204030081c4410b002d18059504000d901a40c0041450142d0302c4008030381c4107800c11500c2002c1841080200129030300ba8002a0090368503100700c041ca1079601031b01920910781e15500c00c03800e00d0240340199228014005804000800c071071032900340200848010154202c038140950004a0348a4814000e003003201c040b05d42c1a1b00801034580c200f1020458a8501c0f01c0c0c0c40104060541c1081222809148840c00b8401444a590b406c010901e061821a0203424440210741c000800400ca00d21445043d2411510103c407280001c16050003101300400c1e080e00403c459240100c02d001c581d039840d601842c1030300c2c403001c06c0b11a41046000c080d980c1003152803030f00b00c40b5031042240740c1c200e09244404d250000c0c40580101d540030619070004105548150038403000040105040100081500a4035200d2002d4009003100400d62411100c4610f8403400c10814080c08080031700454503075000400030410010111600c800758901c00e44040c407072900c01d45100310f80090100d45082510f596103035803140c3c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 843216717 1250 843215467 843215491
    0x2040f05180106300f20040b100f09030501142703030402130f1e180f2a27020301120f0c15081b0f0f16021005070201090608 55
    0x50040d50303240912007550700c01c40d004190b4200c00000d04a00410003224032840100c8400b00c06c404520b80f030303820702d0b40341a4402c0741006041c841c00e441d00040000744d21820315089000080c468403e41300740c0030f160700007480c0d5840c1c00c0c0b00c020301003c00312206015400e5003640441185000c41c041c0d0b4010703441100d04145030010004103005140c0b0440c071548070b10032182c0c042095502901e007603040783d51401d01c400e803581d241e901d11440c90343e8600c60701000c901e00d03821680c2003820329107600420444600001700780491420007410002c1e0f14080e0002c50f01070440b01c1c41091a00c801c0201c04a401c0c2800382d12a800701c102ea070013a00c0903e802920b043e6608485151981a4161610400d8070007082054a01143d10b40011480c9188451314100026840e11640503904004d121030460510292880402c13050904c071030a507481e03040c8101c920b60810000c0240d1985040c80381c1041001c040300d0008c0d4428035000b21f6100042e0000080d02100c0d0003621000c3d4000c0d42c8500c160f070701502c01c03268031480f29 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 843217967 1250 843216717 843216749
    0x6111603180b0406140703020712050610050306090705040209030c090c0408060106140d02180303030112020a050306090d260a090b090a11010516140c09071d10050702040f05180106 79
    0x2c0204021b440c4041c0a48100c91486641d10341c41070b224040807a050345c075a0400d1040112640304081d150004210a0b401416540380465040d5210601800340070320480d0002080240c0382c0e410003100441540c024a0412682024a007401e0b85910521440801d030040000000c2d490703008030a154400310341c00045c2c502d040c0042520f00000e52180501144031201c0b4500980c0d40d8404101a501070540180d250904141c0d80c0108101800035a10903842940304004100d0a800d01041081810206041110000120b0146400c041051701c040c0c803000401081003068801e49500000c0d1203900859500c2c0f900c1d254981d072035803507049451000e440500d07124842103c5510801c01003006001418544041d01155590a20748c000b180340d0442945d40300e808c003480b062030b150086541005442c14200f803100c90034540d40c011a201c03c45410712402c490188154958050011110b00540c020b20800c10094018088070062006483c0c10140100d0f090810b01308010500c104001c6d1504505525050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 843219217 1250 843217967 843217997
    0x140717030c091c051902121e0120120c3a051302120709060b1207020703030903061505120703031421070e030a0506010815010302090406111603180b0406 67
    0x100b040c5006c0343c20425403070342400010030034040c070b01c0c15000c40044900034640c00d5514500b510390360390604629410001c0320010841203130080700e03504136210120181a54941182c074156014001200440a8118032190030f00c2c3d00d442040d503c92842005c20044451400700100101c0e4011a00108021800151400549004c1c081c001c40403845600b1622804d88a41036001910495400044003020128070700000c94031805015500c00b200d0300c01040b40920f15203006049107820f1002402160342d5071050040c078428001c4080107460301404880b030103600c80c4030407036a03210320384421360014100880c0c01c140c41600008551290654840007102460340720303080e42d507014000c0c00f108148400c10540c03074442c3d1030512880ca2220300502c064920b40d8504841c0754104501511224040c0d01944010300c01a9500201c0c80d801a8204000140d00c903110b040c211102d101c0d80407820f42c3d00d40c0e1484010b040551101d1000040d400c1e00202c88149a42c8101c0c40303120740528001c0c0030100380c0c0c4480b801c00d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 843220467 1250 843219217 843219253
    0xf05070f0305040206190e121603082d090a0b090d0605180d090e060405070917011509092006030612120a09080d090501140717030c091c05 61
    0x83c001880340317182510080d01c032100b40b0b060800706c0012410a0010091600c0d04103c440b450030110006400d40c85448000c10040701014000140403c1d00451408108c803d40070400c640b40701000205003c0d81d001038540c0d022030300300c0e06407148100703130000c4003056026403602940d10410010382000c1c0c0048041c1d0b1500003504008100d083c40c80228074203c050740c6401c001c0c156a1341203544810900501f00b00e440180c014005001d1400346040c0800d10008543c04283c18007201c50001d40d0000e1201c1605c6154094184c1d003003100003c480120001c951200030740d1001c2186032141101e480440e1040b04019044850350241c0c0c0d5021000b800000c05d50304082c04d01500100007402a1600c0900b000c0601840b600821130190008100315000d1021400420a88102c0e25407420194111450540001c0019480c09040b1455140110700c600030844010200d800d1904c2c50001c080e184c0c50081604005600002c1001c0d1040040050b003508030410025071810341c0e5004400f810b4545510304140d80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 843221717 1250 843220467 843220471
    0x350d051603061a16050105130b0a050702030a031109130b011101090b0606070206040b0f070204060b03092e0f050402010201052a16080c010902090108030f03060d050316030201020d0f05070f0305 85
    0x40130803d8401c9000081c400e108540c45015944081c90000c0e84504003044004001000260380e21b25208c103003e1001c0d000400e4404038841031038041600c00107075030790040324001c0e103000c42d810114400207a104100d940d00564903110081e070f1111088034500060500ba1544098084d0110b034145020480c1400e080004003442800076015502d081d6642003000840c2e0320241c0c461540e000c0104200007149414044c6e90000c01902180754190b050090340a40c98050035041a010707151004003070703081268038440000c2c070240742907030801030240b0450003440600f0b002c0f1004c03401940303000c0016600741c8148101e2543d01d01c4e040c0c0048035034141024400080d40c86250030318201085510600005a455402450251503040000c03810080d244140081d02a042c0c01c904880d800a11000490f103061b6020349034405030444001c51541110304103503045200704100c890340455000040c00a2580540042910781060300d810044140c00400c2d00040710702c280c4140c07000132080d2003020a21846904841d07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 843222967 1250 843221717 843221737
    0x10061202190e1302100e09131b060306081e120a05040b0415031109100810090203090d091a0301030609021504150e030703350d051603061a 61
    0x440c200b621031103200c0c100d82085500c4a10008088103410460074440080b000c900c4c610705142d11074058400000e554440018986003a00141c01c90600500c05d00c4e24040c07413000040350500d40815101c80d0020080c143c82d004250662068580210030340400210009007622210082c0c204202c001d100e43c55036134494460102002030a0001244105848000b003009021301844c40d0b000002179000a425903040c012654841c1d10103212080b210380b510b40c403002105a00d441c01c2c007401c2c2d0342c8642c0328141801a4001c0f901c05407000c0100008507000280e59000c15846407140300110756100c40c01401d2400b07a0105411440081c0010000110030b600f1042949100503c459400c000b000583e12041d086036000012040b980c401e41030786c180d000040100d0b81601074015103c6d0381d0660f114000c21841c1d101c0705841300c40a403a104c40050140646241010b448130304080e5a406c1c41c0e541240c090101907031501c044103403281e20a00424040e109aa04131001c0301e12114028240462072031503600000d26007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 843224217 1250 843222967 843223009
    0x10c0501110409060630110d1404170c0a0816020d1101030c17060108090307080301060201090b06030f0606010509010207030602030109200c0a120509040e0f10061202 73
    0x5101c8100c4140c0241c405000312101c001444e42c900000141a160a41903624901c020400d0740000101c2c4c170f805001e41c0404114011035090440b59903001e1a1290484054540349802c11501c6400c01c20400c050186000c1d8420002240e40710340b0800e5648a8418644850340c0700d8503070080080c0243c805001c503a144980405844111500481c003031a08200c07037203c0396035500007103403c55030b018071031000703041d000d03160200010241e601c4801d203202020305042d041c0710070500020b00003030041048810056110301031a440e540d444801034068500c1113021a18010304100113500c604002802e02c844000003001070540e40c95490041d2042c0d8403000100e4118011301d040030000c288140000c500070b000004e4001814072401066155241d45100c1c60b004004c002c011034200200c00281402c4003030307040720113070780c907030409804c19240351150706441030300241000000b800302c04010030440081e84401c001d4941014400303680004445c064040c14450440c0d0013440c002500701402c108543c00030381c0e464 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 843225467 1250 843224217 843224231
    0x501051606200a020607030f060305030913020f1b0c0402030c070308100506280201020705060a15051e0907030605012f06010b03071e0e010e0301150b0a0215010311010c0501 76
    0x70810598010f01081000d0380c098418801000d0b4940b0580003d040c0d2806c1c1040094295a02c00740c5910a0311580c512904800c9038503000092036a040710710f000e604204490742c65001a8240d1030002c0d080e42400e0340c501070040303010414101402102e00c5080001c03039084c034105155a0540340703000302230801c0c08c040e00341007000b10722501d500000b00f81c80034005210311005d00e50762068400041d05074132120116401403040e04001000000c0c0642c021007100d801103002500b814445440d41506c1d845254001c0940205410481c280c45aa540c2c000c02620901801c0e40c80080503805e03112103105190008000401001d001c44140ea100e203445000f049111a8151003824864903085c002c0c0c100c119081d00000c14404042c1e0808581128120702001c903080d00c540303044001d40540303c0540102d040c801d0744565108280d500794000d0750051111034000d2070040e203852159800340c001040030070244c8105070308042c3d01e988507114181265404034400a070b000d0884011a03004a245104072425903c410b8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 843226717 1250 843225467 843225521
    0x50307050316120c23040b04031e061e0f110d020912030c01051906030c0501030f0905010c0203030601030e060108120703050408071d0109020901020606010e0a0b0318070501051606 79
    0x908500110165a00b000d989503040071030b18400c88111780105140801c001c100100c4024000741c4044a0f001540004001c2c0101134a5200c41880900100b50a2400f12810000045c181a83e00d1340707407010600f004403c82001c1010111401c200c4200c3e8a100b091004030800145500105007845002d480303d00b000c50307048066840c40e04001c80c118103d946841c10400c03a0700301c880590380386100c503030814401145544c46280c030342002c40c041c880c105501d40c1c04810300344405412480300b103070b4024000c01101a00704c1009480303800980b1000e000034100242c60340020300000c0d85a040e40c0f03098000d0a01e85020010103000383c2d10400080f000d00c5428040090080014041c40008003a2102034a110004040c2171354000d00c0160016010648103120042d11a40d0009020790b0000003820820308005001c1c00241100130182d04ca506424000010050042590800440c0f001c1a01c811a40d005845900642c1c0b1805900c0e040c01240c10710a80050121703010f5080300d69944400c1140302104c09180f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 843227967 1250 843226717 843226721
    0x2609090103050c01170c09041505030307030906021207082203021c060f0615080a1b0207140102191b1d0f100f05061c06080a110105030705031612 64
    0x1a1007982c0941142e0240100740d41c00400001e10340c411651100c440c0e1906410320941c80c003070720304003034011546c2d02c9104403584092070342d090140400400301c0303444410a150040011007240100c0f401030043c0c0b5010b910760f10700501030b101000d038440301c0325080000382e07020103c1040c81c82100014213410302e040040940c0703480d522018413482c007018050081259091480c00d481004040c889010b00c1c2c0b0b1005c1102c0e10009188140b4003106141029285d00c9903e140f0018180320314215a200701510b0070410081d400040050494030030100c03503590030400b03200583c1c9a00d541000001280740c00d40144001402400c1c202115030320b003624a5203c02d440701080c0f1a201e0b240c03c03200b2640e0303041c04140400e80b455503868540c403100d800f5414001c10300b86201400d800c401d83c800d50b401544d000c580e028120701065950310952140d00c1042004580c0c6071020342d42c1c0c103865801500e480c00c1b40c00040d18217501c00c0048a109055580b0707000e180d43c807070724800340f03524400f05e02060400c01c40041d51405001c0c0c0e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 843229217 1250 843227967 843227969
    0x706020a03030f0b12030a031a18060f03010c0c02010206010801061a030a47010f0309050102090d0516060806100c02040e010f051503030306030c0f1f09090b03060426090901 76
    0xc41d001b0f40d220b110002000c0d0031511300d00186514488100d1105c2842e070744d8180411b000901e0703418410682c0d150a804600080d07000040caa615508060b0008522640f00b03e040240034000d80c219011642d907200c44c0f80c200d03500c40c002c5081040908d0030032003121048030001d58110740548000101e0b9590364030302056504052103009031900d1250b512011003403a9080f1400c41d01020780c42c2c1c41c80f8800000018000c2d9040200b1b1000741900d0341100c07424428294140da000700e10182480f580402c1c2c0e45405a243c0000144804546c508010f01140302072090b540c6900c034910280c49080e0b090800d0f079040c1e8000409000c102d138016140c0c1c2024001c50820301884090401d450390100b282d0514186a28440011110380c5002ea8030510420040b5500040c4440160b601a900a0980444400895841c81d045c004013241c1c200c52160003580d441c0d0004461046425a6404020130000d000416031911b1040d5406081c81c082e800c20b40705071b5142041902c9091a000c0d20b11483c2c0f21540700030501007002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 843230467 1250 843229217 843229249
    0x1b010524060d0905030c10330510120509030424020a031b051c0e0402090d2003070e061801061e0509030706050c0709021c0e030403021309140706020a03030f0b 70
    0x15600038008d5240030001000081074450314a078081c261200c0c0070162000e883c0f01e581d202e00e07180c0c01c0703e04050b03004030f0042c1400b0f61203010500c01450450042581e0350f1149c42042c2d64403201181000008000d5405004901040c4e4050540d042203914122680d08080c4010031710951a08803100009504002c8001c85a4481f031102e01031941c4070750058118004112803601490041000341a10b80e10018115681da030f001070380540007240403d00d00f24444404540361703094400c8140208000902c211002d210300021103190301c44001400a0440e01c810a100708008550b000085030105c0b50243c0c692a8540b020746886414402c031200064076106251f4040c10100302e000400000040051140070098003000000394585900f14000340c0c50240c40c000a00301c1190364140080b85100180215401190000c4c40c8586203c105005d500080004020450b503c004060f4121f114410110700380c8125540d03030b00544a0141d160314140c016241340c2d00305034407050351242c0390105a910321034200705001d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 843231717 1250 843230467 843230471
    0x30e0c060c160b040f0b03040807051603060b0a1805150a060c050601090501080601030311030d0c030203060f0d02010f0e0a030804060816020a02241b010524060d0905030c10 76
    0x365890944080b50070b500290400941000148a000404101c0c80d040b603c50b011200d0390b03540e07039040c10b003c58020100000c0c4103000f070080c1090090310320500102074901503a0200500a5400b080081c117902c188030b411541d01c588407040b4403000d000d07402681c2c401c07014007924100c2c400d1000042c041c0507160b0003000114074410700c11024440308004c070342d01422540707004010650503e05247c3d501d4005100c0241040565800024081c0d024401d4441c1c5c0403d119082c80300240141c0068082e400896510b40542e14803401c481300d41c5030180140c86d50300e80603114040c5903001000c040f40c041000d804800d03040601000c000000501641c000e00007803e003503941c1d00007420103084801c03140c12050502011944550400e901503030316100c4898102142c0e03811000d1140c4514510040ca0140c0040341c103851700d4600006502c08030640040d481032a154a0701780d1111031000780c608000d03011004082e049001030003842414641a4003224030940150202e030700b0482150641d0b03141c0b9908445011500c0c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 843232967 1250 843231717 843231733
    0x4090b010308220f1505070501050c07060b01020309010f1206080f060609010806042414240a0f03080309031b15180d030c030f020d0b0906041b030e0c060c 68
    0x40d40100e0420691182c03100c1c1c42c283e092400001810259082c01518031022258026200050203801103e04080c0e0240013840f0134034000c4141e0380543c00041c010f0792200d0411452111a40c404022101c07042c0051f1504500d400142400701d5800100c415214043c50b500c0f4070124030664100042d81074116611f00510305450410f050003001e0300c040c0d0160310b907540020140030005401200205100c1c010801d000c40800d40c4010724006401c021654078424501070042c800401080c18680c0348010f100c062285040511a0511640100b10f20590041c0307081c0910920000c0c0000c00110f030001c442c041124208426000034200c00c042a090250281d800860842c0e600000e241003998004c0e03506405886c0b002c50206040d440c0c91036501803104240c4d552114001450299200001c0505040c40864071600010700a10007450b00800039486030000d40001002440c00b80994104080c030050484000c03202200c003600903010080001407940540d00c00c03000039446041c050080241800010205a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 843234217 1250 843232967 843232987
    0x7050105012603070b1f03150c1103040b0d020c011508010e011b0c1a0c0d0608030703050f0f070b0a02030105040f0b010e1e04020315132904090b010308 67
    0x540202100c101110302c01207104a4030300700481592200c035040f80c0b1171304483c1e031668445098410a082e080004690101000c01400118401c100e20050720b05003c03c40d001c0d60b1a81500c500c568084c004c246540200414800690084013400207049250000360404041031200c0e0b0a543e49a03080c442c00d281c01400130004a00c0c2401045000c031325013802001081c40491140200010b90b501c840140032410b6100400c10190044407114071392a090b840d003090a1085e0444074075880418000910360404c2c802151003c00030040361300259060700c58518001000a00344e01d5034001050303110f8110030030310400011503104c03040e1521501c07000350b005a696050104000c1102c09050850845610b000c0703400300c150741c001c100720350000411a0a034078401c154031101e91054000b0b460b6240c002e800842441150201c1d0600c44414140c1110b00074403400c00364407804102c1e0400458030b100e92801242a002c501c0078520605a00517010b440860020342d540c0b11452404020390003195844c0380002ea00f220 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 843235467 1250 843234217 843234239
    0x4140a0507170c070212030910110c12060403111608010212010b130902180d150b0d03091e05120d02010b010c0b0f0a0b090f040c05040204061d150705010501 69
    0x40c05820030034030b15281480c00d2009501d00404a000b8005d0070742084c00700c81e94604209603040b124004248003610356080e9030090004031180351100c8544510111001c50340b401c2043c40c410486014002d204540d1162030072225840c0e0054004000c3c000c0701103a8121105a03140f030350140171003500160fa42d5000c104406039258050380140c00c2000e0610a00d0000708a00c01d680c2c0c12140307080d00240c1c403440900f40d40d40e88040140380085d403113200f28000008000082205010b9105000d200300220304020301403000c0c41c40e6800c4000c0006015140034456403040f80c082150300054181d0711072007540c40b4030110750100f40d14000684580e101c0d02c85085080e40c24025001c00c11801e20b0240410403090752504408000075011503950062080018180c3c085507111a45d502c0c0010242d01c2a410103181c91800d10500341d500f03503225040204041030034201402103400703c030030303582c0d0320100c1d030000114040e10a40605138055100070b11ba00b00458100f1480082d208450003a800069254503004007800c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 843236717 1250 843235467 843235487
    0x3031b02010203030a0504060e0a3503070e0406120b040209130209042a06030203040507060207060906141608040825060c03021005090c210a0b0a09050a03080402040c1d0d0204140a0507 81
    0x34040bc11130004408140c100b800b40d941255040c10b18841000120300000c02030450b9030021200507004500d00030910442e140d8143c020b500036141c540f03054403001c0c991080c0c450301b090040e401c1012980880c2c00102d80d04140880181244401c1da01840002119000200245d0103030f400660080184000d0120a0008034000c200c0ca0004040c000c1c036010000d40f08040c98810402804020b02d0481c0304c3e42c1741c002c1100da14241a294120704802546814940e641050040c02d00030b1040400840c020a8000840780c6120b420450f40003940b46007050440740740810110480441c024184010030608d1035005142c00b405464014145007108401480b0004000d80c1c506410780d90200820154580081148070005400502515140d80c9100603903000d403046200c018000d1184010800516a000019138000c1d0710860b414040168100c6044440d0040040301140ea100c4480310381c81300b40740203130030059aa440508081400185103240b04100c2e00d044590340102c54a0300d041084150b84554015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 843237967 1250 843236717 843236783
    0xc12061a090a0e160305160f050a18020c011514150a0e01020708030c0105100e33090103140606012604141603031b02010203030a0504060e0a 62
    0x4032503010000d0019020300c4002d031000300030a40c0d8108100780400248070484441c00c41481000040f9928542103980d042204422400703009076000206505825807450011100000c2c103020003c1e0a01d00081540202002600d4249a00b0040d01c40215428002c0d0505800c0074542c1800440c905001100e1000681341400e10603040e05914440c100104030965040b9016850040c196041581c0181d252280340e82141c10240302c042003c440c40c0405401c014810380024051000399039071000c51810101040e903180c106028400750000c569802145108030071020300b01440064480c0c0c00125602e11020381050b00c1007400c0d032024600c0001c0420031903401070ba00b0301e0300f4005150301c1c0d503a000d0f02c003010401180c0e41d1800707440031170103014a035082d840d84140410709603400c01a0080229038240030511045011400e40c4020700c1c07051688103003900c482c54068001c0d5145540320b0403014010100204121121580c4d0b04000c500742c0820400700103618851212000305168a6010b611001d6000d4059 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 843239217 1250 843237967 843238001
    0x3b100305101a1801030603170301080d08190b04061d271e1f0e011a0d060207081303030c1a13020d050708100605040f0b03061b070c1206 60
    0x80310769102e0040485048010f01e441d110300c1955641d00482c0505269403028150a001140d0b8405006096004604a948240444030303403981c030020944800400f204c0f004425400c18000036031a20301904803250300b21000b030000030340300c0d02d90050b204595803801040c00300040d90004c0040e0006000780600507071071050000d40400401c0c211a03551650b0b42405d003200380143e82102d840d00c04080150111118100070300600062580000364010100600401d02e550700b00b01c1a07540810b42c004001452000c003411300b9040303907501d8907543c001e0b50050100712900007080003241d0b403407006808040042c0d0322070ba40700340d2109180c0c1407500640c1e480d0387c0e45c110343c8040c480911010b061030040d120021a811f54582010344da550902c1400c08030300754032054160240e141002140e818691000b0140d95084500704020b00e20007801d2030840e1080034159816610138400304000d0102800c02038030127130b00040b049142150544d1a1019942254003070424480b58030307080401c0028ad8000d25072620519204 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 843240467 1250 843239217 843239249
    0xb03010b040605060f07050109122a0201051b030d020f1314061b1509011b05040308030109053414070b06040b010203070606120605073b10030510 64
    0x140c454031031482003200c1e0f001700151303503c1040000e4000300e00c03613a04000d01d040320140c1840040c0145110032004030740c900d190844445600d008031701c444607943c5c041e91a9404e1404080c0c51110300f40880944c0301a51000b40807000001c403142c0024850909450203c41d00c1d4294101c4009801c65a03030400681e407520400001c101d40c40c2c81e01070714003502c44140c84c20b030b141e1581c0101d5402d01130000d56001c804402d02041101d507000540142c2c22500c900c803108586000c0121088810f4002d5010007080b406081004000e000440e81105401808504241007400d051204001031201e030a41c1100100392110301c11045141c026023200c03400c0f030952201602c0d20000e80c0e2492070000d0020400c031303c40c50380d99500d00f500341d108006a401e40c603800b0343c00304803081d120340c0c1c3c02d08504480c043c03c4132002c0c05c10000584681c4600c1b040100c00c540c4200300b0311010409010003040001c15032007026080318044101c0707100ea0f900320b41c2ca0400152078400040318102201c4480c0034101c01e41021040701c0700242c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 843241717 1250 843240467 843240469
    0xc0105060306090d030207080d050f0103050601090c020a260703111911151603090801051e0c21070f030f060f0b07021801080f070f0e0609040c05130b03010b040605 72
    0x4001301400524507005039144130910b04002c1c14054411401c0c01c1c145081d003040707035a1304154542d074140c2e8042d0003299101ea030790b0900c01d800c0d9840c83e080003006800c10a042d0000031101c94816180b00e54820103c1103000705000c07405840d40044030705a000401200e141a40044207104203042030511422004140c1ca4603100c1d280442d4500000900400c81520b0707407151100020103075204a002111402400e0009003002407003000c6602881c3e801d5480c140118810f128810151180480d00b00c0503070b00e40d992101c41ca45580d4004c1c014200100512403108000910500f410900c0b80c94961255441c10700c080c1c20080131900031a100602d0a03203003103400e00c0000101110281200c101001e19075403904688041907040700611001c1c10081500710000c2140c40010407018404107950003160300d90360b03540b54101c0500c9583d1040b0110000d00801041680c00c0c500702c17460f07125000320901100d6541d9040402c00c11340c65000510314850b501c6128034200c0c46c0038011801010000c407028042c09003008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 843242967 1250 843241717 843241723
    0x9030405061c0905030a021f0203060a1a0c061627140f0405010306290a0b0304050c030d0509010306091b0318061103060f12101508120c010506030609 66
    0x844200305040000c4018020104039802034100340e41e108003034940b80d800000b030103541e2320f103824011110040126103500500e0380d54400d42e803003400001c007004c502a2600b072000b41d10170040b142e0207440c90420030443d2500a01002602d0262800d403e007221a401024001011010140000e0141c003a2111400600340c2c04d200c1030700d003622550f80c59811a135528900180443c50808001a041420f000000040c49915402240040d9900424280d4091381414502030030100000d40780d803210441310b05001c50409200a1030b4000e100c0e1044882c000710300800039151495001c03008001501c0060034442c1544c1c140104070040c00c4010052010b00c000d0042c00c500302c04500e141c0340402d40d40d502c0e81040204605194050150000c07000c0100444d545610305a0740e100f1154103000d1044112040b40f642007070301c1e0001018181201900e102010410040d01400c00c40d50403540e902164400840d64070001c5c4000c00010504d448826aa002c8440d0450300b0348000401c844d220790400030400481602c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 843244217 1250 843242967 843242977
    0x901051515070506010807080c1002030301121e0506070e01021513030207030b0f010920090114040f090504060501050a0e04030311120c07020a05061806030a09020411120903040506 79
    0x8499284000304a000c1e0031000740641c25001d442d03072003204000591046c010a030041522500c40c20b0b00c3c11480c414040c070441350b01100c18000160301c10401004840380743d0012101c100d102c1d5001d0301c000000030529980084204c401580c00c6e421160900000319006901102210000e0028080c44500100c000c120540010b00c1500c1c4190f2080c400400c05200307000140103591700c00c41e84012818804180110502d09024404c9820715000308110b48890580c100d058a20110801900e060a10001110f85044528440f66241400c2c000814400f90710032213040944031000001440b4589810080309944040c1e00c100e000d03001c5c00c0010700c20900902c203100e83c0142c00d410080b4112a40d4248690107104901c1004010102d41d8180421854201c0c000e140180c02120369005103a21002084103600c40d0742d101080814100f445942c887c00c01038040c40c0d2000c2e408900042c64401034010505540c00c4400c241c014007000a42903617200c141c90307052a08040c1d0701c4019070a16040002003a92407043d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 843245467 1250 843244217 843244219
    0xf05010f0b09030c030d09170a110d020307360e070e130507060801030312060501050a0c060608060c040509010f05011416140d11060402060412020d14031209010515 72
    0x54502c81a102001101d580c130350040c0440340b90400c0302e8001400c80059028240108030712904011130000b0001c2c409040c5500005407284c0d442040c401c101c001707000180d0032030300b40c0a035201c0000da0250001026024584041c0c4440810080c0d003410681c92140a50303860f2190b24142000c2101b240005108060719a4130009800300d40307400d44d50903610603094400401c1c0b0701c0390070004600c560b40011000c2c101c0e4469240d24404085039143c05060b42d099000705800a078040c0180248144510204186103001e1034002443d0b50310f44880601b86030b011a0700c21001a00020100312505010010310300401190b0510710200b828000020b0151994509004180c60040740144840c00030401d00031885a10084c038801d0742400304103e070b40b60800e04d5503440202e4066980da111005000c2081445181e000704075524041c20805960012484031030140e030041014640c100008100c2002d120b6071028902c000d5031220340044020310340c2000104895080d9062a0900400712010b44c41110000c0e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 843246717 1250 843245467 843245489
    0xc06021e060105100908030a091502060f0411040608062403030a080f0a0b0402070f060f060f0510050c06040c050a150e0915030d03051803070b040618080703080601030f05010f 77
    0x200c901c0c085031440e01c06c2d003049859001c002030324907080b03030090302050071210214541c43e554400b006050342c075090101d13408006864101d00140008011021505400d0301c000c0c000201c2e1611018014a004002c4440000e800d500300e1541f00c906114183c2942104001c600940c03801c11010b0004100e02c10150841a50000d00700114000503a50f402040240d94040c0045449079000c0c14101c5a0500111040d01c4071031a04640b03100100311030003001d05031200524162138480c036001c14011100304240c40007040040a02078800c07030000910869000e03502a20003280301c0c60405040001ca40080e42c005c0d08011202540288c0c5287c001041600d40801158840300035030f2186892000c070580554080e41c180070303c03880d40c800d075605a480b03140224050b03050788100b01c1002281079a24854010068405108680001e0006950780c20071901aa094160402090315603a5608030342c3c3c020900c01c4020907011000c101d05564503204508800c1c10140b024082ca5140030000d4041001c0d0b401a014405d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 843247967 1250 843246717 843246739
    0x31409030324040b060a0203031515040b070c1d07020d0e1507061b051309411009050a0c0e0d03050405132a020d080702190c06021e060105 61
    0x55600e40c85204c4000d0302601d61556000c45600013520383d8412103031090308249140305002c45040580c03100c40600002100d80e403903e41451019000c43e000b0410460305141ca0003030100b400c507441c0c4400420b950622401c0d0001e4145200702900788000312000c01c003040043c124042c0203503104406103110b070f9030101010703035199010704054004d4421000d59519034490380b559500c0565005000f4010800122070040290391038001541c16103064000c03d043c4034000e1880c2c005151043d1340a480d040140d19a505107042015024114000044070040c0719a4040201001a0303034190064a038801c020b01c4040202d024544005841807090300486801201080c4650040501410403a4080c010040c011005810110b2014010b003802000e02c0100f400000703003641d01215107181c84141041c568025041c40e44c41e91034205c4007405d006095400314401d82400581408080e001140300600a8400c03c0502c2d081c00d0020b03241c5460014024021069a1600801840081620790542d007086400c0a144 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 843249217 1250 843247967 843247969
    0x40c030c020f0c312c0a080a140408120306090702150406200d02040503071505030a0c210b01230301150903021905090f01030809130f0606031409030324 67
    0x2000800c1c04e81d00d03000d403602c026007181c43c4104103103444200c0b410484c0c5007124034410b151902d4104075070380100107035028040860a00c0c01103880404403880e20b10381d18100386c1d035081c02c41d203418100903009a2810000040c4002d906043c40c015a01140a00080c01c2d028114011320000384801040588420795860800700126444005440b0302d040003000301c0d031100c0203c948032000f58000e1143c24400e01c2214400992080e0440005048940c25290701d0b04658820a105014103940d9900108000b5140703022048034103441408800d030480c2c03407400121080000300151080f10441d49842100d803544c0c4801800388120421a03046d80e060740903070b000e0311001d01e03802c2c4c51611941d00020350007a00134005c5101c0700204003c01040302e000f2503811001d519007513149408141c080c007010341241d108015441d072070704040d26040c10701c0907903600c0083c1d0000c0440910085800540199001980b81ca02c19440d440e0301e820035907040044e0501543c510700300280c4882d16003c55281c024001740c110b01c1c00c0714503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 843250467 1250 843249217 843249289
    0x30a180b040b0408190806030d020609030a0e0301140403230f0a1101092103180c0b39010614030717030c0a0b090d020703151109040c030c020f0c 64
    0x81c851785481c500d880c0c810328207030160070884101c94150081c0709403001c558210303100050f1103009d81588405107103003182c1c81d041114501907201100b9059906c40306080c028240d141c1e0a0340c0300324000c1d925400e400950031101c8107203820b29060710300454024000003d034a82c140c000c030740f5524000c2c180102c10a101e42d60950244c10015000b0f402030f050b07001c150a40c040361004007408034013aa94100441855003e550700020308814010380040f01e102818800c0c4103461004120455100d61202d205802c19100d10180d10350f00452540c00c82c03c1c0f079640152629090240e5400351410003000e04d1400c441034042640e4881602c941500300800040e42d9000450034000c0b2082108028203039403e880550a1030192088150b410703160f284076149582c001b43d44003003600001cbd240e021031650600c3c80d0540c0d5010240090400303180d009801008000190703540c61050110700703641c2d41ca02150759800240064203148035940b04906a80101000491a64a103c03032609901e80b00010007200808080c00d1000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 843251717 1250 843250467 843250477
    0x306061903050a0506070206010e040c0b0a021c050903010c0206010518042103021b030307140307050405041508120c030901050d0e10090b0601210b01020a02100302030a180b040b0408 80
    0xc1c80c003c0326034000c00c1c89004242648101c50035004c81d40166643e610710616540d046402410b080b41504043c44550b00301c0008000d02429441180c40003c058809410038561100c51240850340c0010b40d488681003e000d010000c3c800c50010b408258500008a00b8021a02002c0d1486580304c0002404008280c9000c01a401c0c5484070701200c011400d0018009500002060342d281081c01780540301d00700300004507446042d032503680b0441c2c40503202190304986c00281c030700b4050000038000031455481350710400f1000c102e5070074004425460300c210755060004000e6002210380301008030b03000035403001044403d80a000c3c60445c0c0e8a881d4406131100405c46c0c141149914003402e04088802a490741080c00101c1c0550641002900e400b0015600ca0906980c51441d0300c603508100b1030048400da1102040d4007060055410f488905d40c00540e001001e0b02c00b0401190f80070003070000c5000036115096400c844121041d048a1440c2c0b10400d0714803000340000c06401542001808000e40801610 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 843252967 1250 843251717 843251723
    0x90d0207142202040e0109021908060111030705030d0c0c03090e0603030d060e0402130209010c030c05121b07120b270d020309090a180f06141311010e0306061903 71
    0x51103060000c2d00c0010754003e12071100050031080c000300d0300d00500d2003250100d00140003000c00305400e01c1c000b035541c0b02006040c6414054030780d00c0340c0b1080314141300428080e440b90000d181d80c2d0b000c0c014004211032481040008000010f038955001a0b080026101500c802039071125440d540e2000180c950301c168503551401d03078105140003540c607244192080c0035a00c01c43d420401d040c1d00145100403805881106400100188080c1020038000c94071640958040c000b035404440720000742240c142d1208008a0781c00d090222940001c810511009003c3d044903000c9a40b0f145403038842c0b00c0012006401400a8085002580842d151901c0d0344510320400750b0070740f48900304810000e03440307030800d4540501450f201d000040ba183c4062040000508100e058807108200315103840380010310000d022504c450341d5043c0b00000c1d04a04036040d101ba501d050b880401d180240c138203030042241710003103036040c0160000e01c2d010580d8041001c0764811019502c500c444039403c0f01075548491564030103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 843254217 1250 843252967 843253009
    0xc07150219021c1b0606171e06100e060d02040c050c07141008090f030d0b1002010509071a1c0b180709060e01111b0108090d020714 58
    0x111001e00201d946215103840d4580035030b07039640c010f6144241c11448a000050000c3c2484c01c0503407080103155140c81c1c456000c0c850020702c80f9200d0b00307100d10481001031002d10990241c040d4001c00d400360907031810301e005c0003c081c0c01d150403e4100c0c1c0c14803403884c0c0111280c1c08004800143d90b038590007180496103030010310900c11082c50400c0035086a1002500c40124081c00380c01040101e58095200840280a0402144100703065070466a03c080a4840c20071402000c0c2c2d040c0300031008001822614010302d00004480105400308a0040d0300c0381d82c000d0541e41080b080081ca181c1c00310310641150f45180c400c1b10000351300c0290b5081841070b1500e0000c2c0e14683c5008480010259000a88010b0241e43d000074240c403410701c40124100484400c07002a646800620920384a442c2201000c4810b0601e0140340d5808003242e42060703030280e00344580319400307207a04000c3c0d0f034031294040d003101424001d00040808214002e4403485140184040361140c40708041d070b1500c5102131002801402421 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 843255467 1250 843254217 843254227
    0x70f0c0b1003051c0c110a18060602152401020f0307050c0f01090f0308090402091e010201111e0f040b0a0507050d05120601201207020120060c071502 66
    0x1926281c101a8041942d040c400d546256031038010701c0041c8440d14140d500c4000ca00181e40e5074290304654005032060708039100050019220b82603440c00c0340810b40321400801c4107810101c001741b401c3e61b1000d4864403408080305000b6080c4820320880b80f64456159920400c41c00400181e28140c2c1c0060042543e110001d08681882000b254038005014111541070780f620005004603810720290003002940d44042c078003080040d00b107200030b008042c006003000d400d1184610000300202c5284c140d0700803107454004602c00560303081c42a0701042c00300d6550582070103c0c4a5010320b0f04c81c0d48146000351b0725000031303003841007421000c25030780100300f00310700d1a0b03941000c0f00700144590800401240c1c240b141100500740640100141e90700f08554420864050b0f4552004580a602c8000703075003544e84981801007100c80c0300307001d119007072001c040c2c1c4581d503070019100041003140741c244000c07041e010740a60910090404a00f060b000601101c440da207038800f6080070000c0c1100e486040d02214070001e8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 843256717 1250 843255467 843255481
    0xd090506040e281401050d02031218030a0308070e220b030a0c080a2603061c0c03030f120e072d0807060807051204060f14010b18010215070f0c0b 64
    0x101440c13403a802c0340c00c0d00741d0341d0351018004190b07183d21000b94560010b81100c8050203c40d000742880d529002d03600301d884140107020a0525651480c2a0002001441000a55a00003884c0380e4001e600340c54209070403901964040b00743c0316042040c140c1607101e4076088165903040218101041e000a5100c0c0311070340d203030700d21940c400031010102c6100c50055104802c900c1010070300c90b0328207101501d40e4075644d500400c024080005044400709001c090580801203000720300303150050b610940b80e820840f04240005000510b0034200b00440b1820b0002000b15144049141411501210400c0c80c00c1103541402c0b00750300c1a11884000c0d0041942d60010b010000016450202ca02ca91110032040d140d0580c111030601ca043c88149424200c40c010a00040c0613070300c000c4002e41107000003d4401c007594140303205600c2c03e038000111400049254040071440b41a503401d140f000340018002a078440e925806d40003801000b8000303200c8d4090403525900d010b9404000a6548a68551210b1509003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 843257967 1250 843256717 843256721
    0x20d0320040b0d051305061f0305031201080709090c05040c05040503030d0603060f020403020d0f020303041502031305030304180e01140108010903022509201303050d090506040e28 79
    0x30f81141c03034240004520900c0071403405022154101000d40031564803144007204014401c12220070b001c0d600c45001021030411b0018004210303d255088460b9490f0100c0dc52601000350030080340686400003030b00008020380d8281048940c290f401103400d0000483c140c0301030003164400e60705800005034075480703c072580d40b00c98262031098a041051713000321511380040f0301840c00000e40019400d114800804c4210289000341840102140e260949550180d480d116915415002503880031031141c0829850040c16000350105500860416103090100071156254080320496070b81d440c003c86080305020340201201c0001c92910045e40d5a444895034000d1085050035001402020500940700d100e0443c0c511400701c00001c0d550302a401d240054006091190323104003501c6108840241c182107030405080d030764400c001d0481d4090b00d18205117051025405110381000140141031100d640c40070f00307a03401d494204400303107410794400c0c2103162041040010311914100707961501f12854059 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 843259217 1250 843257967 843257977
    0xb0c1b03030108070e04120e130c0207050f06030405120c0a1b0512060c0a0e0409020307032906060313031205010321020106080303070c170313030e0907020d0320040b 73
    0x30300201c82044d581c800d100509424185c0c3c0051040e010840c0c44c0140318402c1d034a90300d90074002040601590b5102001d0000c0315800d00003040913800146040205182102c403810810106540007407075881e080c2d941507214a400b0103071a40040020070300c529441801c0200c10343c4181c1c00302142e8540740070540c00076501c02d418420b8510808050b0000d500c4420089015401903100c41c5400713040c0760140314141c5010030300400042d08a40c2d01c118a40250740c4c2000301d040114041d4004103031301220150100042111100311111031031701c0200340300c0c40d6201e14040b82da2048540c803056000b0b9900e0314040390400c0c60445042c1c8094180000802480000b44c0b02a1040054000e078180300c8a51400c10f03802d0350b0f0140b00e5008241c005100282c00e580c02241070400d104d104801c1c448260101001d02c4203550016250b200007550700d00041070401d07811940401c030f2004229011400d51a05a4009644000900841c02055211140c18040680000c40f00b400002e07901d14842e107075600d41e00004010703004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 843260467 1250 843259217 843259229
    0x80111030a0c0302070c050103050a1e020a0f081302220507021b04090b0109050606190f0e040e06070f110708100c080402150906120a050402040510120b0c1b030301 72
    0x600b220548809009200700c814050b803105080301d000e0314000041d40101001000d800c00d440e195903944c0189104940c1c06040e040d1a01320058841050100081070070000d4018541408012402d10520304d0100034090303040e580c1164201108002501c600f25400b8566402410f058200410710100c543c010401c007080d110381d800d1850a8a807401d040009031841940090850703841a001030241001e0742d044103600002c058095032030051250001c4a5414851342100002080c00e0000c569441d07001e030400402941c01ca0b0140400e00f4107215081d01c90101500003000e000f401c2c0c04501046000707105c041307403460240c8151004a50369040c01d60b12851010b4400080c2403070080003000c99070062034071034000c0350042c00c60082814280c0c0600816840744c079039180c0c02034043c440940d400581c50003c61080e401d589003c2140d041a10500c025908050700800d81203000e0b0505010070b00705054a4000d43e60420194080381e01c80c00345144c0c162059011204903a0507203070400d40318400001c001d50407550 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 843261717 1250 843260467 843260471
    0x40b030a1104033f080c040b2208060c19020708070b0a031103090601030212030f0d1406030a08190c05060901060f0b19030f0b0d0501052205031b07080111030a 70
    0x444013528144034080c0c4031035a03042c07400c2480008800c1d80b213500c020b6484604000f003240303410f4940800f502103401c4400c1c0400d0141000c03e07504220107049044c0070040c08044d00171b00a9003050a0519058042d213891083c45400000c00780101601c06c002801c028007024044d83d1456031505256800c0703074042c1802501203400d011020b801030841d1811684105034001c041c0843c0d03400c6501b0400080c040342d1200701180700501c08038000704402001445a8a51845c0000703001d03188500910301c03000018840c0740319030003505d80003000c0b5441c0c0003101d07140c2e0601101c00720003030030844041d502d0490110015009100d060100800450154408015a400403001c040c2c0030b955aa0314204038800c400049180c03248031a80c94291901035008050021a0800042a403a03000004075040e4452f50206803aa03a45810a12801c4141e0825400c3d1400308010700d100b4180260700c407650340e0311494161078200c1a00400340e813020300080c0300301d8000e801c23824000e00180c66110501a1203070410740700d80c00c2443c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 843262967 1250 843261717 843261773
    0xf0324090804140f100e010c050d02060411030d0906030e012309013611060c161409040f02010c02100509040c0e130b24070501060f0b040b030a110403 66
    0x21030800c142c03039800036004200d01c80d45d8020003006c542018010b0301c000d041c807140c0449980003c40a001c002000020760313008084034501403c0402c0320214a81c0014080c0e000044510b2400b80c0c043c5440041d508035040104150203403600c418018200e000300303524810051940352801b5070030001c40d41d00680b2200000e205082c40c3d125007641c50074240c158a10701c420f0101d6038600301c40c03905400c00c01040c0115130380c5a860f0310290110301c10384d100e51400029500800084409030307041101c100083d101001d0a2681510120007140700c03802c0c00703000035244270074409558046a100f1000512180d50103003040c1102d00c00300d0740103440c2d80c0008140324031407810400f204046a1003050028881d0700c0041c00e0881419204101c3c90040c035030000c47c19005000ca101038002c400d042c0308510381c0e203505480542d648034224100b49084401581203c2100e03160507608009842221007520240c07419801400c0d42d80d107505200c2801480c580500320441c090204000092000500070900c10554116200c0d11030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 843264217 1250 843262967 843262969
    0x1e0c170c01291c050c04110c010c0302160204110f0f07060e030913020a14130602060c090f060a0306091103040b1810090c09090c150203040f032409080414 68
    0x41110010142c0c000c89041a0301c0364015040b00900c3c0d110b8016810b6580024032880442d095449204100c05503800000e07048510200910640780d604080303240440c00e107940310b4541c000500c00d012020388200d1b00d072001d148001f000c44084480720344122a219580c0c40e420042607000b900041130030b813115403401c00c600136200e4020044528040e00109040d115520860b8840001d40204800c84d00b042034034405400b5081841000386410004030b00c01d0840e291600300e0080c038280d002000018950814040000c103034452040c0c80384210412900a030b10340140110841c0145010390200460300d042c00582100045684002c6000d14043c0540780059500c00038186944444800200821307030284c01c0b03560139040c40b6840440094419a203a00d240c554070310700d10041da140c1c0c060903640041e0021007040356174544159403c0120490014506017490480101120079051001070000c07211400c4000102d40b1800c0d07002c101c901c180e00c007040140030504003000b0035045402000c2c2c0c0a40564a0300200e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 843265467 1250 843264217 843264281
    0xd21030b01091403030409050c0c010e06150a0b1e0c01020712090608040c180b06030c13080a03020d0806040605040221060427020105130602010e06071e0c170c01 71
    0xf00d100c080d0065140030301e881d4410340140001842000201c074144032809980e0340a005840844502c2001031509080403002210070310090302032180301d804000c104011504094080d03130b48152000340510030440d10344a0604407840703590074641d002d500c00a030a0b410003c05609020031203002d5695201e6040d01c40310261202c02098a0240c4114100d000c10003559420780c04101309100c1070075000c54a5807040010078a290000c1d9294210701c50040f0308401a003580211440040510320f00400725541c2c1510081d4031403070300e600d9020400030f04d42d0000760301b902c603038010303038000c10010f80219030748c00b030810310385020206030803840c0700d441d841d003022074a9860603010381c02c1c02030164542c2d1142140c41078403012941c41c0509003281800010f10480c0700004001d041007008000d560000701d0340050781c038009414420000c0908040c44a10418101d402000e0701051038a01840d0400c0c1c2c4403207106003005a90b6405007000d900d4030b00000501c40c0700c83c00c41900074101184407016100c8203840000d0030404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 843266717 1250 843265467 843265499
    0x50705030f04020f150d0603050606030a08071203090804060f110f0304050d1106030c04030b07080f04020409021810261507120c0f08060307080c0d21030b0109 70
    0xc0840c00305001d032600c400d0b00c0840a04c000c09000402d03110310405075454215040c401c205540d940d9042043c86028000d8660150048014100c000d11903515803d2600a40300081c21031207250000213070882c000da024400ca0768002440984946d41c03010003c12220075840f511000030450025618540c0d80024026024600d09016608141c103000600c0b2805002210603901c01c101c0312404441e586584004500804825030b1050b642ca0540c10402440100600207400b048401000c00002c601600d0071541c1080d4111b802003107001170b134000501d18031400f08251240300c4242050020040130300f075640d8200c0305c2d003500e11201d0080c4142c0c110700a402110742c40d08107400040010a501708ac610010340e2090150510300030003428640828121203403016a0008035038200404102030790008284c5900100440042c04400d0500c0d0792641c550104584c030714012514a00c40c20200080307456502c024a10a15005039210108600103012341101e0f410310780402c40000010400740305c40b00a1513 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 843267967 1250 843266717 843266731
    0x80c12071a060306190b0910030c12080306131b2606030d050c100e010609050609090a02012f06010e09070b040b07242c121803060112050105070503 65
    0x40300750b50b03907258401070071708286441001050f952418141260741e10b4402c580204100074560718810f042d4900b0043c03c081d0303504402e40c00c241910b006800950b07071104072130b400442601d40c030650211074511034000d00000c52660444d07040d140343c1006442e5100b03000d000c010060003080e5a0078400081c0d91088150300340d810380c0d050f400c46408a000316001e203008100301901c0b50100c0321418445040002200d9403c5041c0d0050b03511941c08200720a03490040700d402110031206608107041c040c40b555641c5620000090500125143d40418000300540e00b80902042014070111801c28000c080c0e182c0c24240140032440203044042402c0b0500080d6120559542c0826145401e0810716026026040100f040782c52408c5c1d210700b40780d00c2c0324640f0103400c0c4501110700814420a02c10158880e0b03a030b605181503400c1588100183d00203400217a44c0700104030a040c5550f201080c1c00003140340e001020200f41c05108103800042c61000781081c7c990700c1d5000340000c01c16500c940800321010303c0256142 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 843269217 1250 843267967 843267973
    0x405060a1212180603021908070f03050c13080a06051e07030902030307020a0305010213090b060405010e0a03050d120c020105040f03210e03070c0905040b070c080c12071a0603 77
    0x20740002d10a4544020040240d041520090155140000100700340e5089500003a4010451380c0800c0341e10119014a191305061100b80d9241c541e034011b2406580100340030401d519040402e40790801d4108848820481c0d8007070f101c5260303c65138000c0d07442c458004201c0d0380a00c6c0100181c071501e030754001200c180010120380f21294489080c1140540914501660b15010422070240103942c0c4020f190021032140c0c002503211288151501d602c0031075940140d40c561700b414048440c43d9607a0040b1010741d0404d082c012401c0b03a9000200710207400540008229108501500800c01e800c0700110039407106c80d03802841004030800c01282030703507401c1c1c0d0000c20784a00c46100c0300c0000e024200c0085150600c02078858481001000e40c0251a400702c2208241c3e000001c10a041c409042c650b03a000d072541102c1405242416526802e4501c0300810000400c0302015101081000d00012a0320b4a0b00f0a42124080b14a0f81c510258650003c0e00480d440c0c51078031010f142c41020112041c0c4540360040207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 843270467 1250 843269217 843269249
    0x3181806060c030405090a050105030c1f030e19050a0203100212070516050a0b150102070b16020604030c0308031009180b130501090803010e01170d1809050403030b0405060a 76
    0x921a4a41002c0003100c0940001d102c04601134440b016580c2c410005c6010204c0d10394949018542400241004a40952032200010701c1d400c8000d40081001c191a00d000181c4c2c000c83d4040e03900740484d20a0061100c401c62030800c060101c000745901074580210160781c184511603051104038429640f20714074101034240001c4800d4013078406040010202d100300107041c030150b6942814000741010494400445205000312250080c00607000b2910a00003003000740d083c015a03007a9030040481610303908a421070755804540303806060794003c40d13002c92110a55922450b08000c607030022551888170f428401c0c0c00107810451750044c038002003044100c13080140000d44501800002c000e110f5000340d4544582100014401d105141c00c15005003042501e0b5410141e480c240c1e018181c3c480700d640b81840c3c05e9400e41c050701040c0344074601d07103500702100d0404c001e51003003010b20400c0d401014400c0c60300b1300304424180c1540118130080b4007190b08118998900042265040b8240110801c864001d01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 843271717 1250 843270467 843270469
    0x5060301030c03020415031e031202120a09020109080609011a101209020f0a090614060c0d080406061523040f05010503090c100f08091b01050706061703181806 70
    0x3100c040a00d1410180108031505c7e41c898080c1d15013030640fa0041080d520380030700141988440b0844242810000c107600e844070180d4829030210000e0119008641c0c0ca185c5101168010401c082c0108a0348055600c3c62070700c2c800351f90090444110760a00001040010300c1549450581104440c815440355144150503201410050041e040b04070b800c013410410034041035541d00c01d0303403008000b00c40c000714401e400d001c0c6050034942c070512014003d00c0f0511200500000c082540307401d42c4000e15002c07a05603102e0516001814036607000c901c3d05102031510340d80c545c0d400010064031103c08401d030010603000781c030100e10502c07c84c0304030480205452030034010f0b0b6200b0740055070428000004c881c0c8034000c040c00100c078040310001400224200c1500c2041950b0890407881d407001d010b001800741c41d4030506140c2d04200c100c203001c40c1000b200280410822169a00880181c05006076156441c4401c1c000607541c1d074410400e201e909000103c0740304161a1141c08002c013000d10130080501038550030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 843272967 1250 843271717 843271721
    0xf0a080a0e030d020901090e0405191104090c0510110601090c181e080706080604090204020c071e0801060807061404080303100f080303070c020f0409140a06050105060301030c030204 80
    0x16051500a03500e034074010082100400c09882483c040110060340d50724940005000c803407059000140c1c03070b52800300f00000f14401140079a50207114451500f10001c003480c1020300b2900c400101ca5001307140031001000c1c0a151100d40d4140c071003c2e40d014200036015003090300c901e48450020505039005c5401440f040103da00010000c51150418000c426015100c030301d914255600b1600d40350400c520301c1142c0381c4030100c4020040103102d000c2c003036403030034407000605100f0010003007030145131281c012008544a41d411901e04500140540b6203003078035510110300c0301d403410724503090b14800501c020403042d1062169104443c0700c88020300d501740c5801c03401e980040001211a00c55071052000145852040c00210301c1401c41ca242500c0103410308a24a0102885403c500030551040c810071190700c0e040380220301c10503011554440303071070100c1002401410746c200c40103212081e4400115414100001c1515916200700002c0c0310f26070700c9030140700302400700340b00240c01081c07850010005802e0603 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 843274217 1250 843272967 843272971
    0x10e1b040c05160809040f3e07050f070501050708090f0d0615090b0a08071404020417060105030d05040302100809120d05100e07090e09161d0c09010504030809180f070305010b0f0a08 80
    0x4083c1281002c003923040700e4003d40c000d0340c03080d200354002404101c1310b034100b444144003070002400e006041803090340302c00c6c069016550032640a41700d080070600190761040010f609159208005003d8140103c1d0580c204403401c0c4640c10415042c407813140454076142c0138000c2070300d080c08000c1004503d0400000410000c4110194000b542040085030300c0140f04081d6210800c503a0060940e5407404007072515258040c0568010088103010500042e5141103100c0d246080a203070084880d183d245089042c0b092105200700043e8001903044200d0030704e0340119206008004030070b080c1c9980c43d80c1c1c0380c00307030b0100315403600004024107000d006400001803900d0704510b41c0006c580c01c20b40301300c07a14441c003141c94108450400075600c5140c06011103211981d0b00000c034519060814500f400064007d000d9800000c004400104040e001625005940d09500051480d800e20604181140340c0d00010207407505800a0308040001c50b00b0401d500841c1c8454004505d03003483c10341c410800b11068000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 843275467 1250 843274217 843274301
    0xa0201211b08091c23030106020114060324040f0c0e33040e0a05160510030606021207031b0308010602010e1b040c05160809040f 57
    0x203089012034400440388620907407841540c1104a1030305101c1405002010010800340041c0c4c00920b000402c03801c10b80c0342010b800040e00f0018896004003942c6502c84110350511080044d01200010f5080e42c150040040d602140070010b00035240c0b5014140c489103c08843c030711040801002d002545955035895a10602464a2250883c4640d5400c0c1d408202c1d80e010f03ea80c01800c1c014441070401d854858403980142003166180301146044500591003c0b00c0350b144504c0c1d8900080c041a5001e100d0070251580c00002c1d01d8518440524420300521203010702c034010032090b0040358000c3d0191240341e00341d55640c0c00405090204402d882d61540c04100100e00300401c00b401107449000108000c8103651082d25082c90641c10f080c402421203604c0d00c8210001d81c8000191406003224404640b81441d0946d400708070900648020764561083c10320b860b090982440252003030080c85800b40128480840301030281c0316400203420203850115940e407515603241020f8005489500584842c42c82c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 843276717 1250 843275467 843275507
    0x2134050105091309060501050907020102090f060307110f03030702070501211a0d21030618090501020c160801050606180d0201111002030103120804030507080c0703080f070308010f080a0201 83
    0x1403241c3c804001d07525610700031100360307485100510072071501c0306440d60721024500c021801c0c0040b1500140001151100e202c0c080e840c0040412003080c032039099084681344d41000c9860003000755504950342c2d4001c48044005002d40d11380415a580308801c90300a1010a818034204200f0142e40e0a000300065440c00102c0e50065186090315240d2088104050b400340000b00c80c01d4035444024140407400c0700040f0101407605000b07028800c0d002014190071200c200b400200f5940c1490414028850000314030040d20410942c4060345861954080c1910041c00080c41152150b00c140b0059009041c00c3c0a014042e8066444c8141424071074940741600500d030840448650302115030415140750741080c200341c0c0000052092101c940c41130b005580c0c2500c0c10001d41c0c54242c50040c00f40c0102800148140e02c001000e0307050700400c100322009141c202c12555078480350482070800d16804400214007040100c3c0c000101050b1600280f0112124140034001e10904c039070044410020782400680d04070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 843277967 1250 843276717 843276739
    0x10b1228060305030a0801140a1806031a1603020406080c0a1e03020702030f06010803160c0e010e09100605030709022d03040201120c0c020f213405010509 68
    0x40254090071008600402c00341d80d440485900041c00741505811201440880741c5030300c410742d2070743e003101000c50300c2400000350304000e4407507002c1c0a0042c0b030340090507481416082d01c12400101141c0340c0506070a01d0400464015540e0980580c000c1b84117241c046001800000c0760040d05400130113141646150012024015102c5031301c04504e0701d031840c030004c1e60111700c10045050421410701c04c000c2d400c00a11803981350601c410380d03c1c858504090312445100041c81c2c1003102040003030300030702255140107100350384508202c2d910160031140d1030351500c2104a96880003581c1e1141d201a5a00070f0003901d1003504004400c006544110348407540ca441d0785445131910340910012125186c510f81c0046d07a00d0405000044c10f013503080303001401c8540351240406085407c6040005540d0341540e070500d03d0900c00740040c0f80c00d5140c90849031100310b1030141200e003e4000c610f0700d0364140f51005030810704042d541c0003c440c4900d818000101134aa00d030511066005901600c0c00100041204201d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 843279217 1250 843277967 843278041
    0x20108040327080d02210711150309061e06030703020103050712021803010c17010905151807020708030703090b2506050103020f01110c01210212040506010b12 70
    0x2d014650700c258100c0e08003a01241c15258184102c01d40707100f00d80000c5850061010a841c803520680c5030090202d0407842c00c50030161038080c0340861980c1c640440c6526460402d40b25070701c0321000c03104800f4a04400d6441001c008240001e58000c034070140040c8a01c504660054004020240030403050051141d0044980c18144c00205001404a18182c21200d02282418295440c4801281c28800210700802c1c0505110341710504480c5141c1c130102c2d40d0785800e01101d5001c0c00d000301d401d40040000b64101c6140030381c46200360064000391300b10741013542e81d00d903019141d0185100042c0050b00e500003c019150060b80134020100c15205010700c1c0120240d9803070980c10111004554903502e440040054ac981242900782e031032420308000c4005412044070355114240762510038180102c0c200c860a818410112120040140f604110b6551240174102c1d02c403100115012507042c410b900002c50020002016034800e00d224147c2c1c0641521204000c1403042c41c42d40c9216107140300d2883c500c1c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 843280467 1250 843279217 843279287
    0x50109090c021b010306121401150e04060207060f11030609010e130818101e03060b0d1802060c01021810200c09040b06090601020c030303071202070209090309010f0c0201080403 78
    0x652051080f4105904411400c90a461310a440907030949032b0750100704000000f081c8455805640490010b903100d91600c0c002c001455003100d600162071924007410710091030030300113600401084a011641ea81c0c0d076140d55001300300840f2140d403858000c49050b400640c0c0d503405003103104002400c510203400004003203010355944a140300001051b0080c1c641380409403201da000350036003d14051000710b04021840100744540c2c5070300021940d807038820100b40082081d100100f0b03a8018012996200d540d002140070350840034450441405c1c1c035012000920300040e442c0c140d12640c0d2240402980c044401144090015005c05158044d002c5904082d59501021a10540c13181c140607c0900b8840180092184001d00c1e0a041d9400480080b02c240d60020540b07034000b100e4603140011744500401c80010380900342c0700070b4024901c041404440b550104c09443c100000f80e0326011207408013441120410514980039010490400110340464440d50211203c0110481800c842d80600800c402c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 843281717 1250 843280467 843280499
    0x10020f04120602030f09070608010b031e0a061404060317130305010903020a03030e0609120f13140103230103020607021f020105011e0303080105040509071d01050109090c021b010306 80
    0x1550550001c100005e132899400243c0d0001e80610050500908101c0094640941809040c58204011001840162001080248941108075006154140f084404d0040c1240b4042d0100310017a0800742d440c20b0400d0301c00c40040743e0708000f01d074009006081391405251300280490074004015800400414001d02900c41598401c0d402031010075a5420010201d0300103076800c182c039801c48002e11812140006004050381d8060005968441c1c072025280003520907041d50001d40c01c492030700003558001d0880740c60a0810280c82c00c0c4103c0041d62445004c00074100300201d081001070700140050300308030029124080c4060601d12100203a44042007541544c01c00c00c1d80141e440f13070010300c090094161004940c541c02554280d140c3c0c110303940602041c805014950280d982c0342c00080409800f041403200500c00c4500e110044907480c091042c00714024098107000c18820040010324071801e11440c03131140c4031035010386030804150400c0001d0700302135941e40341019201d4401003002c80360b000003c0c17 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 843282967 1250 843281717 843281723
    0x6070807051b040506010503071d0102070f27090507060804050a0b1f05010206090d210c11070605040605070b0604110313020f041a060c0a0602030c0a020f0f10020f0412 74
    0x111004048904020980e40004c00a0b81040010701c10710420f1600a0540000f68241401048403407211000407464036103a640302100c10f014ec10400610003441d040b0510118241c131507110708080c1c9030ba618009507100d0680c001c1a40d40300d518100401d80c4103400598000380b04000740c40c28228182c44004e400c00c001d95407200742e0184511925888a020382e540700080400780064034041c50321041881e2506242c0c40b8800c1030104d166160040b8910462200c1d8080c070501800304a080c140980003401a1415103045800744501032010440c180900265011500175a603050f00e0014180e170350307a1a0ba1809050150816141c050380c1c030540f0003450240d442400ca02d601307540c0020741e0780100f1485005044441c1d020f6031030210b00d0b2031807401e12803110701c140400f9500aa9902004801c06140c40ba811102810707007031001c414031440d40c1c008002082c4114440d4211070301c03260a4599540c07125404191100b10380d01a00d070700c510280c0250040c000c141441d100d9103003015920310801e04054294070f411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 843284217 1250 843282967 843283003
    0x1020a030e15060a120620070506070804020303032212020d030f02040305060105102c091e0f070903050610050a1203020606130b2806021b0607080705 66
    0x180c140e081003240070081c04451030b15030342c0c203014000c60807002c21801541030600716030440b0014401c0542014840700c80b58007007000300418007000c201c0d241c0c10501c02101c07903000b40f60100d00c5181c420600540600d400502541c070315140c1c406a2100040d03540303a1003c5042d4032002c840082040b00070420904151034019101082500380e00904580704080829045441032000f071001ca00d002030014190340702591210520085d018055070151054031180c00e00b0000c40b6507440860391000c0741e884030740b40269010010ba884172004040031103200400d100c0301402480014212240c00d404441e0081c609040c5000d0032a01d9450300350910200721051404000111010003140c10310190b004000d144001c4406845078942e58029181d038800740030305114513011603450b00b80005c503610150034414001c1c10300c001004603600a80e10020000c4200c000301c88484000a4a2070001c41d442e004042d12040c8100d1101100741003040980240c982039840c10070a00203800090020010703120038021004403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 843285467 1250 843284217 843284231
    0xc010807030e190b09070b220b0708130b0c060a0c0e040f0b09091606080403260610020d0903231501090e0c1302210c090906030a08040501051b01020a03 67
    0x1003184c1108000d0100712140d8081c001c100000f21224007a81c0d110386422800c1390301c03000003c0c07890510282036080341041010000d407070010040500000c0041110300300041c0b19450b40c1c3d1451445170300803030100c1610340e080303038002807500c0c4c0065200c0100b100a50a011802d101c0040105044074082c0f801c840c400e9a231013401c400705103420022107a00c40d10f40380080600c1c14507208101c49545040c4180130a100841011508050107000c034000c01e0601c900c41410149403540105444d400d060300c005018000001500650b03d10224620180d14403640303401101d50310310399464003004054243d41c1d504015205240c96542c030144111500092082d440700c50380e5040c5810481200c2c1d00e811001c6555102d20b020001a4444090141c0d906e0303001800140c441014002d400e24413055040d00d04882110309040007a06c142c0070703003d45581d00e0b0079103805943e5500c000500d0b40e90b00380081e002d4803298090104010750340c442d80c01850011018038100040c100c1a20040c0e003a0b070080581100401d8407140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 843286717 1250 843285467 843285473
    0x2070306023009120a1b320d0509031204060f12050702061302030a14011a04050103050304030212070e01060e01080a0209210a020316090506060c0c010807030e19 71
    0x16284585000d8a40c030704042c10a444083d540d03090b544001000301c00041221701c1414000c1e000c0114680b9402100c000c058503e03d403211a021829182c002c01002d10412104400c290310550003000300d0389001080440e0350385605a0f80d07608101a0151305125030b131000c0e0360180441000d403009111a4a60014840c43c0c1e4101500b81c806c00c0b0842030401d85003508100c1503d50018031150012181920f80b80e2960031800401e003418207250001e003514204180f6100d101c5815480740f849510460202c1003400000b00410007620420f210140c590341c0144003d1000d4a00118039409c5510000100c0c0c0905a07180034004008400340d000002041103540d2000440d41c010381519070100307031200e0441c80e00a103400090f0040c000c80c40c0c1c104284081c0c1030400c3d403c0c0000c0060030480c03900101111803850b94542001c0113444039008220041e1b00300800314103181403030800e031455442150040d00c14600301c03600441d0056801030071f00041503207402c5070044441c0c042c0601b51058020700038400c4170309000c0c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 843287967 1250 843286717 843286777
    0x13020f040506191e020c04050705282a170c0d0207030605061c1506090e0f07080601050105030c1614160611070b1803060907090b0910150207030602 65
    0x30203405070240541c2c41c0c4c04610342c0d000c902850075020840700000d05480c0c1603421240c43c040c031441a83c20b14140c039800070541c44500d44150400100b42d546100201201e1221015110440c2c1409807a94200d5820740000f00e0044010f5014400030a2850034504070152492800103131a68000c05070304049000d00a0084e980282580f004007921002642e0040503013031010040141000340a107119800c40c22240e8606401c604000d01c801c2d8010303c521000b55490903180c002c030001d000c1883c403d075407000882400c082034560413030304161600c1d41107680c0c005603156654481d90620202e44003410442d8000b4070301c0680f9681d001ca11070010f01100700035100c0c42c0d6040c5071917080b8005005926201528000e8009076880c00da50502d03085640700c14030307104a90503031062102450b038540186401c00072402d00c00105002180c0d2020001d00c40c44c078882050100041c02944c4190040030354000520000220800341d00543c9010320480786095036a032100c0040381c02003005020f405213040e4000042030198 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 843289217 1250 843287967 843287987
    0x3060605060f03010b0703030b10030e0c0306100b0d18060906230a020d0902090f04051b0105030105040914070e0604060b040b0d05131407030b130213020f04050619 72
    0x58401c1071070007030003035060032a5000c148602c00d9148000600581094840e410030302050070b020b410311500c100120000b0f0040c048038422001700c5c0c4980a8400d183d480d0000d40c0e54090390951400820060a00e03e081c58503078810946010302e1034980c0d010301910703003806061100c41805072000003288069442c0200030b60b0540040c500004208600c6070101000700007005070402d200d05401661607904124110280441c10000f030b500410f104200003461484405280c0314503c9403058600c0100300e41d10403c0c0c0390080b0340b183d500081301440140083d040c95488a43c400340900b005400040e0702c040394074507000c1160010150042841c0911001d414030780240030142158204103401c141c2040301a0040d400349108550b0000e417070f80081030851010b0182c2c0c8440f150050b0505192032002d80f00c15940305003920044840550560000c0c991041c62450f502600d5802001c0c20f08000016010308003a410503400c80c2c00c188401c00c0700041c195124401000c0401c0e241c414980240d84e6540068030b80000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 843290467 1250 843289217 843289219
    0x1b13030f03110d031a0d0c061809140601020c0102031e0307030f050a090c050f13090602042111010813020918030d1d01060f120510090602130b0c100b2803060605 71
    0x946c1d0350140000c0c00411107905032001c600d00030030440707070384410950700700ba17254844c0200514111600da95005508203252150704c00307808a49240020707000480c2d80340b14000d1000b059511391071048a011881c07000654010009140104010f064548040125a030680b0469100340e9549070300020441c0d40e84440d0000c08044510700d03016800480070805900501e0b18040d0500d0b5103234900400c00c50640e041e41c01600044d283d8100b00da0704091030409200b0340c030704107072186800c0703030140c0c85c0c2580310b501503030321903140d284500d01d2145142c0c1c20f00c00291805001c150118101e01c80d00020640c0c10400742907028003044002ca0075101d414a03401061001a00c4103500740d042074020300003c004401440f0450ba15182900d5610481c2e0900d1420000d400412000c401e00300700d842000d0003420380141041c052002c141c9007031280d560480400c03034440d10a040b019074010340e10010241600d54486c5003448000707840d4003081011104120318031802d01c00661000070311080d086c0b060101c03500c134074005804 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 843291717 1250 843290467 843290479
    0x40f1e0b070f05160c0317040f050a0f03060506241201080106120201140d050f091020130506040b1b01050c090f040f050a051b13030f03110d031a 64
    0x5100500d036105043e0110910040c0000703801c20016807038545e8005541001c85040040d01900c44114950f00c0785c441c0781200a2460408101d5241c20070203401221400b0240303180c1c603440c4d82d442d140900001040940d201184400384400d140c0c1500030545801028501141e17200120100c0d0104140c0c1a04010300742c2e13261400500c54040100304005070507409080c44078102c4008010000c1622600300c8040c811400d000502810040b41b80c151030241d442c40051750740346c00e00181d80c941150240c8030500724514540542c80071090000303000380001511410442005500e0310003055a96005a03c0300700b12040001c1c03680c0c4040900c0003000ba030080388038000c0c401418105107200340b038000d4031046407069000d041b642c0455a540d03440905451101c40c020301440c40e201e00c0000091604a460f071a20450031000e9980080c00e14040380c0a5a5501001103010380c25a203400c1540311040ea021820300031048007812151104000c1c1812000e00755901003003402440c0c0004891501e000d2855014032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 843292967 1250 843291717 843291737
    0x6040f02091f021e070b070f050f06010f0902070201081807091b030501060c0c0504020f190f03060b09011403090a02090c07051615210213080d09030f0605040f1e0b07 73
    0x41a200d0031200d13517816461f00da1803a4141040b158015001c010b101e07106540800171403040200d9202e04a480c0c41d14990070990350754260100364424090001d00242d448000185401f00d0b648000c0e0010404008030f40056440b241c038002100c1d920b04101c1c003607207800484011001da240c0100350141a16250903450215681c1d15801694414040c0c2d070301c00c1d0340201d944c1c00c0002d1440c051380c86031410010041405100214060441c01c2d20201d580002400c0c280d02144801000c021500039400603134401e185150882048a0140c02c040c0c44d45001d4000c1608210140c3c1c6c486010a01540341d40e001c0036500d140d9803510601c0c0c480b42c0e103c0d1006040b007001003007002c86004110300031507a006040802e0100c5001040308404030400c403807003507501e1010410f040100c0340098100240c503c29003c4510340c071081c00098901503a1440010409040d50800d0350000364030380c0015401500c950100030071507a055036224982c500e800703a40e100210209059105004a00b42410340010050800c18025 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 843294217 1250 843292967 843293023
    0x41e0602072d080304031e0c0c14010228050102130e060a050105030a05040f02131d070f030f060b0406170c220903090b0309031209011406040f02091f02 67
    0x41d0086400243c8043c501000180505003c1c120100a410700390343c032801d0038031030140050722141c000e0105071102902c0f0f580100300191401c0c280d505001050300140344e00c40704140313502c011101c90f9041081d4010948070420004a0034006400200a01c3e400c6080c1c4905001d5510340e00c00c4010109803080094010800080c0d0700b1004590b0003040d8010301090558542c1031403907222007545d00c002d40101b14000544005045a44154a030031010a40440c140c07003980503080c3d0b42d220380d00030214020010141000040c24158400c88040d224440c0400c121000900080844040d42e01c4003144500e030001c1c0b104d00510030301441d00322003070450385400350305641403c100700e404504040d94000c5070746014100906006050a000514205d12110b0780c03480c140a001e5260742020300345044229401c80803d400100c107015404010a0600c1074945540d501c00411028041508484050907070030460303400140c40740e1490090041610340025500d00c500704c030089c9084160080310496030340c0202400c3c21 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 843295467 1250 843294217 843294293
    0x30c020d1d010302030624270303030a020c2b0e01031a06030a020f0309010b030705030a0f030807140a020c0f0406030818010203090d0303050f100305060f041e060207 73
    0xc5100d083c60010303200d41e54203021a52078141c00000070801c0560f001000141c1140380002c051a40d07900c0d107410a003190301c0402116070040500c1445c7e050300107000140002d501c6901904501e803114044880040010f0483e100c00e810b550f42c1c4020f00090701388039022841d0000000300d440c0c4028030b41040021401d0f00802111030085170181d1190b01d0010204030701540c40d8050300d501740610075403681e40381002901e080c020440001d1060190044180004143c940451540f6401d5000000e000d80520b46690480d0403102c0100070750180509440002c02620030b00c000b038161240207400400300b01d1410400c012040c0b480841c058890341c2007032001e2001400d140141c1c1c000d62208501c00c3c0c140111000140c6c06c2d4040c4c0303000350344c00820501018041c9a4140c00550103200600c06030200f90302c3e0440c0034a00c0729601d003c00b0702b09030f11160200301c52491504540768410f0040d10b50a9010844030b44048007108940f038166081d03600440c0c404148054000c0700c00769501c0601d00616526101050004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 843296717 1250 843295467 843295517
    0x18090606100e1909050a06061209241a03030a170408070803040c2912040510050c040905160906080c0c0102030c0301171518030408030a030c020d 64
    0x4058600048011a118003070402280403220040a48000e0000c3c02c1100e444075400344510014a400c00c0b0101d000e410140c442e802c2030300c01c60b82e6882e10015a20303100b94090203511100b200d4280c0d00221013560741c04024035821001c01142008192828034161902a00307828854561003600200511161aa0032512141c501c41c00c0c2c0028840c00c0d40c80c0d007003481c0d0f140503156000d094408001b04010030000c6402142082d1404040e100059004a6038000c13891388101c02c2070100c0403000c100c400400d00020320350650091003481100c003900121510402968003c1e1910b2260000104e4188802c03020b40c042c4562004803142d101407048a4140010030011880c1b052400344a16007011840d207100700e10444000000c400d009540e139080091010b4459030091056206110f441980d203580d10401145100354003082079245500c540720881c08000386914001e4502040c4810000001c911000340054030003071060f620005140091000b01074205001480c0a000700460a4100300041d451016640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 843297967 1250 843296717 843296719
    0x160306050616150615020607020a0c03060f092a0803070218090f01090c0504060e040f060e0f0a060c080903040602030a0f27090b1206060d020d0f0c0518090606 70
    0x1001040c041c148000b00002d003142c3c0f4101d0324282500440c00c0c500c84a03e010356141d9503407c4481d10b584030101282c4803903807110300a0117100b00301800c20200380250003400382401c144034000391944d410341e1085212584009007040e0f61100c540d240d040f605800c8080070041c00b8640c040c42ca40300040d40081d540030912840300e8410041c1c040840c1e4040307401c00032303401007412110080003400b09078200352080c2c11951181c01e12075401d002c5c0108020b07000d40c4000307010b1903005080b19000d401580c0e803e80544480c071020303d5584a40c8010400100040005c084054005c8400040510780c100d002040c0307050080c10130a040d4400c00c410050203600004481d103c00c141d00d00108012010344040315090b02c5440003034500c50711210a0b55086440400350404c440c80ba51007006403101d03030024031110555010389420f003a0006000a24642010319141403a144003c0c5110282d18165550000004111100399000a200c0b4803c0c0010b0030301d80314080015107121640c10032880c01c8132600380e40788401008a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 843299217 1250 843297967 843297997
    0x9130b0a0546060203030907050114120c160809120604080d0b1302040810051602121b0d0203030f0708040b04110a08010e0f01110309030304020913020d0602031603060506 75
    0x480c0c0c0001c1500c12950b196425000041400c2d54801009541c0d0700b0554490301a4081d100c0000707030a60044a02100a4522021140c180002d610710140c1c51341004010070164801000342030710200e121003000e203159100f0181c40351942d0b941014000052880034004020368066014480130901000c00c0e04d11007030240b5008151200f080c0045103010348030030300500f48540041408a07a100000c60381c0c400303000c084103040000755503c0800e140f030300026080490150300201660070181e42118000d01050000202c1b4414296903081c20514140a24075601300503040402401541889881c3c904d40121107032800c2c11550400e902d450b0000717000a00020008081591411702c940c42d46106500201403079402080907540c55690161203885262101d00a94a00441010110122000c0d40c0c0a0b01c400e00096095940300d07428010b08510162820340b0a0003c9404580148c2c0c0391200c003400d032849150090b0710390420000d01d494030703414800e8041c14541044c0c0d050000c0c0d1215400c1e940320b00c248490b5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 843300467 1250 843299217 843299299
    0x9061608091c0308090a0b0a0e0c0a0611060106030b03100504050a0c06020106051203030f01141c0c050f0607030c02010323010b0301030228120809130b0a05 69
    0x20a0305100e0090700e940c200e20314000039600b920300c50041428107800303516000d40f640e07030b48507610762100040315008101038617a03408a09004440e80c44658050754030740440b0780e01019400001e2444025510020000340c0c0f03620b042e1492071052140600501103803d090003280112000a41c0320040d6100b2203407840e0741c803030001e0140102013101d581a960005c102c1401141c540360000d010304190300900d8061850011080003640c0000116445248007844801c91a401e190901140030755683d441d99120410481d4441c0600480c003042d144607116143302c0e2403c034030342414048030b450b501407014402c400500020010a4100c00d00d07140d03003903091070006003900101e01c1c0d08040742103010902c1c414103105c200101c0c201103008002e43c1a00d0003102c0030385001300a4210346c0a260b100c50142040407202c2d8008005a01582c0141c0d021a031040307029030b09242d0054080b80c1d1650600c0803020420707440c1e00c3d00c5400c900301402d00d54043d02007550240d0240314401401002540c11412624801c0030310b81c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 843301717 1250 843300467 843300473
    0xf090207021507060b040612020a0e2805071d010206040f02060412060f1104050a06112b0905010e101206050312030709090606140c010e190b0a02090616 67
    0x200d020320250a82e003a454507903101c1d0030a0401800312084990041c3d28128002c1200c0441740000d850550b802025400c2c4241010311210500d0000751414850310000140c002d42c4180130940e45442240a0400041c5864034440041048568848404900d007a203684448141d90101e081940650008000c0080c61020720200b00300344110390020101c0c60510361201c08124490f00304001c20308151005005072110301002d8444d80c8200c2c400c050740701140d0101080540d004001c00c0800e03042000c15201e4440c8141c00ba001e1020780d50b9491300640c8400c00050480a40205015000e04000c1c60902c000040c50000b0401450104601c40c0030b218102c41c1940d514291600a00301500340513066906070900b410348002c180e0800d0f21500049052070b030010552111510034801159684d40d550140e80c020300200c10340741e40c0202107129040d501d40325194002e0008200d2815402c01411100c00b4041c0d00c1d0400c0c1c1d180780d1001e803000910340d00421050b03180b580c0784402e5a580340c0420f100340188e061949 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 843302967 1250 843301717 843301729
    0x1080412050c12041706010f050d02090712090b04050609120301090e070503072907150218040e0f0d0912120c0f030504143f0a0c1a040f09020702 64
    0xa041c190f0f6140002a010880e0011150400403501302802100c1480c1d0f00c80712000381350480c500035681c00000c00da84900243c0b0382032411680003826803e2900d010003031652103005540c50510195031000483e400c2c402000801c2107040c1d84900d44001070300c0b0140711036003950000d210611034840400d4403029103e00d024402d21060b0003d050060071181c0031680ca0b07200326440509014070f104a941c0000241c3d0802c0b03050000c03243d8541d80918858280044041c2360802508106590b42d1221000a4500942d4072188a10708820483e00c008103034414240c2c804030320f4604c480342110104000706004008803500300d5086025690311042180c06c0008405080390400720611003d0810100043c0078001c0c9500b140c01030040e55690b54450226883d600300388a44e80d07240b031001000c2e50441b03080a031408950300c075200e041140461001e1070841c00542e40079151110102d01550000c00c0d05100b001791b01260003102c2070102960320224102807400c000012042903e1048204150300001d11000715503440c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 843304217 1250 843302967 843302983
    0x90504110904140f1006270b0c0a06050603070f210804140117010e04030804061d0c1008100608040507050901090209010206060f060d090c170a0b0601080412050c 71
    0x16204121081400d101450300c10004c2d510324050038113200104000d04083e0840300c060720142c0c0c444209890074014400c001002880005824294500000c50032030305c000000c0081c0c43c2000010040384003182402000c403040588028400c0e404044104560480c02032000e0844c0d02003119041403094554034490008007000c00100381c0f000c00903010400303c071001d540354513144003a1394040b800914180581201e96080c091114060f1810f00080c2c00070f03204100b00c42d03011f0702c624004101090340ba0480740b80946c210a03000320365004001c003001503003803c03000407070302d00d2251810000d1400d025420325a840c11030300400d010020090001014820104102c100a00b000382c19404190780d120072400080d08071244450040c003582c00812010b15003800034051070340b00100300502c0d20404900310b900401241108944c001d82e603c000086201e80c881205400c111a0405000a02800d00e00185a10b0008006030b040c01080402d0102240488106070740340383c070f10304040d030303a440802d50810720308004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 843305467 1250 843304217 843304219
    0xa0302041a1918020304080301090203041406090705240910091a0304060c020d050d150b0301030f1202073f12020d230307200312010504020702010905041109 69
    0x1000d032100304000503080c2c0b40c0c400c40711100920066000c5100600040c2d00c01541c001d01010703030600050081050650085801902c1180448042c0210581e40e074200030041702c030b121480d0031480040200f802e02c2c030040091490328001c0c030340101d00b48505500850040c2100305026202c4900c03002c405a00841d180c20162032411480e006040405102050355401210221800c904000503100b40030b0002860080580741a1202c2c0d0400d0b099202d510018480c00340c7c80322030854601c40c0058200001ca008502a41c020000c0d14a04403840c01d00d00d0311940d00403030320304c110340c4000703010400d0002403140587c10301c0350100d804210f01c001400790007035202407920070800704045880d44070400040c00c0b5001d2030040c058003640ca840b01c500c03405a907071007207400c0a0300d0350752940450101c0700c03d0b20f04001c40c0e0000c0f440c00e240d00070703002010410581d0501e5102c0f80600d0382c000901e003401200031002c0700c1e0042600b00c07815480c1c211680d00003003030340505104260103039403103a41500340486203100356121914 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 843306717 1250 843305467 843305479
    0xb03010311010e121f090c080a050708030a0e0d020a08030d0b040c030e0a020607031b0c3f02030709090b01050415240201090c06020114150a0302041a 66
    0x6141e08025003032090411416003c03a00044201c0d20f141406008501c00900d1000030382440300703004410f50f801031809141e101030740d80d541100318001641d011000d0068030b903010080814100303601c1c04924005041e00302c45404e41c41030124400301c030741c0401a080c80c1e100542d4000000d580d10320102e40e86508942140a540c0004901240122003a501041540300122020f000c00c100c032090540441e042d512070355000340c1201c040c8001509082005003426880781c82c00d14814651552007540c80c0c01d00036000c445030703003003403508111800401c03418141d046aa00c1103c80d072038444603401285908041d01d1821541580c1d240c0d002555005d001003401030041800511980c0018030700091403050074055544a14500007a0450044256140c182503490b40d20340a44107200340540302c903040d10f07422001030840d0349400210b070001d102603940000030242500003040d110703010f4031840151600100f0404160080c18a882050759411100008507601581e0015441c0d4562002500d031300d80518040381c100c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 843307967 1250 843306717 843306719
    0x3110d02040b09010801050402030105010c0f140105070816170429070507020a080a0206160c0816141f0c0201200703141203010608070c05011e0605061e0a05040b0301 73
    0xc0d00000240050202645c607009243c0e01c0f0002c0000300d01007030007014001141c110002c8002060720b10841403c0d80104c40303034075a1080d41e0401c9400c0d50421103050f800210000f0600020805401041e042c5a600b03040400e41c01c4c240c0103846e0052000248040e00c1500a0b100210b01042c54007a0724101e80400d101d18105450f10560180140d40b10140481c0170719000c010002c0c0b141800700340002c02c9039006000c46c0ca802005000040e42c264481001e4032807001c05a40051078107010001006a1112800100300d85072400104001c900c50045d0381501407120040082140451b85814407480c4002e800c01080481e42d43c00122080110406815104d030250000d54860010028000c01260301c500103076078100e016074180984484034400b655804200910040c0500c80c05a04107646c40100ca2a03c0d0300d02c50b074241c85040c01d44803004001c01d80241515811082d2648a000384005840c0c140c1da1315183ca02d0280388426074007401d02c282e005607040450b80741d5025118004540013412000046034880d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 843309217 1250 843307967 843307979
    0x20f0f0d08072001050118111b070807060206040b0609090c0112060515040e101d0604091a070905010509130216021e0a0609141302090d0b090f0703080a03110d0204 72
    0xa217000c0c0602485003402d41c1e6502c020840b00c1c0103051111440050413400c1c407008402101c0c90007484800b68a0600500e00d001c507001ca020000c42c0000e280c2d0780d00070030f65400e1508000d03160400152455000d0342c032200c1080f2900c00006030380901c0c0c01007860b00ca00c0109401c8150001032400340c000c10b6000c258025003150345007020010b00195001104c1e20b07a1242c465501040c2e8010561154104c1145a0102c0000c2542c40c0c100700d540c0501301400200c2d038032189070f0300c40301d5041080800b5100d903c0c0d2034007070288080d80a070021028200a007000d510384250000002e400400200200c00c00701d8000400c03201c004e800da1161402c2c1d0741d0140c03d40319094080080a181600c1d01480540600d48444001030124404c00b4514112000481c24a000b8040001408010704c004a500c032103940e001c103c020302c41d4845e41d040c00c10715406a044d031105410424402420141d00c1034090003682d000050a002095000044554903d070900300061070010740101c4882ca070060b482c03112880740c0302081c00911 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 843310467 1250 843309217 843309221
    0x506062a12070c0b040807091505040c1107213f080606070210030902033d110909071b0606050405090106030b07030f110409020703020f0f0d08072001 66
    0x350394030034a0700d52030786512244c46a0b001d0040348150000c0e0303802640704011a421983c0300300c00c011000028880075a44441c080b40c155080c40d07a06c40b00040e140c108006107040107000f03040240c24201c0401c2055801d2459600b50500c098070b0140c18062141c0600c000d407411000c41e80c5250300c260818540c81070f006c6c2d42803104006e80b15070800120340030304009111840c2000455a4407030740201340f80d843c4180904101c0041141500c01c90b05841110710910924400d040881c9c3d080d8003500202d407803600495030401c0e0818400d140c6100c0c0c2410191040e039250320b0f420558490502c261400c442c6660344550885503030701c18442c943d007502d0081d207100e4140205600f03c1000e50f00107641c00e00003901c1e0005224222200c1d4400a04074009410108440c03030f100345c00140442510754008500014441c10303d007281d5116a00140656500003407840c1016010700003100c0c0c0c616204060000b41502520450701c5100301d206a00400c40c0540015000b64024a0014a0528805c82030108150246604c0f40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 843311717 1250 843310467 843310477
    0x6030b0402130615051b060a1b02031e0702150c06041101020606130b0301110f071703040c0303050a03020705030c0106180608100b06040302061305130506062a12 71
    0x401942c46050380c64502c509402120100c44884810036005001804101e81503000310541030f000148500304450a440104407040c0552803400c000103071903c1c2041446030084214009105641040c030061482d6085222104034600c0858030003952101d141c40004c50324404141d090101180110f495042807100040c198402c91240c01600803911000005a0780c40c041200e000ba400806402c1c00075007280c1e650848803071440081d0000c601d07181070321411901038000540340558100003184000c00d101c0b50390f00d00e500703c1d04005040c2c0e203581040c1d103441000c207981e400060f050110000300600e001c1d104c1d17412540c074650084192604c410800800f5800b07040309101d001d282d9a81c0c030310030752206c3c0c12510810088403040401000110782d984940c0002d0240c40e0409a44100d0174000000561940702c001c00134440110001200d942c20322040100044411046008682c5844104240da440ba0802c5400b1181c00070b910140648241a1064010b10740c0151040c44c0d020b0385600b00c05131859200589 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 843312967 1250 843311717 843311719
    0xc010501050d08091011030a0216060e03030703030b0303040b040306090b071e0309050304030203010507080f010f0f0e0604061a071118040b0a06090203010b0d0b03010e210d06030b0402 81
    0x401140da0725010030195041185010302805030070051342e8290b00d040c5054034421070080c101610060794001910b401c641043c58141c0250f082081007440303404952035403101074016800d1144881940c01c010076605d0048820040605a0714240b00e00595010003d0b00c00508520390302c030707544548910f030800107004010300481d0003100e0b09d408030f000c02e80101c0701249000c910b0425403500000c0108128050401c001c42a00e50380010131010015813428090a4800c81c1242c035070040341d00380000c2d48045001c050348154018031b86210280a020040d0500804940c0c80b9640311142d80c840c44009001000d042d401464048810800c203025400c00741d02800042c1d004a003805a8000014244400f2107600d40f01c20011038180400180000c00321004683c00a0b12000300040407a01d03034040c0800c0364001e800c4110406008224601c41ea5103601030808840c50560080c85400700440185a860341c1041d00655090b0030a0103030b080341c0c20000c06682080b40c001200b8481a542da0070100d0401c0030586080e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 843314217 1250 843312967 843312971
    0x3041e05030a14010b0f060313020a030203030f07020a0e0601090b0d1b020c010201060e1b03070c05010c03061410120c0203090a090906050c030906160504090507090501110f06010308070c0b0d020c01 87
    0x3070140780ca8070301c0c0501c04142001d007d052442e50b03030b401001011144c440c0101e90103010a00c000c000b40e10b0400203042d02d1022022001d5492696004100d81c207500c6500082010840d00c04014059911034426011243c0c0c070800c0b10384404c04030413801d024050280030340340c46030007841c01128039590004d6200c20a41d420f800802101d5128900454842000c139007040154052a08082c5011034480040d50301030314600d0401c484000030384d5058203440c45c0501d00700000e501c1d81c1c030900461041c1541401c02c030404507203000c0d000841c40005880800001400515075580e003000c03001c030b103000303204940d1507020040c102c81410b80c880354080010454164181c503c1e40c80c1034002215000d418040b40d02542d030b600700401451360350421480c0e030b40002010802c100642444000341c20074180c06540e00a00c1c040d01c5560031582010001480d14124400c14452580520f44c6c030301c40303040c0c003140e454156604101c3c80341e696074030380c1003a0180441681c008404401e002a0112405403154003402c2d40403011030003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 843315467 1250 843314217 843314231
    0xe060141370f09060302061b0309060412030e120d03050601090f0f150f021903030603021503191a120109080a2c180603010b030d02100506100203041e05030a1401 71
    0x383c108580c440e000082d004081000306110301074500c2c40030250b441c1140e007128501400c3d4000b260b03180d04941d000324240300200c2082c604160b04940b50000440781641c21107598a8461001c5584183c05030007681450383c1c82c4046415644101e40030000f03441080b41e02d0341d6090307079002126210310301c9110f038404041104407110042485020841c10b6041245d0082ca03055603400340b51040702245078030071011f0550b030310307400001038580411030340803c400d00309040d8507845c0c03407680040c1c14401c52817000c0c006071800d01200000301000c258001000e03c242c2d001018845c1110071030780140000540901f011a02140d07032200158044601400203505c4055124081c0324400f404400310080611f1551207020b5815001c102eaa2034055598803400040c00800c031240c0d038402207400e0180201d80d0400581004007904030128480c05071279009142a6030a0111060713080b0029203a010318005c2c140c4480e464040144580d400d448240090480101a1000007000b03107070404214104400801441d428901 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 843316717 1250 843315467 843315479
    0x51e070f1404060903080354030a030e031b0f0d08040b220b0108010203010f0f080705091305070605120a0b0f12010e060141370f 57
    0x760340c11106142c070745203406070542d9210010f9810042100307062412648a0f41c80100c2d000a03c82151000c0f1240d1000c900c0d071103d0490230781f1000e21341b085c000303400840001c021810000300310340789028245070000c0e10078030503c42c1c0c03030039403140036030301030a46009902415050750082006051881ba15040b1147d10001001c10b42d42140304480290191f158800002c101701001941e0b40803d480e1004005484142c0740e1311107040400c282c104040c5a03502000501041c13810200540241c0481021800c0d064070b001111640c1c1d0445008943c040c00025020800040f0500c1011715180e50040070350300b515031201c10040c11900183c6443d840c02e27001501098140b21240b1071612401005007013000e030400f0000900c4000401a4a0341c90950360707551360301c8840f803802e0100a0107000312880c0c6d0882968038514510143c1502c94016100e00d411048003006810300180b8001012016610000340f81c003500a80007a0620040c0d585c52451030301c848000303007513804560b5402514007508a1a0040362141 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 843317967 1250 843316717 843316757
    0x30d2f01020d0b153421030b03060a091b03260301080d0c081309020c3315090103060c021b01050913060803220501030203100504051e070f 61
    0x4c1e2072142c80500c10000d032050b620350b40c60380b02d030395500c0b4170102c01030380ca445000d45211418262003a0303118000002030f039511489800d11281c4065680c80c080c041c4200398000207031580d02c043e024103040c558403441102080034400d03076021810000b00245c3d200c41e40c0c03824800e01c0e0685500100600e0042c504410740a405a80e007604e0503250048018a903100c81c11001b81da80c001c90b00300580d140c02051102c84030b491580c125840c080c2007540800f680352110051075074640002e03952821801034140124074554a1101c2c0a0450500c00030504002d80e00c1d115040c0300c0c008040a07060f6040f6061500100600031307240c010410080300c3e030b400c540e104903910b0440409003d1240805001650401081c0da6600c1c0401401003c6904101c0c000b80311a915805a440c543c407131402140406440e100c10145a0641c6a28800500702800e01750b2951424503600c01c08031445020301d80c45299100049440c03d8000c0306898242080750400c14083c2c14000e40280c1280350b48014000080c10504028a40701441 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 843319217 1250 843317967 843317989
    0x110d0f090f08071a0a060f3c0f030b060913050c01050a0201060905090703031103120c07150f1a06070b04120c0b0a09060c050306030d2f01020d0b 64
    0x4804540340303410b0b50700e400540d400ba000507903082519808260407041c04e00012801a4161800003500e00e18052131809000301d0b9910030740c40c2e5041c04103421208a019075040c1c0512040f0310021125506803500049000d00e107802c500d0159000c4d440220801c00155603d9001d50b00440d00c3c3c01c0680c2e01c00100034001d02d4441c3d001495a00698124116075000e070f00074068404075400003095543c3c841d030041040707400450700c0c00c000da40994010400d141d0000d59a22455000e8009107281c00304507101e445000c0d00c094600480d400000070141d0a1010180c0c840f0612107000d14240040c0500803400b5003e046000307401c002e102000701880c0ca280c43c0c0304c0101d0710116402190720181d661180c85404004c0c1185503102c0520089050f010002101d0000a51080400f040000b94400f001c5c10010210b42031a4580c8007440010400e004055400140100c070010300d41c81c1c194503040750b0b9a82600210b06181a803204280040702110b06d040c41900504001494000100030003d40e40e01040020486 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 843320467 1250 843319217 843319223
    0x1020a09080d1e170c03041109010e0601082502060702160e1801020f0403080c0601050f0d020d030302091003020711010c02090112230c0111161413110d0f09 69
    0x5818942080c410b80c44100d80d0f10441d480c146201c04441a0745000c1c1c0c800d41c200e60320708001d8800420401000114200b0709100e14042d20603c5996043c0341d0030b1788ad07141d400f4100506009c60440002c87d0400e080c1c8295600d40d082803c1000d601903841d01c040e5541005640d0040580501c0303280c1d021801c10441c2c52806c450415040310b0090320307100700040782225030004064841d502042010301c0010444010001076100e50b81c55541c43c050158020b00707115042e006a4030130b41d00d025446141c0c0e503500715802030b100d8044400c1c00041405140650003071052014a80e00b241158180340825a01603010303100280c00740222195401c140b1004540301d98014100950101c61600144200200f409141e05a0b40c45022070707a880d100b03624076262041c0307034201400310107070310401e4010043d5030b000c4805101e072080d800040040d034070300c6400c44441d01d84500915003100240c400d000070382d03915030072501506101000f0811420130001041001c03a441551007001040c100020714040c07000900c83c8a0403550 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 843321717 1250 843320467 843320477
    0x23040506012c060a080718060e2e051009050406150203031303110303270609120d1506031401060519030209060d0f0e010e0318121006030501020a09080d 67
    0x1104400c1105200d8024141c0c1390084600700001c0741c030040811000000d81048a1054801c00b150322900c0c003541c07500d4004184240101c0b0502915000800380041c040c078003050004075000b1a90030422400c001940119400003c02c0c4161401c50741196403141a01c00581d801e118003a102c0390070320b4044224010940c0140c0c020400100304c0885e03000800c946602c41c0c9050340702c00040d6425245160425a0102c086103956400c840402d500120f07050041c40080c0082c090921f02418103584841d80310404c1d91403058001407482406006911140f00000004c031408449900c84c0e0000340200130b030743c048a618042e013800104005010b03005071006600e03c070115103803c0501034402c5002c0c1d0020480d4a0b0400d1050240044080c81406241e140d110b104c000060844c075420681c9081d101400d10036015070300200407400e035000808146451031841500c403080b810300702d00310003403600c54240c01c6401070038035114001c42003080640042c80204d02c1d81e5915945d0741e443d02c80c425141c440c80512000492 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 843322967 1250 843321717 843321779
    0x11030c07060c17040e2403151f0312030b010207080c011409030613050601060c020904140a170301050a05010f05030a0c212702060301090f2304050601 66
    0x544120310070609035100d0409201111107a0300461415007085e0040c60400308030784100041e01840103e0001100300304c045c0c12000034120b0000c41d480b650780c0c1e01e0420109440e400041c1100c210381142c44101c5903800f00c10070702c0c6642c0741030820320000c19003a4980064141340c0850329035840000c154003606e0001c0f014000c5104841c2c01992000215042c10140c0310040c8585415a40c041c040c580c030681e01d2140c915148165031600d5400c002c07058010206005413a141c07240962149540707640c2c0149e000e000c044a070b0741000201441d010505100410301078031164584401010407002c0c50486400b07442044210380c07031b0f400648900204034800c400064083c03000035030a01c2940c000340c1e0b080c0a14101200840082001f0007404c40000d421009002d880e9441c1902030300d14002044903813203000140c524598425400680310348010f100f980340480e10740c502541290001c0d03200d8103042c804054045e030000c2c0c00020007101c108044800340c1c2c03640100000010f840c01604070000c65031280183d40f24000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 843324217 1250 843322967 843322979
    0x90f01240201090f050a1b122901060c0b0f010302010f08130209070c23030909100b04090603110f0307121506080601050307121e111009050111030c07 66
    0x103010308000d00001c42d0340303802e65100860300080003080114051005000480385509100d2580204944a09400701101104009400100b61100e101d03d43c40780001003120041c600c4030221500c80703448000d08100c1c1000005400d42c020840c103144912070600c0000c96503d00010060b604001d03c400303404601075021003001584104c81c2c6a40c0030300b140c42d0106400c800c540229030066011201140410f0721401520103101072702c0d50800800f100c14540e4001c02d1514140b941d200e025200200d401519600c0104ac0c40c00e00b4100c00b0701c0584101000f482d00d49941e5421a005040907104c00d441040346c681049005081090303010f200d440001e4018051185040c2c4090891604490255200c5070b007621a5100200c00f4080c0c0c800030700303010b40141541c3d4100f07000c250401500b548151005810042c2203400503821114003a1000315148a4070348004090400300c1e06032920b00c10140d0b100114181c01c2c14450341058100007981e400ba600c031a00b280c0c81c0415141d45e4400c4e0200f2000543c4450ba0401c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 843325467 1250 843324217 843324269
    0x1b0705070302151e0d1401080712140a0f060b2e03140405011413170306130c03090c0b0f0f220e09120a1d01110703050c090f01 56
    0x901d1500e243c2d481c0f518100240300c00900b02c482002c41e418100000344000f540079103000c1d807002210760041d107111039498060703001d80d50f5406109031060100d10310340210074004407240707c50a0402c894150f0f6850442890408102c0540040445105207810901842d5003040000507001e00e10010300c0910300c05900540481c120750716800c1c02c0c1010f841c1e2814512082241810741c0c00b461040b000480c9001503002c1c0b84040318030040002110102041c01030000c5101034040c07204600c8514400c81d0f980e110000031403d0400c903c030240440300c1c140145881510b0b4075500190f0341c28081c2d120300950b252609803a92140c4120320503404041e400b405000880c1c00820014845c54250040c05066030751003c2034009507004561100407104140010050540ca0a015000c0c0703908003890b00a281ca540280060b0003403024980c04080c4081c00780c0d8000076a401069541e480e080d4030030031a03c1040d03813890075968804251210364003800441d004585540d04012015050b9110034914026202c90300c01d0b9044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 843326717 1250 843325467 843325489
    0x5070905092a03030a030e0d0320090f090c070501060503070b0403020609041503050307030e06030c0301120302120f0d06050d0b07050d241412070513110a081b0705070302 75
    0x80b400201c41c030038444954040005010320300c940d89000c50740c5d60361814414102214000d04005260524014030240a680e4004141705500d102c5903c0e242c1e12500302280890b100300001c076800c903860704140301d05514688042d00711280b0910082c000c56444174285501d56136980f24400c8405000d00050005290200c040c194259001d41700041d12580c80c00c62000c5c0704540d030b00c02e4803680c00006051040c0f550103940003003040d009032090b41ca1804c002520b0b0f0303050300c014880c2402100b0f045011008040c0300b80010018031641400203a15040c0004041c40e0a03481400b0401c0c03814035240c000a15824030180c20340c009a04284108003d640d0008240c607154045034003640f01d40c1e591828400f00d22100c3c8500803141c004440142c01c61070400403400b8a00d07001010300c0b8444c1804900104c009032000424205a0b003080d07810079041d00004004901030040101c2041410a0124900c0c00460f4880d40307461291101800c503180038030102c510a00c40d40710f00e40001d003140e0450704c014005801d1100c1004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 843327967 1250 843326717 843326773
    0x10912080904060f0e010806060d0b0406020c1f0b090115050c03041503140a1803050c34150509041806020a03060e010914040b0612190507090509 64
    0x36140104820008040340c07040e401150020100c4c4506000a00e0070004403405402403900034032107070078800b0003d0880340c0c440d030000b170012364004002010080c80390107407180610031004941d0450b04a08105a080000c9040c5101840c40c00745511954a410190300d8121800602e92140c80c108403041100c0c242e10020000c00b840c8030401c00000d4910340d012300100d00d032a031b030750b00014001e070900510079964401400840c4214204951060301d030005000041c801c2c1d81c9410800c1d525420107030a03034140802190b5031501448a100b2a6030111021211040c5032891460118074441d140c0c03040490080d14250301343e0026a044c400c4d4225428180c0c0082041910b503080510029484c1e07513000c00b40d81c46540ca400000342c958000f00038103052001028050082064284290307246500b0206080000401c040c1813042c0c0030010907000d0300c0d03486000a0001c0031105454115034502c0340e20124045624003114540302c1c000001550180901c01c6034029048403014203c0c20481c50601c515050080f5000c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 843329217 1250 843327967 843327983
    0x105090d1e0b090a030306300c120809040b0d0b0103030c021309030f0f050f1c090c0807031523040203010e0d0f0318080a08150603070e030f0a02010912 67
    0x40000c01c2e5000c90070340c4503001d8200204103040c580d1030020261680c560014282c1708036042042461001040c5441c0300300f000d60b20300c40d035125041c01d105a810705c981e840352803150030743c50340c0500f4030107d40d0041050b8141940d080c801c2c280408241700905011860180c11752410000600000e072040b1200139240b0b000400d4881c8000d0100344080403540c0b00c000c1140854080300712107146d10b402c40403007030350300c5103906000741080020b480c50040c1e4441c0c0200100801c100c7c800f0800380f440d00d80e0290034040e411034503c51004d07840302e0b50242c3e54000c0b40002d03900d0100221035401d002c0000d004182c20322054200240c00004150b503d580201c0d40648120703459502d074495005038039030420880b6900012950dc2c2e800070703004048090102d441d8036848100b540f1210312100f01046816040f2010415185000c0e480c079030301c86086100f410320800d8890785c001000401c0c0075405500a52051014000b103082e601d5000c6244c840541e03801e18504001c1c003152720080f040100e40390003484003c60a00443d04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 843330467 1250 843329217 843329273
    0xc0d0b0c0c240f0702060a0b040f0609020319020301080c0d29060a0515040509040f0f030f030f0528093005030f060402090103060306050f0a0b0105090d 67
    0xa00c9003000c0409880396442e40c440c040088240c10740340c0020750024441c00b100d6801d402c0c9564000c0d16048018211402207031204010403c54589034000b1440c4080c200c400c0100c0d036114011500658001e88149112841d540c003486900400c5208032b034100c481c5000102003000d03a0405001ca00d0481c401d01751041100208001c403240320200f42c40a68510840c0d8400c0b85144c8941000403001d0070b500300c680940110b00e03107c480c8000d50821101618811078191030256981d1a040c11034084101d00103120356000c20300502010703000382d40c039141074410751030500c039615104448a003280c00850303007007031404940440210f00d42c00202042008551080012940519507180c0c02c0c80340300c00100c0d62001d03108082d43c44180c84040005034859030118a0304a14500b0070300c00040b075540300030303118074840c0d60b000410840c9070b0301a90040b8000d6512180900451a2003111322046a808852406801b0304014505610b0b6100e00e00b1079002d43c1005100c2d5000e014036880742c01e4429007030481d8140000c85041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 843331717 1250 843330467 843330487
    0xe1009051e06070c09051e0f0c1e12060d0b040213020409020c0a020f01020d020a03110313060309050f01020a091a1e0712020a11220f060302120c0d0b0c 67
    0x401040442e00441c0c002142c81c0c034080100040380d000170140c41500402c032030601d20881030004900c0e00a2120711150b22303a915681c40301035251159141e119008028814180c0c0380c03148400152003440b0500300a403603955110818000796070f4001000805062845000400526103c0c96230212240c07114801400c1a44500c0000202d074062460401c481e4406480d100c11894400c6081e81c603010288041c0460344180c0070040d5444400020050610480694803210340388100107682c00195509900d000141d65901c0140c020212201c0594160181d20742c4031403001014001caa02411f120783d189440149422440028500201003800b0606400c00c0f041100c080b480d050001048000c00034180e5542240c0f4212305680241e000134010740d0030600f4400e01260441d0803200fa5201b0544011342003c0b070907100342c2c2c4101e07141c0d84055075162404102040c5c2d090168090401d0728401e44075a10761422246010b950341e6040004550302071906a2194001a50b4902440e0000d400714400390034401182 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 843332967 1250 843331717 843331729
    0x30e070503071202150c0606013e0f2b11150105120106081c17090c0a0801180f0305040f0e060906061602010302090f03030f04060e1009051e 62
    0x2510408400103c02e41500551600d1480298560b28002c42e6910f070101e0f22411a45400d00149940e040c003a401144040007441d98600200311031030106c2c56845250a9884046d084a1444034140d242c4038407903d00700d41c0000020304440f011407500640d8440100050403010300c070f03090a5140d00700201d4540c0d417100200304001d4040d0f044050780d550034656040205015014018880c4500d042e030510368100500c85021400c080b950070b001d00283e040043e101c1c401c1c1c4e9022101041203803142005020014509400701d00a44c50590448a14030069600d030b01c06403d0707500719681c2410a14454000070300003900c0584101401d4468200a410030380d8443c1c446011240d00e502044005124008201003441d0080d8803d6012200b110000c2c1001c100b502c07032084544405034000c4c14154000b81002a42e96109101c00c80040b0040072280d543c2080b09000030700b50001e21600c0c020401c009011102c51810360202020001a951800c00c224500700c2002120b20002503c845221002a18070307040d52110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 843334217 1250 843332967 843332969
    0x402090603100e0f160b0f0904060e090a050111040302031504030311040f1806060804020f12030408010b030f06060114130f030303020901020d020c060d11191205100e0403030e07050307 81
    0x3d4010341551040080d409003480181c00c043d000c1c41000f140306119580b46a0103031038000c102007641545881945d40810000c02d0300e40c000c0c0030342d20b1015041241c2032400144422500d88510f0080c04036040c140903604660145020095040e04240c0742c01038209019110154403500900d000300d1041c0303e000c600d840701d900c180c110a1901c6200c010510000402941011144003400783c10403015240c0380e030007080701c1d401038402403040920940c5075516a88210880440500001c1580c0e41c95a503518854000c0c484100d2040c001c1c05582c172003888445000c40c0c1d1512560061311034040d41d002d02c006c52a003507400803400c1e049941c2e8050000c580b20f0380000c042030146100b51001691454158000391802d07400385085400c540c0f04016042554a4030001d940b044403130308201151408603039000c40800d0196079410400002a880814000355001400d1303091042c6014040103d80c440d00d01d880703030200850240018010044c0041400288298881c0075850895016518020388070303400a03050a0007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 843335467 1250 843334217 843334241
    0x20030c1c08040f081510090b010e03060c09010e0f0f13150308220b0a0c0c030611130602030c0a0236090c0f030a06020f120907030b130b040209060310 66
    0x800f00003030140070401c2054003050700440d941c0e40b07813074a0700062410b48600320b4060ba01032030f6140c05031504540d0040c1c00c10700361200000d080e15403910780031241ca4601d0300559100750000350140103040803402e1486064034a11000740641200c48509024040800c4c0c4031038020008607035400071070301ca00c410030032640017462081e1056a42c80785100880548040c9640400402c01860380b0100301070300c0035108441851a803414801950300d55400c1a11400c042a40003902c15418410380140701e01d48603004000d2004018056480303591991003c0382d59024003162900c80e5800301d00b842001d846d04245445407030000c0300b80750404480c2072200c00803604210401c81445040002440710440341849003042c11075007558115000340007280069a0f8400205002d0b144540c0000d29800071310104080358103c0141108294040c202182041c0d40c41c01680300503540c512a0b1b0022034101032101c4a083d0400b50030455a00140d201e580800c81280009405190715118185003032010100e140036181304015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 843336717 1250 843335467 843335489
    0x2131509051e1806040b0703020f04090c091a04090216060c02010c1b0804120804080d091401080f060f2d09060a050a06030f0b060d050420030c1c0804 66
    0x2400300041d0a42e01e0024003070042c004201e000940c26040001a0b13503a11581104040c59203171075180e410380081c843d88a015211078800940070400900a0b0028600c0c001c26640301d030b403c1650b800550302d400b20f8200c0d140c0704409040008002d01c0080340c010b03154000801280c0b607480c142c00d40d548070442e02d00d9840000941d4455590210180c2c2140c0c1a0a0582141c80003003d0740d840313a03549426a1281e170042c0c4210030000400310040c0a10074054070003030071100701201d011011881c0d0281c110718003807085a03003140640c0c1c0c0101082d40700d21a102d00a960719442d50355107441c1c0c0030401400516840049400440d64400642000300003151044103c44003100c005107021888144162404010303c0d95002d070444070000c001d103071134683c45101202d03101e140c000390103e0100d104502421251030059449100814045810102c95001f02d014510903a0f80c0d41d2000d001030050301d5400c00b401c9441e036045e0003855060070030781048030305400e9805214242c8040c440c406d80d1000060f400c16080701030542 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 843337967 1250 843336717 843336751
    0x11011b031a040c090e09010207051603050708070609050f1302181507020306130303060e011701050f0402060a3902210304090b190803031504090213150905 68
    0x54122841604841030742c06200307410340c0c100060300d16800e500c40e445002072408005040400c00398161003503160310505641100403041e44450f0404041c3c00107a405004135840018141030001d0030304125605920343c4c3d0b1400e440c280c1040141200e1022298001000001c5d2040351280c5200400c0505501c6050440c480500350510032000c50804c4031410a200c200f241501590b80010001d9112102d612140e0b020b0507181380c110058070290344011411043c3c0c034004540002400480c05a0140d204000c1100360313904c8402071200030382941d001c1c2d00031300100560140b07a441340826100c040c0c08001c0c0003184030090f4181c01624030a03041c0404004d00d030002c07070800718030309440d46201c1075410035118120345c40c2c4401c5080d100c0c451880b0b107150345603480b01d00160b1a203541d424507840c1e075003001119401d9652450000e450368030449070050f1368016440000300524240c841e40d00c41c56006000740c01c1412049443c0002800c02c0b0b04040100d82a520b00051400c2050244600c2850f04140160500b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 843339217 1250 843337967 843337991
    0x1210204091a16080408090909070306020301060507021315030201110f03131406031b0a1101050702010e011107030504032d080d0510030f11060903070e011406040803040611011b03 79
    0x169500502d00f003c0280301414403000c40c1c4504195020b4400c21214542a0b4a94040350346c502503041d07000521881c004400012103540281c040c200c003600a480b401c0c4c0c40030384281030108840561910140d5164607035021300165101d076000101d020150310465901d0410306100a1a6401840d0f00c81140070384050280b150b0440b040e550001410290345003030442c18100300607920600030b2500e18107424000305030310b00201d200f82c841003103142d19003008000c541056607009000c1c1010301c46050707066003070083c43c40310f011701042150915905039640302c0c00c10b41156140c964881e1407907113002030b500c00c15003042c3e07410f410b44c03070681100f9120742c0320a41e403610000440c00683e03200030040f0300011072a02c002c00c041080b44113883c041a40c4058144125102c1800080300b034011100540c0c0c00d4400c040003c15420509104c0c18166201040c0d460481c521400030001c1904c114080d51440381c00074041003102c02d000706000c0100102900010030000d09041c0c40b00b2209080400d1500041d4030b9104150344 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 843340467 1250 843339217 843339241
    0xb16030609060e010503100c051603090f06110648042c04030905010c020a0b040803180409110d03020a020d06020d0e010e0c06070f05061003050609030301210204091a 73
    0x201241f140742070084908100f03001d887e0b070203410310180d04010011400c0040510510071280135058008800ca4440d40325800141100b245110801c002d00c101808103031105003c2c02058600041c030b410b4071110300c0301501c00108001c0d807400080c41e680f1441c1c824202140089019202400880c003400e440390b410041c170901240d14680c1d150f020701e2a000280808079500c4403680065a900707003410310541a052021916904050307018540d00c50700881c01207140c06000c001000c481c10780904285260320610200320803103590300c400a04410380280d090700c150410680103682a402070041d24450305450b008621b4001031442c08540d40d1783e00240c0c0015841d814070a040c0007840c00002000544804459103039650802ca208034800e0030089508410400034000d116603030381d880707800e884a5042002d20401c005012303002c11290380c00340100003018091700100f07a074120761980b00c0c44000c2440c0388030341800441807418141e070803a88038440500803a4101041c2c2d201d2194041c85180c0b82c0ca04001d42c601 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 843341717 1250 843340467 843340483
    0x60103080304050d03060602101a0d0303020c0c0103140a0c112418060103080c030c0313080606061603050703171602061b0414040b0d0308100b070b16030609060e010503 74
    0x40c10701c6c010b421310605600003582e0b0040c1c94003040010340c4807012900728114804540e4031552000e100c80c030260403d540b5802400c0382c2141c090032150460000d40040d026039401c2800080c074011100d000400d050115040106001d042e030030021100162004c07014100b4601601491076811201c5181c5600d000045240d035204003811504103611700710709640f5403a00010720016141c488080340d2400038001c2402103401482c200310072280e641c4512800c000c003400e02880b848180d0702a540020380301c0e060500c02c4030034021000349039460b129125a0180c80070382000d01c0a4040241c00350045060b1490180468000c5a01084803001907051920080c90924028120104ad02c0078034045255a0303140c10a903802c0c3c4910308134020484000c0c0c00402e004041d444c61070350b4444079408070031040c10f802001c2c450164001c0310111070455154003007000d0078804c04100506210b44440000c0352403030046198406ca09242c60003280c150703074807000c480c00d480385038005601907054200100040d244c00c0203014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 843342967 1250 843341717 843341743
    0x5190302040608070e030f0a030305161419032702040e0d09030303050603030903030f0d0506030a02223803070614070f05150115080906070302160506010308030405 72
    0x251401d800d2200040c0414005032a00b410300c07094035501c1c1065078041c441d000d5075111750130880d05503540d2400c00034050031041c2c401c2c03454440c401000c2100184112071110300707809002480c030700c2d00d40070f40b84200314003000b51041d204140c0c1d100405085195001640200201c22083d014100c20071070041104894600d4103040d26548298200a261504500c4100c02c598246c200050903075901c0010078110310400b1801c0b64513010010341c00d180340159401508005c21060410081c1c2d0351010280741d80e441c01048040c0d4800e640c081e0b90941c8601c2d6a031002c0c45030f42d44c84808103100d1140402168225001903840848441c0d0010000085542c0e00710082840b800703d000b0b20704540b4095018000c802c900c0c03910100c6001c00621101800310701b290003225144e00c003040b00c014a034201c0c45103001d0582802910a02c4070302000e01940184a112094002d5002c40058402c0e40c851010a400035480b1115154018106040b5280441c00600c4a80d000714054004903544c0e1a0500d000360510388010405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 843344217 1250 843342967 843342971
    0x12070615090c0318110609120105070201061a1e0d091b0602010f06050906090606123d09020a170a0f0608070f150309140a030201061a0d09020a0e07051903 68
    0x450086031402d440c2c04040170741540e40c2a500d82268001c070300c1c1c4e0f110451000045600740000d114101d0345c154007140441c2c8400d06460701014100e0505011480340c0d205180340b10140001100b82c02c03140038010722003610002d2001032036000c1550740381026000b82035039041440700014204401c1c1e03028064482c4001d45840c081200c9070514001600310345014020b140103114440000d222502c1d00d000b00c0301c0d0160304a500303988a15120081d103040d0204008003468440303840f905110100f01803d6660035548104d00d460401c581003150140023908011006000c11221200c081400c1140c1c02460380921550300e80400c421081c1d900705000d07130b44a540100425405a07000300300741000c1c0e9903244242e5500b41164810301513070001c11030161030300b48000780070740201c2610b00d8040ca03800218080d145d4400d0300240030702e41d616400c0080b10340580031044405501003102c41d0360312140758002c1041e50720003031140d098540c81e04c01041710b00008544000200c2d00010700c1043d00c01151204e4440d4030b0081c078007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 843345323 1106 843344217 843344261
    0x51309060b0d120c0503130b1b032b020d0f09022805010806040609181e02060f09040609020d2a0212070615090c03 51
    0x10440d01a840c018101c10399007020180310002d1900184203088001d00b1003400d13640c00c0e0542c0c03c03c0394a03010800070460001d00c42401c1030301400900715078940fa03007041c00240145181c2048480d00a61061054900354591034120301d00c3c0b240f02c070442c1880e88120a540501901501c01010501810403844500040c51607000c011820f0088900d204944802d040d91020391041985060054070004000d000f40d500032441650492409040000c02507131f01d050341d104540d40d030210784502d4040b141030b10052010003c10b03650b85041d40e515201e50003c041d800a202d40c40703804421112713080049841800d5a0f12940550010000b0290a40d0303203d9203081d001c00208455120b89010950040d103a084000d085030320740105c84199002481180d2030085800007a170010041119901c4d00c0703010b0700d8101c4222402200040441307100100e1030500a0304040c0a03a007441c2c00c0350100e001d08a10b = true := by decide +kernel

theorem cover : BRFrame.Cov 843165467 843345323 := by
  have h0 := BRFrame.cov_init 843165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 843165467 ≤ n) (h2 : n < 843345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
