-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5012
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:27:30.166928+00:00
-- url     : https://prove2.me/submissions/dd9493cb-7f56-4755-b703-4caeb1ada20e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 901258992 ≤ n < 901438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 901260242 1250 901258992 901259003
    0x91223120c0a05071709040c020325031413030c0e040b0a0c0908030c150f070e150d0e0106030b01061407060908090303030f01060306050618100905030706050c060a0216030507 77
    0x1050030b15107803030313a401068035180f144e26040000e400c0d06d103040c540100300200c0550b000450034081141d505506e51422081041c2ca12580c4074584010705100e959a007601e100c825882603960a81102891250742150000b551040d07241080043d4003442c0e0890607218a40013844080f0584030301692502030001a81d20704200f0101d1000854030803001d0000f40b5641e03550b0f070300511488504071306980310329a00501401d0b42c81c030741d88108040700e42c01c880d025110318811600048441c1092140301214041e551031100c4641c60101c40c0b1401040541c01030041c0c0780121a0b070015a0303038614003200d603400003804e0416070510500503500040d100b50003900002e0321070300c801400c0034a000003080c40c42d0422203801842001d010b00401400d41c0520440c0d0140000f038488915081c4a6007220003030906800010303004440388046215407030b10401e01c51020705130040079580803d40c0e620008110360024071812645004141c0402c84021441c82111019a00c3e0303104035501d0303100343d24151865003084800b03654 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 901261492 1250 901260242 901260247
    0x305090705121b0a030507061404121a01080d050d0b3d09050a0e07030b10020307050c0a050a0506030c0705011506020d11060c0706091223120c0a05 65
    0x241507031620390903901c032408000285680c20001c010f6203041d540078500b290084c80908800d001050b0301068050640b5014240020300f090003007034071059441207602c5a1a03140740b2520303120410282000c0d440b1030050780384082c401a40c0300e07205c607516070503212480c5011800800461040f409680c1001641c028001c00c500049240e4403183c10941680b007104030f200080e90b10041c03c4c0750f209406c00c008801140d03d8164020707410a000700b40400194003a90a0300001300000034000b91094000103082c11000d02481000c285401029541e90818001211240219000e4100600b4000c0400003160307002405089014940b409000c1164005098501480b01c20058034001c15400d00038080740c10041030411440502e8540002e003481d40240a0340c0410200000f010451480029083c3d000308803070503955510030301d41c07400750001e001c58071004040100386d00b402c101c01604034400039042019000300001895031541d5461040c4510050387c0b101c0c100c50300c04151454501c9000d02001142824042e2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 901262742 1250 901261492 901261499
    0x91b120313060e120c0d060509160303030f0b010309020d03260f0105010f0c0c032310021909060c030f030b13050a1b090b0a0c0813030507050a08030a03050907 70
    0xa60750880d0360411000308000c810403800d20b0804003c83d0380c2220300700c0e000e4001100b40f9400500c0076107440c8400b40072292217101003469900c05106d00080d9405140b49111415030701e1502030301070b011080c906143d00f4079105c42031a81d54040d0003011100d5500600721060f00800e540c0c15280d0340c190300715008400003041444500c0d040038200b00c50082a41c10030360f000079171400300014060b0004417061005c00c401102500001801f1004100990f03a002492610791601d4150751004c0380000400082148200e5601c85103078842c035401000403042051207000044440882950745199507c143d01c006032502c400040801d2180143e4100300000c0c0c0b6010680c0000342000800881822030070f98882e59507401408108400381c03240004540b11081410070320981510003900c4001a0700c0b40034111000082c140c3c408034880d051030b012142d44200041d444510030ba000100d42d00c16404100c40038804c4560128462070184095805caa000030015454040300220031406414050115131030f074841c088010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 901263992 1250 901262742 901262767
    0x1002071d1e09011a040908093c0a120302030a140f18031005060609010c060b18040311070e0a09060605090108031c020429070204050c030f091b1203 65
    0x2940102c1c070000c000b14100324040b02240b8080b28400c9100d10a9142c45110400071341d9070b1098032206c11040354403c3c0c4450414064050b9440c004400c80903090a10500410341e0007100d2584108a0007981da0600d00e07a103450880302c11260025002d40980d000340000c8154510920f410a40c84c041a08000d041c040d03442802042500190303c0b40301200f42c41481c440303080c24104055070801502e079105001d18280400800c440d4032910001a0400c000e02c0300240910095800c40c0c010306030040c0c00c2d00803000c40510480318001082d58100d0009207000841c40c510713040091842c0c196a40405030000f641c0780c01800000815025404030340c0d40b5180e083c00101552041c607140c0c000d03d80100507660b40c10b005121f003219071100c12400c10500d481440288540b03405072103128161130342c2c442c650002d00c510003d21a4540205a030003075003c0c1c1840100701481002c00d000d1801811116050341c3c1035110804c0303003512019265000b580041d11480480490f14106030009420610030b001d0328503050010540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 901265242 1250 901263992 901264051
    0x10b0f12010902060d142a21091c020105062d0d03030203010602160b041401051608120604330f0b0c160807060e121005061002071d 58
    0x40d00040d076030300d0341640e64205600c5003860344071440f187e82d40c0d03c3c0041c4141284201266021000c3c4881012908030304603d0000c4003902c0d0f480525200922034504110101d07910001d154120420310101c004003070384580140a1036014000081640303911540c2000c048600b0010154018107141a420038080c05880d01c03090885107038003942c0c0c0541d0307941c18104046c2c0b4151000c50302401c00007101d0800c112240f0b40c1801c1e101642e5000c3c6803843e001c05404012500c901580314082c00045d8026440410000020000d10b401210040041c0c3c0c0d070b903180380411048803488038000d01c0c01031006075400d511104038080d13410b020701405100d180c80c0f81c44006944810900c2d401954030610f0000340c1907110b880c20441c241c1c00c94401c013482c5100c142030040d02503c601d00e51048505000ba001c0ea00e640b0741d40da40b10340700040f994500c226048080d08a0000b40605025105036000b10310b100c240501043c80469031005803141c048454007412103003480c080d081382d07008212050748a00c0082d2003001c929030780403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 901266492 1250 901265242 901265257
    0x3030c020907212007170f07120e100509100c02210105041104090314070201030902090a05060103110307020a11040204120507030507080304141003091b080f010b0f1201090206 77
    0x180052a1400c00705000c140d2264403105004d815030910600300054a001c039000461500c10200d142c40d07200400009030240a0958010a1500703050280401140d01c4001c0840050040b42c505071b0400c0114011388403440344003045e9400480c070070040c01000d4000c08189403914805420707105038942d0b0703800c0c0da50494128009614665120b8052000f44180d003040744001e280125003c22a5102079640070703254200c02c0d10300241c5840b01251007000d680c002d500c508002a000b401c45a60346c5801c01482d002071100f120001e01080ca000c1040402c9203000c820f0301e100346101c1d0000d010010740354950b40e4241114a4603290301c41c1c0c00b00404109240d401c9032005640b4421401030a9050851a086040c0307813590b048010960300601c8200150385400030030740b9200c0026990040180340d8520210041c01124502070160030300700c0b080880e45812020100c0807600c5481c2601c011841400d80c05080e2420b42820700c2e0312010501c216009490801119891010460000030354003210781c0c041490342d0004003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 901267742 1250 901266492 901266557
    0x111608010209130209090105100e06040e090f2a0402040801020705010615021c120923010605090606032701050c0711040509060117100608210403030c020907 69
    0xb044089420540034040302d90032801d80550500a01d50040b804008051040700d02c01c02d41011850509401070454087c0f00d031000d020309599949070005a810800c05403003011082c410130b04e440300c500d040421020288961800c00030241050710051a510f0149924916409503081100052400d001d02c000c0c4500741c803860020907500c0c9060100c035141d0107215006002e540284103001114801c02000c040c41e0a407500380100401c8045101030000d0400940042070f080400c140c034178020210700c04447c10740e12000700030f11050340c90300b05020b42044203542d030a82092080c00860440014606d81030090501b0802050952150411113400e6031010b03503003401c2e400e0303000410744107100b0450b40c22014070307000f80d07002d004a0400d0104c2a82d50201440344401002c0100101950340e48288103040c1042600402407110503142c000658541c070009000780006460308400c1d40846401c035054408894041c2c03125100c890040c1c082c044a0071000b4044410400100140c03041c050710004004142d40461 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 901268992 1250 901267742 901267747
    0x9060904020c0a17040f050616060216170c030306120f070f060e0f010503060f1c0803190b01090b0f1606020909070305090d030b12060403020a0501050105090103121116080102 77
    0x1810101e032948124800c2c130400481c00c12043c80041140615441194000e0301c0d0307150b450502c0021180312006140000340002d000092101c403200405a100e0840ea018000c4809034101092610312140b041c00b000c03900540003840000c89510345803010648000708841540c003a10301010f011414280e07260040c2d400414200c00500c0f4603507002400f903145402c03d81c1d83c000d07241b80c850300180007404005c1c4602d20445001a4076051074483c1204403c003610800c00300000c5116a01e040c0c142904112001c101c0e038001c1800840000c0c049008035640b100040e1914460305041c425400d105034840c101c00f40324250108581d80c0003401545040501c1400b900d00103031201d100400b007241d552000792841c400c140c00e04051041740e0001141450f0001114140015546035500226946018050700408240908030400050680100d210805184600c2c020807090b80c842040208016003800040d11080e0a03502c80001c003401511803071104280001141c401100061105202140c40c0d000305280e039401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 901270242 1250 901268992 901269013
    0x804080312060103090803190e060a140604061409040f08030c041e0b0a0c020415030605091903050403080c030903100e010e0a152003040b04031704031409060904020c 73
    0x4041101c0c1c0c01c0301c02460103000a0001e40c407405150b000c054109400280d10754241089030f40316501c106060300005007541c0b05490005c001c2ea0043c2010780350810b000316920001a011310340782c861b010998400c1c0050b104021a030405101c0701c550000c000f00c0c1c049a08103148004100003c0246200d11071080a2035600c1d814640b884103024054100865503005510040c003045420005644078100390385044006c0c69041c0c00042d0150106c9031240c52140444100801400225000544504008000c1f03444101007170516020401942c1d402500041040c0000e0002400741c00051819031074040440381801101b4001038244122100c128803001d540c2d0904280030304081c081c0f40c2c03034a41600080d01081056440b48404a0140b40d0300d000c0b00c540c2d6003046d89000f000281ca010603190040c040e19103038609407800c903202000644080c0c0c0428036001000d079144024941c000d11880d0702d60303140001d04140305042400c1d170700f01600d2aa030021303050140705805d40391807002c2e085680d42c8000034928841d5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 901271492 1250 901270242 901270267
    0x30b040c06051306031808070b070315060219060f0e060403020607050f0706092a050a050a0815040c080d0513050303040803120c090402041211031903030908040308040803 75
    0x185a48101c0901c5001d110200650142c001c11004440c82400e0200d94040d4041105100c0880500002d00c40800815404144404801c0301c0384500e589881c10407480c40c24207140c48540d1158072681006900c41c1e410341e51090901d1407120022803050302d01140042c100b101e06015289201c503518480c1d07201ca01000141076040020301c2c3c003c00c0f5401c1451801c1c4204440002520421502614091b1150740d042e0410840c400e810319141100c2803241c0212140e04058020650300b440b900c1c3c4111a203543c04141440e00c801103100b1604001c0050556040020701008540c0004000360344860b041c0c1c90001c0c0d00d03003041c065040c4001e40380d994140c1e90541c580311044003102c0d40e040f440c0640d20a00091080c04000012680c610300311600084540d41c034102201114854001a1170308940045000540c801140b28810100340c4240e2110703507055604030034966161080388200f0510840c0e005840d0103e402680021855409485400c0c0b50544a4607880c41561180d4004540d44d4800101000c1180703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 901272742 1250 901271492 901271513
    0x80d0c2d020f0604050d0b0c1207020304080106090c0801090e010603052d0105090a030815040c03020403020f031f02160803070e01021b0a0314010f1a0f040b0a0b0304150204030b04 79
    0x38001c541c42c44c209402e08000c07031820020554000c21003442c50307002c00c0b4a06000000e680a40301143c10303a098038504100001d41743d4015210f000101d600741000031407248001d006403c50302000303681703072281c0d41e18001c0503001900301010b80490725542d404000c0080b13102442550258507c01c660180101d88001903259940d0325031104c2d00e80d41c0d14180600c41100008079403a40304a4061070104013585800040d60441c2842c802d12950040c58003040c0110b0b150544c01400440f40200e8100c2c1c0c3e1803e200080c9900c0f500740700072006020154402c58003c00842d64081c240403c034004507140300c812a0b95034224181d00690320040407030303030086a907000c0c1e40c4d041014007200b03c00c42c62041024204140032413080340c01800001d14040d00d5000000c40760001350700409550300120390920202280981d4a140d4031120080e403401601110695005030509010b070420034400504101d03e60741c64050100d44940010b04101d83c1c110f10392151355a40003003400030304003035805000c0c0703920642094946044c182c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 901273992 1250 901272742 901272769
    0x41d030a1106041e0c0f0608100b2a0f06130c050114120711061816080307060203040204061d09010606110a020d030e03030f040f0807080d0c2d02 64
    0x3640300800b00400113a440300742400c0d10703500c07007001e600120483c544489a846283c0007034119000c0e030f041c00102240c0c0040c0250282038007140c29039219460310130403403051046075090701d01e01c01d0300c160400180304190804c6086540000a8079582d4801e50220750801c80e00340d41c4042407007800c11700c0030140803020792135400508090a02c2401c44481245802060042110341e076172120070000000c140314001c0317070081c8c0356141c400d00740c50503490407e144443c60700c03503400d40d030f0000d05c14080581c0001c2c40030003900c800c1c3c1d00c609008500304541940d81101950008004030381268440d54001240c030f50124403950014022032081c130700d0b417400002060031aa01940140100200f649550100e480301040003810540c050700c0700403181030607090554029000d01183e54261000103483c80540034808090400c1d50f0000d000491441d580c0c03c0c11a0307490540c5d005140454112170001441e540c009c0c082010864400c020f07070322107480c410136161072035403245d10214081c00f00c1001403421458222914003d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 901275242 1250 901273992 901274027
    0x1003110f01050421054c0905011b0806060d020c010b0a0308041a090d0f060902120a020108340e2e0801031511090303130305060907080c0402030402041d030a 69
    0x5c02c8000c6c0f00340c00c00791040d03130080514403240c007642042152500c680d1004c01c591100c01801018490f10740780c2d0003009000e81c0c80403040e420580c900380f07051040c2c0155004060003004d46007001032403039030301009600c40b05020119660798100344803292075014402000b03600030114a600c4a261110350480c020000000350f50208041010040541c1d440800e003180581198000440010500d8610010300442c0006540958000c0d540d107104c2d03030000f8011100c0c074030070390320914a615543c0801c0d20311015118043c020140e80d51288001040249080040c0031007440c100c0a9480c1c0400860240f0943c206c22001d085140700000e89070101c034200104204182c0e01c5c00d00c41c50361542d280c40d180520300c3c0d0300f0000c110362990f003022000e0304068107440140100805603940c80a13555248503903185644002c85445c0140780024148400c0401e240c0c0445d0040c0e00541a42c90101c0e08000080d8002041280d2041d5a51140503a50340304488a0961200c07240046580319079458007e0218070b04507611118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 901276492 1250 901275242 901275283
    0xa150e0114120c031f0b031501051806030606010c1b06030510050f013617120a12150806090609011a150904061203050307081003110f0105042105 64
    0x30545000489465040303030510300d038015841080e100070181401b071554a07858401c050701210050408000e00d412144219075030510810000c2c54040300c91801c0701ca00f075040d04203d0006810394080c00030421080d201b40c0c011f03444992034811a0303084554503000314000035039490070402121605160103020300400c45520041115080008208502d40040b8111030410240c2c005495900a0800400e1b04051a41148034a0312a2003402c1040c1110110380b116108c0d0940410500e0b85100c101c420400481c0e0b00e20944c0007203002a040a0000640b0007102c4005c02040001ca90f4818019280980c082102402490401030400d03400d607500c05c600a441000100c811104a0340d82009050f10703419600b4031103844941c21000075005001c154480c03901402d030055501c04050340400114443e01807030716504041c1c0c445007108008c0500b02d020061070400c140c540b800d11841c1c013102c0800312190501d080b030f24103601c0e1015034160a952429407800a03003c102c8910801c00700344081002d01107001325025 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 901277742 1250 901276492 901276513
    0x1f09050103050a02120c04060308070c0e0c1b03040302041e0b010516030e040f020a02100501061b03050306130f150801332103031409060a150e011412 66
    0x5031207200f0f68600910a0204181c805405407081c00396824110000b002000500d940b402c200000340c3c0000070072180e940f11000041050b5801451440c084c0705046201c60a01101c049a841001c044050071940c900c0b00784400001681c46001d034000440c1c021255610000035101000240da0000420a050003000e12224035200c0e80600c203900c2550705850030040711a80342010400030080880c40c0740d175450000030140758464002074101c0301c0401002080000b40e9039034000302d604c0c09074020343c01c003414500400400464850b07405583c10110051030381302c80310350500e110400c42e014020905010b5403507140a01c1c0d070300552041800100080c4000340f0000c0c0340b0707201d80c5084003620309104500013a81404680c2981e204020f0002611001f40105a0a81c9165103284501d40102044000908048010031009040c4240354002e951a000902d02ca449604444000d010340103815503602700d125800150143c00c1c2c0308094020429415000d43c0740320841c003440750902c0e044050410a1b806148d650 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 901278992 1250 901277742 901277753
    0x10020a0209060f0406170307030f14070b06040b211203060306040611070c0605031801090f08160218060f0603042004060314101d120d0b091f09050103 66
    0xd40d8408411149103496918100004d0000c1209400c1410407072210000700d080712800200034020305000e900d075803100c151403240460b4010000c8404120745003003071200c0341c0000c00b410b031a60380000c1c00800c0400d902a924003c1403400e5440008140c41c2040c0494019180d123050121500d100440d104891441c5001da001c41c2e500c000180000b00038a81e12544050340603006800e54208640c801c2140039200d40d0303800c0003040d540094031210400341c1a111030070514101445030b61074844e4403c04010904071651031f042010b8020b19450308100300c49070b807504016500e040802d08500c1408104c405c507801c003d018400c0c44010080581e005403010410f210205155852840c481c0084952018400d0700316000326000e003186078002001240492408210808040b071064204007030b0041c03c01081c1c400b2070390b400307c2a0315031907907043c035030002044002021002d0009240c5a80003560120341c2e0184240410494941120020241a010410031116050301c5290713800500da5440c040c0032550654854 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 901280242 1250 901278992 901279009
    0x31309050901021e07020103110f0a02060601081303030c02030405030d020105010f0509100b1813050411031f051302030706210219030209210f011506080714091e10020a02 75
    0x44411130109007402168803d802c415208039410050ba40ca44640035201802c0360030526017240035001c0c00d0001a81d9510503420308c0d200c0e50b850800c00c08009803681b4280e000301300c1c80440d03400b140410040031820742c03010414500300c02450b60000400b5854403881002c01080c079040248101c2010040c00385040c44640c0e8942510540710105070b4030084003510b4088004074000003900898000c2a807083d403a00f60380301740d100d1405880c00030481007450302050303110411901d034170f5044128a00f4844142c0059401070b540020700b4000c0781402645a0000b92404200c0c1e441100001da040941c0300c500540d42d030f00542c91800401003541420b0326a0b80c21410003032090506c008241c0d011400100d107590b00010708c0344a140300d2400d8010030703015044e19a2a0345140745402c0e55036080088000140100c8803180045408580d6825003640f20040d08994407408601c555a40000038040d080f8035550b10004c8000c0095107103000c04820038144280450542a4107252044d07400a100741000b50b11030f07065 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 901281492 1250 901280242 901280287
    0x20307050f07151202070f1a0a0b0108131a041220030301050105090d0b070801140306160f020a060c050406090506160303111b0d020f0706050d0203071103130905090102 74
    0x406400342644092098020700070054044c0007d01c00b00140c0c01031207d03021100080c145030306d0440c3d00c030b603660407100390a907815110b07e24001a55000021603041c0320f5515045a148101c0d00204222040703950001781c0f20041e01c0554100c0e441351020b84403240c000f0102014400b00f0f480c034500c903c0348038160380c0d101e0005100c0e0314107200b030000c1c40b261984d60300c9010502c5035a01580c0c1c00b010b810701420051206a0034014000034028021000120b460300003000361081181010040300201d103810221041e0421000020551003030203000c00c0000c0b6107001c1c5000502035507985580b141d10380b140090201c0b00d1503010718000c01041008404420301304240c0209503405040205282c420090060100e102e44c180b1180380c905902c881c1c550380b40c03002c218458a0301c5903600701c074026040b10899036200c0341c091042002242d0100031402d10f4070000c0e005543d0016483c100044c1c0c5d0a400e680346801d55018417100319030583d08032030501c610f8145124460300600890021401e0010603035001c0d01d560452107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 901282742 1250 901281492 901281497
    0xa021309110909091c1b02121c1803230304080a0c091406241201051e1c0609171b0c012a06020403200103020304030516020409080a020307050f0715 65
    0x45005d10f20100c0c0032411b1680c2c560284c03d200b40342040c80000d40e111000c0c4e8000c800000a1600c11000c030500c03403100550309c0f106130740e4042c402d00d24555400c0d030001160b2421520340d01d2062050419483c045c0081d20061000301d000c1c003503207a40f603e46000f1032003e40e0443c1036620700c0d0071803030100910740405060380b0140503182210b82d40c940c400c1c0d482c04a0340071000b400d031203d0f0015210324544104000d40d07040795000c0e2160720401a203228040ba034102106200c5800014403242600308600d1040e2075481c4d136002d00000074509880c1e403950a5121203104004a00c2c000c00030301c1e1070912000440c02481d03070f40c04202808a601184000910524812664a0200c51030342e4010a007080d1001009110079800401150750f0356481c90801c1503410b00402d80c2d010010658640b0700c16502a000301e911983e4956505454804960781140e070084c1340c80c0c4c0980e0081c1d5110420400208144010300050503039400440d01c1c0d41031882d00c4c62800c0031070540b008103500940c0c8101708410480e010480701802c41d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 901283992 1250 901282742 901282757
    0x30f0402030c1e010207090b030d23030a06140103091101140c25060c0201020a03110313030b0a0b040b150a0203130612050708040b0a021309110909091c 67
    0x80c00024641042e80722190f0740111108014064009003541c21880c10f0820703020f4131081560b0740d07036510403aa40a040d4a405070440729400345e1591007030001e0003017841c9d0b001114807480000f018880c600c1e0001c562451400e40d030340906000101c001c000c03581e0884c409107000c1c44540210340d141c04481054400c1507050100c0b0426850915101100741c4840c0e10408048a103004000504020004021070550010104507400030804c1352003030f06103100d42034042e0010308031100255401c0759030b002c04c1000040e240c081880500882c80340c0b08410801103006404078041070a00c0854103045075144406148030710b240c4580700310180c454509120380005281c1d04d82e901e13507640e20026400c51042c800f00c4008a0a051400305400380c120b280303144071910318601006182c2c1e44002c2603c201c941560058030030501c10000902980f960f030006d22205c0c2d450b2516070103407aa6040d581040e51104094003031000808907100744a41030640007281d01c46000b02c0107024007050302c07001c02c0100c28684000c3e01040180c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 901285242 1250 901283992 901284001
    0xb0f120c04180501050a0903200c0d2a03030306090204210f0b2d060108130303061a0c0f121c09080a03020d0b030f120d1413050d14030f 60
    0x85000c0d0b03401d550400001e102510b840e001d21001000e42030012004070b071a9911840e2261440c0c850308040b034408030010104c40b8160010041003110b85c05013200e0241c2d203118003603030305200c036030030380701c07210300b03000741c0d04112402c5250150030703100650070041e131281c07041c8000c1104011aa4000c1e81d142075802510340c46809900b45000f01d461400406000146140d050041490b2000d030300c0012401d030034211040035540e603c074031806800c0c02d4403010300144039030000c503451440b03044541c42454480c0c203001804c140d84202010540108940f001110764ac0481c260014080510050307a00e480c205014001c40350080c030031104076015032243e841c22212442c001411810b09a80402c4055821182042d00c46641120080180d4001c0720140000b0f8100140074406040005503050002e100e0000380c44000c041200e00a0281c01409005642503200c12500a03014860b0340a51701480503c182c56030071842ca400d010780313003c07040c011030810040f542a8101d02c0b40c06141c280c0382c200c5419215410389843c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 901286492 1250 901285242 901285271
    0x150e090603030f04050d23030a080705030103111306150c030201110c1e07093902030a030f1103070e0a06052104050c04051005041d0304061b05030c010b0f120c04 71
    0x2c45030076507807d02400e0701c2c07a801f2014000020b420308103220364034903400d0b40c0d484030111441c1c0000e01c00189008014801880c403403030300e41440c0c0d9006a09440005095070b4509000a2000071840f0001c003085c014098a020306a080c061209052070513420381d403400301d42480e880d0b506d6031080c900070203141442c036212440d801d060001c2d80c0244100f200520056518489481801480400c56943c010000420711203410205003c9800624650051800d052101005070040c000e5104130780c1042e42d030741e00065a14403000c40510300230b51580d41d410010004100500100c2c10440e000101807080600680110152a070810940c0030011007001045480340d142c81031070540b068801c3c1d6841810801003081da60303801c608420884404942c14001c0380e4082c4040400310640c0001910315800c2000b00f809060b015024610302511500d103581c0e0307180b1094a03000c1c00c541003070196280d241d441d0304844403645400100440e84000c22144c0120300300c0841002d690b20100340d401540900e07241c0030340706d84110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 901287742 1250 901286492 901286513
    0x130504081b031611040614030604060b1c05071d0f0a0209130513060605010507030509040518070b0703080c0913050721020c07080c0607110a150e090603030f04050d 72
    0x810b410081d0303403043c4500d0010115441e404049000d64600303800040c0303c862520819440c0d07100640603042d1071f265a115400900302070154150040c04010f0081011907000158020300c070b0040002c0e02301d241c10280c04000c0498900c4001d41003540080920a408402400c4c640e0024074010780140d80e101050003081d010041c1c40c0d4584540e030704e030400f0019510319408080b00024880c1004110158541c4015140c0c0e0068103805000100b051010503030030b01701a884540c202d00a80c0c6240044100c141c0328030302c1c10301c80d82c22034100b04101182c0081090b0300710801039080301510100318103011520000c1403a006000255014140c4c80d2004921242d000d00e1000142c0320740c0d540c6103050b001c6106510f601940c001000311240e8864a80001000000810080440000108818540780560301c4800c07000c01ba003c00c10303900400b042000561003403940c0010900c001c03e80c032103400307452000d0200804204001d1440b4004d41040004080c11b003481d80440d000c1d01c00803075203501920700c01d080002403c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 901288992 1250 901287742 901287757
    0x1021506031609090203163006110a02160b0d0f0608060106050403020108090c0f10030b0607060515030f0717010905160e0a0204030506012c0a0506130504081b03 71
    0x2200491000c0b40100f4641c000702226402501200d0b0a46a111100300c06a00341e8880c0400300c0003140c0040a120358842407503480d40d5081208000045a00d072100d0b41214064885605a0304000a040400640500c440314165a0040700b9840c2c142c505145003100f0710801c0d00b0340500075502c14a58480c00e100742c2c4090301815505007251055030312880c010305903901c2800207a0204481100040e4030140c009488904040081c001446101c00c20050160500c004401c9a080c56100e11045440b91142005401202d002e07040c04125420a070030344061a074600d0091900a801a03151462528000207215041320050b00513220f290b8501e1000b1401866845001400d03402422071640d40d5540700d40307941c02a640150490b441548852800704224440c40c400108281c204070010003610380910841c41d00342598462a82c002c071714076561440c3c04041100c001482c15601c1c0c1c1800040c1c20506682410700c2c070311802c00c010f507040c2a1151007050107500706100140c2074501ca0740491110910548022 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 901290242 1250 901288992 901289023
    0x7021c0f110a080303090304051903150f2906130b03090601060f090f030803070c0602071a13020604091d0d11010b04090305071211030426030403020102150603 70
    0x4030841c9001400450a49aa94840c460034003012503051808000c0740d0007000c4a40c02149064603100601004050041060382044103100f000400710390501c2e0615410b1030010000039004904031402421680314031269010500524032905070138500c12080600060100c519a468240810208070104400c3c1c00031480d444020050080c0c80320005030b030f60305039401900e4806814281040440780c866441c030500074641407043d0200081001e00c002150008802d1400c514a0304554841d041683e1200c0c0048840d05c1c031044031035a4103003803580f40c5504802007007600d00100c000e680015a031781c001c41c05181281c90790b40d42000f44000350783c29503411214140d400d444002e120214040c054041c2980320300400d500702809543d1601e0301d07106150007198952a040e0a05003142c840d01c0c420780010344241c06010207040d100005440c100003a0005000c01e0090341c00c18080c3c2110342a20340040640e05410b42c0c024041800187e070040760351544031003006421821a43d0342000a40b510200070500d508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 901291492 1250 901290242 901290263
    0x3070e12120306042412060f050103080a0908010b210f1c09050102030703091e0810060f09020f0f2503110f060f071202071704050a1a07021c 62
    0x508040701000b03144150030441d004c1098100c45040040e001c00d01d01900d260f280d46205c2c00f80407007a4401c2006200e10f010b0f40d40050714804035007424084860a030820f4400300b0000c58548107a40e8000c01c410058482c0f2002880310485000c0462940301c440e00800064024030516840398040411080880107950400c85262110040d4500380704081c408801c0b0004842102c089040c1d4000022134541e240d00d44c0d01c0302e060524005070391441c2905404032510250340e034100000c6a1000700031415034444c070a5000108145412030410b02d07861154000103500c0e00520055450600e0a41580d50404441410703503036440040c2040700303822a948402810049001d041401403680c840892a210409081264107500020088642d240310803608040010818030004000d207114200c2101d01000c289005070034001180e0341d180300d00c07441d5a504202600c000c50200a10b1a0141e1031314002e09400d24005044400408940c1d140d21484401a011380c1e880c0401200702072110b240c2c2082d40b904045841d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 901292742 1250 901291492 901291513
    0x30e0604080c06070302030606030f070309051e010c020105100306090c17030406030f0902100f090f03110418031d0d0501020c0c010e0a060c14030c030d09120f020303070e12 76
    0x1c1c580c00c40c81d0205100e2250750b0010b001c8500901c2100d0154400600c407a00b55981e00c0740c5581d809000405805c00c1503140c060f0400028402c004151186400782100180b2401c0038074424210380f080380400085a04080070300084d084030f2080c49003940c1d0407040c04100c100650810355a80600c50b8089189480703d03034904c3e6003a01c00400a08240c401c0c5590501c17540c50440b1141e016500d84900c0a9403001400c000109a580144a15101c00301982040e00c04140d039408800892405a48182c82603c803040302071102d45014441c2004160341141514a11802502e005040ca98904002190712001d120f80104a6803141400700310b2907409002995104071860b0204d80310511305203114040f82510031200c00a20b054000c0e030781510040d541e140c00070196a214011a40604045003645005c10040c00c0600c00c820710041501d50a6840041008506c40c604003a001044448000130840b104040c8110168003000722500b0038510f01d048116400f01c100010500385c0003024813403841c404d207141c0d903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 901293992 1250 901292742 901292753
    0xa11100b03060a0902130f0f0c020303040c060207060804031119111302190e0d0c0f030512070804060e03010e010510140d031e020102210a0c030b0916030e0604 70
    0x945000d003003a402e0701d03031070f84500c401081910000f8000075489090004650034200c06544840c0600c440c50101048888641003490204c07201c009071200107801c0001080700744004003083d8001443d0f1480100540d502e400b0005203204000340006041001340f100030030500004101c00c0d8031924840d00803181c3c10005181440c1160582407101d4051950800c1c00000e040740d030b1083e80c014a226415001d11101c0e4590125489981b0114042e4002180352100001c103500b00400e0003c0c050009448202504508156183c45020040c104442071700300818000a01000c041d18101c2d4194140501c42100100019001d4108142909919071a0908100008400c01440011214140c84010307014080d0402d102842481c0744001d004074082000059042040e04030469030703401144001410109007410507a102c55001c8031007802603400200b030194802103071007081c18038580c5003801c001c0241708401086017040c0042c407005628103255401500303c5e009400189061002c24240c680c103180c14a0b00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 901295242 1250 901293992 901294001
    0x420903020105070f120e1905031308030306060d091401050403020c15040b0a08061c0c03110d0b041502130f090b03060405032205030307050609010e1f020a1110 70
    0x2940158240300108101038042e80038209801c00310350350301031001d00402195000e4614050054064403131460a20f0095141080e01000d15110758081c41da5551030944d00c0c900280c55820040c0c454000b0018003c00e07079070380001c803a42c402c0310420205030f07111b10382002c0714803240c0c0e4102c01003607509100400c0101a400724079806030303c1d01180ca40d480180f503140240c0351070040b0300404000c90000c10220301100d002e04110703948104007d00c1101d040040d030307420485503413506000312050360584c1001d008016101417014a00102036803991401105078454152080c030140c406024207955245000d201c24a9804a40c0c59052140c00b582615507112485041e4030403038895031404a02e13080340e01c40c0c0d40c90b011074194000c4e0b0b0418015820000c080d40500ca0100c1094444d0301848540d5900081645090004d005003074003440140a41c0c0c94681481800c3d2451100c0c035901a40003208840ca00c1d100111040d040d0040c245001038441c40d815009a8105210325130706480c51003040b8144407906010b800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 901296492 1250 901295242 901295261
    0xa021006060c15020c030403150f0501092c1c110c0102030319111312061a010f1d0a030f03030c031b0f270914010342 52
    0xc000c0180e4a210450305402c59036001030440141001c1d014034035020360040c0660408010550b0700d003a542c0c1d920308600c1401d06140112403901c6030300b043e00d03102c0c513449228014603a1583c1803001402584501c149203c41065020900800315484445000308004403444040004107139140032013150006072903541780c070740604410700c0384003c5841c25501c040709890082078801070751319880d8452032000c0040d1072802e1001c51048010f0010702d12607400d02c0080802040045401100041181003500580700c6821620401403240008420300c0d90303100c1d443d4030441c4128038107040c1c046144c5c01c03440b000801c0400c50a40c41182c1d0310000c8140414420408111403180d1020020400000000d0b4181d403a84608061141400422040600d0080400d95070703001e158605102c01c40c1c8a1462200c0703158090004c8140c144220300c2c18800e100f414850720f00d2101000102d01c07200d615690743c502c480307801e400300801d0000208a1420041410044c5c3c40b4071820301c0c41c00054203028240e00303030005201850 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 901297742 1250 901296492 901296523
    0xa0b040e010b0703090509090c06040b0909100f0501050d09120e0907090f0b0f0c010f020c010b06030907030609020607080a020a150c080c0319020c0706020601060822080c030a02 78
    0x1400041c610b40060103c54540354182c4403200c81c40c2c0381c001080014000105055290f009104071401c150350b805c0003c002802807003074020b4580310107005010b40720f40010b11048018000041c00e101100e00e40340841d080380c0d000d1801c075070742d0034904030194064070100000030144407441c09150b1000d500205d16448100095840e440d00760f0300c0c040d049802071820700c151140890120414015011403a005040007062000b4061400071000b030001d003124103441142c100198081140302c0030707483c28011001e101c102100d91700d00b03500b0000c504948940c010b11000700034030b6481c090507003151501c400341e44603076030001d10168440400b54006904c0d00084141150039103681d000308a140c0301188920342644070156036064240e0740f4200002140d510240244034900b0480c441d9403400102400100000c040000140003200d10b0a50003a19142d01078001c4424407544108000784500090281c032181c50001450380103420799800d0042c06440361940e01002404001090748002d03400040c1540e80c0c0082e03d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 901298992 1250 901297742 901297769
    0xf03090f09010f120201030e1621200f0303030901060315051909021c0305040302130204050306040312020913090b010801051302010c1103070e01030b06030c0f1e0a0b04 74
    0x80400000020034001c3c1c00c84440c40ca0001e004624400704940143d5106040004072000024049803500850150000445505c18803e00c0034581100883d284108901c840c210052040d5445501d00c1d14aa20510100118507104a0741c0e980c421201020040340a81903c0c0d0300d08040d40d0190103011640030a46219205107150009042e291003000e1041e00c4140300040031240c801c91410107007a10200590340600e000e90408060410034210341201842a1211940c4902e14414800d03464074011881c035140b841403004010644022404503030141d850b00e4030070a03030f5111745030241c0280104121581c000419402610442e402580708940d2980240e000400d20381c2c0e5003c61900307070b600460b541071030030505c039001c2d034015401254a0804035105d0001413007038003202c030301082c5000707283d522003015001003400400602c42c50f520003c4c1c100c1805e8001d4404180040301040d10300aa44074024081c0300310800d081c80d50020883e003610345c0e9100a20426600d6601c010801042e0054000d01c007038803811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 901300242 1250 901298992 901299019
    0xe01021317120a0504061b2d0516030215190507030c0803070f0215060a060c050715050306360411030a0c06110a0c0509092b081e1602010204080f0309 66
    0x42c41c0a08100305e60102c0582101408c3c1e030100d21009521040341d031020100c41039480f00180051114418440c1e610158040c524690b004000b144a81c1c0c1040070441e90003088801f800d44610b0001003210364490410b10303500e400c03078074003144c0345d020244018020207008414000100e0b40103581002c0070001d942103c100341000c0f01e410702c19003c00d075407035a8081501c010401c40c0b14002c084503001e0a0150782691601070f51102c0c0740010900b14034445d40011800410411580f900c1801d8485107035020701b1407205526074804100354020b081c000140303001081da00140401000d0b000c440c482200c0a815540410184e01d0881450780c0240146d0001c5488014000f4903080000b540d07814054001856106181c034000500946800290050660f40076694060500d0380079011802c605600f0403c00ea07031140c0d00164000d1003400b0243c02c0395403021101248682d0f088402c4006070300460600080c0103c4078003003c081c1e0091042c0e1f0711a074024080c85440d44800da0001c000b802542d0825039030310030340c2d501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 901301492 1250 901300242 901300277
    0x906040e0c0907110106031208100303080402060f0c16091112010302040216020303040e01140105030106020c09091f1b140a081e190e01021317120a050406 68
    0x40445020440c0da0040011503828a840e04000790480d00301d0030081c400e000d00c8900c10b42518610340041e55070305682c2000722042507101c00001d610080081c030b069419030035540c00400074a13001c0d20292080c1404104264200894011144070b000703440100c0e91400e401c0215251031180c1445203402a5152164001c0482c130820102c82c1d048000c0d19003100f85a085a0800000b03400210041008403520038200d070060b1803c00081010b000714103036a14507503144c0386101d00c03c1031410b00e02c98100700c1c090004018450300018803066a507011140f60300c0c1507072a0095145440406010f200400c1040c003003000425616500c0450454004003202d44116a4004180e41c41518002c2c501041d0754101300c4034441a104906150b00044064094000c09040c2080980c60a1080d6204040c4001401c0d0b41850701c40c00c2d20030406a921944000d40c10903008140700910a6010321807040c2c9104684000d054601c014820301c40b00c201d5030550107445800c0d00000904030740150060074049038582420800810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 901302742 1250 901301492 901301501
    0x606090a0c0e01050c010e1615090303120f14012606060603061203120709060f0206190f0e060903040333020d090f03020c01030f090c05220204030c05090604 69
    0x700760300d81c1e0901620300001140e0641c8071000343c0c04a5503070340245421007181400b928643d8030381a1849500e490030504c294409100b580007960030f00050600070030000780c02080480454107107180016030200c1040010014040c04403c042c1002604000450902c10181868800d0a2503280d1001e0720600042807982d107490a031403c0e0360120041c80014142e1030320105803100301c00070f9401c0e00d0404a00c0c90380c50200440644000d00490745001003404140e60120340081722100601c001d0040d030500f01081c0d0201e405c0d40c0c0403c600e0301d80f900701c2210984a9500300441517001c540469181c4e01d03040d50313150b40307a400c140000c50b000703020100d003a040d8507107801c100d003010040c1c85555050081e414180400a41c0284c50460040e074480c5051000b240010703140e494454040c1e0050072000021a0005045500d5401c003c5c4003a46480003a001003018413048a0a444040c2e40343c122540314904021001100b01c0206101c40d0300008000c0100603041540c0c40480b84155424074141e11800100825134 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 901303992 1250 901302742 901302761
    0x1a030a050616054623040b040f03020a120302060a0b0409051621200a030b0109090b130816080417010e1002070309180f020c0606090a 59
    0x29402a00840d00244504140010610b928200a49402507510781101c2d5a000041d030f00400044061400b8407000e141d50030400c000c41c035005201c5010f5401400540080d003071406070315403440f040502c54040100001100c0140c5078454620391620b03560504440d5071001804100d014949045000400309400c00310068095070540103130030780c2c0d0740e4194004018540300c0d0440390302645035041413000c1901402442441c001d913503140c06c1e6190801c08070010491000607442c16144003001c45401148034061302e141054038008501010300c0050002910b8602540c101800c001540000003e4085090740700d40592489003800f58015a54603841107050340300132601404400c030800c290b801410342c89616550b81846665614246600c1d80c07035210905803884188441a03549800514007034001b00a409044003800710294948802598010001c0d503241c030030306444a220340c0412001c1c16003a00484041c4186480c01c549403a200010555074001c1034403c6805841c110021403661181d0340951303c0103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 901305242 1250 901303992 901304003
    0xc010e1504031b0213050a020c150603030a0804060e4c050403030f0203090c01020715090611121303110a0e0112020d12030b01021903020c040902130c031a030a 70
    0x201106450a1100081c00f0880e07010701e815800c0c0700444000d22071940900000000103032030300c0a20340007507d4030000c000c1c0111001801410801a95000000c6400340300340b0349400030183d103c038030f4040c0182c00c14a8205429000c0c40b2900488442401229001d400da1074001880d0000c0880f290003103803042c8647d042110115140850b0042100d800030307a0428030910303001440703501403200d80c2d08980040c0c400440b01c3d04058404c804540c1d040103050090f001210318488024800200580611010b1203880c051000e54800b14944071030500c111648082648902c0c1d9441130902000e642c0c05010f400101c45820030402280340c3c5090a00104055030b40c0c090340c1c010181d09140c2c1d2142c141c100d25004036480007601ca816000580c3d0350380d4103189401c49840c003044400d010000681803a81c000c944400f15003000313103000301082c6c0c0060348401c00c0c8815500000c081e0b00178004a1201c01c203000c0006001030520100082c5580d05030300009a0410a00208000010310010152a650b031203201402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 901306492 1250 901305242 901305257
    0xe07120c15050d24240509102322060509130e0309120708060f090c090705070f030e04050c040f0513140108071a03090d0f03110c010e150403 62
    0x1500d110941c0042a072892034440f04121411030b90000c0030130f0095420248140004020009290300b58081080b1210045d0a01030308009612010460381a05411020b040006d800c040c51002603400c5100b80c410b14945840a40d0b078400717800403d0030b64032500441034220303100e90703400030300c440c4141c0c1510640d100c0200b0b10404400340c00c010708003620006401110320f010400018002d40c0d10004002c0602403507201500c241d0f45042d4000d07007860350080222050107100707402c0190051010030700d900c4000742194401219241c10000f01d80500840000800d80d80001c0ea00354141a04245610500380088130280200d540780540400c0c0e03800b8a100d145d01a0308214028000707031502c031041d07040e500c02250f0300141286040010b81455502030b480a2216001190b0511104850340e0200e20301440000116246040c00e001043d03984888800000400104002d4116294441c1c1c100802207516404c2d9651109807a018141c001d00c1402e0351411284580004041217180b10009103100725016211910b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 901307742 1250 901306492 901306507
    0x2b02011d13090c0906031a060d020d081c02120f10060909051b16060506060426010e0607032a0905010503041b0308030f18070b0d0e07120c1505 63
    0x1c06062a040216525598801c01041c200254802d680044d4003070340a17007001c4021a24201c142c2c0002800f01401019450844d401584030743c50b02000d09584101400e070b481601c0c80202240070301d0a07050103002c3c2d0000a501144007a6690164054809103402c1d24541d00e564044107180e9115101ea4004034075110380c10440346080d540495070109511080c0c02c0450b26000200c50941d02c1400850100d0350000310940504c1418851540d0124094964501c1d00e820b149091860613658017004800c1500900180a480000c2d04580c810086034001c850050500c08005030203840c07030a4900703d10180030084c0d6030316003601d403060301d94504090315040080c6013003900440b003aa20050041d10032002c01c0c80d0030709040004442480c01507000d07180e01512400e110741440b202801c00b818080c040c03140d244101041c0e1001203541d100319401004185d95401b0482c4281014000c03944110840c3c1c01100030003e8100c6920042210891003081c4071000540c440900c0d010343c8621a40e4400010014040c50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 901308992 1250 901307742 901307779
    0x102060c130e0103030f120509030405040902030109060f050714070f0b090f06040b01050a05030a05060f060d0206041403060c040f0302060a050705030d06090b1008040f022b02011d 79
    0x91241260416a05481d075842e021080480942a441240081e081a0520708459881161591a80d003402002d20250411000d40c1b90703280624020103100e6a03591000710110356007580217094040e0311840600140984406260081c441101c108021600c0d2440b040300450030042201d8a042e4040009211803500d51150500110010308101c0c0354411807003800b104031400c00c80a841a44103500f410b000e981024180581e0140c203a009074040c0d480394103030070f000840c0411103d901210030345003081c440e0f1b00c41c0b0000d00714010030103001c1e40080e400030b0b01140000007a10b0751000310340c0035421076525403034100b43d080d07046c410341c8642410740b0b00e1000e0600061914200601d1707c88441e00c0d00c0c43c1060000d840b01401e661004003107600c540c0c2c0d160700400103540715014a1540c00d4080381c082c002c645003818040d088580040009103c0315903a19417204540e01c000542922580c0072111032982c1401000102040d490310b14260b020540b4004260009031610040030814280074040042480404220 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 901310242 1250 901308992 901308997
    0x6030c1206060e040501050624031b040f0f150908120a030f06080d0f0f020c0d081b0a06050a09030504060f0c05060910110903030306061309020d09050c0307050102060c 74
    0x22101c031a10b800d400583c0200110003640994099000020030342448070400142c1030711242013407000190710100100d2003504d0015281d1059104017550f00c40c02501d00b8020443c401c0c2d8006a000381d0398488003052460004046006030703200155030440500c0c00441c161060310482c0b01d031443d540e1240315403200c4008908003034402281d032400c02217032081c0107204da802611250340100c1074560000301d40c2c02a09a111200b00030005650500302079600c01500020348603c0185c3d400c0780030704242c20703c0d2820030002c90211184522407aa90080c05201c51600540703030100510b040e22000d0401022807402c043c14861644415815182d803883c1c185004015602604a6490103007031045180c1e42101044060107010722550700c09002e02505040a41000200c8008080340ca003402804c1c020f51010340c40000499802180031200d0030380303c4100d4281c001d0f440545810a004c401d002181c0403c07801c0003504094003c604c940241d81006446000385991007909101d4180140d00803c0403130f46038000340b0300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 901311492 1250 901310242 901310279
    0x201020c2802190513050412030905100b13140106081612111c0b120a111c0804080105040c1409010509180102220e010605040320040e1b0406030c 64
    0x50700d005440d52403001031885178603414070750100c40c0c5500c00c2100b04150304090021400320f03406d08000801c0d19458072552500781246e40e2020699501d030460203036a4844100c01c003402c4089061110802015261803460020320590f4045940e090101da00020444188401300580741e840329a0000c0b0030824034050014002c00243c420010031032202842d2058400a4030160344420109884000b1020b200101504946268940e08000c0f651000070b00c00c4646980e441108031501c840c01004807000510f604244400107100403000580042d24034010f401881c03090b0b000b4040e03510941d60314145811264a02d8039116800080b05c401440b541c6080300c105074011105807040d100b4000c0c2901b0050032684140c4000011140d03a21050302c0d032101401c1c00304050006001850680d500d0010054040c0c080c90200038072000584401c6600750400601d02030078294010010300103504012101c949991803615041617100030005500340604090141408481e0f009490020092600811240c00c001d07200c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 901312742 1250 901311492 901311529
    0xc0809060a0c0e1003060f1703070825110a09020708030a0f060803270301271a0c070506010e070914240d0f1e09020f0307060201020c2802 61
    0xa01d601256101c00860510704200e0391000106d141c00c1200d528051601c6900209081c28900c082560301c91000c804d4900300ca40c00342e60961105800c4565024030f000c44010105403c4c9580380450074000103c8641c490b00106490b42800192100c0f0f2850580c412030724080c00070103041010442076415a0300000c00601e4003400007440c1611400903500f076500100710b1400c0c44490300102210801e14000c05c4108800c200c008102d000500c00c00380c10305c200c2090303a4184071002100d0003c01d0240c844211009450700644640c4d640ca061070141240f0340080a09032514400e92002040c039210342c11003d030196515444034400c00d4038090044100c4010a42c1080c0c020407903a51812540200304001940340e04103c008175203a4012180311401c03a8010001360003081c0c10b11008480410480c61001c801e003600d004003040b60302040c004605c09100400b00c040d050f00c943c92000405035070642c0a49104007181c010780300001c50300200d8118000004012000d10a0904420401441e00c07a20300100c035000d40e07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 901313992 1250 901312742 901312757
    0x901050d110301020d15080109021518090a060819050c061308070b03160201180212150a051623130f0605040314030307091802040306050c04090c0809060a0c 69
    0x4004603007a17030800848045501c0c2c03540395502102d10200410300c007030003600d0002c11a02ea415000035501c46010801c4004075000051110741494011841221b04000540b00090905042e00000f00070b00c950b106101c0e0501424006145604466582c01d4200f030300300300100295040d200070000036500000008194680b0084005043d640a001c41c1c2c000b001002e5400d03803203103044807802100c2001315001c1011649000048810b42c503001200f03401d131a03010b0381d0304d480310100060010300c0e1144000006d0703242014041004007550141d00424440c901d541c203801c0c1800d5880600340e408001b102c15a001c000e6a454507214064860070140034890511030791007505981d200e1500d0565155a040380c400a42c0000b818020b00865180d04160700702400c00552551a100e0002000400e283c02001e51615069032010300c02e150035010b840187d40c00c070400b004181030041110003194494407410014900f8030088040d468082c2420910a15030280542042d64602c0b00c114002c0140382101d900b0700000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 901315242 1250 901313992 901314023
    0x1005010f0302130e10120519030c05010e250e041719020c0a0b040608193315020a2a0e1b090d080304170f030f0f060901050d 55
    0x3d1080001001c414020748694101407403006040001c1d50804c41d83c03200400b00e83c0001a90001d6503100e000c0e50501ca062001e000f624041312415030541c40540250700b4283c610100c9807001c108944900481140e0300b42801040e003c407680300c462803188085040d00030000a0110313019052000305034180407955032030f06540e0100c0d20034455048204600581c000c0311380a4040c14043d003c103000d04050403210781031038a03100d17004001c41d20040100c0350054102d04061288022900182c1e007102c000d24900125400d201c03000d07041941e1500c030000c4400c2c00c0300c0000403004520140c9011080951f4098a48441f254541024442c4000848548084016000910b00381c50402141c054180c0d00520f030824106140e80c82c3d02482d00c013a0103102c0b40010040314449503100800140110351082195842e50f803241024540e08a486e4801481d030440000c0701000307400d6180045110b00da074030a0300366980d26403c4030460100d03021245590005032010040c041440c28410407178800c2d20400f0901d40a220 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 901316492 1250 901315242 901315267
    0x2010f1b2307080f0d0c09030b18070312050a030b1c140705100e0f030f030a0f02030904050c07050f03030c16052a0301060b071709010521011802031005010f0302 71
    0x840c1340050341c0c64a010543c5115100746006220100d5007501c1d00030840c80c210307140c5044107035003d0030940e50001108500703800c0c0d180c02c0c0000c1c3c0003141c125012040d030109060015020754480105d03807000a1421604540714544011400461000200d95100d40b0540c1c1d0340b560030701c030304002110549205a100024059503010701148240030f103590707650704907000e20003071050044000600ca84a80c20007000049101400001d48002442915107080c0c44103220300160f027184504010036410a0510701001010345800c801441428412002c541110341040d442c643c0f6800700341c8103448616000c0100c0d0703030030011000b070001e00c05019100381c2e0704061404e00c1d4111103010751103a01c42956512041d0020303510b828841d14004090608460303240c410180d550095980610007220785052020a920255910a1007559006180d550141d109281006131f000966442481a00219020020780c00c00c00301050080e43d004a055000e085034440c1048015030350446540815070405509000740364403041c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 901317742 1250 901316492 901316497
    0x3150b0316110f0a020603060d02181008120d1e020313022706040504060e15160f0f11010f09150e061003032d02010f1b230708 56
    0x10181d05960407040300c0860003401006003010703104140e07001032454082450b80421540718540d030485065560741e6800b4005401c0e011100310181d001041c12000c1800e010040098a0041030070204065080360f6405010b90b0b91512140303030000c811420b002e005100f00c5c264021440c1240d07010080c00701c8044140310318040341c000f100c80300c48103500e140750301381503007081c0d07108000e44410207001500343c1000c06640b400c219005800d0340d0207955100700142c03e010310b0754414000419102c0a542c6501d0007040b041d407405405032207010307400a112590600c4103010b1806d01c86418865110300322240c110903401c2c2c4031040200c0d0841d1440d500c41d500702400b00341911448030320301e2041c0d000f840140302c03101c81041207031200000460180c0c00302c402d00041541c02100a411a9803502d000c4c01030080039a407024002001c0720170000200d0b201000c1e100d0054064000c800c2c2801603400400961488003a002844004440708102003a00e100701b1000c400d103440c10307070649089040c3c0700905d404216903554070305a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 901318992 1250 901317742 901317751
    0x14070317070c14060105060403140a02030304060810050102011b081504060b07050c0a06170901020d0203040b01030210020a080406030c020703050708010615080f010b03060103090c1e091a0103150b03 87
    0x1c4802c010201080072464040d032511948000510181d0704090200342184520b00010b02103424640303001411100c100410704145a005c0d056a48442d034407080600401310640e03190170b001450490100c0c49520500c5a505216100c1e00c21030889040c40310140c4007c00e02a1101a60001e807008966582c0c481e07019420060044098007a030f02c0e034183c14514101002148a18807a211980d800c01c50030b5800034ac10380820051801c80d160948980060314024400e41389100b0005002008200070b005e030007000e841c100d078001d030388605d11140162022a282d00481074000e0001000b030000340700981c030a0b80050b035510520f0048607542d40d02ca03107610380f6100c0075610075009691038401c2070022441141210905210b1030805112a042000d103114116005001d0410210004000501c1c00c0e13100b600704100c8150401c000004490301d4841500b107210401c042c45400304403042000602480502c564840010003071100b0320f0503a80c8500440181508040c0c9030012821100c5c08a1072540900085018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 901320242 1250 901318992 901318997
    0x918030f1b1606021209090106030b01020a150f0e0c090a0203060a05120f2104031b1e050a0503150a050601050f0a09061206080c0405040303020c01110423011407031707 74
    0x70f03160103002071078040520382200d20302e4018801014117031282c44045065801d00e0a02254007680600100c1c64021030302c1c00642030300001521039401c40b1880e4001011254001030500040090206c03581e690b011070b15102e50025a120001a6111016400b03180c102100030f00c04901345680d44d0000c0d80079112140960b07419013200a0821560384c04002e651107505160151840c0aa41420000c46c0c40c002d81c80007824040c2c001d203140442c40121280c1001418040d400f9101c07110004110b045408424050345003d4021100042081e18002400c0d81310a0842e400d1802d0564420025801504018103054107011041c460f0000c040c0c01c0c84050001d05010795501c017907152400000501c45d1040000389000145007880501c80d452012901d40d20103001500d0226081d20759140c1103000b03200f00240030f04654a006907880c42c50311007030010011286400c0c940c0308006070641000740d414001e882250b000c1414040412480b81143d00a00400380c0282005c5014503d2049204014041120500700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 901321492 1250 901320242 901320283
    0x806060405060405280f09061409060c071e02040207031d010e0d1209150e0a2c041104021b06130305030c0f04030807110918030f1b 58
    0x105080601c10300d0742c0b0a004440c1444141000260300c102e03011000030420248540c030314100055011604141901a540b0b0000c000340380140c1080c90081501c10861120340c0080408030b000032100045080c011005401490315001041d0f480d03d8841e401001804100b000401c00980540c0d224030260048034081d0b100e850002ca8862017088001036072031031041c1032200c0800300f06019103c40740002016640301032102c2c0b0300303101208250344614455100d95000c14540f5002e10031554080040e9015150648020018540359040c448003580030407102c0c100740c0a503000e16421041d1000100350000d0040100596207070780e01c00400c2c2660f110b40300214021405181c1c042c43d403a002c02103264080c031030300c42c40d2054040d103503001880c0d40f2000d425090303181800316101e6442c0c813134001150025503129120076aa40c0c002d140100c8407810402e15240708240c0c9000003001c605462486182e19107142c2d002e585002c1c3c12421090064010308202000050400e1042803088010031991490311032212100d030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 901322742 1250 901321492 901321501
    0x50402070b010f120f030c020409051c030e011811130612020a05090f011509180501090c0c080403080d0b09131b0302031f11030711101a0f13060806 65
    0x281c3d145110740c48541d008411500c0312020801613407000441e5545403408807034a00860000401900c2c0c0c10f8000390050241e000b104400d5428621440000c3c07005440c01e005071590702e80e03560708840b01c00c11280104d150050b055400240e4488540445480c014180034030000b6451462080340e0340f03a00b21945414a00d08428190328118101c0c0c00101030440d0400c0b041d290a0300380681b049018824005001c843c0743c0e907109164010808030703000e4040800b6004503041c900960314040c003403e01c24010f43c1e51800b401c0c141550b1103224500072040d0410300d4a85010700c1e541d5001d01603032060001210081c0e4440084400f581c03002c840b64098000f01c14141120685800c24880070b01c020000a054290100360810040e01c01003841d144002c811001c40c00000070f4620744501074100c00701c0c0c0d19007004000040140c040d0f0815184811210301d00100c400e5040c1c21003e00d02145d000100084040e8207a4000d4400341c9030140b010560008043c15038101c1c0c1c0c4c61110501e0a541c1d0940005803503800c00030400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 901323992 1250 901322742 901322759
    0x71a0c040306050606091c03200a0b0105030303040503071103120f0304050105010605190e1203070c030c081f0b01110601081b150f07060204030b0c03061306050a0b090406050402070b01 81
    0x115003000044410301e1a0001e04000502c511200071008504060319407c003109050103041682d2440c00e0761140c00c00b00039018003099494034101001111989085030000c5140d0038000103991041c3c0d4040000c52030010b081d2162060385400300641a410320507500c0102c085208480034007600814014213a489041c1840e0250940d88160010001c00030f00303004102e1a04008155a640c1511900704001560200e2001c6036545203131400041c614407001911a04010843c091141101e0080700d40c07117007054850010f142c45d4000200760080c00000490340000d07a1107241e0000c0a1044141014490306813070061a40c20070030301740c0c44030138244c03c0300d0a15040781c1c032501514075141d1021500010340c640100d407420380c2c600031080e001d1050100412400c0810180354100c40156801c1884404649044480e0000a42c81101c2c40d0f0700408203c03010b281e6a4400b4040c4c00d084c0c94004107034400680c1070080c018025080080300c0c6502039214640081d1580341c2d0710062000d503000b007041903500e604000d404c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 901325242 1250 901323992 901324001
    0x2131523040507090506070317090f0613080301210f08130803190503040c030f05010227010816200705040b1012020d06170606030d09050f0402071a0c040306 69
    0x8060081e802d140410800341d82c8000c0c0e050694600300c0c0c01ca926440c083c24111000c07150380c00c00c24548040081441584100019000b0803114800e0456845079581040400c001d04c0160004120860610042c02000441d0005071030010203148500c1c0c00400e5600c8240140c2d82482e02591200c50001d0304048a40e541e0000700003501c0e02c1d20045140103190f2084280300d080085900e010054084080340421080401c80c100441d0001e1f022400c10900d81041c5000b54008000a11031000040180d032500415000014020038161601503561b44c3d0302e91f2480b080e8001407035030000c104041041e03950b440c0042c09d090b440d00c1c041c640101000380c14407090004540e00e10101900c100d00000441c4401c0e9405907401d25268541d0502588952034426807070090314041e0091100c80400707814400340d21600041651080f1804c41c1140c0c80d0741e1500e03000b039400051038041e00c4c3d08a03101c044c070748c145820241c005214052154200f40c2e000b452030284145107071020b8440c1e03841d00000103410810700c08140903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 901326492 1250 901325242 901325309
    0x2151c0c090b13091d0d08160e090708090c3001060f090207050705040e031804060b0f0f090d0b04140303010e13050a171b030405030a021315 62
    0x54900d42003c00c0480c502d030640368402c24075113075140ca20030604d41c1c1004000381c24100f85c00048942509442c0d4024010a03011980ca1070b00702000d0403000c2c01d9038410380800c132203d000984020015143e60030b08070b910b004010308240451085174482e211701d48401044036195104018004440120003506151165440c01d6080c042c1e810040c00b0301c0858002031700c2c10101c4020510040e641d002510700031781801710a50142e0b0b4041d183c184540b92010002c0300500507120049104604840c1a000304000c58445001e400c0d02c0400a001c0c8048011604004000d1024415030310b0b4181186100000d48000600300c0846200e4960428032041140b5040800a807003034802c0910b040d0740c10120104511b0000516080c2200300074004042803180611010b040c85401000d099800d1030726604400c0e65038040843e0106880030051264480c00303010007643c0c261000180076000f400016020880402031210078a041143d41d42c00200ca81908a0103407030041515100070360201c0404d0008211044a480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 901327742 1250 901326492 901326509
    0x501080c06160312110306010809010903080a0b0a030804090c080a0b031506061b0c0111030c0c0d08120a0b10080f010605031b03040f0c05011b02151c0c09 68
    0x42001265521481641d5400810b100100c203a04000d040894070b0824050b42c6905a83c034020340984000c450800030340c46035600784c842c1001038440c500c015003201c0c01d059029002800200128181e8071a0f81c02c17454000e04c2c02400340200b151240c961a45e0380d8010742c0000e0721705603551a01e1180a800810300c80d03004406803400c000c01d040c428040b070b40310b160140785050590b80200000f00a50740701c0701982c51002490440641c8240e0310703058903540b0f03030498030001c1c04107001d401c0003070485d0f000100700c0c4e0160804401506695030b9007424005882480c0504070b484440600103000d10218619107907120309481240070600641c20002c3c000c4c0605c03001c2c01030040000c00300803c100408002c4007141101c0091a25030358a5541000110440c3d07051104084060000414442400310031300080b100c09018160f4400015692401502c2004008809070389001c00205490090b00e4601c126400c10903115160074a0144410150b0503a0700e9000030107111596103400c41002550b105101102504480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 901328992 1250 901327742 901327753
    0x20406021213300308060a08011a0d052103061c0209060f01032c011406010c14100c12110421060b0a060c030314040309091a120d03050108 61
    0x700061481c0d50580c0100480000c8030b8885a003c442c014000079034110b00b01d101c81c030f0044070903e030007080b010301529001c0c40344640040114410f4010b10500c01012001ca441c14180608d007801d05c0b039006400c01c0d060b9031034000c41c02100e076000040b290315a00b60700060829981c030b14000d02003243c907200d0700c02c0c40400d444c2c2c40c035a540300607201d84072440c0c0c001c8012661204405000001200a400ea240346000c40c94060780e00c14100e20741d40b641041c040b170049002031101502a080f40058860200c444c0340c0082d04134900640480c048494440c0c015606609850989600b00e5800b030035922100307240b800080c0c59440c03500c4580b000d88950300052071524026031410385801c852011550003410401c501c408001c444600f0848554080e41c0040d9000c1c05070000346541c1c3c14040c4c04100d807600203401007818252070203000345e03128074058402c55054a9140600741400703095002020f00318190344840060000c6201340f0765881c40004090303c4c501005040e04030b4140c0e0010143e90041c2d0044540da44039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 901330242 1250 901328992 901329007
    0x20a0308040201031d16091d0a030c14011503030e18060402180a0603090c3501020c0109140d050f042c0f060108090610031401020702040204090204060212 68
    0x3000141c00c241c091a02140c40a030058481d802c088a00070151101c0c441d0030405c207004184050303008204c07036030f110042201040000d80b00513519146554070b400d0b500900c140000090051a9081c072942c0506680501381e01c414410f14219101d5459890911140c00010803c0513400101c4060810080d02e07000031310005000e100e180d0400181100380b00750740118206511290790103440c140c00100815004803140c0d00c03a00900181801001a542644118004920340c5200b5a082a40c0582c8803481041c03481d001201c0e600035000f14800481d295020085814080d200b4003544c1340c4c0a0280040b0441501c0d200c1503c0d00d084140b4400005001051101540c0c01d5441d00964045a002072241942400840610910807462181500d01c0e1b81c01c0b0707010310522038110381c05944035440a807a004020784900c0c04803030303480c0400c54000650600604040c0002402c00c0120816071644c1800542451065130010b8143e8110341c1054051550100d003c000140d81000740090f80903801c50007600d807545 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 901331492 1250 901330242 901330247
    0x406031e02190f03020904060e0a0509120904020a050c01140105010f0306050105041401090e0109050a180b040212120f0c120316030509030915070312020f160203150906010e07020a03 80
    0x20b948010f220300b071a8407900050007501210006e210040041180d552151340180d01103209a603d005054541030000b01d40b044001340381040300031154111401c00c1c13100003c21000e51f10070160401000000c1c04580e100540900920f07203948401d040964030b80d8101000100309a503000000c400f0942000010490369803c1807c450664000c0c41c0820f05400032000140c81c0c07842d40d9803040404890a0b070000034848840c1e408180643e2000d44c041c4807103a8240703403011070491401c0003c1c0c4410301c2e145c08035005203000c1041040c403502802c00e40c1c1e014081c01c1050f00f00c4d50400d003040405c004001501400c600410f02c603068a15100084690540c105009661404a11844140180340c0e8032000720b282a03404200799a0a201d00514034810203102e1011641c00d41c00c02c0b8000c50100b1010790781d405044605000395440301e06088038982c203100310407011400d05d0810400030780e014046c0f4507917040e120740303081d1396607200c1c0020740e004180755490007888003c0444002d00520441d0080000440004da = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 901332742 1250 901331492 901331527
    0xa02041a0d020d05070312080a1104030b010603021605030313030206090105010308090d050c15090f22090f0f0b010807170303010b2503030e07050f06030109020f0f0406031e02 77
    0xd405480030741011442c2e1400354a0070885d5000036010b070401030804050181e020207240e00c01d8000900901c40301c480c3c000000402d006901000b40000300c00001400218070980c0a000561845441600e8816075916001d007103034402c0c0c0740ca480d40404000d82005060b010020309810041e00f000800c41d9626503142c1e07042c3d9000e0044024400c040d41b0303110340300340002080601d8820200600032000781d00310142c0c00c0819401112051f0060700704022036440c80c41d20510510303040850718060907038400c0c0000d0710001002004011164088440054000304440c0320031001c0746841215415115410020020b00d461081e030310040d02a1007289020b0402c0d40f002c0190303411144011003c548920504c2e90040008803051405003602806404407414594190060400c02200c0b40c144e0f030f2600e44803028013110880f40d95200c0d8203c0000c0004000348c1140da4018800b1460b0701e8182c9013442d05840d5147d40552240d0b011000180d00c1e003181035109501c0c07107540c2d428680000421464650088501d2070a40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 901333992 1250 901332742 901332769
    0xe0403080711070609060815030c1003091a01090b0d030c082803050f13031e0e06130617070e042f04090c0c0b0c0906040e0106020a02041a 61
    0x3000001098425002c0c181c4110505020403d844109440d613000a2200c4158451400040c8a10010a41c0c02400111280c03148601030080e000c000e4280302407001c035550100901040694851901001c240110000c81c4258601040e03001e0a5141904000c10340c1d02034012580b00d0b419480d410400a50400051186154400200c80d290210320300381c0310b400800110082c1c01d5001007038601d14061740c036a000ca40b0590709001300d20025160501025041c0f1540c1500a0105034526000940179a002d040c000070a1080d20740200e460600e40e01003042038100e010455401c1984030414400c0f1600400c50541c0030203103080140e01c6103003041000b000484070b030003403501aa540c1c0c2c0481d40b00003840720b0140d03d0074140384800c030852130002e45032441942c1310b886100b1041b8079003a0296000c40c8150010b00d1210340012486d403075921480103c501c1a030082c512560701c00c1d010400092201036043c031460081034030b900075103d45c00b5240103100540740f83c800200080b40241402150346d907521401c08044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 901335242 1250 901333992 901333997
    0x180601060909090213020c0a0219050f06070804090c1107050d03120504020a09110a090b070c17010f060b070b100302310e0c130212160e09010605091206010e0403 71
    0xf5601c0d030020a4882141460094040c0c1c0009a1415100c0000500ba400301e03100b07855000311100b46c508100b1140c1d00703500030300e5409444400822228641807001c0c2072128000c514a51825035500400b81c100c500750190400441c03c0244965144041880400000d100a0741c0e0160b2494142e5402440c100401e603116586594880101c1d0954545407205405052900e030200020310040000f8903081d00003080140005441f9280402c090f405501030760081070703108100c01e880314180145040d07120800c600d00c01e299940d1302c020600101881c01040d008021000c5115565051403c25807050b5800409031051b48556000c1000162680c110104495003081d5111540c00c001070074036121a4814a081a84a801e1856442c1c070850003003114440b60408542030301c50780380c2c2c004c0c0c440c00380c4c0583c502c2c103011100d0102c0095620b4001001100c0205c1c01850140343c000f20000024003100c000381c0252000a0001c41c100146040c12095a40280800c400404866141000d4a84030b0140140001c08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 901336492 1250 901335242 901335251
    0xa090c02031b0a32010614040203041b1d22020f06040b0706051005120703031409040504140712050303060607060b060c010e060a020306030c0d15020a030203180601060909 75
    0x2003082092007600c071626030050380c840003980700c9540d01050084143c2d0700f01420b40303ca1301c403c3c0640e805200e8841114600080c2442000642080100030f4000800075900305c010610b000e1071000d030820381c80024106184401800c000b0b0400340ca48015001445003c0100c490301900b035000e80b030202c030105510380c1103800030241c06a500c0800c00b079001d16880800030080200312501001015001540b28010030000e9414a9544800300406d0301e10050500b00710b9000030006002183c499081c40b001f2041a0780c0840c984054a00454205c80003140c0554045201428240312903505002440c01400c43d1810b00c5103541c401e44549449100c060003152007008001180d4041013036079041418050001410f00e6199074203503e019000c2c09250420b0035007802003900044080100d0b00c241d901402d40540103007800c501d241c0920141c0300310100c003615505100003084000c19554001007071020034995001d41c0740d04080c425011a0b02185581c8151904008010300c081070b44596103a0840e880140e0104c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 901337742 1250 901336492 901336537
    0x5010f030f0b1b0c100b180112060219020615030c010f0503060406030f0b01060e041e0905160801091103060412050f0d06060f0e0f1003380a090c0203 66
    0x3d5103059016202d000c06a00492a120070071004503050050f521702003002d00c0204041d00030000308011201103100d40c0d60300003005000c1884001c00000859100c4c882c01071900b0003800a66801c0c08030b114042e00140c2c03080c2c0401ca485003210b119041848411b400816091032941c0001e00b0f4100781020500c01c204020001544030361781e0380c012500071a004000311301099094200500310007002d00070440490304010440c0f00c542000c0c410400d9180c403102c403407550310550104a80c00380078520b20a44140c0300305000d00c0a49200703d48414018043ca400001d0f402d00c0354a880c81d0707121016a082442a0020802c000c0480c124001c46507050400d454202d81d01c20000145041d10302a1803201c00300e8620346100850100d810007408010303002c1c0b42d2074003c007464015041081410500040c00c2d048111b440c1240178041c040e03001509032824188a540030308000040742ca0502656029800c024142100c01002c41d0a02d4200c150103000c00e02814841d4812404e00030350f5a1040c03500c80603024101a6245 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 901338992 1250 901337742 901337761
    0xd1e06151b02090106031d0a1e0f15050106020d14090d08120c0a1d1003050c0702030a080901030e03070c0501050708070803070807020f150114030c18090105010f030f0b 74
    0x20103020364000d0200c00f0a50b180c1c20014014120464440103400c07a120705485440c10004112441d683e00903440c3d00f4914021041c541c0c1802c6050b01243c14a0207a207581c400100f440712050184141d4080005682d0300d440d01c002d02d012618170190041c0401c503030719940782826490450340748001c10303607160000d11000c0c64020510301c1007008030560198410b050000d00b42e1030310010504169542c0c5c1c1d01c041003250316140c0d000007210300d6106902060703442c0088000313030298104603441255609401d0034403540d034004c42d09104001038101d0700440001416400d641e0140318030035004401e100158240300003507545071004070660007514144000441c00d60108aa4a822502e01650005c802512810940400b0b00515425a2640c0c058024100001c0c0101300019413a603055400740560501070740791083c401000d41c000100c440e0035000d109400d1809894200200c03a802c82c1540b8000d80c9440e08080035400c42d58107810818210b00e181104102268084914041f001d8005240361541d46508122 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 901340242 1250 901338992 901339037
    0x40209040302031b060105030c010f120c0e042a030203090303070c0807020a0306050f0c0a0906120204080304030c0303110a03120c0c020a14041a0306010b1b01020d1e0615 75
    0x3034140c94480e0b9034801213000400c80504036074041c2c1c1195104100f807801964100300b8200c0c2c100000b0740c0080742242d040810b81080c40fa0402c03a080c00f40400150001103400e54200c01c62801039411845884085075080660001d0741640a15045085041c00684682c0760300c0090f001500300034400031003005000040c0e04035010154000c000da5515650307032910b94040d02040302e01c60320707080d01c003000640500f0380388045900b496409d41c1c540d0983e03810040b042c1d4190310740002401e1216424000421a00c1d4204010b1024501504a081c030807403551030018820051080880907541043c2c0714074000a4000391641180c109102000c00d803402590b100301c404665039040a54001c2015100080b60305441c3c940c88501030f0103a07010b20410880300003012040780715504490301a4450001001a84801405064909010310380c81c0c1c0c040c17030480370320341c05c0e03270055404401c81a0b81c82d10400c40070440400b2100222203005070a00c90b041c982030f5502c6205042c4403028043c007211160030004250000e04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 901341492 1250 901340242 901340257
    0x80405150d140415110d0e0f030426030a02030d050601051309061401020a0218070521070906020d1403060418060207020a050904050a032f0f070f0b0304020904030203 73
    0x1030402c80310410210581c000c0c2020f841c265140807038040940c42100d058045c6a9403c5410712170f4a181c400c0781c1040400030700917440b50040e0f034001c1304802251000f052000304010910401100003a03d1194003001651174010340d841440e91081050b40c440b1500802510f1403a580001e001a460343c5060050319280f04844e40000c6282401d1000300d94031031142d00c410160b40c100440705161010120040e651113507444c002a5104030501302165071041d540c81d609a000c010761034000d04001c0700d1240d041d10401c0c2c034928950050034503010000c0e6594070086071030050000703100400810555900182018201c0480201000400400a8011b4480743c03c264140440e804540241b081503041c204001c4d00908400c92003424841c900264900d802c42d0214040d035000070152100b42403070b94090300c81000051038210162600c098640e100d9110032400000354942c6409401001001c4092a04060780303504140c801e20f1240da07080c048003180c1019a60301a034103444402c5d1070f03280d07407c042c1d285000d0ba40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 901342742 1250 901341492 901341517
    0x304031d06041d090d0309081b0a0f0302011b03140f06010318082d19020109170a110f120c070306230108060615070f080d090b09010908040515 63
    0x5004200c554801010901c540314000030342c5e44401c20361804078103540d6640405840400207015840c8100800a018691183d0610440b4508002c6640b00329405000c0b01c01038015075540d451a00001981303401c040b800a499207801c200364411071161030a0b105000e040800f07041c0236800010816406075202e01074159045203041c245104526290180d070b0b002c0d4042542010700292800d074003210082e43e24411103100d400301410a105030b154002080707803000c103c004540d21a6020070114164113441140a80346407041680c4002041000e40065083c0e62048056840f480722542c03100d4000c41d80b40140501000c540341d071200c1c5141034514040950304082c01c0706142c5501c202010003c01040c411460188011480c07581c1c0c3d9104294030b404084962907040001c0c241d42030640c3c001440105407951082269002464480d207c0c480603412180b0b02440c002c0d13589805030f050025641c06241e118441c2c00081c802c0301595920780310b190103540310346401070310841c10030441a040d10003525440c003c0c56 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 901343992 1250 901342742 901342769
    0xc060c12024b07030504090606090914010e010b0c03040801060b0306031e070e06061303050105071805030703120918060f06181701140a02070b06060304031d0604 71
    0x44000060260160714603070503558442c076400e1000c0204054454051103202003044400c581c4503003124039612014040301041810040807504801c14800e14001d0480c956840c030140d070401c010081114400c030310110f91581300d40d00422105507943d64183c10364000d1740100303803a10f0300054101d1445c0602d402480c01542032910118540c50240043c501c200c40c114121220b00340e01c1403e00402c0242c60303002101680010f64240002c004100056402c60009802c0d640741134507000302c031a26108540c00480301651184103115402d03500c501c41c034480c43e4043d0031004d50305142000181d6075103607034840240710400c100003140c01140100c42e5440200130112640070046421040300d401803146020305166200c40c0380000c43c0492280380e44852540c02901040b00042c1040000d807006d0b075110740c02c05520b64850921724245010300c01518068100188056110501443e001ea5501802000f050249400780108408070f0f034069092080385143c10040030300307031003c1e0002c54003d109580003031040ca03106 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 901345242 1250 901343992 901344007
    0x30509030c1f1b03020c01140403050f071418130602090909030d0c0302030105060304060905010b1314011a03070806030109170a020c010905010509040509030d06080303010608070e010c060c1202 85
    0x118449040081281d980c0c032018120340040001e50100f503440a00180d00c00402d404065002c0c448402c400307041c4240440c10b080d034943d0b8140c5403450880c140c0285400090f0200050802da040042003e80211040c0181c481c210f070b15454000401001480d94100e082c1c01d1a09210b03480d81210512080036001d0f01c020303e005a580b07952a80b00c80028071030289400082c40c10688244207482c1030700c0000300309514588031611214094950110255025544da55030841c466441c880b00b00704d00740314040b01144042c400e04078103180950503800401c00805861480045254070310842e50700c2121800d0000164803a180032a0040c201d03410020420146880d00c04c00034900c9038042c08010346690308070f90654090400454018009201d591301140c02484680031b285440c1d006545d11110301011681007040221035a015280994010040c503040080103011302079108034004e41c4800c007420314080d048054400202105005040035102c1d5030303130740842c021b6244210000154042e5006040d500c0740c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 901346492 1250 901345242 901345279
    0xb03030f04140402160209090114090d2007180e100b101106010b180a0603021b070b030a050c31050a030b0f061504030b0f180703030509030c 62
    0x40340c060200e0b030521a21940e01d640c0360a000701c03090a15803070034001c0c0900e0f0300d90a2003181c8401400d00340381c554072103070aaa80f00c81012041071080c6440d02c024481184041c0009d021000b801007041485001d6012240c034100b00044d02030101c51380c1d5100384070407021128401000300000e0f41032403a140520041100038a01d542c1207840c0400007250300500350070302c80e1000d5400442c8082ea860407500200010002e0040a1018200c102e2400c1107040300024500c00058444500e500000080790707005c50000c001c0e40c5465407140040074018000d1000c0e5080840d6030380b40740001007540e100c19469100154001d01c00c001503899000181d00041610700c075451542c1c00140d21502070b00c0d038100003048002400e24128a00c0b00849800065070815501c4100b242d05070000020724068002c0c807194001c03582c9040090003800214082d41c44558282005100e182c6201c00c0500ba031500903280c07151881d20b614000c00c1510407241d06d030600f259100c070520007013418002c20030b84483c0d1005010748802210032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 901347742 1250 901346492 901346497
    0x10e0102070201080105060307020a14010230090613020609040204050616120314150f09010f0311010c050c01390c090c050307081f03110907020d020d05030a0b03030f 73
    0x52013604e43d10b241d0381e262014841d45020071900c41c4010b82c80401c0d90008100b41004060703118041000151824000e210320589000b5001404100c3e80c2d814802421040743c907460745a0403040882c040c00c85414555920708145d4100c4001a01c04d080004003500c82d60b071141e0441d4024803002d006251130740b0300418081c422100460301980d0340400111007036181446445000d00e02da03010b51003503402c2e40f00c9110301443d05001c2c2c0c5440e81c11105404072031000d5a1420961402880d0000a4150300c40c00c510746600d07081000e40b541c80c103000b822051140001c0000c0ba1408010a0a01c0c0103404400356210f55041030728501c010418048148d00c41d070101103503001d064500140289140303106143e981461000302c40c00c0c034180100240c002c2c8080f441c05846a05481e030040d10004038030031100c1d5040c2c0a074400c0b00e81031384111045884a22810820704040c2d2002c0d0b0700451500250000420685019440b125070345034040400070b00000003249112582d220110606015044a4440003c40c490703039900e6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 901348992 1250 901347742 901347757
    0x608010c030b0105040609170c1206090c10050702040c020106051908070b12060607060e01180515010506040b0901050c151e040f0303024008030426030408010e0102 72
    0x904203520302c00c41e5405041120100c80c21070350741b14902c41c80c0820f04071004000ca003c29020340038840c060101561080000c1008140300400f0b0700990808524003481d106207400c1139401030705c049001c60346071a04402983e10644d0183e0f00400c240704130020490060160f504070b03036848104070301c0c0c0d8100307460402c003ca0141c9203e081111980c58440364400b109020b500303695204042c0280000d00541006005810034030310414011a00d000808150703801c0d00d0035100520300c3c03800c0c1c41c0040024400c00300000121800d451140000950515001c900d161280d40240c9000140010700000983d102d070302100d41c90006402950810314180c00c5034070b0303c01d070706503a00039150340314541198101e641010214026507001c80100b0619020b03075001c0d40a5005209415141c54038076070030004101c4118241d00342c18600070022403c1d070207001c0c2d41d06010b510359081078189600a00c4240700030805500c01e810b00214006484a60b402044501c9145104075041202d50394240707507540400361015005003040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 901350242 1250 901348992 901348997
    0x90c031b06030608120f040b04060305060a050904050a0b09071a0406023913021908330609101d0d080a0305180304080c12010903210603060608010c 65
    0x10070380c0e80c081107003a503409004d074016607000329084130385140c160001000058041210142019503030008040349403c681d100c00f02207511001004010316200401d10094502152100190f040070b031034084c0c0c0c9002000c0d0043c171405988012512203542004542c00900c2070f0340707407491011801c1c500d0500301c4d000b6200c0c081c00f52041e41c142c44183c41840e07002004070b07541e0780a5103009165a074000b04054503294a19034100d010000d04c040c0205890009280c0743c0c1c41c48a42d426070384040c10004201250043c0208140d6201100441004420090103542c490386090300d48450409000042d04510a200d225a80400d140706c10110329500005d103141d102005021010b184009081400744400d240c46000304981070802c80011101e0017a406560003a10000ca02c0c80011115004980340d98055040b49409a01603900041213190200c1004a0380c5041c000038400c0c0e540c49d65000d8480c1e03400008001c940d217100d1510901940c5039a0282c0700458014000b404502c0d40c5500300c030300904600141000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 901351492 1250 901350242 901350293
    0x60a0b06040f0603140114100507061107050c01020f0607090b2a06040b06060f030c1612030e160b0403030807020a0209040b060108241507020607081c060501120f090c03 74
    0x25000c0007d07401800b40c59002d003421180d400c102c4011241c660000800b140c106903113144e0b4101400c960405069804d01c56001801009106000a46001454840d20a0540c094020000b40c10740c40a00784044410303100000d41c0300c4c0c41005961078401c3e40e1504601200c01807041001070325000180c030754001c1c1d0243c0ae00c1d00c003070748030002030003030390b109807640028449000c002003136200404100400d60500c40604a11003064180e64004104d41000e00a500003511030304005007465044c0301041884c0c011084150140e440c05c041030b4841c0c040c0b448054140003603e00000c1c80e5038001d1094642c1581c1c02000302000d880d0514100c003003036806644c950300080c40c410006900c01400380d40c0103c0c0008058190014000c400204840e07079a0300003150090381d03402d00c501001038030303010060080c2d10320503120603403948841d0440601c044808610408d94509000e070802960740c000d120015110b003d00c0f004610340040d60300d5840036105102008000104146001050019a021040b080c040941503402c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 901352742 1250 901351492 901351499
    0x5010b04092306070509100e120102040f06090f05100507171201060e0f0906010c021e03010506031b0411091023132c0106090305011d060a0b06040f06031401 69
    0xc0d91880211382d0340e00442c03c104114003940c600440000d14680c1c140c60940c45418044c0042034001c0c03c10b812140e01e0769004034060000d042007482c02006400e06191800701c05161041c050008a014440e060013402080070140b00a4829012030b82040c0e04400c9103d882c80225403a002d071031740300b01c2000c100421007100210b130162042010105c1072500600070513400d102c107400c00ca010080a40824184582d054a03800181c035050f8000145001840c20200440b103030b0300905096030030040071184240c0000c0010442c1c0f03094002c60800300d0030300b0303a400524070010140002242c8240c0360324903845104504402411544441d13450064258094017041c403c04403a0407684a0044041c080504400e000c0c041c0280d80c140c40848490790f1903189a180b500401003241014100e00b80c2001c80010110750050050241c24003550b443d040b14800300d00344e407079424082c0c1d58079507501403d00b8088940f281e05102c407680c0c8140940d809040140c0713040e0403069803444090010100c44140100d230401410001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 901353992 1250 901352742 901352813
    0x30106020714040612060b03010204080d020105010302031c051e07200f0a15050c0a1407081c17070207050307091e0e0a02090a060f0b0c0f0f031605010b0409 69
    0x2101701d07110700c5014002e1a1342c0e6500c0381c000d002a080c84940542d828000000d030900208402d508401d82c0b07400028803541136006040c2400b0108002180d42c400050390164415400b5003190405290b2410300d00403030141c0c50410f00c0d03071b118107140a0400030490084520f141c09601c0180341020040710250466034550040c800001020f1280144c0c0c01314038a849074000f8052801046100419402c2d0f0340c4141c3c1595409001005181000c03503d035001002c00e2154080800a50500725040e550550402e0450400240070086400405441982003000300e100300340200800d50107804018180c03410540c070350095400501c600e20880844c041421205d039100029403041c81c00c00d00c0039501070702140314079030240620160040c0060130160340d940d0b0001500600c621964001d88a00007159a1f41c15149140742d00e801c0e4182511903c0d03030402d059240b840f200000444641d016041c007003c114041034209280103244c88440751f90003906201020081115080c80e0740380010324010520308403ca8082d01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 901355242 1250 901353992 901354001
    0x30e060903040b0c010b0d08040807060c050c010f1101060602010c2a1106070623062d040f021918060905010804081c0c030c140f1e03010602071404 65
    0x601a070000c1000b44140140f0400801d21390700c0300742c00412032040741d01c041641071200143c19075200070081414088001c0901884004000e42d1800b03040c03140c0180c480584641d4030188050501514140c800e11031030251103005c0141d40000c0081200e55958000640a050420151070004d2224040d0700b0303014207103000418120440b15042048885550303590b981c11030026040581c003003000e11003a000206c490082540d03c0c4a80c040c0d500707211001000070051500c0282040d446501d50b1540100b481c0d08590505550403030000101d04202025804600181403616507904041d00014103040b01010700070007120b01040c41e076520820070240d881203280c541d003a405150b0015664000811907980b10b00c5606402c02d01810480346001e944080d280d08049507031040d0b042041d264075101034556007600c240381e45813440e0300b8045d800406803036044442d44100070902e5032140e001300e0b0403160f406d2072000e0040c002c1403122680da07595849000c041d51302c005910584210b000a08490807103820039005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 901356492 1250 901355242 901355251
    0x30a09110a0f09020c071e03020a0b04080307060c0e060d1e060f2c0f0f0c0301060c03030518060f09060c16020111010b040c030e06180a03050d0902060403060507030e06 74
    0x40310b82c1c07082c20402c030000a548200000e90b81c9100f44071000c500805078680021103144040c0394485410b242d032050100050007031b403003124400020f00c410080c469011049030310181d800391001446c224040020b840b4045c400592640041000c038180300824240d9020311110010400c5c404554400380c6411010b80362180505603038810001000c0240004001010f9803c1c211007994078051141d40b1100c803500c0c60111005400481a08240980f6a00003414036801c60382001c0b04034510b60500501600c40d00385094010304050751078000400c0d0b6021031803000204c3c0e1204080e220075003404111821001030689013120140a903034007242420b84240111948081e203c0812a400745040c0c005407124842810079071100d5480e29500b003010354582c40341c820114910784001440c92100c01016140c41c000400c007801038540c09244031707900800051001c402c294949046541c41d043c2c88810300150000010007500040041404410885550480e038410303602543c040003038284902a0507070740e035810799 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 901357742 1250 901356492 901356509
    0x5162901180506030c10080c0f0a0e040c09150f050c0a03050c0f010612030807120e0f010c18030b1e09012306150d15030807060b060a1b060b0303030a09110a 69
    0x206c403514003805003000c3d99001c0d4202d8009400c00712104401c3c40c9651140c80014001140018031034041d161030312440b090000d2074035040726040d041645c00f0300d403003002a43c2d040c2440041801c841c41e6a10a0089942c40c600401c19035244041c0c0d4078026219401050f030503410f901840c3e01c40303201d224051044604440c81110300c032600350110b403810384214001a140700200440802006001ea8030740c040c1e40011494400284100d00000080c28210358078104c8180030086000303100c448444a40420b1026641c00c100300c90394540f100000000c85014051041515100c50f20030803407601d4040d400b1160003004090500145400b0b04660800b03001c00703c1c0c015134820505859000920f0540c400b503c20921700780c00002d4071050311108111101c0982c0d2007140c0c142c00014803002081a2801030300382140d8162510750070490103410250400e084847c08428820f04001c0c0300c070510480d0740149020380000303001d0780c0c0c0d0380c28082000380103420f107400142c40780703036460003036a00500f016030003182218a4074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 901358992 1250 901357742 901357759
    0x31a13020403110625110907021606050a0504050603060301090b04032601150c020406092c03030f04110102030d020703050d060806010612020706090218040b0705162901180506030c 79
    0x2c610038007084175080d09448140b042654010181c9480e10700394000d028a070010030040c0d0a26400d10b800c2074064214108008003841030300f40c90785d00402070350150381c0225802c68403540c44401103030062400740b1026110011103001d110500d0b42140040007400841400141440c1e811102800108003c0c811100e80c2450b090012560f0fa1187ea03c154220384001c102240050390b449003441900c0b100103080d542c104010034460305007020b5825041000f1002c0b00510b045243c41080405084401000a004400c00001d9002917a10038000c881400c0c501410841d21509141402440c50b005510742e280700e1481c01c40c010951500024a80c1d048400c180d407502001c5010400d048003940100384100d40442d11900c103400140c0d00c2c4800c0d21800c0d003803050802c04038606403e003d060f288002d4080700c03d01c8001c2040c43d80c59000d124000301840e03007120544015404104c10404910680d039a0104460b200b0750002c41e10103541c968000c617284c5d42c881c1c20300c80c40c0c442100f01134450320248902c40c2c1c4034828 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 901360242 1250 901358992 901359037
    0xa03050717041e05030f090f0904030e0607030306030605010e060f0102070e1308090312220b0a0f0512090d023307121a041805070303031a130204031106 67
    0x6159659036600080c45800168443c030750381c0902e190410304110112100215840c1140d08112030300d483c0401d0704641c181c601d0305080c8c401424001c06a5804c45c043d0500041240030315002c2e8102d880115031000c0b0400180d80d480000c01c1e04180280d82007803080c281100455155031000a03c0c009503180c4031010080b986030000000e001d0880740c0300446520006000f07110701907500744160603010020224a03552021034030000146141c1c041d00308050844203050500c01ca1821005940126100d030030243c902c28180c1d40d00350340c40d000305800004404644010400f14080100b002a80e24105800302c0301281918031614002840a02c3c1e05040c0e4541d001c0a4410813200ca00b11503000003030307403c00c41800c2829401c8041035401d2080c0c1c4000c1141c2070811201a81060b100d0076900e00c00f02d12610b81e104106a0342d130381e02c80c030080c8000307020551904902102c5200304980344140c0b0800038410303180d80c0c40c80080c0d0030203500071344001c0c0c5400300710b00608001420b02c88211341403280294100d2aa00c4403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 901361492 1250 901360242 901360253
    0x61401030c02061f030507180509060103030c0b0c3015090a0b01090b03070503010305191e050c030304032001031503030c03030f0e0f1e07030323030c0a0305071704 72
    0x8540c000040246014180017020030f000303104000250240c90b880801042201000100740c4001500030150f580c056001000071030750200223100c150b94020f88800c0c80d0f0300e0740481d4140d1400b03241004280c0c40140d40c00861264012030120405114403150030f030a544d542d090345ca141481c5480d4072500704806400190800b80d981c0e1145003c2441418100b0140d40c4500444481c0c0d003046500c0c0c00490000401402845010405c13001040c3c03180c0c1402c03421b407000c1e07500d06405400995664641200c0540d00c2e00410030280100b0f400d50001808883e142c1e982c5e4200300d004804000300c48243e8900c1c1c210004400d52003070107101c4050010000b80003084d0b15660f41159000340030711081c0e0801d9690401110700b4400d81c0036000d1550320000003404075811090000e414100e41c40d90f215030b4281154502c0c1081040412140200c3ea01802e10401c0004a01c181403a00c6020020410450500004214070100800d02a1540010b07c1e501000f1965504505441ca44907007108490002c800c000010001107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 901362742 1250 901361492 901361521
    0xc0c050d08150d060906111e04051012411e090c0a0909020415141207081c0f1b1203020d15061d060f0306150a0201061401030c0206 58
    0x610441c400110001c0c46d880312821246041c0240444410020303060b41103295200111410303d51501d50185441e140000003107541034810003c2052107966403d041000d000b0790700000e000c070403620240f40300c0d480f804e015103d9030550050320107590100390030740f0200c1a0f0f26041c0c1d43c4505031141c1080c056403103100c070803c5180401403003404584103401210307074141c40d400d1600c0d0082032000404140795002c7d204000980b10000d403600258504140100075182059446800000301610b00346400d5400d04143c1e800c004142d0498602440741c8a0014040e00c0600c03400440c418903651801041c9084c600112a010500003501612408410000c40030688a500360301440c2c00c1400c0042c0b8280e8154203060940c1c985c003055610a85050b981000420740040c1c0101025840d0490410702015060005400e4069149050480380003c0000380858680744240c3c04008101061952241c203448002406001c090040c803120f0341560704500c000354020300806a0300225a0003400781980e551001a244a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 901363992 1250 901362742 901362769
    0x1a0127030f15060e040201030e0105061e0f06070818090c340309090606030903120507030204120f020109090e1903091d100b04050a06140d0c0c050d0815 67
    0xc401e000c0d03442c45544503407080c0f400900c1c40c01c8001a10b860280005021642e501181100c141d06020030405990313106842e1381c03c1e1800780710801c0c81d108100001b145500b444114882d400c804005210400d0110a03030150840940000da0381c105410382e9814441010710640d01d092000340300b0310602155a00c095900c1074110a10315180c24000d5010100c4100d1440444064004c030b040540b0a014210180c000c11000c3c181a040c00c1c0401d0798240c1d0000d00002c44004100316090b035810120701003500c41e404690080030b46514151070226030381811720505071304c000200c1c0480c46001b400104c900e414000c41c40140700300c1001d0030315076030301c1c2c400c840c501c1d000c050007241000001c107004101000d400c8401b01e0710782c00c5412004100d24055003416203210b03280e00320000c00b400512003042650b955245000030b450140c42c1c29550305100740140f60031401840304402405040800103500700e68000e44030006240200c048030054141000283c0d04150b041d510545a440d180359985420706000401e030020303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 901365242 1250 901363992 901364003
    0x30c0607030518040204120303050603160504091a011d06030604170304050703121d03031204080a0c0611030601020c0a21022d0a090203010810050603030702041a0127030f 75
    0x4045600f0015040340d0041d08101105003078500308406155043c41410742c0681c0c00d5000700001041001c05580105042c4215131240e80c40d05003c408010800c10820f800c80f800700011082940c5403180e102c1c003614801d0801b0f960056000005000b460001001c6001f5900008001102210207100080c5980000c00540302481007090000000303004a100c0301201c0d442d41d54900b00b101c00c00d13615150303e03240c1f204090310030351080c086600c3d4825502003054102d07a10ac24030560b645d2203014180e40d41096428050143e0b8503141e103500b000c11603480114807400e82603080d107482c03075000d00c20030a80307370850b00810400d8500310400f102d5018070b00403000307809400108541c511820074444043e0300003190f01d81402280c8403002605443c14180e910740080d14803000254159030625020942d1100350011180300b4544030400b04000f610140110b514041c0c001c0d1080c442034514009400055050441041c005025070803044d0341c3c4044103049081c030b00d07030300030310401414955100d102c1501c2d5245401d813803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 901366492 1250 901365242 901365277
    0x200d030e221a090402060a030c210c080906130303050702011509060f0515030a05071202190206010602010b010e0d030e06120106020d110c0112020c0d050d0b030c06070305 75
    0x1112104107031606400c414000020074242c0110703681c09010114000881e0140c0400300500005070303242001e6400511045c50b0000703583d0a407400464414501c4211078200300b10000345030900d4241500100d41107081a2940e03030700d81c1c86241c406640e410007260800204240440b40e507000900c80d0b0040d40c0c001c44a03100215004001c40001c3d02e0504032640402c00807030b91410f04204560042c0d031280020602102c070a0000842010022540c0c031004040c82c400ba81d4802c00104c2080c0104500c5517280707240c030000c64a80040c2c410100020042103041e07405403140c600000344c99403050107581e072603500603034400111840f000c0c03d0000b515400300b0100c062001040c0801201d40740c20014102100e080000211954500b12019041c10040310341c036020000322440400c44000005107454901000786403688901c0c003421146002401014440b058501445142104255011000d0700c00142c180c00208172243c001810190348074a2004a5500301400f404150007007030041c030140041e41c1c2c0c905010385 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 901367742 1250 901366492 901366519
    0x8070f03110d020705040f14012903041136340314010b25051b0901050409210309150f051f05060702060c060106020703200d030e 57
    0x82c2410103880529006901c110020072441c541401b400c141040e0341001000400090034420042d144140201d150b0491850401207117108500080c00b24001a1a030746a240d003440e181c0841070311030190500c0d21400440030081d04007105001610384c01c0000d040c1076503140042c07441d002047e080c0200740d40104401c18480600000404000380b001209820002e2120204281c01030b080306d00c5d9408c0340100d103e50038010f00822079010111030840c1d403140306400c4c2070302c1e08011711010480018001022401110b8034400000c064810a204030003044403400540e80c2c03640c00b8442181d0400300c01520700c260b1500055400c0f0341e035200c00116485940380104003801c2c15210f03030140e10721019501c42e00903035030405154111060312a0302d802840d44c0c00c0c8e46078039021040250036000d03031074001d4903c0342d17030002000c2e01103559490071a000c7c04181c40584006680d5528042c0d143c0c0810302c0305032542143ca07401440d2160040200300c14a0178010f000070400f104644044400446211040e60000702164074003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 901368992 1250 901367742 901367777
    0x18070309060915090309081605010e03030d06081c11030304142b1d010e0910030b160f0f094103100b01020705090408130905060f0d08070f03 62
    0x12054180c9481c3e010074a03845038030b8010481485544a01d01540055952110340c3c40c11070102003c40b002440c11401c1812880300090641c442c03000940405031500c440020700d1800170514502c0200807590104420035840425125400a480f10300c0d40d80c2c00400015002070380703120003640380420040407100c8040a40180c2c45072900e0b15520414150b080e9031084a03195440180b800c200c0700142c0c807440c903150100c800030303103603021103040c091043c000100004c10904040e0004002181c1015145005040c45800b86c0c185403007145440e40081d010b9205040303843c3c000e1015240c0c00342555200708106281016002581000c40e0454952022002c544c1c40300c05028141c10010f595980c0c00c00d0307065070000341010301d41402e00c03c0d90190035003000c600307003c13581e0007090080c00c983c3d05403038031045580c0d0b40c0340c950900d2041c40201d48240e100c5550108017040540d2210344104e0042d11500402d6480500700100c3c06c0130844002c01e0b60408024a200040981c4049803240d8400c1c200341442012800d940d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 901370242 1250 901368992 901369013
    0x19020406062a051f020403200303030a05070509130621021011030708040617010f23060910080a110f0307050a120515090a1a1905060a03090203010b180703090609 71
    0x1040c0301c4c03900490b050060080c10500705540326400b14003050343c5078003000031a450303010061100400310364650000d41158003e8040350b0a418000b4448401c013103c1410600c01000240245011550784102410301c44c01180003011466400800207000544850000c6412481f1040c07801c805010a00a10f00040c040c10041c1010b403411741c89004103403d0000e0080d1700c10205920100321420400e0302004240318820200b510140c0c10003a4410b520140d4001c00d0302886040313002504644886410551594405901401000e00c42001d1100300712285081c505405008115915208200081512103004400030000c0d41114100f08490b42c60a1100604581c401c80d48200a404216003c243d03e1600c901ca455201e08a17040800000005100700d039030024415906500030040005014136a00c0d014a408000344402485d05039aa150385500401511081c10100e00943c00d0049040251500d21707141641031030898412151030341c8000044014040005040e2030513551498280c01082c03c2e03142 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 901371492 1250 901370242 901370293
    0x2070504110301082401120c030c030b010e100b180d0b09030307030e0a0b0f07121109100807230d060e04050f0604050a0303091419020406062a05 64
    0x28641d407a589040680b5082c000c01c4d41403c09806980740940c5d810b0b04101545a040d60300c010304150411145140c50b0040700d0007500080c20f0302240000000c108941d200405041c0e40619840b150b050721b415070072000b03850003070140f200c0002c2e0034070194116080400101c9a103080040004110444946600940700b2090b1580c07403694100104010040b80c06008022840b298000107100a40154941600c14900500101028010b02c1c0101e0f032142c2c805c04010355074910000c010030032803808070807114982c0c1c032801c3d8241c0140d101c9540225414050100c4610600341519400401a6a204586011028100403401e0160140003941084000e442601d0160040c00c0c10512103082c10f050441c0b9020319060811a50b80c8401c04000c0041c0010405101640c0d15040220310111b0516000003004198a12804184200c00d40201450040310380d41800341d0095400300426502c4034000c80e0864410307500740030700c2c3c9840c2101c0c0d9000c1d103a07400303810705050042003900c13408500b049400c01d14860524 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 901372742 1250 901371492 901371521
    0x1306080601050d0c020f0d2c030a050d0809060a1b11100e07140a081c0e120d03110a0c0f1502130e0601020312370905160b040b0a02070504 61
    0x1644102c00e00100141e852100080c01c02500340010300400701400000c14000500700e108d100a000a0740c0c40c10080c1c11000d0b540714003035424010000030300910120003201c0540341442054007094001d070562280400012883c000e8504031034030548142d41e90b80d46003c80100a1086203400001c0b4011446200d081601202c090060f545c502240444216046115103124100c4104104800c440c0050700e2815005605120001c11841520986540c121424500d80010300d001da082c09480010494500854490700d0070001c00c1d0340142081598010007800c01e000c9032040c030346000840d0522107040c985502c1021031034000900880c0ca4000e0341c11160001601c65114042481012260035015074001420300c000c60038900da0500030842d000002d40182a44003450480135060645020001c1741c00d64a030302d140c200102005a404001e08001906075110301418510181a00e44100340300c04956019198600306410400643c6c0164041d5048506511902d4130000300ca44803802011401b080c0300307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 901373992 1250 901372742 901372753
    0xc1b080714010e040204050607200301141e04110d170c0309120102071a0a0f0c120c020708120a0504180c11030304151a190306111306080601050d0c02 66
    0x14000501000041c107880f600ca24010301040c4925107403c4244d44d407050b0000050114600480d610705080315a48200540550170a0722900c44c6d008500c0f4800d004004001c807011010814403028502100282c80c01001c42e50b403070070b03501038615100c402c62244238081c030040150082482d422140a030b104021094041e0004075202c0010324280c1500c42d99225108002c0d86098003e590700d51804e8450100c4c068100c03c16008030380c1c0750821398800c8085540c030316801c0240c4000c0e244040c04043c0304034501c94500341444401c0158170704c045209001c80d440300d4001d18081d004088030001d15003002d6510300801078203100010f02c0c251080c00394100304400b50000112003004074001000010504003080c21684204248000111003401d00600c2044103c000540e0071001c1d61007450021024040503404480105a9840d03000403007503150450f4031542c81044005c450b580705440601030071407102c0c0103200f1044100002d81c0107100c2c0942c45041403401628001140c8411011600c80940081c01a07009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 901375242 1250 901373992 901374029
    0x609090302070f080607141b0a290105093c010f0506340602180108130605040c050a090e010b0f13091b1e06050a0c1b0807 54
    0x5200d02e0b4054501c8440b050fa0603810050060741d14407015103140104244480308404c7c524148054a041040080c084500980c08540e529501e0b40a450300392804150700380c080c06c10200c0e81240c2150404082c881d41b115a10b0031080108041c0010584500403422101148207034000400030307088400c0707060012405000030450142403140503000501441c0c00540c06219a0f03882d2400e80c0c0340104000007216010f81141190180da00c4180c5280c2c00042d0100c9000381088142c0c1c026109416812141300c844284071401101c50400650301d480d400d0001e80b0070100402c00d40d400169110b40142400202c10340d039000800e200341e41c1c1d540200e44640e502d0f154002c400c1d030203000f10310b01d0060131100c3d0920300150000060040166021403030b851669283c2c03000400040c127083c00b8001d6020b040180da515582e980a254000c501e117509080c03103807803620200382180100e043e02d00b4030b0442c1c0d45001d01e414969031098210000320030b051200c0526048002400c0745e041008001804080c030144000001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 901376492 1250 901375242 901375247
    0x31911160b06031501080703060b100c0213020705030f030f06030a0c060f030f06091e06060507060c1e0504090e06010312030b1f02150109090506070e011206090903 72
    0x1410000454004010080460381000308400a2946078020088641c00e40391800002d00e000385040c07000c07101c01072010001403041004940802140e010b10b02c14840c0381208030401c4584c03082e54007140040382c040d240c0c0310702600701044100f92410018100601c2e107021610b0380f902d150802d03642c40d041c0c035500004000e51003c182c06a5500004d0030740c010300c103070b4203140e8491800045030b0081100b001051b050501c230043c801e0b00081ca030020340105c1041260707250310510300544405120360040c0ba40d400910f80030344046108240c103c48455403241d08101681e918013000e0010103031844200711154010fa03404801182c00502c01e0185600d60581d40c40c500b120301400c1d41d11074600710050760480c400420200da668112800a080319250010f480c104400010b80740320b80c0c0880c1c2180309107409400308400c40c1c00080c0000d2010140c186101c0c580c0e03842d00310009450002d00024280c0e004080492200c44c0078006546039101c05040c41c81d880c10811b00c00c44226102607018200180d141e250203030074980c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 901377742 1250 901376492 901376501
    0xb0901031a090711070509090703030906050f0a0507060e010f05090106060906170a1b0909050c04030231090c0923040f051e010507120b010207030201050306150319 72
    0x18103031014804074034400001100900300070265400e00010702c0e00c03002800828006134029113001030400c40c41f41070030480942e46401c0c0d8042200414207001c070101c0e07268001c40c1641c103019440c2c620280342c84002501142c031901310303140c1207460702d0f10340740c07044120b400c02e01079440001103122000885140c40030f4840d0030348600340d00c00030034014074039402d11000d548041d00c07007403040c60001041c0140d26285041c0004080140305070005c522224170100381d055010706d886046480409040c0440c1c1c803141c01d6042540f00b0303440000e41c44076030509200c1c210100c41403001125480358680303214038048100340c4c405440c487e00048030810900e0500b4004603202e84105400e5802061100000d90000b008101500c80e001e4005455414445200c5c0308221041101c00203400c8080042480003c50181207400380c0360070340303030500801c001da207c14031442100e100d204850041680140601803540e0011740d42036101404c015044a142113a4a554400c0400114050310f03800e0001c40780b00400205503400c46 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 901378992 1250 901377742 901377761
    0x6070f030606020717071a1305040614100207080f0114100f0e090a06021c1b081512010c020a02090c03040b010e15090103050f0709060e0c030c0f040b090103 69
    0x1480c1c80c03410b0081c264001040016100d00c2c10051805840c0104020324100d410b40c801409060140300506144003401c0181c0030313451045582d2800d5a84a004120560b900760291a0341074000320079071a04c42c6401c40703004141c00c20900544070101e844408090030001d0308a040d041589d11072a816041007400404580d0043e281041c3d901c40b5814078084901c00e08844c820502114001c001007624000180000002c40707512410455490744061080d8181c0025006409000307468203410201c0d5a400d100001d46001442c0c0e1081034654480180002d03e0480d00c442680002c81c190f544526401c0902c902c82c80403511341c0062550000c03c0c030410113040c4008242c0c143d85141030041c84005603c00250505448217000b00c1c0d1318036510000c903024120010503a042c0d1140d100c00000040c4403004c5120500b80c0c1c104000d4030001d544419481d0151009032081844407046d07240082c00308100e6074081c45e044011004003c4c90803007100d00700c82c02c50708103420468011000142200e40c56825200d2200c14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 901380242 1250 901378992 901378997
    0x1513120207260715050c0109030e04110304020f13230103050712170901170f06090c09010c2006070308092a01140405040c020102090405090a050712020a0306020c06070f 74
    0x15815400c2c0150316804280300d80b0742e5004200d100c940080f4041c90076610442c0c55040200071004850500070300381d0007002c070024011440e00c40460380e04503421003140d10850f0003078400c6042c506ca200a01401860007002c552800e40ea8400483c45802406100050744464159404803541182000b03802c0c030040d54010316041b43d030307101008005020340104540c80752103004040c0d1501c40110040c1d80b250740a01d2110724241c0700000300011903036610202c6004010980c1c05161580d11a41c0341e1030315100304171720940410802810500091108015405036042c40060040006100c41c00f1440641003604200d012802040c2040f104003010410340401e080c62501c002d410340c9031080180b15441d040c03c085410804401405495039100200b100d0041038040d0003004200c08800009000350400d1144921550400d07000c2501103d000907104042a006406405603910341036000c008488500ca089030049140d06000021401078409080d0703008004001d000715160129000f440c0883c2c00881009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 901381492 1250 901380242 901380299
    0x2030c0409170d0216030c2f040e0c120d08061504060509030708032d0f0a08091903110c03070b0f090f03061006080a05091513120207 59
    0x4285026203801c03200c00480c01460f6210301d0940c01202030f20503090484130890701a42c0040415910030031498101d4051488010010440900351540160a000d0281c2c411942c4415010328076040d80702c00140080c2030704441c820030209010078043c1c0054060a01d568001c01c004024082d00011415800481150b1610300783d0340c03c10140c001170040780101c00070013902159192207030310108035410284c081c44003103035101d01c405030700c213215002103030b1441b01280b04c2ea441c01003c0c1c030083d131b090b147d007100104e0409090a23040c1d00201d403a124001d1604e00c89110b070704450b403c5100c3c996050107042d0f0080e42e0f0086908402400d0383e00d0482d000b44141d0003584424400c10048900e002030302c62104000820f25501d100400008944051821080354180190400e0010b4031010710502c00c1101c510b0b450310651a69600041021280c2c225460300c940d800131000402c0400303c50503241c3d80104809000d540100b2181ca50515120b1000944809a400820107211501051580340e091001c500c80000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 901382742 1250 901381492 901381511
    0x10b06031302031905030a0e19030314040306060f050a050108360609070e1806041e050d121113030210030608030f22140f040f09060902030c04 63
    0x10540d1100401c03074600c0300e21541d2054215a001e01030030405040d420340c074410030340b0743d0304006803070b03501c60640c403008141c0c258002103403403e140584410000300680f81030411403460700e003039581040102d030340740703507180d0801c00400080c0f02c070b110b0000902030142100310640e00304400d01c84409815006981408501802c010314200c58400d140e400e150141c0d4142081e030388d10041c0408004c10000102e04a000e900104000c038880025804103ca0041ca001a07403500ca024025003080340a00007011180c00401c0040c000c03421140c502910ba0248100b42c16143c0d9450725030904200144050310001202e0301c28200303840302c0f81c0c01a41c491a0004409509d040c0c10111005a805c03a00c4c40020b004160006030001101c3c000c4e4000f100900c135078002c0e26038032000c10f5086c0a21754403681d0f0b5850880c1006540451291468004400f40d800b058441405040039034200911900d41104041d84503484807a444c240c488a8058001910310035480820040400e20425050203002c803a40b80c0994075180c03c60 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 901383992 1250 901382742 901382749
    0x16050109050d1112100506040507110d050901410f0d0e0c0d0506090d08071b14030c01021201081513110a1202120d0806040e03120a050612010b 63
    0x50300c500398003104802c040f40703581c0040350701d41d075568809800c14015070610310382880f900d401580c42180c0c112030811507540c0d4600240c0c0e81c1c40b10b1180d60402035000c1c0e03c45000181c0620010050a074050404851500400c19107a0382e00ca041c2144174031401c0da0011500900c0c40184d03090000300c01c45081541000b00c111079041e894042c3c400c20354880358407042064210201401861385a4802400216060945041c55962038030700751041e140d14070850820103a0703580700b0f101c00e9004007000c2e646e6a10381c242410501c0c440099445c0141c981d051910000500c3c450104000d0042d0002c200002d62145503409034000401d8050b0300010090f048a120241040660401c45621880210304100755400c01e08068454500c071100782c5800c8400c80e000421091607482603842c00070b2080344c3c18060540341350345294940c07204c9031a44021495110105546107040c0e04055034514070b0204403030415461100034907030480141c4506200540c2d4000344000d50400e020840c404110303a00090151400c4030011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 901385242 1250 901383992 901384009
    0xc0105060f2404030b0108010b031005090c0d1505101a04030f0303020708040e0a02030415020c0c0f0d0b0f040302240708250e010306080c090a05091c021605010905 72
    0x48120714030b5071162880606500429100130b540c1044141c4a0345d038407500c8060003425072869851107442440403411a200c514003c0e24840c0b02c1c190081c03d2003404a20138800d0000070b102049031070301440c2803c0c90b11010107104061082c0701740410b070b250325450300d00a02c250705450702e544441040108070038000b09400d048042e00865061400603503861080c00c141684d40140e070009040015181c080c8a031102540c0c016500650041503110228424100c403034040380b05400080000d600060400c80c49440c2442c10060403002c050042c91048003a42d8130003142c000201e5103e90601d065500340803e03d5410000d2041540024002e84802c0d00d090454080d2918000d0510080141000004048403e00c1c0c1036401c0600003003940c1154010004000b42c0703010070b08180d00340002d2602000086010001518805e9114040c1020046440d1209494054803006250065921501d090700d1414201072010680e1250702e5800f51011041d10724003c05138810b194052810402d9040042c48651b550441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 901386492 1250 901385242 901385269
    0x30c03351008120403050d08060f0d022206031101020a2307031509030831060b1005070b10051507050a38070816020c150c0105060f 58
    0x31090107955500031940710320310a40105000380549000b80014400030000781041c3d030300c0349059503000c041d003840c00c4504c000f0480d0071030340c0042d61900301e0b50351f814042d41420119001130401d08a01185401413458003418050042480b541d80208000740304c0707004908030400f0024809003001521036100c011002a0880c11400c180c038120403010141c1d40c00300302d010015544030b518060446009032400c03004101424068002c10803810000d0b401c640c0302c90a01122501d041e103412903918416000e4268000c004104680e401d680742d9a0040c03581e00c070480700e03094401c59610f6a548040c2d500c0c00340d14103c0e01400b0111030320103c500602c03565968811102896000c11103440d151105410403910f8030380101d001625010001c1346d80c01200c1c028034025100070082e001c540a406d10787c000d00c40200e41080380c4060010b05041f0200e00007000da4001c00301205124411175100105040008655508400901c44080d40000710194103203420701805138460021550724420700e120a02003420212402c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 901387742 1250 901386492 901386587
    0x30f02070c0e090a050732090106120b0913150902181f090e0f0303011203050906130e04210206010e090312040807050105010b071518050109030c03 65
    0x400101ca0260400a850b0fa560b04001110003c0341d6a205406a25090038420000c87e0301c099030b10400c41c0001e44401584031310140c004170040e8641407044400280b0034412440c419240c5d0856413060f03071140002d41c060700c40803401d03481c009268540000c9038032100744072401242c14503650b83c0c0035903102d140301d0b400d11508200181956981b00c030710b03a940955854107114500b11840c0e01061401c4036501c5140340c0c4c9007003021200e0400340700714415a40e0000b403190340c8015445880e01d00000f40b160025140c0400d020b040c00d03003460a0344584c1c845440e5550010940070070010100700a100d100034a0b80020062664403031000c1d10042c2c00291503460500035110701d0a00400800c0403100204100c0e1002c1000300140d9507503040500d0022819804440306445560070b240001c11200703d00300032904003580c0003500e03050440040742c541d80640044403100022031120020300d00030610a0046841d81d500c07079a507202000c40c1c94600940706684115848140d22580711071500720103000c41200350300040300ca = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 901388992 1250 901387742 901387769
    0x1200405100e040c080412021204090b010e1210200d2c0309030601060f050a0f051e2109120702040e15150d020a12061416030f02070c 59
    0x240e41540ea07004041e42d41074200c0c0c6464101100154040410760040d841481800343c4101c00321400c81e0b4551182600c5806000100410441015660b00055960006042c081d0040c0303416400212540d0b80350501804a400030000c5980414543c802c11032003034002d0101102101040c068a460381c062038807101e03041ca0f900e140c003101d45c0442ca40c848003590705803013660040c0c4804807400e5072241c0140c0b400900034440c907000800d80500454070001d240500303685490400c20700c46000c03240b01941c800420107200041000c04050f504101181001340707075880c4076983e189001c1100d40a9080a40001074403207401105124010070b021803020300400180d1151070701e64546000003001800304042c3d85c101c5101d0b500458034904030708440f1520034001c9201d0008015115401d2190080e42050025440a0b079840113101821800100308502800f401c00050002c1d46140381140705101a0380b0511070039506100048000d516018040b8108a014015030501c03120740d4070300f42c60520070300989510b031002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 901390242 1250 901388992 901389019
    0x110708030f04110a0605180a03033501090b010f08010f05060c1005070c030f02010608030f0d1b021b03070e0c030601021014010906060e1806030c12060901200405 71
    0x103d00350411a8400207290401d410341d10380002c3c1895000518101c803042109415040c5842c003221403030202c0703405844403803000c840c0007001d080c001e4400160f80c40b0b1486200b0078281c040080380c0941d001c2d026450b0001040041030b4000350150141c00d91500070004060018040b07010200c0d00c0e40103d8801303540c0c0d15200c4803081c81d154240420f034001c0c8800189811b00704040241d0214206003814040e803140e00c0c03400a8807404034244d4180f0b01a202e1503074010010302010485a0005000300120000001042117494070f40c0c2510a62507a60540140c2c02944001407420350b5170707440720302000202c000782010392404101842d40640100340c042c4a04001c40011090390080c486010034500000c1c0822500c0a40801b4142444080c002c0061651401201181245c011400074422000041900440c170360000c0a2904400c4004c00c0180c02d400f421108060544441030014440c003640c102825035890705501141c02c48040903042d1000d40100c08051000250900454003a2101500c1200b0049807 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 901391492 1250 901390242 901390253
    0x2003070e2704060906060812040b07081204050d111f18051510051e101b030c05060708010302010c1104060e0108060405060708060315060f0d1203110708030f04 70
    0x140c1c5141c8441c10900e00100000c00a182d480b05805900c11306041103004c1c2c481c000960b55178461024042e403600200818004007403000003924030144076100091500100300b0101d290f1040a80f0222016407041d680419860342046000ca030dc0720707a0328001d0514403103042e6000c05d94113a0a44403810940e4500da125012080d4034075242d071590f0040211248210380046490328218100c59280c00142c010380c01159602e02680d00316080120400558800a42d41d020004204136108030321052001140c00d80c0206041c078494200c03070500980351400d440c5810304006003001c0c0014240807c110038540180f0050307800405021180340c1251410031001c01c10000300d001098281c01c15112000241c000040700e0000280c45c5114070300c0b40c0103407441c03a110b2190a82d502e10301518010b42c103070400140790703a046032036400c42ca40c841c41c0140741c514060031600110761000d80c0040240c031202c0c0c050703402000b0580c05006070000b540c000078004d450030600781c4400195000c0680801c000c4040381d07000c0703001d101c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 901392742 1250 901391492 901391539
    0x120030f0a0504090c2328020c031e030415142a0a02011b061107080c0618060403050307030905070f15050705070303051e0a02012003070e 61
    0x50200100c1680c940c00c001010740590014456058001d0a11034a124414416000c403259039032a036040050b9201c060104900940084141c0c0d240940c0b0410450200a00c0d05000d604088094028000d00d81c142c83c14581000f05611241089490b0001e1107182c03850004111800c5030b640c250035904607040c1c030308100c41c41c4100080544450101044e915010305080704984020007081d8a94400985151016600d840840310701902240300070b4010200c00c01d2200041310081c0c416200010107500710ba95454154018031006e4903001700211ba551803181081000d6070304a580d084040c0210b0038200300705966002d00a10003010000e020010406250207908000e007665800800e54034082c3d02c80c40003080025035485810f8440000c5004040041d005404403118550800c01401145003580c80545156200794105014211620403500c0c1e01c403111000741c0b549000c00c2d40082003403c400711010402a05100410429510401c14050108c4e00008010000102078401c0b04101305550540c50b86031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 901393992 1250 901392742 901392757
    0x30b120a020a030b041e0809040f0b0a0501211d01050129070f0f12031d03160507051201050a051602100b0111010204141309020105040b030a09080a0c120806012003 72
    0x115120b0943c0c6d01001703c80001f0b809002416a801c02034980e600c00034801b07851a05034500e40184102c0c0c8c00b8040c07944520300d500c41400c1500f2181c4110704a48010354115101041c100e940042c00000c0700d050300d50700f130040302c4c0100421000500100b002400324441c034255265080d2781c0880002d60b503000c1040220000d1066500606103400f410b500f41030098a400344102210002854a024031a920f5500030030745030510003110096061030800680c0f8054019281426203103449261000502955400e00c6100c005404c00700101c0c10f8241024a00c05640c0043d007440b006138250050b12003450741c0014101256000b0100104100c00710000685074049005a510b0701ca50002801243c0c10030500c034502b680981c166100c4170f15603d95524001100e40c00340c40240080c40400c410810241c00c24007468001d8101c203000250520341c1c2c0d0380d07005240e100c1c0c4090004200001043d8003803002c4518120152440d50600300c41034900302c00003c04039841c000d03100f2107010850000180b0100200103403080e6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 901395242 1250 901393992 901394033
    0x1091a040c0804050106080105160c1103030f07120302090603160e030d020c03121201060503090715030e06060103110301060c11030706230406020715020c040507030b120a020a030b04 80
    0xc0d0724454000e015035070031201580c0d9907082c00c1c0e0001f0403420520485202d034600c43d0145100180001041b540c20103e4030702600c0b0000306000c2d00c070040e40e041c03004203007140c01200d1440c0d80c1c0055207411000d01e2005007506040c940f0512450040d034a4010889a00c04021070200c41034190120040e14144525880302e90548101024005007030340000d40c0c0702900800728100e4120501003030082c501407143d0100e80d421282120010080d81d40244091600080d0080565030b43c00d455003909089140b100041500103034580c420700604c00400e100e41c07a0801420b207801d01103d02840f0f039551440c40103110302004c00c0301503030920061119903403420b00f04844c01801d8800041e95018014075019207000803034103200c001040c01100c030000c00100c40480c0e100703801900c1d1142c5407180c2040325000a900c110191702980d0b14110f100c1ea01d07841041c0c0300300ea0a03240051920812070034001005e003000300c0804203a000e41d805801690b5480f101000b101e41c0700e0200baa90755100c0c501408a0114405601d80 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 901396492 1250 901395242 901395251
    0xf1b06020c0a0b180c0418021011030309030307080916030816080408010b011403070c0b060a0909060617070506040b0307051b030c010524010c031404140a0e07020601091a04 76
    0x10101c0402268510010040c403c40c5e241c0c2101200f0042294492441c09072102e0356000c02400508010540500a208074280700d5803a604000d80c0b43c0c11030340125613000882c3c10000401101b50780144586402101100041681103901451050040e6507404054000080861034140c40c03146441400d69556102003020380b80d55982c0d1501d0701030180941520b0200b5a210801000740c4152020341c2e1180032569589507030030010340c07036000c00810040e00050304044041d0000c03498400c01d00034028400d12a50000a03103d151650802c3e203403030700446841c0320790000c0c1410007076507485405a80603541070034040f030760342c1c1c0381c0040c26501441002c0842c034001e1070b40450401c0d519000b00281c0000340341c04009201c503640d000d001560001ca115860080c202202c0c1c0c00c1c015551252110b50469807203400c1003075401004030070045c2146c00951100b00c02034000d07400c08a0a080c8401604010104444081068141184065100c6005000d584140c666800c0342d500303841c1c9140c001c0342c41140080c00400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 901397742 1250 901396492 901396501
    0x20405130b030c01020d080a020d0906051905010503120f0d02160c091515031d1606020c0604062102120708040b10080d03110408060106020303070f1b06020c0a0b 71
    0x2405001c207030099038401d014201d002ca00c02c1d400031800300f17040e50895a440c14282d43d5148000000c1d000303404c0e00c101d0107980d01c2c00c500010308103118241c0601d5940d45800041d003981a108015124140c009900036080b0319003c6422030901000d541d20020000703000360301d410a12003008000d000c2d41c140500d071340c0d03050108942880407890040098846410003401019103040b00c03500d400d405840354094540108a40d020498401d6100076140c04501c51141040806510074074545013810120701101a02558100300304c0781c04100c1e0061188054400904152412001800c040e030728030480501420005c02c1c101040a0381d5040b034078a1004034482c41070310704101b0f0008014030b004460071030300742c00700d90080354a6070f0101080e14221010003000b003c000007841c100318080c14422034500000f150501c000b0074070203000d220140c041c0c00315900442e16460b1409e001403441e01c1108030b5009100305554450301c1d400c1d00040030000740ea008100561348074100d841c002d140044c60180a0903901c140424070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 901398992 1250 901397742 901397779
    0x516061512030909060506160f02130c0e03060f01030b1e0a060f05030319050f070b090c01080c2113140601140319060914060124090311011101020405 66
    0x40c003000d4069512480c0f07094489041070100c2d0744078010190310480503c140b0108004504000b04024400c044276080316415030b0105221110280d8502e130f10581b95101c0d01205c0b80e010640b0350174207a0480003801c00c0c0c2003003024581442418000a020340b03400381d000805807031600d901007940f068032801c0c1d52414604100c9107c020702190003118140c0718031140c0050341d4503000040d40c0b41961070b00f54403003007214210000d51341640300b45810702c0c100c072081c868200800c242480a504c5901444041c010343c003540380c001450084014442e040040050010034003141e111002040c0c1e5105140c1d5000050302c0700b203006103031003050303401c01402554031441f024264400030400c01d04a403600c019030000c2003041d03020035803a4094601c618100c0b011085010001c07034034030303001241428002c960031050410080c02d55400d01e4826000b141c8a10072000b0101c0381c03120312000c103c0380003040d80352100b105802c590318100d0103012080c00e1410130080090242001074294100c0c0e004000040c0b013080e094022070f210 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 901400242 1250 901398992 901399019
    0xb060f070803060910181d010c080105031e0d0c0201020c040603030e030724231603110c06040b0d0b1c0203120a020601150c0f0803040b070c020105160615 68
    0x102c03402400e0b204081005d08003016850011380304100c502c0300000c0c18004000d002010003404000c00c0184030f07a0368628080d000e11450035426102e85e50403a844d818101071624100803040944900441c010b0000d404640100c1e00d00180102450250206062800102e14000e24841060380c01071505600104040d00f0444d07003400f004081c0c0c2a00c09045e655902145000310b04504400900c02d0654041851031080c565000c6990380c5594184100d68451020903080d0408040b070034000015020040506800201000070110144010101e540700750340411036601452140300100c02c000704003081e8501e11034205d0004690098030504c0c84400c500303202d4013000f4031000241d0281c0038000200e444002c243d81114125105034000303004a900c0c0c070360010403085078071500404005034a2410741c00240610340c4091400d007d4254a500e07400e25041550f920000504004140115000e4080060740c110341511490b00c0040002c06240a1604048000c0c10081c0c1c4400f8040c1c0401c1030200d20305000d00d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 901401492 1250 901400242 901400251
    0x308030a0b031e07050120010e0f06281d061504180b0708040f0c08012c0703020f03030c070314151905040c05060c07050405060a06080a0b060f070803 66
    0xc44030b01288030001c100c03038540c050200e8400f9070013a41c0144003550207030b02c0c000104001040c036001000300142400c0d08490300c0f4500b04d40643c000403850300f559002001000e41000b54003d00c25880f60b1210303050545441c00107440e104868540040303285c40076900d0703400d0b9121450b0300700740c9916280c184250041c80070ba124407284150b20301113401c44043e001d0203e0004440d480800d0900a8540300c600b61051400200f0460f80d0302c844001703d0f0009502c00302c440009054000000c6100318584040030401c021454095000c0c608168010009090008038001282e80580e0b28411b4142c002002c40d0031845003982040881c460100000208a505200010b80d1445402961640142d4210881c071550060701d5803410010100c40c403241d2003d041d8010358020340715034440c181081c0d641c070100b8115000302c06000080d4200490400150805000304c6600c500c0444842d0806428074001801d114000740000c1c01481d074904400c04140c48000c21285030344c08422085031162114a00700e03c20381c1c800c41c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 901402742 1250 901401492 901401499
    0x30d08040b0a090b061203160c1503052a04080d0203130e0c0409180204110912072601060b04030f050c010516080304240e06010e0606070311070308030a0b 68
    0x700207030b80300c10302c0c2c41540c3c0043da01c50000001d80d2548803c0040f2401850802002c0d03000030030030f0310035006d00100c42a1619200d01110010305180000b28505030444500d11401e043c1050308010b0800c200b98850f400c5800042d4440780c3c0c54013010f0003640c080c001d5800c11881842401c1c20011895000005003000100c0e48a46810701c0d82c0751111030162030340c203035040200c00c50700303000c2400151515000410079030407062145038419215000030301901c100d400e0b411010710703000403c003006003482c51484884a080344001d02d1050b241c03442c0400d1410004444a0b00d0405040d4a5000d02a0030340090b80289650045542c5580d1641010781c000010918211803074428800c40d21801d500840a0742e000c500c04200c1031110000c10b850f01c940350303400144111020111448600540d15010340e1400c10b6812440c80003c140107801007481c5807003c10b8004201d5403a0320800c1041030795a0b14100c0c1c2006c0d906140481c06191100d0b51180352045075000180701003404020440004003036130004101070004c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 901403992 1250 901402742 901402763
    0xb0d02180612010308030c070605010308120907030203120f0d06090203010f090c09060302070203010209040501030b0a141012170307210b0108010e070c06021309060506131a0405030d0804 82
    0x420848184180302040c0b8400409100410108903648082e5900c045484031951524683d95074010880c0c800760421500000003044450080c0000282d02d039000500a00503c0c1d02030a540009a41e1600b90203040c0200342e00080800921401e0000d4070381e40300300640140409070311a84040007940003400f500c4410085940009056006400f54070711418241d101c00c10040d0601c00d00f00e02039480300f102030b0382564080201001a0300c0d54842c0314021801a09070364a1400c0002d00c41081c1c64205050400365039843c420b000c21003070750010440c00c03140c030000761a010044c90300d0480c24201004031600b820080120070413240d1a0004454500d003041044040400106c04628000b150003403031000380000d220000500055281c3c03210907400c0100341c10000380c5500c1640d140310680c0e10569080e895003411090400624050303000b03c201900c000c8540707908090f988941c0034060442c5116110003e8613081007420728404d0f80040b540504005019101b50035070411010301b09010550303040f41c1d03c0703980 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 901405242 1250 901403992 901404037
    0xe030706090519080a180b120a1503081b1603080d060e091b0102011b0c05070f05180a061203030509060a060803090423090a05010b010c0209010512070b0d02 69
    0xf090b500c100c80951040441d8104003a00c18101c64a822112150702504110340b40443c40d107500c000980849048401e031080070f0b1800003292030a0700e009503200701880400345070030320009940d90240c3e14681007499041c13456401c4540c0d00da241120301030b84490880482e540c00b0003444040b00091815643c0b00c0810700c622070740d1b49581c01c000c400031103c1507003640041c124007031742c45808100709000c0c40051001043d00c8940b64690f170ba0a0400026600100d03607000c0c01441000820b011420050110704182251649804081076002608020307070014070421100044c400c9880d40e00840240800300c0c101000d4820301c1c50301400070401a2105021441543c0001d04100104e0003200150307440c11015504180e0010240300140c1103a10a2483e800d06180030500c080c21000070452103100070400501c00c1c444a803d09900315000006c0c101e0411404106d00005a01c543c010141103903001e03101259040c12800216003400425080703c50f00038000110484015403580207040c0980c0352010f4010b44548 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 901406492 1250 901405242 901405273
    0x60605092d010f060c320c06030705120406090605190e0a03020c040e01020903030d1e09080301030b0603030702180a15050d080c0304030c121203022106040e0307060905 74
    0x3092007500f0000103518000d01070640700d016070b1a0002d100d10000d850341500080c0c07004940038100081d06500310070700c0103c40c00f14020000c00c001c1c803000b036900901c0c5007420040140903128081d1100322444050003c18100001c45c1c0c00754000c103802030750030001401e18441400c40c100200130864840303401c181441551040104100715801d40c150001c7c026281140305000150205544500c0c0302d5500b032003200d5003a182803006040c0c066000c200020f0703c4000d011100800700150000c50b401a203040020000203201c1e008907410360390008200382c444d41d280800649107110b0014003e421801c03040f020140c240008004a00500c1a03000511500c0c50b61049864510b42c244543d81c2c0c085030401e03540011501c4d40b1300a03c0341041c0c0c081540d01d840c0d10303900d0b040356074091a4004a2031021120301c410600600c43d100804281482c5030542c944400301c0800707070314001c0191b0141c0c4841c07880c00104500e0307919540001103c001c0141680d80307070358450a200004002490042d5541e00a18116525200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 901407742 1250 901406492 901406581
    0xd030501090b10021b0a050405090303010e1e04031812060506090123060306011106090a12030b030a140309220c0e1f0207030b180706031e020706060509 67
    0x80aa40204074103400170302d00840c65501e51000c2c80e0031131682080883d103629207014052241040030011a0359524207c440034025000400000c21011080390a03110038140506554010350145400c000c0c004e210390600c0892046944420754984080d6850300c00c0210716041907100301c20495009245030f90352a000c0d10b1011240000ca0b06514411410309110b03d010000340d5000401031618088030041e54455074030b0f10900b41c072040c503d540481000000c00009400201c0966000c1c0380a00c004401d00c00400e41d00d026481c00103182404910352205002d00410585174030000c02801e500100d071a08a0303d10391450ba52840094003424800c150055501804c50500c103d00c1c064590b80c10b1100c0c0e0b040c003005810144000008600802c41c0001c00300754129003603130140081d2011042200904c0046501e00046c80d4480e0382414100303102c107005583c95414103901c1c41150003000da030b00e1025103071800003005180c0140394080300160502000c0304100c6454107100005003440c0c1581c2245030044901d61 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 901408992 1250 901407742 901407769
    0x3070e1905251b1b05060c06090606031b0103050a0e07090e01060e010f120c050d03030204060e0904150216060e0604030212040e06060711030a11010905060c0706050901110d030501090b 81
    0x22400303c03000342d000622001100c0c070452451090020350b0f07074596000903400d500104130305000340d02c444e050003078450082c424103400c13090880080c44102e0403c00c804058629108065041c56507070300008040340e416402c41c0482c16900000e81d003059440d446610014000612845000d618120780841c2d4030f0180c440081c16110103007241c0242900d011118030741609141403c48040000440001d103e8031911218082e140c8641c6002d80c440d17080038070003040e480603031074158804c442e40c10030b00000c0f81040715003441c00360f8044005a40c85201d6030000510001016005100d140740075030001420201140c0c06000d98031903802c3d1070f0030410125016189004e01e024081e4440c44041c013040242c9013103001403500c41e01c242041c04009081d0700000303003007031030070b400c280c0b00b0031345017007440180c0d60388111082c02908044682d1810302c2c61802c0c00340c0d6101b08500032082440b03000200d03100c0e603a005010322554190418120344c0b0188180b040217002d81000c0c810228001d04011100b80c1310300d000c0752445800c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 901410242 1250 901408992 901409027
    0xc020f0c040c05070506012310080a0f0e0703050d0912050c010806011202130311030a1e0c030b0705040e010b16020d020a1e0e06090603070e190525 65
    0x603800e0008110060110102082c01d1080030001000012428040103000300580700d0380720f80850304150440c1d2030a0500420034410204e601c0f5103940c890300490761640003158110000f540000f5501e42038014115040340c81344c40c1c0300700c503800420407100007000b07401c81a41d640e80c096000d540b08046d05615030114402003d0b40c014400d03105c1d041d440707544080d44c001014034080420b00c0065000b40220790100ba4003c003070001c4044140207000b011000100c080d4015001040f050995440718103051042018010b54030001964050900c071801102c1c4014527088075407800142010070f805000e5900c14403a03500a8140840001303020360884080c3d0303d41140354102c0701d0950019a080040704a06214200c1c1d102d180100040303444684102070502c4e05030001510103183d81440d10510948500400d00c610030440c5038200030040e10042000003c4421501c201b0445e0740301c4000c81605c88070144d42101c0d0b603500e0401000030001c6124404025100c07000703600c0310700002011084a4101a080304007a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 901411492 1250 901410242 901410253
    0x909050a080c0c151207050f16020d02060a020601060206090a0c140d06020f0c060112020303090d03170403270f0513090b0126012d0e0607120c020f 65
    0x8524440000d0000320104810345001c0e4096074001031342d1491402c00d9122030b81001c2071050950107100011500660f140c03d00504103019010000e07602c4c442c20488484c96000c10440710115110000140031039580101010f44906c0301c018000e41d24a02403160794010321448011803040000484d4041e001d94100c0c807444d80140c100516400a0040d59814030380040140d0884408941c0300d201030248402024006952941003007805441e017407041c3c00912074001c000d106a001030350004201c40340b070b45059480501402c4503043c01d071540d10050100341400da003030008110070158003404100040700d1000001c4001e083c0040246038841c6280642d03000d103010381c0b10510540c90004c0744012854130f14a00800d5440513580c440884160a0f8040c8500061a01c2e07554440c582c484161a040306e1414001c02080d40c03054003032144905903480c0c080f902c24004d0007003c44c030352007a005000982183d50890308103080c02800206444c00445048020320703d03212190419503c0443c1504c1c010b42000300811 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 901412742 1250 901411492 901411513
    0x801111908090d0c11120d140309030d0b012c010f0c0f110307080102070804150c08040302040c1412010501180e061005190c03020c0904081605030f04031b090905 71
    0x5500c4c01950b481902d40070201c0300c10500c1030360783c000913040c2e002069028080074180e619000d007810b80b6101016516140610804c02070007400015112062240d541c0404e0340c0e404140184d840c401001c9a86000c00c0c04400d071005292015003400820b0002a41c2d40705400300440f004071500200e0100090160300b06890590100d0141c0f030035080031000040640700603075038903041d840c00c9074030070390040310701c10b0002c07030704001140c1504000e800d80750745400c0c21a010400d036511f04109100d1808024480c0c0d507148004010700c0d00c02d4403020f13081c2803001003559541206103c4003865080134400da900050002080064081c018651541294418103030f0740c649480c3c01d01002a44402070070308004204007030141703403c0844003020380500b03905141c075500044069814002e060140041c0c0e2680110603400502c00096600012520201400380811540201a00c0d140c0d0442c85100140e100317030000410040180b0151580844040005201c04c528a40c2c1e2942040181d070484500603143ea0442858034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 901413992 1250 901412742 901412747
    0x3050402012123090f150a0c0c06020417010b1e1c020a03030815040203010b090d14030d0b040608071413020c010c17070315060f05040801111908090d 66
    0x2402004203980d400b00d550054082001c10041c070003c00420303007107003043c1445403000090040c40c01d10001d540150070707210701c0700d01c0000c0000360207400071074420360390302c2448049482101844400c0b980304905541e216a1410f0f01010661072071040c9280313501e80050911645031801d0680269100048081140c129150800c81020110981d040f000500c0c800c401c030040c1e85440021026510984408185092001c10440d925515050079070040b441000180000c80040060340d60700c0c142101e00b650b84e03545a00d000315401c8172011000d2410b01c00801e4415032910141c03c4030a400710281ca04000c07070381d030b1001660f0703813110b0900c150403010b80b030602c0c8500e290030400d9400506090355070f800342c40c041030190141d00712042c007195100010b02e40d0070340302d042e5840095016040301c2185002c0c00007101e50080e44c48000b480d48aa602409100c1110001c214010000d81d801411128000c00020324500704004090340004850303000800c0c425950120907000d07800440c0101503440c024402486010400d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 901415242 1250 901413992 901414037
    0x30403020606091501030c140f0703020f01020a0905090c0d05091b153108030d050603011505101125050306040b060409020f040207050c090703061d150a060e100305040201 75
    0x3034900b0070003845548c0b5800890100100301c02000e04100e15920f101c2e03824003d040c0040c3c0c074400d1400740d0040088500c0103511400c004140e40c81150400341c41c0c0c07501c8030a079010748103c0c5c25120103107081000300b00c1d0400380401c80717240005410080d001662801c0007040507840104035001c0098006228205114080001d41c1410340c2442c1c0441c003603400540c00710700701c2800c11740c40b03119a0751000546400d0781c401c0d8050a5003100d0203074028031a80348816505000040e0a0141c14011103040c9480301c2d843d071049082140c0d40d9101001d460765074801110700341803540c540c500250440c110b0030000400d03040003c2c403513104603008001d00e9502d0300c0c0d9008000180c91612010b0760300010400f404443c80d6118402804040c2c491001450074540040501100000060500041c140360000402100002881c00c58988140c5940451943d4580a4191001d804000b1058120000c810302059954115101c01200c0304120381d10303000152600c00231000e9400c11100280040d10941c7e0f18062425900c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 901416492 1250 901415242 901415261
    0x210b07230f1c06030f050a03020d091d0406021b0a020a051002060f04051e06060a08160e06030316080a030e011811030708010203070509120c0f120c1503040302060609150103 76
    0x454010740e05d440d01d5601c46540d0200740d4060704a0a1010300301501042103201040a90815208a034907000542c1c2d0508902c2500080244152001800b00a02d1350b04031444c40c550300d1030500102140b400000e94a041091040f8020082400d0100e542d180c190080074810110345c2c01002507079182424080b403144007400403903051003070003c2c1c0c0c407140c1da486504013618050100103040d40e280c02000c010004515600140c005d401800012030700c40706d04c106020654041c10450b2501d61509004245140300d06c0c90700144014680c0f204100700102c5500401c004081035400703201005800c42400c0c00c843c11031002d05803c03810ba8031038070002841911b1070b22010100405840e845950740542e1820380c2d10031620f0100203100014480110b1901c1024501840f0800c4010131230190400c000c1140c1301503030380c6038030311540040e901000116810002c6a4400002030702201c0002000c01100913180c205036001ca0250040100244081c1000b4052074800d0410b400078008401d203050056000301445c42 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 901417742 1250 901416492 901416547
    0xe06030a2a06030f0f0606080c07020a03021c0b0702070e010e180709050603010609091a220f060e0c09190e010513030e0102070609210b07230f 63
    0x14110010306a58070300c010565900d01283c40303400c0d030100310111841e1992080056151410900c10a5480050180d1050380c0849403a610480e81c000913800290740c0e4802540102484203074107010b108c070480480701910a280903005504c40160598030307140a8000c140c5e804c0c3c4600b004108032811a55950340041d070312040b410007402038080080c10010690400e40640d601c0343c1c2072210508003403040200808201c603041081c024140c0d1142c404003403d800404121510702e01241e14941900110100315085001004107143c151401014119941ea01a15103d107088040b0002e1803011030304941209000300f0400e9030b5074481d002a5491803043c01340b00d0400c1e540b1814207402600c24800c41b80226410a43d5074081166131400a22401e9411030650454109100030080c16400034005e1b010340d49071246c00707824209a112108007809807050064200035091081c0301007030750008007042c10152600030032051101031050031f4405200b5180b171071201c54030400070765134100d0750f01c00c3c440a01c0d1640c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 901418992 1250 901417742 901417793
    0x120315240314151203040f0e0a1518050105040501060c06110903070303080f090c0d08090d02041a03010b0109050607260c071d040c050d06060e1509010e06030a 70
    0x4003100030100d04119452401d6090f805024409464082da2034140d0f042e40100561900d814a518025100041c2c4070b581030300701d0524041080d000140d04147d000c1a9181007212070b0360f55991562003000400ca882d0901940703880e001091030f00b454040e00d4180c55064481004d194256aa03900081c100403a070940d10310810b2051848541e03086c880d00c00214083d982e2100716007480c0081084451020348090b00952000c410800a0b8561039101c10f030103508101000d071196440701c0460102c10503070000950003898040710440c08460070000545504c0c041d0020401e031507a190040d03407450480d015150380035205201450000305224035054002031079504030401c3c2050b03800001071381d03042980580d8280d0800602800880d90004019907501200300c0310380e20f01c0c10191207200c0c9248040c000c5c140900e088011040601c422078005000030454100f801140b0314041d18500858907104030744520902c0400000a140c1c441840150f0189a005028040d0443c05503070b0500300041742680c5000340b4890 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 901420242 1250 901418992 901419011
    0x50403080706150f0806090606030613060f020a0906030c08010e06040e0f010c031b02070b0403030302251412032502150c0301050a360b0a031203152403 67
    0x400ea00c0d0801013405100550f0b00c0307030601328020704040d001414021980e01a40030040250382c0001c00c0390300010300d040200d591458a062807000741040090241d542400000c41c80c0c400395200c07942804845169a040002030b5009070b0855480c0c03002c2c0304800c80f007145000401c0d07003071030700d680b103080c0000703038203080b10304010380b801105095401104c07070440070035a2000f0302013450f1150484468602c3c04c0d8405490b1381401c104510300640100d003c0076080603030110f099410640344003c1341e031903418000106a04030000e441d0114190101e4640d07006280282750010b404c10680e5025a40101c04003401140340d1017184041002c0c050b03194040000310321031030b40200140b4200c041214060428802c1c2a44d480d03041c40c0902202c01142d9210540c202001d00103d814844004403046103070342203040d00c80b20703030040601d0140a4203a01760419071180c04003000100b000340c1036041102440302a10203000e40d0648410701d0f40219030b1442802a40740f8040c20104004128403c5900102414180010006036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 901421492 1250 901420242 901420271
    0x6010302131715060603010602030415360b0406140a0c0b0a0902030105160206191d07080f0703150e031204201c0209040c030501050c0a140901050403080706 69
    0x80140b03100410303802c035072841940060040d40e080d601c81819105545154540328000703650b8450340c4141d540140030b01d03c030020b42611a448d4402e8112505441c40f0020071070224060b108003e108201503440714485c000503100d070752401514115407aa89902041c0f5900070102005a80030046c05010000c0080c1e5800c00281c045128a02660343c085000480020502c18103084a0000e0710540c0105a158040e2507810f60001788150302071036a1140544062144070318102501089880da04074002001e0005140100001c0ea84100c40700300044605070340e81c0002c41522182179001c05810078128104100105050307400003101c00345040c045a10b8000c403683d280840d0541682c04035608003104503045403100c5d01c51102c80000800702d4100d1020003050483d0380010214803402405100503e0014041c4034240202d0b50040d40c01800921582c548800d00ca540740e4071030b2601001081c4200c54000602e28260203075151100b06842d1285081c0c00c503101e9480c5500021001c45100d512403190a030743c001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 901422742 1250 901421492 901421519
    0x60402121602120319020904150b0c1908030708040c0b13030614240f090a1b260a15060503102124021602010e040c080601030213 57
    0x805150203511a0441c410000742032002c0980d0b0000908401d00c02e0002081000844490440e00c219006907a10451004240030b80900c82e8000072010074941e000503070328501c0c3e00a101c0e920607181581c95001c1d4585594403c00c030520720182004409000261185008400b0f090700035000304100b00885070b445240707040a45c0f045040481900f8070060400c00c00900b03004402c82003116098000795446d200c480c0c4200c0c1030051200c05a050105122440740b91201c0040000f4050080e02004244ca4055000d00141015120881d9441000380409208511480d90800811084c2070501d020310241c90007084e0b4041e014100d94802e0317a4518080c0101000c1e90100c1009002c6522015145c0c5005c0b1005d42035400a5071098003250500c1403000d45007a10340b1580300c2c1c1980d0042d118080341110090401e5140100c0004000003480040c28010803401501c006502c0c5200340e982d02e400600b4070050005448500c0150b00100b801d01002c41c00c2c0e51302031340140403101001a10307141c02c80d540307400b00348050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 901423992 1250 901422742 901422751
    0x18060901181e06110c0103020f070204020301090e120a02060703051e0a1a030f0c1e0a03060905010c0e01021b0609130e0607020c0d08030604060b0301030605190b03070e06040212 78
    0x8030042c03800d040c0328000c007241080007041142424071032404400c0000b6100c000550019041550004c0c403003844803014826903000f1a0060800c41d140d603191740c800c01c0200080b00007030700d040c895056842080c680c21400c41e94550702c0388d405010b0a4403031000c16000307044040d18900703104200220b040c05114040b4505885160726250200d0f0f80c546009810061000840c0c80f14000c1d04004000901044000b5050b80d46041c103440445032544425180640b4801070806150f2210701c3d200000203205e0680c001c0e851560052008103c40103503104160b031007440010440703015801562501038183c00d60090705d15028000b0f000700d40381907204030001e82d40e4040c048000400b10390741c240002825100300b0840394010410f000900c40c40041e0340016600c9000c140e4000c1c0b51400001c005113a42e203032a000500201868400a80c913540c680ca400303c0a8101107031200c0420002d0480b00ca814090f50048482034480600a40f44160924252852000b00104160342003134003000a800c44268a001c0d40740b25 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 901425242 1250 901423992 901424009
    0x1e0906070b0901020711150a180e0112060b04140103020907090b1902010e060402181008010609051504110405060d090b100807060c0b0705030a15030b0114061806090118 74
    0x2036680c40d16007900310742212099280034440041c141d9490b0b0f81f14100716510240d85080900520300c4c004141110f00003580c000c0101c001f0050000112884e0282c60304120612498080c003801036400c06100485041420382d0070f1484014004001505008802030303003046480c03400110050300d8030480c0d03005a001c00c42844c0c502c04a5040041800e60a11810203108011030107007549052540004211b4a480ca41c0903006d840a5004501c550724840340b181c0007807481500a02c9000ea80744900c400804044900851245c141408000245013500c5031000000c074015095003400c1c2000c0600c44250400504500120b41c1d45e60034201140222500d5440f44203041c984d000e245040c00c19031414a8682d5010300c4c10b10810208070703800181180d19155001441e45001616682e84580b010090711644006a100d0020541c0c04414003c4682c500d07410b84042c1005000d03000d8040d0240403103845540801090765a1103041d41d169454100c0080548000514008038074003110602890b0100040e80308654 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 901426492 1250 901425242 901425247
    0x303170c09061b03070512190509030c091e09030d110a0f080a0209061204020a0510080106181205010f05060604140423070507020f0109080d11030d0e030c121e0906070b090102 77
    0x200d40c0001181c04111300d003271402c2070800e046400481c1c1d955080e410300500c01c44294002543c400394502450070382c404c1811098086041c1405403036223a234804100d013680d80e424030b1801506591120115034211170b1035075440380715001803001111290b03400341c4401e034815020848202255110070250071202e2010340c45424904141c07040200c03040c2e060303202c14000d504100070343d0341c1141c0117501d46045580e00d0809040350101d281803909210b5040d002000181040b1010001b44001588011403800c207001d01000980c44100030004140280d01c112400100304100e42e81150030f040d0400f905850089201d1146400d850a0f0303685401d4003240d0110000c0d4010500c08250f141c41c1840a580c1d480a007440b0110f181000c0c2c00d070b07880750403000e40002480240300c208001c00c030003003007110144210040204040099001d07200e40380d9001106450007031140032590412020a0401c0758541c04194003400d4000e0704140c01c40c44660810800d099200c3c00a202e413002040c0003401c5a031282400c07100069 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 901427742 1250 901426492 901426507
    0x1c0210092609030d0207061409150f07020f0603060a03080c03090301020a0810050118052106090a1a0127151401031508061801060f0303170c09061b03070512 69
    0x18030f07244c0381da01a0411035205480404c042c6402002d0f2000005045500c29941c0c02010081010b0044a542558114100103641040d450502001d025407a2003118540c0e0401d80303110400c14070b804299180c41e0700080d0000c0400018480800030049404140103407410540039000080c00c9030000010b45010403188000c2161000c46800d1980180c182401e00200c4c480944004d501040c915000c2d0034050084440008410046940c0012148504104480580c0307414442c80707807280b188200c111015000d45018280039848002c1450581d5501907007010394848941c050544c1d0148070076a9001e00d0341d6148551001e00142c41528058001108015401040c401c0018121380f207078200e42d0a0112a20800d122078400883d000d504403402c2c501443c140171507055041d004100d1707a4803046c10f60841000010425400c00b04a82c9020081422440300d691210750107400c0d44600010264083c004010f5858100000c2e544540c0c04406401228105540da9072001c0c40c01d24200c01c3d00410702000318984 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 901428992 1250 901427742 901427749
    0x1032d0c08060702120f07031412040c15020f15040311070308090f121c030e06090d181505070c0e0916080c01090905040819080601021c0210092609 65
    0x202030b24410f007017803450000289662111030040e020018100401c90b070700d075103074413807910181c0d00c03440f43c4680c500149050500e00000c0b406500d10604540e25404103007907400c41d0011135540b5021020001500c18503986400c8841d004900030000c40620074404101f000a401c10000040550b02c42d0300390b5903940034000c08000c180c000706803c0f80d00c68107a02080540c2c0480228801d00d46d028030310340104104404402c2035000d070011a0001c0d906110701c10400601c100005017910481d012901d6617041641408800043c00760b80d406114090783c1c40000c8645080d102c3d01c0105400c034000e8014410380e9481e013440c1e4901e80da00780e86042c01980400891425041c5030881c070300003094804000c046a0031282e0018001c54024802d0000d00b0f0f07902e030001004d01c011001116804a016015082038a007588030103010701c003054a009005200b01214503101c500707040c100110340c030043d0b0014282d41c400c440711080075002c11082221004643c9181c0303d003000070000e50748034038520702403c07a40303030300d804402d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 901430242 1250 901428992 901429003
    0xa0f0203060c03092e02070602040306111e0a030b100e090105062106040b03060108060403090927030905041107051204060503071103130e0109050f01032d0c08060702 73
    0x18921611420828004d09031400607071a400c1c030814040214030403500c0c05402805101011106050b107000080960070440c495008105891142208012250164100104502035a58030f0100100d81c0250700e100e180300c900240240f01c00e68034021550840010114a1881c21a40d01c1000b01c0c42c2902800021328015464601605042d0740c00c50070074080da440074a11002150300307845407070b407414045901a00d80d90031140d00e03001d020b411510507594804e0000c1d40c5180c215001d8000400c550303000300341103119000b80800711000a0701610100003c401c401d4000b800c5203030460070301c10814400035944d200ca00a42c4104121151a5500d55125061941c10a950a002c00c01020742c20013051005603041810780340c1244052411101529941d01c0d140d140d440ba00e184c1c2040c44a04001c005511400c43c5d5003581038582c613400a0010761201c1a4031401c1c02d20070301005000c411300c450100300c60200300e00c2d048152207689143e00c0c0927400d50f880d00003000c200d5400005050f0002410486a5a0108034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 901431492 1250 901430242 901430251
    0x14030f010b0f012007030804081c0c12030207050a0605010614030f07051c050c03043011030412060b0103151503051509090a020109050411160c080a0f020306 69
    0xc1c4524044000011540000c0c480741c541440502078803105403090384900208000c3c511030449011940701d05001501d40c0240c07082c07480f00c0c0f043c2ca07504241c000401003041004451500d50602c00002556810490b5204010002c200b41c1e00f071040c0300200c0d20801c007101d012401a2000034243d41444401411028243d90440f5150303001c0081c010407055024000e071340300380c0d0b070328105072194482c500c2c03805500012a00340c0c1c481ca041c54103000760303049481c00540c040c03071007001841c00c104032462070030007000c00d081440306901d0680301750006802e02030a1980102c0c980f40003031b44d01d01601d41c02c0408071240c0401c000d440c00343d03844030002c1c00d650301440b0710144101c441c2ca0b01c80013145885904219540090100d1003050b842e54049800c0c07119045181c10135480040600f0300b40d107000584e0301d58901000000b640012181000000e00c1c1c10036105d11550343d011a9a4580f400304942c400300d80c481070b8403400b1514007060301400500c0c40b03070910142d418948a420482d84665081c0101803411202a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 901432742 1250 901431492 901431523
    0xc030603110d020a0902160819020d1d121e03030f1308160615080a0203060a0524030a0c06050c070e0f0f0907030510021c020726040902041403 63
    0x803038402580d901d0032013204950641d94090380c3d031006908801c141e00c1040d02d0050140401040700c0c040d0901c4061902400e42c065400c64141c4001060100c901e003200606007000341c02c0da101070845a00304188446414502c0c4011246410340e142840c1030b004803842050701c6c0c0c030f41000c03090114042c0c44010b02d50700090803410000c4441c41584580546100b10051541e41424039806c003810441036402401554000a64007420035071341c1c00c075890701c40854003800c82c0300780181c400040d042d111903c282401803120200070603c09541e13100c3d5249500c90390801c982d0500c1514542d40c0050030100740c09024207401c3d51581e4803100003a101d1450442140c102c1402d500c0c2c400b081000601c012503609900941512000d06981c84030900603060220ba074002034803600428100c101811001e4000f40050119030715102402551403080e14101d0040c103c00805c80146801045a20405a4074640040c5080940705142076a100d1034942264400d80c885510500308500b540d5440c642482415120440c45 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 901433992 1250 901432742 901432759
    0x110a1b050103050c0f0f07030e030303040b04030e03061605070224211b0906130b13060c0b0c1b0109050106231f0225030210110a0303110c010c03060311 67
    0x10100e111940c007481283c48441b01010400300c00781031044a1310742c0d28041c0641034070b50f2414070341000c13149050f0488080d404100744502c00d04032414001029803186140c0c08617858000307049402200c2c0c0344c0c8400c000742e9020840c038000c0c1c0d01c07a00c00d07010400c141d00c8401c58800d030340d15180700380301041d038044c105e8003010b9030215020412031881d030f40b40b0310743c0300d5180715085540c411407600022031900851600c400d050780036010104100701000024a11403035640392900740c20b075440804032445020040b00404031801c50020903a00c490001c0902a1254140c0c10481002c4c4200e1002d0308503401c41c1c5040d250750791241020003001c2e4400da03660b0003038800c0590520f074542003000482d10228010004407003c030100300728021210320074042004013800c10440b006440102c0c0f55104084052400300ba4481e4011400d021442c6004c0c142009422310800c01034800441c9a4809400505101c07901001101040210044c0100213106d8010240c034943c40c0000c00c1d0b802c50078520080d803980400e4a0144071513 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 901435242 1250 901433992 901434007
    0xe01170123010c051b15070b070914010509060a050c06040b0402010f0504081b0a05131a03011e020c010902091612050601020318031015030302101b110a1b050103050c 73
    0x4143d1170314900c82c80c1901c10052509134049880c400c401820a9884d00c8040342542c1081004801d0364064601540c400502c0c5807283d4000c24042d240320202070119000f0442860030703003420000383c503c0b0186400d106007000c0c0079808550410720100c60455090b660041003008540e0090707054402c6030722500e0a141090708081d4a40d40e14041e14244640070105d20100344d405035101500c3c0f03006820b02600001c1c205811210030f0001d054514494207900c05440300e1880c290034144240c1c040c0c03078511110340c10406000c00c4044c0082d40b1081001750113540307424070040961144500c0740d005280c0700c1140c402464507404003c007480450a65803a03100d00703040c00d0100740d81c0e00005403680038012250310604070508400091400244a0b0003075240c9042c80b8490200c80115100503045a0107a000d44003075030001400a8111914402c104410b0011740c0300d909000c91184207840355080700c0030308580303d406582c1ca9180d01c2c03507001500c0c007907240003500f000e020b1540d02d4045e0075004204903050a04000c0f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 901436492 1250 901435242 901435253
    0x406020d0903091a161407150c170a020a0b3301080601020f0c150d09080a020d080f0f070c061109040c09030503030106031104170106052d010e01170123010c 69
    0x100b040c000e001000c400d801e030a01c06c50140710f048000d01088522840446030482d015000015540c1c2c1510098451001180084980011a1036800599010b0b0691303000b96642c901403001c010303104101c4024055010410b04042c92200301e03002078009180c0c04c100d07002d100010202d000003004036045400132215030300c08080015680c00c1c034400031035008107242c11010764030410380030b00b901e040f40b014205590841071054200040c00c0d80c018980c00d85901030345406054605400a80c2e50b03141c61101040000c9500b00351141c00c2d900201c883c40c1c60081d504003900d80b5030a841440f200049207100008100c01c01d0b14051241788184c9415040034420319113140c407401e0302c900051051000f45511807144144140e41e0908940c05407903404c01a00c400c50002485074000c2005010f01c600402440c0100c0301210792503080090b8003804030b41d031100d582c0070040045800000700323040c490502031098400b12101e04602141406020300261001e004000c140501103240e0841050906008607402003001050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 901437742 1250 901436492 901436527
    0x12191401090b01030e0115050301050f012124060f2313060302090c040e0601030b0d15021c1a0f01170c090a0e10080d050d050406020d0903091a 63
    0x314001c0d00061494800401a00030b00300300c40b00e0350340d55403170011803100520f4051242010340d0800c3d0300070010340ea16440f01034000c91080c05106242911340c00c000708140c20400001e00550b00c0740c0c1d46100e80315030424000c0268601510100302c0c41c1e86070102407200309d010f284500c005205601840c51011a058991400502801b4040c1e005944910501a61200c25007020b00155800342c00022503107806100310b0a150031500500280606840204030958400d00410712000b00042186ca034400840e03465900000c011488006166024050f80000d00e0103454901c03003216004201041030f01c10700c0382c000c804181501c00349105280e8a45a004182d0388800c943c1902c03440c259100c2d415451700821081d0a004210100390f10040b04040861503a866007207141c0030391021103003854180c4c4c0f1b505ea1103840b40e0303441040500151041c040111840c1315500020f41090007854010303e01004011844107030340480c1c2098010581c22401080081081c814800600144410f0107040c012900c0e11008040e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 901438848 1106 901437742 901437749
    0x7121a01121a041104050a02070303150308030c0c03090907111b091504020c1b1302090906010c053a020604080d0c1412191401 56
    0x540000545204a82e20414000d103a28014030242d0300828014400c1e6580d590320240030700d1503211482078a004100540d405607440d0401d040150076a010715950141c40d036a40f000410100d82440180c0350004100404a40c0c1e9211503015a883c5004110341954408084000d1050160b00925141da12183d058180c6030320f007801d0314000b103008580c040c12940210060002910180282c0c0d100b0041c480300074001800c050310300c0c039441d1502010180200c8289030001891440e807030b0403031190b840140494400d61034607a102c000315485203c060009410700280d82c5a41081102c240b0940d00d02c11104514500106544044000c05a1503002c00030220780a0a480e601841d1020035080d103e103070885240c51424940c11001001040c02403050020010707042e40c403048100c0e494000380303c82014000d0142d4681012804101146900404084514904028404a1060103050a044 = true := by decide +kernel

theorem cover : BRFrame.Cov 901258992 901438848 := by
  have h0 := BRFrame.cov_init 901258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 901258992 ≤ n) (h2 : n < 901438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
