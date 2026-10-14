-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1023
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:52:45.931145+00:00
-- url     : https://prove2.me/submissions/d7b9ce9f-f831-4aed-8cd0-20d3100d6218

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 183812949 ≤ n < 183992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 183814199 1250 183812949 183812953
    0x11010b01051e030709240215010b03180312100e0711100f060f030605061201020901021005060316030803010504060f0f150c0b010b031e04110f0d1b14060309 69
    0x102c1c020080d04a1a0009843c40e42080030102010135580c0f0000d0030040b425146001102440700c1c4404004c0c40c003541c0150700c3d000045607500410100c07030001c00f07480e009100411007089100d5a07520940ca54000c40031005610101c1c21306101000a0f5040c80c8001d80d900c1c80114943c84da01c800042d0b0301282c4da0780d0300300920342c000c4d4060b41c0c804840c0e5001c003a00c9480c0d1400414001d5840d002840741030b180c2d801c26281035680c0c4040c4620307032526020305541180300000a42c20851800e0000c1e45640000c59580402038840001441958051010008641c403490649008545038203001c00d00e80c00c2401030f82d00a9240281c041601011214000c1c11074040040c1c0b590003e0410100c00785d041d020403504828004080041c100042d01685603c0c081c1c00d503100d40381d0b101c2c03414002074696042c1c600304180010140d4018480401e00089506111f00001d4038039862290300328011904842c005030016200c2c1c1d000717a4801c1262142c2003010740440b0350100394030210000354010001288001c0d0b0320b80300c1076 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 183815449 1250 183814199 183814237
    0x109030b0603120c01020a03230a020d0615030c02010c090e010b070f08031906050901080303040308090f0304030b04020406060801050604030f170415030c02031c1503080a11010b0105 80
    0xc00605030030741d1140c000341c241c903141e44101c168200f007a0044c880103115650003241020000d0350510500c402403980c601608030300c50000142c0c40694002400e002000350300085c2500117401d070307600410010201c0307101c2803030041c203020b60041c010b1210841400c015404c19214180170b42c45210640c041d0f441d40101e00c5d005034680032207078005510100d021540c00e0150f000c6200455030010285104040d8011107010050888408104407090b0b6040140305101103030041c0301c49140042a658015818100360105031564241d0031714005403201051070b81c0c44005804010010360340841c80c040d920a45052000949850095941407024000d107034100206102c10004501584c2d50380c02002e0040c000c502c010040030703210010550080d00503007103100f442c0b800d404c091641403040c0c10b60711080d0b1000d035003041050b900e540680d6550243c0404080d80b0341045044081c100c4801000540d8070011007a51101c0044c0082c190041c0a20560780c6035203420303103451541d4000c0c4219408200890000411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 183816699 1250 183815449 183815453
    0x10506090a17100c2a120f11070b1c0908030402061602040c2c030607180906030c0807080a1e030309020a030c081209031b010c060615031802010903 65
    0x15440300d40b41c241c00345200303040d1011520626032151800540c1a9a00e15268490558024005041c024240030929594800c403c010402089488400c240140791031060000c403d1000c5902e101d4501b0248081d004148001070601c0640c0010074075043ca080600304407d94440300c1004440420401a04146041000900520300507008090341c00e004024011018496000309044500c00e008280c00308200c0c440b02c1750004403902500c255502602c0382e032444050740001007034441c1c80152101082c44410840b8240260482c0c407014064200d0780c00820025a40f800c040740c120803907224410107402001c00c04508121301190035903446802020f14441c400d40401049a1510041da09a04165494100c100145e5810720750400841c015203a24100c1030600e407032581031043c800450000340208200d01840c9071008035a0644054484c8405802600742c03c0040c0e6106030710700d500a0040e03103800d50110b100607800c5000c1e00e01c03010a58040008081c21080041080607440004c2e0128561060800c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 183817949 1250 183816699 183816719
    0x20d0216080a2301020a050307080c091e04020706181205041d04060902120a020913051f021e0706050705041d040206040b070b0f07080708010603050603011512050105010506090a 78
    0x8203c0d2140d00001c84120341070780000c4c00ca8020032140c50001d4170000c140009540d221146075000034401c401e4a01e0058440e0000e05c0074907c42c2a916110a101c050301c0c1141d5071030f0303810740b000f030b9804c240d0134400c80ca1079112040c18100e00d0320007141d44010b90406548454440c10585080d81d540f101d03005c05d503561807452190a1500100f085421503202d95085006031110312038080c118444000814116030b2078410060003c1c00105682086070207841c0c00710116000096006c0340c0c2d01004801e1881d40911000000684210001b00d60840c1c2c0c845074401907180704900401d0303880d0003413030200203903228120f08858a00c911700c01e030f100d4030304c0e032489505807148451817058005200400a13860940d440c1c0400140e074220b00025640386401e1020085040407510701300307502c17620307510340303110300d40b0f08040041d01d5a00706000700d200f0180d0f50000200182c509500c01c06240554541c81513043d40e807003404840445005400b00c80079401d220001581d402c0c641c040c5c0300c024400404020070f032424404418 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 183819199 1250 183817949 183817973
    0x30c090e07030804030303050a060b1809090c15070b0c0901090311010309170c0705040204210309240f0305090c01050903070306020403060603120804031e110607020d0216080a 77
    0x100d0280254207002001800903001003008501c00d0300c6c0801c03145404c8103010202e440079405403418030010004401c0c203c1c034801400d240c00704202e5003002551604865503180c904580506034100d0406441001150f160401801c6098412808003066a68a01c061011401450202404281100c000384000b40d0404c41c041198079040c03400140e00181138407507030100b8681c03540808032048005241000d0342e0084c032031400541002d5900f5441c05261000d24bc1c40e0310781e10710703114803030b440900024170400d48650310802c010702001e00d92415582001446480780801c1e54600c00200b03081102c800d031100e009028942c86908110050480309520b1401524a0f038404028160b0501500f5004030010b110780c4081d1002d140184000100a130451600040c43c483c0701030100b003400511410000001e80c8940e08031101840d0326002c500b01c618402003652900311070720b40c6034414043d08040101e0554005030500d03c900c4160308035500448000410b440325201030060300195005020319501040f9120015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 183820449 1250 183819199 183819221
    0x20108090123150405060d020f0a08070b0a09090e1c0504121103010c17060f04060b160b0601090b1e16060c080609010e06040506040e0f0114070801030c09 68
    0x800e151052a90300804845090301c516035644069043c480d814410105414840c0c200713880c1001141404030000d054030005020080c4140102c07441c01002d078461490b02d40c000c1810700101c446a50b00c2d818540076580102144000007983d02d071001442010a026003a00303804568080c1c0410307140d28200c41440c2064030020300a04c03104000000d080300d4619007041480b40a200340400340c0b2400404c042c01e540710b12280c50100504840001c1d2241c031003075a541c2c5c0220080b03400501520f40540454068085d80d070014941d071801003440001c00400900c04003500c0d11819481107155036034001035071259840d01034040c681d0414049a400190071000341e4000304400c0349204d0030100103100740c0108100d43c000888190382ca416481d100035402485c1c1c1c641100084030b115403075605200ea0341c441910004c282a10840c0c40310702103070f00ca4545500c0300d040e02d20320000740d0f1034040d44106214081c1c59140702c4c059407800c46200291b05c00e441125854140e0703500000294000d8034203000103015205c02540717 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 183821699 1250 183820449 183820451
    0xa0f0204081509010e0d08011403010b04021614030f090409020a030b011205060703180305031b040801091103010b280801020a0906080a0902061603030b0637020a0201080901 76
    0x109100108020b8070816200b031010703486607450076114060940c5c200d13003400c0f0150303803011082076040c6400072582415111a420850404078400d070029000d00800f1036282c3d0000e10018014415020b480900e51419009001e28114000c1c034000055a9100c0d5001f0f0114454083c0161507040c03605410404046000408a10f5019103944802007840d0003030740041d0815011842181c10171506101c0140d12001c2414204401d62510489519050841320000c0c00c20400000040040c10762448946001404440550301c0300d448115242c02043c06210568068002030816105450140038030995228081d0001d110800051300095a00942644c0f09210003200751000c20070140034405007001074202d980b8802c0b01c2c1d1401d480500800005009031b8641400c0c004044090780f00d0f80cdc103d0392808400940150b001100e424120020500420302c00c2d8400c0d030008040044802c01b008a0801d404120520b6110310008400350303440c0b0700c03018000760240c1c2040031500055801050704542c403494140c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 183822949 1250 183821699 183821707
    0x100f0c060e12090a0e07050904091401090507050a08070f050d02030f01020f030f0108030304050729070c030201090e19050c0d052701020f180105120108150c0f030a0f02 74
    0x8507508208240700e20002800b004034100c106807500d8100c4500a000d0701d1031204140c100050000d03c0d52007045c66850140340c4804602082100407208140c00b42e43c000d0080044031501c0c03034899211030035032250302d10600304001c1c003007103412011820104854110043d03428403071400060124120098000707a900d4000e0381c4c1c910f03c100a080c00140001100a0f0f09103130f49151403031440804800680242c461b40d03206004220001d240021084c0030b0701c1202d032a0101c9542c1c012010590f812044148803100503021807a1400c000c80f240d81101600c0c400d0b21007000043e196050040b400f10103c0364401900101000c10181d0b0450350b1000c1e401a0410900a140640300d402003001c1d00c03000e554038041340352003040e0720f032908030405c0e60303942da42040303200a42c03509080301380c10b00081c000c22011040c0f104903040d41c170240380e004808503000d103c030b403401c0c1c00360341d6945034800d81e1514007408002c50601e500b18005010300122104803101c01c01c01c450114296103448080d80001c040e55101c0c5254182d00f04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 183824199 1250 183822949 183822971
    0x108030f190e0a0f051e0330040305031c0c0507030e010c021e090705180f0a0f03210c03050d09060b040203010f03110a08060c0a0903080a0309050c100f0c06 69
    0x16000750081c08800420110a91829051001c1b48a04a03e4241c0c512950300c16001d40d540c02007a52a03945011201034007e02c10350120460031400030882c401048840000d00000700f11003c000b07004a090181c0a421201d0342d000300c3c50f019102c03120988800a03208100b040300182c000d0180c14040030040c075058017001c00944c08201640864940d5404400040443e850285000300041da8084024500982000c0304d5610303043d4040f5140e40c0e250b10418080c00c410307000352251103030207005040710041e110245980c1d080654030040ca5101001e03200301c91300e50080e41c0a0040160546a640c182e6a1925240304210701ca4000c040e126130488110f41c803502e48081030396450020718064000042d20080703040c503600d418414020035410f51401414070103420044000301250541c3d0014070465000e598a6038128100d07101d0480c0d0700000d00a040121301d00c4c008582c154044800c280c41a000c613030b800c00302034003044800f40f0b100d250a0005403400020401c280d10400c3c1c810401403180d000415252030354 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 183825449 1250 183824199 183824209
    0x40503030d06360209030309090a0504051204030c090b0105071a090c0d0506060f1f0306052707030e0a020306090c1f050909040f0203150703050108030f190e 69
    0x291004249940b951020312201074100303400c01c03078108141000d11080c5107038601c00c00000d043c000020055640480c0e0754610f903c0900880c1c000c0030000b0008900c80c03525102000c000e0400340d80c207562354401c42e801c9104042c4544200c1e021350b500030040c5c0141918003a95030010700440ea50300c504020301408900002450000c07000c81c0c00f6000b0200d03103040d00c1d080300341602d0034440010765440ba001343d9142c40c0c00b0840115100c1d40000e01078504000f81c03650f40000c50a48080e8061340203140c1103000050300d03000d51560260050f5007088801ca00c4020510002800c00c1506201403500e00b40703440086104680250710250715941c00c003080c3c8144480c2c580011741408003c90352081c1d16000b0342e50a9210b840c260b2081956000e44a03803124104807a190014498020888400e00419111010405210020404001c1268001c0842e22030f048007000e45c404030bc0080d14040c011038140f200124104101000b680e400c0c00e079040580b400c3c030041c00003880c00100865503800921200e5001081907480b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 183826699 1250 183825449 183825457
    0x307030e031b0c0f0109050607020604030c090b09131505060a0801060306020c0f070803040b1e04090905010b030c030c131401230102061605030415020a0f0207090e03031303020304050303 82
    0x4051100c045882c0c0d4240103800d004030301d0f0109200c0c44c805400240307240c0c0c205804c0030030b5071000d43c0c2c02d94445c001c07072010031024400c0b0b800c050310200740d842000a003601150042649440180c030b00d0111921518040303030042560318401420400840c803554214003e5502c29076100800511003400f030342d82d0b1304103c2d00315003460f00103466581d000901c01c0b034604400c126190041c0c54400003401c009285c8883d2a440340158010b0785104000001e16000c0d41e00c04541400000306a00748540c0c1e00d581d980710b20401440164011070700e65081a103070300c1141c500420350811941015000e08008480301e42000750000c0550b0041400c69076400c00c0c00400320070344400b02d02a001c441c80c0343d0958880042d4203000d120104e85114110341c010000c1000000e010b03614400c09640900b44140c9944443c641030148021070109209080d1004c03543ca0707071030f6500105188807110150241c4588035154403101c0141e034010009001264010004078100840803040c00b4001d9020344140d0703080c240c4541c006400c40d44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 183827949 1250 183826699 183826717
    0x90a0e0c04050a0f03050a03050a090b1b19020f01050912010207050c0312040f090209040e0109030801090e0604080a050715050405060a0f021e16020612010e1e0402060307030e03 78
    0x38080740502007401d082d0000c902801e110004032403000c0c075681e9681d46d14009080004c04112012454400c0d603802555800b01400581d41d42d10340314070840000c0a81d184190034010b00f00c3c40780041e00340c0001c04444090b140650041c0034030304c000c42400e0064a16074002104150009454001204003203000c1c404ac01c1c20314825400f03040402d404804243c50300320485040395040303c04100030090a900c0d01074060484608001c0941c4518901000400510310102d8003101e85d400e00040c807082690103551107058070a509030400070120030501440c1d445074211002003984004004010f8000d00510241c90341c18031850111985030340c0c1082d69000c0d40c00c1520100c649a200c0401c0c040c0002040c060800c108880200850618900030500994a41403e40d9080701d10800035071400030007a603400390f8a4180e0040c00081d5100341510750702e0650300092003103040036440e103004201001c050704038140f050040240307040e44544071034003013044940c8094480d00a0550310340c1440310010301400030388080b030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 183829199 1250 183827949 183827971
    0x20d0503070309061d010810080604050c0a080d080a091103070807031a1e0403020f030a02060a110405180c130803070c08070803040e0c04080f0a140a02060906090a0e 73
    0x401c0c645400b920b95000c0e0340098060080c5411103c2101d0140d80303040d8041c0000340f801c0065900c5260301d5a070002041e0300b0003a00c6010740c10402090041c00a012006280c0c01e5850030f0b0843d503104800303902d0f650603c40c01c100044032080842c880030400d40118000c0c5008407030b03204203c1c2e80800024a092000d901a1342c003a001010208140a10b403842c0c03040d04110000d02c58207a01d004107a41d43d4414640f640d201c0c2948649002c2005c0c03510800442401d440c108085a07500d804c10100039507a80790844000c99114288002c000078000e00006540440380060003400d1011005d1410007004040100500e110007800d11100060110b1103000300d0080081d600030350390311411420003c07030383d0400340c0040080741c1c0000c00410040000000306c1d0102c40d54000d0048150311880051495403040c0e03408240c0e50304c10b014240c2203008020880d10030312071090b110780d24031f4145100040e8458007400c001a600510030b10409245043c20300c0200000c610092503040f41d640c5441080e0032142d01610600315079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 183830449 1250 183829199 183829207
    0x90e0c0402131e120201030e0a05030307030638030c0c01062c0906060d0503040812040503071505091018091b03020309030906130b0d15151713020d0503 67
    0x741d40c800d20400c0c2d489000b1110010004c0c204903451005100d8120003d04050b62244540c0a442c0c040c040281101d81c03150076a81c2d0781c10b14a80c02000340000d405009545118861040d9406c008840c5400340c0d505466802856000700340b03070070761098000409028030b50f1010410032a14441c2031007001c0113040d02c0d81e200750140d05400c0f204c4641c000748055224240076041c0034072102a40008055503c403108451140c0300680134640340e03045000d907503c904460f11543c610f005082a02c0c50190083d14429030881c0e0742203543d40311103815088058149008284200403400090400c0c0000c1055145a81007c000c1181e0180414290b6000340e402640c04641c1c95148410540000700c8084507007080d031274150f0860800c48041c84e101e100b80c02c0c200340714041c00501280e400002c0c0c0e06140003042e0780000e50f0f86903e21000002c014005181014031018070000c004980050030f10014012032181d036490510342c07880d04403030601b00c4d4005400d6054001d0101d05200c0140d03500d04802c0c2c00188982c1c040c50b19 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 183831699 1250 183830449 183830459
    0x30f021e1005060f151b060103061a010f091a0417010c0f0c02011403040215040303050307022802010309030905030a0c0527040f0206070b09061608060a090e0c040213 73
    0x202c580181c00f5a01c691340e5244000a981e561046080307922002c28a055510400c94215a2000110341440341c040c1c041c0600002c107000c21503000504404810f500b82d003c0c510050011101502c00d0500d1201144d40e94806001140c072501034400701c0001d0348040c0780303851f480f040c01d840d6207440ba40c2160000da441c2c0e18039546050744121aa40510000c0c1400200b0306003036800030389000210070744e0345510040400042c0941d65140d20451845e280310541503a41d03501c9050042c0103038030450308403000d88201105186120110f104046070200031030714416052055500460103000b44040940400c10003000126881d90705002d42c12005224001c107507421071070003041c0003a1500082000500044c04e2007030801212180a20580c4290f01851100c0710a08a1000810301e004840000c0c0000c1e25030403c0068a120000707291f0702900c0000d04044002e030f841001203484c00400c55405e0380220031400700700b20241d00368102084070018042500c1106a81c080030034100d810140c0003152440070540c017089 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 183832949 1250 183831699 183831701
    0x3090a050c060f1204050709052e050f040b012a020108090318010c1407060305010806090604021e04090506070f0908071a0a230910021603030f021e10 66
    0x41d095040c1c03102c904115034603091150718015403460a0a040b41680090b00b045010700c1080701400342c141d801c00c158100b06118000c051141c0c2000388900d11a00d00851690340d5410404003180c00040813500544600b00922001d01503450026040c00010840c0b00a101c22081254640210108134100c082d44540001480c00e00090181000f5400400c019504411510200701c0070b080d080c240419200103900c0d0043c1981150700302e100700b0f40142480481d00310b41c50b801050490741e02e02d0803a03003035459041e03145843d103e090f80d0080d846281d071030103515800e001001185907043e0041c4001804001d07a15620705005040f50018005500c05070b1100030181c00c080c400024005e4072006121060074401300a880d128540c58180030400c0101f02e400300a8480c981d181c9910040c080c016400c08550f56400c00c5036000044c00e1481100c101692500342031001a42240b0b030408140001d0003142b550310180ea00e044141c03000030441c001c8617528421012654402880c0604460050580700007040006e8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 183834199 1250 183832949 183832963
    0x1060e030d05031003030819021204030e0f0102070303030f02040b0c0303070f02060403020c0d0602040801090c0f061b020d1106130e1008060f090106050a0605030f070309150906020d0203090a05 85
    0x5050000c00d00500c1030b1391000d5980401034030340c14100320146448510494a000022804500e601c500019084c0003c0425200c018021440b0361665510901c204c010042124481040d42d40142d02c03400007003001c28443c0e0814540c0e4603561400603c0d064481a904205500c0765103417154030341c40002403068080d030100c810080c070740d0584080e0010341410760f4029110003e200d400c0d031045000c0c8480c0804c2c41003586c1103800a004d40b8008015194841c45c2040c1440c0710340c4180d1214048007000021418056090640750031001d608107500005640c1c20000a040442029150544003511580700da0f140c81004080c2c2d5400d00b92050942c5161258540d11108018031007903c1d8592421b0810081c140090242e411885060a006941d0341e841035082c014030b50f503882070741d10001080b000105140c1043c01540030b6482d09000000580c1c40e48019010b03102c1000004106c1d00c0c55018007000450340c0c3e400030414078441d0101600c1d01d400c0f44100001e2360015140c81485408c0040d100003000004c00ca10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 183835449 1250 183834199 183834223
    0x9020d091b06090902030a0b0a06170c090a03060e070f12060e030a05070204050702010b1005070c050a0f0303050d020f0415080f070801170f0106030303061a130501030c051201060e03 80
    0x20607081800c20400800e1844039105140303c158011000c180300c1c00310754101140001002e00341124180e943e900042c504405240d0611521042d42d01284d003500c58041250b1304444060042c01802d0b00d10360300c410040419803400c10181c000c12101040c44442d40300342071300425810361242c00010003401c08104507050f40040c40b2140d441008200c41641d002410340d110f45030119000111591520010790160118902040e4065088120024442d42040c0a46469805444400c40c84d40d02c4a003402002c0000380140c0d6800100b42204000107886880108800c01c1c0445001d0300f0103035940100846500180c11000d10610303400c0c90381741e0007a8840c45107070788480c0d020010907190900b07600140646c00180101d101c270240710044c1e07424904040214980c0c44220000030409103a50382801030092415028020480c44100b1907501c401c660b4074182e407044480411a21405454003005500410703205285400b404000c0c00089004036164540d03e0003002d07207450741c40310007044808260400c80080d0360 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 183836699 1250 183835449 183835493
    0x51302130606080a050a0f051f0e0c090420070809040c0305061503060a0806270a03050315150d061503021303110612041b0e15040b010909020d09 64
    0x70044107620a014541003444c040d000a10342d110080e105000c0c05000c1c80d02010a4105014030100a88403000c00426400741100700c00c8140d1541010b50030510250351044000c00d040c44200c195140c150710139213201c0c1c12104003040518600d00d115020341c00580040d15180b1700441e403015070f030071300d40500c100c001e1091034100030610300f0000207188241801650510148048000b41407030721000700c0b00300070b40840c80c121100741ca4a52000200d035070b91302807540f00040160300e20305401440042d10401c1d9543c1a140c090450b52440801540c41c40400c03041c5500c440412203c0382142c1020000b80300f845200140800c41d1410107443c6000100749040780020544100804030102100804e80010b880d0301c9030820b805a901300d4001000c038082c5100c00c070850307824041030004006860692003083c011126400084590300c1c0c1c040d05401e5001c031405880034000388601002890640c0c403048816005040c4038000e941c981044900307c0c0c10051007488013641d03407907510041c0a6010040c401d00d4142c0c00c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 183837949 1250 183836699 183836711
    0x9030615060f031a041107140a2a0f03080a030c0e010909020d1508030a091d060f03150106020114060d120f030f02120f090109020a1202030f0105130213 67
    0x3402c0500c80c40390481050740c4d8403401003242c1411580b002440c58018030502130300184040a103055400301d071040f0b6035016581c0310320f4154900032481c00881c54000d64241881c64885140034075440f40c0c3d8101c1d04402082c04404280454008d4410000e1801b0b0008070f922140e519502034202c81224100030b05005e800764059030700fa80e11000240c2034a0f40c0d0b03072016884101f2460018060001c102c2e545882041c6407402180c0448000013902c032806450391510509a6a50524034100017401c84280c031340b404500c002282403c210040440350070001d41224103070505140b1512800800380c1050b00141d464040c00d181268030f5281c1070360811811141c008844025075100b4001080300410b0344140808202c8245103a80280d201007101c80d0000002c0d0b503610b5007000d441492a40444a02040302c1082011a0030450305100e071a0f80581e006e081c0d040094100802030246c00c0c02078900326071501c203090341c42c54000420301545019450450702c51040c1d020500c101300d001c5099240700150300f40b07042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 183839199 1250 183837949 183837959
    0x30906070c080301170c0307060309020102120a09030609020126090c0609030706030b010909110702090f040215032d01050f060c1203070507050a030f090b040e01230d0309030615 78
    0x10084a0450b00c812041d1a17043c0d0808040500700440d0701c08680c0e060081d503000160310354050304040e032468803d80c282c4142c0300900c807036898039009141d034040000c0c00031941400003c07500c0d80710702d05003401414410007400c6d141c01c400380800c1c0301c62480a42d60034454244105020208031500f400e4004858107418880a000440d44d60320940c0b24000415445142071031140c0d008800e42409005030440501801300c8091252005600c103c0301240100c00c40b000003018554072141c2e00b0b0296070f0050140d0009040603040302c000e0381000d40340c2000c081000c160b52500ca10004007001c00c1e9084801490700c0366150404100c11941040406800b928007000b801c200d00c080030516440035810a113500751641c5502c1c00485140c0190038005019200741c20345c0c0020315810042040c4000410f40d22010120f440e1140d000803030080c1c1c81071500c401a42001406460200c1d80240c41020306070481140141440c8000703800c1c00300b0800c01750041040d00c0740a0050112902505039a6070040c88445c041c9440c00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 183840449 1250 183839199 183839213
    0x20712032a0c0b18100e0c2707140c010510050d02061e0702060a020c04060605040602280609080d0b010c020a0312090b0c01061d0403081317030c030906070c 69
    0x503030b10007480c0460403000600c15807400300c04e10514200340360898214003401040b400003000d80b03400d800c03114403517a401002e40f854041081a0210b000e00d005000c0701d030543d03498403a402d602034050410f000140c441240c011134807001a0910118050012965080008440d810599541c000c24007a40d12090b0100141e140d440c100d4004801030f250b101480d0700c243e01c40071214000c04c030000350302c1b4100003003254002d50700046668210800711400c120360f1307075614026a00c91040f485154090b070844150000b000d04003261401002c00240134031031042e541c580d00c941c2120712040c03007210502008034942210035207501c2f604801030000e00744000701c81c95540002e40d6107041840000d185507038104403076a107648141074007030092850409954450040700c900c43e010340b42600800e500721100d50b0584100b04024401c007400703550180c427404819217510603400c2d2544101030090301c40e204807814441204009070002c5106c0d8510b141c3c40b5032a8100b03a503ca41c00c0c2480074041c60b01304100c445024000c1501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 183841699 1250 183840449 183840467
    0x110102070803010e0406020d02070308010312020703170906130f08060a060509011715042d0c0e0705300105180106201603050105100e0402010e0103020712032a 70
    0x4c95820070300b6540710b203403480c042d1080b1603103980380c540086815020581c00082990580748030301262003030807150701030403030755002a03100150451140810203c08000018003c010070500541503600e061110702e100348020f8115800a4410b03200c0043c00c04c00701d0801d12015801030314054081c80044c2c81c104c0010f10301a018002c10a100382c2601ca900c8490404002218003082100c4e140c40e428070b410b0401000800030b24800c1c4100d0070b046002e108203012040c40d40405268000b04030300b44542440d120035100c41c00285014280003080000d91540e80d0b009586035034640c1c0c024032283e044c3d01180440c510702c110607402180070785c50384284103000300048074a05054585915000d100844c001030520104034982c0030b405c0c1140070f4030101007281007500c84502d0070b40380140002c0c07000d92100c3e6070420b00301c207180c8900818480c030b400200c1c0040d845061350240b40d4074140b40160070b0060b0380d10b4640d20998006c0c1908082a600d000c13103d042540346118911216902842d0307000c03078950070005018500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 183842949 1250 183841699 183841709
    0x80709050a06120b040501050711190507080601030c0f0f051f0509060408010b0f180c0304050102210702011d030d050606040e0702030705060609060d0602310611010207080301 77
    0xd00c80e0300092004201d9032002d402807000d0140d81184000741d0030405104c107410355090707071035500300000540d209014811018240c40c849004140408104035483c41c0d014000c58100e0740d501038610300081c0c400081100354082d40c0220000079038140b402c100c2d41c9900320651b106080401c0148000c000d2580d518101031043c20f503102c421502d007800c00400315814404c3c22080369000b20081004106010305501030010070106840200d881940001040011604036070600324062200b4005038500005402442d0002d2007030b400582000300000d1030b40054203001c0c599100e840b00c0e000820984603824040c802c50541e40070a1201c3c2c00008200c5d090312440799240440c00c0c40d4650703004c01c0a5443d200304031001829079a20000303041c100380344000d40305e13480103000b03075410300c6400c010880911380103080c14001d642c02815850000303803607900c19010f900b0440c890300b5036409104411140c402170741141401d01a24030507c180060a00308081c02c003c00c90f10b16060142e10500c01ca000242e610402c80c1e040d16 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 183844199 1250 183842949 183842951
    0x5032a12060a03060c050c011431020a0608040203060a05010605180f060d090c090c0207230301090c1503111e0c01090605040605061e1003110c07030516080709 70
    0x540c454000c0340b41c2d5180c0b948000d1a403841e000003180c0259002c4091320384101040000d0104038000d02c99000d0440045c1c401c0340c01c8400c025200d03d10808202d542c0ca0140c07814006000c03619006800040300461164441c101082d00e0404200440c90b060185e558010100842007000e5414100024034901038481c0c01c4510040001a0803100e41d2003215298512500815055841301c500c0304090160940481c201c0d0002c1050304041941030160150a0103d503d590003410355034500f045400010112130200c2c2c44e1100b03180d4510007561028000d405103507025100c2c101155250112115260291410324420503280c131040c004022040707c1112400078260654140841141d0f038400002d10511030030148540c079250081d010080f560708010300c00c9004000c1049035545040500c000d515507082c590308140001d03403001940385000c00181581180920f03000a00c00080d100ca010540e001812103045540107401c03c10410100700a0308080c1d940300b58030112540c2c60203181030759074041402610001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 183845449 1250 183844199 183844201
    0x2060609070e040509031803071d040c03051e0607090e04080307021e06070f0c03050703030509010216050309030105010f03080a0f171509010e0601050702090c071205032a12 76
    0x39807054484907507442c80240200b21505007144000d50703036402000404000e8040c3c00c02c0200ba0300e03012071f181040740c44034091240e00380c1040a00001c1494010412181081d03100c1000c00480d2082102119039a0720142c0304200300b401d984c60071300d0540c000346401e0030065011414894030400c01a1243c0290b4042586a2240c90346039059003000c1002d00000c0d404801ca0354001100d07a40002e2003409040151140300c1c41054056088413840070b0b02a010300490410803030031000034820390100c0c0d40540014001800c1180006200d25004c05000055071175500210720b0455a250a224803401803c01188041e41d00d4036580d074400d028056400c2c07001c14000b4032088440c105004512181d044224100c0c580304505c0c006520070300004001c1c04160244102c00000b2408918445286000d000141c40d400c0c1803106035802c1007483d8070014004031400c102842804001740642034400064082030304ca854803403401002c0c4000f03050341c1000c0c07031aa1401c050611804071125000f160107881181c0241455 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 183846699 1250 183845449 183845461
    0x110a1202070b16080f0705041206060314010b0901050307032105040302040615080a06081207031103070b06090915070c02010e0904080c01061212050702150706060501090803070302060609 82
    0x81c0102800540091448403c00c0050290303c02084032450003030719041c00544468151845800044a00e18040340c0100402e10481c0d00c1e1030040303420345110310800308050b40c07282e0b9201d0059454400300d810a80d1288124089842c1040856014100c00e0700188003041c034548a1845005580404078007900858440490381841384c41142c1c06960050030900030b003540c40d090034282c03030186101c44000640c0003001c1420000140901c07002c50b441305005021078580003841318070350b5001d1003084013800b4031599080401001800074001c12401909038001e40e107466810302c200c08100030140451394002a401078403101202014641000703541c50a02c02408882c80140c1d64180c074104802d0740405084108401c0114480080002e035140800a03c50305030b40c2c3e102a40c1040381d6480042610400c000e100c3c84040c455006001e03860f00050101d00c07520950814480b095110300d03c01e458258440406000d5960014440401860f11800a6181c8095a20300030344424000d07198512400e002400303d20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 183847949 1250 183846699 183846701
    0x607030509011b1a070f080601080601200c28031e021c020f010311030103020d110a0320010806090a15150203091f0c0b060120030a08010504110a12 65
    0x200000f580c3d1842c08610709036041007007484054001c0540c3c1c1d11a050006a181c9105009841c1d440e900c684030851540c03100001907601180003486641080f21784000680c0741610907905488098440014000b925076440c04d00101d180d0711418134881c0140924203525500c0032081a20440e504000c42200700074906a54090f0300104020195214400d030014a45481400e1120b600a6108580d940901e1320f944006509840c900701d1065298601440100050700307102e107800c00f8481c0300d140701d41e4000103894009061403109800c01d80342200307009240210b8550080c82c17003080300d90900f400c002501e48180001c1006100405542c00c89448090310100c1042e00840c40c00a041c1003602c01480c078161031002581c9800a05030340d84184c02e801e00f00d554040810240d5030322003096983c0c8412000d690f4441c04080c1a000d0b2100c2d04128560030810001c2d211203511482c03468402d8040d6948803c02c0000030007544042e0401e903c6949060201d0003d020001c045170482ca07150b00b80001500c3c421311000b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 183849199 1250 183847949 183847967
    0x70302120a02010f06091a1e090405010b03010509030a09140d03050c010e1009050105010506040b030f09280b0901060b090411091c050d030905060708090319031506020a02060703050901 81
    0x104c80d03814003a010900c03001075004001d03020010305246015418075000c02c0b1880100c0381b6603480030440b02c20140d0321401e1007408680d009001c1c1002244e0300c1152000f003030860b40100c2d0000c3c483c2e000420800c40080d44032140e0f20042c41d401c100760000e9655200000c406c44003030640181171110000b0f4594103070900b03400c4030511003c024180c0740103c168180070030190081c00d00413142d40d441c0400200c2c051605105071810f40746406011030031a03490a00f140302e900c001422030282d07481010010b16208210b142c1000100b4400e20303035041d07002c509203403040a0701c030041c1050f003480c5d050020501c0a800c109040d200d18200072940824a00001c901485892149040c003a40101d11007000140c0c3c00c8150004d0b8441034031900c00c54504180303000d0100d044502c90b1000a0464000f9008030304018403d09a65400442c8003003524648080d40703091105c0e1501c020207420102e034039220000c4403005155000740090529002400781c014165002403604e101d1a0401401e013d40461030750702d140d10800d901d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 183850449 1250 183849199 183849221
    0x8120c0a14010c030f020301080607261303080f06030a030f0e041b0e1509060a0e0d050703020406080c09010306050a02130920070b060d080903070f0e0c070302120a0201 74
    0x1441c6406011610340e40038220085110011030704000d401340301580d191080364122440600603100f81c1e168404103c814600650140c2d001c00380c801544954964000491400307072800b081c112002401c5441c01804400000b01961a40c1010314104242c1e624081401103500b6414a45405281807a07442511510342d00750a482c1c1180c508000c2ea200031460001c80c2c52590050f45a0408480d401001c211000c042d0580715003005909200b00c0403682400d101900c52020719042c0780c007031048240c0100e082020b080d8001daa0682c400d1070100b05505052082e40040c00000c000f41c054030054030b000c1841a68184002401190740720300141103001c0c0b40c0d040d2820000f010300d01f40781059455004e49c01501c040c0c07800d045001c59001c0150002e006c40b0088031003e0707520401000c4a41d895008101c200c41c0e00d000305031010401000304080e17030f960a00c440c401902c5400c1c88408094246001c006110a004011102a0308100324a002007500016030b102082c01c00c6000c0e0b50b0700d0089140880c05000642c4c18 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 183851699 1250 183850449 183850463
    0x21030f050c0d0c02190602071707050405070305150906031905010b06040e0a0c0c02010c081305060c010e0c03191212020f040510030911100c08040e0105010f050408120c0a 75
    0xc000165009101107410380c005c40e2181c06542950140c42000d4445101c1c1b44050b03407000c00100540c5400039038031001c1e480704a055800e100e5840e8085015988102c0714000003903620030170040a4041b66640400118003620b035000b1515114000c25070f2002c2c0d0b540310109954804180780c003041030075003000c410300b0405070500e41c9580d41c0b0290188080c3c4140c0b0703031251450038140c1c401c03542c1c0d2243e040320f444c1d070b90142d49010a00c5115202e20015034400f41c00240c024002100105494480e00020a83c14843c0000082c1910540700b42ea410b1502c1114500c4c0300e9044003c0008103800c82e00c4500c4d5a2503003180e00700f00a00b15110080c0c1d00c0a0201030030f28141c90010038010a11028580940210307041621210b50811054504404949102e42c00030101c29040207040c0c0207040008003128800310070704281603611016201c1c04c03070980155112a17400038000b0014080d6591103100082c0c0b1520784d0400303d00b080c0c14011481e4403046c6a0000f040d002d90080b4010302c40950400c0584506a08030135 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 183852949 1250 183851699 183851713
    0x4150f020c100e0f01050907061d090106110106060c3f0c1a040c061d06120703060506040b03010902071127100b1c061509090621030f050c 61
    0x40002419450b1034450003406a14130f000800394040c0207992040f02d000015040d100c1c10031005840b45800103584081441c140d01103820710ba10303404146030103030a180d01e80c0031f910502d040c2142d095500720b410072030800554040c000c0008006071401c143e40d0800103608180b500e04803821080824024890b5060312031301e2252548850703002602c00c401d40d07000f200d41d0f21184108840c41c02406c40240e400504080c070102d070800c004c1d849100240c41841c64001a041ea024003600069069084490009004c0c4440700070700c82c01d83e4145c130421000341800d0b00e403c0c2c1080e242c045c101d406404148140e038012900012550100b2401d490f140b404008000c0000d416a002540b4030001d141b400000b80a8201110011941c2e860030450300504032100d440a451500014150910a4480100700000c40a40300d480100e00300c1d100d0742505488800558510b48403526120070142686c0255100c2d0080701051514944003420008260401a4050500200031901100111030501c120815054a805107003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 183854199 1250 183852949 183852973
    0x70522020c03041706010e01030206030f1b0d0f0501080a03090612021c0903020706030e0307030c0809030319030c0302090a030818030f010b09060621090708070e18010504150f020c 79
    0x18440680c40b14000844001d1ba888900c44a175080003800080d5200208ac000034400000c0101c405510420b0010040c000d40352045039860541c114900424802d920f6003800b0f4008419441050300400c03801004041814058030090500c0c403a0380104410841094540a0f90400603011101b4803100345034107a0040490b006624010b0100390300480041c01450000100c241c030a00403036400d0040040a14548a8142d81c01d951031144070f1000c50b4152024803442d245640c080c070143c0380c4038841c001c0812002071603110050441d58944030301824903106111035640340e1034614102c0140ca51000780c60366101200d00b041101c0c1c1581108103940342c030499032015500729064210b18a85501034076140001c1d101c44d0100843d50168581450175040b440900c62041c15655061603004482c580913034404a07128010603007007418503041400130f03100038428080d5180000fa4482100c298a500812050400391340d40c00c19020069981d41190717445d01c981429114055040342c1c00301c680b0000703e683d80c00c165 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 183855449 1250 183854199 183854219
    0x512251103040e04140c0d02010518040608030316021608100203180717070b1e03040f14070f060c030e010e030708010515092802070305091002060612070522020c0304 73
    0x101000d8074940141b0000700c050741040116008006d60585805040c04940311041d01c0d038141c8000c1c1e06a020340c803003100141d290428401140103410114000c1c82c0c4e02d00c0b014020746031900041c03102c00851110342c820480b0220101e80c2205250740408003503a00d40380c800c1c01040d80900f90b01c2080040c026550001030021a2201e01e0312410a0441030728803a55a40e1b001d10206e00680c40b807a91500368035900309180d020032100543d8000e20400905402000741e45801c5030090806da589801940104403d004440120f082072006050b286040d15a1002d903503070007088030b1544081c0c81c0c1071050408800717505507802d200034030283c641200200310624025200d40050a89041143c0c0144960300124607000d140c1d020040b00b64103260b00018240c3c1c00b20b601c82c0000d41c89a80107400708a01880b081c18665540101a96417041580c010040c034109401001104081e10802168903484203204100c0354550388203242c44007680700031480040c20080200340103131142030000400b038000082d01003140586 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 183856699 1250 183855449 183855473
    0xa05101106010603020c070509090a0c090207030e0418031812060b0411070f0f03260402030f190b040611040806041203020f040b03150a060512251103040e04 69
    0x8100c04881242e6030b6104182c00f20b100340000d14629420000080c0318605240c282c040e00212100c0c100ca0383c500d03081d2078030260384a05e41c2003088284cbd00040d0203001d140c1d00008100c0010313421241004090418985000b00448042c2c1c01018803508004c24150b0b110705800400081c208a81d00c2c151224991030124020840c0405461045180542d080c132210704641c1074131050742d40700ca801d92800794640c540c549040c00c0000c0850030440c03150304080307602c0b8012194185e00301e10740000403a14102031040600f4861a0803032034031198040d8005840c0b089240c0648007a131500202042c101b5100c506181e4043e0825001150006000050010340d103103000489038440c80c042e03240c51100300090f00c01101030b88641d0f22006000c0c00e00380424040e40381a81c0042d83c008142c4844000120319a2010601002081d404500400c0001c5014000d9034800394040e40e00c000001c060b140d02c2c125002041801c80c1c110440401003001000e9004544601001200c010b000071620040f181d1400385064a11400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 183857949 1250 183856699 183856727
    0x111070201090e010b1c0e0102040e0103050105060108040b1303140c070611010e121b010e0304060e121011160b040201141903020c070e0a06330e0a0510 67
    0x4919000152483d0580a194103031500780800ca860b160703a22450560341184003194541c181d6655682d01c809210920040008194410340b0714031542c5103042c51421100020a03541c14000060104070020f02000410395000e0402c0300c01d90380340810342c181101c6a41d4150703883c030b802e441d00061b01020540002643e800b214910f940365241509420300c00d82c04d0382c0008a44a55a5101c0e0007090007150b9801c01a08882d91400303410b084482403025022b086d658841c0c04200c198200041c1404881d03030061081c21805010b03580d030001040c002c0051a61440c500d000d08401941e034812040c101c244034000c80c0c1d200c001058114020b280c60b410036800648003900c0883c0420f846441c41e180d48601201501d4400740d003105c042010b03000c0300900390040c4d48441a0085e0b5401241c00110b04840e0181e0201c0c0074201003035000036040d0a00008144600e10104092001400b400d4001c0c440765412002c20305085030362070300d05504540d0360049400202d150304060b51200d0800c605400060344440009c400d01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 183859199 1250 183857949 183857957
    0x17160806010e180304060305130615060906050c032505030a26060d030f02030d151e080601031b030c03050d0216060906051809190507020111030f180111070201 70
    0x2c2c5a00f0469244801c00050071000d079041484100241c070301036442580d0008041e1003a2407850041d5544600311150340c0c4000044245958041c007843c0c0c3d0204403a00500900e043c00c1e03240440c4119126582d002c0c0300d60300ca40810158450382109204441c05149540d800822030303441e003041c5031019158840c45004400321442c0000000d500c8111041d90501881018040c040c0d20f00503500d00722010754050303003080154403080121400709580743c814400910f0041001000703240c142800050703a034044005805040c4c110362401c0c4903501c1e02040c80c85c11282d00c400c0c800001c296400d44a08410f145520103014810810000814400089269803104a00ba429101000c220310b240c60059043c5009a5002a804403401d0008902841c001c054001c0381810b0310b9115a4068002006c154007242d40c000103440c7ca4030b83d900e40c0d140b0340c042c0a80281c280d0000340503801e1000c0040c8010700004101500c810b02c0400800c800f40004000c40840039024002405240c21180c0050300c140d100f01c2c0224002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 183860449 1250 183859199 183859201
    0xc0207030317010f0e07020a0203060a0e12070803061002070915060314010303050d020703020c040c110f03160807060b130501080f0a02060a0806150403060f0507020307050717160806010e 82
    0x1201c2c581c00300b00c1c142c0c0c1c1d041400380084c90504806600803403004100f1010340c420060a03002590303040048500c1041410404079501d21480501420014030054030401e40070203000d080700148500069a41c80710044c0c803c01581e50308038504a00c6e04d0312070382c440c02d580d9260610304102d480091940105031a01078400780b02201c16008041d04540c824800071b00064420b125080190020350010b00d110b50007403045800b002c104000260031181d40c58032440c08a01a140700d031720070900074402e070200141407801071818420101d00c260612015032900514444001070320000b00040d41c3e0001460400251000c0e004059454070a40145020b0045010a00c112070340c402e14044000788900404d41e02501050900490680645201d1000350086078000040058070030340c045010050002540038903804121601080c0d440000c03a40090998001c54104105101c08140c000030948100c030340080301110183c0006902d1410001c0400800c084001290030005460400041c407a0613511421214903903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 183861699 1250 183860449 183860477
    0x11401030b030f061506040e01080a120503160f030603050114060102010b0423091504080d0b090412120b060a0201150603090f06051b0307050d050f060607061109040c02070303 77
    0x550003645652640c0343e03102e5000100e01e00c5c070038150fa140c03001c405094541060b4a070007950450b80310903000525554000000401403007208d40c900c0186030380c24180680342d4104061313851032801000c404034040c0541c928601d24079600c250b00130303002590014002c108903030300341f040c4d02140300c030075070b10f5900540c02d02541c4800c03440c042c85a0b5a000e0900c010158549513560a1042190030007401d0b0742c0316014422040c0014115405400e2295124001895990f140d04182c8011941020342040c00b0b40b142c4c0c0200000540c0350855070350901450306000402d020b0305400c4e0000b81031540e02060704030402041c01501d00b83c0540141d5071002940d4121881b60762503100440440c0d0b50f06101602e2500740311040004200d2503404650845261424440c0c0b03840380c0000f0254642c01038908200203000014070400c2c103905441a82e80044486600701a64242200000e03000d01440c08098101641c3e528044940e40041e01254819003014005020f141d4500a003e500c400c5244420380108603504a2040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 183862949 1250 183861699 183861703
    0x20d05010b212a040c0903031209020105040b030603070f080c01141204080f0c03070809030c042903011401030b2e0905042303040501030e0118020f18011401030b03 72
    0x2d20340b6040080618050705100002d500c0000e9001e183e4001c2c0d480705650241c1c50354000d490b2120103a8480c02078161a51400a14039804034451036141440e080d507680040c0e0b800300032241140c4c05528802d890f07481e81e00000e81450059400407010b610f1b07000c000980c13400007240428030034409882d00f200300c1040c0d2010518074030500d0020703030718510302c0c50010340050720711009800e46000e9070f40c2c010f0a100c070340640c442c910ba1252070140c45440c40420341904501d0100031400f40c3c44002e49050050031202100244a42240600c5101d40e03110800381c80860b0304e00754800f202a08a2030300400342d6581d07034100440400010b48228041da00e403c20381c1304541103840c02450455100410a0714030902d040400801071002070001c482c03000d4204115100d040310f421822011030f04013000345650301c0c0337440005000c892103001880e40726418903000300900000c0100f01001e44c0e4040d1034030030308040d0701000960300d07040c03a2016060b000000b100100c0c001d5501c0300c00c4180d50f4020f817410002e00b0301c4101019 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 183864199 1250 183862949 183862999
    0x403091403030403170f0d020d020403150c020d030203060d0818040b010f020604030f0e040207060b030c0307241e08010302091005091504020d0c0c1e0209070309050a020d05010b 78
    0x30304026402ea00780346005c50384000406c9890340306100141404044100e001c181e904c1509070540b401c1d000325040c4184030421090303070011074000c03108100d042014800070b0348600380c40d00c0c03c1060541c0840002d15684a112410203034aa1050010340d591900070140c14000986012040c0076a00c1c000c050110303540240764084281802d41c004000a96403503030110f0b0030031000c4c41220104844424240b005881d240040e015092003207401040c0c10325503c05041c07528140b40c0003180302703900c203202c200407000340700c0e0000820786007011105415698042c400d503510b00c0785486500d4410444040f0420310fa070305c0346009050364402c48401d075498941076000a81080e0500540d83c0c4201080c000c00d10010302c070a031005044402a20140c1094032550b00f03034080307690f40c044550201c1d800103104e0702040601440400400e003c814800340541c5035030042612480010010018195588810414001c0820035114103d0f0b004040300d00c030348070700c0c54000c0c0a0810382a08602400c0900420070b280d40f5441010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 183865449 1250 183864199 183864203
    0x20040e100b12190603141e070f091a220b01050702011b060b03060106110609240408040e04060c080a0b0108070c020f031002040608150307090c03020c060403091403030403 75
    0x2061500d5808440f4150075a0b54140015655105400400030f41d4801341c1c80140c940724406080c20402041c2c00224102d03031070030440001e4110b01002e000861102880c2c405170b810145d4001100c0039074036415002d41c4034400d400b6a1101c2441d00019400351400041861055005002e01c41480c1c1c010045d00c2c41d002d007020081c0130440c4044d0020070b401008030752280c551300520001c40d440010030023280c2000707003e0300500001104841c0860064200b000a103400c8010752008020754120000d1005030300c0c5c43d4103003644640c10f1141c00304040c0f00d01c69081da4084e05a00041030709504044c80d10100600b514043c0c18080b03008800095110005c6100300040e0010684500d01d190b074990004031070945e0350031012640401810043d92690718208000c030f8041220b001d00581d100d042440203045098002c140a40341c02503040654540d48010071010200c0741d0f000ea0100340010005400c0d0040d010354102002e69104810400c003e0542c03040d2050119070409004074200300050b03041c561079101d00d001c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 183866699 1250 183865449 183865477
    0x60509041d0d17070f03020306041503140d02060405070e0c190504180213030b090109060f0204030512070305040618080a050c09060f0307140103110d0b0f121020040e100b 75
    0x468080c0c00e006c0c0c1c0003035610400c010800500403050b4007407210310701c405400c00e4031003070714000c840d46070140300f041000c2c10049140010708503031070107680c0c03140d8030901e0b40542404201d4150201d441c019154058032040000696400e071030b03c002c024002d0480e003041c414409140c0319a0300c440d9003686903100701c440c4483c0c8440118a5541140c5501c24000f07c068240b04541d0360720000c08021540603c10b1900500c07105c2409030380c81d0f00d5401d1982ca4800b01d260f00d0100c0032410050303100080d0300315048504441450400c1c0f084001160801c292950301030380314052a0040342ca0010820001041c4400010380c00c80c3d064034503849401c140840c820380c81889075010342c00030b03a092204409030380d008900308005140100c2e58034100001d10b0390302c0c2c105210700e00d50561241d0444801d8505091406c0070319400380c0e103064121406485407035550303001c002da101c2083e6403013182e80d80304503402c802026030400d1f01c00e05640e1566103100c03500071008100d0340d089408030700c1e07680410a0403140301210208800151 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 183867949 1250 183866699 183866717
    0x20a020106030c0b120721091e030c020f0105340b09010212010603020c0a081e130e06030606010c030f0e0a060f08010b0c030909100e10060e010206060109060509041d0d1707 76
    0x4440802023a25003c2a504580450b8a80d0441c00d030000009400701e02c6552171000c4003da0b4410710612031070f03508096044c040b0500c030910f00700010300340049118080c0205907421240d800c0c14001c0b00f81c080343c805010f242c203000400a0400054008204a2500360302c1c02003140e98846048040313000b610880c0d18203802c8420720307201103854240540005c111009072111802c1d03120215222a17440901101804404600108058504040080d40c000b00941c050a0185400d0300020895103900c1c0c001001e0001c80a0380f0902c1c107215071020850404040c0c54003020b5522140007424103170440c144100010403070000801c00ea41e415041d14400040b10005500f001d5148040241d0a00700074035448070490508400141c011030344446900862004040740e112500f00b110081481403a0340da4503043d03502500c144446a41d109440c80200d6131603140064881c3d14690000740640f428080d1101d4030420000385035a01d140c0070400d0300030340d8160b803518140c0719600303c3c0760408894200d403d500407520045c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 183869199 1250 183867949 183868007
    0x2031c020601150207090507020c011403010608040f050a060f0b0a06091a091519090504151701020702040e0c120a170d1404050d18030209040204020a020106030c0b1207 74
    0x90f0b01c0d00b0411080d401650149174407074041e01e044070340882e990801640a94030762074255030086403a104580b03814220301d14542c103002c0b000d003d0100107070008051910507200e180c00d0110500c40380b080c5030b07405002405821650382401000e00840103406100f2000000c0c002121800b0700606011926034107022840ca640d4184542090f4100006640c0c2201d84c1500f0f120a40c080c0c90010703e105035003901c0c03000004800307a400400d00340789a04540d010764942071681d403800108142100449030b169040c860038810362040107000e401032400c000e4015003498415030f450980801da504c0f80c0d95003610b0b022109400c654400341e8500d8500c0780070f0040500d11000305080c0c080c541c028103805500030300204a58400f403a01105c0741c841124191050b40060344503480d200d80c05440c0100b01d030050100d60040794210b8000460300d07240a03200070b110350b60000c0e200075010b00039004074004542101e20b4081e125524288140a40e00c11480402c541e140e2100007140b65014950104805023070b01000d0341c00300110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 183870449 1250 183869199 183869219
    0x40612020102120a02120409060812071a0903210612010c08011502031207030506030c04020901052b02040803070b0603011a10090305060705040519030201050327030d0902031c020601 80
    0x3d09050b03c05c5010701c4a00b42290207041c002400100f0b0848030000340e140c40c000c4018184640039104401c6a030301080350078085651580070020380607406030301840e2501c40400041c914450740c80ca6486410084840680b1a400c070b280062007403000f543c0c140368138106118007a0880700d1900780700307003c98610001030002070a044440900e1445900450340f5002c00b142c1c0c0c1c0c02c92040c08503203800c0000e846504000780360a0034004e01d00c1103202900c06508100300140060064061136a030702c40c0020001e0402490101100c415140c04020f541e000c542d140d403a98032241d10790f80a00c1041d1110645d1102052139400c0510542603446a401c1a80c0c10310707410314040002c904003807034810701048200480800811010f00c007440c000c00140e00e0b00d0350388074a842c0034040344018407002c406003010b82000030400b50743c1103021aa8040114242c2d003c252421918000e8420b80d44044448580710100c0e031030b00000750940c084910301d0300031002c40d40d80f44c0c801400f4501c00d108c0c01c0104001a04181e004201d43c00007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 183871699 1250 183870449 183870457
    0x15030b09030f2a15010311030606012118030c050d090e06040203040201020a050601092c0303011203052503030605120703030f020c03060f010603060f0f0501050f0408010212010504061202010212 85
    0x1400604118074840ea80c0c00c0e41c0b801c4e000d0100381c0e000c1c0050f4030040040004060100c001444c0607030160200340352240002e020701e0344520f000e0070301d40c510001021501e4010790081e2540e807241e1032180c8055015040040942c0100141100c640c1716000925114a0141170040c2c1112540118010710780d503041c05210207500040c00407419807203581040d200007801408018068111010002904003840c420809070200030400301c80e4401c02c6000c90bc0002101008603815618034001551825210f1720702201d15104000303080d40803054420728454400b00000d40f80e10458029542401125110781c2003046103101b01c1c081003a03a602030340d401c00019025a094245d0510240103a40e003500404011a091036800c880700301c504100c080040c8032458052007a107002c0d10150100750340060800380682c0c5942032034060300c0d05201c008a076214861054008460241c40c2c201c1c001d41d01d44803010030f42c90542e24280203a5114500300074000c07500640184040c2b41c6250140c0c010303c0192041800f124650340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 183872949 1250 183871699 183871747
    0x60d0f060c050417010519090f060509070503030304050f0d090e07080403110706031e05010614070f0c1203200d0507080c011103040c1a0307031a0415030b09030f 71
    0x150502002421014908074401c4084c00440042080d10348100700381141613000c0c1c82070519502d421680c1001c50035052020002c198492000100ca031968031a251822152360300c4298907100000400017005800f0406444400d0a5411502e80108241099555264600510b030104c03d00c180040c60349845164055046402418850000c134000403801e0300b0812250000d9000c2034803100b0041e01c01c1a00d081c400c000c1d95500070100115410100000d00c03508050000000c042804a4000c06104080c0e0340215240c0d030200400341040e540b0300c0c10b556404540e800030f60105450315400c6038070801403041c125081c01e80340003034101342e405a141992550481c000c140e0b480003052050030652442403140c0400001101c9000d178503803900c0e02d0541c5600380c09800200c00500c41d201e89425000e1200f003960f40040c124280807503089407075070020705222203110b0390702c0c0d02c1800e00e040c034200a4180c0700c0361000d5a001d41c112040ca0760725507105036a00c1c8a011030362168000d003000528512819809244600c41d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 183874199 1250 183872949 183872957
    0x50d030305060f100e181006050c150109051f0303080a0c020708070902130803070809040c050c07240801050a060c020a091e2a0e0307210506060d0f060c 67
    0x4000b807800703e080408440b400b10049580380440c90703202c0c94001c001146d2800944201c05403884c1940e90040c0d60b0700284180d0741441703c0440d58059000341401019107117174444004612640c0e5996195001e0a402e54094841c1d40d103101000d01c03a040d141d503000c0c2c1600d4054440d04140d0300c4041483c40100035201000085020708000490703450424410400100141300b405078460100740e5445000078860780c030120441d8010010000042c2400041d6201007000301e500140c50030b1080301c00ea07001d206503030070301d080741c040c10401044c09040d40e072948030000c00c1100e2034100038407561003c1d80d100d2000e0007010341c41b05200c6d4080041c144200842d610716480509a000f240c1e54030300c180015140e01c0390b45440f8450809110020b000043d00c50814040d0101c01d139070f078007200e44046425060501c04546030400480001d40310741520200401d500a20081042e001e0b00061000041c0030718003d860308031011b000e1007000c81d81c40e2070a501c22504940d003202400708a452a075581030000c02e030350030000c1d082c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 183875449 1250 183874199 183874219
    0x412110a0503040806060f0d0507060507080f0a08090d020a031704050f03030c07110402090d15060b0d020903060601030b03100504031704030e040b040507090b0306041b0f0207080601050d03030506 86
    0x41c00a20143c0018403018006007124149007081095a015020340c99001c0d5070b900c84008045030001480004a0f1610300f0320395aa03100302d08010109204160f0a5404d440c000511520090781c0041307035502c128060b506441c100c01000104a803a040440d40c09000103040f810741402d0b450000700c0310380d0007a210b02c080f12403540300c0d206403509503042200e1820302c0080100d91542400841c0501d010b8007a4101c4045103414250740020b00c180f81010310103040201d40c0045603915110380d60101018014084500d5120a141c0750303c14082d5110361a03081c040c3c0603040104000e0350281c010101c0b051780c01000340c10701101c01448640101801402034080100010500095052141da0b040c0603d00a594902d003040d02c4d0414082a1082027400c1c0740641d240c04104501d190f4001e04007810744402564980c0e982e1071701400a8043c01c0d05248062403050001a6804081d0b080401d8810f00e82460f02510006552810041c1e00c45109110f003903080320541241c900064803a81c0850791003c001090343c078403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 183876699 1250 183875449 183875453
    0x30506040222030311070e13060906020c01060f0f0302030a12022406030d02060105091501030603060204120b010e0405030304021c1208090f030301031106130e0c090a0803030412110a 80
    0x116052603491050310340b0020014070134140e021060300d404045000003407440ea850f21814102440e001880c04030903d00d07025080c810080c1c1508071003021900720300195100c20084600c0d038001e02851266500d569902540024040c05078441241141e800a000d0120b4044548880c3c600200019008003107000c0d03403003110b0020114108010b41c0146010344454240b4001043c145000d18200d01c10040d94400c0004100c3c0780d031303940c804031760122001e2040c1c941801d02e240143c0181000350001800b090000c00c1c08101203504055019055029403101304599a8590844401483c02d503005003554004100040c09410010110301d1255000380540e20300591a85488070001d000030f0002c4d001a80c1e02e000d001d5440700070031180c084044810003031071542d4515580d0302542012401058040c07040804d00e09829200c001e01c00380104584100d20120341b40402d44c2c40c09a5124481c917a1041e01880d10100300000d0000541e4070595226030480780480e80900244e610b01c8070b0001444d401d1284102681c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 183877949 1250 183876699 183876727
    0x3101b0e1503060121020301030b0a0207050a11011205010e040201030b0108070c02040513080a02060406150e0a0906060b0c03040303020105010f0e0a2a030b12061006050c01060906060206070905060412030305060402 94
    0x5000c5c8540001a203a504503c1d128021000280070080c130540140400d0010400115906100d02e901443e016008001c1c540107035881e04c400f4080d03102041c5400000500261800c1c4103600c100e100f60380800a00205a006484900c4255506400104103580c004018141580b0080d00103002040204043c070241d1303136101042d440081900c0050b0001010710040040714022510300214100e0302c08082c1d41001905004404001c025110725611017140c00184202980440d0250003134111090b512500407081c95560391092008800540c80c1000000d80706e95841c0c5904142d8100c1412941e450721102a50006402c035140244c9071810700407601550403841d0340c0030103080701d00743d1004140300180d0b4081091848900c10321302c0705600321170301700a01c04001061010030b40d841d60038420348410b151400c1c54010300361038106e928094039006002c10610340005226110b0b613125964803096648460510182e0702840c4074060354490306030804c5000a00a4126540c405c0000d0700c01410510400c21783c01d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 183879199 1250 183877949 183877997
    0x302030d091511040b250212071521090201120f0e1605010804140f06040b090c030109080f0d020721080114032a03101b0e15030601 58
    0x1c0b4900031200c10071441828074011403a01e803020b4011603041510384084038200d4071480401807440c0d4142d550405200d082000c614844503000b8001500b81034500e1101940c880036402503a0784651854102c00d40c0c0c80c0b0032105c40d0702c8050340000c0301c003070702d801c0100d00000713494000e404906010f07010b01484035000304d9100f58071044100350700209081d0300e8000301da800c1c1490056110513140d0b500c20144106e90f0401c1180e9040369004201d0030f0204503200d4960b080c05001d243c68041406654140b0050012a245540c041c0d140e1f1320544400c42ca81c00201401c9400c986401002018140a4a0b5999140304058840b84650110240c9002100d680d44064661520424504050084110708016901c070050a002d000005411000e00401d44006660ba000d8030000101d1100100c040c0ca010500f0b40079000007000001d002c607441c8403110509076025028901e4a0580048060391601070310f4420916142d9441000e0500b090011101c07680c11540e6200810850600c501c40100440303d4185010348 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 183880449 1250 183879199 183879203
    0xc0c130f0f0204050f240c070e0f0402010906020f07030227091c08071d010507060504150c020a081c0b0303070f0b0a0501180c030b04021201140d031202070302030d09 73
    0x59440b82410200000082d18108142c00707004030099080f000b128040d544000054a911030f1b40d16641822200c500e404170503001003400803002010f100e00041d4407041c8a0099200340c868005090300c81c1402c9136221580c0b28018034a44c0404000c0001d0304283c02c24203131030317620034591902c94002c41c112144100c10542d03500c05181e1000fa40410480d0341900500311036002481d003c4000d05240d2402000c07200d9500c144070309904004a800d68a80c01601140c03503071540f100c2e050201d40b520b810304040c180005110514001d05052941140a1022aa404000b170344040060700b040d031440031043c802d00203070400021041d41c8005e01030712917034200080c2418078842c0d1141041c02c405464860f0b0100c0000d000c000915007064010311000441c59252070082c0c100344000111000c096008a0240c203140d4405500184000b8150300b0319003148081e141614a80d01554106140714002c2c0038007280300709009000105541070b03414103010b41d0380013010b045009204490134110407440c4101282c90342082 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 183881699 1250 183880449 183880451
    0xf030c0503010e0c0603150d0c03060b03061501050706050414030313060c0c0c060c1b09150e102d2630040806070c0b0901020c0c130f0f 60
    0x2040100d89424000d00a11001c0c0501401001500300003040581c0005440000149401e45c41d042d826241c100c4070340713030041c3c100c0c01c0203140391368030b0074002d001b0405180307801c2c0280039503000941181c032280c0b20042c92070f9060f595580740200c00d443c0c240003884081d01c06c03501b69030388031000307a18044104007450140c1703444600481c4102032840c140b400c480b000120701c014404040f80600100f0300d00310400040710030340c0c101107071010744170300c0c00c1031501f68040480348100c9045031002c244849c00d9406648000d10f80880910010b4481c0721089c44203108603403001140510b581c06008031380d071075110305611404040c0d41050b0140150b54140003401d40d608a450000c0c804003100c00140c40340100107000440d9075001d400302c020700364041000000d5504070b03980c54100407504410040d044408403001481b4517010340d411801d0003580282448040790041d28000c070b02c0070110705001d0061003203400030f052601c010081607030b00d2003e00c000042d10603242480c0361f82c0d070f40d841881800ba5004007a00301000400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 183882949 1250 183881699 183881723
    0x2030a050c1e011b06200901020c0a0b030a230f06040c0e0102120a0c0512040f06090f050f060d0903030c0807020109051b0319050c040506090f070f02070f03 69
    0x6106200c0b6600300d41030109410b403207100e1283d0360851100c030b02005040d951015410314900b0910080e001c40d03101c11601a0008100480e1000003501410110100743d0948280d9251039040091030022030295481c10201000410b00301480340c2d02c80005884201048000380c0c00030408082d180d030086440c400d40d009860108035251030280b25012521000b402d0400a6141a000007075540100303010784030350388100190004182c0c0c0181c5c3d00c00c01c01c50b840300031115070041c21030506e03225170014803840b1020b042d0882d000c20030500802c9084151640c10080042c8145450100466815001e1031980c2101c400c01800203006241e000b040d020354040e442c04590390b208000024040140103054000f10b900d001101800a440402c03440c00c550302c0a051a0358400d03540d0300080c2484000c81c180c80c040c80629450741d0410602107800351642708112000c02040e1744e0031090000411080740c407030741e80603400d00014a00d18081c000303006c60007581388116500903854100c09880d820254000340c4011142e00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 183884199 1250 183882949 183882973
    0xa15080a060e0d030e030304060b150a030204090f2a0c060203090312060913020111070e011701051f05060a140d0605040e01141611030f07031106060a0504020f040302030a05 76
    0x2ca02400c11503985005c00210403a807100369100c0c08080c02c014a0540c40b90101d4400b0342c1e90082c14003500c801291a5a41c503805d04001500a500501c1150302d8142807064019141480e1310940000907680d0200309040901400c2d034145c05084020608107200c0c02007a0300d40490498806588242c920074003d507500c91080a1242c03003840700805251203550b0441c02c104be400c40a844204c1400c0c2e0a0818079100b4004030511400c1111030b41041401000381000040c0569620615002029010000300003e03107524490700d0007104443c1040c020040d20160410950401070020300503c451840e1000b041300340000b011702540c6c025504d209805440d91024095803030540b29000c0820040c900800c0b00500e0304413400c149410043c40c00000e9555845511511801b408640b427119500000740c90380c800c90004c9020158200500941c0054a9108006c0c00c4290014076140a504c0040c01c00100e1854030041001030740c000c00304e404403148107000010060310108204102d480c41032003e072030f01107054 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 183885449 1250 183884199 183884203
    0xf0308091e011d040914070303142701020c100f0e0105030105181e01060207030c0b030f012106051017060412030902040b180406110f030a15080a060e 66
    0x406400101c240007442014074981e0081d05510540c0c40356501c80c0104a0ba820000303000b418020341c05800c07500300c0900920750040106014040d60712030303121300e0150100c0d017507600c165000f13075090203407006480301004400302c031900340c540c144500500c1181c901408960100c0c1140501c140c0280100300e07482c003103030701c0c85404c680c005a0141003840c00c181107600d040000b80301e00e289090b1030010b10b2040c00204040700c049418140c1c4941d031548070402d080d6950b8000030740e5000c0c01c0c401034840d8440c02d2004905028100212030003002c054040c2c207456404c8c035980d00341005485070f00b02c1c2344090010044c40010414010148500342d204070141006d4901161202c2c042c1e08441e01e2880c640206081200094085e103020585449520380002d030310b41148080341c0200307108210141e1204045002d8902a003102500c030703106620a2070188400e4480045280d0540038171560104c0003c4280000385102505500660080d10501490703a8640d64541e0a542441e41c0d401c41902c0c250703201c020003610382c841 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 183886699 1250 183885449 183885469
    0x6081b061806281b020f04061703040906060c031e110708070e060303040303020a031409310b011407150e0d030605030a030c0204091401020c011a04090b0f0406060f030809 75
    0x83c1d08040c521145803551071094a080300c18001c0c404c180400d8142c0c0d880c0c40b0f550060000d84440c00107001b460079102991a0f40b90020712405a1781c5041080224042e480b419480d410355074036032120508443e0040c1c070292802c14250f0481f003080f11002c02c42c20884c030104140c8000702091000b5118203070800001100c1c000d0010324580c0a40d0040004100007540054807a03c3d140d098901600322582d600208501031007601900744c0e11000c0c807403105102c078040740c540900708502d818400c882c4211324903801c1d01b540e04042c1c0060100e80c2d00100d080181402c00000c00b83c4030300c0303800e00b50f207000356101050381260813464140300250b0100382c1c8100003540500c03d80707026080450060030701807050ba030000c0100e0800880240282c0e221400c450400c90100f40001a200020b1b0007513440d648000d55090007401104140d0034550b486d030030744900d942003d110710000150010030001817981c0301c80440c01c81e06006441201c0a60340d500300052010700d003802500240d40304112840c0d9501e80141085400d001d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 183887949 1250 183886699 183886777
    0x902062205150f130306060902040509130803060f0d2a0602071a09060d05070206071b05030901140d05040c03061103070e0f01020f01061806081b061806 67
    0x3081080b200c4206140d00c098030076090480103030030350350f2400c0f82085030b07480c0d41c035840100414140f440c0498003848a40144c01524400e403504c51b5150707100c150302428040234180107003400c0c00801c0414458201650201076600c0058543c01d21307060701d039031905e222201c1c0c424cc00c0d0780c1d80b4113031241c51800c241c1c646684004001620050000c0c5081c558110010a10f41006591044000800c1c408a458144c02e880804620364020809071030041c101a460380005c4030700200140d80031007190714290708824070701c5405401c0b400445c10a0004001501c00790315203a119508100c060003074100b624468050300b0f03c10745c400e0030f6240c100c501e503103000d00640e0402c1c0d0b4050b40070801881000700c40c80c2c3c01507000c80982c3d800c0322800c501004003070060303003003502100c5003030a83d5091110106d81c0305602003c090b10b00000c8a010401b0320f603156040c0361613690ba80c0c0c0e8100314401d01501c0c0f020303e10f008400fa0902e913080032a43c0152081c4c2c080050820340c01007414800040d040c2540403864003514039441c0350f043c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 183889199 1250 183887949 183887959
    0x1141305100b010c02040c020c01020706020325030c0516081002070f0b0a0e01060605090a08070305030406120f1b17070e0603090c0d0f050708070311060306040902062205 75
    0x108640c0d035201c0d21884118104001c1550b1078414200756072060404c106002c3d00034104108440c5140f400035103800d54607009a02500c6102c000040c00d03072000007124914401ca8060308904004646001410b14103200305804100103d8440d001241d024000c1d03d0346140c0c42c0400c03100052a100f8440e050510a009400140d80305000c0b1101080444030b140500990006001500340c0d1100401c0000b407810303420f00d420b198078201011460707542000092180c0f0b03070300301d4000b48040c0e0380b201c80e80c0d034400243c04010180d40062104104060052410049201030304102041e201203100c01d02c0102c603264014504000c42c2800224001d40c3c214006007401c00c0700003242802072130074050240004e042c00d68182c1c042c0100000007038108000340001b007a12840240701d10303810b10460925000c1895400001e413614011510001182d100c001a0001201e901c241200c40c071500395410081725400040c0016001a100e1140500584e18500201000382402040002d90860003080345050007035038206078083c7c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 183890449 1250 183889199 183889231
    0x20c070602062212110102040914010e150d0807061a180103080a18030209070f0207170a0204110903161406030c16020a08070620030711090a0b120114 66
    0x180d44a420841c4103d500085000c1c40c4101c900000c481c01e100f0f00c180ca40d0613510100300455014001e8000d9074038048502c0750040140d80b00c0700e000140380825210b60803a600b10040c08416400c002190100450180b0b10280c1019119110441602c03140300200082600c2c14023480e20030700d2b01c010900214414281c0307401c44c80d81150b483c100d66105141403c070901c5002900c03031800341103a40e030302c8001d0740c0d01500c10b03400da080640c0e005d4078060081103854058000c01d6800309011102c1181ca05445d00200001e003a030344600e030248801400d03080c812101c104404c2002d4802501c003000380180c2940104001c40390640761004142035a00e0704042103200c1c903000c00900c031480240c3c2069035000180e400d0352007061440780c03000641c031408681c05002103001e0600c0c001401c54020316142e000359030402d4140540405035412507168451418018136488017002a02d00d00d0030259440c40e44140c418500013050f00f440030016000800f0b00100c490580e4681d0306411031114505803154100800340001085 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 183891699 1250 183890449 183890491
    0x31906020a0306080d0801140406030f080d050708090c0f06070b0f07020c04060803040b0906090d0305030405160303050d05071107030f0c0618090c0e04020f030f0f0c0703140d020c07060206 83
    0x1b840c80601c503495a0120226025a60382d943e903000d030000356485044250813005030320788051140c00010081ea040c1c1e00c0c0200085180c4d0155044c0c0380310b20744180c054035100c80410708101c0914031181c01960440c034140005400030b14840d20320350284040340c0b1011040e1030b201000901d40000d039103903540503c0c100700d13080009100010035079083c4d5004229040e155014400421003500510f080c0d40c2e44103010004d4101810b0b0000015405140900242c800150901c140090118024800240080d0341002104900b81103540301d150003d26a2403d86500c070000c3c1c58442c41c0260307a030425034510b542c100301c2000f08121044140001c000600b40b0f01140c1c001c01203030b6407042086216050006443c0e4009509151003614041c075040c4004100315100c004410316180e00c0c6e00112500102603400d40c010074000d94805035400e22940d80d61100c0c0b840c00c00305580454044034030040d5104402418030400040000900181400c00c0e00342008148151801038001d140c44d001810200c03200700f6009603446 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 183892949 1250 183891699 183891707
    0xe031c090b0a1506030e010f2f0f040501031503051b031b03032502030a0309090e1c051308060c07031b021302030408091504090c082202031906020a0306080d 69
    0x84a22030f040010315041c003440f1150240100d03100c402313100c92604840c40300c058928400501c9151031b6a005800244403d0601201e078030854845451b48030701448100503a61090708080003c41c5505132000b499980c03552420301c1e0114450700b0085040690703512100e6410304220706041011401004200f0851007004a83c40e44200c25041c4044400744070981c0c1080310750030902d02f4459024007103c0d102445400c004210030a075000c2e9448190070030403081c000e10b000080454104814100d0f86c00120300c0d4030030568186c5d2040d140300d014100c4003540000c40c04000d01c81980306403400c0c1c00e103540c2d030b458604d0300a0005001c01101d40c9008840c1e03110b0005a2218400902519800c0500507525100e070308000020b8010b50500c20f902c161042944c15101d4000c001900850314a00e1080c02006c080017815030700101d003114071110445518410740e80b0f0010710185404510b00290549070342135040340ca082405409800182c0d00e05400007000100541d061150a00034071048018060500401000030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 183894199 1250 183892949 183892991
    0x20405100f05040e0c0405120a020a0b210405060402090f0403050702040903140a2a1505070c0218010503060709150e0a051306090c03060b030a0e031c090b0a 69
    0xc401c021400c001181c03201c2c02101200c0103024065a1402c40e403400c010301d81c41a1307005008881c002c01480041800d4064001180244940e00800d80d5401d103060609075051034120321803581180800a00100c944100d00140b24040c90046000c0c114514050060103005000540b005096240f410204000709610800b910030031507044a000c181c81e813003810100d800c4107403c4e19000c4071034000110714280f103411122003202841e683c0301c03000c0300d20280604c0070014000a20003078641d022000080c840000968000382d40031000c0e083c50082c1c580c45401250020300704503890104805150010301452408200c0c840e44442e152034610790890400d0000220203048940400a01c00452028041c503554110010080c25010703040300c2c0d08035000000640500040d20508440350320307054000f00c215100b0301812055440b031170b580b40d00d55280d00644400600700f1104d504020b01060110202c26840c22925000c00d0300164400300d0300140d0b5040400c00ba0320301074404242d00f8501503001c024280080045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 183895449 1250 183894199 183894229
    0x4060302040311100c1401092118060c03030f02130308030a060e0408090607111003020d110903120d0f051005040b0409031d0a1509080d1103030109051801090302010501090f020405 79
    0x200c240000340d2100b04d0140040340f900404020010002030750540c8020a034284845066490ad01c00070105040c60b07808152a0048000092001e400c4c6004039009402c21103010100e40c000601d00102481c186000103d02d80003103400b400c2c00030038005484901e009070b0003d807440d42c00560440c02c140e41e46442c02d2180c038030014000ca2000c2001010701010381211030041001030706110103034500b03000c000d00a5100080440d01c180c5810703103840084408070140ca0302250301400a1140c400c1003c03954240341c018040358403400e40c9601c210f104040150040d0760007108a10715000d50581000d0400058607268408240140d00d42211100440d91200c86061000c20141001400e1032000004c80e4607054241c02c00318800030140030400c08258800d008004440c40300341910100b402d5107404a820820354020110190300078030040c003140140d54011a00103c000d2800d010310a03010600d1030a60b2019902980943d66a20040084002c02e0040441540c4914401c61a0030304041c0010345a209185c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 183896699 1250 183895449 183895463
    0x90106030b0d06050c0c1005090316140f0a0312140a020c01020f07350d020a0309051504020f0f060f0a0203130906181b0e03100204060302040311100c 66
    0x4610326502d41d80c2c41c05480d9600403070244110b20703040a4480341d55000c10320400750381c8101d51024010800c1882414016000a005145450700304c505100910070644c13000c0d03441413600c1c840c0b00500d54040110300c19418803403000d400a1000c0d8103001e450104c814061003d11814400140d003010307525a1115448560300320010b849010646280e402800340e01c1c85070816040015041085c41b101c400f0064419004103120640c1c1401d8800c1d0f4411100030560300c0152410034008582114015005000c5012043c5400902c42140e5100d541c030300074041c456000c8154800080c8815070400145110700c0c40320603190040f000c0d8400001c64203a01c0b07035000c08c84181340c0103d411901a44240122200d0454041d00c0ca000e0f180c485962800508551140d4000310381d0300a0300800c0319280d405103820204180034020290b43c80c080e01a106081c01040c401c0c0c1c140507240300030b808080188050000352506a90041c2c0316802e40c5069290120034030206071013208080980ca2515034030007141c054656202c03603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 183897949 1250 183896699 183896711
    0x60a0c0219030905061b010510030f03031a06040608091203060a0302010e040b04050108060f01080d050306090601090e0c0d0b040605100f11010c080402010e0d120e0a0b030c0403020a060e09010603 86
    0xc0868200d50f0396045a0342c003500004902c21220f03030424255814280321030003080143c4500700d01101e103402521008044c40e140d41c1031076000c24004e0f4003100741e0a5000c5084d800d298220300001d40d8542c4250040030200c2d03022014050f100c241080910700e24514101c4403450350425400188030b41d446888001d0400c66600c05800143c5c8640c1c000d14500c00e0701610510481d610741100503203c081c2101c0c010f071840e5400000080c0600c002441ea00e00345520b846961079925580c0501080c2c110044c5810706009180600040b540c0c40c00e40503d101d0440c4070050798845040c0e403c0d0f001a039400809440c422070500609101603a1750303010744a05034641d820000c003c0700c28070b503040d60300d002202104007065190102903440683c000c1030f0f0b648114400d91741c1c0780d5504000c00801544040f1804054407071908079a102c540303103002e0050240050307002403c03200103d03520407852881d54011124240c6000c0c005c43c0420440c10b00b28007401c0601494203040b030001e00290301048008005214440030192608 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 183899199 1250 183897949 183897953
    0xc0305060a08070524130806070906080a05060d02090a0e010e0601051813082709090703060209010507050a20060309060f0415020c0610090c081b040806070e03060a0c0219 75
    0x80003071000000c0d8800e807951106c0071010041103102440c480c0801c00d001d000c0c00100007611401c455421303140151200f03006ca8640307018043c01480014001504074051207201c0015a0303807526a940700700d030003002c04034803500415002c0d42074803202540787c56980c0c0000014442c0e56180d01001c0300e11110704003101e28a03034445000061003440450003401441d030015088036502c3d000d821030220040d410f0284040c000300380d018030001000803101d600490300054021700008982c3e4000308080b0805140017410081d01782c131603d04100c2d050208480b2140c1c5959100d80545828103403002011040b00e41ca802c51802624045d1a150700400341080500d00a000500304510541e05003032421141100b152905012030080c0d80da20000e540260040401807400114400180125a05101070b50703070707885582e02c0e080c10030010984034012a090880e0180b1000c621010100052481424580d8607030942e04540d2090504151001e004401c0702030410342ca009800b5000102c620040710b210380c8200301c400043c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 183900449 1250 183899199 183899239
    0x504030e06120106030c0f02030a12021e0d0608030c03071415070302030a0518030a08060607020d150c0215010b0703110609010b181b1e0a030c0305060a080705 70
    0x1404030319510000c08224860070540840499059030141e0700c0800c8840c3c19100141e882e104280f00d0000168008c028038410309204101030032990514103000b5080540c2540c40300d10241c4555076245c11480042a01f1100c58854044c0c88001e1228501031840c0ca000c00740c01d1603d81c4140500a03242580e50300e80c01e080e2280c2000382d441c0c10712402e00506074906210b03a004010354810f0315100060303400e00000c036498094035004034031b802c07205000a51030101212010354501c04000d10055000800b40042000750300c0b9004c001c21641e201e02000d180701802046000300b107528080c0c4000840d0f019448079103035030500d425002c1c10341c0c440c500015251007491a04883d100c020440d404110f0042034144401103005400001101d58210741c0507540060101010341031240c01c0ba0301481c142e40ba00e00a1b04600d80e81c1e030085c070118a81038800c0c01c2d100c0703003038440107503941c0050281c00c00240d854003801c8e5041d5152044980050086406a4080b803500d00d03096942d040d580240c030320541050740e8030265205a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 183901699 1250 183900449 183900467
    0xb010b0424020f101a09070923030304030303020c1002070f0b09010b0a030501050601020f01090b070f12060b1b0d080109020d02211803031b07060603061a0a05031906050403 76
    0x18000403151310100005058000d403a480020b501c030b0203d07500c07840c130b002e1a2441d0218843c0e00301d5a5030380300303c500d030254500400c40d500040c2c83c081004408019850b07281880280051400703a140969151848800c2c54900f203800c1d00c10a050610601c0300c88002270803200000480d5030020310784502921945881c034010b0900071481a44640c1c1217200004108064100d14821030f400d03001d5445503044082d0403800d0b20403c1c14010900070b89003001542c1503004030a03448420032907140040010342025030034011600241c000315100c1c200460305009020310320503501d00406000c4050040e41030003480241c015001070013106d03130303158003ca0720003444034965054030043c00d100c00755a0644660003101800d000403d850580d03184c100a5191140040b0000403a406241404015019169480003c3c6031581004c841202c10540750382c000804191140640c200306004040003168241b0900d041041c0860303682d1045009170807581d42d10013060300117070110030140d4102038040b80ca5503407890200c40b01c3d06 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 183902949 1250 183901699 183901723
    0xc05010c03090e310302070803160b07111e16050306041502221406090d0b04020a0b120603151b070218040f0623130c090f090b010b042402 61
    0x21212060360855012080d240e00540a038082e1a100e41c4c523460016201d100c0e541084404030080d180c440002202c0750101d5034004842d20b488050940341c40c03642401c0c01c4112503013101c03507416a42d004604000900180300328000c2055240d0300079140c6408240c445000a02c00391031118a00d1490380d145039581c0440348500c2469126070b0300712040748021513540c042401032240c450700500d410b0f101d9041c4201250384102d00144804400c1b500e95403003c840100050040340c203c410403500155054195015007080d600103000381100b440d0500078145042e021300c0e50b081000103102c1c103000c040c0050480101c1c00031188000c0b240d88080c580040f40041d10120b901a409640f074000300414048161700725001a0320400c0c1c184070f0740c00d1800500b60502c042400c0440040d40e103502081103071640b5081c0f1000075100c0c0000d400d8041d511840c81c000c85269100b5081804d454000e0782d020490102131712405846a5450241000e040a50f960001031301050340c089520580c046c924000c500030885d0090000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 183904199 1250 183902949 183903001
    0xc0b0a021606050a020114060d0228091d0714010324080a0b0a0501080312040203010b030d1101060605040f03140f01060f0306050708070804060c1404030c030c05010c03090e 76
    0x5590750b07000400c1980580721040041d460a80a201c07002010100a1700030440107240b80840f0311550208074440120718400c240001da11064011a20b5500c200c0100619400000162161561003800580c0508501c003d0690700240d406014050503060312028140c0c003868005810b50300391000b9010000c0720701c000b124a0f01c9410000944400c00510380e0703c01d502c903018440040c1c6406080006454080c06030407606d800a05c801007800401c28140381d0b01c1030000b00003242810b03030742e00424100000752050138001154182d9842c6140382c00d000d28030080c2010715096141c20700d003407208103c0601c1c3c0c0c00010308006180e100f198440c02d0400185a00a411000030002d050b42c84105c00340c0b03074486100031a0024200b0300001c115501540009200d032099460342e20311692540e40b010014010b0301000c0c014004905103c80d5140300c0c034406480614410071a5a00b13a50450800d01d00e210295848a410401100940c5001a40c45000d8104490300808003000360b486184100120050100141c0240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 183905449 1250 183904199 183904243
    0x60703051e1524030a0c0903030c02060a0c32070609050d0501060305060a051902031e0603100c170112020303120901060b030c0702010e0f01090e040204090b07051b0a0c0b0a02 77
    0xc0c5070fa200045010310301070401004141c1c62004292003400140c40003401083c158405e03c00542000c2000700a100701900d00808424500c0c1c1d5004000621500030340003100e010301d04c1c003514414910b102e03440050b0140082401d00d1030088000c02040c0c09003e598016407514488c1070410000750000f0307010f1a4803000365800c0346002e01206004000482c2c070702004019818460103156075034421030b4041c40e61401e02000008211008056001016000a800d4070400001042c4240b0620844049641903a20304400544c50349038003210000603005425090720b00c407a1500140d800008554070f0482000ea603038566074a021443c1d006080b140d0002d1854000041004603107000a0018026a4400d88a0002c019280014800c6c6040c20640300b601003880c00760180400c10251034429445403005101103544a060341d910040300310180c650034003081c030100e9412003802088100c28429200e40000f4200d0000b0b988031203075666403d01c01c80720020740c00504040514800d204e5a800f240c1617045600781 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 183906699 1250 183905449 183905509
    0x303070506040c0603050412030902031203100302040e03090d1b09060e0f10084219090206070308040f0507080d111207060209010207090905060703051e15 68
    0x201c0000302c0d400c07503248220b2800411914040d205940c040d40e048106500980d91100f001c1e0700601e09100180e9040c405c100c0850605043e800007184611000d400c540301d5a842c0d031040c081a105d66400402886e00107002e4005180c840c015043e1075140c0003d142154030325140310004404640390008001c040c201040443d0b50302400b40b4850040660314052200c0f5500e108030605050658040d5210580241d00c100300c050300c410b01c000501d0f0020f81c0035102042c1840340c100801102c3d01c1c207410b001040350b00811400044d25100c2138480f04944130140498613180c1d0014000e445040001018000d600001c40c4c1405807207044c02101b1070740300003160322198480d084036580320b510710305000000e121184a00d40c604c01c0880c1c0c800c40ea00c3d011001e5801d101d1070359180006034224060031411880341510000e0742e0085d03406030110950244c0082e02540c10305d010001c1c01e60f000186000c01440c070080d02440750951100040d64021006980c00310304121140000700081d03540d01c06500ca60680c080e055035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 183907949 1250 183906699 183906703
    0xb0c07060c05040510030e1c0512090a1a070806090a0b03060a0b040b03010b030715030b090106030609050f06090a0c110d03020c07080a0512030a0f020a11010c0516030c02030c03030705 81
    0x4144c4000b1289607000c0700540c0c000301c06941280d0180ca50710303044441009600c01604204103601d14031030602905042c202c0c122050304200860f4010b016a21104c0b0384028403081000105010ba10030402414a1408a00207003a080f005030401e400f8001700c5001a0100c005944000c16045d0001c050f00c1190400040ea41d0103030003030f01c0b6410300c103c0c41c226043c01f0511b014802c2c2c0308440c50240c060a81c0c20702d00550000301700c00032800303c010315807034034400005c0d51307031b00514640640600d450018100e82000c008004450006000230b100070b200701e040c8a22a601e03046826485188808081604c6107808003c547c0c10f0720504892503584038810b080150180c140d0050600060326004485026544600301c594901c1191f4001d4095007001502c0207540f6010b400a5030b02417a004008280d881030890408200d038881c003010000211034010303880c00c601082c020030b580844c8501d452410401c04112113a06141102001018410009644000c54405101c0d0700c441990040a60744c4a00305810019 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 183909199 1250 183907949 183907957
    0xa080318061c0b040f090503220501080105040c090315091a0105150318030a0908010b0d03020c0f010e0607061401061106070f1b060c030c17040b0c07060c05 69
    0x100314040ca2a0410315420300905861084225186021078031401c18155030007031140c0418107401c01e440301c403e2800e140c0301d80107454100e40f00314001c50396250b5129420004124040c1c250201c000700f06010091a80d010401506440d0121000141030508420686901c1c89a13400245a201502010001d1051552100c2040c0380a102c1c020582d0b040440100c0d1161340c01d00031190700c541c141106910801d801c2028551010100100300320030a46500c2d41403954010b5004c0f10f00040c0361540c10f10822100b8014860104c00c1500e585a20400966001e51030b00108945180900700c5190340c2d040326807080398907000d904006884550740301a182020780c090500002d5080c07440d500c50000041003407150182400c0504c3c404098025501ca142c0115251410703000380d03108000300310184103801c0350078141c5031940e288075560000d5614105640070301074548a801441c00d009204400b00c019840708880c40d5803181c0d000085130666503401519481c10b000b05c180180c500f500d00b40d020744560341c00070014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 183910449 1250 183909199 183909217
    0x50610050103060b03010503100b0a230111150406020a02160b130501020d170c0d0c1205060d03090b0f0c19050601120f0201031a04150312020d02030307050a0e0a0803 73
    0x14060a61208003130104c5100a100b1980c140e80409042c0c42410102d038404036055400a103414081c40c0e0b100c284034010400074468001d29460621900a20741c3c10821440415042c0000b40c0350b40004881900342500c0300400141c00c0a40024003002c800b44244003030f5642c0800400040d40c060303110015146160050081c0b6407060f645e507000428198000a000031a01e00d650341c9100d000c4040f243c1882e0030707140190000307800c0c0006001031401c40803540202c6130b1505990386ea480c0d0089941c4024000e40c3e00142c140b5006030700310b00c00240466400031004040c0e82c40d21074003507a5848110300f810258480c95501011074080c0000104000ca0b004d1000301400d4041e004645980e42c0769800079540c040d86101c01810010004c080c0700055001c0d03008424100703000c195051040040e03002241c01e88030417040740c1c0b50000300d40b0003c0c0104200b08011181c0619030740b00900d0b43c107283d0803001e0750301e12001d480c070000e1000c04100852154420b1810103141200641082212139803500626500e400007015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 183911699 1250 183910449 183910451
    0x1080411281d0408071a04060b0a06111015080f0604120201020901051603030902060d060320101809020f0307110f06070c061407170f0108120d0207050610050103 71
    0x2d00c0294403450710740c008030720300941c81403501c85a807001000e45c010300d000c549445440424148400c1d8204041d480b860040c0e00104565040008000341d40c1181d0300580e090041c2950100d29484002402c41c080e5045108002020f906c0440e07140412011540a1955403003a0382c45001c030400041111405144920001c961044013118103900340d015498656000070000c1c440110880700c4000c05241090003405c002500e0200c035004961150300c002525a912901c1d44000c02c1005942005401c40d416204038a0012070b00d4000002d004030702c01160790781002520f045034910000e03070304261f030700600000800315940c13803030751b0700c1030fa607941003103903003c010400106090302889000b003240c00c50607000c100540300c00e40c1c81c0c500966402910742c10a0700c0d41591244a145182071507044a40246843e1302d4540847e68100c01c242c1044c24010490109240e591004100103000021109103107407646010390385582c1031503113580090082040c00b40c12032003100c040c488000c00c0d0b01c41d108191942079030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 183912949 1250 183911699 183911779
    0x9220b03060a060605030a0507050c0a05031c020301050603040605100e0a0c0f050703020d080702100e0a0c1a030f0408090303130509070c050705060703050403120e011805060901080411 81
    0x610b00225000c61080c1c101245040002410f5004070b40e110f42d5011040c0c0c10414101908580f480e440c0154060040760389620015541d00000b100c01b41e0072205042c2604190318547c1041d0218009000141000b802551508049103201221000400c0949001d201c0f00200c0d242c9072407a40080d040920004001c5041c00001000042c0300da82101d4089070160014902c1c1d5501c0f45048070a120010244001c6000c1e07100c40c0e00302000741d070047c120b00301c9504000b84a404d82c0781c01c007640188446c0d170001c0c05a4901110701801581c125084e41c1c4d220006407000c00381c0f99114242444a1700c40d0310070380390b0f050200040250a150b8420f01d514141d5070300f6240000b05603521001680e0500c4020f8000d00b07954041003041250f407400c480100083e030300c40d203825800e1176070302da955000c56140681954040f54804417002c82550340a0485009031300071103000034106241c840400c0c9603120f000600b504101d0300c0b0001030f080c0034190040b1044404050f0000e900c1d451541044d650302010702040709290780040b9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 183914199 1250 183912949 183912961
    0x60403020d11102c1008070201110a1205061c1403071a0f010b03070912051c0908010b040902010e04020d060e100305060f090d0c170d0e010b040603150209220b0306 72
    0x2400000d51380502600054501130743c0079620300c0c0f0b00526000840d0f4859503071484c00380c0d284002d04800f03005a107990001c0c10b03542581906031900149070600070f00300704041640b000b2280214461440d00300c0c402c2d510b0350306070852050940c0b06844000c0c02181808440e600c42c41d2840c101c051284101043c896200c0c1d80310141c014540c4000c1e00e140380001d000c11414024070320005500050a80706100300c0e00c45410070510222012184058200400d103051401c0140c2942802029007015003260100500880359001030141248800110301459010662000c0c07089554000c4001d00800d081014040c904134082182161460000300c40501912010404583c0380b041c0c40e901602002c4082c0107003500d0400e00705c6000d04484801ea41050403044d106c911740c215a002043c5040b541d0201141e84c48449034031a00b5205d140398514002d0b85444010400300e102e0312140c2a280c01d00b4040035a48104a000154080030405c0a4101c0d6401400c01340000c2c00755a07010300c0e80c0c11006d6085d42c0c00782d40c0700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 183915449 1250 183914199 183914267
    0x7031203020c010213053c010905100c0311060403080f060d0c0902031605120610051605060103020a1d07050307090b03090105040c050a08030f092806021b060403020d1110 75
    0x6200100514400d060b40700420f0003c2c580d00c101c0307c00b043c908419060b070f40358005014224001c8807030010607941c05400f014140c0c4400403880310502c090042c00b0b203043c196802860128018008142c071f400d050080348580ea0380e6003495110380c4d006460300201c181c5030081c04001b944180c5916400c21103590301e600c2e07864000c0c82a51940c00740a0000119540c80300b01f44101081070b0440f020070408100b114204d240b505090600c0c203240608014a20766055106004504e07000d5041500c0c40c43d000ca804441d403441070404542d0240080c42c1c10b98032504c03048010380300c511054100030100400481088a20750055001d0b5100d58020380c803104055640b00148860302030103008000c5960000c000809900f54448024500c2c008041c00e81101003001d01283c68102c24000440c049010ba0a0b40c2040300036810041d00722030104005210710100c0784100000c00714030444c03100a00841070154400705001c1840303c03d070780318400980310700712411079040d000300300030900049200752140015a41c5181080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 183916699 1250 183915449 183915499
    0x11b0302060f0a1a090c04031502090315040b15030c1518040c0503070c1112010506040e0f07171204080706020d031803030213180212061207031203020c01021305 71
    0x143c488130b18400320414003403180000c07005051001c00e010801000000030703488a940410500a500b0050300e400744d140030181010180d1095219040710700c3d084c00b0200e143c0f450ba0f2074000c4084554041c50034001000700c0e0402004244242c0c0c84104400c40c40301030b0880c07800070700103803140016039818180034804000440d800c03152020001681400040e0358103025121410403240100361007030b080390065000a030506000482651540d4564040c0040e90900f4012020b04d00e108a016080700200c4e4816941e075058580724110020030282048805844284450445c5031501012242d565440e00001075440c0203a108000051007904c0702804020f1181c030440d91114554100d01c0e051340ca20751011006500151003181c883c614407000042c03160f460314107a81195420030005030b26100d904100ba6560000180040d00030a481402608210350200304103041d241d0224031140e810704420400c5000340515000c92585601c0001c11010f0355994011481c11280121100b900801700c03800303100d9000e80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 183917949 1250 183916699 183916721
    0xf1e04030b1b0705100207050c0d05030327010f091401050c0f0706021c1508010209090402010315080105100e180706030b030f07090e07060804031706011b0302060f0a 73
    0x19602142c0d031901d0806158104035000506079041101588401d400c02040d8003940030100c3d0300044840800105008040c07454004407180c4c0b550749541c0c1c0703810307849100003411540050000800c200a04110b40b5840c402c0d919000002c2003101f9140b40c940c402007000f10010ba2320989103081110441c401401458414844050481d041c5120215044200c5c1c2022900b202c0c96034090004008a0226443c002184c44c8980350200f229000280c00d8403a2010541150100e40d004000700c0d00e4a1725400c0159422660a2a000801d662041060055000950000e040039420724083c040c0310421007030091701361200110f0344045600c45140302500800400d07850304194210fa6000c1044a029500402c05100081c041e05e0310030b60080351441c241010b80d0018560340b82d5134400b04103102d03010004035010300342c181040049410540c9010342840c100851126400350200000351050340300c1c0e5105013400307c0b1400e0000703407400e081c40d0207921004111021400c6a0719000010501070343e40c095a80049 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 183919199 1250 183917949 183917963
    0x212092b091a07020405040302010f06080705010806100318061a01030204050d240f0614010c0803010b0d06031a070206090120030c22060807020d210605060f1e0403 72
    0x9841c210b00b28400b400140c821910414060006902603242d074000c9500c500d1007035000140c0b1080c0485442e0032101c80c0e0300881490340c840c1c001400305981089141d07402c40001c4a95410800760840c085000d046015030240c03c145041c1c131041c0801c16282c000a02104103e0007a24a1a802d04011130481c0502d104096000780300503420808601e140c0c1ca130b960504e840520540c2c0940103c08035000ba200303e10015100346590f10b0301041095172440307080b2001542440c3c0898202c1c815141c0300d50a0206000d0001e5440c4000ba000c0510301040d4001801180e00250030078803288203100c1001c80902c201d800c400136009000000c0e0603801c042c800c500800708203250264171078400d22000d10994000404210743d80c502000680140e048500c408241000f54100d807007255030030564020241c440c003400c0b00f4150350000c1c000380290340d0400b0420031029903008649001c480f03010101000f40c12181d00150f000b41001519240800001c801803600000100752054028140d50555041e48114400a007e034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 183920449 1250 183919199 183919217
    0x207050a0309050607020906370303081f05062506050105090619150e150c100507020303130f0204050a020c0c120c060c0a0b07020a1e0f080d0212092b 66
    0x192501c54012091030041840c0e1003901480c02d6080514409d4000707500c1c6104454080030405c140d07001400c154002c0c04000c1d0036525080d00c1044101502a901541e8802c0342d0118a09000c00182142000880b41e00300820030315903058200309004100c280500303800790304680000340b102c1c100700040d1407082180b0b5403009a1903281001c0c24034000c00e02c140c15010031540401c101c03450f5507010300f810640809801d40300d0792003517504071080c41e0148076001d41034801d0800c0200094a034000c81580d41c02004504074000c4a0340310314100140d14550345009510038605030901c0f40c440074550140000990100c12a042050b9a80800080c105490601d490541c404c64244003e401d182028010360010081280c010200c0c641c1c505400c0d40048807407100580c01421072030240a50f402460144c045d00e00c9070704c10750003040d45910041051100018010100c00603641824180681c106c3e2038000480351941080c0c201a070400d41c076581101c849140801c400c0101e1241c049003842d50079034180d0315032144864 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 183921699 1250 183920449 183920461
    0x60909011404060b030a0507020f0f1f0e010203070801050103060602010608100905070b040b0c070501030c1b0c0f080c04140f1504060504050c19020c010f11030408010207050a03090506070209 84
    0x3001c884203105801c1a00e541d40024400400805580600c80555021402c1d24103401c00a1038126078040108a99008104c2d0480c201404980008051701c0555040c6005240c00c008902030000c1054809056100004004210398401030b1141600d03030980e4280a0541d90740e40803800d1791010300550310150400400300c031403c403890780b2400385548103000380c0790580e9840100c1c841c1c1c1c0c1c0043e0b1003506485000114040c150b031061110b00040c203000d0a081151403505580204201e1034a00d03240c078440d416038645c106201030b504000000f00000420000340940b145000d5881d01001c0503054000d40c1040141d03040c0102240405115071018551a68250307a640001c418440c80c0c10b840b2070b00315540307400200c0c040d25240206032148208880d55569100c80140c8003021901c0804002d045400c50700700d403540c0360780c048120780402140c5e2070602800d490000c1518214491a4040e20241d032000400c00704010380442c0c41c1181c40c2c003070b0b2030b4804090b07550030a00c56a0311542034000e600038500000568 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 183922949 1250 183921699 183921719
    0x102070b040e090109020303040b0409060b0f09040b030c03121314010f1b20030f010b131a060d05091515010302070302010b041509061a0a030c05071a100506090901 72
    0x1910a200f04004a07080d0602e0b00801e01b994050780108409080005040c40304000d540541d0340140306499684d0701d45000d0011700310f010b0044668291140d0f0319000c0107140d5039403c2090500d2010000d040d200c2c4240d0494840c841d030f5021104081e207051381c00314000352900341c0c0c201e030340300000042e10307a004c41583c008001c413002000b0840d006403106900d48100c0224520001c101c594020390110b0f44400079288003003600c0c103008203030320300480ea060001412030768545242d25000f25110b04008544510707004400080e81c030251060641004010404c40b11000030364001c00d001d01150016034292000340c0325020501031049503490108603500d01003214a5202c0d50007407141601078170000560092100c0010292881c1c032210301204401204144410061440b81600900e51441c1e409074203034826403a051319016941040041c1562442100c00060244040740c280b07680c4480403504c0c400303841d50380041e410401c1da0000c02112400c0000b02c0c090806104a40541200600b2442a603203015002c0e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 183924199 1250 183922949 183922951
    0x1602060a02031306052a0d0806030a05010e0d03050f041106070c05190609081501031205190201060306050705090303120603030d0204080a06050c04030210080601030921020c0102070b040e 82
    0x10003184401c03c000400300d84542c03c1c640c00740c24269078031a81d88580c02640840341c0000c94542442c10301100f01040c000c03000242d141107095040c02c208205070340d0400024100509000301a00f29402c0202011442001207408240c0080f103450400a40d12900d0b605020f000c0c0c00c49005224102083c07081c1072516044000e0040c0c14410400ea00400b0349400100c0c40c0402e19580c81007290104500610130356400128000140100c04000c11224883c40501000c2c9034040c400900200940c911043c042032140c811101d8000c600c02d400030950081110003402060648810344000d4940808100000d2086048440c4444010004e50034024140400490f840300500700d55418801004640c14040c0307140041c0004100e280007814800425052140c150f0b036008080540c0030301c04101c10300c0140c0e282c803110410098a86410401d07651001c005800a1883c0c11014022a42e00d4648010444191002007030151039030b825100000c500000699030b0b041c140c040e10b92190028802400700c040040945 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 183925449 1250 183924199 183924217
    0x150a0c03030216212d1805030304180c03060b0901080a090212010218061905070c09090c080f010b03190507030209010807062c090c0d05010f1703160206 67
    0x920550b42541d4601c2040c02200e13909840001c01c0d002103d070702035000741c8403258005145d8000003030f8200100d600580380b080c1c50892420f01c509842407200160000d6000009041b000e4100da40c1c403a100c01d110792461030900104900c00303003000300031030010380319006120480719000d07032040c01c2c004074500644003442c0003490402c001e0b0b6200e16080150381c500401515040d450800140d41d8900031000d03e0f00d10100361100c50003540e00300140035081509540d845451100c501c2c01545644091911132a040c1561344032041c124100012803081c006d05248200c1203d807100102e86661810354042030070303949410b08040e0700d80c21101d809040f0a03050400084403910510513944441c1c0c07641d0010710f04c214281c001040d01e80c041c01c028040325410403000da40b02e402031024482c1a6050b0311401c9008810580c8281c0075401501c081250b180d84541554000d80c0601e2060250b981c40c1c9180f4503400109100f252104000d904014404007004800c0300c0501585808418502415409101c0294090141 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 183926699 1250 183925449 183925477
    0x3020906030a0609111905090604051b030106120506011701090e010f0f0b030d0c0c260d080f01090917030c13090603021306060e0409060e0a03020705150a0c030302 72
    0xea1000524113101e52811184140715064203035a244c004d0010500d11040d401521450780a014011690b895030b803694807071002c4401103690b03034a000510340c40940f180714500d5181004800414420f0300488a01080c9540c1442088242c1e2040d004551280f10359545071800c124180041c401e000040d00046082c030b02e020008101d144190304442e0860301c0c90b070206460301f5a03d0070721108c0d91a05002c0c03503071101c040c0c0c9011503500840e40ca4246d09610389205d1807a10119003984600702144504503407104500030815a480d039149080082c1c007981044440a0718000400000304000d50144aa40d0309560000049101c44100b815003916560020f4140c80003070000b48a8203035a8849009410080d101000c4003023081440c61050140310710000c04010036241c00c000b03083c01f00980c0840c02640c42801290080358480d22414214010b0a0060594103039000b54402c240034136400141240444900f59141403000030303030403910340780c0340901c000c0e1070000b0b90758000c1080801c1c42a000307011115802c8403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 183927949 1250 183926699 183926713
    0x61003090201091d0a060503210306040b2e08090c2803080c060105060f0a08070c021f081608010605030727030302011406010906050f12010b070507060203130302090603 74
    0x40ca013034405034030f5000c40048042c240b080000e40798607030141c40000c2005a0052041001c0311500d0b03407400c04074400b42d1900003000b100142003641d413600403450207030001d410006455001c4007040c00c1e000c408203040d6607040d011005000704902c51202c451040820342e025000402c0c4400c20000d0707041c0704600e074500c82407503039019000e5611081d0510000314450085280d0311030001c104241001416440580b0450b428440002014140000c460440d08980788c0301000e0358606000355107011805a02070b4002014046000c0400b1000c400e10b140036130707940c0b1201e42513a14403804407901942d010032040001d40c070b280104015806140074540007a6036003441c2d000c261242c80f040384207020602d00c001c042d130701c008c5081040c1602886000240718200441100e90b00e02500041c24450b079600c40c0f801080b400080e080c2641c03458500341d03400d0302c45d12036842c4240e5a40f400741c0409a0020a003d803002e005450000420b940000112118861000d0512300b80c0341c6542c0030402010b0004040300e405000f290 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 183929199 1250 183927949 183927959
    0x305040803030c0405090709030b060409020414040506071407420915022115030609010603020a0b071221050a06031104020406080103060c0c1a09060c0306100309020109 74
    0x84059482a0003d100c916255460201040406440540000705000c1e0b001410b1021481401003d50700107000e41c0d0200d90303020244003080040200301c190090074102d10060000f000390103c0c10901032140c6542e061800c014243c40c00e0101d00c03900700700818140300203c058101040d40a03803603600940724100100b5220f186c0011425001400b0b000340105540c45c40400f0400860000e520310803480e0040843c1482040203030560681d121700d104102042001d000a075100b030660300d4115107480c0250588240e800c1c8a14110b003c1d10007400300303d11036014001c000c06c000d0040d80941c1d20b210b03041080d4180e203884142c0f06841d110607140100c03030109074407148407800d84036602409004000000000407068a1410709080c08c1552802c007611950040004004441e402904039055a0f00113000150000300b100d002d540800482d20000d00c4181c07052101050241000701042c801c5005000307695865466444061085c84119030759540300729103600f64158140f10780d004142c0b02d481810210140361710380d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 183930449 1250 183929199 183929203
    0x509063004030c060606030626030f07210f020d03090218040b1006140d0216170a030f0204050d082a03070611030615030a02040b041401020d080402061603050408 71
    0x40300c1c26400314050300d50020802256114010040515107020003055007000d800d0781d881c600148140b038083c0180d40510190715001e00480d450351f14511042030780c0d0101842c103003000c00c0880c4d6003815603510111000401501034907032a00320001c20343c003400340d981c16500c0560090084c074806982241c450149148a803400701d002c030340194000c4006107030764035005001000140547d0404420880018072400d441055902514440d08031400050384900505564880842c2c03d11300142c0002944440104040700100c02021100d820340c0e0305005c035a51601225007648a030b03216444c1c01c016041e4680c4089030b82c040180014220502c10748035044136005058000032407541089005410000c0d00000b004024440c0c4810303001e00c0d00074641140b4044001501718414859404904180000090310444155040302d010b08030380d4a5441d125600e412801400c1110301c00d000c1e015204030084d09030224040c03e41e0707900c5a0381c018416450a804480181880c00d00ea000c06c0b03007440400c0c040401c0d84141 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 183931699 1250 183930449 183930451
    0x305041d040b071701210219051e10030c05270319050c040506010c120807030b0f0d02010302090f030f060403090f081b0109050d0b0603060705090630 66
    0xc0425800c1040c1032600b420700320454040c16034020300602c203800202c00c1c21502c0d00d05045a86000380c81c03d10a4468140400e081c80485000350b204540090307921320a4080e05044c41035030000e40d43c0d0340e10000ea902d100c0c1d61182103200802e41c46185040410701c0d16210f6000101d0008551605a04001c009040c050408120a0a400324401071440012160408000001c064000540c010003510555100d040d120007940a6a900451b218000500315034000c105260341c455121035004c000e51450031008000300b006550080000b4241054a0803901d0f00c0e21007100410ba00070f02c050521501c6600545c0294425403041c1d400805110610100c0c1e501480781010b18064030b00600300368030301460011700c1182150412064522100300621004100040b00540100b40b580310301d81f580c1c4d0000041c0d82591a9902281d40040310070149001c208030668a81e001d0f030815400c5802540315244195071070f0003448079141d004003082c441c5548164024030026907003907241d124440b40d24900c0d1044919480c2c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 183932949 1250 183931699 183931739
    0x30822050d050a050c040c050910050c0304060e0306060109060215150312091009080d1b0602040915090c0c0f11060f12060f060306010f1e020d0e0414040f030504 71
    0x81100782600307100003441703001001103080b50200501080464040e202c4c0c0144542c20b40100c41c0811403c042c40c2c080c90413101d150001200312521241d8401c0c00908019624104a00038010b281c0824410b50041e00c11100761120f68001c0d009041009451946030b40006002101031a07803a4070103400c40d1018445221030700b83c0e146280d40e603003003640103000d017858140745600c08028410608001040000c511071501c2c0420b440d03d00300c40b100e40079840c41010311441000e0807040c400500054030160301c0e4843c1103011a640d5185004030b5a680004044402404c00c54022070214414103002a01100b60001c0703040c03090303c4280c0c02c9080300000c00c030b05070024150000900c000254054100b141d0781d0034194007079400c50301c0c03401112103032011030b126010103840c03135050180c0d040c10071030300c5400b4883c000a040e4542a4250703418442000080d5140e4170100c0f05c2000c50003c0416000c02d05043c0030300c0070391215140350315049444966600d0401050440c05900b04070301400f000c03e98214441a1810380e1b1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 183934199 1250 183932949 183932953
    0x207051e0103150e010303080405120a1e140a0e030f0601030605060909010903020d030e010e12270f0d0f080409060509090309150c0a0f050a1407030822050d05 70
    0x20458100150450b03280645803e1007541541e4108003042c090f0700395070f055951500c0c011900d038403686446880c06038040c0d41d54400403808503600d0b440e590301a4202c8011490400384c010b4001a4910a4900308440b050020b440903080046020041c064500b40c045440040e040b501d1825500c01003c0c00d00b0f800381c00885809490b4030500501c4c0c54041d01513600030060000800c440042030b03502a5a81c2a80700c94041419201c010080a5010a6100c10980601403055514030711103107074003880c50750181c203002a84003481307601c00e03007410251107400f41d840001901040070400000100200078640c00701c203c0704140703101104000070300080c01900007005070803000318407a0300309010081c01c3c14004119031341030751050200c1082740d6502044101a08003895555540d490800d0346241441105003010340401250301e90f180400030000b80b0206a07134061000080d00d01e0002e18aa52142454803001c0c12806050040100400d84005041c14542c02ca94000704103d584a011802e0980f00001c00e91700e035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 183935449 1250 183934199 183934249
    0x10504031b09110c0d0305100b280e030a11220c1715090405010f020406020a05070806010501080a0c030f2f032e0314030316180b0901020705 62
    0x4460b81c0100803000c40f001c2080c1e4249132403841101e50342c40000c54548101921080172410007984950404050f00304443c070607035110b608031404480b0905804607804c3e030090310341103050014464800c02005060060190034224481c0e105c0f40c003150000c00d400c55202c40314840954050303070302500344000c440b4402008600303440000800361403400c0303c19802802034022000c00ca10040044403102e012507003141c0480c001e8881e420070314014503440440c4425113100040c007003003940d000a00324070002d11400881e0001516881c000392600004c1c45540c1c08142e030140402c0d001001500000034000c414900002c140354940c58503401da408031440c805608034a81c49440c144200701a20481300303040f4411080c61418421828901095100366004450450604611010f801740140000868010f030303910a610310069071481d1a54401d0b44c03040b404030b44110400701400c1c05404010302c1c0c0c00e54002a140d10394607140b51200107074030819061307045001b00e210100c3c084d610191404e0003082c0307123100c0f8000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 183936699 1250 183935449 183935459
    0x5010e09190b0c030a090c080a1401021305010f0c050613120e0310090c030c0b190206010b1b0c0a0b1804050408070f0305040306050405101d070311010504031b 70
    0x602018072400409480c0360040007002c5948180401c1d00120240c400d9540c035541d0784000f00c002c00010800400358404444001004400020008489401103500c5501c401034420f04500300e101c0c044941806905c00c860401142d800350b040d6440b034808600342409501d0700c0f90b60f40360500c04220341a00c05401c0110810040c480482481d256204482c1072403c05480e1290002e41c0e1000208070892603d40c9400102d4100946001d143e8002c591101c0f02400d490749800c100c0999422100c214240c40d84400750034808a072001407402c1c100c40503800003501d840d06101c581c8180c0c6450496203041403140c1d039045030140e10b400b02646d000b801500121620348101480c42c950849000b903c49208600303105c144408141c004088450195210342108a41d805610b0250750300d01072a400034042034a0902008203200011650145c4052061800c02c80c030084400e02009940320625a0703001c50b8004134040c000280c944502050000c4141406810143e5175a10340792080c88112101c183da516140302000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 183937949 1250 183936699 183936703
    0x703210c03080f09070e010b030117030f1818040b0601030b220c09120c0e0109090f12030e010905030403020415050303031504020405040e010c14130302060903010f05010e09 76
    0x44051403031400161128807034400a214240282050070703002034600118080c0b40302004a00000d21640d010501150394911120206800910841d4030381002421b40d414500d8001c01216184044410b540741004110100c1c80c1c416030320105800d400149800080d8450400341c042035104510480e03070080b43e85461400141503c1c003200343c6d1030060413084036241000ca841042a01c0c0300710306950024843c2c0b5411411202400b144d441030454603034402600080c48148100d81e0280c805064041c40d01da6685d140320012205008800740c801103110b03c0420003e042002101f070103440c1c61402207001307400300540c5400c543c0708007402c88403079000041c1013086040c070703018640b03166001d010503401c1c40380790401103038681c80000d02c104c0b500c0701031032078a415940e15907058038094040a001001103040038800d0b540201b061107180070104044490014000d42ca000032165103491402c100306005182d642400401c0d0082d4500940c19521585000413588081c841c1e107000b4085a42510503504212410034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 183939199 1250 183937949 183938003
    0xd08070f140601050a0501030923030408060708012303010e07090b130b06030f180a03030f1b14070204020d0e070e0106020a0b0f040809030d050d0f140601030c110703 73
    0x4050b0819401040f03540e0718400e42600302c44007800c0100d007900e411316050180c100001c40701e00d050074003c40708a0000400101520075a0b001000300e5219131501d44040d07130400024032170810175000c02c80d048000345d40110640d0aa240010b00007142c60408640c0742c0f802c1005a40003210b641d541c2d54004019464000800c62407002424403c00002c3c00c100f010134010310005000e4815a00a0320200d03211320001c05a44043d6600300c400d40d0040c5c451494010301400513145010341490410b0040c07141d1480f030300c80c024130360301c2251110301c44140c002d0f6500d07000f6040094140d80c41a824050610703010031900408915240c1d150151030080d0820300b015141210603000340341158400c055641c00903204407200303500f2400e10507010700c5035034503450084080d00c502d400d9282c043c02100b0400301c000ea08400a8000c00888410512101c2c0451002a085581103e014091003041c480400c003a540139510100304c0a8061903c84d40007102181c201d40350041981c01140c8140d417021401e078600b01c600d4111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 183940449 1250 183939199 183939233
    0x1060e011701030b01030b1801020c100506040509070e0a0209031002070c0b0304080f030a0603020612060906030a02030a0b0601090b0f030f060402030114011d030d02071404020403031d0d08070f 85
    0x38100a504641380c007002e4400c1400001c0004001c0c40200c0c0403651403000750b1002c0d0803d480259500c50341d58130707003580b1010003812400d1201e003801c0c0450601c2ca000c4c0111481062110000c20141e89010300074000408041c00c1c0c4440e856007000101c903281c030103000118403007500c2503000d079841450745403041c03040480342e0141103542014000d020004a4140031190050140c00c401c036143d0719145280c6008000d6903000a511a000107078000d080d040c7c500140d03200d41c40854401c01c40e0307a2800c0030701da19042189402541a00040d5448000903080060181c21402c185040114035031544007500781c40c0e0050355030303155076030300481007201454000310034980c000000d0300c09604551500620744c207040c200d000c2e000c6c1072024018811040f620800a42d80003484e000b02190021800b1110180d100e02c907a0142d07c0e50100b640c09050000e0516000310750440340e15aaa84d4200e290481002c0305400900100b594418501c0030140040768149003d4181180107103035000482c8824901102d4904030040f130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 183941699 1250 183940449 183940487
    0x3106060c050f0d0c0f0201090b040923090c0105211e071e030e0a02060d0209010e0609091b07050a06020c0d02070506040b09010302040b030c03041208040b01170a050601060e01 77
    0x2100f40309941c085502d9016560010948030036060a20060361559600d8120301f100c464041400942e0021f2500056840d0203160404591000f481010b40106001168040c1d01e5a0100c04210441e5104200a10444090341d0750000d0360040450300c0c1c6180318050328150b1080e085590703d80380044011400540100031420300d0503090240100c0b50785031445080804040c15600c070b00a6041c00030074000703c240c2980c0101919a60001490380000130b421404507640041c030040c0c9150028100007003210307150340004050940d00d644003406610072030a4001e40140301e1b01d0034041a00043e8081094140e450320400002d80c4541080c504546082d420507601d004640c060384c4101300c6500d50208507025119144202d82d600c2c819040180d0107403145521002d1040000802c020016080401541c0190b2040c410f449a0080041c4211060081030360090300300b0b10070b000104075191208520600f51a107200c1070700c6c055556526941c0c00d0810985c044004150041081c190720340c0d1010020346802e1403011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 183942949 1250 183941699 183941713
    0x50d0206040f02121905030c0106140a030f26070605060108060a06030203070521090123060f0d06020703080603070603061d0403050c030d090309050d023106060c050f 73
    0x1111600d00103104400703800380130715a0f20380c0310345007090040c59010b00d0028418135070380550303280c000e40d13a0380300c9100d8401c2540381503004201d00c01040700c203940d07404008104804071819501ca91102250300c9804441c001c00020145800c0b0714020304844580914414280c1c0398006070070203a0a4a000510440c101301d134440404c041595a0407002d400d0340c0880c0307001602c0760b46120040d81c06110f0074520240c0b074000510301c04400d424000c0381c3e80c071440a0300020320184080600c9501120120702d4000000c859410000e0038504201c2c44003008500010511114003410745c9944040303900544045e17000865100170803100707040070042c1c04014105480c00b000f00b0b5140c20142ea5062500e01700342445016034201040505116100b80e406011510381500c4d503d0741d00b66480e4009003c000402c4001c25605040005e081c502144940f820680142c280b5440c180f00c002425061046410381900d0321a08a20045102d10b840c86440082c008644a20302c41c0c1c0b02908000c1c1c0303010800c0058003203983c0220 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 183944199 1250 183942949 183942953
    0xb07170a02030a0807030b0d080c0106060203130b0304020109091a010306050102191106041505040f09090305040b03130c06020304080105090a021f02010e0313030218060f0f06040e0112050d020604 86
    0x11144000f846140400b03407910b40c0d00040300980300d6090607540c04424021102d050103070542c010440c542c10b18008001c02c4ea6203070303000d81e20713401640c0042c86500c018040c2008201d0000c0d004560040c4145003694910b9240c0e00604111a4404802c4805685280b840d40d4507503018850003000e00b10900007044140105c11600e0001d0310903d00003803180d928100d0181c4261583c01c184d4002d8001e2200781c9006504c4003000030480c0d04030b48942070499128040000300c41c3c40c0b9109516000b40c166907030514060825404240c4e5500c003401c18070790349a0003030700300d004500b00c0c0b0100d4020340000d41c0038541d100d00d071502040c2521300140500c0c1880d00085030400043c0c1d01c01c0c0b0344c080800b940501900480000f07541c02c4e4014070144c1d489a050703000018903002a8508039241606580c0708550104901300146c440d0140414110b03803044d045181d00041811600c0c0c041082c4c0030f074440c0106000e1401e42c0f141020383c0340c1c140a920101c0c801d9044d540365000c103c024403001490041601c02021585415 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 183945449 1250 183944199 183944203
    0x13050f06060a0b0901050706051503211209030c0a050102090a0512030307201005060909030a0e091f090c0e030316080d060306150f0602070b09100e0a0b07170a02 71
    0x28490fa280c0440c0020707031045140d001da81506c030155040b030820041850862014823050442c000054405d003d160754100ca8030349420081841800114480c0742001244001d02a0a075000303045000c40d880288100c40008404102039828a031040c8000340c0ca4944c6d00c1e080c044088140d400c8030741304281c00030004209030380010a272580b000e05858440d12100027a00005840c9040c4c0300c0c080514081d440480c511460340c3d400180c0565810748200741e05a48a1882c40d440c6d00503c0c010b0800100270070841710030f030300d880f04400b6001001504030403103200ea06122074a03c2a80c56104550584d120381c40b01209607000703100050300d4039094003d10f01d4210b40403000030110b144410700900c03206010440d8900d51902d58443d1015581c0030303604000d004007a82c84882855540e1140c0041d8042c1190b002c078803644003040721400c890488032118181254001008280f4554200300340400c6031385001d031000340e900c140d0200024680c400c0250340c0d4039400d0900310322101609044003041101084481d03980344e80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 183946699 1250 183945449 183945469
    0x30c0c020609010306030b161706090402010807021903020c030d0302092b0609060f050702030a090e06062505010b01020c0d20030d0f03060f080c12030f0313050f0606 73
    0x204a62080e0b441280b8001a8010302c91604050030b003580f000f0402441c3d140041c07206440d0156910b40e07641040211001640c003403821121980c010100b1004100194069040103810080c0c60055030301800704003100c2180b219000c8001d80060303000071b10642e140e08051043c040a904245020345c076056601011031315a41c42d181c2c0ea500e4030081201c0c89a03840e001c48a01c6a04590b01500901c441425401c3c0f55028201d40c0001044491503d000705000900020440d0948205500c80d509000d1615070100301c07101c0c0007003489800c00410881d40c9078a011004010b5040e11034990750182e05d25141c100b130360843d0281c2c4100d03070543d8081503ca00b507c0e42c4003010414001c0d840300c201c81803105000015000000c0d4010365070380502c24146211181d64020f010b07000c98000c00d58040110315030320461441d11400301d01c602001500300c04035080c1142082c00c080380800704c48204492609026008408091380704413130105c21259841420002c021003800300b021400c0d501802096141403403000070f0840e0718 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 183947949 1250 183946699 183946703
    0xb0a061e0b070b0c0706020f0705060f2401020a060606020d121109130e0d051b0c130209060c0f060103030f17071b0501060e04111e060702010c02090901061401030c0c 73
    0x660f40001080d5036205030850b400c0650102c0150b44036a141500d01e0365542080c0c00480c1c8600800c4002241c10303844a18252185101c0a032030fa410f08080c000281d0382141c4a60428114020010f0140c0032072124014100103102c43d41c0203001540c86040b0050010344003100710240b190505240c0304803c20300c802501d4122100701c0c3c40c000c55103882d0811500070102c0c4140d05503180034000c40b1041040d008400342211484071085041035001c036510b000d46030310060b00070b103030710a6074030381c217030068504640c090008040c018056510740070030850f400d450110030701c1c020000e83c0d11505c0103008141d40120344c24240340940c20424182c480c0d0000c0c058050000034100400c100b0002c2000c100802d4541580000c1508031008000c03803500c0f4032009074441000c8805a030f12101e1054901150705040090007911000c0411b10301041c1e5040c0100211a449108244e040100700c91190300540d131144c0c103c03401503074080c0000030043d2038442c24004840c80c48071180e050601e1316200102081d0450042c9031116 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 183949199 1250 183947949 183947963
    0x706050705070e101d07020606010504030c1208071401050601030f14040f032a020a050306070c061107021c061a01020c090405031902030406090506090d060203130b0a061e0b07 77
    0x95139000d400040ca100da503208007070318840b00385882d05040a4440c09070050295500399802940d0f004015a250300c40c0f40b00052103840181820001084444c01548885101740d0070079141c0349503625180d1480005c061740c1011655510b05004480da054032503e085040ca06400b4001c09103000054109244000e0015003680b1803101e011082503c070f001400c01d14110840d80a0800400c40292520207608640890141e584020042414134000030502e10800c0107690380f44030481140c0c7c1e040c001e0020482070154019081c04a440107a40c3c0403c00d01114000b103d240c4207181380c904250058807030181001c0e10748034038882d00d1002039a006c42d03100c40d00c030401c0d075034822103481d5481c08600d144204401f80c94400300ca018100c003601c0d0301100810482c2c0160341c505030400d89440400405120300c04610b98803e2014141400040b91074010f13507880f250300169003c46c160140c96440c0441c108640800312a40c1d203000501c402d0101449099101000520702183c0c1414411000a144140c00b006842c0c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 183950449 1250 183949199 183949201
    0x501030b0606090114041412030c03030c0c0a060c030c1d091303050c06040305040303021b060a0c1103120c1219031d0d03140106030203090c060f070602030c030601020706050705070e 80
    0x41d90181062000b2181544510782e0340e160303161f0a43c2c0e0b6a60442030541d2240700c07544030a0011790400015587c0310204100903610710784500320b101705030b03501240700d0907800c0c0114114603002c81d806110750105440130340c0300807410f0100c2c95001820f003903444d50f000c3c2c403003220b0b0400c0d24200d0302c4040b4201c1e03000c0c9079025685440c0c4100d00301550740c1d004241100119210321400c21040580c4007002c0c0c0220780c825001c85d011031300c0385954000c0c0a6410103201d0b030000000d01041049a114006980030395000c1d00340341007904130140100703081c2072001d03d80307180c05540010300290b000d804000d1407180500405c030341414107070004566148a082c01040b03400f0540c41d411481c502000000c1d507001d000012404841d0807417000d05015019101040e03002e900c1c113800d2000064201d00034003c8a200d0002030000d40b100031645010002d054011072410301150100388010400161248011401411204480c039260f140c01170009192031003540201c020010306004c04000150005202c1c0c0a480f00f0703454804007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 183951699 1250 183950449 183950467
    0x90f060b0a09020403050a0209070c0f0206070303090b130c120305040b0d150306050a14040308061e0a090e010506030d090e070e0402070f20030304090509070305030a05120a0501030b0606 82
    0x2180c290000030b801440020b0002c01c01c0000070703110030705070310a030b414400a955298054460161810b005003800e003074620030000500e880401006494424117000411b0403441c1c59500c0104800c8070701500b5002c10900e01c40902080e11686801040d01100c0366212401e1980c00130030740e020301e1048880c0e03a1000300b0345002c1d0810540201c040c040c40c00b10551002c40d0389041180c09460107582c8100454900900350a042315030b0300b0200e00c500d8168890310202d4a41310140000c120350b0000509182c0a20700350200316660703030324101006150340f41c0e0101b8080c0b0b85103041800c5071806001d0303510990080307001d890340942241c44070f401c85810101d04513155861550945030441da14407450707400383c800180b8a080001c0100032a10140c0110720406110b14294071103454907100f107401c560b056000b88420804140705070030140d0302400c0b59095440c180d50302d0b0340e10392968115039018000f16901164400b0140c411401c5141d10565200c014859545103407600f441e102c5000c1c10060095000050300c1e64 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 183952949 1250 183951699 183951709
    0x31e090402160308040605010509040804330504051807020601030f080705030406170a0c0503130615030c031a07090e1f03050309180f0a1509150e0703090f060b 70
    0x4046400b0003440d40aa4405150081052004890448100e072500c400403501e810b00c0096075100e5075003c1e0040340391501308001c02807076100d0000c1070381c0300714440b1800804d0303042401121142039059894460300c660401040020150140d0503001042084000b008403090b40062101c2c112a041303503200803410040d003480200b034480c400c0050a6440700041c005250340d841801c4400314009004503000c0781d20350300d1211095602d600030301b000090081c00130402494008608140591155400141800180030500c0c0d16183d00c0e841039400d002d032411f0070401c2c0311114040902c1048110a003028900e000f04010744076a01070302076a00c02d07914003c00582010b13044914035621480500780c0c5c445040d0b8038980540c0ea0f074480380380580103482c112244a04164680c018a00861000c0c078910805da0343c50301204000d015407000c8900c460214400000ca00d942d0340b1072103212500802502440f2410414a24801103025006e402098685603000012032100420b4000b9036a018078003169100c42c500002c2c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 183954199 1250 183952949 183952957
    0x1e0907090306061e050306040f110310090609020a0f0602070303050f0c010e070801150303120f02040506030907061d030604032010090c0e01051503090a1e05070503031e090402 77
    0x2e1501e458100007059648060180b039044032250b4580218040d1140c00b0316448000503180240b0036452030440d040010004a0585503440000c0c044406000201a001050300e2031003070143c0388690382d24120341c1507003001102540500504180c0701985480c01c0720095880c80e05d48005000c224010a00099040c05d0001307c1d0440c000d01c000034814803854100d240e0301c4408038403500361558030300420b81700e81d416220b400808403505620381001034940710512a01404011000b06e070a240c1c02c0001065555451000e18000c84403030340106115070030202d0241900251008500940c0b01700309218505603800560740c0c1e4071540c503140c001104959120b117000c4220141081c0206405411007130418041b03140d01980ca058080d1a1095090341d072207400e000c4100e000c0c01030740d03040201da0034660704000034240216040700c0d40d042100d03504038031520b0342c06c200a040040c69002d04145c0411000f8030101f002800040d18003100510314107100746d0710f205000c00185840003840c0a011800b221544d4940c0c4c199 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 183955449 1250 183954199 183954203
    0x303040f02030307020d03110d0f0504090b0a030f031734020a080d091703040206070201050711180a0c0e09070e0a090c080910060302010203030c03041e050705010e1e09070903 77
    0x6c218410a2460003421030841c01006e00044e2003200500f1004034130503032405440c1002600c0300b62409041c00c003c0748c040c150842e000781d00040c5030700000000034190001544c0c010f00a50391031020b100307070900e1103035122009030130801c1880110f0403040461103481d4281c2c05a40624865445071400350b841039040c5075500c0406440c85402280d82210f50a050304401c00c1c4038804d2520712010000d845040c41540001d42e0040c1d0400c000344803060055004d170006005050203070b180601c1405ca4040003a4500801c180c0070300d118100c86041c080c1d0694580540d52103c000d40c1009100c0340c10020108a00d0f0500a0886e030410403d418801c0c1d158441001000241035046028004241d800c0e1000d06404000e8134944003e01c02e100015000e44001d101f40000e4030381c140d018528503250341d07003d4101900040e00039a004c0495800c1c54108064056404298511400140c00f52600d0140058000c00341c0302017150080e20600d401c410741d4a071a10404100b540115098907507900d502c00120b65044540c2c00c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 183956699 1250 183955449 183955459
    0x315030607020c0f04050f0703020c071e0303030c0302030402130c03020c030f090f01080702101a1e010909020f0405061e04090b030c100f0e240301260303040f0203030702 75
    0x24007000c268042045400c2010540c2c01e075008000c0c42c01400100c07041126280380d4500780401045145109400501d180c02030724007240c0006450348901d003004908006500d4807002c07200002c00402d07405008807800300c0107030700f030450035850180c0105403c40620510141020355400c00b035640c02d406941500c1c440c9040e18102d0303032030f4000094003006644c005100345c4e2141101c9002035640e5032003400342c644619001d030701078000340c18450250b00241045001c0403505620b5880003910070740b1180215042c551000480e41e41078015940058842d203565049411102e004000382c1d0314180d4258211411600c00b6079150703650781c0c2400d010045142d070700c410124400d5800280000d18901c01c0c0c02100b102e001c203c3c16105808010402c00841d40345402c606008212426980c42d9541d000e11180b000200002d42200304070745005544104008540c2540304211101100500c142c02c622030080c0e03c090281100d4001d0300c05410310503903076408000c000030641610040b44804549062055030007aa6011300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 183957949 1250 183956699 183956701
    0x10110c010216110603041e0c17030a1701120246080c0108010620060c1b010207080403020d032303040308060301090b01050607020109170f160b0a0503150306 69
    0x190020382c031001403000e403446082c8951142032071410904481c01a40d000700a0050030742e8000c24480f070a2a800b0068900d06040980001c006200a803003c0482801c030703001e103545418010010300741101d0415294101421080144000c1800982554407150122081904941502c8003032140e054038170800d200314a40108405000880c2c08800351032140110710300e02c1480d440700c075155519218040d12500103481440100300d40380c000e4515840c49050711a0000a0204800030103240080959000c4a104c00c00200352800c100094a460300080e000d400951508205444185841c02280000703840b40110ba100c880c10275006d02640034031a0003003030304919240c800c2000c8022681080700d05070302003901da0740003814502c2d041c81065081a80040300183c42e0b401c05081c40403c2e000580b04905111035181e020580c044201c508860303806494008201080900410a00302802d9810380e50550b9203141c0c09118420000c0c06aa0641c8402d2402c0d5450b56240a69518100300364100c003a0980a40b0f4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 183959199 1250 183957949 183957967
    0x706110708070f03140307080301050d0206070b04030207090b030c03060406151d04110118090e0f0a0f0218160f050f0a021011040501020604150b030f03130603060810110c0102 77
    0x11811000303d1380181c01d031001c505c0b00c83c1c1c0360503103034400c214008100a03030400c0103120500e48500038449031800640550f040c0301c1c1ca80c0d102c0b00795020940d8164051390044004020f035400351700600d45005030a5010f0b103a01d00d26400030965498002d031000b803040d51941142c8060b001d0401e10840144111000111310600c03c0040c6841401c0548054604400e10360040c05103501506040c030100b0405200c40035224900819580280a017079900d83c05030060468015404108220b0840068010b1035606c00561440c13042064034011613900e02c44000311042004010700116191040c10382846c2010854030016900455280c807070080c1c0300c0083e500105d540f90556a001801214990850328100801a00340b4010b8260380038030300c140ca0040c0e00440020740080c62180c61050b00e4a000b044c045502448600002d003002c1c80c41d00258060742c0041405910058561840f01c01442907003030401c4280e00b051051a214060700c0b140780012500c421881c8031480740b140480c0c403002c032400700840d00e6040320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 183960449 1250 183959199 183959219
    0x130b041803050a02061501120b220b090603060f04140304030b0f0f0106030605060414060c010c0c030314010501171308040f17010c080106080903040b0a080621070611070807 76
    0x100743e824010300c90100003800350300c4440c0d070004c1c010310f0585504a0501000c00e40c1c20190000f42d10140d08050590000c1f680001058181d810b48280f110000c00d844816005100d4176074000ae207528401e9008a0600100d034000f1281e00d500070f174022400120314a80d80e0100d528500c581d50000b800c20711070b001002091103231003a556001d4100c0d40c00c2c41c842d59030381d9a4100e05640407809421740c001ca0070041003000c219114240c0c0141c583c0030b4246810515503119032801c43d0b200d0000c442c04502040c480a00309a85803180310a2035045c1d6410342407550400e00000e01c80303410303d034845105008200110710054150820304d00740f29071100c013407580c0300d8841d4242c1c1d541485a1248a49400c03140e00a600c04c500c06010382034010101c0d81d84d1401d242c0c41c0c20402ca0780068041c0910f185400200f101041c03810101c0c0080502c1170054494140a060500a10110381e124030008050034060801100c81e21202080e1001103814600e03001540c036000a28a6040030007d50010041d840f40c032500107102d40007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 183961699 1250 183960449 183960457
    0x30307060e0f1515010909020c01020405100804080d051503060403090503071a0a0e010c1401020901080a14071101150816150905100908030a03090b010801060302130b04180305 77
    0x81c00305640582c000100c616541e81c3d088a00d41c0c400800038000210005000c0b5a143c00d040c4052520041d41942c0e051120300304d038008090308220340d40000c0d0511460401603084000b40c040c600c2c00d24003602d007d4451459500501000c1c00200c1e80311404150500e840c6020155080c100070107448070303401c0502d00940343c1c00c554400c0b280280102000080d8541003e041140302e0302558021601c1c1c032402d25801c40c0c01041c0c0d89042818408200555000b00ea0b458040a401000810005a88444040c0003400e03500004000c0310819040121940030600800c010941181d11810304003c0e00c1c080c0d00030707507014000c02d031800030a421714140001510384000600d502c201e0a80841c0c00c0c1e8887d11950780302c0d8036a15440200000c14000003040003141807c1c400c3c03941d0300900e46041c80090361075906440c21944014180c42c0084d480d1280c2034140902d100200d40100b401c10001c01045145502181c03160701e913080383c04502c41d030320148400a40c80e2500800b010f040d00700d0084140c902c00d480c0142c05504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 183962949 1250 183961699 183961721
    0xf0415080106080a08030103060506030304030b040b06040b0a08101505040c020a0b0a0c02070311040920010f0206060114030a02040503010e060a0c09030f24050703020406110d0801210203030706 85
    0xc207040b40081d8801002c0b0308500090780140101c0e00d1a800e6488040182c0703405403945815210030400040800c0001c0300860240b40300e101c2401e03480c14403108103c1039491044020b44108103164003004000c2c000590210034200f60040414549540740d4080048220b40e0b010940060174111601c8055a000c154041c5180c414102d40d000c7d6200d1700d582204490003000c220016a00c204414030100e03903202c0c2e804510301c00040000c0b4000c0c0d82951a044040644107140e0b921402c1c41c1601c440741d603000040784100c40702e988000c0425141c98400200450580d16502c400e80d40d00101041c00240b4a030100c45c00303020082c000303105030940d50802d1940e62801b03e030201d0a0350300c0c140f0503140c2c03030703108d42852021640c00032001c0401d003c1c152540700307030f0290401ea0711501c00e220910007600d0380b026000e054030074a096100162900c0c540003000d80344d60500000341e20a40c11a142082441e9080b21620b4150380580e050800481c2e0742c00100300088003940c202070746c144400b00302c081c00c1140580100703840f00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 183964199 1250 183962949 183962951
    0x130506121906050a0207020603061201110d0b0306181e0a1406010302240f0a03150e0115020708070b07020105120406020315010c030c0305160212390405060f04150801 73
    0x13603107403002003040f8011410000e501000800105605150a074040381c84c001405d00001a413903e660b00d88101079121400303681c070300ca4540d0089903e1740703014000e646d8090850980000c0100303e03d11110f885030340c80c582807510300740c989580301c0c1103007010800c801005600410070140c081c0b050203815a00d0300d0034801244030740c0c0c1c05610200448940020f1900c480700b0f00009504000c0e98840b80c1140b90400c00448042642d1403100000901c422002ca9005000c41481d192040d410600001288503000700c100095521100003046030080004d0024110741c0c0c6141d1494a0784800d00c012100340c07003215040f00b0789982c000300b440b040c441258003e40c0503a6149500769042520388e401980c0a686144020703010031820640140424052b81c014500c44400c0c80750001000030b25400140c9051894490500c943c3c40b034440101d42240008541070192501e0318190f0025001000c0b404604240d0680980601e48600208101e46c58a0108594042d0010f100f40000360340302e90304044074619481780c0c400c59 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 183965449 1250 183964199 183964201
    0x210912070e01120302030702010e0d060f090209090c1c020d0c080d0906030c052208070806040b01060e13020c03040e0103080a120204060e040908190f080705030613050612190605 78
    0x503c860300c0c4500300e6a941900998100040d035001580c240c009030f40c080760002c117400c03090302c00101c40784078014024142050018020000e80180315082000821101e00f0b80d0103001501890b0703440c070310318014040300311440182030280c91010683d00070030040010908103c6401c003041070b1902241480b00503025540301c9612542c0c4440450030b0340c032251290000714000300701c3c1051000448815016031903201801c40303202a0781d006514a8400f07654401e6802c3e42281042c80200031240c1000c50041140349000c09251014100082c80500d1122003854440e44c0001c0c6401088410b1042d90024140b40d008106c3c0c3e90780d02e040c801c10503817080044800013100307002859071181d054400d40d000d403422582c81c0d03000040c1035403d11001344500901552440c400707101a44601348040c008407a1101d090755a036082c451280c1d4007400c0c2840250410f0207006040c000c00130f0946038048245090110a40c022969840f4400442c0c44030505110440301401003116032800080c0400d2161100352041c90704203d2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 183966699 1250 183965449 183965459
    0x309120a1d032109030a080f090f06120106080910090305040303030c03050f0c0c0a0606030c08060108031c050a090f08041409040507090b13020c0601051e03210912070e01 75
    0x44002400f85584000d0414025800d4080d801d000382c204020040c08880200402e5102c0c4d842c0ca40043e441209a80c0300080c0b180102d0820341e111b00500081901d003541000006026800f820405000300010410100002015000104691403462400d51000c014040302c0b800c0003061a40070340800e501180c1802c001b052510b1003403203058841c07400c4083e261400e03160700303102c21415404030000b5842441a00c8400300800d8140c0324080c01917110328404003481c4d01d0001c00d41d003010310503807050401e500280198110394036000d4001341c0789104c134000020b965940c0b42d4032500508207070314050a180703a50404202003254200080040d0b501a202021000c080751003044040380e0102c9004140d078004107070030440c014040d000801090001031440350f40d15409a0280202e800122a954069002000401c81410b01641c041c1561150f819008914000c02e80800e80c0d4a100c40c0100710701a6007450040c2c2081c9004c020703150480700003001c0da004880100c0351a59a00c15500407452882c101d003000040c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 183967949 1250 183966699 183966703
    0x270b2106091503030c0f06060f09240411160c050a0b0403121b05160501030506010c02120106090f0b040b010503040c06140d0f0f050c04050f04020309120a1d03 70
    0x80318080080c00481d1503a294414018658401050b06406200c103001d101003800301031000000001a00000f840285400b20401c89904c00010f0514001d522040910805024100b40100504001e41c251007003101c400001c42c0007840001da071200300d80004140700409110680389481c40340d000c0d0025131303040d640310001c003d9043d68a2007218100c0780d0800041000a05030140c0440004c0300d81000c0d8002c5a03200001161904142c0b81141c0c00e811048820104629014004000d040280b0f42007140c0d2030901c0000c0e04012071010040c0c450080c14149285c034600c25004080176025456061203030000160105d0050144070990510450400d81404559449035044d02d216a0304120307034440380e52801d5170507202030803031180d107080309003040060800060031030050038092034452a000505c842c0510b00001290307005888648008010002041180da6403400c0c0d08100108890041e583c1c1c642001c0c2c0c601d00300d1604c0301c01a02d2000420b592407000c1d004111520210580d605220540b01110101070f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 183969199 1250 183967949 183967951
    0x207020a1a09090a0902030109080307020607020d0801141201060617010b0f1c111218010b03030a03020d20070203060a0209090f040f0f0602030601031a030c01270b21 73
    0x1e0515a082c042c00000303203002c14505030040840200022810481e4020900f56a802c04003604c0d1031500006010702d540d4100604d41d4428a24409000c21016482004080c0c0c00c06202c1c25114042c03c010f102e1a43e5204409225000151802004101c1d900e0340050042002150f600882006560002030325460040c125005100c82943d001c0c80c01c1104200c0388500140001401d025564811801c1141d502980c018021147c1040306800149050440581501c800103141d5482d40d06103012840103842c00000c0e41c01200340c81c01d0141c5c0714820000c244005207903500706146c07040c01c0d10b030755481e48403410002002170600036400e031007096542407815010380c408c081c04283c00c0358260000401d02c400d075072451074109105500718103080750301e600c1c0c480801c03230741034001d4500707507030001c2803040c150f03014031443d1711a40081d1700303036211004213000090b162200b1040040c1440088824054920300d6110507070f80d54081d5084080c4415207415000030f8030b0b00401103d170b023089101c0300c1d88034200384144465 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 183970449 1250 183969199 183969239
    0x6060503060d020405090f030c1501051e062214011116031205160b062b111c0b01050103060b0705061501050f04031a25080601091203030207020a 64
    0x2940703440342c0c59083c80000e01004020385aa8054402c0c5003991003401c3c002041c1c0d20a2a10040904083c001c40d01c070160041a40560703c142c1c003081c120484140362014800040d14100d44280d01c03060000c0700192072507210305030744c40c0c0ca9200d180003250704003211150307039903544082c0d036407071750100c03a074510503540c3c0b003007040000144154120300700005091801105c0c01140300c2d241a03418412101c15003008040d0344c1804960b00c80000c0b0820296003401c2010b58440708111021100c3c03020700c09800d450b0101c4120014146050b04160f2180b00d44500c1004981e0062120b00c071b00784040c080c24040b0f104442030040304d0000381428800100a406142a91078207030704880030300020307215074002c5015044500d50842c10301406214200c030050458016200441c041c6034000000c40d1b04279030b03401d0390110040c50200c8100c650360003140b034080c1d00d04c802c0d60314080d20f0a003600c07140c03160401a211080d1550000b5050a0089200340400d07500d034014048840c4243c5000e0042c9484440000b0040c5054100f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 183971699 1250 183970449 183970459
    0xd150e1021030e0901180c0311070212070308030f0901060f140405060103060906080706080c1323060d0608010c021f090201120213030218090c010804061b09090606050306 75
    0x80d41541c41d1030a003070040792007070902481882c02e410100710148400d074401c041c2c08011030030700340c801c0100e80500000540b203480c0400c0b02c080c590b080c54584d0700444802070301034000b0b24030a98080004000030400755070820310380c50700c0381740034103081304611400c4031410000c0d400d106000807040311201c00f134402c1e551002c4d110400b15889409100007484010016810036458040014031890540304107005081c3c1d500c00b8003401d500313000d8054500742d0041c2c0180c140c154108004081130309940440d9042d168034142d101c03100d20000300c0828000c605407400307a03848030001804101087c440d5010f54100c4035880000d011018181105a03295200d055844107100c1d40e207000501c209407150f2119043c544141440200390300310b0398181040343c12420070800c1c0407038500020b0003940303040720030484400001000d02940340303440090f0300d4031050740740c035000d06012401c0045010000c054000d080b00d0000700162140b00500c3e5400109043c01500c1025161880c040011654501c07980c00c40784a5500904 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 183972949 1250 183971699 183971729
    0x108010b0319060b0903070b070c051207030b07180b090108010605090a080715080c0403050c040504060e0307051f0606020309060f2203061103040f030e0103020d150e10 74
    0x24610400d580020100e400070121050840480030700c03403080802a0014510482d1600140700c14149042e1040c0c10045180e0300c24440c4a0004c2c40950980050b40d5040d11a5984450400a1140b0f4844d060b04004c02068442d800c004610740d000e04071006581c403000c4103c411a03612080800140f040c0c0d50454009142c8100611805004800410340c0c81c801404c00034500741e0741c0343c0381401c103440c0350400300862943d0740c4103540c41540900321035082102038054a107000c0c80c607a41d15035680700c0070141e00d00941e00c580014040c0482580010070f030400b41010b5130303a070350038501d0302c20b4841d02e106510841480791070010340860202442124240e42694005514150500b07040160507044410003022003401001082c4004d410500110000100040402801400c518254050350703414040203000001c24000c01012a80d0035100320f80e40e0340c042c100ba641c1c103114480124040d2280140402500d03052190251885d02c0e4070701d480080350003001a841c0311b51a460071030908014a84599604d0488a41c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 183974199 1250 183972949 183972959
    0x1050f1e060a080a030215060a0f03060e010b0402120f0903090109030303090510090302030301090b0402190e131a03010f0b010f080a060e010e010801200f1b010501090507090f05010801 81
    0x26824a03084840100500050b9540d940e4242c60f10220140c2200181c109502c04148001000301c0503030442002c4030b402c081c0078104003040d0724044c0035100140909844035420301c008002944001051400a8004e5503030b0031050503c800fa0140030354000158a0304c2c0c0e000500c0b00035022080c2d40300c55505940314020360786584c0303048002d4009444103403424003845041d5845415a4881c84028910139000380d80c41e50314147c0c000e0112031403111224003460040000c07032880c5003480415004801c0d00c0c01c0c8440101c01c542c0100f429811403607003003540d00e8905402c0c0e024100c1d03210411880342808034020702208a800c92824180e0710039200c40c5002c51240c004029000b4012202c0039408202018000f0308240d54141c100c0080320213034050040280d00c000144015a401e001c0c50002204202000c600b01c0340032080e0113041c2c802c9901001d2210000700f1041a404000f00034485181e41f4840240300c0355071141079960084c00140c03850004241403003030008501c151414480c0132500143c490071081c1e8130342 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 183975449 1250 183974199 183974251
    0x20d0903031b06110c0a14030f0730030f0b0a0503030a031d030a0c0b06011715010507060e03130e07140304020d020904030207030326160207030b040b060301050f 71
    0x303190480f6400d440b0640320b805004500c003e4040140010000c0540c0212428100301d40c2c19201c1001b52a908100a480b800c0c02044c07007100e030a1075014030122084042c1483e140d4100d0030440b10b060340c0200c0883c803086801d501d41c1006075402071140b410403c1c02207050402414101611030301da0940c105005907070000c1d01950000e0200d1500c0e801c81c0d2445940d000c10f460440d44080040c0e40802e41108185080c8503041010070352014083c20325000d00c03074a8142c0140e4010707008000c016900d00c054404003c5034410f00c140c5000a901010500040d1342d0b14140c903859802c820a5041071000c0c0e0000003506d000d28804060051764a81c68003020001e00032034502c2c0c164401001030742c1041400187c2e000503183c86509a204c2e50280d800741c8a01419032500500425074540512052045481d210441c2c0465030500c942003540c2809101360b50780c405902740d080841582c40a01051520000c00c0140001914854420841100200555541c401102c09004400d0315100a0110750fa100c0000482d81 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 183976699 1250 183975449 183975497
    0x140a03022a090705070c0b0408060115120518030c0f06071407150b10021c02010b1c050f071e0603020301181a13020a0914090609070e040c050a020d090303 68
    0x1490490304d4091207844440c01000d940e81f0041d0b00707000004041080041c20311449014049082403844080301c01d05004101c28114500c00c0c0700d06555101081255003ca4084041205e2030802d603901c680c440c404041d12551030401c82206401108001010b10340b042c0c400300000060a0801810b1980d5512442080320b40b08030500c15090340c400400002e035948480c1114561211f41c01001d0f42025010605200c410f03608456082da03041884c0c41d01c40d980d4903102e214501072071001d80615480c60b81884e900d410f8400390814070a000d15240803a880007503c941c040e50303828242800a105980d00320450881c40240b184280700c807100424610410f10a40004240840c500881500784080900040300755105a540d05445540040c0b0007908a4000400700d000380070200d8a80c14101c07034840800c4014500400080c41103407580005001c260107040c114032401c801030070400010041d0300c0b0203861f82e80412a1714003d880f507804400ca01c18414810401a242e05540300c1c0c940703641c0305001d40e098542c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 183977949 1250 183976699 183976711
    0x1605041a1008190216060f0504020604090b01050f04060206040b01080319030209040b10020105060a050f0f061315080601121a010e060403060906020d0b030d0822140a03022a09 77
    0x3e1020b410b620452030015221014100d400c03130502407050700e03040b030848014240380e62140d4108410000540d0300d030b40c15a81100d005d108045114460100100e0f0715100e01800d088121102082c040740203940000c00900c602e100d150043c0803641c03900c1c0c890341c0d6405032070b00800404e9407440305448c40700c0c440c1d0058070030858050300214000110000048010300b00c001b143c0c3c010f0795507200300003541c54003211960041c502614090805d4032150082040b50a00c5100c890140c0c10005070a9000b1640d8965100100180522030810a04118000309511001c0c0c450a0008001c90a20711017000544a261000b079601000c00114203030741c50040d00c80c84400700c2242d500000902000012800e03c4c017810348140c0c03148400591300c0040d0405802241c00001c0d506020341d129440d10620755400c2841180c11840019080620340c1c1c0c01c203405040d4450300700000f0443c85500c204041a40b20019a48030301e503201e40c09460302103440382020403c102e14401c02a858030082000601170f030600340d0080ea0814 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 183979199 1250 183977949 183977971
    0x5030f0c101b050d0219050a0209071808010c0f0e090714040f0f090e0706090915031703040203060f0c04030605041502040b0423010507080a030b031605041a1008 71
    0x8808078140780d0110600036010780d15074120420440f072481e414000700d806c0c0c603a0706601c1000c40342c1a0700c8862343d034212070600a000f0382d40f0700003041d1910b00402500a241c0c00c01462045000d88400b0301e18003801e042c2d80200b01250481c80807498850241120502c00305c00a01301c0d00c1a503448400803160b05001a5000f49203160405c030200e07600c1c080c207170305030094152007401c1814a40b400080404848004440c24070f10340100c08107101c41c561042c1e044088880c0362602144d0140450005040c1070001e074801400d0300f4503841018a00e202510103184154022000e884043d40d800010b0185800704885011141c1d104000520000d80c0c00d9101a8103d0300508c0c25540d216000705090f0100d03400f6411041002e00080303005c2000c0401c50700b030003880890f1401500301805141c80045d006000c2c540d8000c00c40000801d44c006814466440001c0f001e00043c100c8039201c03a00f40c6242d48840e140d0083c24043e40c1000b40071451941c03600c107400140e00025044101903020120102c070b02d0000940800120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 183980449 1250 183979199 183979217
    0x90f06010302030a0b120d08010f030506072a0c03020f0907050d0e0a0b0903030603060a020405060409020d0209030114010f06081b30070306050415051504030b010b09030705030f0c10 80
    0x581b2500d0f0f525030348085010003450711104000000c3c0807020141c3c0503101d581c01c0c6403c14400500b01003401900035106080501040810044480b410b000e0810003044407008002c03c1020b010414481c0c4007140d0081c1c5650403c25000d4044c04182c0780110ba213000411410040e41c01d0380a031590050764011854419544800b100c1c0e91041159503044e58034441c81d41c000700501c1054a000d020040e0004039001f070851619140501103400c40c010362107881030a95000c10500000c041a030101d50700403000600800402c0341a407898000e0410a0045000302682d05d040030501c54001d000760340c0541407003003401301100e20310030340c4401c181d00403403280c900d42c44002c000c1500c0400181540142d000d40c0c00303814980b8640b815000f8201c51282c1c1c0403c0c4140e043c030282c6c4042590244d40d040949d04150359200362904400c090354070038800c80d800244490200380001a41c1c841a802a140005044090b00e800e16594000c00da991000c0ca03003003c1c030742c0d040101100d00f0751134040b110038101601420080702c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 183981699 1250 183980449 183980471
    0x80601050c1009110d120c0311031209010b031b09060a0b0c060405061302010c020904030216090e0c311d010c020c060f0406050f070c030f11090f06010302030a 70
    0x105002c001002000d00e803504900020000c18800598220340280c0c0d02000102c100d86030041c10b2014141c01070140040c1d2840101454420351201451142c500100d0f82e4840300c40141e905840d80c2191314440395440c1191207040c600e0082a6034000040761081c0c10b890300c071598100507031a0f401821156002c07108207400a10340b000c05014104030008000944000c0ca010f0070030340c2c1403210083c42d02d2100d412034502c80c40144c1e0000030014409805440c1d404850359140340603460f020380c80c1411803016100740400030b844170450b0016201c0c00d0b802010382c5c00c520301c11418044941500c82c46040010044e28056403040b08800d10132030101030581d00403e064100c8541400d02500181d082c4d40981d45031081c9560158040050b11000c41c8161491450005e45107035444080c090390003003904000e0000390000c41c05038986c00b510311040e004007030491540d507030f0301d000f00c0d1001c1003900c11036207501c1102110055207040300d1a00d105d90120030640103103a4507480114020340c0001d00c15840660396a4070130036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 183982949 1250 183981699 183981703
    0x110303011a0d0207050a030810051906030207060f0e0f10020901050f0a02013206090408090d030201060807150206090a030e0d03020118240504020a03030c02031504060b010305010b1207080601050c 86
    0x10f6254001e0b08d506400341410021240d812000d03030009401007004100128119902100d00f100311002d902d00141c542c1c0b114034008000c2c0c00510201d600c81c0313092106000c40d8a4010440c070811a980404039034801040100b01030070b030301807100801d0116000b80a02ea101c41d504070010f2000c0a8148000904004100303414000784030350355100256103149651090f0920001d4000d140c02400c200e85c10400c46c5090b540c0c03012584981c0104074040e841055246007018000d4002c07801500c1c4410903600328030b4a0f4031a04003240b5410920741c0052142002142c80540702180038220300360581d48014110345034030248101e54042c14011001c41d0340e210080041c0c1c94810400e02c145520030000400c80d4900c14055510802503080342c01841c0340750005000040c0e850f954082c003200c1e450304118000a01a00002c0c0c10529102d0b814100b00c015007042000b000007641c451695140262401c20242e40c1b42c09104180740900289184803000060100302e42d18050708203160b10400501d081454444d00700344e064 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 183984199 1250 183982949 183982963
    0x50d0c0c0201030e060907052803050c010f09030804090c0519021506040b1806040603020907020f1c081801290901060e060a0e041506020607110303011a0d020705 71
    0x44002100304500d04110341e814010a0700001c41c40d80241100d08000502a80340d00d00c5100e05803150000c0121780c184107800f880414180b00109040c40b000c41e51703030700f025030711113415107015800501c00c850324151041c080d50030241540c0d00481642c0c02e00303003407440c81c600500e03200d081c02c4148082800104000d91180c02740c40110003180d405480c4052403400014909100904098462400e100a120382920781c440c1c00d00b524917026011100e16143e24010400030b1401d908040d42214000c820003030b41a400150b0b440400e400c0c441200d500c1440401c0d03107880303581c1c3c41845000045d18500072540001062419544003820a000060059803140300c1035040b1680c0766802c4d080705247d252031407030340c6840c517030a82c01003055081c804e020b00c6e04600016413501c01d08202038240040b01103c042c4a4403194410f50851b40140c6411500540300c000c0030359688070845405000410244405100754400f0094904850b100005064100c00402c1c0c1001e03640c00c968a00e00c80186d0a10440e004910108541 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 183985449 1250 183984199 183984221
    0x50c0a11070510050a080903090d15060803070b0414012307090b04120308010f050a0e07050904050f040b090d0f210204030303020406110102040b0306091f08070914010e040f03050d 79
    0x1c1e542c9085170034000d441d00300010101c2c0e0287e0410301005003141c4030a4840c0e0801941f00000d00490300d000201b070320062516410400040c400412000c040000881400d801280241d68500c10352009d5964079080c0c40200c44403944280842490003200301100c03400d907030440706ca800c100d045151101040e60498001d54004003400100000355000e060300a042d640c0500707004171005a80a0402c2c0c085801700d1242d100703110010000400042131244a181910a035a200420503c4a42402c5448008040c42501e0a841c543c1100001c41c0240c0e1000918031101089612190040390201c0819103402c9050194401040e00d079000810100c5031610091002e140310303443c0141c41c4c9041c00c200070550044d0581c02a003581c4100014080d015406090b00ea0211045900861941e03802151495010100000301d5400c60703180c401180c441d10104021f81a2000304004020000c54001002e0a940c4c0a10800c10002400c802060202c3d94032854510001c0c06414103500c0d2110380c1c0564001c80d824403802c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 183986699 1250 183985449 183985457
    0x2060907170d0c0218250305060a05062109011a10120c11160314030408120f0c0f071401090302090105101106070c03091d07110f100b090604050c0a11070510 69
    0x6041c6e00182161016a031032120740780410180c58030b5030102d07000d050f4502030035101d0900400e07003610000d40001c0020101070007047c1a6054201607059a000e040c200c64034108074111032000d80884c5c1018100485c071246159039111078000c054001000818203c4c0810040084400b48140980400c012001e2802e000d400b8a04141c1c1c0b031414075681038219245030520070b400030003080000e080c000518002c0c100c01080e07010340d00e103041c241c5943c036440b40c032445000c2030017054501840c1c0075000c508403040300c40d078210710840c01036039000444115070369000007075014520100500140c100700d107558842c03900d035041c559040509003000510b071850072501c60300010213640c07680040681c007484000c010701c00c40300540140c0c81041e8040b01c048800038070500c10024144000d8041a40c1000001d2071b40c0740100c151941c14503004006400b5051880b00c83e4011103441c80411070608003403040314426031110003c18100040c0038401c50f2062400306601046110382c60012845a44074910060b90305401d4071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 183987949 1250 183986699 183986731
    0xc12042324010b040308030a020a0207050a230102010605100302090604030204020c0f0c030307080304020f0a09051512070b0712030f02030f0405060f24010207031202060907170d0c0218 81
    0x2040a000000c1600001c3c05440e05100400000303603a103044c1c03a0030501c8081c003d61600038010080f45070a41c107038005c540c00594803e0019164640620b020300300e40d1020b4080300080f00100040e805da90315840b4082c3c00c0707845112a50005446540580f8a0100c01400d461501c3e030b59800150a80e00b000400c103080e0b0700508002e941c000410000c4404030a4103402642c18480107449050792400000c1020340104100d1180b00c104c0e40c1c9900191018042c125001c10581c18580c050740c0c6040080c00da528000c0c0f0030b0500102c00c6603800039001c0301300c511260b8554030b42016507440b010034100301805102810344a505031268081240040c40c42203004416402503803a0505005241c04009013100003031000203400d010010015141482e12110239040301010f000b510b0004034600340f0140d00180000c0c002101001c038442d4081203a90241d441e134801c0368643c80d101c03010b02003503441c43c0c4ca40344416442242c1e00d104403401101d10700040ee00060420341c0c0300040d006e0200400004a0b000a558140f0312 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 183989199 1250 183987949 183988003
    0xe0904120801080a11271603060b090604060f09080703030c06180b040209060d021e030705060c0d120b030102030a15080d080114060903120306090c120423 68
    0x74811900404610004042c18800741d1201c480c13207a0340400d501d0140078042c1801b500c007801494005174011850510445528207107401007001500508860000f0741060320000d225003000003520300f108001060340e45400d1900c103080d100c803031941e83c07505c1c01d000741071400091115042c8290b000550080e200c42500304420300d0218222070100460504d448528022000803070350003141c2d1580181d055031030280c80d480b034900007071512089040095120b100b200781d24101c080c11440700d07441e100b0140c0803aa5410b4854080040900074000404d07581d6000301c0484800502c00c1040503d0781031003000014041041c42c0202e030070391340202c030a841c5d019118a80e101d80c038454400d010000300460809000c00b10032401d0010f2031f80c8418800c0c0c481c0c090000014488aa8884003110000c15008040321404c0a02040ea0080354004680c050701c14144070000800080713204088494424002002e4605036643e540d0b0742405481c09819040a52a42d81d00842501d03010803812040d9004003400005020b080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 183990449 1250 183989199 183989207
    0x1020106030b040b0a060f06050a0c020102190807020319020102150601090b0c0309030c0f1003020f040f0f031703061503040c03051603140a0506012c01170609010e07060f0e090412 79
    0x1070b41b001411f140810000c2000ca03900c03105440502040e4034040003d80c0403400105d161a034940310850031303042d4404081e001c002e19600100340741d03442030f801c0c6c400c004064100c155800402401c041c2c0581c004071f10f511940620012155401401414500d06040e1521a4011150400d101100c2158000514540e1900c0c04101480010608a520460321507000c404201a0854a42d08809054000c54a540e80501340d406540241c442c02c85030b0745281c0e5175090109603400c685e220544140014074400c00344520003900f201d10501b0301800b00c3c000e041c052031a403629584020801d599a1036000c0d0084009402400211200301c1660004209542182170008150785541c1400c3d003540d200c100c541001990218101d1304695040c028440c2c41e25200028030380300c100c005140a80541140700110307071300c03400800501074440c02e60201c6030213580c2c010f00d603801c0301c0714030b20700c2d40d4560301c5900c0130480207100c2d80514122881c18039120076050586000b02c1e09445003500c00b00c90030030020003140b0285500c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 183991699 1250 183990449 183990461
    0x50103060e0d0525140d17150d050a02030601091b0804050c010302030c0d0207030807030b040b0f040b0a080708060f100b03060607030c0b070801090605040b01080a02070201020106030b040b0a 84
    0xe20303000b404603805240c0014206101e0032054504080d0004840214014004020755445030091683e98007140480f00803501d50481c01c1101d400f142c0d0070901e406080500058481c4148168100080320101920810004141d610030444113841480300001c010b88043c060745008045a031400300d14004808913007801012005000000c100d0000c0400000c83c4001450094240d82801c00580e291201d20801d4900d10032051354001d60b600000305001003681c4035031030300c3c072981c20742d60104066145202000180c5504000003070b40407085100402d00c40ca0a60f00c40840c000008001d0090559a180780741c3c03c0c00c0050b13000c014640c1180c82001150f4901680280d40440d68910715410f041c01c00346011034038000604083d00404022810504050182030400a401d4110424180b503180c00040180004001d014954946040400010b098200743c01100e21051058544c2c00ca541d44070340c0785000035005807000f41c0c110740d250a00000812903490989010794050006860300d450000d0001043e13400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 183992805 1106 183991699 183991721
    0xd1b180c0801140111060c0903060a090b0402131803030204231e04021b0c0f031609090f0602070318050306060607020909011d0f010e031303080703050c01050a05010306 74
    0x1f4160003812440074210704468280d80c41c80c0d100710034bc0b11a21402041413a5881c041401882c0503890400001d040d03502c00a031121306003a480889032040801034008ca80d00080a20011028082c4400c0d10030700b5030850301400c2d4030706010946c41d202e240d54060780c0c050709070025680361361207404549803142105440c1b02c0441c6140340c4151070700400c601c0684111080202180641004144001c85107000c03007620f80c8a0785401341c102e0180880000c00c0b180100c000b031032a07000030f100388054003045010784c0d9002c080b5010700d407100614036400c0c3c104a21070381c001c0e001c12040d903a071300044030f000035410345070080161140600741d03000d4480c66015182d0821595203008001d100000c0305201d03203005e0310080c400803011555140d00e81c450040808800480f10300309201040d05140180758840c800d1600c2440c08501025043c00c64105854104245031140c00400c00e1207070034020a51005 = true := by decide +kernel

theorem cover : BRFrame.Cov 183812949 183992805 := by
  have h0 := BRFrame.cov_init 183812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 183812949 ≤ n) (h2 : n < 183992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
