-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0190
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:20:47.351745+00:00
-- url     : https://prove2.me/submissions/c8a0e82b-f96d-4b8b-93c2-66df2e2e0b36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 33992811 ≤ n < 34172667 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 33994061 1250 33992811 33992837
    0x1518020102190312020c07121b08070602060a0f0e150612010e070b0906040906060305060906120a03050a090f1508070212190c021f090b0711041d0f0708120405060901 73
    0x10403e10950460001048211040c00500029448040c9d00c030100085280c60341c1d955050441e0380340f480b413007480050b0f001200003801d048034551220303400c1c1ca55440c01041004034513186c2801e25100300c009151007220b21040c800c040c14002e5462005d1030102d0000c011101d88500d0580c0e450200d1b20480c800e2039400201e150458079500c090f203006194a0383c06001139174944030060090403003240c0090196203280002122441c02a42c0c211041c98507001511081103251801c6845501c090044014042c14034000070304150b4a0075060000d003440c0441076044005418020b042d002c000e1700751811548100260034212035070400702d680350180c203080007c50881d450401d8401040102c00a035004aa00e070400921502440c903070300c08200c0d81d0741c0d5000c0e400e85484c0d224220f400b6485002d0070701e035100e0301105510700341036016014407840d040d1844c803026030705144245080a18a89012150070a810070400f220f400c0100e00c546018141e4240d05050601c070104560f07018030340501c4e04218013429005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 33995311 1250 33994061 33994063
    0x40f0507030b0a0f1a0105091201021c0e0c03010504020303040605030703110f12010b1606091106030702030703021c080f190216021302040f03020d1518020102190312020c 75
    0x80055070b01560400c99850b02945040092200c3c02c2001410381c02c041e9449450301481101c1440408142c60b500e00b480a55001d000250400806c444029035080082c3c00368058007410b485206411002e020a00c811a06043d070304103800c0884250207a810720382804016038002c81502d00f514102d203001d580700d0b44c80140450140c4042040180601000a24001c1d1428034800401c18212004680e44459a943c80108180d10598030881406044200110002404ca8100c2c450160040e0854000d0000010008a060380b00340c8550015910005224003019010320a2808140b44a140504112805040036101d1100201700314a48944500082d50204000c0c1110b0144a2a96005c64031140903c2404802c00c00329031040c1c0c440c1d401451241400c01140c02214256051880071507142480d650902c80c8000108204031010b5021055084030403010703100c0c44400c0c0b44092545444120180000782c2040f0300c0d403403074001e0460780030030490102e9003241c007000c0f9501c6c0003107005a950303540b85030319 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 33996561 1250 33995311 33995323
    0x6010512070e090103142a041e0606090512010603030807030c0c0b091006090204050a090c0522030b06010302070b010302010806121b09010f030f0305030402010302070206030702010c080a0e06040f05 87
    0x543d5224600300b0000c002e008010343e601c8a100301d584e0844038400090780d03900340c00c40c2d0310104036041c40032010711018950030b041d08881c062410340080b058000c915000c4040680d1040c1c0c000750009100058100030303e1a120b50314030b02460300d41000704549411034500412428000700000185511a002c1484103881043c2660200341c01030b01018003403c1c43d041040d11680c8403820310310013a00788400880d00310b42601c01c88003128802051009131074901117a0138040c000345005038003880000d112541c1c1c4620041c0d05c1e00701c0d401e143c082450740d890840c58014509900501014105071050244100140c04068a5410340c0d409003030100482d5600c1c40001c1c54800708849600f104c0c01307140409801c3c20385409418101120403111440260313201e208010804400d0710000c0c106003004950400483c5c001e400854025006140242c0b81c02440d80105078154801d031201c4006039501c0f9204a88070340e0220150750001100d000c00e008114820b1026640c402001d000a40314001010540c0100181000a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 33997811 1250 33996561 33996587
    0x809060405031005090609010c05030406150b04080703020312070209060f03070b0705010603050601080d0c0305030a0b0a03110310060b0d1109030f070609060504060f0503060406090e0a0c0e0601051207 88
    0x103c980121100c6068009480700b690f0341503580c4540e41c0411482d20040c040c8a07907401c091340c1c900e420341c0d8030341d140c0c0d8000e03020440c01038110407507014021030031100c4000200003400001e030041403c2c4e49144141850200d44031070781e0030744d180144183d40060741d40c00b44480c3c00c001c0441f02101241d807120002814240d40347d0110418100000e41d1904000064004000322406902074801582c1c0e0752034016181c840000d25100000c0450b051400064000e802558000400703d074002441c4c4a1200810740d441090380050f5030041c140c10303402c54117140c2040098002141d03550b00b0301c9100d10b8032001c5140750003100b4000060319210038905001c000c0410503201140d000500f120610301d5104d080355120741081c00b40380c0010f0060301d404140d5a0080d401c4500300d031a04d540c0c0030003c02e9450002c5596410241003958429180c90340001c02c45124022a91092070b028042c01c4200061718200702c005070035600141090310140704000c003582c3c0140c1920098402c5000301c8030144d0782c1200445a01564101c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 33999061 1250 33997811 33997813
    0x705040501060e130209220902030307031d030c03030d180804030602070c0b09180403020f010c0503010807050a030c0303030b0d05060403090306050f040f080c07030c09050a0606050313080906040503 87
    0x1e0043c0d440301809111203001d036685207680d0010312000c8145d204104603c0e8010340000f000d201c04006801c2030101000313009030001000c02c1c1c0c0741e00082c1103500c1a0360a0780015030300c1810800124196440d003062010440040c080b4110182c0802d40b20300680c3e0b0f2408110343d44e150b070a0300c25007007a5410f26510f603200b0034080d517660b100d19199009400062058844c0302c0100c8020910b003010600300c411444004110648001f042c1002229550000b082101140104c14081506442c01d0240742c2c20382c40b15441d055201e60401c01b04500d4181c840d44200c0c426044c1100030402304201c15541000d41750145000300c5c406400d000444e408154101000b05103216980401050503408000c80f015a441000d050200b0380716802144a42d100a0301e02a04454000d407200c2c0c000307600c07400105801c00c0300f08160745160342d403511084c5244601d5408030b18515160010041c041c0c40b84e100303800c05004642032003400e40c185034805c00441c00100381c00409110780003d6415481d41d490080e5030060030014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 34000311 1250 33999061 33999071
    0x5181b060d06050402041e0614120c0c01020d05070315051516050a050f0d030e0c0d030e0307090b240f07030201090206030901090b0603121215300105060a0611070504 73
    0xc036541d007600700180c00c800b14049400701090701885040c01c040b1003d04000e405041c080c2200d2b03610401180036050f808101d80400c0302c0da42c0d0500a001800c0303240d201d0702002800345400700001d0196400c021029080b4040c005040c000c6944820390704058003160791081e92200b40342503112442007148280500031b8403e01000340100071000400b48503c500000586170b2032500e008040e000c0c0e4140204862031030b00710380204070041c00d0007900c66001c2400782c90094210054040800e0601c02c060300311a0080e030b150308000d1030b0390911003003541c0d114295402d2459070802c1103560b07206070300403502d041d00306290004840c01818400d41141c4402c5800501050b900e080c00428140284107480089403001d800301c000a405103030201d10481d25030540101c02d072170702d41520b80d0200040c1f80106070f403201480c00002400d960b2100451018080c5543c0c820203501c510803030404440819500c40f2503d907030b0500c81040250b0300e581e0042c2040fa000c034103003a1000c28440020034101002c0d90800303600307d8602 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 34001561 1250 34000311 34000319
    0x110c120607020c040507050703050a0207091e0b0d0201020604021c08030f070809010b0306060f01090b040b07031b11060d0207140102130603060302090c031906060305181b060d0605040204 82
    0x800e40c140aa000d68003280c400c2c840300c41c01e0000b519030440761107002c1003081c81034002003802240105000c80003481500d8003183c680391098220b0b990b8581041074601007501d1011140e40a1003410001d0700120f403449040ca038107900003542c0c1c9000600c02030050b101040c082e04001280381e200104558881d00b89900c0340384c001b6501550940c200d596000042d40750006c55200001845204100d00025016100966582083c001d006d500c40023a10f04002945800145401c1c00d0310142000d00b400c88040e40d511242420014210222032245220160001020360300040e00b080400090100503118240c030b410501680d4002405040c40203000001080460200030030103600034103102c3d4804054801264661390110200c0301603000c025001030349500441c0303e089900c0091a40b103664500589190314a0204a4054882d0ba600c00c00119071a44280403822031010002e000b841d088100a01842d058001c0500c032020701c421425003d01c00000e10900705c2e0859403c250042c0c58054015582c959035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 34002811 1250 34001561 34001563
    0x602070b10060503060d030f0e030f010e070e130f06110c0109030210020703080c03040620040e15010c0f0201180602071a090901030809040b040908070204050105030309060703110c12 80
    0x2159241c0c5501038064000c40c0e694010002e40e40122005031203010864900e82c2c080d110643d20700c040e6014040301c903448042582d130400022010801c0c40c0004100ca513480c1d00700c2071510104c0d070081ca0100d0352510400c0340c01e0010390051203400b038200c0800102d05905081000051074a8040c003040080001942c1c0f01c2c2d65015000302d0216031003503088031140c440100b40d400032030042c5c1c0c800030000b4030300802144a180342c5801854006005203000030310100100003210040d07903020040ba005c07001c0802e04100030b005414449901c0b02d042c0a00804080300a80000c0a6600b419130084c0001820042c10080d6442558800000c0040854002007240c0b241d4020f56546000e100306034500da10f018499000e442074500b598070b10314024042d81d4035a42940d0300d02203250820588030750415504d81001856a44134010201443c1c051280c0c0781da07403600c07401400192201600124000d600400a4203103c0d1150021190b0709901031418030000ca504017005400d01c0710180c50140d102c8150740b211035160b60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 34004061 1250 34002811 34002833
    0x9021008062101051b0a0e09090f0f0f0c030c130f1e09140706080601142107030e07080c01180503010e01230402060f2b1d01050c04030609030903060207 67
    0x1103449104052461505d01c8110703203104000414002a200c140d0340c04150500c1040103821020010540d01035003549240c0d10301d8504170740c51052050f0301200d07483d421803805022082034008241e0150101a11030804669a140038240184029a803001c01c100c846810350721030210000c0300c0358013104c0f89181441e01005002050019211210403842c180d0b1703d40c80000300e1404882c102c3d2544685680d5a00054950f404a0600c03060001005c015000c500d0a00e158a0f1540f1545248140d60508000f20010200e403414000649940d1203800244018440050b449020f1542460405c0e88c091454400390790401c1c0c0c50303010680542c01c0411070503c00c0819080003140c1281c5d036440500c1e080440700130146155007560043d4001004008400095a1220042202e02d42112001c56014100c000c0d2503004817009001900e9a0380c0c031030441c10030258009010003603090100c0240b01c2070071700041c40f0207a032080d448020500d030b664090002c1014010500c10009541088045441e03407014100403030048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 34005311 1250 34004061 34004071
    0x3052a0304060314041a060d0609031e02010510050402030709030605010e0105040b060a09060e04020702090403020a03020d090501091401020118030804020901050111030304060510051003020d050105040902100806210105 96
    0x190400c08001c0c1c40c551640c10341c91017160004010100c00411200c00000e012000c1d14464101ca694485903000c0f40e200d025100742941f09584036000d0760001d881c10420314040000c9442103904010a1107001c01c5011030301010b540303080710016520b48903280300717480344091503100a001500704000050b1456800751a00d040303d209550500c13a00c210f100800146100c2c501c2d0301800300f900048180501d92044002c6628880098001890030030507400141d65454110317011001644005660310070540d0601209401c0300440c2031520120b410100080d1000285008074444010f500c0c10480c3e06031f01c00d422980f2030010f050000341e00801c01c3d0500501c225030807102070b40280e805000010b0b10703501c40c0950001e894405409182176440c1d680d201c0c80a024060300c80100004211404201595240301240304c40c00c2d40d4800599640340c0d2440c50054920507030100344607030302d070110520258031107201e03101415200c0d1034800e905130384800000c0e40d01d403c4140440c0d9044604055035820150544c0024054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 34006561 1250 34005311 34005317
    0xe12010509010c05040509010306050a0b0d06050621070302061e0415020706090b0403080c1f0f0b04140105090406020c07090b09090705011209020102030c100207020120060403052a030406 82
    0x10046034003584d00f0b2207103108140e0030054410040001c80c0e11907000c150402c61100c03010030303418501030014070311114218058078440c0d5114203000941c905001101184c0c60703000d95420170280c0350441d03980c07142d200c1e01c03020340200e5001070048002000211031014011040072901e8407180c0300c0c80c081e988421101c580101501c40d003a00402c9490054240c02d04031810300081e0342c0f906055a072000044e4100c81c81c0800280308190000d403448030404021782c6c1507462030400090340c2d100040190f00b0342d901000e1143c0503601c2c2415008c10200d9900c011411b42e2401c0c1c401030400e032124a01140240b01e907001c0d0b104940030300e0b000450415400d401045c100342c030403100181a6103c0b00c000c40d4880509100707803408074000100c10b103400005a00040715050050060780d040010b03600e602410010800c1e28a0541540016084115a0440c40c46d880101c18185015100c041480040303a407060054805402c1c00404103104003c0090100105150301001c40340c20320b0445c03254801662034000c0d0180c1d00c04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 34007811 1250 34006561 34006571
    0x5010305150f01061b0b010e06040f0501050607240c080604060803030702071a0c0604060603050d0206040302280227090f03120403021e1b010f0c02040b010e1201050901 74
    0x141410402094012104440c2d1603020341d2904400351003d510804054080665050302c260200c0c05845070103008107408074040155103800010402203c4c1855011140341d89840c3c0140402d44442c01070300d0501740d04c0440303070b103032090b86a4040c6160307590030440c00d03515820600c08080540e40b20a02c240140801d503000d010040e11420425164007085424000690109000f0402c010706c0c2c507921a20b0032072190021340740c0b0340114400390a080017102c05560260301c1e000100204402005034007203082c0603201802071402e0580e002034503940c3c0901031300000c104d0b1000002d1007802e212501e00400d5402800122080b002c481200020804400c8000081110b20b00083e0350910215480d0b0000c465280a145400388680c0708105084001d00140c04511030303205c402d020100c040051008031001c240041031381c0081d0882c0d43e880038a03842c5078241000910814884d20755008800e040f0195411100820355000f688012581041d00c1c1810a9002d610180c1080840406620150085c2c4542009001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 34009061 1250 34007811 34007833
    0x10050901080c0304020f0f01030e1002040512030703050a030f150e060f040c090b0f090306071709030a08060d02030a0210030603020406080c0307030b0705070c030c140103050606030c1b0a03020105010305 89
    0x242e01040314046c1d000411001c1600f043d1038a403010500510050400240000140801c58a82a102980e0b0840c1a40c0010148840c1ca461803010b0b009410ba8002985440502e0b80d008181780102c0c1d140b42c06141d1107100d5021f00180d41c0e04004401c80310345000c036202d13640d40d400500c0c101c1c4065800502480075100b4101d8141414007d0401908182c3c50b1000c50034070304600700840340c0c080035403075180e505d081c402c0822941e814040756000c1c070025543c00d0303040902440b83e14036000000e401c1a90990040140e052907640054050340c4c440400c55a0750351704141400401e042c41c0701c6e0741c8001d600a2100a17540c00164041c0c0c40704040d0303802903600b0003034503482c0c0ca441e03a82d908021441540c5a8481c40c41080014007081a143d1702c80101d1805500700005c9960b0001b01656a0708107c034020b8001d0014000c0c0340d02100050700c0c10009203000d0140303040c0b081c04a5481e200c003600000340f51200142500c010140b03100740150486d0120304441c010540781c00e0082c0204000e0208680c54055110492 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 34010311 1250 34009061 34009081
    0x100c020433050618030102070b07090602120307020a0212100f020c010b01020609100b0312070f03111606030513080408060f0f0907150e04090308070306051507020609010e1005090108 80
    0xa040d10b00152000e45801c0315035004030881400408142e92541d020000c0c02c000604050f28140621300c0c40e21140250780c00c245010b07092000300b10904015041c04d004000a060780050304855103601520100340d04040030b01d485040c00200c00035440c0703890920510211001c0349500522982e08410020080180003400482c1c9074001524242c107103501440010300c4103503540d0700c0114000d00080864802c034080200094054100c0750702920240440d4401c40c00303254001001000c84030030f000103010000d03ea1460340c10306980c1402400308244c0e40d41c000854001541c0c08840200340c01220f5681c07503554800550b690341d070041701c2c40701c0076421000108503260b402481c1e942c02028064080e140490811320354100500343d0b1802d403c20045010f07105141c588862051081d501c2c00380e910f03840b16107003000c03001d0185c0380c841d030140740034070300d07181110001098500660380030b0b680c110f030070075903803143c0d0720040f20f14840c488602c43d4800c00700380794240780982140c003d20034005d00380c85a65141d503e041d212 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 34011561 1250 34010311 34010411
    0x3070302090a05150901030605040c0e0103030503130516031412042402010f020304060b0306060102030901020a08090f03010e16060512070309170a0e01170114100c0204 74
    0x9400000c0c140104800748002d801c25035110f40e4004207010541c1003e4001681010301fa0301c180d0701240e5a5081c081441000d1611002428040280e82e807554990b580061140c4001403103110f100c902489410100700082c0070f90140b5030310804044044a40302d082c841008130030074011009501c103140c80e04405280060030b031030031264410800306060703880060f01005141c5541e555070465585076201c40c04d01c01c46101440c0182e01591001454410a034141450300300701501040c1954000c0c07001000584c4e00040c814000e6500124031501c2d40700a402149048880b6100c0942c59402c4c602c80a0504d500000e0f80100245405d07540d0100d42c0d03a680c019030b05880342e01502d503a102c011100080f003280c041e030400b01c00e580c40b80090024a0041503881310440c0c101c4962000003600d580c107482d00a690141a40a2031515401050140e516105049101b020f449010b240074070300c942c48050382c0f9405032074000442074014009000c3c80d0b105400c4c0035000c04144641e440c0c0442c0304c1e000d810369a505e201075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 34012811 1250 34011561 34011563
    0x801060f1e0f05060c0c0915030c0307152007090504050709110901110a020a03060b0406050105030f06090414070305150702150c031b040b03040201030b01020f07150302040312020604050c030703 85
    0x40b50000c6040009000265000c00321219051180700c203010280d4a602e02030510441081e8030070704580440c08200341c10000d040c50010b1107940080c038180120680380310581c1d0781031050300b4103100c5129044090311600750040300c0310066001c1c7d400000b9108142d5048203120b80e11580a41d52500d885005042c1254160204c080b02480c050080f500554043c115940880100000319107445646600180e048034090300102c0b14503407074008100140c03e00f401100094002420701c0b0382907292031203500d4590040180031074814003080d8045000d101200810340c0c0341c0440081520107154503401d12a43e01d00d07a103881d080c1e01115440004601038400300d01c403440745c400454400b140c0c0d214001c40581030380010f46024001c2a0101240c00034541c510000c0c801071519010b070707944a00d007900024046580960006043d9005000d82070302d5440d0100e20201a04d070555010541480d100104400a0045410003400c44036034400e070f0f9801640000f117180c8a244160101c41d20700400b8004d143c0c030381c0c1c050303c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 34014061 1250 34012811 34012829
    0x9060803070c0815191e060509130f060207060e1221040201020307030305090f010903090503070e2215020a0309020f03030a14070614100e13020d03030203040c0801060f1e 75
    0x1081e18034003401103170794100c69034100100c0c050456007091805800d214104044859940c2c0b000c000a0a003044442d620484130002c02c1682c8a036038480003400e01056000402d081d0b40007c0b02c408011103980a131038070300c54000031140c041601445411a6a001e0219100b81c0c0200b401c003e804041c10010407131203180c3c1a806582030424503036065003c3c04c0d02a1400d071890203541d00c1c070b0315030070000d2245500d0300340030380c1d6944481454401414140001d07600940c441103074000422070310a0341c90b1207241115170900207a9280b02424101403820024040803881040d00000d10340b2003459058000c903510a00803500e0482c0c490210b41015642d206048100000ca480d045401c0d00b04031181f00505444e03400b5a10101d602804481c2c07105004004850509542c0e03950007080c0300c010b42002c3c00301d41c0300301e1400d2501c01008060b00080c045503d0480c00608042e0000005000c000304800f46100811a21000f88112a101d070220405d144103402000801e01202c07070543c0d0084000d281c0e28044a00c880 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 34015311 1250 34014061 34014103
    0xf06120308090708030a051c05010303020d18050402071a060f031905031335030403120314090309011103041a0702011707020309041103060f130609060803070c08 71
    0x1a600340c8160300700802c00c4115018644002071419000e20044c9601d25003035662079a0380c1200c030202c0c80064440c0c1c40f9240418079004c01480002d400003000c00c1c4500300b03800e080b04c0c0041403c501008003103458010a40041c00411000100240d0080140002d082c042c06168030369116020702440b5074150840d141c1c541c1c0250300241d0300201c1081d298900e80d0150054a14003040080d95010141483e804055081c41c42e0b40d601c80241540400e000c464038800076140c4000409851469883c001d600024003c022542d00c03861080340030758410040800300180d5404d1505c0d03c06600c2e5102d4014126450108006240c0382829540100840302514514943c03000541481c040c0f414480e009264101d041c806010724016100c200688818072a4115500031039950b0144010700064071890045540c0d035075403d0080c0441e0b6910800344100e16101a1103c0c4075201b0800c6002e0040d05841e80005ca90b149400b0011801d000080000d080d80383c0100140f521180e541c10b41ca0f545e41014200d858143e81420b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 34016561 1250 34015311 34015313
    0xf0a030c021507020d060c02071e03140601080a06051005031902010201051008061602012301030312140a1a10020109020a2907080d0509100e0d0c02010507050102190903060f0612 78
    0xd9800340351030247c10300c1211141e07910390b081c108500a0f220059039030f008a0302801c1041003911021305510081803405840c030b035450714070b90320303500c0c070603080c0c010b03c41034861300054504840b450000c002002e005040b188070804c5004460800000048164010350905001a040c2c03500d49803a030040f10840c2e401080e480d41c0315407400c516484ca0210722800c5540b44d210070b241050403c0c0b14100100010082d440c255491403501500103010100010106c5061000130399403004500f072065406022101c0211307a078014011815402a00c0c0c080c3d4a5000798034000300e0340059030540c0200d001300d04c2520642901a03d44204881c0c00200101c0c42e0709450010300c0c1d121001d1000800341080c544240784550809040300e41c2c2c0d0b42655401c49009015034886818032000c00d0391130003211010030181c005402c007212400801040520b01c0c0c1030107414403d00140e0740c020840e00750f0480d83c0c0c00b8030140302e081a916403000300603d0340c400780c8026556907003881584000011140304210441307440c0030f8000540003035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 34017811 1250 34016561 34016573
    0xc0e03030301080c010305090c0910080615210705150901080606130b0f0405040c030c0201050a05040b15060c0105070305061302090904020114090d060c0f090e13050f0a030c021507020d 81
    0x70003230241c0c00038001d00103070701d4054651180307942c042c008010340c5810b12420003548034544200100414a241007041c0200407030389070510503120070303c203070b01641d006540b03850740c1d141c6051100c0c6c1c429a007009003c615042d0200a20014200b408001d81e140011521940300300261400b0711101070500006140c41000140c0c2070710001d200c1e034280c0a5400342859900c900280490340010713a100082611181000b0459a0a126032940034070702c12030400190805884280c09454014283c0791114560041091a03030b5604003620f0800c43d1300300082c00a843d00d100c00501411060320700358041e52122070096071039140d50080d244000006480500d140d036a40d001103800b101d20389040c2d45500000c10824030789072901111103000c3e9010b40030100e00408202d034003c201541450055041045041d02400134a8407803c0d503980008841d903080c291072145040040c100700c480e89003030601d44200c008280c201504160b440340114022142d400070b222815104003054415223000075444000b0806900016070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 34019061 1250 34017811 34017821
    0x30f030c0312131505011503021603030c030e0a12020c0a06020c0114040e0a1a060405010210090507152607051603020708120c01060605120c0703030902060a030c0e03030301080c0103 80
    0x25240c04121503004158a0f84c9510b201141c000d840056102c400510402062800c10040c0001070329003180f400c3e10100403420f030407280383e030011300701600c8402801c90244070341c1015060030444002d40e26281c2e640d2030402d80303490101d1440d9026002d0110840b40301d240607a4020103d40c4941c01030105108607100440c0c041c0e029070116a0554010b100c00700e90051301d0090310b84941146c0078009165024501e69210310b444400d1064030401c0c0400050040384d034003080c02804d0301c1c1c0140d00840c541a20b842c4c098100165608010226501d108407110301d00d80c481d40d523510f0768880e0424440c2c1c2414412003038990143c1211a1408a0010001007141601042c04066403a0080c03054802d210b4542024a007041211210f1a10040380481c0c003d66805084c407401d0024a81c030f007081460302c0408210b0007072504000704030065500c0d0100303401382070500a410440026034010204c6545071618400038000340072000380c1ca0009050301c0000700c21414004100c905941c2c00200801000c1418401180606 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 34020311 1250 34019061 34019071
    0xb0309030d0506031501140406080c0d02010e040902030a0b01030b0a06050a0312090b0d0c0e030a020904030809030c01050f0403020c0306041104020f1605010b09090a0b04080307170405030306030f030c0312 90
    0x485002400170921980446840c080c1c80d141d0380c0006c0604c8804108420f40780150482000c540002c000d044c0103503201d07803462507883e90a0820016523a080070010740102000f8002942500401c40d042c0104140072103c0d0307058a204091118007521549881411134681d8050241c10030f10a100034000305203101d031340e00d03124100c070700c0c040c131607652948040c1c80366400030b281420502c0d4a80d030718075280300d8020018980210f070079001004403201a8000401041000d0300c040c040c0040240413030303598182401120300c000b070004001d02072414101401840341408032070550050003000d01c524010300d80440d10a01680d04910041440214802044020350001118034a410410003240072100c0741c0582c411625402603000150101920081c0088100300401000d0302d0380102c1d6142c0002002c02d000700307421540146281d61640d9a528042d13903a041d40000190288001008110402000100035480391b0000e03000d5802e100300c20500c2e655a40903041d060310551704203000032841d5a015002c0541c1c02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 34021561 1250 34020311 34020313
    0x5131413060609080c03031306050a02190305130e06010f0e010309020301111306022a01050d0524010302071104090606050907020609070501090311041e06080312010b0309030d050603 80
    0x48250104a60304640666001c403002c0360040004000c040700500c14803259000503405035181109048a42100307540b40c6c00343c030040c44030110b0f81d000500d208003e0b0981340c03442100b0119503202c46003005030054011911180a196264002040200031b800d8614090001a1240d40c0c01038443c50003500c0e5001c504c0041410103903609800409607909004841c0b4003200f5812096480d80716030300c81c070310b400002e4209a0665100c080072a41c2e800c60040303210404075102e51002044080762004965500c21010a40e0110f07060006108502c3d483c1000701480d9880b6622485805080070019010382c01049000380540307020396001d0300035081c60707005103480c0343c030035500043c200c0d0f00c034030005032041c00591340d00c001603100034108240000c04000c2c00300502400d00301806603e103543d444100c007010200300b03180680e4680d005154a03172110a08500c90841a4130240710090303d801141756030341c0003c9006035044491100000c0e400900300c0407030703004500781000b4520341005104040054407001e0724140d05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 34022811 1250 34021561 34021579
    0x6040204180b011e12050c030f040b09010204030605090d090f05031216050a080a082212140a0203070605060409020a0509040c08100b1206010e0106120f020403060209010906051314 79
    0x54000916001542c030055210b0071400c40c641456402115801000010503c7c020014000942231302c008d00d40c0e01a074030444885040e0764147c240790181c000c1c0d600c014006c2d424101800314044000c1544c0501d01c680741c1c0d0340350a456503800510f510500a1140c6030f0180c01812500c4080c00c00d10001b4400f0001000c0581c1941d9500d03511585086281c40e410741e01a00c000c12038801641d48192060b41041010407801c032103030f141100c3e80203034034910b0038001c1890403410042c4540602400c0300380e441030313810190151a40003a210194a80d482644120344182c80c0c480010105c0c6454030906101580240c04044001e04100c00d0080e02000a407055859032400d920000d4812001c10a03240c01703c0090b800410128004828002c0240d51801182e0480d0400801404414510054641154000c0c0340000222107000f00300b00003001c003a00c091501e03038000075011040c00f88980041103200b60a03aa0349104c60782d01c810454560041c0566101c00407290001000034490050055032008002408050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 34024061 1250 34022811 34022837
    0x20f0721030c020a030305121506040b0706091a071106190b0105040b130906050102060402010f051815070302060609150112020d150906050418120207030807050705040506040204180b01 81
    0x985011907034070841c0040ca00048c0c01445c5a0299400c0c1d03000300714116140c1500c0640d41c00030361280640d000d0750015100118010342031054a0300028400341d0403230041002ca00041c503422040034403c85510000c6445020f01102105000641c20300c9032540041070100700c1a003040c1d030400303000358031001810070030248804566a21124001d044602e03c140300c029000340362038560426510158441030664002d0420480540d800c60741000421181e1325000e60f4900034814241d40d00e0001f10000c0ba00312002c290110400c03c0801c004000142c000d400721501e075075402080055502040343d900109556a207d043c2043d4020000e00b82c0341c801e056800f6040c44d49200300350080310072034003e00684002040301081260690b21404001e00000d40b800d01c00b0700f002c00c5007040c2072034107080300034a0004c0009002c21028402e000d03c2000e558400c0685590b050300d42401a0383d0f4070b45004292280d032401000c54007a18103442203900702d44040300e2041d4040c8c40010726200520a003000725041c82082003800d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 34025311 1250 34024061 34024069
    0x3031b02030703021014060919020703050d1505061b03040b03090c040b0102121804020405090c0d0c020a0f060c02120d020a14160212151006020f0721030c02 69
    0x400006a50045480d5400382c20002e26120788610005d000c18130381101c400320640065181503000e0310070340d2125003613241d184844100c0c01d90751110b00f41d05407000c01c03000205a8005e0040c4904502603609101f03107480c01d09a60021440b0340316a03640100100459030841c24603100700600c10380d0840640b81002d81c0c4a03100b046542c02110b0508403908002241e15403880d080c892076000b40c100703200410302620f0104442c0710354824590443c00c0300201072400c8a003540e03650102e80152001401c0c6003001d00341314819040315080401c01000da1420510107066540c80010861196604401d00d40b02e0380d0f8a54454400408031035540d0310440c05a50224440325040b1b8000f00000c00d680c100051303075440c500301c2c0105807841d585a1a519a0001c2228501d62104403215100c40c50301112501d0002121501e102c0c40d000c01c01034074104003140bc10401040340b540d000c840e02102c11540958400c101021811900d43d2014081d00b18507803110b18001c6e42c4211115020040c2074424205101c6101d0030350009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 34026561 1250 34025311 34025351
    0xc030103021302090d150c0807050f090a1206020301180203040305070206160c030506010f14031513150c0807080702060117070305031b0c120601060305150603090c120307020a0506070303 82
    0x1514034109046c4810640901d912441807400050300e0503500d14107058400400030700c1403d512541c648004100403050341d5075070341c680c0c0c020300c0070000502e8041c03d40e14151010350400d1280380d140701d2810003032000031182c2c2d0003102e104660660b036441c60506284d007003107455004a00c0d02107607402d000b100c41000605020400e07000c0c5014100400d21585007540410a20b5025000000010443c4144c02c1c4035841c005001c83c4114100011030b032a560303801c0e0b45c2036105030001c50043d10860340030a1140c0051940e5016880301281d03030755590040d07500c0103000d03691070b0015500030f00144c0c00000104000700c0902c1481480200710011758001584d29261513103550001c1e10320070500c0000c0004c6501801040007280c903440d005440b054212004051800d4481c01c0512804e000d050701c07840011051000541c0003204031500808207600d904229084070340d20360440342d0080c0200c1480407500c4203003900100352201c0507401050070020034201828051030703400520003103041c10346a4000a0819050b0401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 34027811 1250 34026561 34026563
    0xc071509150f050117060412030e03030c04030209010501030c05070b040507120c05040e06040302030301032402070311060f0105030705011103120f042f060c1203010b0703080603060c030103021302090d 88
    0xc9490b10362104000212501a4801c2d8408014101c880a0b28040801d54030350142d003000d9020301c030800c0340310143d010300640440309071140400000c1040003c103143c06002503900944030101c0b241e8035000190100e46c0310015110114070240300c1600040c89614281d64458030486c282c8800958601c1118280c0e0250302003180e05d142c5201051282d030415200c1c540380111003800a100c2402d294602035202d20060001405801e2448141d802549408943c0b5585a40c0c0d203204664503201410014210301440c0348920322030240da070106400250b4a440f5034180d88005003c1c080079440d04005580980985240c1c00e07071800f09024030700703204100f0462070740301d0450800341c4240791400303141c108280c40446030f0004907141c800c0768071040d202440102c2d07804450103665075503403000d0b802c24030f43c80e000315044e018403502d800200105203001c02002901090303100380c8a45940e80c459008054030360390708469010390310301d0130f00041001d40341141d003071800c0740701101e401850302c01c9500120b6002698004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 34029061 1250 34027811 34027853
    0xc09020a030b03061302090403050c0a08040b0a020615031207020409060516020f0a0804090509030910110706050c0307030509180114210717010212010909030905090c071509 76
    0x100703481e200d0505103c29176200400020f90142d009031a40010340100380980050100400400c2060003101c04101c8120284e4000580a40f119030742c001c121151f0340641c915400500890340450210144141c02d10382172580200039010050001680425580242d24180c0e8455250303414038000c2031a41c41140d00a91614000194a9074000c201a24005051201c0200e50380164920004691200c054a050314610840400c4540701c94090310700d54000c940c0c0159002c40f103444103800300ca810001d048480d03a4680191507072a07654202c1076410740034a270021002e940003003001c540080c0c4070f0390050240e0710f4001c00b82e20707143d41c2d02825100201c10903009010110071115503002d00340750008c41020000c03e00070a2010000c0303000c40c103a4544000d40710b00e240c107612450018005207400e40541d50038191120208800f9a5034001c40002350010060941c00720311003840100b080c2c20442c14184c4680c40789a0a01e24091f200e0359000e6013407003010f25100710941d94a10103400541095218040444048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 34030311 1250 34029061 34029071
    0x50a0f0e01020403021807050f03040204020403051c021207170f1308100b0a140433030c060c030206070806060403080a02010515030d020c0d080904060602210a090902070c09020a03 79
    0x2c4103101c00140c001c407000181d2401b090402007491742c45001c03202040f100e406000d84035166480800d0181c0030780d0304010070702d000d00054204e561110208186100403e50700301c2c3e41c00380a01c860312206104032000a040040d5081c00c0c460b010703120354000e00808201c122803034540500d0350314075440410a0341240f00c1640000c0c03c0b14500e0b132010300074401c1d550000c41d80c00055a02e058001781152802c1c4098030b000781d0703c4a03001c0c5c1c2c100c802c2d070b0054203080307240880300561452000102496589240000c4840d0001302c00042603091143c00326100d00c40d459002000380f92550b0506640b00c16004006603404141004048009501c11014150045d520740000c0b0b02c508014503885003200c1c00c070800707034003942c4441c03000103060794001109440440191031000200340d01d030410151503c5600700694100341071202c00645a94000307402840c5040c600201c46910030041607183c040c4c40343c4400c500001d0810082407003101c03031540c0101100c512030444c0a03003803559046a0004c0c0d800c01280c035808250340e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 34031561 1250 34030311 34030313
    0x1203260f0106030605011b02120703080d09030824010809030408010c03020c0c0f130c17180d0509031209030102121006020124090203090709020d05060109050108060112050a0f0e01020403 82
    0x141c01240701070310017407c00b061403640c1e180002101c0104013a010348103803054200829030110a1000c000916045030b1119039803081103220401524282c5011400a043c0d0320004400d00682d500811080500c00e02c50410b01d1080801106d01480180c0003c010340010003002440020900c214125a140d5807030258845814105203820465000d0800b8000c0c0d01303404035007140d40d995500200c110564030328001610091500c0032200c00348150b12003804844c0d0705050060525420a03c0f0600808180859400d03080c170403c201d883d030054104d09034041d0301c00d61601400381e076000090000d00b03802800050400010901050000f801502c1855074002d04200c20f00c502542030148281102101481d2054803a16014080c0f01c2030043c0310f84808140d000c00452200142489080020140950159100d10924030100d00030441500c1c0103012660300e000c00a46c40d40541046849244140c44a1200c00fa2465103d0302034030000340020200c5a0314180340140c4161032144c10903685041000588403421 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 34032811 1250 34031561 34031567
    0x6131e05011409010b0c100f0f0507051806070609061a0f030d0e0409020d0206070507050a09050601120c02010e120409060602010501050303030412020a0803040f1502041203260f0106 80
    0x180c12055002002c03188684950700c071110041d0440312001e440340d0341c0c3e060030040e06e4100382c1200e0405e028141080c240d0b0302c2c0c55050390030904001d80c00c000700b0401c1ea19000c0c2d0940d514810404001b45241e801700544c1c05030700e0085c0107011118001c0034017040009003690351104440700c402820f10082c2040c000490300d41020b500605e1240e100382e0007032040b804404405001d1010340c40c91944502c0d1a0403001d003c5455040400c0c411a5001e407155444101a24009855011724050039000701030074480092207400034003403503000f14410703160400180343c1101c6450103011014136040640d074071005121b00780b00c4200800b410820040391080d4403103082c04150320a81d4101c0c3e10901c11681040c00503c02590040102c075002548100455030341800c00074180d00344015a54003500d580800300800c014040c980a0107d4424460041d0010320f40c2d090f11504c00324002c501500400b481c4004c411030000c1e0003810441595564061840e2088481d40c0414a0120080700c0008111071048010040250 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 34034061 1250 34032811 34032821
    0xe01031515020f031c110705030c0709050c04050109150e0a18050a02030403171015030203041401050907050607060b10020f06090a0203060402040c050c1e0708060c040e06131e 77
    0x3444007039854202907440c005165841042e07450384c0580d803002c2440d0380200c0c64041f69010341d40301e03065903103079082c1c403c01d6a1101140d11809500c181000c0004200114180c210b506894050315240c141d01d04202080d003002e001c04c20f0380424440f070340413100135699401100308020442459840c56182090042c0d000780d503006482000418018421302002070307042100c0c035000c000340c2c208102c42c5982c0d80b1881440c0d0059a80449500d4a88041c049201d942c10b070002c5104901516501c0d2802c814020203a003200d204603040c0d44990841802444180b40100080101ca4010980421081000d00016000e0500c3d4041000584e12080e000c13411140c0c140201588000300c103001d0b181000068000c2a01d98100806c001d10950b84c410781c46d03c0c8180510b0aa48200300c40f82d00b101d501404112000d1308400342c3c00401e040c540324408000030150000076036588600942000c031800c1c10320b4282d0050010030f003e001c0c00c1d441030441407600c041c0d440c280700d4201440c00c00c511301c0086c0c1400c001c5080c1110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 34035311 1250 34034061 34034083
    0x1090f20041104060c0f080307020601030b010501020f0c04050c0903030c070905060d0c05010327030c0c14011e03110a03060302041b02030711030106120c0e0705070c03030e0103151502 81
    0x75041903005400300c0444410b0703404035042401c00e421748442c0341c9071102c801c0e019080300401503080030041c00304080d40022094142d900c00d000400c2c0320b90b02c075801039a84814040000e050b5500030183d031842428a038205540218500043c141000480400a0b085400c29109420654454482040911028015140c00c84410380710b02081d0285a1200c51140c0081d004082c10b06072607480640319104412001c819424210200014001322450028041080f02009440c1d4450240d4040342c0c0c0c10f00ea002e01a00c03903405850b60b040c00c01323031600100e148043c1141c0341d500341940c40c81110600e60b010340060820400594000483c00d00b9032040000312441c1c540441440701c4c04055103d0080d800204030341605422501682c0360400c4040003d0241250350441d41504800080e5075040066102810b402e40d65203081d00c9a03e982d82d074008840364014043c1c054500440c0032001c0003c24000c42c00246480c01c10b00d000b146c005100303001c030204d4046a901118001425140031684554140480c500207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 34036561 1250 34035311 34035319
    0xb09010501170103060903140c0f0c0108061c020a08010e031e0315090402030a050d050703030506090f2703030106120e010501050603010b0f1210061707080f070201090f20 75
    0xb00d030158201c42c1c809005020061400b0307a1120b800080c54050001d0b0b425140c48071520301c1e5200151b0a000ea20b802403203101c0d128521421baa00c190541c01070035594840c08002d0034940307281968030283e800b060744030031040e0780202c82c280000c075103640203001714941d9a889100440e40c3e1400c4c1d00e41c91a1515058445004444cc2481400100e0440e03d460703621041d401ca40d44111519076000003410081038260050491180c3d5070320350070075074008000c3c0c500c4038002c0d00e040100e640c0f00c80034070840c030104030f66001c802400000000d81504c1050040b119500c4001c00d002c200c00180c031005495a4000c2e003000c000303c0c51400c094081281940182c45212050704000c0c021949008045440c50106006100d03d0b03810125500034803095100648268203150f04500c802420b1070000d8400d210a0f900a810010f040417046d05c1746199140c400714020812aa6030107400e60320b0b01040000060043c103144219501c5046203030118070300b03182401e00302d40903000707480110211a92411090440910032401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 34037811 1250 34036561 34036577
    0x207061505100809070501030203041a0106030515030304030b070804052401090534020f15040c0e09030307030203180a140d020d0905090606091509010912050d030b0a09060303030b09010501 83
    0x43c104d005c42c81800b215400c0c2009601c0b501c0750310701005046503140301041c0311071a603000007a115600d9004640206c02483c499143c240e508401d160300e900c5607000c083c0660400d00046420103100d911140c3d40030740035000f41d480300f11060154040271562552402003009411006203c0c2000740c0c0b28081e040320605d0301940c0c00300c0c000d1031070580305140648952030a2080c2c4281c80e031a18000c1c00004060a1884259190f10342030401c0d01c58100320030b0358161060340c0d0000bc00f00d140c000c48800180110100c0004504650381c0c200114040e620081299200350b0341031944448842040001c9401c2d50320607800fa81c0e84091508116140440710b40141d801c56005d01000c0c4c00164215030018207a0707000b07550082c80c41d40c0d0000458007a1089400041c1c06c15100e11818990701c60500241018940c00d990780131015540780641c00c8003100054014215400200780b410659000f80d000305541ca10181c0b0804049950b56511004c0701c0c0030b9407040e000300c0e07100d0092844526010b000180940000d0821030382e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 34039061 1250 34037811 34037821
    0x2030606100c0b070210060909060b010801050a03060b061e0a02010c0e060a080405010b0d08180901050901090b0111031305030c0a06020a12020102070503041410031e020702010302070615051008 85
    0x10410407005006440c014090010404d0716100384103650300124811010300c041d654070024600104a42c00c4243d540070b1800d05030440540c40342d8010b9040324002032070821124195160070000f45540c504803940082c00700440120700c060248808a46144840306903140c0c40e100304081d09643c1c4c00e0b1802d00c10004034040040f03059842c0010ba64400c1d102e858141f80302e50359464194010800c466446505c121610005010003822600400800c440c5542e00100202868248a465042030141941c01b40c00c0200600221003242d103c0301c00e040c0145032104c08803106842da07074115840b80740568411802130005009070b08041000842d080b00070b80380103020a1404ca4001c3d01c030507030890028648502070007841280ca1007501174464080d000ba06032036865a03600361540000300002c8100c3e000e02d81d11003604c40c2f041c0c084c0c4a42ca03017102112002c0310840254003c182c00a40c0028001c905140c2c0c28007160010030481d1141c40255502c040c85103101c2818681000381a0035400002001c000f042c0082003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 34040311 1250 34039061 34039067
    0x30901180b150a05010203040618030f050703020109090c050301151803080306150304020609210303090610090e07030b0604060b0c030306040e0a030c060c0e0402030a0605190b0f0d09020a120203060610 88
    0x70111402751034210341501c242c1041854803c4182e0018210502d1401c104040c048049490002c49200740c0300d16080c0e640d50040d034800d07107034500c1c1e5150200300244010050b080d8040c900100384000c500d88008034542d5025031a00300d1155410507180703a0404404c100341d9042100004c2c0d14040714103115410751415600082252040604543c0a0603c40c081a2150003095030782c05498103030302043d241c881c41c0604a80f695210b04681c640c60203031006000090961103031180005e030303080d40d40160070143e0460b114105c01300000f0740b00c0f0342c20541e01d82c400186c03034071a04050310120b4400005180c0d24108041080242d481c031b2403001301d05410201d65140040c2e0020342c1c10344015440b883c0071a410740d10040542e81e20001c00ba80703a4015000204024452580f41e00290550380d080700c054002c1e00c13200704004650f0102d0701944051a5040050800381180304014094403441c981c0040380b0262681c1c0418000121580072011a6004404200840c0380a101d0540d2100007961a0300e1a519075040003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 34041561 1250 34040311 34040317
    0xd0606090605070804090e0f0d0f0305010e1314070812090307050105030618060103020d05131704060c030302090609060c071802070b0105040c0c060501060c02010e0405040b0c030901180b150a05010203 88
    0x201380401c0d87c035002d800114030107110709a2400101002d41d00603405884019120134212290140003c0c035000c000309044c44c1031403042d401804072044c0e1500540903030b6143e10f851a840030f00d01585110702d2100003403820702000b2071440362030f007000281c0e03d5403902400c0c507242c4007080c1c0041d41486010300402c001921080c0040030f162030300c004405295101c540040e070092040350340c8014903a0800d02007056070a031117180301c84400d100703007020200561200055001800f90f8040c410020303145808043c00701e8425009000d0000000382054a00307034403600010800e43c0035800c1880c40703030420b06042001c404220300d5090008090102940b03081d072541d503548d1700247c05000b11480313076030703280114040d2603c9014500025640201c0030080e80d615000c01800d2005213142c100d00080380407070110b00c0390800d80501d9016541c090402541030300d41000e0382d0800e4100400d80b608a40d40c5643e03090000e081003114080702c501510344041e203800d100000b00a0702010140143c00f461fa10101004141d03400022 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 34042811 1250 34041561 34041569
    0x10e03030705070305070506010303050403120905010e060c01060e09061902040b040303030e010b090901051b1309320601090501020c09040204020a030603050f100e2107080403080d0606090605070804 87
    0x483d64500040c5010768142c0a110b4015180c3e1060000204c2019040001001130364003484802e000815000812a0316140502440e4002940c00e13092044606192028208118907403001040003074590540d450320201c100e035000b1495000006125141e80580700000b021103494000390702d4241800c43c003658520443c80001c0425984079003501c071080081d48105440ea000030611101820b08200e0345000c0c010a88030140300445482181e48809186002c9501520507040030a902910703000c2c0f40c800420030760304031501d04814050215074800b4641015081404e04007410f0500d810210f00043c90011740e900801d0655002c80c5250071241e4410300b01a5004d41d0454000d0707038813201210210040e1900b640700034150322805040240c409000304240d8044a10100c3c1081243d4104030410343d607085689000400c001c45851240c0b911070390760010040c443c0140344051a0540e00e81d600303241507020460000f10300d50350768014003c07140c1c0f041c1072030020000c61400310708000603074075119494410b40c85 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 34044061 1250 34042811 34042817
    0x70203010504120e0315340f030b030706080103080313050d02060906070801080312070302040b040602010e10181e12030b0108010f08030a1805030307081305030712060203150406080a02030f010e030307 88
    0x30300c402d400c2500d401c045000083e1f042d500c01140380112000b42c02e058850403c8000300341004a0103045040004515045804a0f9164403842e4690345840074260710203070141c0b0306030741c0c00348014000ca0020052000410869801059103152024031b01c0d06002001d400f02081040d010010480320070000140c456080100710103c6080d07c41c14026402441207900c0103400c00008500021400d03019808160210b84810940b0f400c0c0001010201c1290400c010b203c981e400a00402d2000c03c080c2c003a44c15034440346044103900e107200307500c031500c070384bc0c0506203a000262900c4585000d541e0110b40e4500400070351541b40c0100f41491507031501c038020810000c040140f4000344101c0841040100c4000b401c001d000d50381d481da01ea0500508561080c00c000203803c01c045400038003424000303051002c40e844000040c901c0012903071030201940c4003814108800e000d06000541a548501c903e00003080510f00512101c0541d20526041055030b0040c503445900d090b10314240003c0210450342c1c0148149 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 34045311 1250 34044061 34044091
    0xa050901020c10030e070e160c0303090804090501171605151b0102090102061005100f03020714030c162904090204090c170702120c03070203010504120e0315 69
    0x1200403450305112080d61980b0a50302801540d6064055000d25125280102580d03401c0303440b41e011171640c0c1d1094034528822202c21602000451050300c0300d0340382e43c0c0f1034a0041102140c1d92500703034a54220b0f0700200d8030140d0360b0004111000303440590b42c60000340480506030b4072100c443c414005221a110b60341c09440c4034203254410054030400c840303140c44ea080040791030162000285000350003801144c0e0151107000e001c184980c2c02c01421808840d001400605024940c00c400c40b081c010001844041c16003d010181c00100c0d0341800005c0315203050015911b032541c04403c41c0c40d1400752199200c200040365000d110300c141e00c0138402c0c0c801720714004142c001040020a08514411580700e0340030684003150205500900c0d400145102000b580c0d101c000309806401c807002110241ca003070003d81d010501d8407020030424009031030243c0c44c10040d64104a11500072a0950f2821182103d26458114518140541140c9542401282900281550801c003c00c8890804000c0c1141c3d21040e804 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 34046561 1250 34045311 34045327
    0x412050903010207051b12070918080703020a02030d03060b0706050702120304050604030f03050c090d14010204060207180501080d0806060d18061a0d061808071a06150a05 75
    0x12000c0380c60412000e0021561095641403158a07180c0080c42c1044c1d000c0d032a00f607240039103400c1200090f041c00b010003030a80c0c6031030502d64500508048890b0724201030004001c20105146901a2200c14003d03009071407030038180d1041505081402c0d28030002e042c135103c4244810307141076065403126a401000000c1903214050280c2c50070381003415600010400008110070040b010513090f0043d803003600e030b00082c0c00141200f034040d940f0480740c4040d20714040c45525800c3ca828212002480c0c010929000c241580000071826684130341c1002d009070740140c81c100996003124141a40d09110220104025414218800d84541d40c0038224801c00c0301a07004580550ba501c01100c0002000e61360410040d2880d02d038011440401e14020380d40107160151442103444041229079580000030901c11680210742d5540e8002c080e6419000c8041170301402040c00200b034503004150150044440900c6901c914103106001c3c00020105402409042c20002d0791340c10220940d1000112414010740310005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 34047811 1250 34046561 34046567
    0x30c0322030f0507061b08090d021315062606060a170411090a09030e010f0203070503030906041b060509040e0a241d070302190803030118050f0601080412 68
    0x1041c1c2015014581c00d0028508105000070040b007101c1d03042e00c403094040059608020550912000900034010400101001d4908200040340351762000701885060072815217050211a660a858100762000c20401d0296541003d81d90780c074010342c1e55400f026200801c01e118400c0c800135001d81e014800114100000702e000d411000340009002280050900c0c0c1401c0004503200600300940c0181002404118212203500801080b0b580580701e011120007070b04011500240f04000481c114081070013101300041080c00214068403556008000d241004d080c4401602d10007100100d2140300140c1c2000401d400c10140e40302c6640480e000036440041c1241d0504048450400900729009032202c42d0302045160300040d803816540f1000c00148005284004101c0d14000300b101c0964064241000140b5151101100c0140e000c40302c10220781e0b5860340549160801c0e0040c149480300c92901c001d05c8080ca100f030f00d600816519240d045410210b0003e0030209000d440548480b8000411000340c0e40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 34049061 1250 34047811 34047877
    0x2030a0602030711191a0603120307020c06040e0103030e031605040207020103090f061a03010c09030809010e030a030203030103030f1e0c020f130e01050906010501170601021906020304060509030c03 87
    0x60034415a0540251104542680700e170907a803c642905c0d10321001301c807441044400e00d02c80c0001500504901805010b4680310741c0000b0079100440c450218002403a40391f03030b400f40008040039456040303654110300c0c005d05040580f110480c000da01c582c7c4036403000380010300e45408a030070540b80180e4520390390004a0192208040c050800c0c503440c00c0410410080b5404010002c00c41c400304101401071400701403c2e0f808407151000041e007140c4003032000c140660020108601c05040c0b0305042c4c9100d00c04241000d1550310b09402680020004100707064111021031410451451700c85007600c0b400c40120011080280d2000800449040e240c08540b0360f03030f111001c40b007001810311401400b6803450401800c410040c5041a5003014042107400340002451416039405850b8615144a80e43c040c52600d10002c203000d04602c1503142d0030700180340d07441c40740d201940a403401603a0b038549407c102081d6100a09018010f034800c0026080450300801501d912903440a40c050118032190006c0907024 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 34050311 1250 34049061 34049087
    0x130e041110020c03060c0405010903061d0a080304060b0301090215030907090e0c040605040605010c0f0503160b0f07081b0c070801060603060608090601210201020f060c09010e0d02030a06020307 85
    0x9641e031444804440d00050348110000c0101c046400c0e036039403c40c102c2040d0190f840340d01e02041001741d0600000b6016001350030307058458a44801600070103000036141c940040c0c0c06a424140000c248010b0120a0080a0364401d0540080c8081d000c1540030449a240700c82c2d07110764130740000c0042144840184120402410302070020b003c00d080e01040e41d0b03107801d1480b0209105624004d0700142c0d6092070b000d01002c89105850304462001507440349e45510180010450b040e00041080c1d0340d05d004400c1c03c0c4600c032401461150070618040413903c1d200600a8802c10030f0201c1c100401c1040b044061540c1000c183c0c0480c41c0e921100c10308246803400c9440d800c10344455003000c002286403541503009e002241c0040d9203541517074a4000350300e034807586d00b80547c1200112401e880443d01809605981d1818410320440c1e00601ca81b803c140d003090f07800da490500310348001407018031940e840b00303034003100f00003c0390060b402d00100c0d800642c3d10780c80d6600003000c058000c0005455071b80100c44801d041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 34051561 1250 34050311 34050319
    0x12030f0601052b150e040b060108070207152f0706050f040504060b03061009060504030201031d03161b0509130609020901080703060c1b03030b13020d02040503070b130e0411 76
    0x202d00c05a0a00c000d880c00d09650001440c1c035280c0000e4171002200c000d40203540007040708240d038903180011105404000c05d0841503114042d00045c441040303204443c5001590f60310300c1c190703030103141e40a824070344101c861010300b903001d0005c1041c05002194540403a406820001c2c0d03142021407400a16004a502c0b16a00c10f20304500001c20703a106500a5102d10750480342c24150160001090311100000e006000000d00c044c442400107501a40c003080c05c0391041312550050003d078404d4240341d9400004182180b0300010000c004001d80144000403404495613080b1000c1d013000045034030413400600303202c01c03d101e600500c030502c0074540c020891607401912071000b640c0c44048007035484107240300440e0a14544008030408a01c50824001d01480b40040e83c02d62101c142c1301280600f241b00c0d152548109455413140840d14540300500154444200140c0c85900e88401c050505406170300080c02124104200e40a510b03410130040181ca0030780301e0415130f0342c590782410940300f10040401c03070308 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 34052811 1250 34051561 34051627
    0x20d080601141b060603300409050c0a020d03021c05180303010608070912030c03120e030409060305120310030f060e030706020403020907090305120f0705031201060212030f060105 79
    0x90f40310240120b03d2040c0319822104c00791281c105065403000c0b856882c0c5400e0b111081c440700145142c5e0301e1842114985006203082544960340c5c1700440c2c0c0140c501c6044050000f40880549030140700384003084841d4101181003a0904001c0101d5041c0080704401155480300000c50028030f40c00c0417500145550100ca80780e60715160041d1a4040948843c0041214020300080d00701c5001044246143d0640d1004440307026940c00741d6001002c8240094507a80f1010220110103041001d44008c0903074032008260ba40c6076080c0241049841200950945001c00400c41021000c0d408041120307401004003203801e80f10b0902200a065030720018103d2302002605d803081c8001c035005001a24001c540f60021915030803020740b0200d9407444000c129400c802034115010302814054041550941000d601d892410394406013035521006e01b2900f40101d680c0103020307095040150301100284802d44c0c0d841d41c107061400000480c8d00502403810442d0020b40e10a40803210f82c6020b904c1842601d40a003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 34054061 1250 34052811 34052827
    0x30f0a1b08030105120a08041701180305090109090b0306160918020403021002030306030d180323070b04061d010302120f0403030506011706041d03031008160501020d08060114 77
    0x2405038020b11500384104d03c01ca151402088001c030324691a40e5002c0d49a510702480c2840b03224010703400500c260b010303540c2c4170801c1a450000714032f1384400c82d200e40e075030355a00d901e201d0016003000c0e002d03040b4610361880e205403103410f42c600044003500103040350941400521140000c0310074058503046411550503034200c2d811100140d4015000341c2c5d00c00c40da03c8104080b051822030b41d0f40400c80f000c0e0707410341c0302921441081f0b02a0400040d566082040064025140d403201d0001000a00310198120725118040179041c10130310580e8054001102d00300c0c9080e02c0c20100401c00e0054221202026148000442681c0c0c065411540c0ca04c125100043c000d180900922032070400440b02a0046804d00c000a02c40d98030030988000223501c00140070030705454200c00e01000b04401c200301c0200d0500c014021205a40c204050f61003151105818040d89051504903030402c2c4c00b510801e40d484018807000c0c40141c1e008649d85c884540d203441c01c48515902d20004861516444000c480c2114000900c0a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 34055311 1250 34054061 34054073
    0x2060f0d0209150a1d04020f07050309120f07030b1005090a0e0c0108130816060504080301140303040b1206150a030b010e191205010b030114090c01080108030f0a1b 72
    0x2c10340e410304496070010149070010440943c402d20911300d00043d201131101c0e4440201c0341007203100b48800b9100509041112400c2c103100e6129203c161400e5002140301c503a94503120340035000c5013180c2006400d660a040788269074a400c1d901008140f2a03106000070000100100310b14000c110040c821101d9080002a0740c00034203003043c0d011941d001e030f08450701079540100c41c3c072400f840400044a5012205856203c002e40040e189003000f4001c01901c1004941d0700d002d014041c90040c0d020302d50725450706500c0c03a2000c15444501c3e000741c10078130040101002c0801501d00c036040700001c100d6240d45003000200e480c9c1486000f07900f55000410801c40160380b59105000440c02a29414030700c00c03810f02049100b66008080000b5418500020700100c80510b10003030340d25100f8000400c2c0300f002880007a09480c0e00c40b04001c0f5009240f01004500c4500300245d1050210a0034061415418000e581d9180d108043c00452500b00c0050f004011a1140300d54120300001404079000400b03803403034a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 34056561 1250 34055311 34055317
    0x30e09011502010f060b031302010c05010c03020c06012408041a0405100b0102011e0c0203070b04110108070806030a0308070e0a0f0503010c11190c0905090705040c0207060e0d02060f0d02 82
    0x7640150700c1c00ca108000e2662500c60711042e240c07004d07552425562032032240715800c1040401203040100111070348000a5090040044400c2076481c0940c8914a91200c1840d00314140d108080e00d140300d40780008400b150f11500384601410f8030301705038143d580f400e01c0c030584645120b14070072103010f050402c01880f10101e078002c030250f5041c6050080660b01001217080e9421f166092210310700c02400701c0d800c1001507009086280d80b60058908100c41612100c150410882c0c0545604601e0211aa915a401001154404414181030415040103004695034003950b21004007484450800708071114099608150300d004003e00c80d44989848403041c21007038540c1c2c40b07000d02039800c1c251296000c80c05480c00d0080100604018443d020004064806000b030201c030a41d070300c1550140200307503610903011700b40c03040d004880104440e07840c010038801111482c00302c0e102150855038090000340d51100e82c07003403003000494241c0c01c80d0341030b4000a121445095050f4040206c00a0545090303401c40d005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 34057811 1250 34056561 34056599
    0xa0305060406060e09061905030604060b030106150503041101021e0a0501150b0316051c1b0509030d030504060f02220608010605090d05071814090a080412030e0901 72
    0x105100d030b5503030340101360b075048090252164007002580010700541854400c90000d071007403c075440b14460792035003c20304215044c3c505482c07858450a208036103040074040d5400030403d51303407941d20002e8481402000c2d4000035000072f10404c0b62960441090b131081000c002000003010354001180b41c00919940d4030b81428a00f11915400c141306420030308005420316040329280807410745541c0c1d030012080340c05044c6118a0040c40010b0104181445201e5800101d030a10b090000030510680c4800d014809100009041044402c100150a64074086269000c1040f241000b1a4645903403402c01d0203000801c11101d125403020816074445640e0109041d4074004003c24001c505481c0d4008036680c480c00d010b01c40210f1f03404c01100125040c07a01403401d00300e0094003a80c2d5455103c4480f4070000c400b641000030419200c404480307845c00c240007016045102c100040c8468103190707076400c100d030045124808080c0800c10010007818025038000c400150020020081d56840d440b95000007410704103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 34059061 1250 34057811 34057819
    0x140c120d0e0105130f08160b011206051003021e0109032907050c030318030d0e0106080c1f03020702150c0105220c030212070e090609160b04120c08030a030506 70
    0x3c0859031924003008a032103810b8000042d008a8003003030700c3e501001d9014040180ea000e10600484001c295000d058501810003003541c10200c90300d0341010015114040c00f01d1000141c80303002080103950780403614503d0740780c6000b1000f2651407500141c800000315403006e456100a1101d2a002252000c0c04011500440c1004c202c00d803202e90342104d45001d2841e1348001c6920030004981c1109201c0c484041d2000c5d0f480c102c80c0303401c00c548980b605480c40c03c01040016912032a080c014650280031024500c0819200c030a000c4940710300c0c0400410303e41c4189018561b0011740c002c10342d01d81da04400c12400e03012840b1580c5200314000f15000b04011900050a0002840070118242e180c04043c0c0c040c80d0005100413005013103408000440468240c0b141091017080b1000440c4180d080480c0c0c4070700740101c040c00349071030155501d41c20005d001c6500503000409801c00c0c400081483d0030f03074051b2003000031002c098854610b002000c0415680119140c0e1001045290419505401c00ca110340ca043d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 34060311 1250 34059061 34059071
    0xd09060b0109150801050402070804030203030c1c050702060d0b0402071a04120503060603190b0316030c09050c04060e04020702090f04032a060b030102070605070804030306060906140c120d0e01 85
    0x300b01000c1d43d200464000020f0b010600400c12841d0503005005902c0c004d041f40740c50650b89030300003442c0d940403081d070034030360381009460394640251084541c04d40e5803a8100b0500d4000c50350300107461480307100e640e000415903418103c180d6854560513101d0720b80e0700c803140340d1040006c543c811803031641c211401c036044019154004c2e600362043c42604c0c020070000e8400d90943d00c41c141a00d4407000c0841c40e45c02c03100c1d603c00a010743d43e43d0410000051000c0170070700ca00c003541941405010540d064011480c0c5906180911010711080c80c115000c032203440c0f800900e82c04032000024080d200324a4041d601040400601a691200c40c180034000c40c1b01e5158a030204c80c1c0f880b98403034180e140a4000e80852010440b440c040381960300140c0c00c1a8002f8001890007034250340340740c08c981d0160303010300c00999070008020030141c15104410241101d402c18808061030048010184400c600c540308480d400030401c002000c504014000c110100500c065448600051b000402009070008840303481d800c4c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 34061561 1250 34060311 34060319
    0x7050414011b0308040515010b0c01050105060909010302120309030a0305030a2405100e03010203010324141504020d0e03132c10080d0c020405060f0f090702030d09060b0109 76
    0x120006480415500c9440b9052025a01c0070303941580300910950f120b0140e00d00c00d151454118034900d0180c0b00304490300e92181103244112342100c605801c001e02030081040504847c1e52411482d40c1160ba0484160500300e1807080890b046004110302c4030b070103120b030038820820140c1080186208607002d10302003001800c61b200d21010b401e03040d00c40121904180b5000d0001c0c1c10821040c6103206500c0c244080500f1802022a003241d0091344190b5010144084013407113069092480c5190781d510100c01d101f885090a0f50a0300d44a006e499003540c20143d1b07403041001d80301e640503903288030191102001070520304204079460b40e000d0318421007050070200001c50b40c00100c9014821001c01041e40c0b44103541c403000b44010710b82014041075003643e10303070740001020101082000042c2100e80da8540550f040c61051200780c441c043c180c1407280d00b01c0c014004045d103484c03480b00103500301150841d089889015040e030841c403d04000704442801c080703002050042507005050308000a0343ca21400c1596 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 34062811 1250 34061561 34061567
    0x100515040801181716030e011b06050103060612120302030712051612060f090207030915031e020a050306010e010516050a05150105031207150903030f0b0a05100302030a140705041401 80
    0x9000c0d0448207a0702c4003c036203001c24420030f550301d4440418100741040345084051274190030103000c0200d410503141c03c0184100800c0703002e414024408071402c0d00c0b6000c000d60750032210540c1c50400d1010190f001c000100010b10540c00954400400c0c40100200d0030100c2514140100c0d40740044007042030410034142d18407040c800c59048450345000c203101542008480c2c4003030343c0700640030340070042005004550b0b000000303174150068202d03072000508204080542400e856004200c070031842e10510040d4040c03504034040b65408502403a0821501e07441500685160095025181080002c09182c1e41005800904a950540a0800c0700e03150400d211000007034200134050240c1503084078100d40d56a41b8100082e109251080031210300255042c022003040f100c0e01c08098000940755018004086164400d9000c0c00f202901c018190a0500e00480c558805084040007055030000c0040e000702c04690114400030f8040503000c010703052848004000340c2290180ea540e140b10b082d03010407c0d43c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 34064061 1250 34062811 34062817
    0x108010b0c0a0201030902060702062d0906030a09031e020a060b0a080a0212010207120903020f030a050303060105090303040e070e0108070305070212030a0e0a0302010f060e1005150408011817 84
    0x80a00c028031442c9099401100504410725040341c100001384503e50060f903512002d06a0501000e058060921605814500c4901202601103c0720020045446191118012030754884180d403000700c0d03800e00300d00d801c6601080e074543c0781540c01001c03120f1702d81840e800700e000142e143c0240028442c1d044440200704d14042c4900c9111416030280e07803920010304004810242059001c800141002c1c500c0e11000c203030a105548140025502d15000d00451515610303184200205500500714600d40b95034099407884060f16203810310001044a000c00c0d5410011140a807103008038103c00c5050001014018054000049001c00c0c01e403c001020f581c40380c400d0603c03a10503580105050211560200415403010700500142c0c0d44844482c820518104500d01e5400d10a500002e10f404640d8107843c11145240c002c020101301040a002020303150307140341025036004442c8001a950780060403c4144215404142c140d400d01400208000604660b401c5d0780c0c2c001c0c0458090b40307041c2c078601c00c5144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 34065311 1250 34064061 34064077
    0x2030c0d0e0610091b140c010203040501091505070206070302130f080709110703050706020a0306080a05070501080702010605210a02090a05060306070801050603040f02040b060f041a090109180b041107020108010b 93
    0x105e141e0300300000c1c0070b104000c03891001040c0c2221500d44440380d610079007079a004607020749213a916a0781c10005c0050701070180d05c010038101d07420491414801c000079141c040240842d800c0580208403002030a5070846201c0c000c148840c1000c180543c1c4111b05621102390344a900e44082c03406400140c014504001c407655568940d03509440d000480e51014003d40209500c0010956221000304a500081007600e403000c0c041c00c014901e09240200041800c0c800421040840e410180e08201e951150f445440110264940b0524814006034680e8a49126404080e6110340c0c1c030003c2c0301ca042e800740d100314000c10041e41a40c0a607174a03a00d05540e0000c00707100300c2d5001541000002c0c003040d00002c01d01e11051005001064911001d80040e403a0742111010f440c10000005081000740380c10032800c48654540300c001c0b402c2c10110400138089611070700c0340707a810010b042407400d1000203075401080102c200170030800441c059850700c80000d030041402203010030010000404c440d00041c082d250310f1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 34066561 1250 34065311 34065341
    0x303020f011a010207060c0804090606050712020715080402150a180f0e01030f05010f0c020f0705030a030e09040302010e07090209040b0118090b010507020306041a0709050a0902030c0d0e061009 85
    0x104e4501b100481704d481c05107a00f51010f10082c00042038030141c60141c0c0005020795640c40e0303180c1c40c1c0e41c180000c800c1220382c00503055612007032003003049040c01c5a50a13409003440c10110380d19500e50010036a05015a6620100484001030b100c0b05a60456210003901501c48407404107603882d21031000e501006405080340c0301c00345000420001c1c5404440d011401d109000104690341811181420740d005131003440050381141c103240384881c5003008110001c0c03004500411900301d044c0c0300134041c40306410384035000340c2c0040c0025003414000d402112500d0070101c00c0707400f4a544c5159001c020b41260b81d40900c1641010000d000130361080e480702265032100806088110f251a1040009000c02415207061007020300c42e440142e6030900081d84228040c0800304140041d0503400c2c0e4400c031004058005000c0707203040034407042d01e806200a0a42d46102801070ba20b0b110110890340c0350060340c0c0c000c1c042605184900c04c0340d40000c10000c0c001c1084001e10100c075500c03108104162407043c0b03882c6200c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 34067811 1250 34066561 34066573
    0x617061012082101050f04020f030a0b0a0e09030d0c030e0d030218041d0d080405030a1b0203030a0c1101050715020d110c010b01020c0405070c0f0206090303040303020f011a0102 78
    0x1090341218009060078854009146081c050540c01c01c0c3c0e10503420f56070070051031040010032150500f21441111a0307000c0b01c0444c50b102c0c0e4022801c441d80009062a5a001e0b920340100003d03855414840001d403e480340c03402076030700d04400707042d64903804070000d900390394242503134503003400e00a0064503481000340c03003d841e004a20304400c1f4025040b946284d240c903540e014500c501da8980e44034010b01826940071514100b041105001e01d0703e00c0c2d800e03e0404001408d010000418030100580d01d55006519100301c480c0d80c5400380d0f0403150003c81c40039505000020384110241e8100c00c41082491240ca01e40d01c90300000001903c0600800c140941281c5c1c0710342d091410000954020026000208000910700d03002028000240c0c11003d230a131850380d505c0c0e252880070360701006002e06c2c0035811541849a07150120000344403464130340d001800401107200400465032200150740f070025001c0e00b01c9845960343c1c200203660741d04c403042c0c041c055440c101d840600404419514103030b01c841a002820 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 34069061 1250 34067811 34067819
    0x201080601270e0412020f060406020d02040306050f0601110d0f030906022b05280506010320041707052206150f020c0108041113090b010906170610 65
    0x54200c41c00c04050305042001c0b40652200ca400d41e0302602402180e42c8580da5441c0a10f007540360071300130f03e0300344003950f01c0444c50300561400080c10541c413643c8000c001d078444000010103000b03800345800c001c100d81e0625080000c1683c0258400307105140998a0060301c00c0c00c0b1451580340d021110700c1500040c040640c0c42c084c0c0d40070380c0080c1c900a01c118001490180ca041d07400c207844040f5a40710316078010f0300400707200302c11560142c1da42002c1000110032040900d522801c004401d0303007003000002901c59000584581c080e0b4440c0381142ca00003166010418183c148000e160301c81e00408a50302d0059150b84010b040c0081d5002c00e44001601d0007019510088181c000400700010004640d07440e4000030800c000101d58810040c401516a110742d5404800c010741000402500e03941080201d100f00300c0459482c000040700c50800391181452410102d406802900e103101c0040c1c1810044070000411921039032010003100e03000f0b02c0c0c4090009550726525128502540c070200401d0f1851000c2c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 34070311 1250 34069061 34069067
    0x270a06030c0207080a12091a040911070501060e010911030103150203041407082d07030303020a02010902060f0c06090a150c110f0105010503060603012a180801020702030c010c0201080601 82
    0x1c400915540110340310107075211051442c2c00c2002c0e00442c1d9081c400213886000c142c101580e00003615420010b6084104c02d515200307210b01a51081e90714154072500142c0300c41380100304a806080c1c10600a011903078403150402204542031060402c25032034141c80908a00f10f48090b43d06880c0d03c901007207003000c440104400a50406801915814a5034000d49981001080914000e00000b00507214641c0e0320711017005802d44076079020080781d611148200d010500171600c1d406072b2303606007401a01c42e2000b040032401811045002034020b4000640851055402401b03080480501400c50721107555952400380c035500d80d4400144100d0300c032544d000040702c0f16004409030865900d05190f00201940c212841c114103604115040c0e50f40740d00500031400e040c04805e0703100c0c109030004e100c0c1c0e10452008101c10300d0744115640c0010002024001640e228401244403802b1000c101024503032142c00050003540840303c200d10900c40c40f019102c165003d080b00b081c10382d8050f1100d00042c1d403044015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 34071561 1250 34070311 34070321
    0x50a03020d022706040f0c02060a050406020904090507170d080c0d090602070807020906010f05180303190807030b01031401090c0c02030319020f071401050a02030903070308270a0603 80
    0x1ca07840440721000004a04450f010402c0c43c00c111801c800b180c0c1051410310080f6800200007810300b50a200440f4040c0380c0024071a034101070401c05c001506d59940c104a0001d004012200d9485030420411600340080080e00205079452400690004442d880040c3d546000040041c2c0115a0103c001400198118058515400304510120301003c16650310002c0b030344002c5007145c02c0a00410b481e0290f0500c49400f13944800c3c01c0c00d2651694001250190050050412075810900300c0034640c2d00540b002d00c140d408040600210034922050218094000312040f1901e10019241c01c1e100102d40d84640280e881072582002c1518080e401c140010028061a2441906001500b50300c180180c42c2080248545c000d9031030703120b59030050000f0080c01c14103c8600c4404e254008035080c0083c84c00302c40e4401240030309080060351040c68850036421800703a02040e42c3e050180403c00828401a10001c144601120f40c0d100e10070300e0603501d070401c86000440c20a4100d9201e460a01c00c10b8040d030305c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 34072811 1250 34071561 34071563
    0x50a050909010b03010806060a03030203090d0606030b1e24040b010302280e03161e0906060915030e0c1509060706060e0c070b04030507061d01090318050a03020d 71
    0x295150801850229101e840d0a034803460300840008010040c00d00140b00c0039801406c103c03000d001462954900954900890380e00a11880c80d12610108101c1950302401c0199402404811249040c002c084d0180e0566004003d15110030000607c3d6250740032100c919050055489424191403182803200070810b040200e4140b6a00308890f0a21003030b40800d00c0c00400f100c0c0d441c540c0d180d5400e04004c003008020043c843c081d611045071400b89071180c07a504019640c0d080c002d0b240e44500d0390121040b008c0d080e0b0040300154640b1b400800c3c659480213900c8140c0c0c0c002c242604d1001c041c464200c0031101140e0b41e404a0741c0103000000c20615100c60360f421100902e4200e542040c409000181c3e4941c44400d04856050b0343e000200011000c12080c0c075408a25680d2103400c0078803544814142d600c0040000f020490001105410001c0350707400000c901440c080c1148080302603c20503802443c0e030b54015000318814403d10199030301c1100007c01a00c1000d01614412803560342071111036004094 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 34074061 1250 34072811 34072817
    0x308030c03100902070c090b041509020d090f0b010602010506060a02060f060a0506040914010603020f040b0a02160311090f0702070b0c1005040b0103030305010b0a1409120f070f0801020406080403050a 88
    0xd001860a00f1400600a03e601070540c0031401ca00e415445000c460300045428012410901104080d0044120076012a50880c8001d40d44050002c4001c0090004805c01802503440e864881c1c2030220400c2494107030b8000c0d800030002c0391039000c208000c81c00380400fa10300680c4840c9c0010f810b5511558210707008040904012541504c0d080011030329007040c0c00081596540b26440c440d4524040704840c010006c50a0451504104207012403151040c5d0055001d48207000446880700ca00c2001948200b0b45070100bd9501103889242810229815084091045503501c01181c1000248401c0d1801000c00da00244181d41c1b0300080000701e60040b80da03d0200380980c14103620224404d0081c50703c00c51050404510960440c13078040c04680701a00010b02000302032082d0010942c0018445030400c100c412141e48802c121400908401c2154001c01c00a00404005c56014a070000307448060329242c1814203545c41d19041090300302c1c002c9106040004070360b50b0109000c203001e04001d0001e14064a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 34075311 1250 34074061 34074091
    0xe09060f0f0a0b0a0905090405190c0302040603080d0b03011109040c0e03060103030f0212040303050313020402090d0501021801110d0f0207030501020c030403060b041406011b02040905010c0e0a0308030c03 90
    0x100000c0c2c11205560300c40650503800003020102150b001d02c03880060101117072226400e04007515100ea0301c081e446d400004c0740c10140400c00c144a041894480107590040c801d0021680360b18100c40399401000c0c0c5075405500305086225249010b000f80c522000929990504004c031040400000c0d0641120395001c0c40b1050b440020140c80a10016020b54042d803204541e100b040d04001b460514600c110045101c1c09010500000e80e0010881c2d8000c500c1c0302612101905500001c0c009214081d0386d55442a0340003866010408190068a03000c5100fa100c00038050020005440f034450400502420b40c2165050302d00c518018169200e181d9103070f00c112202ca039201d0355510b003280d2126509900c40c1d07201241c100104002402a11044401900d050001c0181d0011041c01108040d1425042c829504c04031a4040c00c0002e6880070607400400500010449041031402095821182c6001a080700c00300300c081d0510b107200c01c003141e078401c2070603103145d84004050303815400c040c05010a40380d1b15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 34076561 1250 34075311 34075339
    0x151406040b22020a0207150c060b0616050705090a060503072d030318050604180e0f01180b0f0105010219050705150c2a0111030c030f190e09060f 64
    0x24841008a89007200059a40d42c81c007401900e844035541c407c8a00b140462400d94203d940030340e5100891b6440040130031030700f1210700090724900983c1d0070300003400039030840d40c000c4c81800a41103080b1141501e07016103c1d226aa1040192242401425015804881d01300501224510412289115415805010241048440084a6560301c2034001a50744861011a14056800b0000030142250001d161505e0041684030303c80080c040d6040455540c46541002082030009082e282c10402c000c0244d015240e06000071104200d0003600d000c64114000303604901820b00039810707100141c00502018854102c05081d00314402d400320350b18014884000341c6a1980201000c02030f80ba40895503e0300090b00300a072500360aa0348620b5407084a40e0b08404004408428080012003860002010101c0c4500c10b4510303c62890300d109a4403000031256440d0782440090300c0701070040b8420405c01041e00c40304441c01c240745072440790b02ca420b00c40800c0381e519005180c184101c5001d0040d07800c003080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 34077811 1250 34076561 34076599
    0x603120507061a062b09050d030b0103050f0a1805010615030510080312180604030f030506040c1d040e030310061b02010203180f04050a0b03010608061005010309080c0703050307151406040b 83
    0x6840320884807540b1a0231100001601070140c00d0403020300f8601000145000003c0c4400c000300902050701d501d036100c90b14040d02800200001e184c6802c80020300c0040d541d1401e103032259082061410000e403070000815441e110482c8a04219082c102c0218103008090480000096000d41000c0c410040f800b1a66100c1c00c090100d01d1189029440f003144000600c01d014043e6178000300002c0c403862070b102c5d800c2d001c603070024101c1010309621100c0e0100d4185200118005002198010034a4403000c4100201c001ca500a1441070764040da0b980f50481c43c142504407116000c00e54000e015801c244081d6038032414065104038800070042600c004805082d020900b01c440030388405ca010f5494036602c02d1213007401d0017040000c05600c0018003c0e0306d01f602c2555181001c0340140c604140e00d4600742e40070b00c800b010566801c400c0c1300041d0b0380403950b00c0c50700316580d40c0a501c0440d0311a9040320394103112100c920424200c2e07203030000501c1c003e5403103d0410004080040501d507216080044008821310 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 34079061 1250 34077811 34077821
    0x11031c030b040609020306030a0803060d05010e0a02010f0527040b0d05010507031505011b030207030506100f090612060e1f090b01050a0510030b0102010603120507061a062b 76
    0x4a0349001515801c0c0c01c0c14802640d5040c1c12405030240100240192510300282d140380858110701400c2d10380d120400001d05c07aa080d03600140096003081c6500c01e8101c004a82c0c4c040707180c0300340c8812000303451840d0262518011140302d100c1c9101c000b011104c40001c6103503410784800b0300401c001036076110310002901d40f40a000c020f5684e60b641c0c60401600795014410328000c217a49025203080c4500d0000001c3c00001d0030740d1840106907004803c501014020803440020b50b9101d401c0d01c5a6140950700000301403007038460300d840b140141b0000540c0300003070f220f110b0554403054800c07802032030310341c5807d00030f8030848882c090f00c1c0c405c0c81c00c0492401c2061403500700c001d100610200c0c2c6a14a03007440c0400a0f81038000c20302c00c1942e680c04000039585d07403008200c4020182000f007049001500141c2c010003041d44090011f48a24460f038481e5980b01e0000c248040c031412041000e1180c0c00c0320b0b46900d07070401000d56000081007040440e41070300c1101903c42200703100c00d40d50058003110b5800d02511 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 34080311 1250 34079061 34079113
    0xc090504050c0612061320090402090a060203071a040b0f090a060e030702010e060901050a0809070b0406050901081008061801020f040801020715050c090d02010507120e040b010503090a1103 83
    0x907910f03101780b007201d1401010310320120a154009005c646440d403c40150080d00481c03840302c200000a03194002c1e15150142c0d04078150003030841100c01d171741e0000a900d07540112001c403401e160034440c2418420346508124001c41d00031044000966610030f4044c00042d000e00b1b00c00f0b16104500807400001d0312400768100018240c2c000c0c6468020603c00500640c1030629610701c079200c2404911241d99028003650911801881d00101a4451580090034074603207401c888280400000d0219106822030010908444203a03a4030240da80c607010801da000c40c241c0962401e40c2c10000100b07030044203111000e4060782c0000d00062410b00003040b0303c141c90b84240d01010707c40c2d4011400f08144406084085590392542d8ac0902941ca042a10013249100c0c1c544410722544801c8100419a4824000d4802290340011030000300034012138007505980040f03507110b01c540d050051261035544900d054070f00900c00480249101080c0395501101c040c1c1a1411507014407811210030b00c42d01000d101c91001c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 34081561 1250 34080311 34080337
    0xc0501060f06090611060f0403050f0c0a0b0604020c06070513050901031a09030f03011203030605030a15110f0d0e01090503030a020423010e0103050a060504140a0b0d0c090504050c06 80
    0x510b01d09a005042c004080c3d1140052200b410402030040c1008241360b40e104400510100056540d1b143c2613480d4010f12000d00040710000c205c08808101c0016042c00039030141600c081195038050402050348191500c10619030080c10105040300e008034081c182012100c1100c0c100d0903160008220940c00c268010380328546800c0d81300700482c10100c9520b0b007003522903000d036207054804603040a2502c01841000703101c038802801041814420352100d80a40402000e4a140000c0307800d14076141000400d0901140d803030480e9407c034813621030044620003450310b22800c0c109100014610010100c02600f071400395200c48035400040c8041c8002e42c4150a0b0382e00040c0c4540c10328a80104038282d4100c6807031041c03860803034445940c0e00149010030366882481e0114a5640c0d4902e0000030b07040c07960040d42c0060520300c00a004013940d10b20580300b01000c4c90304010303080c05001040380182c10100c015016450f070100a01c09614944c204503031150013001141c1a1400040220700103602c050740c07004032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 34082811 1250 34081561 34081589
    0x110d0c031406090601081503010617012408070605031902040b070c090b0901030b07090b1603030f110405090709080d050a020606030a08030a15090609021908090a02010507030c050106 80
    0x221400410400e0b402c03003000d90f18145203180c42c9001800d050409484420300c480780b0800b10840340e600f50861000790030707945561088800c603200c41c24080d049140d14240402d4154000e0380c0500105070101003120070030030083c0502840c141c4151003d07032024240801d81c0d11521803d0000650368002400140f200617030301591030002d4180744200303600e542c11003d032369030a003040500159290000d050540341c003c0c10350000c60f03e901c030f41600d580e91140d110007802c110124017000c8105407400d203444054040e031410f02c20004001d0784c0b0021613106003403d9038254000d00060055080520b00150f2040c1907081c45000c182d1200822460101645c1321100002d00001c0d11102040d814041140c2103182074002786240000c582d074001807400018100260559511404c0c1c845a25860401008081e0f1520410220391200e1166003e54400113141c40f4008464122440640c030a02c5010310070640f4002800c480d8940b40c1c01140c075079004080c141d003003150240d504004100284203d00051813200d40c2e51395 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 34084061 1250 34082811 34082831
    0xc080d090f0215030402030a060b01020307051204051905090a090503040305120301030c05010c172b090302010b01020a05030901080c0904020d050103050c03010e0c0f03072c060d0f06110d0c03 84
    0x10003600f89480003d0380c04041c014040103803000180f5115a5a00c0003000c40e60810420040b4a1801080d45c0070744244102440317030340c14545101c01042916400e075015280b4a603031102d2010a4003240c407850303801506400002d04041c100c1c0c1d02500c102c41c070917800d4034501513480c1c035000d150015000d40c8203d00d00001004004011500c0815402000c0c00c2c02e005120141c0f0761202c80100c209107c41218081000a010299490080a10038170042002c5254414101150200c00818022008074050f6182c80126076443d030001034800b041c03540c004000d6242c40d0405004546017a0080d080c82120703041400f030a503882d9110b0001d0540f60100725000500c82d891800d0040ca000b1004080501903403400c44075500841d0003180c00312201c20709403820181d1142c0400800d00c1c04005510141c0182c5044141c0c40465902c410146d100112207510380d04591620310070031442088124000781509140c00d072240c00035240d40c012200c244806041d280c140182d03401e0000c1a500042040b6000075038079001c0c19 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 34085311 1250 34084061 34084069
    0x715050a0f060302030307020f12030a0201090b010801050907030f03030209040504050a060507080606040509090a0602031801060503160905060a051c032a0b0406090203031b15040302030a0c080d090f02 88
    0x8000c1c000d5140050045619540100f503c0344203040b4042d0041b9122031034001d00342c03901c0c085105048912403c0b2540c0c1d450002c1d0090090110000440c1c85640d01c030000160307030105000d281d015201c0800a480d209146654441d010110303e00d084050640a000c950440d81d241d109551045d4003500261080f044540741c02e008450b00101182c0600c007814041c45810b84802e016202951415200b40e484c2d612425441403610400c40c1c0c00400003400001042040b08005403007504c04a0200000d001c0942c88104054540030315444141c00e240020350204803c52407034110541100020300030b0044180c450780886c2d01d81c08540910036940029941c00701c01c05601040500b0b600c09040c01070103240b40d8010320302400030003004019001030303020008917051000983c40004840d6004040341c1d52103111040015403000d03c41c400004a00911120089043c6044043d0f4401c1e545503018526044c900741064a461071990029203121006000d000b10368909071061241080c051b40c07860a003201584100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 34086561 1250 34085311 34085321
    0x7050a0314040804150f0e041802040c0c0210030e03030c0325080108070603020309070302060c070e01081b0f1311090a0b0c01060b043006021204050607020102040303140a050715050a 80
    0x8810401e441c9010400940e2240c1d1f0320f1491001220080350300400869040000b030b502c03d00207035000d031a002c0c0707040303001d074006020404481c42601d03054449568240160110f401518440c400c0e0307007040002480124151000f580d2080c0c00000e145804e0040f1001c400200c0000042e21011070708000040c0540f4404001702030082149140651851a00c1082113845400d1480002e020351070200e502c0005110500070807010b040d0340d4107000754969444007510b554660076480700409010084850485051401340072440e50005805d4000003440c00c0000b000809000700700c05000300c024019102ea80e0b403035a0344880207000d41e20104d070301c82800009050071600c00340d201204480d002c1104208600d074000741c80382c29031400540081a20030941a640c40c8520404004005600c0061202c05052054a0745e5000b980214115803090381c4480b000d908038812400003401240c603010072202e060005d00001d1802d42c000b0700d8040d00f0018180d80c0c900b682e5403828110b11f001e5844004120901c1030318410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 34087811 1250 34086561 34086599
    0x9061a030703030e040504111915080f1602010f020c010204172d0705040c050307090f0803070f08090306040f0b09070f0e060d02060a031406040207030807050a0314040804 75
    0x141c04803a00c1c6980141010700029401380c00b40745c590300004c050100b0781a0440c140003001d8001c3d031a08811051124045456000d0b104803400c00480245d4914400e82d4940d100f038014620410b8140c03035901d100e41c15045000514001c66480c0c42e04125034100350b0000e010011485000580c40301c0c1411440048024038100b107105682c4505a10240c1100460ba080da010010b111071840a044600708141070184507000190042c0c2011941c0b00c2c2268020001c40c420802c69680b50800d80d01c850030350798841c0d075900c580652a8030600156020401e400a03c11441d44941050fa181c41010030100781000340c11681911070070805170f000e00c248500006d241c0e0780301c002500645a26800c1c252120701142941c00f410032058421000950942c4411501403510758008250540b00c4001100003006040c0b0804140351205161000c141e1a040a0080d195100d901d6140c0e0740301365072620b0040300c3e69080015640101520760a07202c002e516010f103814000c03802034605954403030030701c90001000328007249 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 34089061 1250 34087811 34087813
    0x40509010509030919030b10030b07090501050d0209060912030a0908010209011b230c030f0a0f0201050f0409060902040510020c180901110c07060201060512060402090a020d09061a03 80
    0x30001e141002008a85013000304540041e0a185480c2c0301e00d4555105400050514040c00d051084001404d820f50007260b205202080083e5900314080320400700314410035002c42c8007070101e4801d242c41500074062040c00900064100403040c40081c0c100804000800503542000070000c90041d40400d02c803000d0300c0241d00942c50418201e000a100e071a400c5803251510211020031402c0110740c02540420080324a40205071001f18030140362103100060071540b2912030240b0340000030701c01144992034542c02c144450011020303500151a168011071303024000510400000c00e40c90390512442000c0c29040d100140c0720380c00c240c14083e50f0000c9e58a140c00b558041c0d4088041c40e51012a122440c5100b51a1070b441c68480d528410301600c440c13080440703ca400464100c021403030005d0b110381195400c1d8001d0021541d02e1050100036051011189c0f1990002c00c006809401c0102100f6089020b00070010b160800d010440000c996a020342255460344a1140041c0000390704d0003440c0346d40040b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 34090311 1250 34089061 34089071
    0xb0303040e0c090103090822060f140f040807060503060f0607200103180b0907060309050601060c020d0b0106080a0e03030108101802030f03040305010e0102040510030905010f0606050904050901 85
    0x1040d641a080002800500d44240020b400f080592194220000c20ba60102c00c05841d54810040a10a5400100b95082c0002a480001483d40c4a400c6400f80e030250b54171010500b241c03034a080b00ca9644400c004d810844c40410000506100400c04800141100d070b03140398590504c50208500b41d04086c41107803203910140501c6000c540000210940052440d00c100c2e98444280e00503009059960049800415014602c0051003002c5521074440c0080c0c0c8255040b5540b00c04c800d404940e126038000d03181d40c0c4040b0040c46090300907400001a40d00003008812001816580c0010882c801d8010b0700000c2d00035424040203411a020b1010003090440142d4190340c1400c000c90f584034a100d1807a200d20b5116010030031080d540040000034143c01809444440d41900403440d070b02ea1091000303c03090340ca05903810fa1105030610903281034441c0100b4001c0c1e40c00c0074000c110083c00300751070240c405544e83c04801c03100a40c00c0c45224020320294603540c0d2555074010030802260001031010245074100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 34091561 1250 34090311 34090319
    0x10605090a0b0307121a01080f04050a0b07121a0909280f1e050609030a0906050a050d0e07050f090408030402040e160914070e0a0314120301030c030302010b030304 72
    0x20190020740782c0418059071241e4500f501244d001000d69045186289803a01211008491030148184982c00707803154007150b16422844000c40400325805401508104401c40024510300410f5822482c24a0100c1c1d52a906e842d03010100c034150781100c0c81443d402840390300e0600340b8122465005d40b085014102000c0d500d0940580c1c851018480300445a029404804012415100000386038109a800d030800d03c0314503082a85801503002070b149031242030005000c1d518000100e4801c0012030741c2c0c114903d03140400c10f60302d076040f1980724400d0000500050020034054803525101010480040482500c2d03c03040c00412410004500d004a80c90300070480403400300c030126a000795042d0380004034003411003032880c100904000b48620700403160311f000940c5070958000c6148001d200051040e141c860240a603174441304013014a401c00c043d400f041010800501c2c84088030000507003900c502c540702c80741c00b4100380e100341c008803001000d207542401859030905c1100520b04043e00103518103820 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 34092811 1250 34091561 34091569
    0x504090e210901080106140c0109050f010b06180906010302120a0b090a06060905130902060f04030c0902040302090402090c040503120d05090c0a14040f02180f01050406050f0d06030506040c03030801060509 90
    0x105005100910455140c1c100b6587d00280844400f042c54000800602e071451170171507110b0141140d5882d0940c208102c0da0700524100c0304a5a5a40101b82441c0e5110b42c0300c2c040c040c1031080103143c141419400d200143c00c00c1900c0150038441d1410a400240f02c0000004000030660058844003d4038682001800040e0f0000d1600094542c12030352046e6000313512404c80050030740b080b40250401804540c02ca1300b8000306c405403050324400e201c01410192112841800ca00a07848023175480401400410050706001082581002800000e1881c16440304086450140404035000d00140e0005220001d5051842156009414074000d841c201250b00c0001c2e60a0314079000f0640b500d80a0454000b2036a01c03980810110640c40400755119131480140e2aa40f040d000303035050017200320010b0010198481e9044509481a50311040c0c140040e22001c0700d03d80c0c01c9640e122a1640d40c603d40440031410400c0200d110380d1040385000301c29810351800a00c0c1840c10391003801445814045c40307480d552 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 34094061 1250 34092811 34092827
    0xa1703091c05040314070f03031e02150a0c1e0509010e0a0e060108070201150b040312030c08010b070804090e06070915080c071b032009061804030504090e210901 71
    0x508401d200c03110482c11170710036061038072a0b400b0882d159441d0f6400004c142e0040d50603829031220713104081882404000607602e40000810580c0c0d1039204000081d108103103903015054120311403a10a04090b8110b0145180625182180011680c041030444466a2008400c10500420b941405081345002865415000301500090600c5240800140d00e240300750b04c1100d00542c040411441f00340d03614a01921030303105000903501c100c0480243d202d0f1038081c1c000c0f01c04d000030594a14040c0e83c0b0f8030140980c01d800c0000c085a401c8000c002c0042c2182d003a00070148800e07500780160466050001016008030b00381d90100354103903666044e10310000d4014101d607a1003040d035040d1540e40c05051401001d40d540040c14091503a54207000403007401805880045207104526425602d081c00c4020090070700300407520140e020f6031760314a4480007640c40031510b800900c0fa007400760609403035040a10941d045002e8100c8107601003400503404124641000342c00c80c1001c0500c0e4036180d06280000e2110b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 34095311 1250 34094061 34094063
    0xc0f0f1c0203120a17060d031d010215100e0f01060504090c2f01110c0c040902030102090d03080906060a05060702011805060d0207061b05070f03020a1703091c050403 73
    0x2003030805910040d924140020700b41c3c0d80d1211500f40d51411a000003400001d200300078504003092000c0020303418203080b105c146040b034150b1035641d0449041c40c03076180d580700500741141c118010100c1d6040310302c034841c80082c003078040c691403902c0d281d0514500c01d0381c00400a105141c2260200010022180c10030116400c0c3e60b01c6c000b0104020071443d1090f00d56129603039088114003401c1c2c0211905210b207100c49041d0b102088000d21008030b0550021145003d4415018096002804000e5152916521140455101500150400b03a408000039221442c41e001a004103002d00100b10354800144141c2d0780c002001c035106940c0b0340c20312011503a40d00070011b00070306004503e1490380c910380d4002c3c250f10042c0001400b065484401d0301c1402d01a402001c2d040715860704060714507100702a59442c1e165002a2a61000e0520741140c466425102c01400c054007580504440c40011411607000501c4510003000700c10741e641054040310b4600030720300030388000b0b10440865102140c0d072f02504881c101c17 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 34096561 1250 34095311 34095349
    0xf030a03080a11041d090c0103050121051e0609070503011b200709021b06090a15152d0302060405040c021e0a03020d05030903030f07020a0210020c0f0f 67
    0xe041c07a0f01e440c040500c40c41d04061040102207000e0b06203014040d012502c43e00d1800240c49140900d01c0055081c2da0003801590b103c03003600c404400ca43c0c2d403c10444032045000b04100c4290020301521640c42d0714103040d507280c4a801c94030411120000c00c014210003003900350020040610104a1040d901e580714105074208602c81d85906004080440190a4000f241d42640d000c03035561002500203500c0703072680113801403100d00c0409100c50082259480b810a4201804500d00343c0c0d6a15086000004040b007100c40d5035122240007901200d10000141041d07190208031030010a40003402d560340d031902c40340e06090ba8141400140c03500020f80302184d0b0f0a4074007040400030031030240c1c10b09080040c80c41c80038820150081c44220002244080d07036010707070241c40400f81b8003081119280b10440d00c1d582158010404035802a0948e8900355006002e481550240b410342c1c0d001500103c0c040b05c115005a0100b400031a5501e0141421f139102c030340483d090b40c0081c50200c0801c04030b0828007203800b80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 34097811 1250 34096561 34096571
    0x6080f10031e020d02041b030b0603040b0109020f040906030b07030e0c010c082508090a080601080a0f14060405060103051002090a05040911060f19080402010c0b0403020708030c0303060f030a03080a 87
    0x11500d4500c0d00d80c135001c2d801001406601c000c0c558540c0100c0750300406000080c180f000c0400c9504001088a0156410070031841c104e07130a1404140c080e42c0a181018074103401040006000740a03442828040e622442d0b9001e52414828801800c0d50102c507542d140d2038020080308440740e81c10205014042c1c0e8045022900e035180e0701c107020b400501000321095115080d030749000401004100801000800b12400080f0036107401e90641d50340d40034003030044a9401442c2d400003140245140000b018414981c441b42504100981410b0440a42e41100e00b41d01c43d000500030007500b808203100c1d080002c0f004508260800000a00f0300e482d910407a4012503441e0815800d010b41d031100310010a202420041ea114002d004441480c1e11810b64481d40111244000156074400c4160341d0043c2d80503558216079045584801d48100e00150044040d403180e0710000070828000e1002d80200e004031009036403245424014008a809641c000e01d201e07801c030880705c50000b60481c03203050700b240002c200056 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 34099061 1250 34097811 34097813
    0x405010203011802032208040902040902040f0806060a030305091c0b09010f0e03070201270609030501060503030f0405060a0201140a09050c0a1508090f01020f03011d0402090604090302100606080f10031e 89
    0x56070704c1072750064040d5a00024020481490b01d800030800c407229001c0004005948140060b210b110540c1c219078400c03074800040000c81d119001410121a0092440c142180d50482070030385c5200000d401c0310190422402c01c11215400c1c4514102c0c0103040d80d0900041d210401c21603168400c040000381488041c4481d1108110549196a980301006c03008410098441501500b0300c24544000c40741d41d82800c40210715800e000c0280d6224454183c074aa00b850705200801c00340f50400c0d00341004542d40d800c411a00e000501c03c0e400d008144030100003c401075142441400c06504501143c05607490120070050707120390314040410300e01c003890072201a48030003074521306050200210700180d40c0086010006c4485210040d8100e81d4404003814100c0d030320181c8180c00b80c43c104e501030747c42050b8a000031300d5803c044e003040551505c80c1c0b0543d00c403041200046800c6420341d41007200040c440008000c9a03d20070a03c282e0031114410196001038550341e079170800b1005480010580b101a916104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 34100311 1250 34099061 34099073
    0x1180605040c050316090602120d0f05040305040503010b0108041e0f080a080a05010501030b01020a021c0803040f020906030303040f1b0806091005010501030c020a02090c1204050102030118020322 86
    0x1001920005200388401c074507100c0b0040594000b9a5482150b001d5107441001d02c500803407111084a1064014100c0c12411a9088406402000503014240e0b210140c2c0300c0c81901c24800c00348110701c0b903241c4035111800c0000b49800c5903405030b69181072060a005000100d000e100039414074039229010380800084600e8030100c541c9400b43e00400b8483d0201d506515107402890312845000c9500080001d40ea82d400110103403003900c01060301613041120400058185603d80c141c402c1c40307003d4241c6c000d8032555121003041d4001c40d8140c403031440c40d844d01c80442c5441d4040c290446001c500840c00d5080075201c1040609040a0013004a0803a1080000c0c80c860015150000e280070b100740e410510b403002c00281c0b12a08243c540c40d00a142c240085101e600900c02d250b4140c095034020021030041e6420f101604501610010310712005000003500c290302e41e580640b1551103100091380320351405c44d505202c980c01c02c1da02400180140100704c904401903e400482660f000044c010400d00c43c1050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 34101561 1250 34100311 34100321
    0xe0120090604030f0602030a0c0f050a110c13020d0f020a320304080304020a0501020d0903060f020d021605060a0b060d0209010e040203090106051c03021507030f09030806090f040b0118 81
    0x1800301c601d81040100784541d0f9800795100b6003040006005000103074070100d0f00e882c1c0d808444004601cbc10701041c001e5900c54a5100c01c2e40920b0340071070b04403010080010340e14002e1004100754084d00003c1c0040f4030a010302400c0d21072020341000b9800d120721280050600c0e81c000c601004403000c40e000400c0d040d00400004240c0c40e0201c9a0660780b41483d0074113480c00da100320342c1030307000e154403000002e2a07520000c0c1d0a820720700700c0d607944041c0e10306590f100c0000d80307001c2c1040c80270a50280034848107920b80388003c102d0201180f6040c1c40c2c05655281c2130b03080500c01843c92503010b1610b4110102611000200ca100c400400c00059a4031030301c000588d01a0301c2455000d810a1010080140ca40f80552154081d140d040314062070213207002c0342c614015040d07810000d00680000e24501c0a00c070400320f0040e048051401d01041d940a140d024600f10b500d5010150002240d0f40144200c41c20003030f00c0315030041403030b481a01440c60a0f0f00c3e8080811018800c0301858440100041080c000075400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 34102811 1250 34101561 34101563
    0x1401150f0311030403080411010e0603060105130305100603030f020601150c03020a0b0108010b0102010605060c07030204150806040615060c02031f240501030b010906021203060607061409010e012009060403 90
    0x82e15103909142c1401450b06400315411100e451098056002660080e1000b8086410082840b0320355134880004444942041d4215900c4001c00100880029014482140a4107503001c000a60901d1418010b00c0030742070f140924259002a00107102a02440341d030f008504052307007890402042c444c40c04a25200003141c0c040c010f200801c00200f5802c0064124a50440b07090f4000d11005403280100900ca1203540b0300320071158041380042005080a0300031400b81d502c046682440306540301c26242c140682210121880ca64030078800140d2501c407400c02010b00603600d000c00741c018082c0c2c08039a0300c600300c84814108403480741000d0519030b13080e00403402d0b00540761402e49100c4206c00340d038040820103001300c2e4040703414400090391951044030400c1c00c03502c15500900140c0d4203008550ba40d81c1c0040c0a20b40c004500704460f03000b242081c0504d0000440d001002c5810749070101c00142143c018040c013840a1341800303000c1c240e00341049400348081c4002d880f119586c50007200018958811544 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 34104061 1250 34102811 34102841
    0x3140c0109060e0f010605010c02090702010b030604030201020a030507050705060f1807030b06040f0905030f0d021b06040c08011e05090703141509030a0c080a0207170f011401150f03 80
    0x62010700304603640e044690079102080480720800c02d02c210b4107007a610315002d40c03030010300310803000b602500e84030307820a0300304410b4000001e404044102181c1000400c0703d041e00580c1d000108001e05980c14801c0c1039000d885460050f04010450751080c0d107500e00507002c003d2503d1190007164043c01c02c0310044508000100c05c0300c1046540307142080008004132020303445940340511a513100c000c83d0181000d9140d010000e94a080c091089000407501310391000705109900744120098912140d0314100d401d074201c0300500e0326240c245010012102c40d9041500f0300d13418020b0300c0104140c42312146028008201022809581d00080d20389072014545c40075128221185d80300c0345040003c25001d0020b220307405600000d0b42c40d0a00181d4030302c140b24582e0005041d861b280000305d5840303c0540002940783c410b41d488159104000324045030f040c40c041401c1d0b000402078002e110390034841c44113085020340071207945603d0158012070303440003a4940014420018140c4100c24400d034004004603041d08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 34105311 1250 34104061 34104071
    0xc060207031e020d020105090309060a14040b040b0910030c02030d18050d030c0f020307021003020d2406120b0f0f030a0b010605090112140a1808030f040515011203140c01 75
    0x40b6000790b940c84c080b44540c01651130000828240c07a008000c0316000c15002d401c20340b40a41014084a10b0f0012042d1401200e4050002044011244009000610308121000e80300c03a0003500300012a4079684c000c10a02d8503107110a20055008400d9941c855041c03440060707885021500c10b10700c2d4091340c0005056000f007040068210b50994801d160300e070090f540d1480e05043c10388040e80e0303a10507802d019500401d014100520944207400900c00c0301c600c09400309e44245500e0884031111001c1544402c4020300304030a00031681c2c4180b11010b404400001480620b1242c004100c01d03a00d6400c410b030003124941c6410010792020442c0201295003e2441642580d40d80b80c0141a500000c0d9841c1c00610211006042c00450b4055100d070011074510b1402e190311801c51020060a8a6080076540b0304100008008100300f50060f51152001711400201898140341050030003c040c0e40480305155280018409448101c80042c01e0701c0d450304000d01041d0740720b80b2044c400e0003100e4000e2160341c244 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 34106561 1250 34105311 34105367
    0x50903031c0605060a0c060b0d0213060501030b0a1a0a02010905030a0306080c150313050f0d0c061103040312020702010c020d12020708010b01020d0c080408010504030518090105010c06020703 84
    0x14201c8100030541c14010801c480d214800c2207100d10807242140006648018610080359440c0c0c850310807510028040e114061141e070114170050850b401c15000e0aa0f00d500802c91941c143c0152803204200f240c000d6202c0b0304001c060f85014680c415a002c4ac58404129003030214000d50007044500d803c070302141d44800d8000381c0140600900e0164480c94000d0314001c1117507081c021b00704142c41070400d24079421643c40c0080310350008000e900c00d0700c440c4504405603060f030b0028009044400c090307030b540314070b80314003403c01c0300544100f00c004400e10385c03007002040b01180d404042c038500c0c1c5a80b20800360303588a103030004842c22480004007940c4108060400c01c01c20214001040e01000785da0203030303803400c0d076200105822100581d4415026030004003002c80c0c00361289403080c101520a8a050b424070fa00e944000d421280b04580480114200103107000c4022411034070b07a80d8010341110b00c02c240c1d40c148000200004103588004013090740200b0200100341c09104605c1d1401c9442194054bc1d0360301c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 34107811 1250 34106561 34106587
    0x204030804090b01080f040204051e0106030230040308071809050603010b030105010321140d02040602160f060c0f0605090c040c02120703051e0d0f050906060d02060a05090303 77
    0x402e00c20708810514100e00b1060700e50040c1c400c0780c42001c501c1c00803100c1c1d075560740a10000e482c00400058004001c03401c14040609120310300c0340600386640d40103031240310500c2803410511070054086804015107103407070342400c8074010869100780e2514051485807151035058941c0c050442003040c030051429070108246180da4019480380d00c04500a02000b01c1c0c14050500303c610070b010191207244d0500011701040c0401c2550030f41d41c8914504031590071000ca5140101d0b0b0014900d0755215600018100700065040116030700c54052242d640818070b00d0b10b00c0c0320550a4103403160005101d0741c00e8061041c401c40341e2039041c45540105003071000d4541017404546031050703000c6e00703840340d0700c1e0004218000d4400190320703c89911882806241c501584c8080c2c030b0341d030000c405240303580502407800300000c03904a010f441000310340c0d10b000c40d81d20720088214090b62802404035800385d1004003080901c0d51440e12070500182c041d1075440c0da070310f4051012201c2e13215100a66816100c000f0b81c1d0b0781e40c2c0178 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 34109061 1250 34107811 34107817
    0x4080a06020a08060904170906071a0612030a1706060705010905010504020a081204090216050d020606090703020906071b0b0714070504090f0308100e0c19030b100c0203030d02040308 80
    0x14060f80c41c03503900da50752000c0044265081e2005401002d202038844040040d410040c840b41500403d11410200d460ba42c89280ba00b1030190308010007214001d0000c3e50510082c0b210703403003180001550520100034070007001c40b151401c1c040500c10402002c0380c480c3c0c0300c0300110b800d1190800001d000d03010351030402c10301030b00050301d080b03011b510070a60000b055417011940c102d00c0c081c0e407010b2500d01450204c011000e508000c080c10a0308008105a04c00600c00304403074509400305401400107443c2031020401c8050b002040101403500412450803d0780c2d0320300c01c460040b0f034042e0100396001a400301b182c4106102e81c2207400900c1713000070381c81d003800380000008400140f00c0d400caa00301502c038001c1c00140d501c900f20007400d0b0499050315400082c0102d00880d800a00e440170780712070b40e65401d040003e41400381c0c4c0002200030005a40c00d05000c1035840c1c04c0341042181814001c8180280100d028088040702e2a801c10a885490000f19503090040b034011400906095489507241d00300646d0642c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 34110311 1250 34109061 34109077
    0xf0c0f08160503010c0203040303031509021207030507030c0905010f0306030b07020a200d02090405120a030b03010c110709020706021207030608070602010b0901090b0f090412270b0a0504080a0602 86
    0x11504500000e294a8140210561017829038007440c00d05103180c0d819030103002c0c50b00075107a44568995010808000a2024203102c0c180c0c4031035440c0074282003401a0403100003802c1681050306000301840156009098142100d60030300e80180196000d0100301e004003440d41004060000700c1c0300b8460b81590009035002d0700d6001e00340c038800420b8802d1140c3c10981d201542190401481078a04015103004444150300c54021401d444d41c00c6610702d0b100c0a154006c01e00000445c0c1e07204506c1d401c03420248600c211160140c01e007401c10355145a002d0b6603549240c45416030064002400a04105079501907034486511000944406c2c100881301074040c11550003a200c00b4401d001c400075a5500c14007800300c4500000e000645c443e401c01d1800d8000d44003280400350448980d100e6003c042e1285a80725120300c1c00740c04181d00b1102300c010010900d203400054030300c02001396040c10b5600728444859101303e80244690666504102d102640e10340281e078411407503030043c2d03c0400c05004d07198005205407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 34111561 1250 34110311 34110343
    0x20c101d01050412030902011202030a0204140f0904060209011701080c18010605070f02041404030806120c010203190306050a1512111615020708040e07020a020603040f0c0f08 77
    0xd2114550140c01c80c0c60449010345001d07900c040c9014494001d6015182090062502150f81c0c0010344000c1c0c281d91064402a480c50790004040004000c1c0c24041500f91804403401c030030b402032260000b04c0401c4042d001420341c56000880c1d03402d6a009074070020900400421083e001c3d070b91820b401b52101c0030350001c0303401007000044180340d440c5000d0005041e915a510b0b001d084c8001c5481e40b0043d100c0c4d08038101e80050343d070f020b029903406491640c00d1146110b81e9559000b4503100c81446003901103c0310140305a4462003500c000c683e00802036426000c21070303401d88001201164101c1c0505107a50000d40c0108052401050194480e43e80035a56051501c0d071805074109900340408603a000c012450340c0c02c40910a03000c40344404005070b5516030081d680840181c5013031105504990203a1000c550f0701c44005010032028030056122580100d0b540040d1403900700395000319038141b0004000034200c2c43c640030200c0400200e03180340800740c1800d035030001086888503c0c0e240d407001250340c10104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 34112811 1250 34111561 34111601
    0x11802090703060305120705010204180903020106050a051e1804120201060e0c0d02070501151205070b030705030c0f0d1e05100602070603200712090b0403050601060f03020c10 77
    0x107110300074056041201d92050061104003041e1a42811a4025080448043d5001c01001a003258102c610301403807890681c00080768200e42c074000e0b0844121303601c1340b40282c90300481000603039070310391030f40041e20050f04031000d00c100e00c503002031458039000c03040e146a50070074414031081c041e0700040002503041c260020042c00342c807000c4c8100c0441d01101c0107410f500081103002499180354000c3c00b0050301c00e03c008946a0040914a60307991581d03044003403110b6810042c2018000104001c80007480b409104500d03504000e83c009100b8400289162441030340040c004901c54440c000300c41203180d109200708030b20348042115082c0e01d0940d480d085104da00385400303d1590400a40d80c14201d513980e03001056124a800070079806449500c1e4005429081c901400005018020042804a20034841080364980400340545444c3e82d541000200c2541400280001440040e500b4190f8042e42000400700e0b5440c541203020b8030404010340c038036000f1554815580c1c05150481d0415212421075444c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 34114061 1250 34112811 34112821
    0x5011805090a090f06060b0a031a0607170d060e16020303060108060909010b031501031a040c031e08072004020a080109090809120706020105010b0703050306190801180209 75
    0x10900200e02416510000140c08120716042640c000200302d403240b8041820080d15403254001c480c1c00b640038000b04032000070901e4201d58144107146519103102e91081c265100100460060701070319000410810319038a4a521101d11607007a20002100d00000744941ca84134000d2040e20003060341c2c00e00c5039003119000c4681140c000f0003580e100380c00694500a055580500304840711030040d1071014595a2030100d04030b15101402035556050a881034107049501d94500201d501183c0070032040b100000760280000a80181c00090840e0b8202e841428000c0e0000e00b03010507103081c050000c10007980000d0300310400100164031204081100401d102e1031b1a12030a00c0f0903445011301180000740c0c0c0000601203269540c0c480002c2c02d0003501c8160403d210140810a48883c01000a1a56028070b03c03c02a05a0900856025040380380465050142d035590161881c04060040da106060355030301c4a680015800340300c00180b40c06002031108168040860510300c40900c416400380c0e07c6d60002030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 34115311 1250 34114061 34114097
    0x201020d0c1101080a020f07051b01031401030b040302011b031e020a0c06050a0b030d0207081c05030720120d060e04020604050d03030e1b010f03050708061e100203040501 75
    0x203141c0c10040900b00348144000441d5541c10062504030b281c1da080c05041814500440a4208035205200130185140c04207010802c19044078a020704050502c010f101e080d07400e104030207046070740c01051150b450b242d5107000c0e809004442409440c4000900c4040c14081e03050300a8144110004c1108010400d400c0c0d0000591042001c0840070407500244e120000c5e03191f5101d142d1045c0e5210000803001f0f681e6000a080c4020034003648016030140c00305100c00601800500c078540100011403689902da241c4c090701c24040280707203000703004004007403401210445d00341424070340625054034803103512942c222000781c0106c2c5000c442e09281500c08552511a819400d0046400900c0d441c1894684030811041900014049080603181d5851036400c1904008500101c1c9500c6090309a041228000500c80200900e0010400d42448284011640c01c81d84943d08004240e8403a455292003540b0384502d0351415140700d4101174100c018408039075010010304160b4400f60380d00c15007245248421 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 34116561 1250 34115311 34115327
    0x1110114010506160b0a0207021002070302010f0302030402010216060503071107080a11030a0f05011a04020a0801090c110312070801120b0f0709030b1e06060408070302090402041e090201020d 84
    0x80020010803005002c03518210010301a0414a89040e14503120669100400c0d03070002e454500c04a5008501c000440c94060884000400d41e03100524049243d074000800c2c041a109220080c143d000002c20b0669100380700712500510700742e00825032940e079414000c040c0c1d40308699150004400d24002407040034045407035011101c1a800404400700c00307494811900c26038020060341403040003492000103134a90302d0301010318050000002c4485022114002c03c10703031040f02a104038070411041036590f0308001d110341580e5081a000510a00301d50007035440d40d00c2880e080060b8400800c0d907601d1060035002652107804075903511200e44e40da0b01000400300102c2c083c010038800501000448454880d0100e50b4800018640040c640d50740e5203c0704042001074804611840311040c3e8101090f201d017880031b0300300303c2c103444c000d00e030900c0d0184e05c2e51541e02c03a003c02441001c981005c2400d40d500c5402550038441d0116210040b8030705260385800400c8080012400750040c54041d40d03404d4001d40013 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 34117811 1250 34116561 34116581
    0x160603141b04050d080406140304030c0b0604020f0f03010302041803080103080901021002120f280f111306020c0d0c06030b040e0f0c150c030406080c2106011101 71
    0xc0386100e900c56500d42075003903040c4124a201c8140500002443d40d444542c440b8003180651403555913981410380c000c140400c0300903d41c405000400a010001c1c2c0e1212082d9446900800c07004115111200040e01900ca44903901e81541400b0039810841800034000314101c0e842154200686000324025141081072a076024000c15003010042000c20002d03802800000c0341441a24240c1070280082000c030b801005145280440000c01c00810070f1070205407070380002c1d030101c503094441c5402d003e0070203401c500310321b44445a8035440a803d021499401204c21070300c14480ca26111903101400c40100e24840c80f0f40c10040c4aa81e21915190401d00d0070710300c02a41040c010000707103080c0b400550240c00c03c0d48000360030540e2030b5403100f86204284030b04540c61120b00050705000300c0c00403c01c48044c003102c00401811008000311200703400b00000b1a42200d0450400b01c3c01d6030740b004030005080c0140b21403d000352043c5010300641c5110550342620a19098035258204985131141030300300d464500f8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 34119061 1250 34117811 34117841
    0xc0d1b050a05070c05060423010c02060d0209060706020403050604020306070e010c0f140a05030c011a0306060906011b0803011a130303110703140c1005030c04030204090f14160603 79
    0x20401078280e100b0740051980f240203c481c041c42541d50000b0405550065000400d00d031030018008076041c00c40c0c2c60300000140246801d044400132900060511700c05d01c480f50308042c0d400507105155480b41c4081e2000036401071404c540b607079500d09001707441e001c2c02c4030100e02c00e0040d4400217050314021031507032a8101041c2c2d50406544210307991910b010720720074002d0300e289020511103c080310040081940d0306202c0d20295071101c0c801e117202404c0d00d682260140d05c2682056507c0101c0e140040e440b80d009030216010003a90703c2d032000617200c105002e202c1c1410309205020000901c880d401c010740c100e80101c2c0e4506111311000326502c4003230240b4106c00c1c0c207254141c2c00800c0824801c0e0121428202203a090322085580d9554070308164440310544110f80c0c0040540489600c0c0140041d03609083c0350600c10316501e002e80e050343c01441280402880f41e0741e01e910f240b003071014442018405a40c01035a5103510889000650781e5510303071070300c450241545244003003950703480f81c0102d90000f10048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 34120311 1250 34119061 34119067
    0x106120b0f100b07021c03020c0a06050f0708090409050a0606030b060901050607060c02010b0d05060f0601020f100c020c09010305060406051f03030305040f02030d0c03080703060b090f0d02090c0d1b05 88
    0x840694511341c8421010b903842000b00c003820000e050880a000c40749440303030f00203114000d4188240a00c0c014194421018000244003090a44144c00100c5d00780d10b5004007802e5403501c1e0b00001400411030850054450700ca43c04114040100d680c0c005025240140c1244d0800e541ea58100170b81481d0034000c1c3c1750072403014484e03d00041e072541c1121071900a9400040303441c006420102e507480a04103410790701940000b040c04100840c403013005402103400e2001d403280b020280b1800365036030415404030324101e030340318511071400c0d100b442250305882002b46400d40c0340d41c0d80d0401994907101514240d03145881c050100b0b8181018091244403500c0f81e80c070501c0344500d5510300b41c00030701004100b5215000d24160b9038006035803d11403450251316035140c1c01c00842c03140c1001404902e0003020501070502d0514280170100340b410036590030311000c56202e00754010700c0002c55000089100c001707400c00040c20602008401c6640600061400c036a01085070360700c40c000b1540851504190500411020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 34121561 1250 34120311 34120319
    0x10b04050f0d020a0306020f04051212040e091c09080613020907180512061e0f010b16050105010609170106030b1807030f050a020f010314010501110c030106120b0f10 73
    0x64520011014002000b6200c0b290396602d1b00005d03a4009a2a10282440000c0a07c4249030000064040d00600070041041d1200b00485002e20700c079500480c0410b070803410006100140c20001c2d000600c201d00c100c00c482240e60503010380501c01e41e0013001c4480c040c52000070b0801e9030000300c0000c50b58004043d610913440701031042e96480802c4144a0148034040000b00c2c050f107844c1031100280307841ca002045186407080c0030b0b806050408848181c0c0845020622500300c8540e440d040c15200102c02c42a6a81c00c2000e02d04d0307050b80c50440042032035080000000e0003030717042148c14040b211070340300340c42e10f601210905c1401c84045010090182d02c000012442918510908004540c03c1d801110400b41e2aa140c072420003c03101000c40e8180e014400400850601d00c0c80d40360580d42c00e08040c0b0005940b81e100b0074484005002d03680c100032808490000c55403017041603050b0b0f80307000b5000f00b0080d5110001d094804e9094038064030304182200101c0e1540400b030320090710030190005403441290070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 34122811 1250 34121561 34121569
    0x80403020703121218110604080a150f05040c030b0c0403050709020d06080307050102180a0b030402040b03010b040c0507050105010b030603030712050d0c050903010515030a0b0907081c020105010b04050f 89
    0x60f410301c000070071044015104600015200350000c045500c002924892480d01c0c00c20616482c26203a1402080140804c128001c070009170361f800035910908034500140042940c4005007240e05103c1c41d030b42c0c100800d00003440040c400140949004002c40c0109a8801a03965080c0c4218440100b0652000808000c001170782d0707003c0d10500c51000b0000c03030281e503540c1c2500c2c034603005249c2c1035410b65800a0b2580325441d103249603a20020040d20822030407803a09a1004450000900181c090394560380300c2403459a0070341c8410811301005004000040d0000802003075500400350456841d840c01d400440c140d00300701d003500e1003042c1c024000c1d8900981c0c0d0b0360300c403840400c2d22a1001400303814461100c18980ca40038102c48102c0c40d540c4d003600c48a49030101420344601a10007003e18269501003034554501080040c0c0c26904024107540e04e44030805201e15046040e0b000016500454103564a01104455009d0301012550f009100c07030b980b1a20070244030321075032141e290b026021100e283d07443c0c10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 34124061 1250 34122811 34122833
    0x7030513020d050a210e03071d150a06031406030309030a02010c03140d022502150c0f01140907081507030f0b0904061d03040b0313080708070b01090b01080403020703 73
    0x101ca00240d03480d030792055441d03c1c030410741c0b01d4645170b480210158041d4403691281c0c82074001401140141710252501d07080340710500c1d0342c828040c07030501c202e80050700d9410054411004800054103026880d17680755002001050f5034522070a0320840d04c1c000c91900c4c41d00205803005c554004004e0524060301e070780103507244203811100324284a400b40c11b100600000307601804550411501c003607035595100102c028550a56002c600d28009006141d1303015032954408940711401d03a030011643c4602810100745041240c01016141b9800c1440b501115080c032844940a1440d4004031002d184e1106a116102d80196005032103050a0344005407207117120307400003161070490840000d1302c9080031011a58200007100d0a440003906c48074010092004a600c811003421004051820a03041501c0c4009610010b0042c400309800c000d4a1f030181b100d00f004503100150301ca42490f41c0c49000345041c0025450034861058400e2410500c5091940658441c42c8915456400761041c141540d0b14100a08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 34125311 1250 34124061 34124063
    0x90f04030c0503070609021f0e040b0a0803030103260c15070c061a01090603060501021c26010e01050d110d03110d030203092112060301020d02030a021207030513020d 73
    0xc07560362070110200d24184011310043e4000e00e400b10341020343d030050088642c4400c3e0000d00050188034141d249070382c03001542c51440e0301258081550344003c00042d110b41d10740e421801e140c0c08000000010404010107110001d5034494150181c20040c0a03404420b000345104091143c104080401d8011007005450354040c400b410300d0000c2003c0c9031500c40c1100c0d00c00e004150200d031001c5080c030484d80c2105500c401015036150078040c1d03c4c00c09000030344402504013841410300c11110303e0b180540c016202e240005c03c9260800c1c03066820b141d62860300c80028855071601803200c000200b00b0303041001621500581119140807400c51520911a20207240542a030400031030401c081030314007041c02585c40c8148540e60141c1c4034100380440d80c0c02d00340d800070002c0c42e441500103420038850a02e405e072084400d040010a0b450703640c80e0003190180c802d0705000c001c040e03c00010850059104d50240000240260556000307a44114003501203510940b8111400c8500040610041c80c06840d08420a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 34126561 1250 34125311 34125317
    0x10902060304060b270406050f0112020609060c01140a140c030402010e0f1005070b01051905120106090213032105030c07060f020c010b180103020d120309021504050109090506090f0403 81
    0xca2400c680c07424001c07011741ca8880394402082803005004039170042641108406c1c400040c1545031010744480020000c60081c040d25021038a030f01d01f66a80030a5815041e4400c000703010001804009500c5044101d8483e00a0b9140207080403100c1081e03540540b0a1218164035440e544868005580540e0003281e0250b1001d0b1249440319a52034145a00948103200d440b0a502c41c00a4a8902101c40c0f050300040e0140f065180b5244042500301980c01c1200c0d0280c1d00d00c41d9240e4844501405010305030440340ca403c1c00003a11140c2440c5000b0a032044038051069040c0060500d900144103030026801c860010388284003040e401c801c43c01c014807815101c3c641c00580c00070b82d5102e17001640c01c002d2003864039075990100010182084c0c2c180300754801d0f401c0d54242e080d40c1543c2c0043c4c15134258500180883e00c284020034406402035110b1548660001c08128052071102c00700d8030154054001d1a000078001440004c40300051f00405026200080c040700240d50345150711981c00074028819810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 34127811 1250 34126561 34126579
    0x3011403030c0d0e04061d07030c021509100c02010b0a090c09030516030519050d0f03060506071b090612200a1403060c07020f010f120c0206090c03010902060304060b 73
    0x20b810020031520a41140c2038030342d103001a0300082004119050b5600010404ca0300c055007080c003201c00c10140d640101941070007d48100b01c040e0032403902c00079101c0310b03c250b10300c8005e0100c495000240f0001e5620200e0040c00721300300c0200c0490030303a80f510610b55000030200206001c1c20100c0e07004280c1d41e0001e8070b424a0855038940700d40e854000002041d21021491000030b00511000b80540340c0d1104844c00c441c000e10700260b0b5400e035100c0711640d00348104840400a214160f109030880c400134180240207603121169410300c0d004400710911075200ea02c170400800507840415010340411a4002140c203010003003e0b4680380c0c10710311000c00d00700c0c00c041204000c504039a1000d001c1d101504046001c80041c1c1c1d14201490b10701030015202c0d0b41410400e0220b800181c0d00c0c40102003041000303103440003c6115015040c0c503840310740140d4000b55420803070b21050856001070598031554592049581880e0640141802c90320b4480c8069044102000085c01140450b00014000b44000d490703101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 34129061 1250 34127811 34127827
    0xa050c0415450b100c050303070e0d020603010e0703050a05010f09020f04050301020301030f03090506090a21050607050901031803270305010218011808070611030c0304060f0f08010b0301140303 85
    0x80029154402d40800d035601001d0050341401d03c083d410a06460910030650601621031694902001303265008000e00340004414640303a1000b00c0307404030742c054885d98607940c5800411302c1d078220803986440001d14060018416640c580140e5040714080d0074504100307401d145152020f50b00105280e00d200b20200702c0012992000d1008600850085c600d80e071020001e46802000b419650303100c030b4441c13407042c024030410303607100117108049a507a440008071601440140030400c0584041c0584180250020800034a400900402285200f644c04000000088900d40d03048105d07030300040c000a9018010225082e14202142004409040c4c0c0b5401150303207950741402e80e800720807400b1007500c0c0d0752014000e55070400c80044059241301203010069041042c06a654070b00d42c459402040350000c0782140034841442220900030a0b58292555581c032001c0141c00240f08110b04800144091034910240c0d11400c400750580741400801d900d181d01e4100c0100c01010040c0c0384590500080050034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 34130311 1250 34129061 34129169
    0x80a020c0a0209070c05070806010e070c0201030902030a150b0604080a020103050601090e10060311030403140f0708070c050108010527100803120702070501030905070b18030a050c0415 81
    0x1e8402c443e9517980c940040c580c1c4ca0068103000341c82d4080d401c0c542c071000040c00310745c0c4851040e0f0b40c46105450007507140041400120040c1605500c00380d01400b854100d2000d10004003280510001070070070520003c61460140049442544500c1600b5000f8050b030000540c4245c002c1500320405142c80450311791240940440b0100984d87d092a480e01040c080024039010f0090040303403410001c6c240d0941c076080e180641500c0317031130803104484000029a402819414400d441e48550031054990310f8646518000074101224029240414022000041c2c01d00e4403181500c0510b0201c08452440d00c20b419072040c14081c003802c101c5100c0c04008010904400400291403550000c2469003000d040c442c0300a403e1801c0e94001d507040600300000500401c4001a61008a0b8001c902159030350f140d00c149210199800512103506004090360482030100c001050440e034042160108a001a40d00e2001d908000d18400c04501c2040351075183d40120180300d08603483c00101294100c05a4148014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 34131561 1250 34130311 34130329
    0xc03050304080a11090105060306011206080111090a0806040818010207050402031303080c0a0203040608131a09060106030216020111011b110f120f030705041814100303080a020c0a02 80
    0x1220a030751007403080c00d083c80f130a0a42402c408909543c1010694100400300f4101e210040040c2e040c0003454400d1014580158041001089040003c0140c140241c04440c869031280b40018400e8a44000c00300d02c210002c00c90901a640c8895400d241c00781c0e0240600c054100030950034190f000b80c040006a90700c0300e00045125890721003003c005086a440c0192500700d01605600080310148000703071469400104440c00e8a6150800040e641d031034090780d1007940c14110004103020304142c2145078441c9400c1d11540180703c40002d55030301d80c0c1c0700c0c00210201e00454104c08030607440b0450b1b0030b0165028248803400844c000001040107900489441011114401c01000040e81c8074004e0300b0b1528288000784043c0f0402c0058000c0b00417202d80c034401340c000c5c40c512038036140380000840c92050055003194000c1c0040c1e045040b1102c3c0890745c040052a2030360f50488a140c00100140c050448140400240c903815216201d05481365801d01c4001d40005a201c0b04900c42e038070b61070000d40d80e010340c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 34132811 1250 34131561 34131569
    0x306030b0c07051005060303030601030213050307030813120c0e0a09020a1e0e1e07090306050c1903020a090e1503030304050c030111180d03141207110f03070f0c03050304 75
    0x7880c0d48040c240751480c0b038000c0313811010400a107400c05201c0203550200442c3d800480910307000d61141d9041c041c8a40742501940708607450b00c07802d01c0010030008114058140100c00c403100c0d10f005a911018041d4400b41d0078001450390211501c18805a04070480194000f250100300040195030755011860720006600440000c01c100c1440000310343c3c018068901070300015045040c0350900c045c04440e803090201c0f411816040340000160510b200f082d1340c0005503000032050105080600076210603510041c00c400d1481c1401402d041d100780280200c8180c00b20a9803134065680c070340110808508005441441000107000c6259140d0364100b0103103001e14080e00c05000f21040c01410542118095004c99507240014001c2203100c41944015260480d4280c03403407144081e8510f41100c91000c40c5410849400c001308600c007214208160451144005443c1e00203500d00c0c1402140d580e00324110341010300d900400c1400b00040307110086d0860503209859215a00c5c0c0ca079540d5500b0743e082600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 34134061 1250 34132811 34132831
    0x310090c03062301080a0902030f06100303170106080f0c040f080106080d090f030f02030a060f09110301050907120809090106051c02040303120b28051e0901050d030306030b 76
    0x7040c08022545080c683e00e4051075000c0001c1c1488241c0080d1908500505048005036103255503001d40d10103110009106404100340c0700d103071030318034481c003403110f043d000550000340a602c42001070a006154203042c2e1b007480c8c5508180e5900d0028222803024018035085480c0d1081c40700240b00c40181140e0b40141052100100d152400e100c0c10078034011040b004002080800e03d0204000320300341211006032600002031100d070001600100c2e140c82e00c0d0010040000e032800442081280a661003228154480c80305542d9445d101d43c02c160070b0303070000d50b078a140c02e8103c0300080103900843c4a4001d00719224124090601c014040080c4140100360303c160302040d130000e40b400c05603a4008104c83c190300546d404500345411514024644513580c0302c40d0034881e544005601042d0b80d40304245000302160184505230750b15001410030b01e03152900c00c45004a003c850a41a10842e05a0f04880f190015005608aa19007000c21201c0110f00c1410382c140740d40c2d0100800864884294070348a035074114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 34135311 1250 34134061 34134071
    0x30e160617010b07020d0501060b1204060b0d0809010c050a020d03031d0106080c060d0b100f0e0a0503060714071406040309050d170c010f0207150c090b0a03020310090c03 75
    0x90150400c009484100c0a845800005000c521128402c4e0b4280c0d0f601560a00b1042400f4034125004240c83d4000c1d0f01d25000129456004124145282e442140300d01401d0040038441c41c1800680500f01400070f100040138006070416521890103001c2007402070341105c601c107030241c000c104406042c0310180c0009455844554045500c49001c50000c3c603024020000d8520740402151501b040b42c900c2441600c00007110140050103401c08a88604003c000120340b407000c290262950003100302c5c080224140c0600c0d08018503140803c0c0301265400b9000e84801c1e92401002ca030a40f04880c42d10700050028002030010600c504a00c84030810f6170b0300180a40e040c0f909014000f50300ca40d220a10642610801600260100c101c3c0d4101903542182e168035500072200d00c40c05407544061200150b84049042400c0c0301d404602500034500b008002c02c00c01c40801000c031030300c1d10b60703000d003107644c0c6420082e02810074803a500441e840502076952040644c0c64503101c03c00d58580c07100b03100029440d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 34136561 1250 34135311 34135319
    0x605090d0903030203030a0209010507050d02010f05010501031107020d170301030524010803090f040605100e040513050a0f02011806020309010306080120070c080d08010e01120819030e16 82
    0x1089003180405490910100103490342d54002d40d81e11005025404442d00840c405446901a00a60b0070096011003074555069030b02c0350090090006148207080141458000540c550180c030416400040d5040030720711f070480d55000d001010340224011035406844140c95420126440051030280d44200c0c00f070028912010400310001e64200c079090720690031170004100c150b0001049030380621058954085804100c0300040040c030596000640140325055040f4050380d1000c1c50a0a03a40102c0e420800307074490080000c100c0c901c41e03a000700035902c4403543c0d00c0414480c07000c0d43d02140c0305241006500c0e0884042d400003480940c407290142e440400c040541f5a01402000083d100c108000c002c10b0004c2c000409604807000c005841070040000c1003000e1040c1441c0d403c001c1c00413202280c03c800000c9500404240c1e0900c05c0c0b06005c2c18480021503803030b68a0700d07408003040d000003155040c104d0106400344000760b800c00c14018580e0300c00d22042c120074180518000c0a069034481201700e450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 34137811 1250 34136561 34136563
    0x90b070305010b090109120203070f0b0405120a120c110604090c0215101403030d14090f01020f0306060f0c0106060302030610021f1509020705070303111603020603091009060509 78
    0x1c1030300400742a0905000510180c0d910408800881da002a08600000001d001081c20300f0000c3d04885212080c410003c922051081d0080007121001da03020100c2864807021641c94508000b4014844a80d0380d002080c1c041c4a4000c06620500518842c054080b640c00014050350082e4404050719807108000b118907a01444a400e4a034030104003140c3c0b80c500900300c41050030043c01200341980c00a024125a52010001e55880300c40101c0304207e0f45480820958001901311061030b224485d2a81c910400c00303040c000d9032030070200150018210b407151401c20195801031001d00d4400389007801111440c11007402030302c00800382c0783c90040ea1780c00c000702408443c1c40003414100a6510801000301501e1124418a48a0306803260004090701c1d0b00101c0c4582d48040d6101595040c0040354039418458046180c0c0d081b40c0c401d855060901d49624406910b031027040c1d0900c0341000307510070108050b080c518000e5500284150035070783c400039086c02d9072003200c00c008416a500c1c0d50754020481e032400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 34139061 1250 34137811 34137821
    0x7150e10030e060c0c03090301050103050601050f1f0e060702100c17071104050703020408060702030c01050114090a0b0406090603060207060b040e0d0302090a1205010f05010e1504021c090b0703 85
    0x609450305102e00200481c182d80c0d261405807010394209400600441055401c1c805c2d150010b20080081c441035940341090f5560f01c00c04e0140034400c01d1940102d100e04e01c0d045030203178004588882d01c41c1268808500c151080c03409a610144c101d1001c00c08040141d03038030000884116503039201c8160016250505c1180c600760200300f08000c3c0d10805c034034401701e902100446132042e0115404105696441c008501901680e408105103100c0c010a0003d0140c02202a041201c0440002c010740d0fa0b070b0b0790340758030f6100d45c810006800038100404582d440b0b0280c1c2010035010f0025002041842c0e40c0c450501c215141a40b09580d001e0380482c00e98208a000c2c082d036071a41d0400c5a050083c40c05460100d41c036650101204403d050380083d548019490b07041c8140003e0040d100902d1101241b82003490280819440d01d40c95a480c00300003040455001404a000715070070316060549081c0001032000a51100c44180b80d1040710304081074201d1038502501e03c0031441120750424a0818050207010b0390 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 34140311 1250 34139061 34139089
    0x901060f060e04021303050105012601050105010806060306190605130f05010503180118030818010603030e011218030c0308010e01050d06021617090a06110d030e07150e 74
    0x4000041003401c0c2d02c00a50100c22100725070060341c41c02c000c140000c040700d40f907100821030750806000160000f811041c81e11529a9107464100060700c02c02410300300c0e4000d014260100e80080041030042c00d120000d0b6034006030103015803070fa810f80d40c0b1132900840700a511040001d800041d401815968210040d001031003008150102c3d80e081000281c254003000702107072811074003440000800e21094104d4403a9551001c1010b00c04000c0d41002880054215002c1c0c0c02c013507000d4200202c0040500c10a0304507905071381e40f0010110301d9001110072010110084071025141d00411103184d134541d1746280040e1003170b240c180c20411070b40340c003501da8501648040c1600141d00010089515a00d80c3c440c81d030b0b035014a0040c0d032070125501c0b0320100c040d4494050030301784403680100e444507030035802440b52190480d801ca180959071380049800c030710807a1402c4843e0708003030540c0a0050083c6c210000b801020025221143d4407961440c0340103030284003400c00030300e110790311a0643c103001100d09011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 34141561 1250 34140311 34140329
    0x7090b0f01021b0f0607060f06050f060901170606090307080c040509030a080103080703051c050f010803090d120c0210050403030f0311070212030409060311030f0a0201020601121b080303090106 85
    0x3585044001a021031503c0c81e07190203502c03405501841951648103c03040594000b074100081103030700303160700002c1000e4040c1c1d600070780c2d9004062101c9d180c8001a1aa180b038140d40c1c9021611783c03a000c014200350080c19281d00080207002c1c20003981e0f41404540d001d060b0500c0204080420841000b059501c050941c45550b0410450592070a50000c4101d06613604048450741d40c0c80701c1e03d8201c0f10345c4200c060b440302e4808a800f0036034900080fa08030a010b20503101801c02240d0f2620101a282c0c481d000c8029030001c0f008a03a040090401150180b540c00a410695410701554001c240c100310325400c0c0380d0000303000040070320070142c12008404881600d40790401001942d000100d00320310072010003a03c41d03001180c42c0c802d003003000c00c1102c01400c284c11013070150a43d6480d11241087e00031500303521a0103000190b6038002000144004140c0d0142d000301041c0e440d1403d03c0c000c3d41c444a034144e81c0d0070121078000071141c0d02c0300d400b20700a00d0f500c8011590b074503200b00001d0840e009500b01443ca = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 34142811 1250 34141561 34141573
    0x515060403020a0b2214150408100f0e070e16020a0c05010c151b0908030a05030610120504030507021009030b01060e040213030302160e0906010306090305090307090b0f0102 76
    0x540c6034032180c18161088400c07456554041c2c10a152600ca510350400e02c1210480400841c1b031b91002e40200d41038001c2901c143d205850078039050140b60045014200c3c1d1684203550440b0440e9160b0000110180c1500001555000052400b800c295841e0010070724a2507071010b04c49103501200c40c8080706059440a401029010313600e0b0490304c2da0510505040002d40d8682e6414082c041d00c807410104040803080200501c0b0003940381c00c4d6402c040b00c80000c10f1145900041520003c801c84041944540c0c0e410715650701c9904105245030440003034020490b40803102085061240301d1103000c0c1e806500e4164a0304464410045450400c907154001c21141050030030014000d50189415076040c1c0c20808200d2800c640818020b00440802e00c01c11201c1070000010716801140c035040c01c4406080610200f621074040a07540c48007510352900c258445401000816000d80c81202c0e95032080c0350051420310400c00103131030160150032441403590b6801e100840e03072030301d520707040200c210a001810b1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 34144061 1250 34142811 34142813
    0x9040509011d0a02030c060702040212041101090801060b0403032a0c0e010815040b0a0e0303040803010306110315060a2709050702010903020307020d0201020c0d14010f0603050a110109090e010515060403 89
    0x40c03031303042e2201b049008940114481d802c643e80c03034041c1c50380c140c0350303400d800a10700e01070030003240400380d0300303841400705505080c0403d100206004c1c280907140020840c1d4501407031a03038111102900a107548140181d0644029003241602c000302c4421806409440245400c001440101000c1a07000541c99030040b00c2504910000ad101d60383e1140e000441112942da500d0403a40240c0b5400b0340c1303101107000000400041000b020040c40c182c0b40030700810003a890304e40c61500c0007444140c60a80f0761200c520309406042ca8000000c1104100b6450403009220501030303131030048040542c1000b400c0100002c20303c4024210f2240b5035000941e0f10007402002020b0310081e441c2d205030bd4000e800340e0791400d0087c080d64020401d90180402c050700383da8180c800e50a08800500e1800100d40c110750802114217a40c182500904054940000c0944030800d03103545d44514119003024140d052020034040040c07114254405caa0001c0c800200204851902000000c00001d0f0841428410001800144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 34145311 1250 34144061 34144063
    0x90510030c0f0c0203030c030a26040c1806050d031101050a0209010507081305031e0f0a021305091002130306060f030803010506030c2503020c01032f09040509011d0a0203 75
    0x2440310102e820300074207009050002c6801c1d8824952900241d100004481c0000ca600044031440340706001d450110941c07070354028001c006026280900b660003071a0041c45550102c02840d400e00100c0400050f01d07070303910740204803900d500303500c10350205800201c1261050f50038098140e001c01e550724110300e41465040041c0103400707903031409001c400000c00d0000c2e2046110205001818006040301c100e01d030100500c1036031156001205025000356076454640010000351504c071581d00411a0014000e012003a00040c1070081025000784140b1100c040c90b200907100030058422909550600700b07055007069010b480c51a4000448403008001c2000407030014400d8a044d100100c500c107549807100c07414031210780034017545052982000c4003070104010703450040e0800c0340d201740c0030707182d00340c0900d001982216821300e1324844c0880164a92038030480541401c0d100078210117a0300c0e080080c400d012030100d40007140c0b06a000d039518000f641002031040060b80300040c07070000900c14402e50764082 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 34146561 1250 34145311 34145327
    0x80109090602090414091501080d05030916030b010807050105040b070602030403090e15040c08070206060f062802010b0a1206050711030a0909051e06090c0c0607090510030c 76
    0x2411915603280258800c02056030121945000014003d2091340c82d82c8100210302c1034180c940e81c0c098440c40700700c081d41d901d101080034120340c01c0360003038030381b06030f00344001c0d00c09600c0100b10300000e003d0400b01c040a0034040c0c190344040c0d07001d2440f5507410340c1004041880c10003c0c4d0800c9041c010103000130002641725000f219009a4015800760702e0b0303115440c09688400a81c0c209a0f0b6561200d03042014030401420100301c2410f04540510518203003202c1a11400800d945603030040c1c0020f40061003d00301580c00794040c60000d40220304d44134844c2c203804003031a0541e4601c000c02002c407044080035a03090280c43c0e040d0741c0458803100d0300d51908180014084068030001e00341c944400c0080c490b14007038600408011092000d032a0740b081c0410f0000e040380058010b115110b03240501061150a402c9041410040322100d0b4240035191641000021040100000c0b602d104c10080f0740c2040d1000c0c02802d00030002d84d200e03464110300f850708004070541c82006520405d443d120010758020703805841 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 34147811 1250 34146561 34146569
    0x30903090504060e240d0302030a0806100507060e1c0305010305010c0504180506010207090204060f0807031b0509130903090312080c0a08150603190e010b010f11100507080402130c0801 81
    0x1c85c80c0703071103004031030410070004030b94913544001c489850106158000c40200104100d6950f80802030759154200583c9032840c5001c0d0001030300a102140016005070301550305040c0f4442103032141c4040251030142032190b00c0d00c01c00001d45800040080010901480762414203509010341080d0501e240e00003043c10719000d282406440305e011894a900a01205000d0040c84509550302d07600d40c04040c00070841e00c07044c400010f9505000594992280c810000718031f00c02d2180c100e95928420084a65070401402c0d503030b002051086c04006003203544070310b00320640f09850f00c512403491420016000c10134680d82c041400016000c02c0100d150000803100050403e00b032020640c2c8805a4040c2c3d8021070700185034100300d0000030f000700e08180c601b0f081c9044100907401d00100f50702260031420f8900d03820105000c160aa882986918000c3d000d941140c800c0324100e83c0800411070486040e5030082e04c800010901c030030140070650520740c2500280c1444c002c014800180400401031100c10305210b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 34149061 1250 34147811 34147831
    0x1050703140301060f1d0102100906060b0403061e020c060f040515180705010203040803040e0402011101050103030302071406130308181501050102070806070f05130312030903090504060e 82
    0x59058201070048000c0d0440e0301e0640300c075507125030315000050a030120801c050804101c444000e40c0810607a0707412001c0010341a806450301039000d200d16005400207007002c03100a40c03a0700002c01c41f15070340d0010384001c60050300d02040103496050012410a00b00b0008070315640104940c12074030000003030b82c03a044075840269131402e030354a040040c1815504028208410002c0d404d002070750540810307045035034021000740e4501076511001aa568401c0d442081c4550304140300c20080707400030b0751100c0e9025006051103444222020300d0311742140c100340c1085012950100f564402c0c0840c0042c2e071181194040000c160b2070411004040c80c8072400c0400404121b00c00002400e05601f070751082031840c40e190300b15400c101440b001c8108011090245a0052050090000da03101000464034010787c0c060301c40b604803600400c81251268403c28140b8200d02402100000040c805013035a00e820b0219a800144805280b80c01002c01d109648a00d00c210f05041c030601580010510740360300920088 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 34150311 1250 34149061 34149067
    0x1507082e09050906070f020309090a020a030612030201051005040504051c03020f04260601032103020f04031208092a04060f0605120c1303030c03020f032208010b06090105 75
    0x1442454036590740050726098141414401c460a00003550b41c01303600c0310345540003000b0b8442801c0341d0700c1c05000900c035400750350f081c040740001445900a100d00c01c0360703180100d4160348482018440c0c00c511001100140e40d80d400308041096010000300c0070700b908035401d02c42d50801e074a88986e20703502808043c103c00c1502071010380341c3c0e010f40d04491420059070b803007984543c0d585196091515510311012002c030041b19a240e000f001c041052410b030381d80003400d02e0321034108034a0410880d50181a132001d1503800c01031054803c000c0005040254812401c41243e03001c41d1340020940d010140049071641c1c00314a036081c0c20300d1070410302000d4100c020701418010001200083c0504602d80c000d201041c0e210902044060380440146848006520781542644591400e480e02c0c1c420b98284103040160602c0502c006845045202c50301c9000f441110b41d6144240b051504540c001d500d40007034200d490705000400c140150440b00180000002000500b00990204046101354005241044400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 34151561 1250 34150311 34150381
    0x306080d05040e101e0504050105060304051e0f120406110c01080604020d060308030c040302120a0302060c0a0507050d050310050108010f0302040e0a0602041404050f040c050108070201020d0e150708 87
    0x881604c00100b28a015410094070030264404650685001e6640a40e0510001041c0380c100901203c0c0600e80c840002c010030003a903440d0b00001146c0c0c0c10080801d016883c01c42050090030805d41015144881c10f181c3da5a2400c040074000d10200c48045040d6049100c01a01680e04031030001da2208042d03c0141c0d030340002c1d94103500204401d80005142803004404d03c45035010203805042a64400d076442072407942608034541d900c0c1c140860040060340010b00040c07400c01103402a0560001609200e4200700c0300f0f0365514144690580c0e507070000303903003c0204020444a286400010300003820700d600a5410f104946030980001d0001a004076182c1d1402c010035070b01008000002900300104540321901c0b00c0c0c0426203000314494240c8254100f0707000c00e1645001e400b100c1d00966105028003000c0385000d006488031003006043d40c055560070700001d030300c4007501c0c0203070201e00c0720500c0940a03031015805116240700f4040d16110400100130700700660a50038000c0f14a088000c040c0c581311584036 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 34152811 1250 34151561 34151581
    0x3050a06031401141308040909060b03030313030e1503130c1206050f06040c0e0d03090f0e0103021008090316051f0b040c111e0a02090f0103030306080d05040e 70
    0x20503480201060704412480c01107a41c190304c03044060746120110382483c0c8641028440d44c503412040540b030307090100b01c1040304e0316155001c91030061045802003a05094280024190b4108564104e030200d49071040a04151b4403100b0a51107800444c0d083d40d00001c6030303261004c00c0c0001840e584007148012615403d1201c030303171004401002402c1d00c5041300d16aa15048025210640d00e1a804c4184000441c0040c600703400340c1c4102d9141070703541c00ca84912400810880c1401c1d0007066080c004403003804a1441c5500b58070401801203080e0003600c035451441400f4122a04840c07081c01c0160520a104040102004480f03104144070b000140740d8099090040c00c11032105104012200454102c40c03145106403c10080d91404450402c144200103c00761000041c02220f0469078008000010308030080025170307265000342e5001c5450002095010403140902030b502c4c1c40d00014900010010194540106006086904094504c0c1e84030000003500710b0050b40a1a840c20080c0b000090000003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 34154061 1250 34152811 34152821
    0x20706032a02071e0e070c031103030903090906041404080304081c05060f0102060103020a0b07080909070809190506070809030d0f02040504060506090d021909021903050108160603050a 81
    0x2072034a4541c0000c0c4070380103001c0d5840f0b034a44100c059201443c403c1d810000016a0300e542100c9401880c504507039a040e40c12190000c0600003181032060020209440038010809127128012142c010342c1d0f40c00880302001500c060090142d1700c280d00f400c2c2c0c2d01d28880c0c840000315400c103034030020321500c1e91112301c0c040030103020380094481c0321003214243c12400000c5070802d50041c0d509890909200c2c04e24801245c41c0c140034040650007212850040280c0030030300c40103010740c2d4041d50403203041940600025441030001e848100000c4c0600b02441440d40b4180b0003400240191090440303101c801d55034003503e40c01c0040000007030100490010b000d400d0300f1720880761046400c6800300321018540f0010360007908a4021540620b00d00100882d89007001d01c21180034400c01400010351444a900700030700c4894082040d0740328000c0302d80001e884501c5001030300d480da0180601050002d800030000f412610142c3c00710341c00e54081d03042642c00e82c02620010040d19024a03004c00d0a40d00c180403600548 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 34155311 1250 34154061 34154111
    0xd020103200d1409240702010618050609060904050601140a08011508010509010612060b040b0a0e0609070915200706020f070e01061202030402011808060402041b02070603 75
    0x70005100704110a00350711004400c1c03080041c11200d0348072018803e42d1385c449011180d40c2c1c1d501c00402002c2641352200225031144580c4008580070340c07a46d104a160840e40365108682646a009024461506002c610b50004068074001580d14050711034a950720810322403a23540d603224501005890303c070792031200d0103808001c009000a4240846c07071500d03010309219000e9554a040003083c03521206026841c112026801c1c540d00c1a1241e8403000010b101101d22541d00903500c00311458503881c1d0351004001402e0a82403006649050340c1800803c403070007000b0804211403205c0501c41ca0003a00c2200c0448c0d0b4080c03a00700c550b1800040840c240c0005c02c0410550344c0b0425400003406a0700085003400170f100c2e0b0065440003952080c801000140a00a84012905c0610072000c40500ca070701456000d0b0051522400c120034200c400e050a42c40c6420010031038004208110943c2024041c1219070706c2e0402401c0110b101000300292200d031280070340710800d51074881c90320020081500e104821 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 34156561 1250 34155311 34155371
    0x406090c051807031119080c0403050f16090203010302060d05040f1709031e060403080a06050a030317070c03050301150e0306100302010807020d02070303031d0a06020901021b0d020103 81
    0x6460010b210001180c01103441d0070000742000d85a482100b14030050300d2008024202405108540c00010364109900510705051660180000404940d04001c0070a0105140000d800035014400000d0b155a082e0b070040810a80100010070040e00c0316422600d101170303201e400041e503480360302d020b040f54024a50041c1258203500c0340c04040011340070040c03002040403001ca90021207103600591244000c0701c0065400e420442c0010b0109010b10302e1158491591000007400d1512200099002c991076002580024035120074003001c00c198002c0d1ba0781100c01401c284000b00541d940050044c80140508040c882c0e01c00c3c5c07218002400782081d0560840000c00b030b6006450401c42c44c0c030a005440c40141d0020f80b14602050405001084010b8050f100364003030b00303803a4159101540901821000018604408807440150503004e22150001620620b0050f0340d8401c0a40020310b48802700d0600b0b0344070100c510880000b50f88000718040f46940c2130130049501148a19480500d101495005040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 34157811 1250 34156561 34156579
    0x7031e05180601030c050a050a030809040902210c1008060a06180302031905150415090c030206070506090705060c1009050111030f0601021b13050c04091112010614030406090c05 78
    0x1300045d0804140076502c0642c0c0c800b45441e5140208403440480f803101030110341c4208804c6169091541201c0ca5003030000d0098101031203038800d038514030400e408181c80b40d900001e2049000b07280c05d4861100c00413440c6003142c0303a4200074000030400300192180a052102020310503c170080c400888400440c5c0017010380e1100c00c80c0b1283e40c1d030512141a030840c1c1e82c0c00340c0100e0403000400c029a06003d680c11980441440760303824030400c001d148084058641130000800000183e4941005244841c410302c040d003c07508103800190b18004064100a1058100344994282a54002880c0a2150700f46c000803400c20490f040c0b0750300420101c22212111900002041a003a007101041d5000300c000b070342190444482b004e0241d01c07101510020f00e0340001c0d0b026aa24100180740c200302d03040440801490714165039140c014003140c0c0c1c0c001081a0700b440103c0e0803141c8000d80e030751302401040c080c18071202d980c005034043c401500c001400180038587c0c1c0c820340403e002200c1d070401c024000c0a000301c02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 34159061 1250 34157811 34157813
    0x1a0403021c0302030402040b0306040507030f021f021b0411070b0a0605030a1a06090403050301090e100510031a06060417010603060617010b0a0e070f0c06020307030b0907031e0518060103 82
    0x102031340c0b04440503030169003041c5c2d211000307040024480f0302c06c6170071001810103c0d0031742d41d5503041414806003d1b688140403400c0513015150234060100402003a07002031104140380c003080088a4a002203d61003103241c601e2901100d1500c02c200d81c0416440040302c101540c403001040000c00154100d5501840303228882401c01040312050881b0b18502407030104980d8444080250300c0c0c0c000ca030001d00080c0c05200410408816070040801d000d841001c0e00c1d80d03011002009421620110355044075240b04232002c0043c410405000201d00c00041030180325440c006000c1004c80c40b452040e00611032206564050b1100c0c01c1d8806400b45900a030305102c10360340e91211082448102c142c0020a5286c080d15184078a09114140308441a01c03400b00da8a1750703080c1003034512050311650f10051106c007542d0b443c0006d0032480114070820f1107840018001943d242130000c0700c0c0c4000c0c4034006140c50025100e03100069040d19452000f42d118021406a80c1c4c1d86078900350190b8070074544150310441c4000300c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 34160311 1250 34159061 34159067
    0x21012022502011116090b01051c020301180603020d0b060d05100f06050418120318081e0a3c0908060c071a060105040302060a050304030e0406031a0403021c 69
    0xc51118000d0760f03404401c002e0000304d45d454207041d060300c0d4003100140074200031114040c1c0204512140506209080078208100c5080006066800080081c1d0000044c424891305100d41c008280c0c880004000080c00d5030302103191460680d8001d0a070440c60800180e55540d0902c147d00741c81d074820203480b803089101a561002e8040e0351540c0c5e4206042020106681c109440350041100091070345a8034104191280d526001008160b0310800d42c8034a0407500035500c005907030382c0d050b218155007a0b407050340d00c4100d0108241c2ca0032203450035804018401580d40d02400024a20b8144c0354000c1d10306a40030101c0d40d003038009002c000e610501e56004070a88a03000b071402e104503100300094070141c0d6107105429100c1c0c407944000602d1004280c500c0e1403a901e0441c001a0300c10b2060402c03528141e2250000ba030203800510740c03000081c0c400820481055800401a40c0b41c0105813014041103040d5520300c880c8508044010540c04084400101414800c010418454070b80c0340e0340103040a8a54402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 34161561 1250 34160311 34160377
    0xb0406050903060f0402010e0112060504090c080705010c0803010b090f04050a140108061618080106120606050607110609040f020a030b0a0b070b0f0702010905031314030a02101202 79
    0x145102c0d010703010001c0e00800018441502c600e6050799134000340c00350710005540700750403040c41d142050350b50080881c803a25030784900c3d0005170090414000041c981000c441c6014803e800141c10014071422145c0003403c264252419141c00244868031281450041810f0800540340180d01c942004240405100c85501004c0059880204009242e0700d0710100b580d12a01964160410131b041d40388440d41a02c2210014000700c2d8209008200e2036450100b182500c0e1503401c076001c00c600015104041100d035224040c01420203407000c0303040244a445103103072120030990f214060301d4000340c8031840307655a81c80484801c0203914115200c0100313080042c0207210340f5400c0b90055040e0300340419400d50b00030aa600042e40000e0703610040d580d01c04441c04c0030074083e16100c150746d214034007000042c600340040c00c603070100c0c1c00c40080e0140c0381c10300880c46a0440b2281c03c0c001c0d000000034401603180c1c502c001101b01000d0400155950200034484004d200c0c40603015807168072141d61942c0340d1080705030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 34162811 1250 34161561 34161577
    0x60c06050a050403050a0e040e030406020607020d09060f0e0105091207171b0409080408011406010e040e07150c150e0c091005131116051c0503010506030a02040b040605 74
    0x1003000240c0d10a00410121036080c1c1e4041c010500500c01c0b05006c070320441d00d0010140001e0300204002404542080c9181c001d40c1009026030440c2c020010916030411480ea04c0003aa494045402e52918501a0803886030690070000c208101c03c0194031a40648d084940e00030000d40440600d01d4040308698680d12240a00896040d42c00606007050000094072200810030f00c4002e50003004541c01c0100a1013a0b1000b01ca0000052000091041c0f00784242a42565542000030341441e150000410350100e04a245105910784034181088180008841050710701c450030622900e1110f56040d10000d01d82e5000606144c900001e20f0203054080d000a2a080d22900407110204400010014070320021100300400f1b4102c20380c20045450301c0c1800070100824581e0000b0715840050000340c0301d44c03043c0c61000c8081000c1c180e05041104c1004942030f01360100c0d81c910070042082000801d24803040c071a0714031802c404004107007130400d2541107400034085010b11503600e0b80d90b00e501070050382002c1c0e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 34164061 1250 34162811 34162823
    0xd180309150e01050d0f0603080c0a020a0f0305060a0b030309060a050409060e04081e1204050a0b070206011a030c0408030c1e0c0904120c020901060c02040e010c0903020d050102090901060c 83
    0x10031603844500603031a21000c10b00c140c46580c01d0134426860903009103070f4a1140d00505480b4100007020400d203c00614180b803100b00680080078850041c011040f90580c00005c01c1c44010741d0800c003140011907440e13001030f440300c1c020440054940000e80b45000340d075102603018030700244059003d9001001001280c0d818901406403503600d000068140d80c00300c502410b40780c802c1000000300780c00b050008410541b004440360070300f410100a101c000c041101e04407032036840359654206014409821903031041403807008002940c140402007002082c22661509580000b20110b9040303410a07040c1c40c05401c03081c1c1100c3d103036041117144941d60070b82c0c82801c80c1c0080800901d5103141001145140140b1006045114907803203d945844400c410144039500b0400c41424030030069440c1c0280078020501341e51071010b00c025600402007117600801003440240e1502c002d2401807504400b5030000c4a4040b244036100c0303400c60910300d019104405140303034400d8a070030000c150380303410107040b10246010320 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 34165311 1250 34164061 34164089
    0x92111150c06090307080a050a02100f060602060f1501030b030f060705130b0c071a07020306070201050115021908030403090b0f070303060503010c02060f0a02070f050606010e0108010612020d180309 87
    0xf65409459118042c4040c0c4190400c0150045d214000e43c002c000200e1144100c400403181404001d003104c40711400340b803242e6110401000780d594104542e5820020840701682c0b5402c16a4400c00c0a01d061034450b818942c6036840d024195805100342b25031150b840040e1202c0380f030486401805d650107840b00b4100b582c141040031404a02c4481a0780300c010041d0000c21440f410001c0c03400b00c0003610301ca0701d000e915081240c000142c0b01444054000c80301d50f0004240355050401c0455881400900f15045501c20f09120400501034500004480d03001100b9568980700c909045441840a42001944c6200042c2480380140c9040c000e29049002e942c1c2040b03070030b07207501c101f50903a1005070000c0d00503440400070a00500025824507003092503030f2001480e19070741d82e0380c108d446080e0b10317003e0b1800d4000c501000204d58221a041e05e0401c000d2808101c198140b20002d0480a00800c4140c1101e601142d100c0f40500a6070041a08440100510580001519009000082500034507031074400c40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 34166561 1250 34165311 34165321
    0xc0114090a03020703060b120a060603030e0105070f150b09010f0812120a2c031309140f040507120b060a09110f090a050a030c15092111150c06 63
    0x200785440703031a5250380034010445c030b075480d100d004e0084180d02a900c0581e5031005102c2000401035820050710440303000c1450342c65802c01602d41c8608091540c1801400c00c600800580c1c01c3c00052800c650288440d6100e1014140300e00c01880c40001594004d4021000030a180c0c0301400c4403000c6504000489034040f10400b0f0907400f074040c0c1700c00b00642d0b00500d00810406c1032139401250104035221110b4040d840d00111450254005408040c0c564100040e0003001c0081d030410000941400c010602501001d1001600c080c200103107c1d5924141d948081420040284003031700040004880383c12440072607041940000c1400ea82071441140911400541480c07607000c0d010204d01241b1407281841382282d41c0c541952f110002050744098202d07408102c0340e17948450000954000e46800c10540e00700301a00d407840307410101c1403040c0100c01a0406c0405c141da059040300030905043d0404180e41c516110100220381d10020794010000e00c3c0b144000d9205101070841c041c0144112170b00390303c038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 34167811 1250 34166561 34166563
    0x170106090207080301051e10090501031a0312071407150f0215060609040608030301060302070c06020708030304060e010b091f0e040507030b040c09020d0b040b0102060601091401140c011409 83
    0xd507042c01000a00140010001382c070708841c89000c00d12001c1074001251608200051605c10145005008250121001d0000e568544074040d2000e0101100c59281c2c1c0c91100002c0d500c01289000e1040100002030400401940072420110340f00c03d841120400e42d140c954981c0b40c00300c0b0005140028800b00c0320380700b42620008100000c0b0001d103c4100945e20343d0f4040c00142d9001280c1d440d0416203400c0006001e24041001314020b1020355001030300e440e9540b600a0100d451503016104540c441e1b141440401000303c203c03904607500c0f070740025480090a8034640500549040907a1140c1c5003003c101101c1d82c2d107080c0c500c803440c01c100001322403501c0d494151014a03050f00c0251507584000401d00029040080041d005801661a8031070507590780740a80682e4003010b551001c860720351006c40c1003800c0c503010342020510309002038109880c1c1403000030b14001c258810342c281c102a00d01094a00c0c0d014581402c0541c03194108143c1e6070398441c82c880d018200c10b49441804440c80c20000c2e400442c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 34169061 1250 34167811 34167817
    0x82e05040b010603020d021204050c03190b0703020a090803031e090a05070b03090304030c031a010f050310090c080106030602120c0406320403060504151a040f0f061701060902 77
    0x54030007a031001e243d007009000c4009412145001801c280c0c20083d01a070b00d0034266600b0300c243c1c403403001804d080c04400181814000c01e84001e50803024142c074039100003a501d40721542d210340b1070318006841c0c0000442c1102d092403917910110050000009020703d140c00107080e0703d4080200796814a079519508980341c1d8960030002c01500f243c0048509100c0504200300071600090003804a9007410740700d8544200c40b4406610448040c00d480c00070078a418041092103006080103a4220145403130040807907141c007900c288805c0c2da02d540c1c00c18081045040490800542072200c000c0101544910b0301c60020b5102d0540d000f50f010740e42d00040d40c0466010300b150180d80e00c42c0d866941e000707480803070110b1182c3c10b007803480314900014560782541c000700005080214060740c030100c0c81d030619051120742c5150341082442800d04000c2c000180300c08202d05080442002c3e500029001d030804222802000f42d21003d80545007003960008210000b00004108a2012002004540e036146000ea08070302c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 34170311 1250 34169061 34169063
    0x50a06020a060b0d08030106020a03110c0a0e0603010e0313030c050405040c181116120215011a0f0a05090a0b03061807021f0f061a030a0c0504082e0504 67
    0x1038441070305200081ca4a402c0b910030340402a2092508406541e608000e07600240c100e4801640140310302d000f45a4842c50780b03100d01f03084001030103079507086101040e0384074800d000c2c00c2010030002000c59042d4500354080c6410440000039281c8410221303031600706040c800c5c401614042200f000c04207035860944101402150302c0340c043c140445c5825540703c04100400603880c1c1e0b6a581700c0c0300c9426449280c00904c0c3d81d40c59600c20003400d0040b4946561440b4002c0c0b401421136004c00840070305598492205e9054405105014108010280c3c06178641d1045c220b071141c40c0c600100380c1240d51600900070b0096a80c00726040d2040750344070700c500031031804221055503114412124001c10f0744103041d08035030488042d10540c0c81040d440b101c0c00c0d401180c944402d548607966041405180a082d104080207001620100e04950025011440e480d0102070408000c1c1641e4101814000340140200c600418080c0b0aa9001c6201c1e181c040f00d2600d0004800003a6400b0000600104031a510800e449a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 34171561 1250 34170311 34170313
    0x2030c030d021c02240408070b070801030201031d0d12020409061d0714030604020a09030b130c050d0b04080c0109020a080604050105010504050c070605091f06030515060916090b040b0a09050a0602 86
    0x250741150010914058002d440d11f01040144a0200d02c044c4c083c4c6100b20f0340c0303032184046945144001003c03582048a1410299064102c46507406000310740d0080d50303041840e00c0c0305600d80ca200b40e60000c0c41a540107007181483e1050000b0328203001032005c1114a4511809142a90b490f00c05403000b11041c05c4007101580204000b40080c90240e000e06120300482c604994555201d9542c8035035480f050326804101390400703280108200442c0e80340400350100351402c1240d0811035503901d000900192000b0f1641c1004130705401808425440748002c550010201007200da07854403000e458803030a8030103460075401d04d030012034542864020140035480101e00140f030300341c00ea140c5100505010b000c0e51014040d100a46407410109a41c25820301120309002810303a00c1c5107040d915143c0100c0c103803500d195199040001c42d83d9094412a406810078440b8894070480240403140000d00350018100700501003000320f0480d801a01512449500d42c55814071503455400f00190001c40d4441c107801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 34172667 1106 34171561 34171603
    0x203010c0e0604030602030a0f14090c10050405062209140a060b03010b07060b1801150905031b040e030705012003040209010e0402030c030d021c02 65
    0x21400c06410a5992205410701045950142e031202401e9241d010001403117002c9541c12070064110b40c0b0404020060301c91008001c401000e0b1020241413003003100351440307410000c1d609068402c00d80c86682c100742c82c040070014107902031071a62001c03081ca80014441c0800e01c10a0001800820f40d0104542c241810043c0302c40800030a550076880c14120208004107600003140d064039480c0203d9961003580b800c10002130481c400310960001c0480c1000c2e03110342c036038a40d2541030742c900c183e0740d0060103032110080324840e40324091b4940c982c02144054281c54100e042d034143c0325130003400208480f040341e86004e086810900003600d40340d442d25280303860700c03112041c0c019010443c034020a041d420143c001c01e8120f9014000c40124082423001300d41903507030421a183d81001c0c018112081d070140580c00039210394964907111114850b811014600d14000f0810001e071100d10f40000c00c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 33992811 34172667 := by
  have h0 := BRFrame.cov_init 33992811
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33992811 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 33992811 ≤ n) (h2 : n < 34172667) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
