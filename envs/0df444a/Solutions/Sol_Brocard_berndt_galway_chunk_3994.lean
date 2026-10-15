-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3994
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:16:16.232806+00:00
-- url     : https://prove2.me/submissions/ca3a732a-c0a0-4cb4-b019-05d01277a31c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 718165467 ≤ n < 718345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 718166717 1250 718165467 718165519
    0x3030705090d111e03010b01030b011d0109120b0f01060c03230d110c10150b070c090e03090103060e01140120010c020610060c021305100f0f06090e06 66
    0x38a01000074483c002c1c0d858a448600b03000c85a030b50700941d10260041014251604003503040d040504111500f04685d0300010041030780307680b10724140012402c507401241c002c4043d6200140c51110700c28200d062054a83d01180940c0410b04118543c4e80ca9140a91b40d60002d01d00003400169580c00d40d03296005040c40c450407000d078001203d850040340d03c0490f42610244611480b100c00300041680e0301c010200b1082031090400d0800340403002e070a428488c0588118480c401c0e14a0b000a516400c106905e04c666024080500007006070030480e00040d696900325031b082501007441c01b10085888140704100300e0480d0a50074080081c40c512400442e2200c00103c440c040c0e010aa08210000b0034082c0a00c4540c840c0540c01030441c4c1c0380c4070000341400500399001400f440440d00c85880581c0341c803070400b060601460b40104003921012007090000c100b40c5c0c003a140101ea41c0390042042c110046540d02107807803541d2031401154039000c5500ca0714000352085944200700009640d203040080080310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 718167967 1250 718166717 718166723
    0x30106080a060b1305040f1a01080414150402130504051002090a1703121503070b0306060c01110904060b120105040b01051c0f0c0309050a0b091f090302010b0303030705090d 76
    0x3065043d0340b20b01c503481e1900b002078058260411001d043c006824944100d000003032400c0703c103001051100c0605c20034283c0301d805250400c0fa15400080c00e010038144c01078580d011040440d0750b64400c0e218042c88001c1c058404910800300e00c8907001c5050103a01400d0f000d160401c0180c440c120010045400a511415040740c00c107880c8000056250700860b038850080c0d20160155544104405140d40340c000014000603000020015030003998800190078429100388a41003641c0783c0718000014000c1c09004060f82c3c403513091a00e020600c0b078801c00503140030002514144045038882000c1ca41030301801c2d0804446182035401000760f443d280d0846c800044c41814014030341100b50312110200e8080c452629681d584405064004004902c5050111a2540f40400503504665606512035010311000780031065184081035040d035084c03104191800801c5c10070a4002c4030307007500401030322015405401652a01400095906002c07084038070500305c50f078545103080007070301c104051031030701c61019 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 718169217 1250 718167967 718167971
    0x7151a040c0e1f03060503030c0706180320040e0c01170a0212010f03031202121302060903030a02010504110d020307090e030906160b241201111c05100b030106080a 72
    0x200041e85440340082d8034480b00480c1c0940e00c503038000c4042d00f980c0b17150b44003034005d6000300520419241c002c14048103440507440e1520b2141031800ca0100d00070039a0300058500007900590002030410b14501c0d02d80640c054800780306a9100c00a41c43d00c500344943d6050215120310b6840f40b007554284212507115111890041c100b00300e12404103440d1900360403860103440c036280c0500600d5080143c085a114240000b50728060100c0036079601f0313030005401240b0003e4003200401c1159141d40c252440c001025089980740c0132500002406040143c0c0d05030f905418503086001d02d13007072020248582e40e8001d401040980d150100c01c400070440303000c50064901051180590642c2c0d074000401400c041007000c041c0d000c40904004050300805002d0911205100004180444400003c142e1300d0004a4100e0304d44000011918050b28081060019070ba80c0040c2d80d12082994841d84608500c400c0c03005c10155403040406c1010100d0790181003070421060004203e0a0700c52019103921554110340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 718170467 1250 718169217 718169237
    0x1703040b28110f03070309090e07090e100605030a02010503192909070f080112050a060203041407230402031e1602010e0a02100c05190807151a040c 65
    0xc036410000c0d00410103000400035070340307401080000c000804402103c580654a40b03c580e40c0e02810214051007200340e401d84aa13840425810188055402080e8021040c050081e101c403100d0f490b2100d850007804030900c1c0c0400030480d41000140507076200e9042e1a41031854599180d50391040e0126444014800d07181c01004882504102050103a408881c00010b0080303210703001c105040c00f00400f410104010380340c2c41c5032410340c444403d9045840110300c01c2c09000c050f00b4140c1c20104107150240c000c03400002170000700303d10707198540d13521a12074042d50621520f40069500d0310410464861103122004080c18140c606035004540001d030800380085d414a0003001082d41140c21210880c209041c00300783d4828940a0142998405102d0080c080e1409140d00141030b6034010354212003045020b08000b810000c0400000b040e01240c0c880c8440008503510303049846034080320382120800107403401c0842c2c0030858000c04071941c03401594036800344018001e00c0f00400c4040c0d611800c0100e4030390 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 718171717 1250 718170467 718170517
    0x100e1f05042f040b240c0a0b010e01080c010c03020703080d09051005060108070c150903020c03100b01091203080a05150411180904030903031d0604080a0204061703040b 74
    0x3502c0070106626110795600c002010100701c00c5030b1200b8041401803000444010b00c2d0031a90015540ea0002d81040580702c1012281c001d2404103400d8000301140050300c00420803c0c907640f000c60403141c01c18200ea9003010404011605403841003002000b6a0081c001407001880410180800e84516840000c1c071180548a5131315003d40d403100c19400c5030b5075030103024007540c0c05010990f2101445c10000c0490301c1c60b80e20030b4101620380103201041c0d595850341c1c0040600c02d20903100c214100504407001401030070034180041480c40362482c0840c41c03e000006000c1008007810f00b599405403a200603580d20120382c2000707010000e210026541d800300400b5582d039103038030491908048690140f5142d4071101c003180442580c0f4201a48200070403c104800254040c4042080e251305107825511040c80040d10240007806125203079019501050114080c00c000945580481c000c1340d0520056907110340c40f001d010354401002805400410080c0300e551180340003002d200038405a80042d0703c00442d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 718172967 1250 718171717 718171763
    0x9060f170c06120609060f15070606031b06032301180603050d0c0203061506070816050712031b030e100e06190f080c07030f02030714100e1f0504 64
    0x151042e08020f106601340001802d000442d213500283c1915441c2c109900c0c540001c890050800144044d0080010840100074141e040b040085501109880b060a02010380d004420703030038041e00b40060318100c8241d000d0b001036086807950b00e0812650003c583d080082d03886240354007902e0f01c503c46486100c0000040d10800825030f940311140d40c0c1000b85c52951042505200000c0c008000e00d20503007049000c13695802080310450303580211200d41e185208400040524078041015003607024034503000643c403130004054103071144290b40b041047d4520130407928010b20381a101900064085600c2c00d5113080010107850182020f080001604a5940001e6025448810b4071195100080402d101c4160407220b400580c11003410f1052140c034181c51010a14001c2580240400c050380c02c082c0840b0380240212a07aa50700111080c012400000b44a6941c001e40895043da091a0207140d84084e000418884588400c0e0f4405040c0d400303254260307801800010b00142c5200c0c90700c1d051010664660 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 718174217 1250 718172967 718172977
    0x10090c060804020105070c0f061b0b0106110a06050c03072c0415090e03090f101d06040902030a06150207030b04060506040b031501090b120303060d05010b18010f09060f170c06 77
    0x80380d0008a22818031a0003000304020381d04c21014680c2d00ac54440000c1d4054505605680e01c2d8545400200051184180340000e8020701601107840c1100340982c050b44400214030034041130305c640c0d000c4260304095850103c8150700c0003044840d916407a0b50700f450b203608105501760941050b040c685e80c541050400300c80c1c4012065843c0e500002e030342d00703445c10009a07449201b0000c035a104100383d0b540d207014142030720f982141781ca030a03651001d2114503561601940c000e090002c0085403070b880c3c1340300014002c008500420001030030a8000b514403600c000b41400c2500d030b0000c1c80b20010f0b241e41d40c44801a04015144c0c50b03016480302c40c07921f00c58031700700311748510001420343c080001c3d49043c0200086481c07660f0801c2c010100d42445442d28180001140e400641c180d410452001040c10400d004000040740107a0250102c000305a41440702c202c070a0585041304a4501030659502e110401c8500a01c280d20320014000010440c40d00b44014560740c080c16981540c0c1404003220000c4c941d0303802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 718175467 1250 718174217 718174229
    0x70c030e01110f1006061b1104060312033c020c15040b07090506030402150703140f04181515020c030d05030a1b210e06010b0a0210090c060804020105070c 68
    0x250a07400710704e5601e00882c0b00a003020b0030300500c003484100c0e014040c020001f0004e40300340c1c840e003c0035032142c803a070b0320440c0190740000c03a041c8284800b84000700030b0f25950321034562a01b02c03480071944030782001340900c041d03990348042c82007845400c499400c06500088000c0d501ca00aa81d403c0950050f200c0210384074600c10740070b00186152404000d0000c03000d45d00881d00403403040c010000180c440004a45652458009264036000f451030100c4101c0804801455201c40228004e007642442d4000342050fa80901d13800c014410303444e2404400c0f1000e40000c90a0083d5612003000400c411070101010310440d4810344802c0819a4046864030240c1c06070140014030010801100c040c140c0300c0e00f51440f0f81c1c80103203151404444002030420300d00e00880032100340900c1001c03041c41c0e03440d0302006296802c8000d9840369030f5640300c0d801d05900120205c002601840341c004000c5407803417040c1d0348902c0d8000c1d0030b07803c52800c05200311042e120040049040c840300300109008181d5440781200203001c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 718176717 1250 718175467 718175473
    0x120b09010b0c10050f0f0a1d0f0f06100e0c0f07030206041e0201080106050a05091906030606050c0303041104020d150f0803041a21070903030e0603070c030e01110f 72
    0x2185801c11860880755215941c2c14503e40313010b01010b8816003600e5a0000c40d402c04620351030b11180100002400e100b49490210002d040004000e080c000c03d40d10310405141c4281c0c0e2504d0032410015071a9407080f07032500c0a036480d03d08280303c7d44000030402ca07044445880d8860409000c56013074901580900e6054001da0320403001c003c03c02c58a0401c0c2007a80e101c8929004c1000d0b403d0780081c02c0e18074103024003010f1000105420070910710a505030343e80c1107002010840c0060802d210490300110038003400c3d002030b08202c408606039000e41c0486c1d150160341001545940d4a50300c400c020315181c0890181d0042c1c08100294444030580101d003c800b880056612a040ca030046002154855a0041e840c0c1e07001031104002003207201002d182d0b10034039500150743d1482c000c0600c0515007032a0302031010b8400d591301404585540450880300782d82c4240c071603c6001d18440100821400100c0e0300c9000120031034404800039100c0d070000007000406061090f0074a50220a2605041440d48190702d0344d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 718177967 1250 718176717 718176727
    0x604020c031c020c1b130b030c0a03061506050c07031b23280501030b06092d03010219030228050c060a05090a080c0a060507030203270d120b09010b 65
    0xc01c0c07080300e44003040e11222000c4402c00c503006c01c45505c0034400ba481e4180e50340d52512000e44040c882d02508800052224002c69140d00e0b02d28020b001c2507204060211101001103907290240c81110042500c407002801e41c1443d40d5220741d400603800c0d81480090307121010006001000b02400c000c40a42403003000481240b0100380045000007508180e036190480c41941400404d210615040d90303020702e4085001000c0201041e440c1c4100180d290304600130218020700036044070840980016840600001e000d855400c0500b81d01507117602c6842103290f910321415140c001c0c2d005148001e10510711540240403c410103403503501204450340800c80c002245041d15505100032640000401000c10040c10700b03c81450b5280f00b400001820303500d000031000710b0454200020f0103140d5008106001c0742c903048a000700a900203490348811000d240c8070217503044407600c01448030240003030000c0a600c001c00780c0c00c07294081006100d80c81c40c2d0340c0c0e80d043c501540b034003d40b0b94060322402101aa8030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 718179217 1250 718177967 718177987
    0xc010b100306060e010f080a0b0a0506031303021605130c0e031c12050c0a0c0302030c0601032619080601050909010e0708011e0501120209041a030111040e0604020c031c02 75
    0x1356040340401d5040041050324441090780021083d0740184904100203814198000800c04070303610354101035030040c0040100140c003042040d0126585200c0d40c01d44032915128804016240664001c0350340c490050100102101903d0307004082402907494842c1410000e080840d0402200140b22800309460310901d11189404c000e450403102c1c00d01034100907620380140d4180d118004d8441e94010800355801040625200704140d40d0002c1d60302c0e003079520f5035940e4030b0042000380b00203042007580026070300a03d400e41c90010a89140f013204003100d00001940d0103040b44d58881c01451079050040a00000d006912041c40303140c0601040e03141c010007820940c60103013031224140e21400e0b0406180800c2c488102c50a8603602c2181c00070700b0b082540c50403040401c2c3c040c1c0286080d80760002c2ca00956600c80240501c080340c03407400150b008120b039131004c15540c0d469100740e0094030001d80541c40407030030509280e03004190750010382040da400c2c0000c0444900202020000315000540c020800000b8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 718180467 1250 718179217 718179227
    0x16050304022803050c1c08030c040e011503110702010f230a020f0106050a03050304090203070909020f0a14090127081e070e070c08070f06061503060e0106020c060c010b10030606 78
    0x45c12085a0404007603030844501c00d0303511406c06006081c141c020000c144160700200640d4060b125000b1540c02a60319452080200c1c03040c0c0c0404400a1308207190000208181402c5841064042e1349240f9180c0c50034100759200c400c00518441092203840c03a140340041e8120180407848120f6010304400c1c5c140d00faa240c00d44945400c03c901c101404401003000410010481e0100c503180480540c8075a103100d800d0b40c4210045d0700604813140001081280d500540c8002c00d000301c0740e070b00c508205030b038081c140c5100c50042440c203a0200c2c403c0b0079044d0720341e0201e4030b00c1440b852009000c0c2540703035200c5001700d0070540103920341e450940c00c1403c1c01c90712240900140000d44001180403031140b800e070b8002444c140c104070740a0810440000d08009001c62000c03200c080c2d6030010320911400d0394485242d00c20380c103001600390000b131400c0350100b16988811825070480349140c2c01803003000d03001760030856250701041404e4907079940d400c1180c039a51150808110b2030112620300290551500304003520b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 718181717 1250 718180467 718180483
    0xf030e040e071e0e011809050706030e061f14130603050721080306010f0c050d080618010b1e040f08030d0e0f10020d02040f090219081605030402280305 67
    0x10036684140a01803040c84120f6603045940400c6d0500c03a0b6442625800010b0484000140250146010204280b90190040b240c22841c1908607903040c0d8555449411008100508800e5080b903480c00300003900a2004442c0c08800040120218013400703a11a0201c0b5002d501c1214543c000060800150007146111901d045000c0d85c1d1222510036503441500038880101342605100000c0c0d103182169124008280f1640d520804a034040440303041c0140200d80103c850a1081031300f2641c07000707001458030f83d2038100d03951040e0b09030030040303400101c02168401d4461001344c104107001c0081c80520004288000f40b173307560041c1d941d8544034030011007640c7d400602d1200f00d82c400b40c0c90303a285180004070841010207a03031006844070410340707151002c0e1089900070041d806030b0700f10114200c10964010640030071184c0d18022000701102042d00d1011044031401c80c021400458980280d00840085620910040c044000d4800004049141d11000301034029042c0c08501c042c420441c04012041c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 718182967 1250 718181717 718181759
    0x1109070206091c110115080606040e060112060e0a240e0a020907050c0d120e0c06040e270d09082e0b04062409030f0f030e040e07 57
    0x1012a1904480b1660b88841881c5240c000c621a004080b007001d120300070180c22a11484028000c1351100360007000b14024501850741c2034014180400c0080c501442140e00110300c10f030107046242c0c0b80031200e100c070000341c1d40c00b80d49494841c90710340e0143c0418004460400d00c962022154031002c420384d1800c1c3c5401c0a100d031600d51402600b401f0000740007562100307003641114070b030140f96154041120a0701403012204443d01c654200c01d0002078003c106843d40c6200c850b01042038404040d8002c1da54004854495005601040240600084642e1203544114204101c0710410b00b0102c181c02c04240a040c410099009441c0680005510241c42401040000f00038030000782025002081e00d26904200701c80c078115240e103070b12625401c1c1c2100300303400700041042081c0c655441c0c400284100714103c0b005c0070132545806160003070103803480c0c80c180c94109040b6003034020b06950b078854030301900c03030141c4c10300001162180070781c1e0780e034000c4514004580c8041e00c0518500b1400d04a0650f00c0340c1c43d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 718184217 1250 718182967 718182973
    0x703080910060e060d020f130e0c0a0e060108040314120a20040b1602151306050c03040b0f19050c0705060705060f07110a0c060e01050a020d030f0204050a0311090702 73
    0x812083c05a00c00355a004501115540074151181c400581d4031010b4a000e035401c074105c0301400400c0d03005540050041c1c01620141c40d0b0403003e4000b0010041103c1c0562000c1c2d040c040b020620f01c0d44a880d1541e4018403034100b543d00600c01c811082c1307558005c0002310480304146000c000c2d1482e60340c06071035a46121100b16807509180c81824010b503001f01c0c004c280c22184c01107920181c143e20500200c0e0020b80207072460301e002001a030344110a502242e2400f0400c2050800003c005110301c0455811811000156081c141001502c20907940071901303403036411a00f809822110f01c40343c905010880324a880f0503949100c00c090031b82c2020141d5016a100300c0b000d010440120700702141850380102c10701040106070b070382d052080e945403207590b44000051283d106034408022006070104140c1d807064481e405a4901c00d801111240300d002060350060308001490304010b0b01a0f00300324408403007c5400b42c180b40d1903002084010707050f90b00036901c1c52030100d610b244a05000711070036080101440a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 718185467 1250 718184217 718184219
    0xf14010507020f040c121503030305060904050607080a111305040b04021812010e0f010c090e01081509280b0c070305030414030d0218092505090312070308091006 71
    0xd4200361903002140d0180361181095407801c2c6c4241000c001490155030b00f048200100f411509102109000c06c40111303280c030b0003041d0035281407a0024403c0c0e80c0700c001454940d40d507980466810001500414425031500400c0201c600070318054441c1022030340c03142e010345142404100c00c0d505000c8420f13020300d104111000b146003000358100100282550400c0c92406a440c55900402441099075014003402420012909064000c42c88081103030751510b51760f50b224941d0f00c10182e004e21407203015070310400109100094031468180e0040403281958440007a08406400d0310002542c850304121000b600a010040243d0720940c200309110b11076420074826a40c060500d21014101508400d0120a84540100c007001101c032070004843c025510307100302e4241e1002101943e03989511407414200046e1040328801c0900c44e0b080350a01030b810502e040d003082594903501c514201c60700340c01101118401c2c02c3c000d2004082d100d20a0f0b0b200800d81c90a50344480c01c0800c4a02c02105144c20098 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 718186717 1250 718185467 718185469
    0x9060f0604020f090f180f0403110114010915031b031b061b0f0203010f05060405130b0a0209010e0d05030726040303050918010e01050a0803070c090b18010f1401050702 74
    0x3041d24290030003685d482d002c0c11403034000034100c441c2c030409400d0720034210380c00c100d600701d0100b40d200c1c02140319843e2a10200c0c13070380f5401c80c2030310402d503c042c80c00f0314020010840c80000da003220300b809038800781d001c014503189e132940e01d480ca414446a20f070100340c1c07042c00c104001c000d014090820710700d0041202c0303050404400800100e280b824000003c0f103406800000d100d98080b8800b6a039600074003c200c29104005000c028002c11612540324628100c00682e010181c0418891200e0b4015034400c9207541c1c00f0500c074000d4100c840c3c800c2c10003124500303d2a540c0c0702c100c8000d2200b405180110303200c00e01840c20444e02c0120075041200c0105031002c08070522240c07010b44007903a5141c02c00072744031000040070811b2a60129084541c030448200001025001c020041e8141c940c00c1c0c45000c151510740540581e24400c00000a04811a400b0100b0011001d17502144905000500071551185621000004140c00b07800c11665100d0580003004180756070180503001c0042802c15604050040d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 718187967 1250 718186717 718186747
    0x1d030702030607051b0102040e04030e030f0a060f0f050903220f06140c0604150609020a1704020d2307060e030a120504150305100504060b16030c020909060f060402 72
    0x2803e094107000c8042080403505046441ea200101c031100021506c40e540d480001018180546082d004070b2138040518416050200d00201d41d401680020449581c2e43e540d6840107100098901c0301486d030f00c0c40c40440c0014540035490248804a00560315400811121001058401c80001e084410300e00e003002001010010302040300c00d02d00b041d04c0c12114a003401300c024800e03111032441134010042040708000d140511071094814045040113803a4454100700700303d100b02005c04020818844543d9004c0f04c00003203241c2c0c0240b010300f0041c18410742e642d0b44024510a0000d403420100d0030440030050b0002042080014aa60b24240410a0f21800440c2d25500b1155015046165620b810b86600340120100e4000300443c0301c51181f02c1c0c01003070005000f40403e407040c08105c038516000003070601e007901807401a194440d030042e01e41070b4a55580e68040d5a4540124144040146600003503900c0b800403502c1118203102800386840c14048031100d1080c0148410301c079501c10b0002c1100310762a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 718189217 1250 718187967 718187971
    0x3021309020a42080903040503071202120610080c0307120b04170a18091a06030a110d0632210625020c060f090f0409061d0307020306 59
    0x14002c29202c04000202c910103040f0003004100700d000755070809264108145641c118810590fa9900160782c1303500c24a107480b881f45200e080c1e8594040103080c80113482031040c480c840c5200604401a0b401c04110b52400c000049034951000c0507141c1080201d010144404451400120007429540741008540018100201000782c07540010070300090810071055880d1040250280b611512402c1c40303100108040c03080d800c140c001e00c820724000541088036019995203010100ba0251400c1050b0050102541000b4961007040fa11040021038110301c400050050281444000c1069402d001c62510f40b0304040308100c24081e24001c040440814a000940191404449440c81c25020a0380d094540b4100c00071360405000340414801124124207100602c060044114491020421402c0c0e0b1241c440200c0300d07030880010000000c1c104281402051407a4004100c0200c0c0d611010100703003102c010101c01c80f64180d4030244415045001e05000340d8a50343c1c04025031030003031a980803d898100c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 718190467 1250 718189217 718189229
    0x120a1e05040210050f09030609101512030c150908130605090a05060c0a050f01020a140a05071106070f0c0f090e0c040207060219030605010e04050c1b190c03021309020a 74
    0x4030b501c02445ca000c400700c0301d5140300101104e08078201001c0385d94982009202d0420340500c0c02848071445c620741c102440445d003850f404440d41441c00d131002da0380302c83c8019040718002a2402000c240c0c4256116103080d26014461b10707600c0c2d181c05055103034506e540e45c001406100c4148082949a510803400e0000e40d4002d485441c0c41d4a545098507182c030081d0300c40200701740900990031643c02c2055005d04100c95a60b62880f00c008008140c008292042c0c20350b20740066010400d4401007035103803c03a40c5c1d8170301c4064031040c60300b620f98030f40381c040c0c548443d01110f2030204003004006030521001d89401030000c81c0410080b050031a540b15548a0418442d18051900416807009110056040d51500040340301c10710180510144020000c0c41a4090030f030208079502600200341c2032a10480e880307582003910b0342e4502140300c1d01c01c060305a07003040140c800741303c1c0310031044201c50341c00e440e5150381e44915403030f83d0300504620401100d8803504802d0169103141c520450090303541e441080003140c071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 718191717 1250 718190467 718190477
    0xd030b030a20100509040606030204180e1507081005010201060f2117040801140f060d0507091b02061b0a0c0c03020303040608060117010302090615120a1e05040210 72
    0x80050542d0105400325565035002d0f039203540102e556604800204081c0904030b17410040d058944034103400f03d00a9020360700f0304140000b509444114140e00017105403114100720394401c3c4c1c2d40c100300300e6114030480308040018104002d00c00440103110f00744014002c00d00091201c142000e02001c100946441030340500c25100d10440c503a041d00c103000c416480c5d0012110f048150000d0304000b13a0740d2080c840c2711819032a04400c40758807d02904401c0c001c80344c0d49012140e644501e010001d01c04c05002064a0f00e020f40360000454030020f1080d0417543e99504103e800c413551046c006800e09400415031a0481c9a100006070000941d004507182d060030f0742041002016a400c1c046440c610a410003034061000040101300141c1010f0424840c510990741d601120000903050b4103060000c1c44000e4208403504045905480c0c9050500004841e007440241892240c402203414844255903520341b031a510402103a0040041e07c0a04003036103403003418017050402c0d502180030303450340030603090400c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 718192967 1250 718191717 718191743
    0x915050a11030d09120e010516030e040f06050a0602060c0a08090f10090b01140a0b0c03070813081203070f030b010e04020d0c0929090f090c0301080d030b030a 70
    0x150040e8024111010400201ca441d4580d114900b0f00511200700e06a40a4581d520503101d558411403646c80e0020060355a1810f01d0000b05800190f646035500841c28807130480b88161003603d441c03060b42c03030161307a81c0d00c0400e41c14902014001d06200c990044421500154104aa1150620110b403030300c440a1800d01c07680d03a2034100b4181003020103032202145003e0080403a8081d90710707811611140d03000300311505950340d941020902c1682d8410400784c000c407990804018828400c00640101da105c441901d241050581d81c41600f54040c010500d000d0012181c2400491030402240303d41c2079003442c40e21b00c1e5040044025001da4001c1e04180c04250f00c0e1186100d85134468812000f140c100580150f440e050301c200c004029150b0f0312901400a000302800003440041d201640880100d031400c20f0155003426000540560f004100711500500400301000251315038100c0c0d18420300c14401d14a8613941030042c154100460041068201410035601e20700c5d48e80c01003040c2c82c8080d40329802d1250b403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 718194217 1250 718192967 718192987
    0x306010e0a1e091a090a0b1507140a1a0405030405060408010b130c0c0206211021020a12020102150c0706060f0f050904050a05030406030c0e01091505 66
    0x400861412140c20555005001030107003404140e182c540d6540781c9007544080d0f100c03c02e000c1240da90b8152100350380780c41e0300341a003907040c481c112540100684102040740c2080c400400c55004084582c0150a070000400409001a00c154411503003001c3c0c019100c1c0d040151038440b078541710801d00806c11800c284c00709040210401c01c84006200103400726803103075581c800c180d0080032030140c118000d81d580111905c2d0340b4054412080003045903214003110309003075028002650450a620011081c004560b10320b074010907000d07940f140c11046001c03140b440c1030001810025140c00d10003503010022420b22801030f50341140107801d1362030030b0a4000c1c25601a00040b850880c02c000340c42c40c1e9201030400d02c940c1551042c000c000c00760164100b40841a88d988000e04800340d02d2113480500b510110092050740744c114a2550882c0c00750040700d1040c20b10752202415684264030007000300740e80301c000030758880e001000061140c0013424034501c00d40c41c1c03032002c298160700f44244908004000030700c8060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 718195467 1250 718194217 718194227
    0x2511090c070609031707020d02030d0b0d020a0f06090b040326190e01020f070305150601090b1815070201080403030b01050d1a0307080f07030f0303090203010c0c0b090c060906030601 80
    0x9058100c101400404800e040c06040c480150440c1c1000c42201000190f80304d000123000300028500e580210310701780c1440c0c154030080c00304a400702e92000e103040b405000342e66103d00440103060070307501002049144c048081c15480c0780d60b000d03403882241884100b010400303913540740094004000988005409001204c1c856201c1c01220103021f4000c101c101588a600041c0d466040d803003a02118019245407801d03a41c2c07090706200c000d141d0b81c0300700304035480c5000c0029a0f5800100c18100045c01315103035210350036180c01c83ca240350b080d40003079145110a854442101140d00c030310480c086261010503000200420350003400a0141520349016400d9039201c0c104603446041d0811080040290088a02009800301c1800c18820f2207001c0c0c0225040c2c9021501c6454a13204000605100e440e56884280c0c030156400300b1740925039030b11113400150700c003030140e010040001d0740c1d5600e02501c50310f4482194035000d8200283d50f8040c0d04d00c0205926464100d4074600c07000c94842d6100c1d0380d00320040350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 718196717 1250 718195467 718195477
    0x9010c06090b09010b2803141203010303031b0c02011d0f040207240225030210060b0309120405130506060f04030506040515070c0b0712020a052511090c 67
    0x40000003241c00c10080030410743c00001d45400444041e070b02005103101800407030b00041c00200c40b003400106c04100040010404000800319181a01d06a0208400c0d02d2601d8000b648281d011a8548050441e0740800c920303131800180203403c080c400e001c8141c00003000a8490344801e05441000c0941d4609503417201c0c0c08039600c07200244107658030740540c075200b103044500a03c0c24000d80c0c0d6054412054607480d0003518007000c22003072032103034a00034110702400003003628000340c0650140e03003c0c03c582b610b42c0d805808050304200c200729680b07040020084e80340402d00030031000003910510041c00170341d03190039201e41440c0c801107012515460b80c4000510521825150304a03140e0000380000030400d01041c114801d60140003614a1500c50750400e40071400111804c4c400640f51a8a5800055030f4400341504200c40307142c000d222800c015070341030032a4405030b800d50119501040050b03101d0100c1e1007004009161819003a481c40e410baa41000c5090262440c500c01d00e04100040c58826840042da4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 718197967 1250 718196717 718196723
    0xf16061d07120b19092013060e040b1306020712170108030a050f090604081e01020403120305090a020d0b0612010209090406090311100614030a021f11030c010212060d0809010c0609 79
    0x3486e81d2859804040201a1001654021b0148102e81c101d801c01c144144012aa0b549100881603136441d90351106544000340b0f5004d102000c102c10b03101040c203d1000d49051445036603890b24503030480e80c0241c03107440811201451025058018041c200000c0184d5103e020a0b0400703644900240d100155613000f030134501c0e0f41147c0c01040000f00031b840090290142203140c4070700500b8104000e00142030344107500010b88040500d0002c1c1030902d200ba4012680800500203841243d4995800900001007800017a00c001f0092014001c0910344136011802100c0980c00071442e03c01d0180c0030a01f0342000030005401180d668210300305050190080b051030504100640302018494840d80c001031040e4000e0700006000a0400c00f074030700300081c0000351550020310240b003540041d440d150301c0c03081910800040106401c059440c034a4100040c0109520742d9001580351294104186508072000b4070395807040507000500c1002c034014030201e9002c48420302c2d00808950b00350a0280141c00c8402c002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 718199217 1250 718197967 718197983
    0x3070501091a06032a0616030c02090a0b030a0f08040e070201020a0e0d0221010e030d09020f100903030507081603030f050703050c0f16061d07120b1909 67
    0x480801c40744451540340305002641074205503c640041c103685001c0081e41000c2c10118030510030040500720301e0180441c1d0000c086074135280c5520205a0403c54415040f00898007482e180002c618000d60013961042010800f081515034540009541d410360300400f800d110611840e0506103c4084c003200c010745241000800141401500207000f584100c00fa580040c469500104540c41c2503682d42d000b658000300104444403012110251800e00740e610804a0740d80d40e01c0141c1d54100c180302505408662003000103203c03003980144141c948885d48511722450000e194417560316000100b10341920b415161941c0c484201703103081d120900c030303001c482d07000001c054403000101a850340100030850054103046c081b03900d4218041e01518070940c4c195802c0003050051400200780c0c100540b6081c9030074441c201100b44a6160342c81240c400607134120030f03038801c00d014140c400008c00040008000f25422900c0800a94682e2011920040c1046011a6460818840d040040d07040444426001824 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 718200467 1250 718199217 718199231
    0x12f03070822060801030c060f03090b0703140606030907031416030c03050d020f0c01030c09120303021909051c050c150406030606260c120c070308150a0905060303070501 75
    0x85600540d0312490b05002d408241007001c2200c61060706081e040701d80c0300041e1000e86050103019211411044e81c1d80c0c00309580c8581c584c0104544c4079033140140d00c180c8000031b10b04000f5420140c0250014600b40c040c0d0410428030a00c07040c00259002100c0c1c00c61035400200c028406000c0c242100340c3c074940440751148601100703000d42500f00390202c80c4501c0c211408d002051106070380f10030341c2004010342034000103086c071a954080c0e08410350289280c900724100d25202c0704043c0f4a501100010b5000aa0114080900a042c030010781c3c66000b4504103144041d2400340021702c1d400203000034015010941138040c0410108010448400400030800705a03009004021005900144100310001e424004005041402000300111440d0303025010381d60049280c01071414104003806503000800100300c508202035500f84140d00038a140c0043d07940c0d074495030a00801e490b5012340801a202c04801d0100c00030707a41d1a00d9034003103c460300e10106107a0307100c0c00002d0450240d0f20000c1d03c15400d10359 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 718201717 1250 718200467 718200487
    0xa29030c0f0c060601121404151509020d0c090b030a230a0504060605121c050c0a1406010b2104020f03010e010f14010303020303040611280e012f030708 67
    0x2030061085000f80c1c1c602da05142038100c1031003034601e6440840e5541f507105020a01090800c00d65020003080752070085004184080403500c1581143d2060503210f5020840160a1030359000d00003c020140c540703040558201206000c0781d2002030b08005a0b6030b0f480d035048550094181710403000d4003807070080002910b0301a19a5018044c2202c4c100c03a42450a0400301e601d20b400d51194142d00d4540c0018103d4400b0040300325410050080000c090103c01e21030300340e900c407041010000d010303c45c8014139040048400580d01d0444180c01c03000800301c09201f81e0960407030b61100c08201828030f010320151500d650010030401c0d40d84125494041d42444444c1c41c60b80f0054000d0311007202a007000f0052410b813506110800e074021300001380140c00410100d0b01103080e03600b10b03146868807140c05038034015101802e04006005086586161030101d0021442c03590481d4948c0711014007820500c8000a03000410441d44407541032070b40090803401664020400100141c07080d241d072020b20b00e540d0b19081c031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 718202967 1250 718201717 718201723
    0x140d0204110a080c1306110c1f0206090d0f030c0e0405011d0a090305030f041b0e042003030409180b150913020108061005070209040b060a29030c0f0c 66
    0x90b606012a0307070300c0302190000300d00c10121407500440003110b403d0b16040000c2101c10700c1000528403070a12034801c0180003540e0300460803003460041c690321281561139450183c1000801800040e29401401c0d84c0c2d55030729081162082c40011901e00050034144030502516625821210303260480d18007400440c2c401240b41c030070010310441074003441c0ca41d0707203507001142502e101840081c0003e5050010584c1c600040d0081a000f510650000c45c3c00d803040074030700c024452640e01907000d02410809000078800c4641c0c0708040c0303409105401649a0102020035601e00ca00e1240b99040e65442c09410046003031244030b030b2801c1d6032081c2ca08480303040a0b402c010380c8905194509200b100341c207002c58500702c0c10707007400d6030f05950603100c0b0826a9140c404021100d22000b0b0400d0900a08021080050f80c1d0070311100c1c8602d1060a001c0b440e420900140104200c040c1c0120740c0900c20b003491112a03d180662400c0c000c400d1011095480d9a48004400c9a0060040191102c030000c20148003c607004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 718204217 1250 718202967 718202977
    0x1200a0b01260105100618030605070c142d190f05150f04080904061701060e0705070305040b0309070803160209060409080d240f050a0e010807140d020411 68
    0x12210300d001d86030300400d102d400c0b14001d4072150703100c00c0c000408005850240350a08450601c0300000e070660b0303640351146400c1c2c52045a0800024602c24482800c00c2020080c01e040070b07031120020140410480751035a95843c440c4043c90524407035501d28000d1420420083d10240001e4100c0341c204900303484c0c01d040c03d00c950a004c03070f0075003c1c2c1c00102c5241344600100074070510f61414503000c00e4659403078921243c1c0c41044d03a25005074072a54023095042c40c2031704440000b0b030741c040001603646c540b80d038158201c1800340c4070908003c0c0400000300401e50000540303050b10311442c001d958a4072580364081c900519540a12118080400d10045034001c03c0d000b103140b04d009071032020480da5a402040112110b005008106050038400d129014200d0f038807042103c000303200c0c0d22008855800204030402e610340d1101000424140d0184170505180740f4220040c1001d101c00c0310b4650405d00410344440301030007016014840d00719200c40c1e41e552210201c11464000d00100400c50420700084202e0f802 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 718205467 1250 718204217 718204259
    0x503011d010f050601120b040f0c08160e010203391e01060302331b100e030307080915010f090c0c030203090d020d0204060801140705030601200a0b01 66
    0x2801120b40e200442030300601d48a020165114918080c0608a81004240110f0001c1c2c02554490035111a65881e101c0e00e800c800d0701d81c9419400b4031b08281542d4000340d040d8489020040000d0444009036000005d41b4540900030110a0f42214180515404501048001600403000c0c07c03c0100b4070901007001c861102c445000312035280a810f000318242c520900c0000e41100e0703021100a10b00d10080d0f61885492201004840034031032144580381d00d40c01400c40c0c00010109d081c49419003d07001c010200d21407441c4081400320b2000e0401c0180c0f03d010090504003444490400158a000c1c1804a011241c0b8607140700c082c1540c54a60700c0645003460b0040c1c440300d0b131900d4032070600f06010301100c11800c2c1e41503004500d441d001105104d842c0e4001c0d401242c014a2400320303080181d5450080380003425264000064002820f100262851340c0030340103406110042041c04030301c0c0d0b88604000240344c02858980c0c82c0c00700920400340303401020280503080300402000402d50003005e4a03900c00600c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 718206717 1250 718205467 718205471
    0xc030703030c170f07030f02090d0309080c030a0807170f07080405100503040b010618080f0604060b0618060f091c141609051807060c0b220204050405070503011d01 72
    0x314000761a02e103041d084e50740d01d489008450000d180680709801210b028820000007608100d00f2034003040042114030b900f01c1c0421980740007808010000c000b41c100c0c5080440c01070446d001c050300c80d0b1219224190001d000700407203402240b44a81078030101e800c03100080b903840781d07210307880d0500d20602d40182c0511031203403140c0382918581c0e030b1195055a0107039420900c2c801107646010425594012824196000800044400aa501000e01124540400160180c100c1d8500307403600d101243c44100140d88903480521051041c084010000c5413240c60644515030f45001007080b080c0c06000340034841d50b01122900c011f04e940749958107120ba079240705003901d5581e60820804c19444443d80755030802c442038001c0b0108916000380c4c100d5508a60344040ba1030a6144940c0d1150400c00d85401c4034001c41c0ba84800e010811044003411a8090307034000f801c0044105582e94442e40741c050760b0b030180c803940d145e0340401d0a01ca0248084402000024001c0100a00c1c4003407030b0301d140d44024184d4010f54 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 718207967 1250 718206717 718206737
    0x605011a0a020606040b01020708030f0d060501030203010609170a08071a0a0e0c09100f080d0f0906120507032408011b09180f29040603081e0c030703030c 68
    0x545510291041d511464010303009030b6543c1d00034000100030052840b030440c0704207000082c0c0c00806200809605910f070f000e49035030390f0100215034161074883d80b0050403d0720400041004943c4084854103844021303c900f03030700e0664042428544070300440054130710200000c01000708480100741c116800b074104600185039645070004800c4543d0305414442c103800c208240d48045c54900400d6510480e01e990203c2c078036880386031240a15200e40c02103101c55004010134000160084080340c0081c5051900024881c2030500c0140301100c0000601c04280d2034034082076029000360884d2150211000003000010100414800303000c0d4a403280c01c00315440c118154a0030205020104800c4070281c0780c03111740340c0c60310301404c00300040d6940c44203100c0e50381c4101d0900340b1301c2e50240031040d50b0075059001400c2c5281010040c1d812000003c18469468001d040001600d1941174a41001a94510075046a843c41c800c1e1240d22841c6401d9801340400160b420405070076034000c2d03000c410303140d661030204 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 718209217 1250 718207967 718208009
    0xc010f02040e0901151509080307050312010f12060b12012417060c2808060f06030702071503090204090c1a030c0909191d010c050909150604080a060501 67
    0x71703200c50f2030140c1c14030708914061120b20710702004143c03401c1492404212566541a2040c1950130030f1104a5031600b0000d94100043d5006807040d015054034441841c4030313407030880364000740a0340f4880200382545400e01702c10b0380d99641c800343c900c0d402c1c044001d102d4403c4207034842c01c0c1c42105558042c0030307520301c64022840a080c1110a8414490540100950b4840708051003840d0402c0000d40020003000d200b1010030300e007070284605c2c2d4403102e403600d82d403d0518000304107101074001001406200240b007041151540041d2010441d15900900c2200c4110450101c1c0540102c8502940150070060b0340003c003c207d000c103104659481c1c008842e114024a400c0840c1d11056503c02031014080c4140101450820030340c0381c100d03081c9010002200091300c000b40c107480320421804070044c00d990424110080a005100005c00c5601c0c0180c03030030702141d000641d1000050f0445901c02450f6a0203d01620b4100407140a084448100c45814416190800180509000f07051860300100d04545107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 718210467 1250 718209217 718209221
    0x70906050703090b0d270606120b04030c0816081c092105250b0f01061d0604030506091c03090308010302091f120506090d020a021002030c010f02040e0901 68
    0x95a41903548040c298a094100013032038102c50090907115554641c00d03028518150030380322401c2c010481c0001c440780329042c0801103484a034065200211780d0701304100000e400a44803980650705041ca40c5000c1c01e41c1c00c11a015010f45a8a803004640905900c1c00307101800011306038000800c4051045240d514035660195170704650010301c5c8078010f80fa0700e07040d1866110f180e00f06401c0f61038800c0c10301408520013a026084501c00c00c0349a03441400d40000c1c00110380300e255001e4059910346041e035142100083c1402c03180c56900c1c0a40c031112502d60b1455445008580045030460211040c2e03040501c141034481102402c81960001d00d40414041c141c00707400781c0a003581d01070303c421485d17a2031a0244100d40e000182802c0764031000c4009941d00d0900985410080c1012101d800000e5a1030f1420f94541180500284859805003184d021700541c0020300418007981500d03110003018643c102a407540c060100103503d55402c10380098020140c1d980500129204519448400e403149104182 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 718211717 1250 718210467 718210477
    0x1e10020a0c330c1b05010e0405010f270203100e0f0c0d0b010c02030d03050106121e110c0a080d050f060d031803020303042c0708151f0807090605 64
    0xb0420700b00741c0a4246204030b808400003000618106428100c0050f40d500c0b800c2c10600c1424544148001c00c140f06550380b10325039501c2d00005a07420001541416a18103103d0000d00c5403a000302c0805441a80041c2494201005680050029916800d22176400400000d10b40940d0420b070030110005694144507607450380c010b18140c000c42d80b03400c03d0078040402618600740010f042c07001c01000100142c40400000d049003645590005065040c413200a2508002a070b86014440c200301d910821030603100b00e1510f940f14624800034401044041c00c0d00c6501038099140c60900034017802c8000c0c024020010f04c111120540108021b40d19010210f01d490b4081d6a901d03013100740c000d50340000a015091400c82e80040001c0000226a2540024995441500855006110f002e260507107000003c0050441a101c0c0154100d9890048402017201000805482101c0658005040f01d074484020340c0c504005001c0c1100040419108040c0c104e0b60141d44e02800980c0c401800960071348680240e41c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 718212967 1250 718211717 718211759
    0x106080714070b1015030605010e1e0607020a0308130810020313120306090606050405040e0606030d05030a090b04050c0310060609032d030c06150e061e10020a0c 71
    0x1508000d41ea07140e6460a4100030002c00048407070084c0454a0f21030201c004441e41c0340303545c01040709410080010610406054280e0043d407000d1426001102c0844a50070000401d580c901d8030348105000141c03003048164000780004800007400c040c498420f1650030155541c0000711640c540b40020314100702c0c88210340d46000c0d41810240c1400181d0b20030003a08003107600e460041071560706d4407241c0044030f5880d071040020400000d0700f0010341c2464000c3c02004460040602094170708040841d4a614104034030204104002001441035107681e0711040b1101d4000c103914501d03107040c2c03030007940d110140c03481c01d803186c42040d007a40c441801c0ba001e0b820944406540e1520418039581c1c13000c07014600041618000105038025045451502100040481c001e40da081c40c0036506060a00c1190030307a50400380d00000d688400e00c141c070500c0c1c0000350400da06403108204c0d480368611b1111420810040c195226240040300c80860b540060585e041c02d02424400c5445503690101485014020304c550f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 718214217 1250 718212967 718213007
    0x117061512161b03050c1213050f060a05041707180c08060306100501030c0c0506100e160c03110c031605030c1c0201030b01110604050106060305090d020a17040308030c0301060807 79
    0x41c00003440390000c1c11b0940e002004440100300560380300701050f0051304024984070964071040203240f0342450300040450055400601e808c6504000a0040c4981c0c022201450001d294407180d80000304011001840700300c1d02c6419a40c074141448024181d50300d80c440018544802140c914940810301e07030301a91045611111980ca810300640c0030307082004141050020028003800880c90500c24588601140040b02c0030380c905040b00b080c01c03c0360103401000c00c41011403080501c943c00404180400d609810030f813044c10881c0300f10520b0000c1004499405024441c0c2d02090304d030081d64070505441c81102a1a0701002d80d600b1300c0034400f0600215040304a4110510001d54041e41c41000006010724000000781019089107141480940302190182c0d510402080200c0d0f05201e101e8100038040003400742140310800c001d40d9010074042c0079086405500c1c06c0700414040f0021207004584c0400440d07164600101840040e4000b485508040342c04100003940491180c1d00781c4032205241c0d414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 718215467 1250 718214217 718214267
    0x406091a0118090608280308040b0a0e0312060f010318021201090b010b0d0c090617091e1605150409020906040909050f0d050306011706151216 63
    0x1101d5900c4a081d41400040081c070b00400c50750030034094000505003d9004100c3c074922103440e80803020701c14482441b20003000030f03a14002a0711590041d0406c1d017284000b50b00d620740720f040100030450940742d802c4900c0700003002458204c441c0095849804116014100c030000c250040d001d50303d164200c2a0500c0404040b1001840c010255514030102480005a010741c103075030380543c440003030700300c84d00782800801d020401c0a42d41c024a00391030b4035440c00600e080c4c9014400b0b8008003c2d0302140c2e0f07035025040c0c00107003144401c00000400b01780003c910700f22809a0a41e964035116a9564074170040049000816142007043c8840b1642c0e020429852600d881c2648980c0290040000140c1c807001c00c00c4009889200c80c05851402e44c0104090602100d90032040c1d4030b840303481c00343c503400d1280074030400445a80142c680c81aa00d10194050b2513552442d001641c11070800b007950440403000303da00f11103e0301c9101814803954030030390fa01110451030302054400805000c0358041c24403000035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 718216717 1250 718215467 718215469
    0x18071d01141605010207020907050d060b070c060e1201052d10030201051b030304140c01080402011b11120708151003020d0303150312030b060909010e060a15020304050406091a 77
    0x3000450b4070307028a000500707214040d80082c8038040b09031044400901c01003010224035965124a2004041e80000d4503e440c280d03584a07e2208401d00c2404140034078840c80c2e0241d51280324001444c060018000c03c014942210000c080702070614440c0d080fa2145800103d0a001c9100c0c0070703004411845120b507142c2d00d194011215640441460541c803c49002e00e491001c0d420409107002e544924040c0c020644c4140b00d40345084c1010660038100004041400017507600070030801490195036110805400382d900b4140c500410a00005070002c0c1c10031501d85031410040741c0041036414140540d64440c80c0e58034141d41036401502c0c402d5001c15864020801807402c122003221540c801d050206564030b0fa02c00b8910302c00050790082d5807400c83c1e100c000d404c0325071610500b0380000088030140d0500606001045042405002d00c5000200701800302e2200da6034550080300a04c00781e8100c00c200c042c0400002c1d00e0b50010720805010324103000c000b2821080e80d005540e4001d0503014542c00e0312047d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 718217967 1250 718216717 718216747
    0xd15150e03071d040206070b010608150904020a03060b03070e0f0402011b1121010e0a020a060203180409020402190c110d0206220b0c0604021305010305060a050618071d0114 76
    0x6081240d1008080120400150141071224000d01150301c4400c040d0ce01110000f9201c3c00f00b24130701d882520300000b0880181d59414254013131b0390b000400044c2e90070080c00882d02c0d041060b04040b510700c00400802680e061190002c5100364401c0c1d07100c80d43d400d000145c04805240f0b14000800080c210714151003541807401c101c046001300d8120440c503520326009427a08442d0031041d452041c3e008014a0420350425a611900a08151006500c1c10070302d074410a40c45481110118816510b5a16030b0082d503079150155208500320554003070b40003051010141001210704070484e0480183c10030f0b69414546604600c0301c0640140c440d81c074108854040c0c008450481d1544402c0302001200409d042d0101000761035420300b035000506546c207103401040a020940b0a1020760716041c407005100140c808582650440800300300498541c68240009200b8020042e1042d5440e1140080010941c1d0184402d0004180c0241c270009540c6004011142c02100c0c151442034814100301601550800c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 718219217 1250 718217967 718217971
    0x20702062110080318011209050607050d140f04060203090703150f180302071205070513020703030f1505011407080f19050c0a080d15150e03071d 64
    0xe140e2031810030400d101c000040307850032000254080d54000c004100401c14290405803407894000c40c2404071005801801354021215141000240d015610080080780c100b00f404d0380d03000b030540b0000e113031100d0024590780080c14046890b50070400036040302050400c0d010301603c55402802801d41d2540c40d070b01c020b98005000701d2071501c500300000002c141059204860383c040a100403520f2550303014030341c1c26200040b108201da9004903140c880000e030009610801c0742c080346104d00003a903a50501a040107055803107280c010304070b02c013007a5070412589c0c01020410700c0f9031002c2000c11030b915400011070700ca944c0343c81c005d014494020310080d070099a030301c01c074201d400c040301e8504807c2d5601e000c030580103200282d16031a80401c8003203d01c1600f15491003c03842e50b01e000c0c1c0c1000042d082c0c0359500c00c0300d00805040788100040441301d19035682c101c0030349401c1044000c8500c0340e80318070100c1820703200c030000000980c1c40c08040402e45804a01c0008031008030780584130203103040410018402d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 718220467 1250 718219217 718219219
    0x8070c1103100c020c03012703030e07090603061b0309030c1e140604050f1f0209010c1b050316180e0f0d080f0c04031a1807030506041505090709020702 67
    0x52030403580071814603005226143e102d0740d02500c4401d5011091501b940d800f0700c07200200e0703c4c00200702e07684650010896a03685416240104200c0005010503003800042e070440749001c0c0c240080401440595001a0443c2c1d100701d0140403610081001102203551402c0c008000070440d81d5a4404111081501170308080c0900c0074003420042035407070b03000414160070382d5489500541c081009112082c4000e10440296001420342c00e053304514400710390307001c0c0480c080c0325400305000845c0c1e44a10000c01034264000d01c001e22a000002c648140c0301c1062042a01c40e10401000560040084800e00115088502e400c0d9030000060100005040ca81485100d00e100c1c0c1d903520350040c8800c1044c5d00688000752144170303030ba0801082090034001c3c020b050310303c6444200010000580d1018046c0b01c0d401e0300c0200380b1003d4488001e80a00d81c0c28900840301288141400881440030208009004600c0741000e17840441c4031640e0082a500100c841c204c030b41c3c005160070050b40c6106d400502500744 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 718221717 1250 718220467 718220473
    0x80606190311071112010608030706090c18090512090a031e0206070c030309050103050705070219050909010606021612080a030e030d0b1207053d0305061008070c1103 73
    0x2c502c10b000e03403560b0008801503950201c044041d022500b8a03624040400c2d9103c0c000340140d038203058165030307a4403503000c00070304103035913124030805004280034020040d2480c01403a0410088a02c80034000d00782c581c20640d0303140035105980110191180031103000d031070060203d0707000c2c52841c0c13240980c42c004000c00a56000240740b109006954403001000c1152040004ca1103850039410300824440103600b249041c949028188820542c000c02643c00483c0e044500c82c541c12500c4852a4203800d040e03003ca50400d59420a00c4076050043d04640c0c19104070b0ba003141c403016009010050401214805c80026440201040012030081c074000c0c032803152079080202d03040c6003a003241d91542d400b036140e03042200d540383c0c0d001c00189040345030716244907032180007000c103981090005200440741450b542000e03079030750f041580c0751034200309080501100500d201c80d5071000e0b0034014010700411106280b00c0c0029030034240c0501c0c0201001030042200e942c0380f2849814950f50070314950600c0c401c0039450700c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 718222967 1250 718221717 718221731
    0x3060b0706020703090b030403080f0c190e1e090c1e070b040b010b030405100c0c050303010909120f08150604240e0a081009030306080a1b060806061903 67
    0x48028008105081c89003200681d500c1090500804200b03094120b000c2d0000c0800a00c00031a07408034107580c000c901c42005500c1515070a6442c8428403e0f0403020704000ca0000d01242d003141c00c8518401554070540c1c244001d608150401c2c10a40710100c0002e0b4809946800308403c00000d03406003040225490009101d41c0590031890081e421040d021030300109a94100030400440d208003500506581d08014290300b010394130940c4403a64420042c00305d075962150186c005201e00d50380c1420640120540c0d46e2540c440e00c02030094903680e90103540e00c0c0c90321480059198030036407036040a035105584440e440c2d203c1e80d8a14080c10046d094495000d4010f02c804500141d032180040c3c0c0640b041030f0000c2c1e01446170344000d0700d2081ea84c10100c0c0300c1c1c07680607010002c0341000300300d00c00945840c0000007440f00d642d00e0144c2c0145a10340040e451032045640c0703030003040300407200c40c11031030000c801c9601c03d40d42e9410101c0e5940f2003100c116820880500c000703540761200c01c40822011400d0b05000ca514 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 718224217 1250 718222967 718222979
    0x308150d030c1209080f0f120403080a0309021c0807050f15010905190c121a03070506031b0f0301180b0f10030603080307091a0403030e120106081e060a05071b030306 73
    0x445c0c280300b80c40c0fa00740c2041f0b0b805900b0003020000b600415100c1c0f0210ba0400c1e1540d1200201d80c018210240d084c940c9070708000b170455403103002e01001450307241166804131405043c03040c80e90300300c054101c64a00c20150b00104403040050013544940c40004158041c0e0700382468440a04809404504a101240c1d102c083c05c1d00a4098002140c50340e9580c04c9046582110210503509416103101211220824101003901c2c0461003505642c416640d150380d1b6101d1044e00ca00d40300b2a51420b000c2040086129540840391500560403142c40354012a0400394003408901282c618005156110107003001800c032604104400f821000d1031802d0005401c1d030ba1ba19040840d40c802c0300e005000420300101401080300d9000050208940e2000c0b45003030a00b1650041e068100c000a29440b4100300f01e8210b2418009400a1020380080c1003618010402408866051360451400316a1406510002002901315215451056140ba031720b01071036840c90000c551840030300d00001c2d801c054546130701180c0307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 718225467 1250 718224217 718224223
    0x8160f060c0e090609010e180316030e090106030204050307090f090b0405010506100503040b0a0510031505040c05041b080603010204120b0106030c0503011a0a17040308150d030c120908 81
    0x1e11907258035a0115000030008000103440d00a0074544180c40203001402120150700090f41e02070394403045c0c0080c00003410b082603d140102d90700c80410031182070340c0000300340c0c2c00b1617085903410b17050351011502d9889102c10340581c0200d0041c10b806510088c810440c0c102c680d084405502e00754080080d14100750f44408951801c01c6030140d40583d120024801c85060902581c0c541165034501b0505504040d91114166100070b00191031a0340c688000c40c80360b0728200004001103034811b261283c2803030760607820005454100c0c5c05684103040800002500d0800f4060140c5280600c1d184200101c00501c00b503c40620152181d81c05641c280b10110351a4072005070b2101c080d0044103844010b614085008041c0e80484265070700304203052004101e81800d41c0360900c0500e0b210014203442d00b5051008480c49407000082c4030014102c0303401d02c024141c01ca0ba646004058280b9580107110201c020310401210000000780014140f10324000840d184a4980040303810320700c0c00007800d550700c3d40c10f40c2c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 718226717 1250 718225467 718225481
    0xf170409091208090c090123060d0c030b010c0f060c110a03091806030b0106050c0a0605010e04021009050f0111010b09010b0d06050a0501080c0c010b09070201020c0601090908160f06 80
    0x40c1404081c10319003299608850010380c0844d00341c0c0140548a00940855201e15062140700c0c00e800c40741c00111104a001e0f4030b2141076480180506484481411044000d41001d01e0708030042440c1c0080f00314507500c6001003181d03080e0020840c5c11600d009585500043c4a41c050f4101006550700146032100000c1c07010351143c0b03000e0359a10400b41c3c2000d280300100d085002c1e0720102289850003c100003030580142c89e044418904200da00c540241c86500d0030700802003001403d5510b072100219508000c035020500440c026103618002d0741188006542c826900e01440d5408501c0c650b550410f903205070f102e5425000404004200b01c0ba014000c2082e460007070b04821146c480209019000003514030075100286001c48642c0b03205032400d00068240c0c540a85038141c49c400008000142070b000350424008154003825100f0b40d4038141d00020300039000141c0c0c1c001640a854000a00380d050390094401207500683c1c014500305d003100501c2400304080e0000c90b40c00740da4684e0340c0003194032441050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 718227967 1250 718226717 718226723
    0x1412010204090e06010b0403020a0330091502012a02070e04050a021f0509040f24171b0f010c2010020607080406150503100f0c08040f17040909 63
    0x10aa02107890745813418854160030000500c40c01384010000340c1e40f2500b060045035000311900310340080b01019400c52403c10102c15000c160880c1c001c18009600a426034200c54078802228501c100c2418201d09031817090484c0310304481221003004004e1039011100d07051344190f00440ea071407030f80c0d110701c8014400211001ea446400c8064010300350305040d03a160f4140c0308915594100c541d0409c602a085000310280c05005036581c402e40207030100306a100c1c038010030031401040c82c4c02021210851203a5440c0c0210b001005013000c000c05070303100000d00010b0b15080105100405c9000c0018003500405c071001180c100644580032202003000c03885958054800421a011060a4507007030100a280c030082040071544682c0030001a5503018102540055018401140c80c0020399504100d01307116800c440ea01d806185c02e1a4240640e0b0ba107c10301c003080c0c91f8400d00401180c2003060b00c2c00303003080340c0c003030510740c0b0038149100001e0070340e1807211a408503054000c1c28152101e40d0b440444038824011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 718229217 1250 718227967 718227971
    0x1030e0a0b16180806071202070209040b16031401030809030715090503011b0807030f110c1b010c03050418060e0711103e1201060e09060a141201020409 67
    0x5075409075000b0351a01c0360f0301041a10903c890720b0022031036070b586002090720040000007441120a001d01d5011907201c141c008101c0da400742000d04124201c07400540300700c3c002c9220107400d5200c0c0d601078013902c01700110410049001e0380c6152211990707917000c07900544d414019000b021038021020003400d04481e80070381c2d510001e80d0501040c1400c4801e0382d0b444a40716900000c400211030751214203a588100c0794640440e007548440d64000151070310200c800f03d500d901056204912900284590400d000d24100140d18031194006444141e480031025000401c00c000c1445800c1c01c0160300c480c1482e0a210000c1c50b541c0c1d400e030741c4140c24010303245200080c9040c00d0114601c80100074450031046500010418165030168202c1d1030b800841500c037145c9040f5100000217290341c0e4180000711001c164107591340c1ca04d411040c01c0d180d000d014410104086141e09040d074206000c0f414800e450280541d024503007441e080783c1304400804020b540c004410f040d41508460280041c00060840c0200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 718230467 1250 718229217 718229251
    0x11061b060601031116020406050a0b0901080a020a1b0f06050f040b0a14150109080a0303230402150d0914061504020903030d052205030403060b040507020c01030e0a0b 73
    0x4034142040500003904042c04c10014500504041c022618201c013844080d1a04040c2480401c0140c038659124991180c499031000803500c2d040001000740013801da0b03a0880603036402201c94100c0c05803c01100015410f00706542c2a11503850141c41c085005d80e19401e01220142c0d10801640c000721034801c04d0903100c04c280400c1040d0030281c150008800c40b410700540510325a081d8034071000805038003c596a031803d14040e41d000f513000001426840d0b066801c00d003224203001d009025103401030b4241c3d20117588004044511030440c1d41c040c40c1c1c01048804142078410f64100b450b00700010010195a0b80e00301c0b2030004a42c02c22850200015001a02ca1450402c2180401480701c40b550303070003035004004180c0700d80d030040304483c2040440d030000901510750002104221149069403005140e41d03245480c14424008041d20880b0300c43c0d1300a00c03d4407150380900040d80c809a45100150340a100b005201350f00030380000c51605440022101d24001a8135803402d0718109a42c484950001445 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 718231717 1250 718230467 718230517
    0x9100905070c11060316120e0f0120040e010303030f1b08090610030305030c030919030504081204031509080f0d0b0901080f060c090a180209031605100302071106 71
    0x1081e001080f0048407010305500d0100c6007007078062221401b150401601c8039004840140b5503000a011186003022507101d410044e0b00c01c1e000b000303c3d10303005552100c00562224610442c0080fa000c0d508a10a450040d928540d8150080c0c40d601824070704550f2201c3d10706040403803030a00d0401d000e000d540c3d50009407e280300d038ac5092082c0503003014584142d4000503c0400e4114040329001030700400c06031380d02e5a6000d000d504101200e0a0f11200c005502444000c0c90b0303100340500151507a0a090340c2039401c000c00340c000c0f58032451200515081c04a2191201e000301588500505402054560724080e90341e0301c003928a070300c54039840e03034a01d03500c6001c410709040245c911409018604010000045080c000c00d07600c500040c562660703043d0010b600480c0c0e444030b43c0410010500e00f50071783d00d0450701c403076044069002515154000c0c41101400000140c0c40250602281c0b00a00550b0040a04140440103075200500079100b00900818a000980345e480c000c2981560300b441861007203c00d12 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 718232967 1250 718231717 718231733
    0x50903040b0c031308071a0f070507060807020f060f0402040b0301060b030c071127090a0b010303090305012a122a080c0705031204020f09010f0f08120909100905070c 73
    0x18000c942541c1c04504240203040010103c000d03a035909542c0c071500d07503503e142e00123105d01c00d40340024824001d05070000303010394000750350a02600385602594148103002c003c140d07407184115401116204000d01003405414658405400c0c440301030300209041c1d484080c4040390303602c2650244200d43c0c000608105000c440d400550030300c8002c903012881002042d0354090200c800c030481c2c104194000000c00c0a02c03034200201c645143d88003905070340c80c1d81c0d170341409030400034030b0721003601c0d0341d400c0505a03040745000d1080244801003010b40072a07840c23108041202d00640780280a00c030306559000c054001c9a12043d002d5040c1e28200b60f000500728480c00081ca4680c010384850002039050282900144006c01a548000741120640110b135a5034000a40f511007080c00e03030b9400420f80320000c203001da01d074900d91040d9003034040025103659540002c00ea50f034001e000c0c01c0c03401c14001d0000129501e0044913203508080c504060f0181d07180c541c3c081004949003601d8140c0440e00000711401003105072 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 718234217 1250 718232967 718232969
    0x150603070e06060f1c11070c090923010b0d050321012403060504020703080402011b260702190810090b0f0a0f021201050928050903040b0c0313 63
    0x4440308405904190022901d00e00540c5500131040c00041110140f604030600180c0781c58045141c01d01ca09007102c025000b4983c4034290a894500c92400003080340c2605025259140e0341c822000e12041c3c3c00614031081442c800c58000c072031552503040c40303000b5907540c88003141200c2c041c801075540c030020080d106150f400d0011781090174403400c034010440519000c1e81126600c202c000510151205460100c0050506400143e403003440407036500207050780036070368521952007a00d030721480c10710341d040140040c001c0700f00041801003c214100011003841110443c00114407030b01034105036081c0c0c00509104202042080707566140001000982d2003040100203210707489004100444071034031500d034040b40c02003800c001803070b0340c0e4041840703c2c1d51a4850400410030036800c43d02d42c0100503803090950300a110701442a180107022403000240700d40600001c68020301074024500500341d07504003a00c4010300d035026901042c800000d048091000410000c9800d001441c0c1d074000c6210404203186c22 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 718235467 1250 718234217 718234229
    0xb03010c1e0e011d19060c020306090f191b03080a080112150e0a170403170a0203040e04150c0509040f14060f04060f090203010512010e0703081b15060307 68
    0x2c80c88042035076002181903c09410780305820180c403500801203101075211005482c402c204482001407002c1d44000034081141c800c0f01920f80399201c1070b8071680d82c0d54056441c02c0050300003148a80c44540c840525112030340c030420209081c003034480084800b406c81c0b0745c41030700c101d80d00080341500994866101405044031304005c5644e84920788413462065948900c2c101107960f1200501002c1e0010054036554a07844400c82031002e0382c0007084e51242d085448201d4440c0b4150003d001180004416604000f029038021810a4649241071501080240040e980f020f0120301024203211540210401404144c440c560340d50340090900084031182041425014a0482c0c07208280010b0100c5c1500058115040c4408244250004000b003480741e000260240180340001220714403500070394122a400c5407400c2c0044d8040403454240c1e01c01038070807003040d00031000030b10000300703858040e00500040c0124061a001d015004902c0c01070f00401441d07054400d2402c004075850104140c00181031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 718236717 1250 718235467 718235477
    0x11060a02160806090c042f0a0f0c081914030901051b07120f0509130c021203010e010b0f0c0d03060e0c0f0418090503030f01230f130b03010c1e 63
    0x2420081e03150710764020104d128400c5032142e407110400311b00030003110010004104415405801c65014010580c081c0301c0c0c08010880440c0e00707104271800f500030390090036040002c45152003100407100d00b10f4003107201c00380305012800c0c140d07146485c8010007562140c3c507000000116030800821040000611128110344110104040000184516141c8140000c103041825140d0205038040e00d6030f0040080705038015100c2d802d9a4490034a40d0000d84190b000c030740a541944001441441e440d110074001c892104c194030004108088070751008011004440300354604204007400307000c4c10711558440201c00a07484007800d01100d0032035080390f50004401e41c4060300d000828030003a50107001e90310801d024906e003078040c01d030b41012941041e0201c0e5444400e895aa140c001d0400100c1042800b070310380768083c4c207803006240c080c1541ca000d040380da000304404c09221803003003004803102c8084824074109442d030410000c152424061400f10001a4035100f510f5140d1035103202c207140542d0a2401089 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 718237967 1250 718236717 718236721
    0xa2d060218040e0c0f01021c0203070c080d1b0305250b060415090917040b0d1a06090d020f0310091509110d0c030b010f140a2111060a02160806 63
    0xc040050079594600e4280d5044d07601100c5d010040c1d0802c0d80c0f4a000c80c4540c095170401c1e0500c40e5000c401050000e10441b442090795071501c07006641d4080c500d6a9101243e2060710766100c01c814a04004880d500c03034070742980ba00c400385102042011a030341d81056014031a03007840342002009017156500501c03e40d810440c4152440e501c0c0d00a0000d441049001c1d9030b22002c61051000e807080e034610201d001c200e02c1d03540350f2f920703000801d40b64480c1c40c840002074501200d41420002c0f85c801d007920000000e08180c28469117034100702c044280141d040f41c0c4490703c203500050035241404175803a120010f40f00010031040380c4c10201c00201013100e000740e91a00e0100d0240000e8545108040c0c010400c1e9079109807062246000788001d5603039040071b00402d4818000260000e280e241650581c2c211344614170074101c0710010302500d0441800340c0441451081515401c117840d800002c66264051a4100003524801001c162954410304125005810030700c11580004640b580d00001050f4a9004080f54 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 718239217 1250 718237967 718237991
    0x170f1905010f052205030405030a14070f0810050702030d1121100b0c0a0503070f1a040b0718121a0c030c0702061305030f0c09070905030a2d06021804 66
    0x70015035070100c4c80c540002c00441c052040400a0706e01410000e004c844944105e428120364050250500d08002d21a840c804107880942c9a10a005c50701070100402c5241c0042c3d1801e000303040000c1500c0c04500c0103000c4e80030a00706500681d4407a6402d004815500c000f0082042aa00d400d0821003400c0742030b90051100c12074400b01c036141103070031086859440f2130b0a00900360421401032070142c84c81c8800700e070210130300c0b0310000600728403445203d0381d07070147e030045040130b0404100b104d0107802c8280c800b0003d10054014100360040041d80c506070b001594550660000040010409880035140b100103003191048140b481da82025140dc0d240d800d61a254000f0022482800c800034003c61010a43c150172000900004018142c001e0a031607001d90b031900541c2d07a403075038451094401c6d103c0758040345a06008141e8a01a28005030243c400c2c1c84041d103c1e840701c5d10100304d004060482e1400344400b50303662481040282c600c5413002582c0e03032884030f03040a001040c1001591195250803038142e41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 718240467 1250 718239217 718239241
    0x2030a0e0d050111070b060a14031005060a0801020d1b0507021f0e0406081b0913022202030c040f06020c100305130506330a170f1905010f05 62
    0xe840000c0750940201d0705545021409007141c03280210380800085605020445440c0d2403620030760040e44d6090302640c6c2c6040144860018100c0e56070940c002850302c00018150380c12a0b5070000c0054148210f9030b50310a80b16089a01a02032501400e40da191080c0103e40070030005010381400345080b905082e4160006014001090507550012440e006401289401541101c039000c50040023000656558614140c860940f00a0000c0395003030640c43c0c9034503140100c3c0d110700408901100d1850300c40c0c958280b25004600c800c0300816504c417480c0d170307220380320050005620640b2894030340c0b03884600d03050b11501c2100aa0308150705540140000700c41039185d10034100d50943d1145800710341074846014110706c031401c103c0c0180081c0035050420481c201d07031040d4130718024140040500540c41d140c180c0911010003401c46584000f03410403c01822200710701c03e040710b0174008141c40e4003039565009980741c4044d4800085103d020001c201c401d01c0000c0c403451400f404511024001351601006e4408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 718241717 1250 718240467 718240487
    0x610111e0c100f05031b0d050702060a060803040603020c010e01020d060806011a0307032a08060f06040e06091f0f0504050903091f030b04050f0f090a03021c03090218041202030a 78
    0x20440302100050300148801b600050072104003181541c1d612034009102d025050484040c0c0240c440c20300884c00a118520880040300ea584028506141c208030381180030b580040c001130200d45d01c034002c0440101c420310040c00c030310f0034a90340010018503060901c0e08240c016880714040c00360300d80e0f0140204100404495200c0054030300000e030783c00c10400541e806103c500c4000904040c0d000e1601040e600800c1240c000c45088031451b8942288100b04080751080340140c00c00f00c0c0c0264042600b5007080e01c45d940c0c110030300391107174408a105040380c0540c112550340700e5141c504205400f0065801c052280b140c20446901c0a90b25000c20312001c240c4609000004540070780080003400041c07440303030348803076961100200103001a05000c5461a91040c00740c40b1103e850243c0000301d000324000080070304146501d40c0241a0880300c44680c4a82c0b124144441d00c03d054541000000507a07034141140103142c2d000024207050f00300b505100380281c02c00e07030002e0305540c000c00c0b48848554014407840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 718242967 1250 718241717 718241747
    0x90d02060103030e012706080901111909050d0b04020f0a120f080c01110702100c0b0705070f0b040503071a1506130b0714010509010c080610111e0c10 66
    0xc41c211000c800100d03a034001201c0c41c459190020303c0c46d5422040394680d40e00c200c0310903681e241c000d03440303403001c11342214180080c4411750300301081485403801c2a01c2003005000c0c05414000c0c8940e130355101148403c46094000c41310740c0200342c200011890011240b80f2905420740e201c0d4490350905441d0a00310140c52400ba00b90200600c04000f044600130444040d142040006e0140e003405003008142da802085040340715101c0450594951442800c56002054100300c0c0d0300c1c140e4580c3e03681501d441d40400d0003a51145400d240e0b120205d1140110700d030150780300b0310080d03980ba42ca50800c1c91107031f040c00c20303060240720300d490a101810422852a4915102c12a15a665100044809420100710b940f22400342903020400300240300714240710082114a0000901c065990301c2c65070350032610400e81a00201c0c203c5008503840d0304056050f2400c06d100c42c141120b840103c917030690b01e04100c21250f01014185480303040d406a50034440700d82ea01006407500400d898405101410035a64a2842 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 718244217 1250 718242967 718242977
    0xa27060f0b09040e01022704020f03010b280f0e1002061b04090e0304061206060807031805100213050105190305130b071206050306091e011508070806090d0206010303 73
    0x1c5450380d40b5a4048414119908001c650340e2a0901f007140e02000c0d1030210f07208208a00401081c181018001c03200a080d61b523100c80c2c0341d43e08024042c521030300102e02c0038400610f02450068441c0102d40210703024103d070341710444403104154006124400c2040003130b01420001305103071581c680000342d0a0304084184010044507103031040840e1103014039400102c49506000707291166070000b100030003c1e28003e980e0200070801307a2101c0c00541e07404e0301c50140010401350025071803500c241e00c1440e5030880e04800303681c1c0e249e030303030315110326208010101c0b802c11a40001c2d0502c0030043c581c6900000d04003805c3c01e130b0a040a080050000251680410060544800014015054070500c0042d050fa02c0b65900c0e8050904e080010041944a450100d1070341c41c00c00007003003071700d0005520380c03003018a0f50040880c9401c18030760401105e40311018031940d42d2a20780401d110b9100310b940c0000b52003443c004002c010314003005545001d10103843c10031550001030100904d241e020540505594160801d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 718245467 1250 718244217 718244227
    0x120105041d010f0609050903070c0e0402041d06010f17060414120d020703232b111206101e05070803181219110c0a27060f0b 55
    0x11100310301d5400c0d807501d1507529181040800441961120003a91090b1008004a681e1a0b45481e640c1c4a03041c0040c1c40b000e94580d0400504044110f01544580f024202213200260103881c00c0c01c49802c0940040e45810141c014440c08080001d07090041500c1202c0000b8034000c000c40b00e84034107000d4001b030060920341d140c068441204000da030a2440049507401c1d5074482c4001c0110081d001600c00310000381f114101c0040740c041700001500000b070041603191400041c0840307940c1110007000c000300b104500e0606c000350350b0480e108030102d00e10039001403a030310040050070b041c1d02d01008101e144501c0c2c00d1040405403550110305a455641541403019515801d800f040d0703014003032180010200040041040708030001e9500c11210310680400700d400650b03c883c1801c01e9070098685002242c41d041070700c0312000b48504240303825801e8160030b41c0d81001c64ae802140101203142c000030740d50718618542c10078105154001da0b01c2c020b58600204074090500c0c0010900c4461407194a07070321100410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 718246717 1250 718245467 718245491
    0x70e01020105330a06091a1c0c110d0f021c050f070f1b08010f05010332070b030f07020d0e09060f13051b070b04032304030303051b12010504 62
    0xb824114043e0010590500741d5070b01d107402024081c00f8000c1c1d108002e0381100800d00e0300c05000543d0314090210f0020300b00d5a000720a0380c00100980307102d03142000180584d091307500100b8001c0d10703a400a5581d0354800c035042080044d00d00002404d06900d0700d409010802c00a40d0f009007a151040050061103580c1c080c0d82c1400d03006901000c4010745101e0740d42521800c00c0d09803a190700304441d0031200902c40c1901d003900d035004643d400d200c0900610302d98503600820000880e403a00e0700003030400440e2404082c0510451074840b680d08000700e210740000038480910801e0750310700d034000c120f44024400482c1c03e10000700b440c6038420265004444800200b01a5036406100d4c2e0200ca070080c0004903101c02414104003e40000e8440d044c080d9210782e9404000401c080807a5941d42d000048a03001d40c072165403c44000d0700240300844801072543e0840408584103004000440c0644d8010541d400c00826140910005030300300400d550003000400b5001c0c1c4900780076811120115000291000020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 718247967 1250 718246717 718246801
    0x429101202030f0412020609060a0209040f05040503031509090309010327030c020a050d020d1428061404020d060f020408010c03020d06060306030b0a0b0324070e01020105 75
    0x100d0061050011042180160340c5400d100e1240e40034101c01100501e8515090340c84840070b83e80c031141b582009000613250b4034150010074030b1b41b10242c400507109070905280d0f01100c00175541200c083d0000400d0203009a0320038078442400788109c03290600350078508011035aa12408101605060b1291210303080003103170307520701e03c000071080032048100c40407407500900c550441c034030492169180500200300341c01e005640d68029075026080718804881c0d900c405d070046200000140c914844c0211304130546402d0401000592058147e03001031200c03529017082551051100810380461442c01c2102581d642035081003030030f4004500140d205103001d8000007a02c5107400542c0190f0034041c05070400c0d0346c10350051a0a2100307990410582d40c0761041201a181144070207800f400f45500400c002d440260b01c25865000004c04a0f810f0800784040f081c800381c01c00e01500507801c0e0382010803c050380c011004800e07080c0244000c0200385080e0b2028004000410031081c00c082d5816540300381c083d518 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 718249217 1250 718247967 718247987
    0x90f08060c190507021f03150602071707050d0c14030a0b06090a061a0c010623010f03090b010b18010c08031b0f07060209130207080702061c0504030e042910 69
    0x1034071006400b9007603003200f5035511800c4141b00000340b4200c0d04010a84030900140107030b5003542d000c1c00383ca070f05d0100b1b40e40c100000c018000406003d00f203030006065a880000941e094441e841c4010b50b85e1600244001601c1c0e8501174a000740c10050310703003000174104401e0342d0780214200c5240402e0b45519503d6801003699802040760001b000c80c20070140301d004005003001c2041d442c001c3c401d10341c03140c1140714022035050203103810028480b03038060700b50302400f08140c0c03d980500d400280b0101a03213400b0b800303600a0b0f1250f82074900000b00180c01030302185c018448a042801e01c504010741c640d03105403c2d031000401d0798064038451070320750340710010100450340b410750954001d076107424503800c08900a600001440b4031075502c0038648419200d00d030003610b20058010326403d00b800c01d5a024018140c2c4060546050f0321514420308074035003290b2081c2030045002c1d03601c0200b80841c0b001488201d90861401408a05ca001c0010200c41003460590392044015104840180c0d10000e00340d4110900c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 718250467 1250 718249217 718249219
    0x50c1e0928050d021c1e0f0303060e190f0209030a0c0e0601020d080a0507050403050a0b04030e0a050616110d03030c0e0603040317060f03030a090f08060c19050702 72
    0x1068241d16440040016420301a141c07081c0d03400c0606503910704001182e800310000a400c4003500700080d051300d0881c21401c082a00482c00b007511074644d0080c0021800408008a48080c1c5184a180505074540b01d541e020300409210380303085081c0b100500c2550304040c00074145060300c0340c800100304012901580c11085025003241c0c4800414503050056500320300410050720f20010014210398070004020302c0021854032901025101c607204c08001d004002c1c102400d100d001c02001000401c20051449014014640e0100c0790504c0e01c0c1c01042102080701c2d05214442d00c4030180019034074802117901054207120031220b4010249002c000c07079981549426440203041100c18141900760700407844c6104942d5414080101c15020810760f40815100a0000f5a0b800440c001035044d0920075900400010704210f40941c50034000703469548100418400910340004c20048000020485000340090102a08003803903d0003442d1864010f02c4103031f50308044000d080a1a8900442c201c820042e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 718251717 1250 718250467 718250479
    0x1b0f101404030c0815060d0f051f090605150f091009050c070302100507080105091302030d1d04060509071b0b01230f01080714120a05011701050c1e09 66
    0x260780c1c10100d881c0101407242c82d6480c043c094801e403401380c2c541010707840341400400300c00e40710540c1e84942d02312a1b16160708076100e105100721044c1c1040c030030b400c200c0d0b6881c80e0300c008500340c12146030000c280c1703030b0160040e400c6000c5410820701583e180e4000000010090302d0810b03a641e28481d0341080d88900354040d1301c0844c44e100510016400030720040c01c280e400307038003201d9141501c000080d00b100d00803900304002800103c01070100b4a45801416080500d031208014071191940009040101e00c0e44c0b0000440d4141c0c1d810040f920303a08441daa00300c1030440703040240a2030300000c07810b681030007016602000340b03150444203911a000c00381c2c101142c01510034012582c5962803060b110040c80e40814003240c0d01810f88400349840a0101001030061355203960a480d203082c142e6048224a030b40e0101040117201684405248880e4540305007162a40891719526003c400d801601d000d00000505905200411100124500480c2d171655128409860224900a40209680a10020607a10038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 718252967 1250 718251717 718251719
    0x12d0f030b060c07031703060a03020409050307051006060f0c15020c0a0611030621070536180f1203061201020304050705011206050904080c0114070c051b0f101404 72
    0x3840044c44070b041d28400c51b07209122040020005219000c00c4410340d1344001c14000505c01400d02d50044050a8464012207040c41c0d032565030309050403101420128402d5640303004001c8182c2c0002c007507128803054200040d0444540d212107401c02031094000802d150001400041000104844d10003a03401c5282000807541c1c005006401e07910964040388100f011140250321080140b88510540d151000141400303071a2009202503152002c0703202d40c81122800600740e81c14584071900b04941c0c50500100d0941c80c1c0412680c1000c241d11880d00c4055200c1e1f054000c0e02000050142c4200c0503100c0000d49035504d480001c1e8008401c50785510760ba50010051204110000501c1e1003641c0c1c0988070425503a040001400896510b4402c1540c09810348012034080360b0040b0040c1030302e501100010855010406c00303140822800e540c5280040d02041100c4240002881038032440300e04400320158003803400e00000c14a4a1341c1c0180c1e440f600034903000720705207402800e061800c50316009206403a2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 718254217 1250 718252967 718252987
    0xd051203010305010c030209030c120304090e0c090a232802090906010302090a0308090d1a04140a030e1c05120403030909090f15230402012d0f030b06 66
    0x550400c2c071086610f5030034450301058640c081d000b550380402e0060010003280850b082000180c940b450080e00c083d010400c0702290010b03044c00f0705203117084c41c00014101010400144410b050004042c1402186000c0340c0d00346051000c14208000851001c13080740799190101046911048200c0c0e003144101e02c88650307044210341d90040d242401d0b08640c0c08019640c1d4000540903031090303000c0c10f54800303842282400003c01040103402c0c80d00024241f1000313071189a42e6900c9580600d00c21703405d00c0f41c1c50b40c10801003100c0f0003a107415186810b0080d122031003840d900580280c14610714a0b00c20019003400701c0340c1e0502c2c489910191071704481119400c140c1d058000d81300f0b60041c00213400244c80e454001c82d00d0512400317074000465003c0c13281000c514154541002c0302d075504201d2014039882e0000340a082c1080b042405c011451000c13441c040d810144005043e032040b004003e541c03866001e034881885880c524100021082504110300384203200d810407001459189140340d80030a01180c2030800c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 718255467 1250 718254217 718254253
    0x312090b01030614040b011a040306091b0f030c0308070318140a080102310801060b30010e090a0b010806040308090f060412050d0f0f180803060f0d05 66
    0x40701d0040c0f81c204500b800ca814030f001e00e0002100c014100244480040046035043c00281c03c0100c031050072582401d4495503010180c0d11103500a03641d10032070a207001407210482c0342e0704005082d10260742e281c0782d1840d9034185d44030b242c0d403002802c08480803852030207140c02130040000640800000102c01038a8000100c81d203105000c08500501000c0703404241e0f40414400c0310301c9030000141e030a0781d042d08045100e43c02000b0b8400c1c0c80c052903d08600241105c000d010300005072460341071a039141c005070120415808421441c100c3c500b00241c4800c41165800041c40341522030080c0740c8441c0d5660300304000e14003500c652004003171100c2c07280005504000820418003c1e4441d43e035a480300c0d12840d541640d54191381c00004c13126001300021900154404080c65900c103181d0828a0a02000001d00e030200d444041d056000c054550164041d0346000b840b5072815030b8564124140c075030441303481b0b50196010007011075000d1b00241c40030f440c0ea07946014404c1e00d510b92180840e02c0c014181460450 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 718256717 1250 718255467 718255469
    0xe01121a040f11010509212a1005091203031b04063e0c03150403140a0c0606090b030c0111070b090a0918050601080a0308070f170709050f040c080c070312090b01 71
    0xc058055015900c04040701e620390104038245442307023150550007000421521040643c0c01e5800e100f0100090909500d8489000154141903c013940d2249800007620081131500c0c6e9079039880745c104020501a030f039004018242101710b145034080d0381000c0031541c13007400306030140310140b00810740e031511100c144001303003105d540d00702501a900143d1014490f0b40c16100180c80040125041c2540e40703010391200c00140180d080503203481a504400354554400301c80c41a0415100d00c0d807501000d400c04d013005c102550b5016400e10706a6000207064407007540f120301c2c030b0280f24169400000c06580c6942c403810444050101e40508000003a4825501d400714080080210382d03901a0900008105c4008a90007002c2501030319200e820f0766030300a0848030280c00d0b00c488000d1045110404540b4141e015100c0d12500c01c03a1200741e01b40307050a08014584410403085c61242e8201007003485596031009a543c0c01c12102110310362542e140b0b10701030300c46030a900c2c083d859040c070307280282e414014401030040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 718257967 1250 718256717 718256779
    0x21602040204090b0a1205031c0902040524031c3b09010909021804080d0527060630030a0e0906030307030c020909070e01121a040f11010509 62
    0x9001d02d039450001b00000d4441c2c00380503000d034000b44040965090402410901c00d04040000103483d6076a078002030480c0c034140d40e802c040703400341164103041a00b041c021124219003180142501610500030701c0d4080003080882c0100b00d0240d40403020300f0b0a40568a00300b8021051042a0264041c0550511442040003d115030000800084d00c5410f80c4a1001c890b50040c050b1702950140c5030903040041e601074000c4074480c4007004440e005400c0c4d4841d003801150003407913801c540c41c0c0d030a0010041c50001c08094806401410503c4510340c2c0d40d8074041c414400715140040c01070b041341250620380141c14030750a40c5000c000340320b181140d8402800d00c41f4110844800d161398544100345981c1e40150752009012a036040080c0700545000c103400395200304c4003811900c0d1151600284900203100780c1c81007007850200d54000040007220f09401c2c0400e641c00c1081411860203850f40e01121010320005404030702892202691a4482c500721181c4480c050061481d0b20001401604400c210516403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 718259217 1250 718257967 718257979
    0x6040305250f03051011070510060810020901090314070b0a26130318050303070b042006340318060503060f040213210303140c0d021602040204090b 65
    0x4909802e00001041c2a260880010308030441c814400b8002064145c05910240704203000e08000120100700d0b8070800403041d036021030b1032031a080383c0700d20f800c006c92034070801c6500601030500e151341d00c03950350380031250402d4428080b8a41b000b6140e05005180e000314561071400507004400d0350b009042d815590b502040901c0310710810000c010800a803d03208520038000b09503085c004607101d03100c12800c95400d0141e0705105955000002e14540c40008202e8040f240c0004000600c0164240c002c5030100ca1958000c0c000c0b002d50004a880c0701d504400000c0000d968070781c0c43c001d2152000c0d00032001c9002c101201c150014100a4141c01e03442002500000300c504012030b01d5445541564052078010340101c8140500008100280d004016090380081d105440050f004511880c4089002d600183c040800d04c2582401415036400160424600c0c503c9803c0c8407598104800b204c0c40002101401a21040040500031f0854445403010754417600200d030100f9508015407000540080c01c03a45 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 718260467 1250 718259217 718259219
    0x91e0f150316060c14061504050f0907031416060e1e0a0b0d0b0a030308011508040305090609030a0203061017070b0409151802030402040506040207050607030b0604030525 75
    0x3050760b240030410204107484003001040000c64000c0041541032449500194008200c0c01505490800121040c10b0355620b810103c0d1950705082c4242600108140c407040300c036107050104260f9440c800e03c8000c2c15040e20110001104c2018850326003e0402140e031101d2050380c0d003100800005604051900c5506803412007040c12001000400d40c1c0380740642052038503403614880a41c0380d0081c04010076015119002d5120755581c00c003a00303014500c6600d41c404294180b0021a510b044442c00700ca052141c0e0700e05110104c3e41000c04e480001e02e04540f001e03510742221010a0808d110300c0e01c002e405200b490180548204240c5074101034603182c0729991403512924000b2540c8510034804c010124808020600840040383c0016144445286042d140c05590f00b070020001e0700600c9039900940da000c0300784800c40c174081c000c0c10f801241c121801d50a10696440c0d0989800010386100f09042d61141c1c00c00540e02c0c0c0340705603001190841c080e41d0011100a500441e011840c280554164202d298 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 718261717 1250 718260467 718260469
    0x30c0c070305060f0726091213061e0210180501020a0f1112070209041109040f02150322031b080d1401080d1d1e010306051e091e0f15 59
    0x20006d0304094440340c9000f0704c2141c08110200708071010f0038502d400e020b41644140d154420200820720b00716007101e405102480d08000402107030704448040e1103024483c086600460380021100300c00140068002042d0300043c40b012208d900383d1500a180394004145d460f0003941080c0131004410f8262681540101d088413540e803075a40041c900205024280102c501604018916640c043d200341040d0158038500d10020b458480e08540460b80c0402d5040018118180003840a1501c140f001c00c450450800c92400312040c20b01e000d0b405d1310000d1032008541030510802d001c01c210b07070211030280c0b0300310a01e0a0892881d485443c22400460070300c2c1001d610701c0300400c0a84e040341c0303114001e428100440a4101d0300000c070a8981841c4841d1030480400541e542494603604404048418104842e12000942514656031205124031010312519411842401d0b1031101d50b0743c100e5072848156500c100b100301c03d1401c40c2594080446003000c00c40030340148600c060041e000342d08001d07903d1042e10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 718262967 1250 718261717 718261727
    0x30f0b070e1c110a0815011d0c0a030903020c06130302091302030307150b03122503020304060507030917060910020a0516020f12010c030e03070b0c030c0c070305060f07 74
    0x4071044010703504500302c1c802003003440300c00d402c84410080c049420540c1d10f5420518204403581414941c210000041011011407503403206e500e508281c50061510b86106600098050b07940b03090300303041e22485000100340c402c0c41018880ca1b0300070702d03003a02c8404d00b8200d01104140741c00224002c40c694404200700c90410445195100e600900441c600700a0f5540c044d074a2460780c410200c050b45451030168695014402c2d181d0320b0318545002500c810041e0550042140e011403103901c0c1c20440000b807000f0135800300482d0700b5540ca606000780d5807910307841c044803016013584c80785818280c4110f0452400102080d481e005183c0c0808882d1512000c0c3c0d4000e0032880381d4110040450740400c400d58110130101c88030030710580000c12144c1c0a280c400041080710481c0501c01d48540d544c4c00c503510034190117201d0141d40d80040d00042d810040c1e41c2d5210a807510303010385000312859001c400902c8405580b002c45403094040019242c0ca40c0da0381c5000340d69040309590b51000c0e00c2003c400146038070322407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 718264217 1250 718262967 718262989
    0x1020c0d060b0604030f030c0209220321020c011505090f01120821040c0b1309150b0a0e03101e0b01020f07080a02030c040c120e0106030f0b070e 64
    0x40c0210510501580c0d108000e00c146000c480e0019424880040402c050b80d912007021402500d40e000c00d00010701c108008140024a8440310303100102800880311002e94104414a0741800d0810580306180f0118020450540c082180d840c000034400803c0c0360103400c260581d1130782c40542c0c01d40e0390302c2d1410020000c0c0203d0307031810102035000040012060f5034070b182290500406041d40b41c90846503a61001a00f611a01044a41d1a100340005c20000003500700082c225602010b00b0030310804801011550984260301d401c54490b120f03502c1a14241c6c2811000f40030231040ca60782c8040c80480034242228041d001c91280c05840c584044103100340c01494048008203c5404a00e003040039400700800b04500f00c4c0381107104601d025000c20ac81000320308081c3c0034841c010700000d1030030701c10140340500d4490030740d00039410080c5405a0075000550509109018040031441154400c2228010040780c0d1000d48000c0b140d41503c002d00400062860045d2411350303500888520190074009440c0b44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 718265467 1250 718264217 718264219
    0x10203030703020d14070e0f010206010501120b0315010e011401020c1c110a09020705010515030d0c0809090c0c06100b18060d02030a021b1501031101181e0501020c 72
    0x410000514071900c29030080c4013003220654000b130010000300f1254141101221102c0c0400c905506000035032500d4283d0681c100000d1000308443e41c14800020900c1c1c00410700040601e03100d1440c203100380e5051044441040d0789018043d2150303510040200340c08828441c0c00c1d0ba403428804620305551011603014000c0c14080c111448401d00c40c0d026018104150703900f56091340ca800c0c10140c941e80d50400540092040d00c801589a806c1410403a0840360040c221014105488062030215200400c200344111202c0c101880d01210b24145042503210301c54a070b40d800715900302002001070000002d8203100c4d91002c00c55a1550b100f500f003503401c858130301540c80d850000340009000051121074447d0945400f030481e038140748402c3d1220b010781e00141c0d8002100d54001c18510503403412031048a1400014100034040304200d4007103004021410700001d041c20a030103001c4660b03a4010004d41041c2000c542d4020410f0340c0d5a0403007071151000c00035078406103608000008082d031001035076446d0588 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 718266717 1250 718265467 718265473
    0xb070e1e10111509010b122a12011415010c0c0312030603080408070e0c041d06121507020d0c050c190302030f101b050706090615080321060102 63
    0x102010203903018000d4890b41070652142440742440f0f540c4a104250164001400201c2da0360488420022000c03132000b414035070b0307600842c2c0030300030f5100005038032200c2d0300c086e03da2240714680903010900004018006071302d258246081c0c40030300c0c424114910302c2031000300076506141c490030004403402041c440b006070540c1c080c00014404240d01d41a00289010380e0309000406a6480d9185c1299800c00e81c01005142c2250600304080c12018001076804400030040d280b0307003400c0c40d00036100c00982000d1f11003c9000c2030000b41468540000008820320003000702c500c652003910410f0100c41007101c1000c01401045215003010b40a9412514901e500c48041c1c00440300303031424080108900c0044040390002c54070000007586003404040001ca0118026001c0350340d4618110707041d141c00084522418040030f08101c1c43d02d9000301590803080c1d200d41e01260705013040c00c14102401c4004908928525001d400051800780000200301d05480c102c021035418a00103414604000c04450682c0960 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 718267967 1250 718266717 718266739
    0x11811040608071107180f1b020d0e010c0209041103010b0303090a06180905100e010b040e07050313080c03040e060603281b0f1b03020d05070f0b070e1e 67
    0x180c0180318125213240c5440451314004c2e501c030419241a82a00090180c6c6c50b5510600070180c10b090065a81007c2e0408200036104105000299030b03042e10b80c0580c0c1000020074030034206030b00c107042c0c1e03c1c1c1d00754004001100760308080c200011078080021550b8425071a01000c041c9605010040e40c1000300010a00d00d406494036409a480c10040c0701c101c05000415100400c004a0038404c00c2d01400b4223041c4440070904000c0300049104041c0c110310380240c028407040180307071a20002c0d90381c000207602d0308540302d40703e6881c02140f04035001d03001003240001080e01c0a5406000014004a031100301c4802e1541c0c40e984140101e901c41590b1100422100c200144d24080aa410082400492001c0080d019015000c1400d812881c3c2142d00d00156019110b4003400e0313804003201000c0c42c6400740b400070301045540c019555060082c0c0c2c45003840000704220f014007408030200039046401c85050300c02403401c05401010307018002c0405103c4c0d845006443c40390b000300c903131303100cad182000bd40ba0200b20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 718269217 1250 718267967 718267981
    0x11a010912021f081b0426011b05340f15020c07170f101109060f0406090b0a09060c0f02041401050301050c0c07140a050306011811040608 61
    0x1000a2000a98003c210f1484981c07121440f0b481d9059020301c0e070344c0c801d120342c102400c0c0000e81001d2038411001c02d0105210520030b805c400b55400010740c8819801d40c0360403042c2e40ca014003404001c840790f0591440d00b0300c0c5140c5d064100d0010541a1000e0036403100d134131100c406602406000c0c0004d0505a1011031420000032022030821030800d0203920085150410b4070b000c40d043e40e11908410b07403590800c44042080041c14001c09110400d0300001d40318090304000c49640c0c3c1c00000e01c56100d19903d07040c0c5082c0c400c54007006c071040444081c148503902c4503d0025086558420300c01d0000198058800003804014541600c10b140d12039940c8440785881d18508403681c0034140c0003541c0c2d0744d15810108006035204d2103030800303080b89000325024942c58238003050300310b0b00000d1490103240803c01c480c180030b0b14085070b00410380715100c0011031180c14582c08a100900350f600850740600c50b903000443d02c040500c40e00252801d50460601c540015002c070f1034524002c2e0700c20340000c0794440e8049015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 718270467 1250 718269217 718269239
    0x1503060b010e090c0405010e011b0303090c050a06020616050406050406180e0103060c020c03010c0e13090506090307200d030806030c1315140918210a02011a0109 71
    0x440d401450800c03038000000d4009031100c0020344401c4881440018104502c1d60002100e210481090030800151681800c81c00c0049880c08801001c0690b2522001c0400c115501d84401501c8080c048402407503c5d804080d646003000d0b158030445502030020710082c14031941c21501550301e180d1b6000d04052400a054640c0f191403d40380f0b0340103041100100d0318035801d0403448d008500a00c40440c40020f0504040c1c280481025001d0299042000700ca4085800c502080d400b8402500c2c00d00c60810452048801070003105401002400b654003404144800000a005210b00640d01c0c2c2445050140c0d803240040152903841e80c000003442c2d004008030740690115503002c0701c05400d880070840c001d8009504031051a40c0400f866541e0b41034014102106420000035110709800b4a40708655100001d00042c0000c0ca003201106110002d520b031404140002101405c07141c0110780c00580c0340008070501d801450350800158a0b1403100d40b4241a44e0700c64084007141a100c07004000c1c01c3c01c0d0b144203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 718271717 1250 718270467 718270481
    0xb25020334081612050d0b04140112060b03031219090b06040906090f03050d06050d200a091506080c03070806040b0105070507030b0603160605031f050d0f0501050604150306 76
    0x100f000420b040c1c0700d001c1407905500303003030002c4076070703103140e45c502101e0309140880380031042450107503103404894403002513400410742c15205000d6039402c04074110310f4648003a05c040d11429401d80404140d0107210843d460340103015240002e0424003094440100d1000c9482d600009040c400414010078040d04041d0f002c0010203009600c003242c40d61190722400b45d0a07806c0d0004a0018500141c8214050360920403100a08011140030f00c50a07002d0310f5a915201031540045a0b81d0164601c05e80e469545a0303e440091400d5101405140e080b2001d1594000c1d1a00c51100401c0d20b04000621209009003140d11038131054031002041c1e102d9606000013404440c040c00c1c1401400c2042c4400310703031300b0040300300114815444440a03203802d405050410f241c01100601c2030406480170300c0415041401c0da070380810101003074030440c0690003035590344070425480309420801062a0509115844404510841c01540203120340d448942c10311086514107540b000e1b40d468146030510008d203064000c28 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 718272967 1250 718271717 718271737
    0x303041e1403190810050d0b07030e0613060b041b0f050409021b011512080c03270a05090115030f020d06121b0f030b2502033408 57
    0x784003101803548280c5154044101c2034002d580019402000a40c400103899014400d5070542000310301d07250128001e0346c2c0801c0020256410540001d440520a91111101e40000002c0319800d04003154111410360845005942e61407d1060080c414103190007072203450001e624105020482e03141c402c46040700440f44220030081c0030403000800d040540090040c6074a209203540307403020f6501065003100d030400b503420041542c001013044007070659070f07a0581043d000003140d50b84503000b442c460304601c607441580390350718440c0d0498039000328038504c541514001554080502600c480c01c20103052400d10078513800441d500c8201e038102e80700e03400940b80480401c0e0b0242c1040c0e0700001c80302c10390720160040000c04407241e0109003400003000541d030f80300ca51603060300f031140d09021440f02d02286600003d03200c15950408034003501410384400100110038000e5414005081400030340742d62200800a035040503407080001007030380c01c01401c05030450b0091806000c1070541e807501c51b2a00042c2210b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 718274217 1250 718272967 718272983
    0x1b0a030908062d13020a0f08060901050115050310031a180a081c020409050708090706050f0702100c15061e0506090d1703100f090b100305130204020c0c010807020303041e 75
    0x84c0141c880b00f00100c01340c10001006520355007072401e91450308030001c1800d40c07141c2c140780c010040c011030200000c07642803007071a019039240d4907500340346048100390b03000410410910f850b04005441034280d0074040c44a0f01d0011035000d000c12200c55503001c04010281415108010124403a04003a0b0303405c200100c0641d0250406584400d000100c0b4012524000400c64600801c1080700050026001a0101d418403d05251000c1070810842c010050024010414404013542072801403c129994560240e1405058110040100090700c218400d40c03940e40882c44003030350440c0704005480107540c1c001d800305082584140411010705c020b00c0b811740d203055604454101d40c030074450082d813051012940840c64140b0780241c0d41c500040070703805039294074905044a56150348080c06859410382e00e1401007016200e14118402c20b1221080c020b6129100241038400810301180013554074800341c8916503e0f40d01c400080e44c403071004513030042601c00c03a1043340d45c1c03c600c2c1005400842d402800d41c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 718275467 1250 718274217 718274251
    0x14041b032013081509060403050901030e0303090f0706021f020711060c06090d030c0e120f0d032f120403021c0210050c04050102070303051b0a030908062d 68
    0x18110740d001c40088200104100700c1440030303060404c404000300c5100600c0c07802d00e25001103115100e00007d0402400c2060010300844e140e071294000700081004c0324281c954904111084951f141a8140e9000c924007c000000964500101d524454143c000f902100c0349500900a54004d52000d4001c81e101c21501c00465031946549000d4400000880001c0410341841582c03503182c140c0c07035481441010b04001118090940c060294a0f807500261214020307080c4a400c40381c00e040c41c501000a540c4501c0d100c01c021282d054000ca8050404460840550030209954a10b0460340c041270310107940080000c15055014207400d540d1140c024030548505101c82e00200701c144c004500316400690003280c0340070703140c10540326442d0440104580145010b1509001070340f2081e143c0700150a111002c00e02a120900703014029100c40211000d036a0070458900c0c01034480d5601d0b00a102d013502c11040040c82d140b00b4014080146220800400d40d1040804440002400300400c0075207002002c010f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 718276717 1250 718275467 718275521
    0xc0c030d02070807060c0807030513020d320a020111120712140a0e030c010e010f030e01090b092104061b0201030b0901030b1b03101205150702060114041b03 69
    0x11803006d10311800da607443c54900b01030030024140c50001d81000c26080381c0e003c5417801640ea80b20400302895001e0440071441002140c441804901d090000091840b410044590ba90010a018024620036200e1741760540780440042e9841141e440c907441c05030000c00c0701501007100081160381411403450412602d40b102d00190030244c00c4002142e000c201290101ba038285001e001000c440c00c003e18204e011240c80e48002091900949000420300d66a00ba4402c850300003900991031441e000394444c207aa0402d86100355990b558498407240d524071270110902c601402d00c044400300c034003581c9c8511458005801441810655000482c1896035804802c4900d8841e00c2c401070086005014050640c0780003020102c1c0c001130448040d1485808004010154540c000400141d40c40340408400c0b00c4414a0582e00c1d000c8200151819006650100709056a0000f001410b8510241e540c400325440081400180d070049030220b05128803420403080514840d0b480580c4268008aa410207942065 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 718277967 1250 718276717 718276721
    0x1507050307060e01330b09061b03191809020325090302030d050909010b0c03070b04080408011a130e10020c0102030f01141014070c060c0203060c0c030d0207080706 72
    0xca03d41c03000740d44070910b071005004800113403420001c0050310200b692001144014a101c001d0251105205001c52070f485e2544403c810740382c420b4225809008422000400a956500486880300500794840380b04000c01c3d20031061140c4c042070403040700d01340a0802c581c2d40061341000b0100c1c816003415100c0f0b41d4503c05150942501104a6250000501d095005150501d202040703244103024042014044072744401c00d4540c11075403d02d00c440d403950001c451a03802d44c4034985003c2c0140d96204103000500c2030210003001200c40c0c2d03c000300000120030320b01e5104030000e03041c5179900c520014a040d00d14004c0350460b43c91024100142e03031441c0c190000c040205c3e0000c0380c00c8042071394040100310400c40780c002c0301e41c09082080741d07403002c40c01c440b0005201240c1c80d0750070f0010001c40742c01d60100d041182c01940e929561094441c4101600d82d800104048529103069100c0e00c1484085095441c2c001c04840b0150baa402c0654036090304500d00d2406503000ca40c040300c461008110540102c2d00c18 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 718279217 1250 718277967 718277981
    0xf030a0f14011e0e070e04090f05150a05070318031206030209010618080102040803190e0d110306132001020f070609180c0210050c09031f1802150705030706 69
    0x20300356855010402d03d0620704400740582091107030210303400c02e02c2203454010004000d600404c44010030021480d20b400f900c0841983d20042c85031241005100541d4a16442a80301311065a800c0041da954280c045040d9851140d0401542245074070365400f003841200c40303030404070001e00b004c1141e82d581d0780400c44030350007684540001000800f000c910f0010011100703000b484130700005d41c201070500712965100d20401c10080c0103540c03904070780c090190084d000408442c1c0d005003502800c96086c2800300c9181d000b008410320901840000841d0724480c81540110550842840c410604002800140c1c038036501009030b0541c4202010342c0c40d0400208818005010141e48605025103410711043c1045c3c4d01006d10444c40741042c00740a0199070000703001444400050001c905074585c584c5100b094800c0c00d40b681c0d018051120388400d581601d41c802d081110700213108005291040b804404c8000780c120000394812012030b1040050400a0090301c080780c080c5043e80d01c0c0003040d603140000c07a006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 718280467 1250 718279217 718279229
    0x1b050a0c14030c0d050705012003040807051c2411031602010c02030720040b1002070816031106030c1603020705100302030708060d11060708030406060b0f030a0f1401 73
    0x709100400350305040c41080750304102980d180401107141d54400e51200240e0060318104021641c2d049205c214810f28608000d00c82c1e0309403595103864000030380d22800326005003806000c1c1c1d9105810b091030072001051032645c012481c200396030304ca0300303104144c02c0d914442400c1c407588a20240c000700c003a800c01107000e004a14803240d0720204a050180c20749601107200740554105000b24404280d003041d03035400b02240c09984010b043e10440004009018140006030004034001240c0c7e01a0b4002600c181611b00d241c0456010020542c02181540b20500000b04040d0002401038401c0c140040919002403160b900507003407829000c0c0444400401203015030050340b10400c20403080c10481160703403200e417491405504c0e41c40c0a00001d00012005030003a030081030b003000a0810300036009024140c1000c0284140e60391811801c195850f5003041d0f800b80d0f481450040c0020310501c0c3c50044864100e8041c6241d07055584051100c002082a104005541c0f61141050001d920300c502a03d03001e008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 718281717 1250 718280467 718280489
    0x5030d11031918050306010e0a050703150305160b0f09091005040905070e330d060509010b09090106060e15071704061b171606020a2007061b050a0c 65
    0x3070b103c1a2910700c0f8550155002c3e80200005200d2010f510140c01d40c01843d000c800728041d202c0070b400728024540108160084601150044204000810307400b440a0100c038050265685500d5a42aa84142450522800c80410910b62542001d10000b40d020ba220b8001c01e40c0365507500081000d07201e06000c11900c0d07070881d8800780301d2a00e451f03102e1900700d050f008621400040c0c1070940107081c46965014080c4417003181c0c941c0b10a55490211050841c3d000c039091015060610310030780a0243c100d28284138407070110002d01c240074144208011603d0580d52280c3c40f00519081c070282c81070303940f144040b04008200c103c0c041008070340e903120000c2c0f000540ca6501c40c54482c0c014082456403c0064148103039074a0034012035030028800b4201c42d084046141d6030002a013108900350030f1001c1c000c01f100d00100b0701280d8150400300041e40300d81980c0000580e0445030b0700041e21042035005000114072a40c01d0410000c00380070019aa05104004403620741c540f81c1c0f207000304100b0300d510500c000c007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 718282967 1250 718281717 718281737
    0x1020f0406091d0c0702042d0c0806060712050c010c020c18130204110c16050a05060f030a0507030209060d09150b180406181b0f05030d110319 63
    0x56100075039000800154480c510042e192816080320440f0141001c0007480e400706100c1e0956959078881c129001c102c90307440104290010b20034080030700328003910001c10b03c1d2100d0344222601504940b441144001c1009107403078490742d903003c1104000b21180341040014403854140c03420034452070b4030401701500205242da2040003040302c82011003c4d0000682d0111091000c03000c0080000c4890316811100410060102c603034818240c050041c9856080c840c6a030048038608416408034140d40081c0c480c2c240c00398443c0e0a10440c1e100311482040034070030404c001030481040f54409034015442d03240261070b06101800049042c3c00c03582200710390350b5444942008201070102c3c00e13035010f2002041030000c0e01da490009400405480d10065480d280e0400150400a40d40d01081c403441d1807400303c5000104500300b00c8000400c403000100d064440e064042044080000d045049441c010003d007030925040c0821500742c0004490341e60180300a0244100c241a0b0780000007542c00c1a41e1a2040a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 718284217 1250 718282967 718282979
    0x906080d0309050c09090c131a0d050d2a050d0306060e010912020f040e0f0111090f13141807050f0102030a110a05030301240f08180304050301020f04 66
    0x4000040394805041c505800140003a0340410b2080d580e01c41214444007a95a11010f40d0900000d0101243c0c01082614001d52012040c2d004c4d024080c4000d070b00009a0340d024040c03107210300e00c0c03000140c519480040c0c0800107510031808010700c420140b100094001d40e20807000707190600041d01319555000b42e1018002c2561510454001300b1076842c15491404662002030b02d044010300400d4047d4408404900a40d22140465807102d10090f00400c04101002d520f40d480b803100d01d0074056554200703030030307501d05501c0c10f010f03202408001021811402101410000002d080200d408202529064140124500455503a02c146030508100112491808c1c502e4241200e5070001d030300c42c03001c0d4100c508440e640003098500d2014942040541c007414940040e24000c03d17640001c0440c880080082101200483d91045c07184200074442c03651800181f040d01d82c445406d0500001a03d00d01c0003c079000c109541a1107401f0102050341e25060300c1d040420f007aa4402075103d80c8402d0000703410042c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 718285467 1250 718284217 718284223
    0x2010b0d0c1d01030210050f0c0a030e01080708090715020a2013090c05090c07080d0b0405240910091406031e060a090204022104060609060e16110601090608 69
    0x140a04081e40c2c00e16640c11540001c3c21841005004000c028020030b29202031040c150885e420703040008103d4402c8146031030b000f005d0f0800001018000350b01d80300850421400f601d03915000e541c1c140050004a401c11280904026014200c0d404502c100701005021420124105000301083c1c8503c080c0301c006001800b10381c0ba8000101c0200074548900400402c01822400c016194111000305203516840c03100c2e02140601e07103014006c00e00000d92403490800c02d500040d0001415034060240b235031804d03001070b01d121491070900e81c480c1690229170040d103854540e0642c00025001034070703265a01c4440070340c100c4136014071a541c9146524280400d42c681049181c0002d2540c0703410301402c40142c40c3e03054483c4406414240003948403075000046696903015900c1031410301c0a03081c1004201c0803070000303004040e1303030035a80d003071810380041440d51080c081c075400c0d2a90750b40301c40c1441e00c0340c54034101c0740754514508008002c45449482103144090010718020000701c103001c203031031303003041e03c00c9003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 718286717 1250 718285467 718285499
    0x70501051e1902010c02240c040302030709140105060f070f0312020a08180a022809020d0203070f0201051b0c01090807080a0f1e03020309010b030f01140a1503020d0302010b0d0c 78
    0x540d4880c0c10400c880c1e0084070b24247d14809800a00082030302c4860b483d6103107000e40d0304000d5041c0204c0038013098202480d80071300300a031444c56440d400c90343c0e21018000b4610910030304401703407041003080c5808203d850030a8110740d031180c60140421b100c400c0114080780c2100e80140f00080394403090045403201c0c031490500103000340002e016000190760000d0b4803181c1d4081d040908600c7c1c2140d071707018140c100a2110051610030344c20740d0740b103258040100084d0300444510b0302080448080c00d1a00e44148940c074407440d140846043d194800801100c1c5c1070f04200000c103219920342c0c140f0400981420042c02c1800e20640d500c546600b0012800380848005403000e000f04614055407410310442c28028400c4008c2d542030040c2e032612101c558601408084185c01e400d445480c421819401d015408103201c003103905406040da882e4610900103854094082011502103c2d00030b001616003400b5843e1020320900000841190034404100300d4507229005a0b503500c0c40b50010012403d21501c3d1103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 718287967 1250 718286717 718286741
    0xe070f0807260303041401020d060f0626180309120303011a1315020a050105070906090e160e0d0b0c0702040501080303190203100305070803210108070501051e190201 73
    0x2c91001a84195035074040240702602102075130f104400c4504081d03044a803031508942d414031a0680340d045440d4030365080d2103034000041c4105031a0a805804140313149071055001c007103202d992136404018624140e100c030f00300c405001c208045402e41d038648038800030140444000e9522580b400002094525100001c400080c40030000e4090107a500b9241c4020b4a200c041c910030465020304080345040e2880b00010103030340c6448140026141c009500070220f40655844034805519040704210303100c0142e890b07040705441c4002165001d800f800340b40c0758100d40904020103100071a01c410401070810340c0d074411007a1002541d201582020700945002d4002c0000a61542c1081082c0c80a6080a40b602e0020f103603012011401c004400c1c2240f400664008080311003103900e980d1001c0d100e0380006135400c1c02980d900c6110516505d6500c10904883d10f04025101c4540381c88019280e070342c0143c000c41c00c00c001c0007154080c080b2072800a01026626050381070700c00b049081000c3d085030000180c803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 718289217 1250 718287967 718288019
    0x3130801060605160b0403050909070e090c131701110310031e02090703050a110a051c05063f0c09010b251406070804050d05070804090e070f0807 64
    0x8415801e02807000c5100704c0341d00c61141c103010782d079508084407035010301040340e40e002c2c5c1d0400921040a070702035801102014111504152901c03003040030100c0b441083e24405089101c0003080001070301035501c0755a54002200045000b007071280704480719038401c5036005d02c040301c0d8110910034403e000c148404403400401c0b82c02004003160b000181003810041419007015110400180c04406507080980005a82403225840b442c981c003002d0280d41207407060b010f04109403411229411002d0103018000c60003c0c180c4a100c00e41003800d0b201c506600d01034060484c000d0001e1554841035201c0104103240080c02808003603c0800030003405504c1a80044000b01d0b0600002c81d40c90032110081541d409403a1413894040c809117410780a081042910710050300841040200300d80d00600e405101c0d07131040341a42c803400c00500c01903e050142c0b0601400f10107080c4000d001280842d4487c0200f191001d00322403110355900b80e00154003609030401e52076900880010090144100e255000110031440d107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 718290467 1250 718289217 718289227
    0xf0b07200706090b0a020f1207150b0105120709050306010e0604050f1506090f0310051f0b0a0e03010b030a12030609051e06190b04030c090b090a11040803130801060605 74
    0xb00a00500c07181c000c036030600c5800580070480034003c11800c2c0b4010251030a81703007890420b48503121140c20800040d10204451002801020961700c901111504142c42d0b060411005459400841000030000401d00c803030b101c00440d440d542041101c3c02800b00000d00400c910300358091106039034002e40340d041300c0f07011801480900175004401400034030b8280c8066454159640001c4c540b07101c51080f140d0140103e00600801c0b46490b041136100386071503a041110210389142d025080340b40e074400c1c8034107980240100c2000380d10800d92440001e170010004a254058440060f04141024008445000d02e520650034130307a42600440004003d810010449458416a04403d5500c54a4000c411628681c0003640e10703174607043c120720b0107804922800c22468840b100c002d096030141c00706842e12031504a0016046145000b03c41607010042d00e0013045440702180744001d130088035007040c1d603d0024000886c9410080025103484120300c44d074020214600100c0d58211000c9070004801c122003000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 718291717 1250 718290467 718290479
    0x16020c03120c0a080f0406030608070803030a1815090203070501031401030f08040e090c03061003080d05072006100e1b03060316030803041119030f0f0b072007 70
    0x841076040007280000c5a51889007031041030404400300c00051007080045040e11000c3d14100c0500183c030410740341003212a45030503455030f440c45144103174002ca49c01040050055001350f08074003103802d0b08a0258040e81010350300c0710038000416015006041e0b8980d50300083d8501008058002d01080c01d00304011600f502e6241c900120500005c4e0500c018110403100700032400b4100c2d001407030007900c44021814605912030b20f8000603100b1901c01e04c2070740085005039128103046e0f8102c961000c60301e841e082c240d600d2007028041c010301c054244074044c0704c560b0000014851001851003000054000362810702c080e43c05070740942c0c0180c10002004000c02c0440054512400540441040901d0300daa45002c006860a41601148a9840c580304400001c110000000e0740c0603e1082c032030300448038400410b11001d240740d4440229104001c030030400100d1462840c1c00c40300c038000d800b05442100d81740c0385d400460405031614000246036000024205c04c10b0030f124030b503101018016250b1075242c4a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 718292967 1250 718291717 718291723
    0x204050105250506160201050717070e010306030b0a14100b310605030403080939180117191202030c1b03010c03060b0304110a030b010e16020c03 64
    0xa40700d602d120400a80180102000c103a181d0380c1c158000c1c100c50003407038407500d801e01a04010100001540c207041c01b1807401030049a60000c5402400b402840680d0340050456030070b0800111141856640d4401002055100c90814401e945648020544034882c42c4802d28170800200f40c80641015601d05025000c0050304550212090581100110492075a401c203280c00704d001182100c0913140c400511640c120001e107100b5030007034076101801d94500c2c01140e01c0381c014840019201c0c4030300c56290002180c111001a42d03600c07030031a16107080740d11004135414150f035a01c0c4410079000103004000c01c0d00e0125141d18032511481c05403e01e840b142c4103510b00301445880c02881101400c0da00070703000f4400c20a541d802c901100454044010b200b007210988150b22019034029402c04180c41e2a0502900a680486070418a580e18558980e220900180c01c04000654030513404c1000001103050610640c8c0030301aa0507100009051a903811006100343d080248250b400c0740c00c40504a07078000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 718294217 1250 718292967 718292977
    0x31002070206041a0c0303040615060206101a090301150e07020312060d020103020d1a010801050d020604140a08160f1208090d02040b1002071802120109200d02070204050a0204050105 80
    0x13540b0b040080b0030030220320051070190001103d0310344000300402080c040e0030303002902024014070150402d26101c02c022a144e98045900031006140e182d4100b0055840155110103800307543e015a05001074040080e007900c00094107400c2c008100f1100b13008020304d081015070040303800d00045150000301029251075445c0100b03810f2065042081c00300c250790098045541c0088016020803080080c0100c03511a0307103000b940c0c60300040c1c402c0004031310303810403460200741d071354000340254246072500480d00d200c01602000a500407904013000614040304110300c803400307881200149440c034100b0709402e0b00c0d07104540c851170852503481910000311f82e000d02200c0302010103403868161009140045005403070500b481c0e54000c0d40c1080990041c681c0407500205460072000d828180d00241c0914500381d015088203904007a4400004000c9900c0c0c65004c08501c00c40c0d182285d5500c01d007841e0302c68481d0411125000400e400081c14000c51030940b00b640d5104a80706021410541400c000070168024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 718295467 1250 718294217 718294229
    0x306270e010c090303210f02030a0b0406051503040203014212060c03090c260105040b180a0b1806161407080c0102040305070509090a120e040e01050f0603100207020604 74
    0x340c00006c5180c01e0001c44d038021188040e510038000c01001801c0840207620440d5281a100d291a80412180c9800e0040c1011507100a00c640e0071180c02d10142001c40e8000b4008917810740d17969140c03199080504402460042000c00f0807005150a044615224089044590030700101c0714002e120b401c07010000b101d5401d0300400001607685090f0015401861402c0024164518203800041c00308080b90002d1303403210b4038000303140d2440c138003010f03607400ea0350b0036940285030040180000d0201441c00c2c4441034540c032a80e045450007491602e5100c15243e0540e11120074043c10030700107020305010840c0540100030311212151603039500324024250f20b03807030504140703d030342c0003880000744491003042c4e422a030b003804021942e50303a0b02e10f403d941d00c100b148138040c010400800000c801c088040390007049140c00c114103416026548904440e030304071040c0441c1c1d0003556000409010030091040c244902803d4003c411542801010507243c0341041c540000341c940104100c0c80161101010780b01104c0d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 718296717 1250 718295467 718295477
    0x2a0a0f030b0f09010e0f010b030708150c090307170705040e0313060f020304050402120604141005092509050f03370f080307091505030f06010306270e010c090303 71
    0x2500d20764540902040074508003244906c01c0749a112902c194004640c020f821002c817001c0c1039444950035190300524180d0001c49450700001419140c105004106c413071001015628800c2d01d81c0c1c8000102c80070012100790315800481c09006500345440f4200802040000441c2005c0400d404010f184c0d58034021903041081d40022255141d0080080c0d030702030800204190745452410392407008440c812110b0b03d00c2039007404020b102c0702c8038490000d802000718400c003e4240e8200742c24410349540162035401d440360b01510900d002c81c0800d01d01c0720f07043c1d03495440c010b444d031134a82040102207403900294881c1d004580c00c8046803020404003110301304010711021071480740140401d014807201c1d5001d00908a510100000c00811600a61054500380c440300725003504c0f01c075120400d0361142d00f440d01107202000859000c4405401c41a480441450080351a82c1c407405107102c00184c400304000741145100910100040c1406000b1000031540001c0203403941c0068020110485440040c0c1441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 718297967 1250 718296717 718296721
    0x110705030712020705031504050d0908120f1c1b05090f01030e07090509060906090d0e090612010609090b360a08040b0307030c18090e2a0a0f030b0f 65
    0xb038004c0c0404801440b005041d40c21070030f00000155004c00c0c040328100ca03203004102c2c8030038025000e4001d22050310b408100034144140b030012800102e90002052190340e5030184582403400d6001d181e03070a0b284a43d1003001c43c00300100ca01c82003035610342869035030038000207214600e504e454410300940000d10910300840c0761801081c0303035814880c49400105440342030100300a81d41d64002010390085a40b40119030f03482d51030100480d1a0440300002c03e00244980030304002c0e91070030782041c5410850003052010321190318100d050031145190f02a07412a80c0301d91003442030254400c4590380c000b002581800b144000c04109091080c0043e1110507441114000980000010801e0001e007580c00070110b039442d512183e030400607400c101d40903400a406d100700c0e842e203144a87c1c0400d624003001044070384400d0030f00d41130030003030071041307035079840c0b034490700c40400f07440c3d14090400241591304070a00990b4408800a001c03000140350000ca0245509600420018030800302d40c2e680185145203020903a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 718299217 1250 718297967 718298003
    0x80d02090103091406160206250e0d05010b1305011203081e15090117101e0603080307180605070305091c0c050924060a2f011107050307 60
    0xc000c00f100140021684480d01200c2407000103225018150b44100b02c010122180422640c0d550221100c4800c04110101c0c1140110110044500d02e000c90811152491200c0b0228450051005042d01c00d60f458ac420f003005418040042440b156095606210541c18289098151113034404d00500700118500060b800c036611003164514a503082c0c5842c2000e04220f03040d500c108112134416449465104000140740b032249100b401c5000310400a000000b802480b0f103002000c4080f45003000c020898118082207982d07200c0e06029610070300003d52241000360004002d0301e2454000a42d540800d8424003c1c01d4214041e20501070b450f1514035a41d000e00d0000c20b04107262039071241c1c42c24010305000001c2104842d1140b06499082d078140700d0a07580da02007060741c8043c0107101001c0c402020400f501505150740140304401060800b84403a4001c0b0908062040e0281da07a0703004c2208522010954210178010251245508195030f4101a0580c860945030720402c0d03401014160074614200d14 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 718300467 1250 718299217 718299221
    0x51005091507022112122815090609060f15090f06030e060a05070c03120204080304060c051207021c060615200610030305030702010b060f0403051009080d02090103 72
    0x40c199004e812140d0360a0080841d07541120300709524841e0340a14400301c44205644001c2d6003101c19003481022860b2540d803981d204c50501000004624410800d02c00420242e40c00762a125280e11050881168a03109010040701c5150300048001d034205202080310a4a0074444030a690b400c244c011011058000141e4030b900c0c03154000c00fa058081c050005a40ba01640031002182c40d440c01e441440d500e07280c20300222102164010045042540d016012a07c110101044906e45c542c2c01031030240c484820302c1c43c42c1c02c240d00020005800078904000c11000780030020740403d00484040c02c1800b15800a220b01a40e2040083e00e0078440240200703020170750304401c0040002c4070800000600e0b0b447d00070a02d00004e000c1c4502c50340741641ca00c1c010440007030200e110f901200021140603007191740403141c40c2c1c000340c25202199203588a001450b66402d0042400d0214481101c0d0b41c0da10f1440c0085c01c01c2072003016080e010b440c095108011a00000840b902c468001c00e0040e07445a0420050740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 718301717 1250 718300467 718300477
    0x50c010204030606032f0901060f12020304060e12041a070f120522050a0e04050f010c090e18102f040f0b07110d020d08030a06030c0510050915 63
    0x19490501d00b00000740002a20000380c44450120048134208844058041b6010030342d941030b800c45d240c1c600400119100e11107001d030b6804a45001e0070007250300c295401c01d0340c01c10340c2c050354030702d64504117003070a4031041009120001000b603299041a151007190815224407080c203a801450000f0480300b0031030707009904d400d0311340d012034080b9000b8101c1c07000504c2034004a14003560b0041d45404400c0c482e0f1810390480031204000cac01090041e0420000300d00341c05020b80100c8035403080c04028854a08280a15000101540d42d0340b00341515205500015200250040300001401c0d80140c00c90140401d030400c03502041c1c039010030816a021109103810707084004030804c10b0761505c1c14110320b2081d607000b4030454181d451360300c0b901c0c0e131a0991040d04d40f04400c4024040000102001c50b5030420400103042e035070000346000c132020016121103038a42e0080340e00f001c15995940c0b06000b00142c3d11a52400340505031084c85100e40c4175507000e000c9205082c00716100c4c0119032103000c0d0014000d02120 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 718302967 1250 718301717 718301723
    0xf011101021201090e010b090c07140703080c060a05070c0b04022407060b03060601020307290702030901030e010c02030901182d1a0706090f0b0c0403020a1a0307050c01020403 77
    0x1540e503940100010600b48081c014140c02d241454080348040c6414050824014002061030250b034440070034042d00c1d070b44081002c0310305000700b00800350700140a0000400450048a4080d510410380802508212004081c4c0060502c3e05081c40761240c0d0203500e031080c1070b40c082c5100d61961994000100380680b619a4604070401c1c00310a11070882000c2d0140010344e202e01030501640031054105511801c04464643c0140e10a100c0740c40400d19001c5240c0140b091080a82c00c0d040c0c0da42c2d1141b0b8186412214500580d200041040712540d0520903030650070402002009111704003a802500d91054251050407c05924950a0b03221900031000c4000d141341c0c421003c540000a410040c0080b0740703544480010310011000810b040300401d040c810501801010303291146682c0e8140092140d10710a40d1407000000820b40040d440c481014020001c0301d0035640ca451461041000c5001c42c0d07000303000c0761800d500f880c8003480c80e00001c0c0c1c0d8101940d814203540711050320000900a0060358000b07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 718304217 1250 718302967 718302971
    0x9050703092f090901091b03121b02100305070806030604080a11030d09120f11030a032406110708210a210c0801050f01020c040c05120108030306010e011106060f011101 74
    0x20000714801503004550715445481c2c1c0c91f1407901c800c04030a01c400003038440502040440000052043d2003510710b00318541c52003501d80c2e11800745802250315082072031641c201007540c0300103000e01c098102c21007940c003510840003803402d45000d90710017001e40a807140080c140480702103102101c43c1c080c800d03202d40001e9203030100846505070402400010801d1581030100f245403106203074207841a55510102d4400b60015880c041d61072800310b0003440100c030040d114109504400300e40d5070014940708000d00083d07031441f00c042c10580b0803904041545d80310150540c0401000741503140000c0b40d0039403c2610105031034880b8114102038500141c03c8810030b03804a0b21854038800c1380c0301640300010038504c564030603610ba078850041c071288100400400380980e10174040e0b10910700d02500142058a41e0340750441c00d182403200104a414004c0c1c004805035000841001140d503402000c10008e0802441e0211005102e150101d4442401404c024081e03038040243e1409a4007441110a59494a00007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 718305467 1250 718304217 718304221
    0xc0702030f150c04080601050f041b02010b0418030207050909011509141506070b04030509030a0c14030102040308030a09030320030402041a1e1504030c09050703092f09 74
    0x1d503440b0220040141101c01507440412038107090316042d5001d9407003150081060f6401d000030403180a49401100d9401626004e00c81e52a26542d080410304c803915400110304c00640000f000161040c40103412a58060303155404040f0b580012244101c0e5070944400600b40c1301c0401484c0541020390001c40780d4004d01342e000482c144640c0c0100602004082070701035a4590a074980c035002d5502c101180c0c050b100340604408100440055a0400e2007824024541124840802c0c2040d200f4802070b03a030020846803c1000c20f2011030142170301c01c002c030021841d160441d83c808107580005005021310550baa17150104060082d40f00640c040c0c0d8003a141403211000c0a10030300f2030360080358100d0280c0d04041c01c850514684041c1d0140e600001004111490b8903003007070341c60491110021a9204241080561401c00b41303800a0010318041d6011404203800c04046400380e50014000e43d08143c0381240c0880420380c3d20520300e040720038a44051848500101a0f8841040f003100c07207036488540c04003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 718306717 1250 718305467 718305493
    0x406080103030305060307061205090f010e0309030f160b1b0a0b062e0c0c0e0103050607020d020609030711040b120c030118020604090c0908010608010209012a0b0c070203 75
    0x59240c100c0b442036070305000f6503440c4428036440d0300303840c450107010401c5005604404030440d0000707039101107100304540104c0c2c0980c01e140d080d10108003a28195400000305a040c81c203090116a10030540f6100814a40586091540e65a100c500c520844100007144d201e082d400702c010601c8003100b0707240448943c66aa03040402029100b6101103100e488043c80340d02c3c6e10740c5c2e010001c074942c1044030605121496902c1c4103440c0c03c442400c040b1a56840c064011414901642c511400307180240002d140d42d1818401c083d03e0700c0009a000d07425940004100000800d0000031540c59941c00408400d00c08010030100700a00045010f040e400562441040711a1000107a041000c0ba0210000c1c090400404243c099110032814040d401c100c04010602071200a50440c06100c40f00340b80c284011543c40207510708440e4503400c8002d50741d400082d100003560b03000c2d04000b006a002040e90400c1c14a00b5540b0000008c040f5001f4030360a100000107224020000a650089801a00355149481014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 718307967 1250 718306717 718306727
    0x27030534090c030c0c03020d0e03030c010e01020a020c010810120c05061c0b041406060318030f0c060601140703080c04120c0f0605120a1808190f050a12050c0c030406 73
    0x42c400020b04d02000c007400c9500c03034a6030789401c50b00341e00a006100030b400c108881c803840c041d074040c0e0103200c06c202014030002d0074030481d04002d43e49400142c44814821000382410a40b468041c104814503040c4202415046e065400312818400e540c0030021145c501b003e1125510f52240781d00c4503000c14010a401301e00c4110410500300c0460801c404402c10003044105c0e082e41084201010104001032500d041c1000296000086110300381c170034050b415102031a41d0300c1003d081c007220300013050311448541d0400160380c0004013403c0100060030a20a44046401a07501c017404214040010a80c41c0070560704590113071410b80c40400001206040c2061144a075100e0076904120703102002407078921031415650030300064022044943c0f1025105009401c0180c0c0d14a02024428400400a50084024064440032459285c1c0c14021000e014040300a031410311000c0c07001c02c100d074003880355020708040322900701400002042c0d2102d00b1588141c0c0681e0000310340c04c2c80001408a0241d8100e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 718309217 1250 718307967 718307981
    0x10207050d0e0406030b25090f061b05030708070b0f040b0a020a0c080408010c02101a0d030e04021c0b030c062502120106180908040608070e0a062703053409 69
    0xb6414807d0000ca480400f200d0200003445454039580b109001800441d00c16900d0303000300b004404108240c20f034540c48860071680444011079100600042a03410880811605030b03110b0002c006007509842c0503110b61145900007080c50303451a038009a014841400340c00c801d101c0b140c204903069144c40d11001ca2500074110921404058403916016040c08039280c019402c003a00410036251415200e44d060244441450f0b00450600c22400040c11550301c45101400140ca0190480058015800c04843c12a01a0858280641c21030032040c80d00c0d846010272183d07680036a240c40444119442400e038181000140000c1d405070740b04078911a187d00c1500401c05440800c640701d0101c3c2c03040c088010403200a030000518400c802c5c007003009200e00508044c1e500404074140f00d11440d00003000244402019004200490101c10024141090820224401440201141c0140341c1540c0b50180d42c0c15408c9000f82c940003043d00d01c590094030703401e002030045103000c515030522526031411001074098 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 718310467 1250 718309217 718309261
    0xa02030709080c0609010c080408010c02030d0605030a1110171005011107030b0408030705071a010807170c09070215090120041d0603070f060302031503010207050d0e0406030b 77
    0x41000040b45280020454504014006100d60703d0107000d080155400d001c1d02000b41c85c0700700140700010382440c0c28051000c02c0e5480798003550786c81410030958001c91741c40703810250107640040c0350500001c0b0486415020b40354219001c42c01c51600c0001100c1004e10b50941c00c107034903c001305020140100c002140d0990fa426295081d4000c43d5034509550341c801e612000e4861740c00c0401080100d5843c10065400004a00e007241c40e1400340d4950300703e01e2400084940e01b0000030b42c010460680d00b803200b1800342a02c1c2c2c0e002c0c010150070282d000c2c0d0303c070280710200d4494101c80d070100c2c0c80729000300120418400c21103802c13040d526003014403d0007403481c3c2030b074208820428500d41e404110418120f40075a04203840186101007810041c18805400825182c1c252044131408607240042001c0c840051010740d1300581e6a20b42180c0e4560010b01140c0124080d81c014090000000c402003044d0284003064034100039010b07807a41c002000780c0138551019001e00350140900140b080c80010100700c1c041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 718311717 1250 718310467 718310477
    0xf0e0316110d0c0e1302060a050a0c0807230304060c1401061e0603050f0f13050f061609080705030c150910120c0807080c09010311031f0816120f0501050a020307 71
    0x34400c5d88050400d0340042001754042420010380d20410f005401521a2208a180c036107806505a59000c130654001c0c5416101c140040d114980c071444d40080280443d04024091414035142032380240006003903a000a0a00700514011801c2031001d51000006280d1078161140c00444c008520300d40d00401e004080010303007001c0010744d0501d444a215030245502c40a044040d9407003514070416416410022581c0d030250f261441161282001071a0080020a5540901424100b0040c1014465900c0001c1d1500306500c20001a90003050030402200192801c0000481307241028810b4420001400d6000088805075040c0a6202010001841c03104d081006500190714040c1c940902c200c0350400094044000100c0c004418406880c1191040c100441c515a00074240511a041121003000c2d5a2191020031021140da0040d14010120b00014142c00203a0508440c0c0c1440c1f1400351000f80c0054a1035801003098902d0303ca445190070400800950600c121054083d50085e03e500c0f0001d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 718312967 1250 718311717 718311721
    0x70509100306050105030406020f19021c090b0a031503060c0347011803111008040305090108070e04050a14090d210603240f0e0316110d0c0e 62
    0x28040c0c86070b03000f500d1050b140c40d0308507a12961888003035070250645a507540814080760a005102c1880d1003c560419005008540018005103c2c00c00e807410810f4100000c48508010540545088903004a018900492004503914807000103100d50b91006090034a4101503004031a81580818014088161f191030300b40ba1919114580e4456001c4106100601160324903010400560081c1a0607060402c00200a800000415591040e5006039081088010801d01c01d140c440c9485055004504101c4501d08180e00c2c001c0c1a070290100d020b05000240d8041244c2038010004040d0302e000041003030201e4074013505000d01400501c03110080c0b114141c404035a030304a012a9407070030240030790345040c6088107504c0e0742543d049504440c1080540d5034100440803d040c6c11082101d120840c403550889a84102844115144c6004c458201860300303842080d41c005c044100c0e01c4a101101d070300d001c4101541800c0009144030168147e100440d4000340301081040b091400803240c03035966641c0e840d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 718314217 1250 718312967 718312999
    0x106120b07120e030d09020a0f03080c0607050a0225180e0d05190c0204020c01091212020702010e0108040204060906380301030f080c2e1a0111100203070509 69
    0x290710003c00e0300b00240c00c1444200c10f45002a407080f11800d00040014807440e64590042103e48a5a00305503584400001c0500102c00200800794000e51145092451b002c042c1000035101c00303210340c034800c5019444849030b2001070303541403010242c40c048401180041704100c0c0c2d500188800c0d46104914040e40040c4124540508281d442710004a0f4000e25410844081140c10380c035510310499000f907007401601c0c0c0024091103540322140c81518003171000342200c480500071a07081c02c7d03100010b074010403903100180d03030048080d504182c080c00c1040d45601e43d0310005014241ca80c0200e0201c500e080c40c002508140c10505e081044100041c81c560020184501845200e800c50012441e4404000400c00102c1c845030340600d19004081345404d1941d0345003880d00740540100381400d5451030b200c030014464000800c003401d03801c240b40d04000c0d0140070301c1f001c03810051001d40b15040c003d42810000c0580d005101c0300030802410034085581e45490700e001703803194101200c4030780282c00c0008001c0c04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 718315467 1250 718314217 718314221
    0x1118010207050a1511030a0504050310020705030904020702010512041212060803031302060c0f070f08010b010206040201030b031014090609190816020402130806100b0d0b01020106120b0712 83
    0x66400242030b00c0c2055081080c881c01c00180001800c0401400380d0350b401721207000f400540f001d0281a550b0395a140e280004061820b130404609000440c410014513001410010442358031600c10f0780d01584032405800161441d00808002c52942c03e02081040b003040a64941f00b4000860741c0c6802803d111000c103888111461405004010745c000c1020840c15171185501e2803880d0b2000300b2852501c00c400124074180440301200c12441d5004050130300c500d0004000e054090022100200044040070000035aa00c0300a080030703050540c1d44500c200c40d41c400b8000c85520101404091010403407240042120020840741d60036903003d800c0c0850b018640105414801403125180001c111840e500c1e8000542e10104080070003c0e055900700c00181c9550000c0c010b007411088521812501e003001c41d9090a8004010b1901e08190340c405110581d0301e10243c5000c44085200003a0100d02c40300140e0040982e81c00a142c5017240c114000104284821640d11503d0389944516070301c4410001702d02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 718316717 1250 718315467 718315469
    0x8191a0a09051002070b15031618050610021f180f050c030601080d08060a09064a0a090b091f060509040b041b06020d090e01061403191118010207 64
    0xc004240d1010404c0710707d48008a6a140800406444e09240485000340584085a110188910968000000b00201441507690212080c0e03540c1d0b1090710000d100940b244440009000003181c0c00c040742c0200300f81c81c0d210342035040f44414504a417440c0e9080140c030455451404444074814244034203030909000c14054100c0d4808001050003958899050b6034101d0004c0034950001c00c0c007140040c1100d618000c0c9002002821250001c0c120f548081030510361f40d0310360f80c1c00280004190004049001c003031400c00c40a8030200c51000f030b1681e00014024000e041c9000d4208180f80050101d100b8000c039502c4c00030500980502e4450940da58408155030071485103a41c0640da00d1b00040110f0a82c40c0b1465100d44a584510708205280a204041d03040300c1e040300300164000780207141000d0300902007001030490f00c0b2003601c0c1c0b9807410900502c00c110701c42c8501c003060300c0800070504904150032102b00444562009000c940c1001c0542885900030381c242092103609140c41010035400818084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 718317967 1250 718316717 718316723
    0x30a0f09020406181d19030201091a06030c10140c15010b1b070609050d11030f061602030301050f04020c0a0c12060605040c0c0b07020a020d0507030b07050408191a0a0905100207 78
    0x1c010101017a01d1444211441b81d000d800b95501c07600e41e000014500c1d410004142d082d000107034854104282803502e00040c0310709280c0150480700c00c520206030030515004521010410040d030791011b001c107940c2000c608039901640c0e11001400456900c1c28000540010a0035038501c1965101520285a41e48224414140843c50b6280e003886603080856028400c3c500601d224400303401040d006c20b14058100b41c134070055402ca44140070882c040d605650801c0d428500c029411035041c103000441e42c545107014184a00c0e800245035002c0b038014814406a2500100659111340c0c0d2802c20002e10104404220340c0070385080008510f500d0288176a410f01c0c3d669a440c8500403103039a89007030040d14040e100106603c607000c0c0040059403482c4c21a1002071003080900703245851850305002070728000c0c102130140038040c003050040100000740041503040c042c00ca0b000101c2c02e030400c108000c07600c039807000c500c0880303504122206806070084064aca2083c0c1c05ca8800300e56000485040b402214401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 718319217 1250 718317967 718317973
    0xe0703170d0c08241c080c0115060c110105070b1008010b0d05120703022a040c0503070e090c0c0304091401060305010b070f03092c010b04050a03021e03010e0604030807080c030a0f09020406181d 85
    0x24bc004610070f20000d118513007060412038540342894541c03a10944044403a10784201c00b20001b480312480038000d00000309002c0c0d4000300c40b680c075582e07070544861008003c901c080c2c0d804107503102818402c0040700903070f0b800c65078100ea800000c0b03403005080c000342d00d84c4180218103100401c41c1d81c42c4180100c3c2d10554403a6a03e91003841e610381007020840010b8a4110940700c24001c6580d8040103000600003400381c0100052625007006056561940591041090501e0480108254031488003200e414640c4900c0708000d2802510381038488108640017059404079600b0b22003845d4625660461607010014004d02c030716039a03050714460078812406910b0304039117034010810040c248929040380c821684028025406440c04c0442e084581c0ea110100381170780198180700515401c4464240c006c651450201d40c82d00c0c00c01e800e07403aa0311010b800180c240e907881c0d80402551601d68440e80c96640c0c0180240440c55a07900312800c00a01c0342019a085841c141740696440e0207040040344150f901009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 718320467 1250 718319217 718319237
    0x60905100813050c090c0405040f02070b010b071b030c05041514060f0c0307060b100c050307020f01022104090605220e0703170d0c08241c080c011506 66
    0x29407503070901441c41260980720340205007509990700540d00d441415400718540d247c0380740c0010003060b07a905028803210715104125110102d0f41c0210154103560008900ca80e8a0486107800040c0140420010208000c840310100c20455070541500c100e400c215014090004086c90194030071030a44582400304050700c07401207142c2003c0300901400c07803403041d00c2030905500c005110704540c0103903812550039903241d14408292501c042c1c440c007100290f01c0e2405101030560b0750640c0c2d034822144007034800c860400c0c180016a09c204070707544412050700c0c1200349400124000d0080340d0040c0c080c0400d118105080400c1d141083c22904009801d14a501c50700b2850044c40ca00c014900da00300c6580e00c0c01466004000318140c86a031303c1c00040d1078108281c1c0da0301600214801c89024075585400c00000c0070030300c600310b40c0b500f00390720800c01000c0601181600c030400080c11040c0791400c3c408440715090400c024086500b018000801c1900000d10101411000c0c0d070f1000845030050002003019420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 718321717 1250 718320467 718320481
    0x1050103020f042f120a090311120301180617060709090c0c020405090309060a05040305060109020406211b080417090108010312050f181806100509040b190609051008 73
    0xb4040744c201c212103001c13031801c080a480e5045aa00071030399600702c29225100d040130582c1c80301e10102c00c2c040c0341024004445121008851a10040c802c1982c0d0010714120303030001c07030400e500c80401002c0f006090080060719026264031804e00700c0345d03a00031600346180058152814001c000c008407595940031000800d41d4200720040c440a082110544020301c030704c032415100e0000500901015032215078030b861075490907a18080d4144c204520450040c0403c12019402101400c0c20100301144020801c00c05030091004181449000664070303824010010440d80120400307029a0085080f003540b00100354002400b403040010309800140401d0040010500d40c034441c030b91030023440c40c00a04d07150161840803c035810900784e1400c030305030000340038185103071205020a042e51150140010380c90814001907440030b00c29190018400005100030382641e50340c0c0b0104e0500300c010900240c10381075586294107900e16015000c00b090290303a02103081e00d0682030350345465542ea0350340103055403126 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 718322967 1250 718321717 718321781
    0x103050f100506160f0503121e010b090d0203031b121e07030e03060c0a03140903160303270b070c11011b060507050a1b05060a090f0803040501050103020f04 69
    0x400c142c3c5a4140c07007084e400000c4c214010040a09004600443d00d0b01c0440391038401d60b002c003800507140709400c0100340b10400b0450340101d0460700701404050b01c0d8001440801d0002c103000a000794076001c000b030380c00c1155400f918a6401c02041c441260854008509107108520031180b050743c88115282d010f4204d807440b41c00034500144079107040c2c60096811400729140c0102555005540310021528800c510303032620407400b014400c1d5000e002c190a262803c25203900c41e4415600e4160501c00c0a44103050080e080400c896038107460350083c84803503004100d080c000c45134045426004c203001041c5047d00c40d20185e03d400307810076221000c000c130307440c01915500b0a0014a42d0803c240201075404960b0a225081c850070583d101c02d5039990f0000e80040039110312945500070440310507034810210708002601c6a11400e50040080d0001c101d061031703218004000343c000c1220100008000c104501034111a0480e4030039207030980766491500c10802542c041042c0205040c805161a4501303e40c41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 718324217 1250 718322967 718322977
    0x7080301051c05010f0b100f0905010f020c120a020102190308060d021512040c050303070804030618050d0201020918010803090d060b0402070f0506010b0c0706050309160e060103050f100506 83
    0x112100c0d080c0002c10743e03401c1d0075101000107003510650740e10340903090360520780d0b40d10450325081e28040b800225032180241c480c42d018010503041240f40550303202194000c0281d903c180d10004c0088500140070b10409903615813128049005001ea1140818031081c503000303c1c000c055054030352121a6903401c050282c072051a030b901382e03800008081b401724906560380003003e4114460001500728549130074442c50460140d8007040c0030760700400032078000c1a015000d4409030b030350004c0045121400d00800038915850280f0140a0340900c00f54413041e143c055004100c0072200b82c400450580c000c0e1000c2d49120000d101d8011241c008208441e901c3c500510381d200313244e2180380005880084040410200d821000f42100c600400710107020511000b084194018044480500c0c5080f9807410b403903840c0d64003445400d0502c4004000b00b503610030180304c8642d0f0244210b800151040e60f40c5603074100c80e0001e44800e8042864030002c180b040c1510600715200c0c007140d00b002807101e8039200c02e000880e0302c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 718325467 1250 718324217 718324249
    0x160608011235221a030901060b03010b120f060d1415010f06080a0b010c03082221230901030204050315011d0103020d0201050a1826030708030105 64
    0x1a008020801048110038410300050544085460b000d0026504416036041e0142403081400040f0402105010500344c003443c5480310503064681e20343d10030b400c0c050880d541000e1401d032004000030a03281c4494018084d40c20703140c1c02c41e100741d4a607507503c800c0d80301003540d06c076401050780301c6008041203001001482250b184021510042c841503241180c120081e00302074040c41d403c02040000d1a0303c40d00003600b0400c0000c04009a103080c2c000a80100b10b020310003410b0000d0306001861243c83c00700c41c0c0c40340d0050911405014946071801c0b9680480828180c0400c0d640c1c44c4458600178850080c401081d41c00c0100d0710102c46c00041c00103441d4026065540c10075800f0000490305840900a9000b1400e0002c0c401620354145103542840c2044003400403803d6490400410160740c0b8451510801c3d9020b0805a0740c82e0694141210002c0e081003448160001c100800940103842e00030b0301d8440040e21809072114000c18044903145d1240181c040c01c0d100c01400188920b14001441c945000d407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 718326717 1250 718325467 718325513
    0x1051e0601021518060a0c030609061d0402010c240e030c070b0904060503010204081b060310050d06090602030411090a0207050615010c020a230406080d0e030106090e1606080112 78
    0x116035001301d458031300c085849204260300c07134203813803041c030b400d402500c000d030480d010140300b0741c0d041107516a404007039110551422200180443c040d64020b07080300c40030a0b0400d07070b0004070340051090010b07510b4440140001003441d24900081d24400401502d04010110015140c2240b80841a040780d0f001214940d46c85540c64900040d107a80910090008016060140034440000322503e02003001e030354000340c0520410400c00561489062400d02502c004459010b0b00041d40d00700040100602c0b60020821840041404148503032031054400c00070b13040315071148541c0c8044c050b500383c1c05118001000356010030040f4641007107100609078080f03018540f2a200400ea500020342014295014110810392a07a03861001180660b80c025040801d507024450240741040c02da60301e040c28449007007003280901d482d81c0d05a60a4120400502810a007440942594400700340c80e043c40b10017010400514543c00210f080c055030300c0c60704850401d4540e103843c00440c0c03607200303014890907100e60040c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 718327967 1250 718326717 718326751
    0x80a0b090f0d0207090e0c0a0611010906020c010e07080d092c01060809010c090e01031b030b0709090f0b1f030e011b0f09080705130209060c01051e06010215 69
    0x1000c01c005909400b90203900074a86907241c01e0454085810360b4040e80d060703400c8186003014503101e14192504880b29441c0c0b40c20741d402a1018580100710041c4002d1030b0900000d615284d0030015008a14080101d60664104540e0b840c101d5581f05804200300e0040740350312030104220b074011500f000581000c01c0242d00000b02c40e03a00300400d25401d07000a00826100e006018034501c09128400402920f410040841410f064294000110520008040d560a0f0744c800c9424a051a03607036006550142c14200e941c1416600904a04902c0c05082025440d040d14040200b03451301500e41c82c1840600900f034440080341d40042ca50580c41a15000d1544640e00a005007200348913a041c4529400341d1744401c2e205070328000706a0000e00301c50000700903101c5c000340100071010406008480c1c00300d52302d500700508a038001010f40241d0750016030204001c5402610050190022889080039845180030021031418920101d002600c40c5801640201c04070b000740c0304200d81c415000701c21002c030f180b226 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 718329217 1250 718327967 718327993
    0x1d0402090a1a0c06090307020303030411010509030f0606040f0519091b0807051302123c010f0e040312090201030204031b03030306080d020307110619052101080a0b09 73
    0x115030103104509189000030b007a040300e0401340602c0d60001e41e800e000c0e44c5817a0317a40d000244d0301c3c0005080900904845402e041d0f1503070042080b240d02c0d03140a010755500604449400e45c541c4800c0310341d94013a5082c0505218003039014030849100f041d0750070728907000c1d0740d03816011802001841000c0b80c0707411002c0803101d640c11210000d50000c109450092010318104070030700c9560407442c00b90303070f850a005210690100c540d41c064990301030414403410f0720340700481000c0600074100015840e80b90710030840c02141c0010140c00d190603240700b491034a00e030681d00e0100c10380d20030301200e000d40060007200042d00d03040803940082211500500d40075041c07680303d454a84000320004c0040c034017a00841130400030550940a0740008140e403002400c41c08085040c043d44a00c1030f01c000409040c02d000f000c0c0f450b50344020550b40941c80307201810f0b590240000380a0301d603034030819031040f00745484151104410440c62882d13050b40e0840016240f81d00c000c2d52071007000708000d4000d50250103800511584 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 718330467 1250 718329217 718329239
    0x11205060616050102071104020c1b0a05040e010b0423010e0a0f05010801020702100509030c0913060e0325080d090606081b0a0f120b0c1c0218011d0402090a 69
    0x50080000680d031389110324008094903547c0c4076a90007980107001c1c0590080010845c000655681015483c00c4a40340000a040d440d071a042a44d2051820108000c201c1c41503005e100840d60981e4200b11032b1903100c810b2190001940d0190903c40140401032150854649003071390840c0c00c00c030f008075141b990034020703000350369098011014582d8049000c50a500d480d000e07c5000240e2801c0c0309250020500100b6124100701060318000c9240700d0120700071035940c0100c03121003900002c0c1000b81050b00202c2c140c582d440000c0b120302514803044040c20500481e0907900510340d008a005150600c402904006010700c41c0c000d0319126a28000020640024018080e0f051070320340d840c0303140d402400300300300e105a440c1d001450380745d10b1403802340110325400d0222803507990028082c804503514040011030328469004840030f05030b101d0b100000102c00c83d0300a05400e0070b1003007a000580006900442c1c48510101040c04ca9440300c40d01c610032030610340d004060031803026188081480d01d0f000510f207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 718331717 1250 718330467 718330507
    0x606032d070801062d030b0a0207050a0204090303060609080d050a031805150709090207050a0b0423060a0c030209010206061224010510050a141312121b020112050606 73
    0x20b44003100d46030705c0e4029800d02072050413141c440304410200b2402c645a200195500030480e00b00d080d030014a460500404010040e0300e81d600802c00e2202010a140049c080c16542c8240e00c041170b01c001c03001c80c1202002c03030f1403442403040750b407071604154480f14120050000c00e515100c0c03847c0c04591400100794140400c5054000c49118144603040030000100b02682960000003070030b106004510000c0d10100d95220300035000b511501080d100c1e8148450700c440b050100b0308811017100400c10384020b021400e94440c030003043c01041841200070099090340b0030001142c0c01a00148000740071850104100700a1000c6001141c00202540200740190465001544822800400100108d1410420980c11544245000d0f0706000800b04090a844a83c92030040400d0010440c01d0130a048a0031a00c02441c24060346680c201281c1050b0100c0101045c5610005403400711048010000380345003400a5410381d20502f016044261001c002c0802911180d03004400700092110f42ca14503020300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 718332967 1250 718331717 718331729
    0xc0304060b121b0f1203040306112244071e090c210504110a030f0302010c080c120c04050a0602100b010804030e040b030f0d110606032d07080106 64
    0x403d0b030003051041014000495980d18411008408030703c800181c04001c0e642102c3d0301a501040080354000c20f402d42c1e0040b110a02144034070811400015241c00a00744110b8240c4802042e0380000c11110b08004152410b8010618110004000c8115440e0189201c501001710131b070741e0540d4075503000001e0090411b4000c104c0340c110344000d02070b420041c07160b00e01c01d0de043c1c10041d07030084d0915030301038003a01c8100b00095801c1d61000090240000c44043c0d092051000340281c004d00c0c6c4a1030b252100c84a0a08141d006601e815000404540106003150099400710556400c1041c0034011001c4030300010203c0b08070341ea0a00000540380c07604002200903000b44e0b0007401a20301009130080c1199081040c1ca17040081c040300b80300100340c024039105120301c1c0590700800c1c1031480c84007003451700080c0883c803c030342d2180c00000c1c1045607008011802d00f10300e8405543c2c564032120101036842200c194900d440c00c44505045080c449110300c03484100e070700d50003500c034400d030743d405000c0c21a42d1030b078000703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 718334217 1250 718332967 718333003
    0x51f12051e0f09070e07180308071a010501120209120a0b091219050901020118060b0307440601060c0c0623030a180f020907080c0304060b12 62
    0x71256004200392016486110018003490624100000c00d80d102810702c68007040d200200041001c05201c3c900c04603160100c40d40501d91180d0f42e1420f14185d07440601d007034402d14091854000c908100085e52070407114141d4401086140100805000350b100038100340e40030710310b1080c07040345503030600030014980d002c4c181d800158509041c0c0107051001e0410008600082040600051440120040232500741071400507160015100180c1c0180090030300d0540081d05106140304009554011003007040d0140e05580c1899600c0200c244031182c0300e4406980150119002c0135294118410410401500c50001002a400100b040d042400c00c1c0c0048001918042c8a403043c0128042a44020310703051503c42c4041d811a03400000c05040200300802421001001c00d0b09040346800c071600d485070044194103c165075140c00000030035650002c900441ca040b0016440c00c0c0100c2d685e40c03054410203809851603480340d840c40020700d9200c00d05a84442c40f080301c440601c4080003104010000c07141e407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 718335467 1250 718334217 718334251
    0x6030507052b0b09010f060e011709010b1e0d06050c070807030503040605060922050c040e0c040c051c0504030519050a02010e06060303430606050604051f1205 70
    0xb9002d40300b06100701c5006080200042004002c8020420308603003562030481000301c50200100e80034070a0f20341c407210510145082c020002c0040d40420103006048810000c410303c1e03034a886c0781c8400c043e0b09103640078501c141751001003030550300710583c0803844a004618014540e07541c040d1a4210140640002d40d000c0200410002e1b241b2550350804011900e8120510b050320000c08035000c09074005002c428071000d04030400204010300c012468005006002080818a85507500e080050b000c0b44158102000380b41c6c035030700031021580d8850080c081000c5050079000c01c9005414090400c5007040303c10808038000d4040d140b0741c0c001107000b5580303d0750b0b5156074042c001d095429400314022160071a1091140c5641e0000448ac1c2046245a0b00780d5420128101c191400d05000c3c0700b1450011010900c0f1a182c00c2801036a0340e003071190100704015a1924181714860185000d183c1d0400c00d00d5081070b0000c004240008143c1219181180c945104950444203072081174038140760312110800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 718336717 1250 718335467 718335547
    0x615040c0f03050a0e34050d0303020918011401120b03120c070302060a0809100e06061009030203123a051f03050705101106041202160608220b010603050705 69
    0xf031b004460503200e50390076907581400f00090361401c074031000905050b030000b0494120303121009070014480f001c504101180da520340b1007400050385449a940003807621146405040c03014456007201c0540a00204201410420391921a5000c081005040c0c8200440000166520300003400280e0b243e507079140c0581003041e140c030300d00303c449022280a58205604041c1031000011101e90120b0100e0b41e03510384145d903a00503030345080c007500f0194050144814074400d04090303030010080f035618049080c0c0c03541250001c22400c0800d40c05040703004a003100c440001002c80d50012600712800001d0303a1001000c042e40c4105d034503010b038001ca41036003114808200c0d501d4680909d001c0340d106824000b281e034184d220703595206c94000308010500348800603e154007620030022814048000b44c000d065450f21014064102c4104941d010f4082c0b401c047c548001c0f43d10200f04a603069401031000720941d0070714000b507020300300c010044010400148120307403048060044e2400650010740d004203005150300c2c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 718337967 1250 718336717 718336783
    0x7030908010903020607210216050c1e0613080109141009021302130b030406150f0312110c060706091104060308071203110c0615040c0f03050a0e 64
    0xd8030044003a4900844203000caa000300e2019844100d500d0004070b000c0400e0310035610301c4032000741006e0701d03840482c041e00c50403001800c500d40c0310300a4046410400c103100400103070800071103d06008201301c401d0340c081420800007500d40510740030a1400107540703503031141e4212003000c202a07070340700c03440700219428078400e01c11800b50003811002848400c15680220300d900003440000f4208a60008a40d041c190020055002400c001c3c58100e42d07078205810018082c203c80d00c4c160005000b0b90b000010125040318001c02182c0c1c3c0180700300001c4510040903695058001d1300e40306140162103005000c0d0f903c00006050707540c4100320016800b00d55007031403a031103c00d102c0014000c5d480c040041c40458007203000c0e605102d80c03112008180c1074080804034007404440464040e815408a40c0710302c500d40c040b9010784152000302c524240d00a0b60404c100540341e00b2a104004100076055a2070030324481e8004640c0049018004140000401105460309840c0101007070210300c0c402d00c11803d50544 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 718339217 1250 718337967 718337969
    0xb090d0305151c020a15050c0d05031306020901030b061b01050105030f07030b040302010b0a03150b043e0c031b0a03020705101707020c0117040506012711070309 71
    0x2c0d00008180010400801d240080307030740610003403180d00a094021581d07816a448081c054011080c0c1e1030107940240680740d40c101c42409103190245034480c0020501c1081907900c950408487d4403106803007611071200035403040c05031904050300c034800c0503a0f5440700310081c0751000c8808852641c08003905901c5003100d0060304114401d03006040c0a03080160001382d80016250040f00d40ba90644592074140c0c0140704111103245c100c070084400200b44800340384441d0350100014800c1c05070864403020041240c0800c0f00e1108000c107168451b48072200034401310b0824210030900d000c1c001006440340c85031901705a07000040c55200043d1610060403101c08100c003001e0b040c0003400d00704095075000e902c640300e5005583c000c88030380c081324580f2446040c504043d10b0140100d1590740c104044002d45070800d42e041d203800300da030604042c40c59140c0d514040d8800c94000e805040c03d6401c0c501d41045002ca02500e807940b0341c034401011804070320544a0401e000624100039982d03101c60340f030060300c0580740f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 718340467 1250 718339217 718339231
    0xb04060e06010909200c071a0a03060824070210090804090b09070c080d0209040e010f0b01170105120312090a17041d06060c0d0309061b0507080c0106030b090d0305 72
    0x82c640f00103200e052030305d1300c101541101c001141e00c031070540202900d041d0701984900d400b0f01044141c42d50710790074000140b40c54416070780c00b8081c441d00c440120740e076500000141034078031403103400c0e003000c1013121540250400c44138410f60f074090281c84051300907a6422102a01ca001c80007504100388802031043c801c0e03030502079034038110920b4a02d00103051414410320282c02e03000005100d41c00c20140341d0442d016540b0041081260410035a0454005d100a1800d220b215142c024040e0242d0b000b4104040246d041014601e000e0b0700b05002d000d030010f45204841c205100030b00205d40100240158a441007240314000c2030300401500306600500d4070180c04144414040005124400c1802101640f0000d15111541951165008504103105030510310206c3e0045034503020750681c1c9a0420280c2501806041c4108a0002c1410741c2100c440c44400011580c1041407800166004018106800b00d00000180d5150b40b521685058407044924800c2c54100d00b82203401c440c0c140c40350302c2d08245 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 718341717 1250 718340467 718340471
    0x3060703090b0a0203040f02090a0c090602070b04050f04020d181523100801150801061505040e0c121e10030506390903070611120306040b04060e06010909 68
    0x907100c140c2c4040c1c028002550312500000020203000d1141e410001c19503000d8600c00b524030302564404014010060302c00000f8038040300019060b03100082131401e079041e040c402c0b85498500020050802d0100c00220b811a40034401c41900741443d00c55100030007038804032021907460070302d0076402d50051020079281c02c91405944d0080a2010201601110164000741401e0303100c1c441e4030304113041c0d19802003183c3d41c2001084102c45103540d810a0442d68a600280180b50f00e07078112680c014400d4200f04c00003803051004000c03010304c1031507694002c01d9003207440d841c28803480e541d00a2000c00311440c44c0c0490281283c440c13010b00c90324071140d0001c00003443c11803c40c1540e4039907803560310107046541d03199003101c1035840038031040c2e05812424045400070804648080c8412046400401c034451007401205000503546002d10041d45100800401038444002a008041d105030405000603401c0345d83c5441e8110706440b940300321000b4002c40701049025141040005161100302d420801c1018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 718342967 1250 718341717 718341731
    0x20a020321041205031b0106092a0302091302070b0103021513090c0e0301090f050705030303040b0106030c0e040e0c1509090f040305072a0905010e04030e06040911030603060703 78
    0x5503841e0a550903141c800405050851041c20303d180745004541e5003245405e146220140326460543c0301804461103a041030181003602c0c0008001c044503640e56004d143c0c460300d0800c4c20144282d0051104032001417000811040c01c200480407078201c140c0c103c502c00200c10041c000e51400003240c215100010a0b100d2500405900d90f4820b125a032042100190310345540e40300280c05141150f44801000c0d0003000383c0d603428280f11100d050a884103540b54094204080707240c0c00c01100b201d10981e0044119540e5074a8580118014400144054100207441d001840d0395030b03d502600d089a6070136401080c0040c4076000f007240c0c1c039944a408040250082240c0350264540c008025481080781c1c0309680241e941b81816240c922486200030a81040e02d1801d40541da01203c200105150344482e60700d51035107030f1004000f01c6000b80102c8040c0021800014000707417140503642c0b03070404041d108030b05003680c03544d540041c0ca007001e00d4403114503008800c01007242810424554031560303901e4244090 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 718344217 1250 718342967 718343023
    0x609080406230c03071127010302040c0c0507150203130e0f10050f0d06060512211204080d110a2303150d140d0512130203030316090905010303020a0203 67
    0xa02c01d075407009121504815006d6035030fa850090054034032441504000900d0983d0b0b054100039002400224400ca2410101107140e40c41150704010f0964000000c0c602641030008903c5020101c0900d00304600c010003402c1441d8244010080040699503a52036031410030811000c005d4000410005245020309401c1029554480e40000c03144e0b0f041e1203a4003024a1303820001c010305083d0300031940101c01e41d0104174141d400040e0141700701d5a00319503800b100c0322081c1ca655403882185c030401e02100c0075901103004200a44001c11040c801003000040c8201b10120740c1d10b05410001c210f1001c110107014040e00183c2200d081c0c0201e8007001c100074030313507d45040d07040703041150002c50b0f03402590240740d003004000003c2c08080203400c0741e000b20384d0f50061400b001802584001c24030580c0718111408280d8800441c440d00c000c181e40140511b066940b01000a408440c0d00d21803002000310740c1c100003820f21aa1f2003a0340c003031402076000d4a9220a103006140c54449002252081b48484007410099 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 718345323 1106 718344217 718344223
    0xd020303011806050901030b09150106020c280e060102190606060e101e03061703040e010f080309040902041e06150903020612040609080406230c 64
    0x4851214641507884a119845d00940031000610000d603803030003003c0c1d0219208040b107611000d07400c0f8001d80c000b0280d00580150700000b9001c1c009080132183d81003001d041400355010754100700c01c400b2080490b485143c00142498002c40c040d40e02c2407043c904000ea909610416081035410540c0040405105a0021824240300b044050920f1fa101c001d42c3c1c02e02d5124030b06840340740c000120624a444d4103410405030b0742e00010a01008104581100b5002100116240c42c2010034040c0e200c0e0042e0080500e2452002e8204801c0100004540301ca00085d40d000c210304e000307840441e0150411104480c00461058684510b80c3d066a10407821240c90b81504280390081c614299282d81c12400b020350005402c02c120b000c46104003c19982080c4038010025821005484100407600a0380000c40012104c040c20b42296400c2011a500300e005800303410301d0110b0000c40650703 = true := by decide +kernel

theorem cover : BRFrame.Cov 718165467 718345323 := by
  have h0 := BRFrame.cov_init 718165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 718165467 ≤ n) (h2 : n < 718345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
