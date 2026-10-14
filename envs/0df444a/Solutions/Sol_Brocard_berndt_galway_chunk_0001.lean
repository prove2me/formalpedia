-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0001
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:17:38.504887+00:00
-- url     : https://prove2.me/submissions/996e614f-742e-45ef-86d7-ebf1aa40ddf2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 8 ≤ n < 179864 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 1258 1250 8 11
    0x30201090506030103030206040303050405010b030304030302010209030105010503010501030206030403030207030302040504020a0201020702010207050102010501060507020402030402030304050405040302060103030201050601020303010303050301030305030901060302040204060201020403020301050105040204030203030403020105030702010207050102030103030305010302010206060102010501030302030301050103020702010201020403020301020301030302010203010302010201 207
    0x91500b000380480303041700d8159000d44840c0c0c9543c2c3e4118041c01001d00190360541d00c41a40c41d000380e405000901c0103502c41d4000581c2c41c203150042c9400d440050b404a4070a924010040000d601d903d8101e83d842541441d00507030f564501e14041e0020301403034104070780140c400304001c210b40350154000d00c58607000341c00325180c89603142c004a0a840c024043c450009005003ca0001410320f134000d560090320080549040c25143c2010504440046400380c00690142004105040d0203209147d0010300a2000d1071031036056403805401d600c018800102040000070024201d90000c1d440038024523402002555125a6100c0c024040e402030b0009070701c40d51a000c0005458a05842120b0072640d020300038509280c59600151150707040100b0300000d5540070041c11000480030700c0110f001c2c5120340c80000d07035541503000080c50060020102c40c10340e8034010040c030210350008144c0e41140d0b400d01e005039407942c0c20310040313029015a0340020341660002c0008000c01d40c040d0051030513a4802c1e0300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 2508 1250 1258 1277
    0xb030103020405090d020304060302070303060302030102030703020301030b010602030304020108040201080403020c09040501020301080106050102010603050705010503040201020304030b0108010903030605010201020307080406050601020309030303040501060501020c0102030a0503010302010302070204020403020306040606030201020105060301020403020102070509040303110301060201020301030201 173
    0x4a194031241740c1c50420001d41e104120400200340690003400401d0f0090800150003a0b8a0700443e00ba80c1c070440f90000026800001401080b02d6070014a024040c2071000f54150b1900f980080c02241c0040c0c03000e4107001d00b040001d800c0502c20009003a8a810140c40d5032960b083c03501e8500d010b50428001d1204550070483d02240c00e5205114010031a6080b000a1058601e48401510700b50301c0034000381c0c1180010440170010504410700d15000301500400060745101c00c2c1401012108550030550442e4010014001c50941c0000c001c1e030465008600001c56898110044c0d2452094a048980500021080100740101940300c02c003224408e07000d6841c440720a03001240c507480398107004004528144010700255101e035002e440d0b030610191006180503203c0d000030349072110488044400365143c00060086507420700556400c00001d4000354281411540042e444842c64002c2a024001040015007454840c1e007099445141d11b02989941b56101c0100a010354000d00069010905000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 3758 1250 2508 2521
    0x501030b030304050402030702010608030304030203070501050601050301030201050306040b0102010204080a03080108010501060206010302030303010e060102010b040204030602030601020d0801050a0302060306040207020405010e01030302070605040303050409020304030207080102030106050702040501050301020403020102030304020105070602040801060b030103020405 160
    0x520103203594000c01940c502400c00c0c00b000000d4101415220840d96500700106138901c0800c01140100d020307400449d19810b02d40b918600351100140407a04005042c0010401030740c200302503a81103041140c01186404d61000100d00a00481e4803036066403242c0740440042c95084140d850507141400000c3c4956030726200142d0b03880c2002c1c40300a405034010001080168060340c821504540140b001040860b00b0310001002e98200e50410f1724096400410300c4819038040108a0f100205810289072540c07414000502d04580b0b0720019004100001c0050102c0c0d45a60454801c00d0340140100143d58545007120094002404110701511a901c40401c0450040055808883c4c0c99901c5d603140a082100e43e0010f5000984114150310804901007110002800614042c1005a40302620f50400d401003200307071401a0301907070083e48100000c4c07000d80d03404412203501580a003091070ba910701625000000307125a0380324071403552030a00081901c2e00e01d0401141240e00848050160703481c0c14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 5008 1250 3758 3761
    0x4060801050103020303070201050304030201060503070603050f07020601030201020c040902030109060603050303010302010809030304080306010c0201020307050109030302030901060603090503040501050f0403050105010305010501050103050c090102070302010806030106030803010b030103030201060b0a02060103020103020904020705010207050109030207050103 157
    0x20f00010354107600c144510f10041d840740e001164018400d10002c00e50540d00c00109180191a400030004a5158020468114041e902d01070f404038880c402001c0d80e515580010f9120a0302c40200c070701440c1c49a0300c510a40d1825000b400b90140e11403000c019043c0da034189035440783c0081c00101d0004a584c00429911180007094900854000c2209880d45e100c0c2c5005444030104004103e040d40402e0100d040480e0080c840d840d0414040d882c09682ca181031110242152071940086c2c041c10b15003040c103400f048001059601382d0703000707003411a6540c01c0c1003807905083c022603000418560030100080100708040d080b190482e102070b01c080c0b29640301c02c018410360b0301070040d0241c0160b00912042001d984120502038100d070300034000048560b1251034001032648241c100d9111107400200402c10158244a0b4400401032180460309041c4c110400075160139040c40701904154021802e010382d6a9154102d82c0c00503400300085660341982d01c0e115010b0f200c0200d00358058040d034140050254004d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 6258 1250 5008 5011
    0x3050106050301030305090402030402010c05060405010504060501050303070302030409020a030e0706020a030801050103020301030206030403030504020f0301020a03050402030705010201020301081005040203030d020301060201090201030b0301020306010203040303030f020705070303080103060c02010209060405040207030e03030301060302090406080105 153
    0x103490351402c11f59503805000094000520981c104140036803140e021807400d100f15030245010742d0005c1030320f2400f030410f0403c4d00d0b03069000714082d40c010414200031a902006035015078080e030601582c0c4001c0203108401811038243c0d05c80740ea000e40760000030b40740d40000750103802a11a0303c60f04503580e41d990064081340024800030b900a41e0810000703000a1003903201980c020310040000780ca100307031940424220b8112414a03004680e071001880f041d80f8041001c00010602413009514543c14040100d4950103121103031922103403204045800c5680070300903035000c3c16543c0000c544940c1e407503100034041d25094405a02007458040c411459040c103008a038494030040c0c0095190510715501140203000c40301b9401d203015400d0101400080701445000000c5010b680e40790619419400c2200807140c44204203025a031040010640c00d0711007009940450f60110780040c0c8032149810162142c00e5946078207685070000100114406400d50301900b4160400c0e201000429225004642201c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 7508 1250 6258 6263
    0x302040303050405010302090103090803090c0901080105060105070f030203040503010207030509040b010306030c0506070206040306020304030302030105010f030204080601030308040201020a0501050108010c02070503010501050306010308090604090203010305010209040f05040209010b030c0405030303010305030403030305010605030103 146
    0xb410403050005500980040c510b0b00c0e0b0602d070008001401c2d84450400760001d540c410741c1ca40000107100c9c3d0502e080540903001d01080c9008100c14104440040d000b4070070a04014001140c400012080c14028026079009040240007075544920f6450010055403100640030311031480d200681d40594400c2c4900d000b600c0c0e0080080b4002428182000320f9030700120022613201c80100400300000e911800918000c600ca074030096265410500050007203854079a40108145c4140420018198005042d50440350036042c00742840d240c41c00103d041540200c00541598200000082c0c03d0005500c0082554072903400d0b50030702c80d120300406017038039020302c1101c0d4158840c40051003c100148000c0618075402045589000c1d503e004880c240d8100340d00c10b0312241d6002c00c03000c00c0e9040c035001e0f0b54220b0136400403c004600c0e04e03600040c41050306002c1c0c08941040440000d0360300d10010100c0e400382c4801001c99440390fa5070316040e6500c0d402404110002070a0030000224580900180c034181da9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 8758 1250 7508 7517
    0x50106020a020904030302030603030403020402040308030601020705010804050a02010503040611030702060103020f01050403050c0603070201020702030a0302010501050906040203070c03030504020103060503070b0301080f0601060203040603090201020307060603030c020f010206070203070204020304020a03020907020601030302060105010302040303 151
    0x1321180c0f003c4000e0341014206641c1404100000401680d1b42c0c0b000300300451160a840c5c1c1c8920303111002904044483c0e20440c1032040d20010800000d10204854a60590909001c4c2c1c90342c03101d0800c0d9009000c2030385e05200b418030020500110b190001032440c103e0b442254801e004c0e96503000111440c0c019840001e0483c0e0000000340c11710715000700070f9a072000240c800141400010340001c2c1c5400c1421400b070740584d5540300113009606018010603407001040c1c07810761442c18140c1c1e0081200d078548001070304055a07030000c6811a0700c241c0000000f820000c04496105032201c041302800d500a02c03a166040c42801c0c0725001c13a420200e100c038103e580e00e401840c1840d140900079006084d1302c0008034110301080140703400151141c4507103000745001c0e680350080e034000c51041c018921090555141035500c4101005189a0b00000b15542d00e03906a0340948c8a45962020501d85da8181d00029848980c0c4408c000003a40d0001d0402c3c100ca00a500b01c1e00c0699075103005404031f00c600c0c0070140c000b4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 10008 1250 8758 8761
    0xb010e0111030904050103080307020606010306030206030406020306010903020306010b04050108060306010302030607120204030605070306030302010b01020105010305030307030b030102070204090501020a080106030603020603040602030702030903060c040503010608010203010e010306050402030f030a020106050103050106020a0209 144
    0x10341c01034018110800c41102680d01d44a0400c000a003100d400344c00461300700c4c1c00441440402ca030b0400400350711080a0a04008450540d0000b034924040104000c105035000000a9410b904c9012980d0085902401300c1e09156110043c403c061f400a000b15030003e030005000034024507001569504881d005805800300d500c810408540000c0560032414005070204400000140e0500c80e06100e0034a540c1c0000b011415460020b00b901c2243c02860304580c1004c00600211320044101c0781c110106080000312206442c000ca030190180c080042d611626042c0800d0501c4419001448001c14940c0c0d001c926a890781d000790101c5156002c00f0350401c106000060015819500440e040129401160f040c403038168006031402c2d10450b0400c1c0c40c0c0d04041070821035400c0902840000d4034004000390709540c1800d8a070f5005100510010300015100d9002c10b095440501c107942800c2c40780030a42e03550714070060f03001c0d010309507520940b40020310300400000c030365101107015540b03030754000c00d42c0300d16 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 11258 1250 10008 10037
    0x6040306020304020d080a0201050105090601020a030206010501050a0c05030403080405010e0306010308030103030503100504050907030203060109020a02030306040207030302040b040e010806010605070201020a02010e040b06070302010504050106080102040303020a06090602040302040501030b04020301060501030b01 137
    0x9400042c4100d802450b45c05d10301e40400c0781c0704082c00070401c0c954000300d40c541c101018030021010145c106415588056072800c0042d8012441c9410340300c1c01c0c6461070f200d02800f0001c82e444000d450018000f070000040c04801c0c4110035005206440081e02e40114407080d550a16035510405d04c805403415a06000500001e0300c50401117404c07002c0803601c61b410301e480354000390403100d00b56401d072505e41c8031180c20001c44c1018010a03006040c000011410001d44101c081d40700d04c40100b149204607400680302c1c0c101801b81e1b041e100904040b942d404e4035135440d00340b0324030301ca5802e00541c0c4252080500004100d4410411100c941d581030b8040d00148140d907006643c907400300c1038202ea00980301d90000030f0b00c0c1c8440010f80030340e038080c1c3d00200d8641000d0900c2230071142d0380d030046000350340100424400301307400240d0b4a400e254010000207456100d030619400034010b6410003540541400000810f200c840300c09140128000c038001c0004035602d000650446203a1100540891000040f09c40c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 12508 1250 11258 11261
    0x605030403030204030803070206040204050601020d0207030b0604020403050105010608040311010204030c03020103020c010b0301020d020a03050105030601030302070303050a020c03010203040303060302011106060108010504020a0c06020a0203040e010b04080303010306020a020307060603050708010b0402030606040306 138
    0xc0203072181c100581019203c1d502c41031560011501900144c0c020b204001c19032900e40203041d000b10081c0040c05084442400081d19035010b8000640380d45101e03030110305c0c1500c89a04807001150844c008001950711120010310f0403074141c0d0306800241808120000d040810710880f0100ca034000c0680c0100303855580103401135081f207029903105568070b40f480d50040c0c8080c002030410003415000140d449032600c0014048420603084140254429001800003a400050900682e901414216100c5c40005012860030f084ad0020380c3d003550011091008041d0103030040301c1500e100340c0b204c80070503035407203d00c030303034801d001c8881c40e001980040040006081c250300510301d1180a1505140e900540e07156207042c0c2c2c0c018601d2078016440060304001d5800082082400f41c503001e103400c0c0c501880c000079142d80740418000504015400120199502d000b001114641a402001841401c1c7e0303a0a0484c0c44152a00c20842a5420881c01d07901c2d0786040e00c00ca034800e24004004a0401382941c45180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 13758 1250 12508 12511
    0x4090201030b03010501060201020301050a08030403080307050708070507060504030303050a0203060108070e010302070206030c0405040605010f020303040204020a03060302030f070303020c010201090203030403060902010302040302120606030106050405090307020904050304090603030302090301050603030408030301060503 140
    0xd0505075169404907481e1000c2c00390b1406880c1c10307000565694074045c28440e941d20960b0099445820500c0144009888807089a411412525119469403600e0070302d40458031601d83c00034140e114031003002a06503005406003088038042d4404101c0f980e5603040f50b000b0b9201c11030f000c03400241c03440001050680200d00210722410b041c54014200015075000c0b9520340d00c01d41d2b84800740307000450100050328203802030303401405007860b012140500e146000fa42da4040988024415030300030440040d418860f602a000642c3c0050403102140101080300f515038000340410b80040c014280d41e0216075005020f144522a03000d0021403a151a6440c1c0340c0003000c0c8407404038109502000000050b07940e40c10480042c2c2c0317804003d04643d0900070101400c442d00c0d40d204a000307030f0070329041002e00403001c420b541c49250150b60a00066a551400741e080d40300d0342e00001900c41c074000e0701100b450b9050380a0f0407074150940c001c10254540e0741c100741da80c3c01148100d1040d07a204100500c50fa82c810350185 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 15008 1250 13758 13763
    0xb07020f070603020405030d03020405010804060203040807020402040303030203040302070807060207030201030e010e0102030103030207080705090601050304020402030601090b030702010905060f01030b07050a0207030203120a02010507030902090105010f020f01050403020109020102070905010b04050409 132
    0x4540841400121a082100c20b50110300002d4011600b8031503841e0600c001500c90b85075013001c600e40780c506400038240d40c0d40107001800181c0e0100c009014001c0b10720842d030205a0007401151345a072280b40250007900300b500d0590040c4105036022551940c001014816500550001c041aa2440d0b004401602c007a042202c2d0300c0d502c9001e0030421000034000346001c0d522a4020f8400142410340682c50040141e001c9445440141c05121a42c0d0f00901140d4115805840150360380d9510030040e5a0341c01e0a512654807000300104004d1081c0d419809014058071440c207544050b1074010f508049004280805006002c0308800701e2a0740340500020f28103000d150050320b0400d1388c3c0750000380c184114880555081c0200042c00f24801e40e081c0b14440e071106003400c2c100900202d680200300d02e0310f814003405050101c00070302101240d000b080118071102484000303010f6843d00703180003401b80c0f0313640304101c0c0944624440461022400c0c00b40e103042e601320f0300409003001d01c0c1c0420400640719a0006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 16258 1250 15008 15013
    0x307090e030702090103030c02010215010608040303020702010201020c0d03050901060b070203030306010302091203040303030207030306050102010216020402030601020106050603090106050405070807020a03030504020607060504030206010509010503030405010503010302090403050903030706060501030507030504030206040b0702 143
    0x380c070051301c540b007015000390f002c3c0c1c64030b200d0180c1500019007044012114a00700742c2d007020060240a410940458001c0c1c0c0514005840ba40c551005030700a11a000d020020f600c41c1c0703401e04501c182d25400c80c521801c1804000d210a075694245001c1a000c0c2c3c1000a40c5078205000180d0203510960180881c0c0c14001e0143d0340c4402215040303030540c1e110b90002e4001907000101082899054041e0100a1100303100841c40c249c81070b1040c3d92078050b17002009208a40000125206a100350000000703001b00802d1581d403810401c010328028115407064034081c0c2e04010009010601516017a4400c2d04141c001d428542c0d0140c1e002c80080c41c000f0703c01c9a210b00c0900480c1e0102c0c280e440b88a210714400d4004240f5941040100710400d14140d00651180c2e0081105000999020003980d0440364140c8509a0035102d034503065550340228010389405203c04202c14003800002c0d049101103405c203803401c01441d100c001e000c80c10780d1800c40d0003401581c1704101180c0000c0a5020482d40403886105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 17508 1250 16258 16267
    0x9060a05060301030303020903060601080402010203090405040303020903011109040b010206010308040b0703050403080c0303040201030509030301080a030302030901060302040e060103060c0c020603060d020301090602030108010606020f0303040309050d0303020c010207030302030f06030106050307090e03 132
    0x550350b9002a0001c0e8006940403507540014201080810b40085090900d426075161690001f5524826030700501c0c016601d030404102050700a80540380700480040c0240010f060305580d5006d0350700400b602a1084c0c1c18030f42e0441140d4004900b2606981e042070000d4545070070101c1e280b8840d03000c10341c118100102000000007256042003d0903641c01d614000d95902d0a00340001415940302a1210200f50401c03c01040b59000004120503a180e1504000da182d82c0e481d42240c3c0141740690029400c142010515a100100070039900e05885c801c040401030602942411a551401032100a400140c01c10100303c0c5440e02c0c24523510300301c1c40100041b0784840d10f584d9071416038000ba0b200c018030b69140e060600c82c0d1030b0140441404040260011030a52500b03440052410b4214800c05010700403514220080c18801d40442e600c0c1e4008800a564031105490300178000d500c00c55214076900c41ca20042100d500d01809450100e46008008059103803c0818683c001c2001c4500f86165200402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 18758 1250 17508 17519
    0x120302030708040306060306050604050c0a0c03020f06010801020705060a020304020303070602090402070606080102030601090602010902030303060405060a0305010203010b04060801050102010e0c01030203060109050301050103060509060601050a0801030b0601050408030c010605010f020705010801030209060a 134
    0x2d00400207140314250200f020f0340b8515001d0150303480581068481d50420b02041403454010b0305880c441c205034a00041441007500f01a41003208403400d00342036000f680000710301600150003c2c140d0381d10581c1102c000340c2d541d11a00d03081703000640d4002e6040c7c10803c041c4012a400741c0180803108030040c03006181c04440c0c1d03100d1003240c400b58803100050750044104a072540c0c00c8100342c4000c0c00d1600003032285c018103500080e107910000308241c1c0300f590346a01143c0e444d110280c0c090060755101c07008560b2561140d0110019030014800c040020f114840041071652042c000c05114055030740003440844482c20040d170181d0002800c90b4101719010700000743c141d600b4010940250b0040500185909041c503060b4105080180181e050003010005c03030740c202c0e40c00502141104c2d0001d10024060b124903004941620882e03115640d83e01c008980b5111501d01980041d0850720242c03200d000003074941c602662600311034425240454100d4004001508040200907030000c1d004003d002d1090b100c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 20008 1250 18758 18773
    0x2090301050702010603050106060504030b010b030405010b030604080702030106060504050105030a1a030307030306030501050c030603030301030305030402010201020706020301031407050406080304050603060301020c01090308010911030103020907030902040b0307060e010201060f050a1203020307 129
    0x8507070502c0180e4407036100300240842845600040c0606152880c40d16086032282d40460406200f280c802020010000d0280700081d48080348103403004064845c541050700b407490044c4c0014009078403a500e05080000c84a006100715011030f80180c5440c4d0035541c5003400a8010307d801c0307500108429030400c01281c1545d082c0000d0801720310079240003071560306500f081421038200400c2d180c00e100c0308006000641d0740001c00d89046961610b8403d54940d03480c40100c0c0a8016034500402450000c000401046610012011b6209041d400c944900d640c41d420001138400e24411000203402c204001e00442c1813840045502c01e07000f03000075282030301d021006400c46a013600d050300090007040040c401071006000c4c3d20710002400c280c1714115419900003400741c16000e440b40090659443c03017542103460700c0d000003400b110020305890085903030f44409071005206240640c0194a0803030085a414130801441c019a440946400c2d10142000c1d000914481801025001d502c4148006000500344 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 21258 1250 20008 20011
    0x1020f03040b0a030509010204050303040302090703060b03010e0402010201050901090206040504090201050403080414010908010603020102060601050706090b01060806030f060103050606010c02011101050a020403020a05010203030403020d050904060801060909030206060102070303020303060904060209030105 134
    0x10303106240e912030364000004c04594001d0104842d907401007204101903074001080d07a041e41e804132810203070b40d2076201c010382c020300895001c000c03603000202c00004d4041d0305000051059000303800034001d0742e030b07039903800c0c3d0803a00b0048000b98000340038070052100f824960b2114042a106042c030900d0b242c2c481c1c0b6103901c80e030007039405004141c03500b9002c800c0f9941d1100b500c00c0209443c6000784842c42c11130f030007c0d444400007441581000070106a030028004150451015240c11200359500ca58450034010202c62089503860701034420381d00306000da964001100c41c1201e802c07201030162520f90100458024113805c1c026130401c1803100d00e811009100f80310f050b010b1007180f1401652071f495031041c4040002c0d958002815504140104408a9000301e0041440c13545032500c141e80e4401d40740060010901038108505541c03078030002007061400c030750241e0200c900075002c680141c2d540d031004a0b603c84003400010010780050010801034288140742c80c0d04070388035000240c2400070380b84c082803c4500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 22508 1250 21258 21269
    0x80103140102090301050a05090106080303040c0603050601090312020604020102010606091202090601020307020306010801060303020606010302070503030708090304090906050402040501090207020607030503060105070609050606010f02010501050105040302010e030102070203010203071107060302030402010f03090201020f0304 142
    0xb034880c107005275a40d09110340c00052042401940c11480c05403101804c3d20107504c549401d043d01e1f0000111941e201d882c21a000c0d59100c0e900f111034240f903040007035540f07608841c205d000d980790503c00301c0c18900031b075114802c0f186285540704922a255003401040b981c043d1003207041d440244900401a902400442d010b0120b03e00002070803465030a000749041e03806042c01c2c0c103145c030412070360002c18004030449a20002600f464102c1303171981402d0078950b1041d070780922a450b03c0d06540008020881e080309000e40e0003110309001360303601c0e0400a0124031a041c8025803050003003206a00007402840510340c0034105041450401e5505d4640b10141c86603010110303041d800180800c0701135030300123100315210002440200b0a641c1060b00180141c82503000290520042c2c1c041c0382c4d02664250100c40300c3d194040c00035503ca051080004e005c840e031a40001d01d25015011011440900c01d100b83c030320a640580d10b02c210a411443c043d4000c4c40c900c8816170442c003462034003120202c01003000340000d25 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 23758 1250 22508 22511
    0x80303040302010b0f01050301030f020102070302030607020102040501030b060c07060807090e010609030303050702010605090c090301020408030408060709060305040201020601050103020304050a050109030807030c030501031203020a02030409050106030204050103060509040201080103140102090301050a 132
    0x5001d107002802c5400900442d440b441c044242e015080c1d0b800b5041d6410340b03901440700b14084185d400141d140582d1980000d525100f20340411420300d40c103401800480e0402c0e00c00788071400c0a4030401c0020300500381c441c901c66000316804c0222601c2000d01607042071140c144480745035101c0c4000d4401c24800d0b04070340c0c04034010300020010145d0601c1420b500c544588020000300c0d007400005031346003d002d0180c001501d000304005141d560298112001070480c5001c0ba5503e0f640c0b4281d075502c0c1c04046540320b001c40c40020340001c100e4003d0060600c1280d05a0240800781c1c00c010040d0001c0d000500243c6003445500111030020300244540700e0614006c0d11050000d00d01841c00a00b030300d490308248001c05003480c0c010400542c1020090701e05599030b09000d40c44d6041042d040b03186008a03440001c440307051600008916805500401c145ea800303a81c10302c1216100e4090210024017528020b00041c1440010808110f10b00e40701004004040000341ca006101c90003e0b09641e01602e1184095 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 25008 1250 23758 23761
    0x80a0201090c0501030207050a0201050906090402030a06050306070207080c0603040303060e0406090b0a0207030504050904020d020901030308060301060b0406120f020405030a0308010509070206040201020303040303050603070302060304060203070e060301050303040302060c010204030606080303 128
    0xb803005944000d00b424030f019494842c907a0b8442da00c80c0341c030b400001d0510501264001003a5504800d60382d400c140034104545900d001884c19010b4040e5100c2e03e07010f8094000403d80c45440854003109480d01b410042c030345000542c00340701c555840100160105070740c445c0045154280201014011070180070045180c5102c1d0408a60740c07540500b40c481c01c1d500c10003241000a42007410359003254011924000d840d039950001c198a401d1112000350702c509580d00107c10180c00408450040790240c0081240a0320340f01207071020f200711f000389800f0801d500d01c1d401c691070058105400c3e05070b29220140c1425900d02c0030926104684404801180b06540107005500304000702c1603200315a4070007003d4134101500081d440b07100181000d02016140d2001032942d4804005a0005550180c12036603070313103800d050041c001d40003510303e9030002e03014803922825807030480180d0381a904024051071529240d0750030020a41d018110000f4155028480040440c0091107694018540e650103541c0d03a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 26258 1250 25008 25013
    0x20d0201050106050903070303030504060b03010204080f06060402070201080609040203010603050708030901030b0901030b0402060304080705070303050702030606030106030201080a02071a010303020304080601090903050403020906010201140403020304050f0306010305030a030203070507080a020109 130
    0x1e5440503008103003042014440c162aa1350700041040490b81c05040010f130b20f4680c3d044c140040d0680c002183d41541c0001400a000c920006408410358644400c0c0c50264441c04100300680c45100c0703010b40010b4161004c202d031b41c038106003110342144c8000e00001c0c00320750304c4e5102402c0641c00ea1000a5a8001240041c807558050140300c01c05c4000316162987c941c11655504c10054000e40081d000e0200400003804115101045401035a001000c945080b6500d04e030080090380b0003403049003c2e0050002088083c1030500400054a07416100e080e41da54880304000000d40040c401078030b10440c0c0d0303d500c4c0400c0c20008a818003840c060b5001e10b54450402c81c1e224900366041c1c0c440800c0340d242824100100350b004051728162903040700d04c01c0035a107031000100d01408903000c0c08500824030809100402d81c001000b081241c10545404040540000400d031701d4004c01d11002e08590810003200d03660921a5005540c070010a0800b40c2c10800181c44141c6160400c402d850051307075444899805 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 27508 1250 26258 26261
    0x10501090b03010b040603020901050f030c040f08010203060306010e0703061208090102060702030301080607030903030b0301020a03090501050108010605030604060903090b030103030201050103030201060b0304030f03090602090d060204050a0506030403050403030807050409020406020d0201 126
    0x64408034038010b1440d454807040340c04901c2140304002c00c141d40807500100d103138810021208110001c02c55107440e4107000c042081c281e4054840c0711495a00300c0d0000564403810700a030384c03007104001d000c1c00e00740e840d11040c226003640c02481c030020944d0b104004100d0028000c8d1300007150f4081c507400364846403030600281c82e1804c09041c24056510074401040707038440c0001d42c1c50b4008101c0ca0302242c1c400d07403440c0640c0981030340d041c26070b450350004c00d102540b036901da030006403402e014000900059981e076110500702c07101402030ba0b405400c01c0b80028003049542c0c02801c040c9100c4e00d0106a4150f03207501004c1282c10a8100701e006035100d5004005041d8240039034400303007a01000083c518109560058040f03a50700e44400e0034545c0341d4040b40709100742a030544102403005403510444c00c003589880c3c1c0081d4014041c29201d40c6020780e0115a40c1400030583c0e200b00d605480d80c80c90242140c505841800e00140101c04014080101064250050014000820f807a400a151803154400083d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 28758 1250 27508 27527
    0x2090603010b0306040305090301020403060203010602030306030106050103020a020703080708040302090103050312010f0501050403020118050405090109060e0601050105030606030a02040902070803040302010b0108040510020a020304030203010603030206010302010210020301080a030807030e010f05010501 133
    0x18460380c107002d84840180d8001c101c65812681c54288180c0c2e441c8404042400b81c040e590024050030310100c000140981c002c4010341c4650300440c001c1008030b48a5005508a00070b9101420044e800418144002803924005003c0300d4060704005091980d65800243d8080d0700340c004603519040402d2030b650030050094061701400c51b081c0338034026402d0100081540c011071101a04001c4a0480c0301031001ca2920114041c05020f03100388404d00d400d10305070340680848442107406600d07061004041c1880812528140c4805035110b1303107151901020814280c0000d0032407100240d0070080012100c10903c01090b08500c19a10b01d41c40386010308000e0b00b11501860b4030745c18410b802c4100400540017250407450741c0c03110040143c40e2519100c041b4a03601607900000e415600c2d0a001000341900050030904980c0300742c4c2100c040071505074191040e0300083c13203120016070128580100082c0070f003154540c011080c0c5000181c0d0418003000c0360a60700740d070380c0300e00e4010b540c1c00050115590155906 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 30008 1250 28758 28771
    0x3010906060908010b030c060a030212010303020607020708070e0103060903110601030b0402090606030402010f03020d09050a050304030605010501020a08040303080403050909040605060103050603030703050301030b0c07020d03020102040f090608030306040b04020408030a0203070209 123
    0x81100805c4040400e0715540078404043c8140e10011b40d81d9a2180682c2c141e170381c2540c4214000c01150384030301d4003955604068481c40b02610500900240381e01001520790160f41607047d40101991866407207002400801d0f0040b4144040d080c8422180c1004020707860007140188221001401d080c010b11080c001d026050600500d010401c000160742c0000400a041e0500e00c1c00503941c880108241000300801a8000d241c0d000c0c401d0740c841803200c00000f07030003500e0050408000c2641d0344c40c01603988894529004240480900c000c202003030281c613503164030038040d0170302c3d80c0781100c840001903401104450486100d070b40c0d0418446196454813403554800c60036801140341540e907440c0600140014800240141c00180000b401001c5139403d8804a940c06410704040080c6450043d020390042c1c080c1d00498002d0320000501d2500c9402031801b241d10328009540f0795201d140c1484050400180000d4105400300700000d4100810401429048020f901941e111a040d03c1040000640507011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 31258 1250 30008 30011
    0x30204030201050304020d02030102090301020408010f0501050306060307030f03030b0402030a090605010503010501050604030b0405030f0703020304060305060303031308090102070506040602010b010909020c06010b0a0309020303070b0105030609060403050306040b010207030203030301090606090801 130
    0x10320050340c00a044941080d0101c82c0180c0100240c40000c0c06482003100d5aa01540081400254000150094034400b03003a590280043d030707211400d050f074030002240d45540c1540a200c041000c101320300c0201d0203603030080c90041030484112002c501a0f2b801601c283c030400d59a40f064806226091080c1405028100e000380465498100062018099400041c0c4840c0a4a001c0780030410204110307106801055495501d42c10942000b0b500c82c0c00611a11002c0703400c04000407014940401113901c1501c1c0800c41003a10842910381d0300b29500100011415031195000103c0d00e0356928019000520f402c0c0c0c00410300307485078000100034804a41c050f10426006004100d250440812010b040da010080b801c0d407520040f01046001d024001c1d4007a40502000888030305100c0c0b4034602c181078035070035001c550382c5807280b8030307000e0ba9100111006800580203102240142c90a90042208490140304517200c140d00c90300080e0542c0e0003030b0300c81c02186540300810000c0365000310400e4001c00001c0c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 32508 1250 31258 31267
    0x2010c02030306060c0106030501050a020301030203060702010603020112020307020a05060103050708010b010905030304030201030b0109030605040503190804050705010f09030b010905060102010b060a02030403080a030905030a0201050702010b04020424020102040b0a02030301060f0302 124
    0x3955070701010f88034502c00d14003c50003136092803095000304000c5d40c00070001d002c14100046404029442808103a0090280a000403481d9005001d40000c0f42e80c107a541c3c00554201d42400c100030b41029102d05c0031805002c04810206030104401e074040c41c0640c1c0981300c0c3c14a85886282100d00c1d480a0906010a8100070402658048161002c50b502800e0204030303144842e004955000c0c0329040181590b10344400d0106100300000502004050304202c45101c580d0700c00192040305017180c008000d46c0c0700620070b22555100d207180c000011001d08103060400e03100c0e681c08940610980042e90003565450400c62590303170900803001000e00a0f25440d180080400000b900c0c2e20a501000d8402c2400040c0780c2541442a8080e03150280c120007507a031a2040160001e0180c10141d80c208015800c1c000151403030301d0103100b2141110684e075200555180428041003600041032219001d55609000000e5203608203001070600c08007e42c0510354070742c18081c02507d104400546401014818070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 33758 1250 32508 32531
    0x90201050301050904050c1003020403020102060105010302040308070204090503040504020f0702030607090302010206010603050601140c0604020405010905010f030308040501090206040305070303020601060801030803010b090d0203010e0102040302040b0f0102030703110307060501030804030203010c0201 132
    0xe0031a419070780e0542d1189a84d40d00c13030a200c0d24101a121500da0040000581c110701d103503160f4054400d50740700b41e003651f00507641c030300044084e0701903400040d020070020440d000041c41e01d03030b1288085a101340e003a41d040c13a50720000201240c1103100b1007a48000001108000c510b000c0c08102e80c01a400e0501000403425500000e5440005000f64814140c0d50780125070350380c1c01400c500d2858070b88171580c9641c41c595442c201c1e8603000c041d1000c90042e8100310020039845c0080c0513090680e84009202984076245880848410b040548155143c0d503a4000c04809a200c2e400140041c501880041c4207803031940ca402450a07805a01020822a0640061000034440421241140d681c2a4040e4480e45c019001809111000303030000e40c150329190190391131800c19009403045070f001716820000b8084100c24050700d0f404801e021070050f0410005040001d010f19000204014200101c9003007904540c0c3e500100c840c20303002540c0c00031000c6800c0003180f509000c1d81c14541c2451000b03210210018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 35008 1250 33758 33767
    0x3010c0215090106050a03080703030b0102010b060d0902010504050409050304030308010909030206010311030309030105010602060106090504090b06010305070504030501020705030301030b0702010e06060105030601021f02090301060b0f030a020304060902090403030b0108010603090201 124
    0x20401120307800280c50108030300407001d40004002d07060040031060920341d680b4101d617840d489803004402190a001049d8244d41c01882040d10a00020741410701e801c221040c0a0020845c1c3d0030b080f410302805000105183d1076512900d000c641c4514000c5030740d2411410301030300e100c5d0f05030700c40c101c2241810503410010794080b8040cbe04490740180e07200608400c040000c0c1c154010380703240359015841d0000002c1c0740d0394002412412500142c403151030280d21441400180c4940a0f070203402100c80d5030101d8290352007540003990141141c40c0c000e04140e100e82e20036099a02001050343d90b40e001000610610181825203a08401d40380002c0000383c0d40d14000e6a140e00f0010001c5050102c0880042e1241c2d0003030261b000504400706521410b02d000c3c482039402500704043c105c1c0a036182c61408201f8610100803178807050007500800f410340c2c1d580d070b0b0801c01a60005100301c0c1c2e240d44501012005890b6091840c1c0194481d0310081400c1100200041083c0c1c2c05901c10030806042c5180b13200583d030007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 36258 1250 35008 35023
    0x3080403060506060409020d0507030b0105070503030c0a020102040305030403060905060601090503060601030b0301020d06030308011a031b0703020109020d03020102030601080f060105070206030406090507060203030a05010605030c030a0f060302040606030204050301060503010c02 122
    0x744085025902c200c00a00640a1984200340c0580001110710440c541588160311500e050384040010070384030001101d582c02100782c01009644204003103414014001b000e08000082d0b840054034240d02ca40c5c2d41803c40c0c02a0780100c0d00940c031100300d40c0c100038090101c80d511003000e10301200314918040c002039480b031020f00b445040c99518441805145c0b800e4040316080100e000040c00b2465a0b4178000301591401d100c2d000000038207000c0108054594021a40078442c03004008403403888800848c0300661000308100d00f9503507200408401070f180c0c200031350b11282c040d03000140c0b41e1501000140455a0007000905242100010042c1c80da07042025202010780640d0819226a1146000001401c18400180141c410080001400ca1340000198805e000c14202404641da0300e00b000d80d00c074001901c003407601c0c1005000042051011b41d000c0361400f020030a005c6165a81d030340120b0203c940d40e1300310200081e000182408941403d00440f801008c4c1a0000c102c500c500c120001e448409 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 37508 1250 36258 36263
    0x504060302030402030a080309070609050301020901080402010f020a050a030801050405060a08030a050d020405090103050309030d020601030203060106050307050706060801020301060306050904020603040303090503040b04060206040204050601020d02070302010503091603050a05010b03030403080403 130
    0x7404004501951020020020050f5201c2c458030b0f0340e410100c4201c0e40e0340e440c9100e280001502c604011400d800e060080e0703456548181c40b148001e4941d9030040d110465030074017440442c4141c2a4180225a04005541c41c81e800782c0c4504009505200610042d075900508141c026062003004205803080042120038541861401c0d0f5156a00039030030002a100c0c1d5802164004240c00c004024841d0101c02400c14072012021a8540340c01c055050340c0341d520034071000e58190040b40041010764010b100440d448199840d10601d0900da55951104807800c5401c00c0c02284e50210040c810740707415206290240c4012101118280307460782c001f0307141c0e2000a00044c2015210004401048802c0003aa0f024041c14100c054031039864820080d5a000200c2c1d0a0713109a040c000415807a500200e44078102100700c0e400b0708221400c5400541e80c075400038000c459180f02d080040641030b101000008051840ba50151003881c20504006095a0003d2031003403103034000700410070000b071099040354200ca6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 38758 1250 37508 37511
    0x6090604080901050403050102040308030108010605090103050c01030207151401030201081308030a09020103020702060304060b01030609020403030507020f030f070803040e070201020a0203031605040504050403080901060801110f0903010e03040305070608010503010203060105040603 123
    0x10b0010040303036140225031004000b0740c004500070080101d0000a07606075010705000f040829554010030a40c1d43c0c0c28400a403040d004428400400d51080d001080a1402904052903010001100c002118086001540500d100c0e2006100310340e4080c50f5650080e80100025a001400c0c0c0c5078907000344002352800e40d80913500e69556085900035010340307070b046400403c2c1c507486e40761508284024004036040d01d4002440c00300003041483c4140b0a440c2600e40585d00d0318240300403035007413222084090045c00e41c18030031030b001161030600070020072001d401210043c0d51150314141070781c0c2039810090b00c1d4005590050146030348499000042d40d41c40414260030030280e072030303160301a10148619080303103170050705140030030080c19008030400d4000c054000003088059a1170760030b02d003220701d02e4822208003c402c004114106001078043e1014030001000051a000603040461445d84158400c851540001e0760400c851a00020440d00405c02a002540b4503d0080e0008000348200c0c000e017000e16 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 40008 1250 38758 38767
    0x10309020a0302040908040e0702030403030503010501030b040605040608030405030c0402040e0402060d060306050a05010302130504020a0506070501020408010903020604150501030201050405040509010209030703030203040510020109020d080306030a05010207060903030506030609060408 125
    0x1581d5812000c0025034010300200700c0889141420402c03640103016284603003600b1004150319520010803141180e406680356803c0d030b403c000c0110042c1200110007944952a0031010402e90f5541c898600104500c03c0295503a5180105060402c1c801400b030340d100d9441407000f0820b40c0450800158030503812214a956900341c6006c0500a01031500302918852800080010741c124540c000c070b050328000c0302c40100c003541008010061304d100311802074000d1b0f20b5407400c00c400e00740200540006031040700058240340e2651001030031910f0500042d0016440801030105101c00010079411020b111031040c80700390f04540004e40248140d1040354010743d6903000043e0304007020350640702400401401d079001c0070f40c0c078280290344e6041400380a1044001e0415460380030700520443c2c3c0007079405800f20903038014a4488040ca078000030641a05805840080c00000b0028401002258800c00c0c000a9080b101d0034001c04170b500007040e080c020340c090030074058401c400142096110354811001d9945 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 41258 1250 40008 40013
    0x90603030705010203040501060302010806030105070210020a030204080303090a06060503030c030702060702010306030203060708040204060f0501021b010509060304030908060105060403030206060d020102120d0203041b03030c060203090a0206040305010b0102060603030c0c010309 122
    0x354824050098401d510101c2030001b0410190010700c2280d000742d0317514800c0d445003800c2500b05ca00a440d40c40c0503030b022400045043d42241c0240ca10560f06080042c1401d81d1041c0c054203507481104c6c182e6040c1c001483c0101040070038484c04010303110540080d41000b6081510540c1c91055074000b034442c2074041114811a0321070342044025560280a031002410000d130003401c010000d4504030302c0780d410300e00085400c01d1a11482e50449005900030300c0d404808503452140080c2c00e0114904000b0200312500668450750000c5000d503100307030b80d500300251030412118145007042e0010fa00c5141c0c1080108007299000501c6a0400011103000380c100d001840141c0ca0241140c2104100f100d0100b051070b1600d01e903501851080340100740b4451004410f01e80180e01903403502000300410300c8840034201044031a40695400740101084803502d6003c1e80004950350860307032040396070f0380d16690200a00d50741440703001d030003083c150011400c004868505507203030b203102c5510504250351812310005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 42508 1250 41258 41263
    0x301060c0c0504020703020102030403020c010203030603070506030408040305010c09060201060602030301050609040f0603050105090a02010207080106050102030307080403020304080601030f02040c0305010b0405100306050402030703020301030302070f03020901030308060607050f01060501030c03050411090603 135
    0xb09401042155140c2d028034019000c0e40084400380c01500481c03036849601d5001000f16885200018050705000e0305060802409410203441034803045c4040c800480041c1003403003081c040c200039480380c602d03080c90312030028203480751500f0000464005000411041d00c03940140c8181010848011840510f8080b80c40000c04850b800a0015802c0c48140040240b010070a462894003e900380c40b01c040d00e8090746420380d08280f040b5401030380f003080010b0110380b1400f902c0c1e800900c01e1054a1030f15a8651191f480c201082c2c00c140c07040c08aa40094003146454030a4061042113130405105640c90303da0344000c14000ca01c90f06020711010410300d40e13a04d100398000c8003c0d01c0020011510780c00c1040c1c0080094000b40000c0b4098400ca80d00401d00d0442659154101d990051040016a080d079074200c801d1003015000580244041c0b0464002070400d00154248255000000415605e06000102030301d000c800d048003418030f86030901010400c1e209621410b80416941c4010359103403607010a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 43758 1250 42508 42533
    0x20102010209031002030a0b040501080307020105030601020f010c0906030c03050708040201031e0501030b0406050c07080306060904090807050d020601060903050705060304050304030b01120203060105040c02030703080403050405030102040303050903010f0b060301060c 117
    0x9503d0700800307144502841e001d80c0514040e00301601d04100005013102844100da90a0082c2c030995482405420015031092000710f41c001c40600c1610407481501d40c0c40d0b429901c2003125030000c194200030500c0340c0c560520a40c00b15221703520301400103081940b00901507000260010f810151514814854032007001e021040760000480308006640c4c1d1790604000710701c0142c50407180a0b0915000c6810303408920705a036102c4c1d411003074880c919294130f800c210345903004040007908541c89c0e580c0300c0045128200604000c1d4010030180141841c01c4000a061001c140c0114043c401240340600c0401d400080c08010380b1410340300155a0340791420b01500c0c0d03000d981e00042541c40d0900021555012011240003247d1081d13007200c1159880700100030650b80075100000042c2c0c018032110b80803078801d600443d003050090505614140d1102c0c0481d09a80c416001600814000141c42c0303100e040900c15610710b00e22a40003088017841c018009203107840103120f96020030002820190a01129043e02c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 45008 1250 43758 43777
    0x11203080414030a020604020307060504080304060804020a05060406020109060609050106020d030203040501020f040807030302010606030203040f02100e03010507031d06010302010203040e070201060504060e0103020405060108060306060103020a0302070203010504050a0b010b071a040201020102 128
    0x104d032101800e40000f540d40b40103c0d403c90190040200004815008106403070503a0355407009182031505051045a00510080040e42d010700e0442d03000581d0b444007030081c0b01500f4240d001280302042410044241c1d4a0340e807040e2940352030309004006455012034000e680c9001c0740b41c0581e40761038a050690290040310240d8401c44400500020b294000054503011240f083c0c00030301042c0e9940300154120301045070094401c0f0303d941c803641e0061903d1988070a103000e00741080c801400050000c00e085400032160031010039070360a1001c51581d0b40d200d0040c03020341a940102003075811503000035102c2c0030714403440c134450301d200c4045817009000390004009044041c00402000c0d0781c440d05a0300b0f0300c10a00c400c0e4001d030714180101e0540e5104075501c600c038410280061502c1e07150180114000c1d440503100b4010503500384600801a5000c0c001d4601460281e401082d442c81141000c0e006d06a06901c42d90300d0030810803106001881c58602004805d2410112407155070f10703400140d000e4810301108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 46258 1250 45008 45013
    0xb0301050c04050a06020105090303040f020301090605010b031005040603020319030903050604030201021306020303070f0503070203040905090705010906020604050a0303051503030705070608090102040501050702040902060712030501090b01030203011203080414 114
    0x10410942120000b610407180201c80b509581513488100341d088407400c0e180c9440a8008000140100310060703044482c051014000080a00ca962a19000c03170340d00781c002d841e40400000030305c049200c0381c041701800b8290072542080441d203103500103070756035076a0100000d1440c641200c01050602030510780000b10781050550340d5a2401e450b000f4003d5000000e0021058030300780300401c09510000643c4c0c410103040e20b0382c0f011110340400c152102e40006181c5c40461100304230100f40704005000b114000d007081e8000f4170300346040000160400c0c80c2e40e0000c008542c0050b0410010a200285070398140d0b8140c20009260340326500c0501c400101c5956503034140c0303c0090040200400000c140d01112420f40d03c0e40e11a032900e0800c1d5090340304500c030b0035000980c24400c0d20098034066000c105600e10040446117002c2003560740019001c0c45c0740300400442e41c0c0300010404140c0c2400b0700724010809127811890b45d030411065505165054201404001c04080000c0812031404245980351641c0404c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 47508 1250 46258 46261
    0x30403030203100905060105090103090501060b0403030203040509070807090e060102030403020409030e0103050c0a02120c070906060503040b010501030212010603020a020a06020301080703020307090501080304050d06020405060307030203010e06090f0106050901030b030105 119
    0x100500a540305454903c18862101d1000403180364500c107150094205a541c24030b44202000118040e200c5040b003034505559400c8002090f1005900500045209802450700c6600d40700030000101c0c1c0c018900d40c01d21082500704021103074446541d505581071202c408010791140340c0100c1c03442c0507030f0300001d400516144030007080c0354011092161207102643e0500c126610002400d81d1409600c69075005a07201004409040003032030080c0620b24008000ca4a82c15a03a20803034043d0b40466008802103440001407105020110032090301400003803d007507182c142103400d602c0b41c1080510640c0e0816501144100707041c0d2090103202442500104295202c0d42c5904809440f000c9a100c1288039108035200086c0c00760301405040d04948003a0003075820289010f0602210990300c3c1000c503046582040085100d135902400f03180240c94681e00141c1325814011b48241d02e00015100e1071158404004000e80d4a80145140c2e065071032514010343c0340c901f2100113802802848a5843d815402d040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 48758 1250 47508 47513
    0x3010603020309011a01020606010c0204090209040b010303020d03020301030507060c02010507060906020c01060905060604090c02030408030d0501050906030c0a030312020403060204030803040b06060703090501050306011101020a02010501090b01020705030705040506030a05030304 122
    0x40142d402120750100030012141007113400405051604a01805600030747d0003d03c81d58010314444000500181c404910001c00d40e00140ca0000200c0e4203c1c0d091422500500a040d4108101c20646085040842c510f5055484240d50342e040c0b44100c000704011001c1d00411640710700e094443c4a84d201c00c0900c01d030991841c008001e13404c031302018000c640c68500001041071301e0303000d0345004010261440d898181401c40c00e078080d102d02e65000082d44000c20000840316030800080c51045000310b0005015410701040082e944000b8047e288254032810340b4810640d01d44a4031000c4941c1414410141307988030044030040d01440d071000c3c1400d48041030002c140b102d43d000a503c241d108a5014180307596a43c108002c1c2e006124002e400510751003000d00c20755000f03900031504244141003a004000310005031a00fa40e001e40b0810005075118401000200c003603000c0c0320203120b803d00250203203504020110790b0391480c500c996841a80c8030000300700562003d02005604c2600a41569500d18160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 50008 1250 48758 48761
    0x1020705010b0301110702010503010e0703090506040602030601020d050301060807080601020c0303070503130501050301030c0902070204090206030108010b01020c03010c05090108040f0602030103080301060908010204030b0606070302010605030601080a0314090306010501050c010204050603010603 129
    0x14842d4065401d00c5000011314511104030361440340d0503125142182d003880304000c200c000042607402031540e15604240802c0042288030311451090002580d60b140800c002410071503410b006000707204007400103004154100c16159406a100c0ca414240c1740d50750f000403864800e0b95611141c05010028200c0d09000c4040014038a181c0201c128189080d550301c0111241d01c1300b488060300100c8661028440650681c004007200c6000070070101c3c22600d1600000c000f940280c1c408030450b07540b215a0400355805000341442c40800b01c0081000c190075840140c51842440081ba0410482000090030000520068200560400da00719240c5da1030740b80c80401640700703014a401140044000282c422014000c4800b5668030242405180e02c0e0501440b056030440340003141555240c0a011a4546042042030300800d501e00040511b040942009000c504c0c40210000a05d04100700c003000c02e4800080b840e04540d02031901a81d1524181c00c02c500a000e55000180c0c40200000005640d6505 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 51258 1250 50008 50021
    0xa020a0308010506070201020c06030702010b1305010602060f0402090106030b030708010903050405030610060203070609080c060a020a0e030102030f010302060705031201090903030c0203070209040204050a020705010f0203070f09030308010302040504030504080102070501 118
    0x10307480740300d6140d89a404115260081c03400c0240140d01940e540b15050a220000d113811210354000482d00d24a0386c400500e00f002020404e0b13600650340c0004005283e41000100d4219254920000d07ca04154010601c41c0038140281d40c00d050b02d400001199440030050b080040621368020007a450491030020202d82c4075100701c030701c80d11911000c98505031007800500e04860707268000b18940b21081d5a9003026100c03001054a510800b488000f80c1c0181c00d000316441348824480050307a40d5410b0a001d021343c005800514066841442004020601c600700c25046d00d0b0121450358440c46580341440c81c500c200d800492042c2188800040d054cc0380382c10119041e44a501c05001503401207200300d9884c0034800b4041d60110b034000108015040681c0046d8000c0503403030000d8946001c40d110315083d6190341d41243c204035400010409281e510200c108501d50007880c04140161840d20f0003040d649060101070301c034507620310110302018021700c11a4001c00340440290f480346001d01700b25000b0010f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 52508 1250 51258 51263
    0x501060603050610020a15020405030114040605010b04030206070b060301020705030a03090b060105030c0306090702010b0406080304030b010503070501050703050901090e01030b040203070605030903040306020706060902030408030103060605010302030103030c0b06010201060b0a020a 123
    0x1c0201240f2503240c050343d42080300d15650300070411120152608440c5a41c6100f082c5e06c15582000701160b01d8400380100c400c10600005011210300302450300c182220b0701684034050b042403d110500041e5038030750850781c000d504040c002ca107607141e4000090082c0301d981d8004020744400640000c0c0180c040e0025001c0074010490500b095440100544062000701c6022001c50700401c00584949171205903c1d4100709548000240c110054012030111121074000b03480c0f030360020604104001501050b00d01400040d00a4594a4613100000c2d00c40c1c019120010700f070005c04200e80e45580d04c10f4416a0043c04010040e01140d6961b003003d401451050702d0682c002d000f1403802007501402135048034007411102e0300035440c2c51300c1e6464a230003d4210001c1190219180c3d40001684500750001c0c40c0603e0151070400e54a5240d482d1580403912254845030500d80188010000700760008203942c2074642102ca03001407903a441e00100e004100c00c0d042005003c2e8003003500d01c0c660f580043c043c0380071403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 53758 1250 52508 52511
    0x6030b040302070e06010903060c02070302030303010602010b09010b0a020c0d0602090402030a0209030d020705090105010e03010f0204080105060109060206040201050409020f07020904030203030709080106030209010b0a02030c0706050703030501060309030e0402090d02040203040501060603 126
    0x2a180c224240540710221071701400702d810b9507820400910560b0000e00c10035450300c140c641c26038407580020704660080e441100140c0d19055010322074980b0100c2903005120324560180b601c0351840003c2d4031a00101c2806204109004500061114075011a81c2c09600144210f5481c40d14440080c02900314040c15070181c82010828010309000140120658000400f0351940384e203444011a42101d0001a031a0995200c1c02b211501d0703100390016002610000001140510b054000100b00449640c0320b13100315849030084c00b000d030f43c100f0103c809441c2020340240e9600209408a0340074072400e103000f500416120100014154080041e42c01982c065441c0c074030407941c8040103404e031070075400041d42c092040340040044403c500300800b6004e0490040d02d0604807849034540c14140941e02003408140f00140200030503a02d44a454058100c604041120a003d91001404c0190303260441c2d0180c0d40c00074045640380d0741c0c0112006003a60040c015540d83c9170525045002c1c0c480c41c0714410209 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 55008 1250 53758 53773
    0x60203010e06040902030705040b01050d02040909020f06040303080c0304020f03030a080103030809010207020603010902070201020c0a03030801030203010c03020307080402040903050409110c060702060603060a05040c05060c010504030e040606020309010302030a02040906030b040302 123
    0x745084d00403040c0c040c1e0001d0091a1140c102070411000300000c48055060000810060298034803030300140c80148030259002a55661a0040c401c0f214030007c0468800c070420041400040e8000c05296001031007661711640b03a0342c4138400300d56103523110350355641e0510001c00c00b22041b41d48042c0c03041c180c030f20a80c0d40103c10b403a4070741400d090f4001d400000f540940184014400c05410f039014010003401481282c40031501580030840d004120780082e03000030f180704018420350500740181603155140f03140843c518500120018070305007010f040244515192a100c0d02850701c524259800307000504800c00003200701680316038007a40700c041500014050140050442030010640920801e0041c001c2c0a041c1e9813946000c0c000c01000704205c4560540000103c2c0c1038a800c80900508030340c0b100006010304107424003910b100d2080c074202c1c2c0318600b0803000b40043c035408012f0782d090050030300307001d6281c2c0c0b03903c08190003034011904031200b040c2c50004c0000910044120950089010342c00740c4541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 56258 1250 55008 55021
    0x50d0b060f01020705010e01050904020909040506010303030e06010f0303050a090801020309010204090b03030403020102030403030c0f060203070305040302010b0301050105030705100306090507090608010e0609040b0402010201090b1005030705010203030f04080a0504030c03060203010e 124
    0x4e440c0144629400b0070486d034001c0712154068001444000c0005000610705502440020155281503c090f103081c0d0020b0b005104154140c8203109051000400a005540c9010205614801c843c080242002008600c00b02c1e01406078010001500c0d442000303644a10f48058810b0003504039126404005091a4640c65a411301104070f030181c0390103a000d1854642903441c15158200c20040882c5d4899400d081540420010300c0910700501d100d0750045001e08050070000d00303540d40380700e00a1103645824010089660005803200c2196426225a2480c1c651058103400400780380d84203248690410f020045030980c4405660217446581c2c40d8180c4990305d402084444c1038080300c08680000c100b9002c5070200307040e030900507481481480080b498800c45d46c0e820440440950b420310304d0044900007031287d80b03818090440649030278030055045141801014031b2040c1d0150000d0940d0301c00003060001c003882801218060f5400030001c4410a0341c91a080009500901c40d80010f800741e800460031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 57508 1250 56258 56263
    0x10e010c05030a050f070804030503090108010e0702060105040509010905010603050703020406060504060207060302130302030a030305060301050106020109080708030402010c0203030a050309010507030504020d02090601030b0d05010204050301060501020307050303070804050304050d0b060f0102 128
    0x403003a812400075414500c8030300307060307649920402841124050502802001504102c0100007640c0704501940e141c201c0500023611006040c0c001b03000210f2044100b107140d507400a005030440c2c0045a01061316100c00b45903600600c0358910140655080840200a018001840008691013601d0400c0b003190b80d203c0c102c6290045010f0040180c1000b10204812032003038014111100130b558a207a10566a030340000d29010414030228042034458042000c10b00e03082c8a002c3c01880e85000038080030040c1c1d27480411903c1002e400500c00d06000c40807a055900c41c60031512300642c00340031a0790340c560f4520302070284d0304110380d0600366600307060006090354440d0050501855024245e031251980540c20400e080000030401410180e40d0000c46a195440400c3c101203103003e0000103079203d0410051509443c1541c01103030565004014520014000104580e40328250745846440e0380c459242050840c803c541c04a039000380741c4084002840422030049000c1d0f0422201a00b24000703407001a80c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 58758 1250 57508 57527
    0x80403080403080603030409020d0905010b03030903030d0f020c010501060503040501060501020d080402130e0303010603020403020901080102090901050d03030204030602070b07020d020a030801090b030304050a0305010203040b07030204030206040506070204021204030806010e01 121
    0x2000104100302040020f40902203490f00080c1c0203080c0c0b0b00345a1a80414400c0303801040304240256110704003c1d080c0842803107040c00072401030b40a18508410540403981e20310030100c1c0442115a602c0c81c102c05000260b05540316248204001d10a035652802c1c02007507908250b50a03251540f9203980002c1c0c170744c0005810480303d4038a8450141c0f994850f000c01c41d1110f0303102c600100c440e0b12204c048503065030610007035000e00800e0b01c0060703c950030750040c041402c805030040d5401740e104200880c2603540e078208a504468085841030120101403038124068069548020100c0d400803541c0e9003003010145016100c0c0006500300ca040d600b1f0018101e0b5109154100a4041082e2000500110b600c0d40c10030030901001404072440c1595030804900603810540c800d80c2c50341d5001c0140f0040001c0d03000c1d032a810000d03600d0254102030a6400141248c8154454140301d9880058034a003103484540640f60120b410301980441031a15007030207061209c0460b10580001d51060700352109602408911 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 60008 1250 58758 58763
    0x3120204060207090507030b041104080f0c0603060409030207030804030b010302040b010302030f070302090d02060c0102070302010b0105040303050405010305041a04050a02030601050105070804050409020303070503040305010b0301050106030606020a03080402010302041d15010804 122
    0x1c20020340b44c500040e00424001d0484400c0603103d6460700342070745850183d509181d454200f000d541c0c2e0300e4224020305000d12814103d07406d4001603210000d0307036100020b481d00f00c40200d0300043c01248901c1c2c1030b0718101c1907031b1004258a83c00b01d000030501540060460489000740d8092003034501c00c1004400300d00c0708031618801c0c1c46802001c112018440e9020345110900a0003030000041290001401504941d095411a0390001100b0302003517030a000354440310300c003801d025003000c1c2141d401808901850203258100343c0e03030704002000c0c000c22010901122a441c5451072141c249401c02c1038135180c1d084e405034001c0c481e0000009155115408692016410659490516092504100242c0320101c003c4e47d2600c0180300580100707005100030b000035880703403000041000500c2d0505080d55016070028050503c0d201c010051a81c001c41c685082d69410700c5d15081658440c401603000703000c1d80d040500385811060102c28002c0348800e0260081d86801c2010300c8030081d05004580000c02160b00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 61258 1250 60008 60013
    0x1103040b040b04061508010506040b0411030406020a03140405030702010206010501090513050907030501020a02030408070509010501050304030302030619060306060212040308070807050a050303070c02090601030e0304140103060503030a0201050103031202040602 114
    0x80100c0c511030386141d0094407940000c243c024001c03a05c3c040c1000c0030341110b03280380d41d103005200882c6480d00c60705a403c03605035004c2c41043e0384e1036550388050200500241055030000740d1324520910aa1004040391028500807005090a0034456a650003224089001d44221800440d8030b41c0070340c81c103104540c2d00500c9081554903610ba02000b804001d05100141d204944011000403803e0000d01004c004a0740195140c1b072400361214a0008a6031003c0c0c024030141005000590b80642101d5100303801d0b05000da6039881b0303070002c01c504004415130200000c0d2080b401140d8540c1c10f800c4401254015821521a0100d0310600d4002e4422031000404d448820070013880040ca403400034201c000e00810580703083c01119111141582e20841d4442d0000307029445581c1180741000e071454110b03c01f880c00704000900842c003c3d40c0e0307200f140192940e05e007900314030120300d070711a410480140c20081e00396521f4032080315000e40605000c2c0801c41c0401c600320b040480160344d9100752021120281d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 62508 1250 61258 61261
    0x90705030d030207030203041203080910020a02060402010c14070303030501090e01020301050a0905070203040b0304060203010603060803090f040509030903100c030b030307080304030503040303020702030a0b010303020c04020703020601030b0c04030b010803070203011103040b 120
    0x7015802544a10000c0302035010034400003d060400d0003100c1c04260083d00c41040e103241c444a040d0a008400b014075120a10500000845690000d5000c0d0b201d40d081c05e2040040445007406802c102134040d02282c81d12503508003204041e45508205c1c100c4019600c1031000e140c045005500781d0109010b100c1c1c1020f000141003000890b15002140c10100c18019030f45040e80f44c000c1c0841340c0d40111800d951044d0000010001c6c141c1c14801c440003000c404e40503501388601d0b00c00103055004d41c030100340d10a60311540490100c40c0144101c030301c69a0024101c2c0d0110800d00d000da8040d01d070181c00da1020a01c0c0c11102c0703055013004001c540e203956102159034a180d985030340a031000e410160003a02016030074442800140c03007c214031015103014494880d40b641c514a4000c4c036140300e199031306000d64014444e000c0000d4000a0641c11359a00c041449100e030381c0c140c2981d0310381c020345d403002d40202c611304000070314440044000c109060094000703001840b4000400d110342d100941d00144088450310 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 63758 1250 62508 62533
    0x60406090305040503030301090204050109060302030105010509090403030b03030703020a02090105060301060503040305030702010609020f030f0601090f0902070503090303040e011401020105010f05010309030c0204050c0409050906040506040b07020c03070303050703030509070503 122
    0x34891503225200b030800c10306182d21400861b1846d042600403006155000500384007541c2c101c0302c40c0b0001c01d00c0f490705518640c14400020308074002c180302507025480100101302014001e030411840c010740a01103980702c1840f070600a40d541f44041e03059008924400001c1000c0c00e143d0101c90680d5440c0c1c444600e1911030f07640440c0c990740001c00d0401155a205004244c40030240002c188055480031560b440341000042c146042501500c0641440a0720204214102c2c1d4a0300758000c41e65030220058860040e810a0342c210b12031382c0103803581800006030206114102c4031045042e28891b40b02c1a1002c00304500580c00c0383c0080c041c9000910075280700300324661194009401d024440d15290040742c1e8554003060580f0f0054402c001d40040c085414400b41e2204d201c0d09034032002d5072005180c01c2c2401d0301c4a940312a03015001402040c038590001d8202c50081080c91110701d8054102c52140d940c3c0c0c20003e140350082c210441c00641480c001c504c0f51500081c000c01a00c000034098030010b603104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 65008 1250 63758 63761
    0xa02010804030e090705030109050601030902100309050109080f0408070602010e03030402040506010507140705030f0106030f0209041403040801090204110304030e01080702010e07090507020d02070303050a0e0a08030313030206010807030203060406 108
    0x1d00031400c01c050b82c007154a094a840e003800b0b00400098490315141c0d41007000c40d500383c0d031008202034101480d00d502c120143c2d4640900c00c401002c142000601c0c01950f04009014080011001e008010005502c8010700d07080e0008204450600d4191003940761a10310407820f840105803188000c1c2d0060021801529195214a4010b101410098913102803076440c400c0c1e1510303001c40902142c0103100b042046040c2800900341c8242030000070425542190307900d174001c0c03030806c401a010320705080c000f07810020611000a01c01490004591303e8555070152507000c0c0c60f0f441d00c00c0740100d00306540e803541c2e10181c505503402642e158071929402d40b004001103561a0300100030a085648074010803031002000e010140c054900810b010669107810b40000e490300030100c15600842d40442e03000c00107c1d40c4401515610003152900941081030b000004410354041c0d00036101c14080001400307101c1d04071540d015480351003a000d8460580e42c44482544560f150310000c4c0d05074000341d00041c0000c1c541d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 66258 1250 65008 65011
    0x312040b10090f060302040c0e0102070306020a0302041205010903030b01030b0907080402010302090a06080f0105010203030106050a0302070206040506030108030304020108010b090f01050702030307060507020d02070803090105090d050a020301020a03060302040501050904050a020108 123
    0x19401e903040e22603841180c941034910703800341002401d99680d003d00175414a4050420010f0460401000d106407a00000390703198060b100103060340ba404241d0b903410b54440d804a400608a0100c140c80003109418801d008004140084011900d080d0b410205540680111410000014081ca06513560042c041d103601130020812410540e00300120f4410740c0d11154880d015101540c0c44c14003602c1d04031604100004181c1041d41550b02c00d00040000907800000c0322524002c0703181c0942c4810322440072a0060166403c001d512520100010500c180000040c520450003680c8500c00c0e42d9840b44045950302c95448030390b4001044009401c042d5000d0700c02081190720187c2140c0ca4a40940c076204112481030b030b079810060300450302c001070a035810481e400180540c5805140f6295440c0006003092051040c100e000300340d0240c1500502c401404080d20080e0098000c2d56604000600140100000e0008a01c40d900d04070000c102c60511208180c8210390080007040456403e80055511040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 67508 1250 66258 66271
    0x60503040606030204020c0307020103050105040b0a030210090801050708060102010b010306060206010504090c03060204030506090d02070501020604020f0303070501050a0606030e0601050306040602070f050706080403080108060402030705040c0203040909050a0302060106020312040b 123
    0x22520800801a29184001c145031f0000e0400345440d520240b00043c1540e2040c0e005a01c0380b42403502103000c0395290581802141d6040324602c51038141c502042e1209451a03119100d0740d4681401c01a02ca90003940203403044009030300800c0354401c0040154200c807400d000d980d00592000e0010f201c40d04060b3b01130026140650581b0b1801c0d40d13680d441100b87d074070642084900350008021302112500802010000c815240041d00040b42403100007075890000400103841500c96520715803042d101803088500c0160080300a21061412680000281c003071407003000000307841c00d0444c08289001048542c1178a0f03005000d003803a900d4a4071404040d4010013420364800110a00b0100060810021074000348503d0716034840c1c525180c24050250a0146c3c008032843d0041d00801006a401107140010f030380b81101d00085a4007820401c91a50080d9004000c0e224078000440b07052080000b03580308042e200342d0885403580c0e00c5441c00c0b61640200303080c200488072220003040006a0607200c0d241d2000c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 68758 1250 67508 67511
    0xb07030209030304080106060207050a030b0708070c020405070305010303020c0102031305090a0b090f01090b0604030201120507030e01060608060306090f030406030207020301020d0504080705070506030603030702010305040507050a0e0a06060306050105040605030406 116
    0x528400010f4215030081e4010300c020303076407082c00b08410754051082c1070048c6412103402d81d0301440c5850b040482030b4000d01040803c244175000400c42c3d40105007606040350090000c016520345030201800a00c805e0000790050707c05d20f19026043d601c00000c6070503000300d000c0e610803001d1900061007803010001e880a00140e482e000c100d10310b0703143c0000c010720900d1800c0842c013041d45411b942c5412503403080c00720360092808000030300151341c0064120502129401d00001c03203940342d2804a0042c0719000c0c0d03001030342d420804000ba1143d84002d910340074950440507500309455801c03030349599007090b001e000c80c184c10030300c01007080d54000d42c06442641d00160001d03280070307801d1400030201c0d00704407012211040c0226104041c0302e400c110981c0507004c15503d003071460400b680003903503d0080740320081c1050346502c00170341000004d2142200400d00030300403d038220707210310b20007425032422103003020302130305d042d6002401c0c81c0319000d00e800701c1d24181c503920b1510b400d112088035135a100070002e45019 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 70008 1250 68758 68767
    0xa05030102031009050109060b09010507020103060f0602010b010e06030708040f0f12091401020105040302030904020c01060302040f020a0219020105040306090302010e0601030804051203030f01050405040f080a0504030201030501081501030b070302 108
    0x152000c1c0010340c4140e8603408001c030801c0c20518a10101c68041c2c1050b1102850254140800030200c4125190020b00f4280720351503004c5c5200480c05031500e07030064418080881000250300350150418011103400340c0b5140782422001e414404d0f240001ca490b0400241e28101260114140141c09031001d4014602000c0301c00c225181c0b5095008007150b03003000507407207032810003c072440390b880c00ca5452800d200078481d605140e02e00a64074000c2c02c11780d44c070035139001800000011096111070000c43d40940140301c2c180303446181000a411640251004d40103288801c2c3d2100201600340c010f96a05865440c200b42c10741e11108000c2400c07000c00c4066658510140c5248901000454002d40c4114603455580d403d10082c040507480c8191942842e074028001e01c60000c1c003070041d007070540e9020341c0c1c009225607a070f0034401c0d2090304d000009000c017a0005000020300b94030100900c2540e00030b0301c01f406541d03070b40cac4004c55a40e174424020811074a802c400500001c1c101c01c0340740b50000c120745009800c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 71258 1250 70008 70019
    0xc030c01020406020c090a020304030207050f0406050a080606010305010506030106080103060506010507020301090f0507080c06040b0a02030906030106090305010b06040b030601030b01030605030f0601030b0c0304020604090b040204030803010801020703080108010203060a060305060a 123
    0x22a0322680184015174050b040c825007510780020216401840000d00790f046003025640607595582a000720391183c03108211884d1b141d01c1c1c680c0a0401003000518950105a4810b41240ca94400b40c400a00080c100b03400410741e03013808400c90b0b0403101c1e40d6a500e0b083d03a10b144c4414004000c040d140604000041041c00c01583c0c00340034054034035015030030140e00d09400d490003a1a0010a40c0104119044043c0440140e611081a58212222a00b2559580e102c0e00c80490840c4145ca04142d404500800040740c01a842061030050300d210354000c00c405d45141c002c200040c001d03403062100d405c034200300103075483d403203500007425110042c1400304005403218006401c041062448403a82c0e40100010814000e59510458210400060390b42c51400c2c00c0d0085001c5100b01e000e54140c194aa05801085860756030440e8020358100c0e8020340c6139610783c10224040d6000000039030002d0008000454a0441031007224050f6034014030010b0014502003041e40034081c02840694040e0803141c00244 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 72508 1250 71258 71261
    0x12090402070f0302060601030f051302060706020c030a05030108010b01020105130201030b0f0301050106020a030206060a030302060408030408040506030106030603030806010906080a0b03010204030b04080712020c03060106050c0a020301090503040503010605010c0203030301030201050c030c01 127
    0x240e0b610030340141c100c0345800000142103030300700401100000d040000380b08290801441410544d90160ba11541e24102b07810500003038410309001c00400e02c00000e455040c5540a03010714181c13000d0000a0110b03030a40310049081c2c1e2425105101d0300620101840015130099100c0218154054000c89074140c20b00006070846a0903480b05015030851000070041690500100da441401103a016940390b0950710001c3d0740e030a0050005050f5400000801d0a1050400650b0700030705005110703d03500e603150080107014100794441113022442410220f2200d40c0105503002c1030b24101c1d86c070030301c0942e0740034003000191034070f25001e80d050756082002002042d0040740340ca104602840c101d84e0703140c1c01031400100340c0d008441110115009000242819034011840e54112444e51500640310b040b2100041e080141d4041c00070342c150f01c0c110144041040c080003400072520118000c01c01a60f50720300650f40e480c020000294590403c100602c0107600800182c401204507000b200c0c10072401000203070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 73758 1250 72508 72533
    0x2120607030c030605030601030b04030c02010504030605040309030311030306030a06020f04050301050a02090306070908031804140403030f060801090201090302060a0207030206030406020304020306010512030a0f020c030304060306050301050601020a03021209040207 116
    0x20006512603182c0ca0702950503008602c0200016001070001d9890b54651000680001d44014200705102c0c4051066a1080c01900d0245030400b20801c11820580707806450001d0521003207012070850305251003100c078040700780d84c0314410140103070a002c0c020b696100021340c40501c807012081e00c01d21001c40c25846c248185c41c420900844010f0340e0b2032800017010b1810078010100c0c0104640c1000c01d001c3c01c131001c4180c0f10000345034400106101c1000700001c1c0685261600c078101895a10104401d0603415000b0f80341c3c520205101700011915980c4450a07124446400390109240740000c00040c1480002016580002d1054950407070300c1e9400282180e20070b44080e1000d94011050009515080c00050f005020445501580554044004d900c81c0030758143d5001784000a285038080381d000740b00e95034198500400b0b50390399070348490b0060010605406850700030761800d000030f8010350001500000302900354000344000b000051081e4031716403000c8a103a8200d600ce00907180010910012403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 75008 1250 73758 73771
    0x2040602011a090402030a03030207020402070602030c09040501060801050102030406110f06010605070303050a0203060109090902040b03010e01020703020f0303070203040b0d060503010204060503010503060f010308030a020a0302090d0605040210050703050405010c021206 118
    0xc615032002d004503103400c440640b030141c8216405801e0000690300065032a0300c666042c2009a165020f900000d4024000c0307120142100e4000010401c0401d0707504000c029404084a0411607640c03210b0040b1400c090074087c181c0503078410031050208501403403071000d41c803580c074080303c000d4440001e003541484000e9000c400030601c0400c01008150b01406188c2d0300c04c0c91640300b1030452a249000a01e2005240320b2442c080c0e503a004203170706646441d0421701d802035018000380044065400c40c58000e5002c43c5040c2c0050080101071005650080200c070f020b0006980114202801c01e0000c0c8003960040152025017591243c00040c203032020300181004096036114542c40398036103014103007001c070000c101e81d50095055005000058104c000e40f90005044c100040c0c803184511815002445044070081d88801d85509410800c541a002644194401c0c3c3d803130000400c44a0f400c0e10540030380d010080100d60180b006011030b51003010309024490004000d000305162440c3c0460810400f03460b00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 76258 1250 75008 75011
    0x10c050f07030b010302030609031602010509030a0204050114040e010203010302060d0203090f07080a060c02030304030c06050601020703020a0306060501030e03030702060103030305040c15030c02010501060507030504030809060408070602030301080606010306080c0d02130204060201 123
    0x4001b5454244640c503444104e1030042d600c1c0016006505120700701910f4000e05004000c0f800500d00d440c1008480081a801b400030005540c50303070880ba0184a15901d540c0c890380c18090f4504244506000350780c100c0f6400b420b0701d814001035401c000f001c2d4100520764851071044004000750f4950801000c0000d1441c0d00282c56080c0c4103003040015686081850b809540c020000d003c0041d034089107141d4040d0704408001041e03243c4100403400e002442e80040d5100c01401004424880b8550015044806c241c8040102c2c070b2400e03034125101c4c0030403980324025801000041003c0b0303007c3c0d040280d000d0b00c03030120040302e642c42e05000c0b907211054940030000a07a0f900703a01e044441c2c092140078094040e5050441c1000d2040d600205503100b03d000081c00c4041c045080c1e5040c0d2140401e86028010300c2096880503529004029a42c0c1c00911500751513210304070210703000394080d10402d01650811009401103c500c0414441c504808100490708052149801001d071480c520140016007040d900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 77508 1250 76258 76261
    0x803040209010501030c0806011103040504020408030d0605010201060302010c06050a02070602120406060b0306030307060e0106030c03030c05010c05030105090a020307020a080a0903030801090c0203090909010209040207030305040b090109080405010c050f07030b 114
    0x18407080c884140c0205051629140742074682c0c0c0c0d0495a400c1d8041d10911b0040c8400100317400d003074290b00030b41c0d0025400c94008200810a44000f20107000e003041d0f240c400708a0180da50b00120300b40c54461002a000c62288a07240c004214141c000d00d92060350300c0c00261a10105980d07000c101e03840307148103103021401c981c01d1200b000b900b4059a001041c8015401c1c0c00c6080c400000f0f6240c2c400d201c4000e000d1640c600c06601517440a42004c07006541040210500d103580c0c1c24090000c0354180380c1212030b54a4141068912070140d0300303a0303050f104007408101c6240e51300100d0000a6101510070821351244481d400c0c0050542001400b000302c1c9644d0f841c2c1c00074518603000e81a0b0744107820640203e030074200b140390f6881e4000b041c6e03150050304550110168031401c0e09180241305076000030350058000603001d82410381640005005900c0341586020542e03480d801381d401c840341110024503094080204206030341c0300701c1040111500550980d880d1303080c8191107502c1c08a080e481115040d480c2d10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 78758 1250 77508 77513
    0x8070303030203011508040305031302030a0807050303010806010b0301060504060e01050d110a030c0302030903090904020d050106030302030901080a0b0a0504050705040803040909020f030d0207050d060207050607020604020301060501030b06030a02030a0207020303030103080304 121
    0x7811201005c150405d2511428a540d0207807460000420700040700c10714545400640d03804000141c00142c00c0198259540814101030b84c0301d0f070003401199110310643d0000106006d082003242e048903510364641d4141400c0600c02c035040070501030154104a01803005034058100c1e4881c402c00c1c828210f10f00d5036105887c1201405403150329540c40c05140c41801004199171011040720444042140c819025075241d01c00900c200e01c0b40c81d0b014103a5868a0004400c064000005141407503003600e6034a626901e041e01e030819210b07078002c5280c0010340c00303004115a0030319800c0030790040f8013401c2c15803c06803500280382c03560300281d101a41e090340b07842c91032095041c0708036104116101540508032400003a0000b075036030f55030381c8200e40c0100051480507091000c6030b030586405030b80c0181510654201060300955622065400741d1195107001400503140d03019100d282050400502907508607a5251881802504001c240990054080184000581e000e10046018501c035448040d102c1c00d050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 80008 1250 78758 78779
    0x1030f020f030a06090b01050403030c02100201060803030702010603030201050c04061d0102010209060c0102030402040605090105060313060f09030206060102070605040602070504090203070905010e0403030b03010204030b04080c0a020415050112060509040201050a02070807030303020301 125
    0x220a0141882230400052001c40d0740203003c08005034068596a2042400c10b908a00400e05507101003107900011081c4051503606406c2201181d020368001d008540b10700e9180c0c240381c451442884080340b0762070100075130320314540702c0e010b9059414000103040070301c000c0200342036034000028000165400020070086103054070805003d854151070720340d40e940c1420013080c65440047c11107081800304961035003c00269401c080c14001c140c6109005c40b4001d850007940d5a00d003a18924058040e9074800b080203445001580c0840d5001d50080003600c1c9420103000082c40d2703c8500b41d0b01070051141c003091a4210780038040c000c11001c1c950b80b03250f1a15080080441d0040e040c100c0c4a64010081000441c0e45102e2190700507400c5000b4968817821080140d24022515000a401030309283c8418100d070350026028040350000c0e04d440e181c0c414900c0500f0112000d601a03035502004101c08207015501c00d10180000c0a29401111020b075100e40c1c00700d1074144151f00407800607400100510940040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 81258 1250 80008 80021
    0x203060c040305011503050a0201080405030d0609020703030b010201050402010206060d050a0203030301061107080106050307030201080601050c0607020102030106030b010305040210050a05070b0108010b01090b0a090308030606040b0403050606030105060108070203070201030f020f030a0609 126
    0x42204055903400c6da0743d0a91207410405001e0304100710b940114081c4141402291280d0400900c204402c1b070390b034203200c406034102e1102035000c24034141d40c1c01082d50040c01464455a416400751480c1c2d5036400400c01d04205005040c0d440f846610090310050301d00b000114013800180d02d40c400b0030702c01100e500b803404c2c071513400c11403d0743d0600d03204202710780b40021201c2c00e42e80c0c2400c1041040d138a020041310a4000c4844001e824410f4100340070003150107600850686586a50501c5007000840054041d9041510020341200500c41078035002840351000c0c0810084038506581b80039015141c1200002c4280c0013005540d544542800c8250f802100e600011706800100341d0420800f040c1c0903288200030301c8090b000080000004400355562000ca80290401002a6440310703142d003056540c0d40c4e41150028080d603e0807021403620341c0200104d0b4030420740c5600440c034000f1254011030203801d0103141c0e1183c03030340c081c404000114000e001651183c1503501000810714540000d040a8070030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 82508 1250 81258 81281
    0x509010b0403030206010303120e03070605010510030b06030a0203040201050702030604050601051c030806010305040201020f0102070503030105090108070803040b090d02040606050a020106060302090105040504150302030102070305041703090906040e0106030203060c04030501 120
    0x201040100b0020380c000c5640350440360103080074880f01015041c500098003088461340c203180000150641040a154000c0381a14021740750111a5150980141c040b100d41c5e200740b130340c07016083c00040c0f45010300da0000d551003403061505d941441780550100703107420000d59040b1045d40003003006100c1400c1c00c4040d5822009415800b00c062015510080c00381c450240c0528100742c0c803030300003c0669000f04030012131a0b234020000c541d900180e06005880c1d820078003c039403050301d0a00000481d020300041041c140c0d0405070141d8503291400c02c9503880e80d0f100d0b50940c0c0d00301d88950b0600d00541d603203120b003000405040d01c6a695403c81000000d0840d402d42e0045411315106200703050316a64848141c809a503002d880004901e9203082110400d244560f0009505600000d545810503500c040500b080314203562200c440d00201420f00341d01c0e801040096600503a00300006000d515054000c92003441001c000002d03920340300c1c2c001c2400d20604403000d5418032070001d01002040824070400d0864038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 83758 1250 82508 82529
    0xa0b0702060c090108060d0506010902040603060801020a140a030605030303040305030105030d08010e060d02010507050102030106020d140a08040206030402060c07030308090c0d0506010312050c01060303030902010e0102010b15030907030204050a020301050901 113
    0x203040302c0d450b4024000e1075911410880341400080040d00c0f0380184c5c010f181d8100c801c403181d540c7d54850710006035204c0d004450010341003000008000d0814000c1d0740d04c050310b6440d4a40300d403103509101103031034002c0c0340b5041c200740c0c5a000001d815103044c0f0095000794000c0da12142d0340c1d81800c007070514088107200000e00300042c940042010500384110b15401c004203e4140b0550100c2d80012100ba0160140203030681d44000000039911f900003450b1a40b0142d1600d40640d030b0068140f841c0b03240e004480b159000308448400240c010714200008551040c40104000d0038210458082e510b4008190401c030017040242051004800341000b6000d0450811540c004e4428110f50340c160f01c600d41840000c10f8a114400e8119004d03028005030f41102100d1341c020050541d50b1b040007000f40c0786c0d0780003da0108486061040c000e5106018040c440d200c0074059803c0070b5440c6000c0c651a610003001d142007409240b00100060b540d6000f458001e184940300543c40794140000c1007003140041c1d0081c0b9216 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 85008 1250 83758 83761
    0x6060503060906010503070e03150105010f080108030d0507030603060203090703020901140f0409050106030209070203040303030507030501060e010e010203041208040503010506040501080a03030203100b030103030f030c02070f030605040609020607050a0b070206 114
    0x1603680b4242c540d800107082c43c105882e0384070320b5401d0350f460002d000e2980c0c0c940a00310845006145001c2c80504940c401d80e1281c01c1400709079019110304000380076116035508204007100ca002d0782500016003000309403a0014082c2d589880f064200c1e04150b9008090b508950340410a6140c403c1042d40944405400c1503000b689540000300300510344100a4082c64072600c031001480402c1d80148011a000350012006141002c4002d440b98003901086000c40c0c68480480d001c2e51091040305c0c180c1740c031a10b490141154460040d500d0400501585046100c00c020225880c0210700c41400014841c078402501d83c0e040604050a40c1e400902c080e0140346404010092600006848100f49800d0304005030b690b11600000d1401e003d003504882940c4000000010403d41d102d08040035008869404100788034281d18100c0c3c41354118842d4400101e01c8440600204045901c0160068840c0780c001905288540c085841074000500c02c3e26150804510001440001c240140d48001d40e4406071815 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 86258 1250 85008 85021
    0x20903030403020f0402070204050903030702010e03041401050306041d010b030712030203030105010c060f09080304060b010309020603010603020a030b090403020d09080102040501080f0603010e0109050313060203040305060103110607060603050102030a06060503 114
    0x2030340107610000e4410400b119000b907a41d20342d603040781c91260300604240004c1c9424041c09549600540d8041c4c019880e00f1014000d5070800710a64098a125103610b464502844004480607007020b007003668450355580380030074034040000368003500d150001c0010500440d0641050b04001155010240210360100c000b03001a42c04021681510401d00f040e02a180b103a0401c03100030145484d02c20a4030745419034182c1803191000c00786105920444090000d4900900110107540c0c5098000b500a84140018040039000303802405038911140b80000341560f8800008089200958040c0d001d42c1102c0b20310359903141d011030020041c1c800d400080d480c0c58603200009080d0b042c001c0c01040e0741307120b03180402c50320307502034000c800e40e280c00d00000d0100d4881400c0c241d8aa40c0100c00d141014440300200240300ca00220594048980040160406a1030760b215000303410075848503030340c0c0076000708414030000e4203d110b424040c502510005803a490150b1412044510755001030703080c00703010300c100405c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 87508 1250 86258 86263
    0x3010905040f05030307020a0c0b070302070306020a02010e01050c03010e0108060106020a060b04020c010906060504060501021b04020304030c0f0602070507050409020618010e060403060b03010b0405070503040609050705040501060201050906070201020903 111
    0x44560000001403a5640c0e814581c2082c191444001c3c100e000010070311008a50000300500e20354007a12010309007030b5403106c910066108246006026130800101000803e256a000d4045c803c410700020032110041d007130080c00c64404603a2900c1d803020100041c0800d940150406000d030070081d0003403000b03504001021790f5540b11800002d08454480f800114542c68039010341e2107400d4440000d004404803480d24901070169802203e024504d4920005070540c40058110101d10401488846000400d41400060b500050040d000d07c001c0000f10070010300d240c01c014052a000704001600c0f0029071818a003002101e5000611443c00d0031501801750751a21b08441030141050119000b0042610050707c6a2002c022459481080801c002042c06815080030b48000d400720000c21200f8003a500300402c442040e10001c0003c0c805200140014a03560301055005000f4805c130b920080e5034400040984400340c02120060351030364280321404000700040d41d000701c5940001d60901078075030046503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 88758 1250 87508 87511
    0x90c0306041407020102030411010801150c0507030b01031202060709140105030a060e0109020706110414060c070510090602010507020601080607030c030204080a0b0403020d08040209010902030402040b0301050103050c01020c0102030301080303 106
    0x10010040040800c0090381c4542c006201039102010b0607185203401c0901074001c1d0412142950116000020500d0940c41480c41d64182c03810b2468800040005030411104c405010008031030902c640ca5020010508110456000394491820301300da8103a02c2000074100788016019070207100c60040144091403080c1c406607071800c0d007032031b04a4030390b510310880c807000e1315260f0f0144902441c2c0c1c000204820500d07400a11003a0b0080500f84042510b91019800c40d1145101d000441586840d40310f2640c54484018403400d015401220020781c2c413440050f8480703401c441a00d01103070740d0319030400c9a19028050980c5c0190a0f00150a60f07624000c441516108001d10000c100b65a40c003c008085020f07905a401a01c0b00300201c9050805a02e44585c1c044015201038016108105c82c5201451142401c0b9228540c003400740c0d40564030b0854600e020707401c003500c1240d1103902c94444446d5074900b44901030096010710000d00030108030b040003a0810580a0701541150000c20050140c0f940c000101c0703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 90008 1250 88758 88771
    0x30b04020103020306030307020a0803040501030c090503060105060702060403200405010501020a0308040201030c02010e03030103060507090503060702070303030504110607050a02040c03020702030712080702030303070206010603050a02040303020c09070908030705030304050c010201020301030209 129
    0xda034070741e03545c03000a09621130403d00940c001b60a00380030404040001c05001618401e8a00300400c00ca50350b01526401c3d11881950f9140e0310080051119017408000b519000d0f05c0503201130700b001e4984d55580c654111400f5007900190508031011210300d068086c09004250038009450321a0207609d00070040080104040e050513100c9100c134011034400d5200f90f01045844040d2074895849160032006082c080e80c200000484901c00072444d0319003c2171040c080c038519001000110f18596043c0c0203032000074016100200700d40e140ca041500c691006015051107500508200e40e520710402c000c603800258503404052041c05510010707100010300c00c064416030300e08443d03074140c9403600311782da441160300c0290540008002d22404580024046050702d8039601c00748180c0d59140211000c9008a20015005074031a8441608908101c240340390003810b1880c0031170382035884005441c0785601c84e2030100c4003940700000700010b0207c14071540c0c1502c0802d100030352641d491900015480440601031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 91258 1250 90008 90011
    0x1120b030303040f020303040f03050a02030105010501030b010801170705060406030c0807030203070c080304050109050313090b030309010906030506010908120702010206060904020f010f0201020903010603140c0405040804060507020103020705070b03070908010204030b04020103 121
    0x100401e65404000723450003001c1070050090b20503200c4c40d00640b11b85682ea0124000e600703000001c40d0660090080c41440c20b0103030740d8400c050b0310307224000c6000000320300340d202c59028a44000ca582d032900340081010f018242ca01041e00d0000c8031004145104c0180020201481030040c04005c942c45980300d08255001200320b602e0780c4860600b41e00601641000500394031000580e0350360141c3c0100038900b02e4902c014100036000005040c161240306144282c1c2c002040b070001400742500030f41c0101d0f00860185850905a40c4458103585840c0d440141c0090050001c945c160440d81d0410a59034480d0058441002d2401c29902040544010030801e5060180c00c0744480c100c24070035410b4422440e8003c000b40040d40d902c0c20b0526054850340c414100d507000d031201428490400e400783c01d015950011b40d081ca441d18059081700c10360804141241099020030200000c103e04116013005442007a00042d41d03810070703410103800b40b0041d82c815010359005100c00c1001c80e0781c11904913070068084c2070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 92508 1250 91258 91283
    0x606010503160207050603010e06030601060201020403030203070803070e0904030203030108070501020a050c04020c030d05040c03030e010302030402090612030d0207050102030a0507020a0b0406091104050f040302010f060807030f0201020a050607020303040201120b03030304 119
    0x9041c4d007042107076081541c0020000c03000040401903405081e010344010788c241d03003069072140070403420703441340303000103809680208844030010780750a0040d50f000c0c8486ca03200710b030b41055000040c0c581c01d0036503050340107910110040c005104140000c80041000340014041608240d8030705840c2c0154408041c422640481c16285610b000e0088505d02d0a8140c0204164039051400c4a4059a43d010940001c1c0c010500200294000c0c400c81e805190010304008880d5104804c201424501c03c94040403030009100442d440c180c0e0740042c0c40040d104400150312807074104012000c03a84001d00e400115480858000f001c00c05080c03040b07070425007020340030402c8161401c011403025800c140c030540061604040201120078010b400b80901d210740d000f448070500c0c0c2000030041d1002805440d41540080030100001004003502ca50310601c180152500100903803180c50411200311001005600004100811583e1006050f0703407050340914100002c01060700401c0c3c1e2400f00410040a40c0380c0d080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 93758 1250 92508 92551
    0xc08010b0c010b0a08010917040b030a090201020c030a030201020301081204060c030311040302060a0201090302010501050f060405090603010905030403030903031704030e01030507030b030d0201020409050604050105060304080703050403050105010605030106020f0606010503 119
    0x400000b400720f03000e4003c42070300da52100503134001c060711076081c2c880040c8590b194404002000403102202c00c92103202c0c2c19a03c8003800e080051180a004130306520907400321594589090040071203040c0242c00058807985056805410150412a0380c4203100f001c1006002c0e46401004040c801501458001940c02a25900986a00c280d800c0a50310600104500c2495507054000d00700040c0f20340c1c000e0049907a03c00a000e00032486601442d40107070140000e0100e800d188084a502130780060012845a0107a12030300c0c110391040d0070540c00224450400c0c8107041d04280e4407506600c012604104515168400500340070000143c00e040584543c081503e80d84203030000341d440701008050358206640c040300a030007544036101c0d505e03005040100180040c6424892281200c01c090440d0346036a680b40e13189440ea912108080b002e02809202c04804134400740f0030517020b8006611002c2d502e50500201910b010042d5400054039400300e800c104d602c0c2d034030100b520742010080c1c010903006103500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 95008 1250 93758 93761
    0x4120306030203100501080d0207080c01030207020409020402030c0a0207080312010e040503070506010602010501080f03070803010303030b01090e01030602030601080906040c0506031008010f020301050a080304080c01050702040209040207050105040201080a0c08010b0c01 118
    0x2076001940c140710b10707a0030702c0c0c500790f013680403034121003500e404c403400424028070507601c805031840b0740f07007180d0880c04803000f07154001d40080410b0b0f031000700f000401c0400e0341d002604030303002a9003103555007901143c1c140078681c040040e94064a500e41c02141805101190001e07441c505004880700400b4000210b82040030800560341a030f035018007a01c8940d078444600074001c01092007030312501d100340803903c900c07907001104071103400307801c0706d411403441e070031510181c002d40800803110341004a18440003030b8000041c59114044d5109200140c0d403410008001401c0700c40180c00ca64003600184184000100e144210074226102030312801c1c1c0365560b40203814001545540403847c6175003000002000d200e4940c2c025410384100f164003000381a1115803c541c0c90044d401204050386c45065128903e600800c042d02041c2e1006201510b00381c0100c0205060360840541190642e44900501046680003a0788035400307a01e40c00104003089400b10020907600f01880342030170103003001649800e8410207 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 96258 1250 95008 95021
    0x2040603020d0501050609010605040614090a03050d0206060108060105090303030a0504020613030501050103050d0503040302030319090204020703080604060504020a0c020402030901060503060405070f0605030c04030303020903010603050601060c05060a02030402010206041203 120
    0x2d1504000c968103081c010b02805086034500d200e10102c80001c0b480030b000e80f050f90295079647e6580541c0250004503944203500c00000c09600240c100000000a0000c200c5d580c541c4216070b01601c1036040c0400007500460000c1c0c0084d05100041c41480b05036107001090700c0d0302c18a40c030302c00324a80d00c80d4000700c1d4640c4038602d21148510031406000c000e025054220a040740d21400440d020046151011079040c04252001030050b0401c102180b00c1c0c003014004055400d4112400080a03001c60340007a0807640302c99002c03000716030010104001403405102c1c0d40010601903c05600d00403070b80c10000c090400441009100c0e41d03010000c14400b0100b58040c00c003500e00139085526a003054140b1070790316002446403c0001d50441e00100c0c40e10700c184240c0c0e0003004041c14050500f030640d9030540194100d0000640c05658805000001c104104201c1d1300a11898a407011269100d04003542000001401c0822643c010014000142da0000c1c40315401034110114503a56000704800b00c02a151 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 97508 1250 96258 96263
    0x402010c0605011202030606030d050301030201140c01090c0905090d0503010501030c05070b0411090702010204050307030b0a02071203020a02010b010504050303040501030e030d020309150601030c020d050a02030405040203040606090c0c080301030f02040603 112
    0x20b07000010841910003901102c07207900131411903c4e20350307e010403d07545445924041c000207500f800108019400f601d03800c11782c03c2026018901700071f0301d52006421540d031450b090b150030000310307001c00c5001510310801d50000242c00103041d00820012010342548018842d041c105a692502c07854031038460016100b00a074045001d05560a042c20900c1d030551a07540b015102c1e160320008949601c1c014404c460450700c02402401d18913145480d10100c29170020a41c82401d60204002c10000b501c41000b0009503001c0e4a006840d8640300000a08440382c011007641400703810442400290340000079141142c00c2481c0128041c5400c00d0301508500818040020090003c1b00f481154807010441d42d11a0300000d00490869803088011800c2e03c20600140003d41c10100300c4076040d5102e14000c0c855a010785c0112842c00e6581e1000c107040340d008031410303100743d940c0c0e43d800d00c00307002c20740100411000075241448400725203440f194201c3c03106210003410721762540402411515076070066001943c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 98758 1250 97508 97511
    0x1030b031203010602010b0a030b0106030c0c0501090507060806030304030507050402090105040b0a02010209010e06030c0304030e1207030b0a0c05030c03010b0703030906020412020405010501020106080c01050315090c070b011202010c020103050402010c06 111
    0x1109150701c01099002805440007550030004a803116040c04001581280d0704101c80c11f04991078030750103500030300c02840f01804101d0001f90345800f09009018018005102c1c00080a20500e00381d001419200d001d440c85110790402c000800110340002803070760948401710b4005903100da0550041e1614895507101501003180420480365058040d40a803c5007078081c1c0381c0607040031010080244501c0201d54203901d10100340b02242c00300c2c0c820101200c140402520349114100d0301e4101d140303007504135030049521000b0281041503100c02801944109400c500300395065007030030807050196010502980003414004a41201410f110750031070078210790044401c550f240d80f22080c49408070140d00c4141d0150b0704100c00021607500c140700702e1085450590141182d280c1900045074954405400b4006181201c24107001503564202c07541e00620030880c50540c0e8001d0b6150003489800144d0200121034510002500035036004044680c8490b42440c000416507654030060b030301100d90510240a05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 100008 1250 98758 98773
    0x110604030c0806010905100308030a0203060a030203030408030a030e060103020109050603090a06020d02030402040b01020d05090f040b04020307030209010f0e060901030504051005040c050102010605030703020d0609030207030609050304050108010501020307020109060e01030b03 121
    0x2c8000b285550581d05ca00d8000d001503561110103551220040c400104600030401c002802f01e1010b50140d41c00c140010030442c0210b640703400080c81c40e042500b120040b42c100107043c10f800d5805206580c2080008c0015005c190302d5600041c040d04841e2085030700a0100000040250741d0500101151561010045488400a445150003504210b4049024501d400e0300130510f0360000900001d41401035a80524248041040c084800c0c03000000c3e680190f2180308035911590b41c0d00203184107218039038005840e860460001410b030a110f008040520028280c9864951207110458588284c04c1c200030a082c0c45a00c0c2c110716000c650080000ca107440e20040c070082003101d0351444110381c000d030300901c20300b6103800405880e25040c2c03200a500051020a000c00680540c000c02c240d42e010780182d0301c0141d501c2d00c42c0343c20346004290449440e000064103109075078000f4030361800340c1000c0c130003107040c1180d580c0080d14480c81401043c050007a041e050050681c42074100102c164005829200c0f030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 101258 1250 100008 100019
    0x301030317060102030705060105040b01020102090409060c03060506030c0703030207031b03090306050106090b03040f02030a020a0e04020910050105070201030504050705060f030405010608010207050a08030604020f0c030702030708010b0a03110604030c 110
    0x20034007410a1120046007032408500c01d580300105a50000781c022020740b4607640f0705002c10000b0b110141316103041d55001d200607000e40e519481403c01d118042c1c00d010a01c0050000c00034102d900a0700000d104035418001c2c4511092054244e6400984c503040060f80c03040d0604003078079401410f4100462020300340820504140c2c0c8043c200c4120703446a10140042e90b203811082c2c0708e0911600941e1030300b600078400039012910201c500d01409002400341d40d808551500072615203241904200540c0210f50280411400e0450490780d000c0400081612100d0030138000802a204035072000e4101500d8a02240a20205001820003000003c01e001e0713a606070401d0301c4809810403030b010744141d440c120b00007603000d40c18000c48007003580c0000138001c2442c0ca552100035a820107080c154006500348902520702001400070160a10742c03800a40d00c40301c0c03500c10545810043d8011101d264105070301c144440d100c2c0500c81c000c0d83d910901031101c9401520101e2880e000b141d2000d0004600384200040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 102508 1250 101258 101267
    0x204020403050a0201080a0507020c01050f040b04060801031103010504020607020103050a0605090702010b010305010806040203060106050703090504020d060302030c01020d0504090b0103020702090406090506070804020904060c02010207050106030305090a05040608030702060304050f0303010303 128
    0x302138400e0f240e440080c2d441111300000c6500480e070a8015800c104010b6550750301c0303040141481d407946032a1038106521403950407445d410540008012851b960010310034000100c102a8001310102e0092001c0c1c0742a60100b4014054140000e040c5600c89002c40d01000c810382012010b058060709c0c1380b0036490000802030281c011000c0d843d0110b4076110011038810b034040b490782c0c802c0c2d8018000f00041e034030300303001214294405002a01008280f00c1e000c1225034441c0000d2800e560403a801082c40341c114010582403440c2d50070000c0c10746d402851540c40440e08081620708443c41d03903c0009032550711070010f80183c4a0001c00940c4010170008020402c002a44105070603030080048a4450f034924106661600c2c06442c040c0d40b21420030700003400540380c6d42199600d1043c3d0f10000d0300703007540c0d03998250a41d1078540040f4042071010078004400d0510120020003440200c40501010749008025a280d2140c00c1d0080d0242c0c500000140c24000e04000d4811280da20000312070707a0f0341e50b80c10000c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 103758 1250 102508 102523
    0xc01020c01050709170a020603060603040c030b040302030304020a090e0607030e0106050301020f0408070608011a03071103030f090c030102040501090312030908070b0108010f02030609060907020c03011e0b010203070302100207030c020402040305 107
    0x5517040d503812020286a0002c0c400d8011035002d06050b1039a1554400c01100e03400080c800c940074411100c0100018650002840c05a8030075001182c980c1410f01c100301e40d800444d0000e1821619180000029040014842d07820030303082c1c00c00081010521021030701500d00c541000d6003640c0002208120155030000401c11100078030295030f18a034a41000325401042032160307141c4451880780700b802162070b50004581081c82c03820050300e21035020340c6c42401e54008440c07111082c0b0040c4200b0081c4002400307a42c5d400704040340214542400e1000203480da4215000c06400a00d02c05101600f60f0b0003540a003040a0b0030007145034a42c0c00c180781c10b030702c21802405400f06079400d044403403e58801ca402030702e000f2003004000c440c0b41eaa40100f4400c0500c4018070010031031143c01c1c6d00c907805840030310508c0320080d0105a08110242e84a01000c183c4491031151070440d071040286c440401e80c041010b841c50901c920f00580e85400c141401c64040b1041400694003070b10004000040040004010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 105008 1250 103758 103769
    0x110304020a06080603030708030a0605090109020c0106050306010807030303020304050102090406080d0207090501030305070b060301061509030501060b0a020601060503130203010c0c02030606010c02030309010e030307060603030201050105010206100305070b0c01020c01050709 120
    0x100240e0b48a110460b0089029030300f490309948140007840c0010070203000346030320000040d4000f842541c0c41e00010b40e0fa00081e4010a40d07543d00081140300441c003805003070050201680200070030b52406c000030340d5a61540c030010703041540c0840801c0401c01c080d0111210594000d1080c03003c551102c00f029100e08880c3c5180000d03105100e00000c0103039490040710304aa415440e13680c200615500c4d03c0d4480100204031a90556840d01e000c0341841007050b41c1c5080c81141d03921b0740c01c95030462a02d00e08684c2640c01601141030300f40411075001c2d600088440c155090b41c40c0041e2a910754800a811804c05030340025855424180c481820a50065943c0f07281030084003122455103071300006442070b528803107002c0c0d015001004400340d103500580b05502180c1c80075003101e1400d1115184d02c0d00300c070302a41084005075101c50040045603070400c58a500800f407002582c141c1ca2550f07440507a07034603851059168590b00896010b041030029415601c0e11800714009200601d00004020000003060050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 106258 1250 105008 105019
    0x2030306010206090c010203090103091103010603081b010603080703030207050708030408060411061801030509030d0504050307020f03030313030804020105040302040c09060f03020405030303010902030402150403050106050108060d030c030f050d11030402 111
    0x384d207450001403040140b03a06030003031890f114508004401620800c0c900b070300c2c1e042030f214002d04680c400b4480e40005500a070a0350342c480c1204c0750300d40c210841441e59001103a0403e8010700208250908982c40258542030040c3d84d22070600d0007500303101090b0b100300d040e03001c0487c0008a1007008140140b2940c03003251031108030204a07003000043d005800c40d00c1c900030044600307240c544d4045da00072900801c5e51070489042510340071412040c0c0d54116003c84a541000c10070400b103051450707040205140490240d0706620b444000162624018400601008180780c00b16003903900074012180a03540242003405581c0100e13401800c00d15491044d080040d211032200c4580611034400c2d40c1c196000100a07501c0c60f445e0804a80c0a0340000d4011390b481a414855019550806d50041c0000e43c4581c001040c118584000580036003002807600f401071402d10003400010350f021810950306640f40c100311200c10512202100c06001e020030f17840c2e5040c9400a51042114441c4c0510b00c0749208458 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 107508 1250 106258 106261
    0x91b011103070204200a03020408070f0302090408090402070611070209010506030106020a060e0708010204060807020d03020301030f0b0702010b030102040603090203060603010204060503010e180102030f0711010504030503070309030203040905010602030306010206 115
    0x111a1001002940c041503041841000018900780c4c00c4103910b44010f8905115240c00311500507030075031104100300e0200764006020001c1d04400d01c50300c002010720024503031171145160042010700b01c000300010310302c07000055540401d564035416a0301d1543c00c1001000a9174586412079955401494280d125200401c0009001d01d0030400b240d041e01c840c0d0b80a849014280c0c1c0e03408019100340e600e41c503410700507140f010400d45802d10240c0010160340c0d4402c44242080c0c0d40c080d05181104102d07100b0180104014004103242e401c06199103a07105d5001c643d1559401000ca004050746110a540b65000080000e40c03180c0c543c1061002f54003c40c1902c21648a01042600702c1c82144111004240180010818269032940c01035200c02c0565081c281085a02056422680129009241c01440d40c083c000c0a80e44070042c4d8020b5400700008000701c0c14036840246ca81e00009080d00d0800d0341380d5400f00c04151090040c2c0340102076020040c03045586131300c00039440e90000c51741180103204060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 108758 1250 107508 107563
    0x3010b0405060609010f0e0303031608070206040206070201110102090904060b0109060215040201080408070503030405010204090b040209010905090a02070501020409050a0507020a0308040305070201051207020607030b0102070303080c030a0603020909 109
    0x440c1038020b400c0141400c2c50a400d42006407040c000c45940542808411001c0d1407194606100a6200f4a800500880d850b180c180b005400c01e04007070500b80466100c84100001030311075408a4000350380900303185007110f02c940c0e1041c0c003901c50001203d8110020006010420035540c01522507000700f40c981c0b100141d20303014101d0780c61894100000308001c8010115015501648650303400c43d018000341072a18050342c40e014030359801074408440742c1e94002401c00c525103252140d61614a001c840075458900c1180009100c94118000d4611444140c8045500e6040513070440b52600d902400075911a541c03200140e00425084903100340e03403414140050b51984c80401e50784400783d416241c4904545603518100c0325500040000c90500c00104140b4921804203034449125140580c0108034916200d140101540c0241c1c0c4614155807000030f0610000750004403060303001c200c48682544907503c600c54040a030040364006900890301906104000c074021032050902112120000c1140f003540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 110008 1250 108758 108761
    0x40608030f0d090309030503030405070501020105010506070213050a021605010b09010506040302060a03020901050d050108010504050d0302040602030d050405030906070c0905010e010506030103060504030c0507060c06050a02030105010207030305070302010204031203090203010b04 122
    0x505807022981c1040101282650b0103902c038000a074001e2508034101070b12641c502d45140d000783c0e02500c660f40034003010410b075a824014940582001c2d100503081400542c0440c51980a124040100c01e807075000182c0c01c4046d50707042e179010414420350400c440e08a42403041c000d1900e041c00500510351240081080c1c00e0540446040320780c040d10444c90721281c21001c038002c0d000b2030680c40c1080810044a40e296009000301806071100c8000001d0350304107490564a404802d1900b00c0038540140001c0002c250048141d62696513400c03808941c41c0d4643c42c103981075100721401c1316031003a000b042d000f0900c08001445000e840c08131400b0005a42c0310026000030310402d00c0380799400001080140300280c0b80d9000b464106209050051030342a02d940c0703050402c69150802000101000c600006021032400381e66000b8000350b03011031455041800003900d0380030902001c1d003400400501e0404041c402d504540065405c002c1d00240c0030940e0788004c0107030610348402da1207982048465641807905 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 111258 1250 110008 110017
    0x80f0103050c0105030a021303080301050306130203060114060409020403030201020405090108070e0103030f0309020901090f0f02030603070303050304020102030705030c0105060109090203061e0a0801050a0504020405070206130b10051207030204060803 110
    0x741c014080e9a2400004691a0b80001e001b542115000d1260101000d049103a00002d1403003032602e251658107050905162241c010f10294003014801d4881c000b6031400326485d41500c90b40400c021000d0006000b02d0306901c034031351010002c1840000c0000c00e15506501800541d50b0490740c50002d40d83e86c0484665414040c01021481e204030b8004000080c0035901d84440d000315803c3c0410307124619000101074003001d902c0040c3c0c05458001c000c03e012203510442001e500040000c42c25828404086603458919000080c1401000404103095a0080066030a06580601200d550700c5103001d03060302030102030f1034450114541d800d010403191101c3c004e6030722404024002d42005040141c80940705400104569080380c0c05040206011000380101489100c10000201d00f0303040c107106001c11104000c00480071900405c0038070655040340d41c1240c040c01d40207413044c54961103980218282c280198803481d03004148094030326460402041d010b080307a000711003c200666483d905107860b4400d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 112508 1250 111258 111263
    0x1060812030a0b0f0d03110106050103020c0303010509040201030207050304090905070504050403050901030f060b0a020703020f030a0b01030305070201030b0405010303080901050c0f0403060207060603060213030606060201020a0c02040209120d03020703080f0103 114
    0xd1000402e040c40b02e500c84802210020a211249461500802c0002c4038810050f00003880288905488120034019000284030a10b411440d090031000f4903178890106021f02ca11402d02c2001080540e07120350140e404890b00f04054903915641c0704140d0307008000018003101c8074025840000381900d041d21030640704030340540b100ca2916491100460041008103862103000d030f515500803034548a210054114400b084d001131241c0d9003140100700c0001544498644a6404040307490b00003460001c200d41101e42c5810081d40701c1c2c44620040e40a0140004059000f0345800000001e04d580055102d0103401d0100082250340c0300e00c50103194071300c1143d102454104041104000050540d801058080d006801c0000e8240d240c2d501c070340990780f03c03140c40740c49590039030000c0c41840410320806c07000344034500086190101140000c0c0000088030400703480760380c0c0419800055101c04001c0880260f140c4242e6224181c1024050001d402c107501c160009585100001c210b10940340003035060741e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 113758 1250 112508 112543
    0x20108010509040201110d050c010f0c0509010c0602040b07080a1101050402010806011404170307020a06020102030103020102060403030902030109060501060201020307090608060603010302040c0908060c04060806010819020c03070b090106030302010608 110
    0xe0900080c070030302d0000584102c0c10800c041940c50034955080c4041010418141d82d11a95021005142070079101c0070202402d40c1490504140905d0780c0020031a0f03048003007030038081032941180c1001c40c020301990380900f4850f01c00055550420003142d0080410010175180e01f254440f44090282c02c80d502110000c0c00309c1c4998010420b1580904013640000f4500d1803054178007615405880c2880305001401810b9038004104442185407022040c8050049032008504661560700000d540d0500034001a083c15a41ca651100395282900000540340d0071031424003341d652021300070b00035803088602c000082c030702c06804107040303128150041c05004010023082c00c613400c68081200604170080e0507010b10485c0c1e000007981d010140521849240382c1c510040d107461604001801a03400241480c1c1003005103420407141507010f03181c14240341400700c40180c448a521500d6850351240c904081c01a858403010803c0303e41054200c202628401d0740284503041e550091540c0c1ea002140700040c0d0344 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 115008 1250 113758 113761
    0x30212010306020c030d0e0606030c060703090501080402040204030f0b01050405010503010c02060103080309031b030403030810060f030e07050406090204050f0402070201020d0302070f0c030302030c01050906060307030305070606030204180309050607020108 112
    0x2d0b00c1c039005040f140d03902c10306882c6400c0c0c00da55284119400340b14100600e4010504100e01403809103d02c506002081d0b807518584010303590004d112000502070356041c855070b0030105040d501c1e29810b94002c0d5500c4076903074011814a080600d1588424400d10b8441c0d170030503001042a0030180907807a0f0981c0ca44c0c0060242d642580e075002207540000301789a226100611058020b1680c0d62400c044240f8000080e55a0703506506000b058510000c02d10509406580410000740b0381c0505008034a240074a00012402c0f0010030240c2001180e07448240d200e8207115010808d80e80650041040319800c40e20b0070741117089034051009074040c400001c0d000d80c00c04450030040c98040c2d00104400d5121313424a051201d0325035035040002c032164000742c0c01a032001c90083d02c0e0520920445811846d140010400f40c03400e0b20009580300c1c501d0100034200f000100b000300c10001130340c0040014640c001d2040c021400b03003552442990718034003400e50019244100000b51401c1540c01c8034011901030b51504c415 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 116258 1250 115008 115013
    0x7030206070213050106050409050903030105150307090b0301080f010e010504020102060103020603040602070501020301030303050403110708030a030905010204090504030c05070e01050f040b12010903030203010503010b0a0506070605090a050109030203090a060302120103 118
    0x981c0141809a0b002024160004000c5030913204040c060907058440f9134071036042640c96803c0798401040500142c1c01040144103d903104085a003034000c841c004141c1c0da503202d803400c0f154401940e00c021802e110200022410100c0800e199003d41c6001f0300820100500000072401e890059802a0158100000500141c282800216402030250401510b440156036589003268001d92040d40065566000d020415500a03481c021060a0f50000c048150600c5465601ca10a04d8040c401b80742c1d0303400c941c108000d02034041d58018003400004000a280c2810b000d40340780814401100d040c010604c000c03501310952004c4c40e045c4c5001900c2c68081070b50b44d00912004040d00d15103503501c40b8000300102d8013034030b0901031040c4d954801d075400342e1254900300606007176660324045148030b0f0340d00ca6003d01c0283c0758001039a411315044000890b80c0c0d104d40102034105041e040e030241081d42020741c81d41c01d040c0c00100034003024100741c44100855607101d004a04a016440c4410704d0342380c41c140104007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 117508 1250 116258 116269
    0x6030402011b030302070c080105040b0105060d060504050108070305010c020f030405040f0905010207030c02040605030a02010206040b070908030408030301150305060609010309030917070f050102010c0804060507020307060c03050604050612070302 108
    0x1441881810a0402c0d10810300c1c481c6500c01c1c2c0311004400098000030700104005540031080028447d0a0080c0440d04055846220078a01401510300a0302c02040122500007107030484402404080c02c00c01541d611200c015440c0d100901080e51a58244580102240d2001503072041032000d1001550809003440104409000c0003149029000d8a9561007404030701c1c00e02c001d0060304e20a03165414804900d205002c291607850344114130981181c0b036030802503600410000c1d802603000040d40e181e665140010b0354030110940040b503141c03101050100d0800c0e0004000e6041e540940d07a81480c003214207d040b0269901100c40640048050005a496501135003010100307a129080c40540c05469100322541070401010245050744408030422040300601c80303040c06042c00f07100138410004141e0b800740c07841c100500014401560f410002d03150b94424000e0700d0241d0b501c14401d000025070003200070007904050381d2161080b8600004203205107000c401c41e2501c00c07403480190140b10700e181c0030000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 118758 1250 117508 117511
    0x60906060901060f0302040b040902030402040e0601080703060b0307120b0403020c030601050607020409170a02070302010e03010b090103080a11060a02030403021501050102070b0a0306050301020d0501030b01060504030503030a02030603010b030106080c011403040b01050603 119
    0x1001c2c11b4081c880800e080751100c0140c0054004d2880058580c03800d40100002d1341ea60b1700c440b0586401c240014400c181010030481c06582d0000f6000c50b03c2101c07003012a02d4510168480344504100031050410003003950201c900841c040e40c220350691913030354101601e522007882441e0380301b001008504014240b03a00a115043e015002a0307001a0380d01c500403d450340706496260050308400c10600443da0888040a04501d040e4020024101c824011959490301804090a00940804c20741421446910040f49038144002500e14600b00f0180c414069041034808401500a0900f02104000a0350082c0e0480300140d0091400c5846c0c07024040d410f6000081071003c06854000100705600c0900081c407406034100b07400501c80d851030500240014060300010b080007020842080411800400c1d00e40003554010010b03501e840344030020380140b22048a0a40550038010009590382010844280e240070a8852001000400c501d0070785512084130014240c4c07454600510140c1821000345 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 120008 1250 118758 118787
    0x1030c030905010504050c03010f05060901050402070206070501060605070b01050105030601020a0305030a0b03030301080a0507150905010e0d021305060102010c0c03020312040203070e010b03010501020706050403031b0312020703020102030906090606090106 112
    0xd544901d40e240c882c00d54404403410303510341e440341401d10101d080911401401d151001002c2002d410044000b4940c6c80c010306c00c03148901e401240100541d60341700121035041c2d60000003081002d0f40ca520103003031340d0801c54041d242503528500000e03131035000c2c8044a1040704140d02510815101e65000c1e80d1640006e0105c0e185140e64002980103510100b000314082d2680c1401400c88900707516210b86807030001d41103400500c8161080001140e0441e01d0041a601c0900301080c0d10007140d0045a40b0822500011b0350148802c2034201c1404440e42c03041d40280c0082e4028400d616510341c003602c09441d6110b004006130700c20840c0b850308502c1008145c1e0881c0c0b0040c240d45840351f075080d604902400a070001540d503000040100899a0104041070040c03032141000d90a251560328080e1600241400095084210042030b4040600c038040c080c4017045100d9045403107284d5414024001d42084406000074881c0b1004500c041ca03001601c07071720440006026064507820b012007204e1110441c60032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 121258 1250 120008 120011
    0x30103050303040209040602040f1404050106030608150702010b0901030303020a0f02010204050105040506030406020702030303100602070501080402090106030507030902060a0504030303060e040f15020706020304060b09060a0305030f070507050306070203120903030601050901030c03 123
    0xc508860042c0b203180c01404bc00c6512031282c240001084100e40042e4880010701d858a4000c115480022881110070000d0300301c250742c10759400c80144d0140144404840d03115000c030001000305901940a0f1050010030344d00d510180c5110241a0308070b204a000e001d001c24401c0c00304010a01e008070095a1051003602c0150410100342d0210f807550300141e0701841d242c1c00c01802485400d504000c408014442440c0144071400d09030007082041c001070048004050701c0d480013510160007500400f00985d8003401d0680d894114510051841d0001c1c00b081b4002814040b00240711040c4503801805140c00004802c518801036846178001101040501910380c0c0030310854022070150f07c080c52242d8096100800c01005070f608005c0c0102c00240704134480c00a020742070011460010540d0041c10b121041c1641d81d0340e4900300303545400d02607800307560305109110410420380e6011014003d83c00644000e40500c0e1a00c004d85910303400122000c6000030403c1c00352200035031098000c40c0ca40c0516060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 122508 1250 121258 121267
    0x10909020c030903010204060309020315010302010c080a02010b0a030302060a06050102010e030901080709090608010501030201030507020d020601060305060a030807051b010c12030507050d0c020105060108060103060303080408030403090803030109090c050105030103050303040209040602 125
    0x2217402c1e42c1140d4800c40c046981c0340c03854402d41c20280141681c80540130702112036981160300107002c0400101d00274142031404a000d00403507000b50301c225040c810080c0061151542c03031600a42c6c400f41120701c442402d0400400086075401401201e0040d003085024501f040d890710011200c2001c02010361041100302d50000a54a13900e10030740c00540902d20004c205076043d03000240035254090180000c5500403850804030a60214460741915000c1c41d002c02d1a48078030000500d61016a04064117002d00001c000e02044070010380300007031484c6603030b640941c42e9192005489004801a010b0b040c0d01c0284440c6002502c41c0d880300d6800041820054104422010034a0480d84094000c5e40940c1d500c00c103000084da00f0102d4298042c07802d00e4240889811950014443c1201070001800c007400800418109801454840060070700d10b42240c0e12580d50305020005003480703203c262260300d80d60303001044c8ea5208108403410303240c010000710b10b51386495084c404487d200400c20745d0050360901 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 123758 1250 122508 122527
    0x4020706020f0a0201020406030c050304080306090405010e01020a0507020301060b040503030406030209010210090602090a050a05060403060b0d0803040b04030905090705030f0403020705040f0209010306050303040f06080405010b09040f0501140105010909020c03 114
    0x6000c1e150402441c4d00050300c1d1401c3c10400750444442e40d071400180141402004000b403506d20441c0d07807060b810b07502204d86864030700d800340c003420307070f00408603015400801d0681e4140d6118003d4403500b03000b10700a105103a56071201c4001032260f805582d405030001c0000b881428003d40003000d0301241881141e0042c1021703038070042150340e50b1800f15409900002c0d82070722850280511405403004841c202d940c9840c000001d02c11784587c4c80b00820b000e4882880b080c4903525480d03000041030300100019a00c4c5020300c1e201400348800c58044000c01d240d04400701d05c0c2d003421120f0320b103c0c80058a456156403551025445410f030700500840c11403040c0103011805031201c4c01901c102070780c2c6401c09a21140e003400051705590203a00601d00942c418001046542003c0065008071022400c00c00415261414864050240440c4450300210600180001c1048252000321034a0244008202600d248440100b01001c28031859000032881c05043c84981d582d58018a610035114040ba8509405103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 125008 1250 123758 123787
    0x40f050c0607060203010e1005010516030c020a03050102030105030709020702030703020d05100c0503090106080a02060306060702011e0206010302010e03010203070e01080907030501050903040305010c050a170a02040302030a060504060c0c050a020402070602 112
    0x110b2084070b100f41c012004001181e00140303a00e41029130310380c035003000c9810310340000d006002e0900140b900c00b800d090542c040c03600401480e001150050102c440316622030410b903010f503000384901c40c024400c603500054900b42610a58910f1503000b0003034002685541c00700504061428000c0d07480d400f515400da100290b1074032541c1c880c0e10154592507143d240c001c280c0c500311003403540030b141190042a00d076001179413000c0840b0341c00300b4103c900c103441d80a1400100c1d0420b40ca41341f20717501000800c0c0d08d200400d400054250480e0300c01da0f43d100726000d080c82418242e000c180c0e41900030900e200d031903120940c0219200b941c40b800400880c0d00040d074a44441d805c0d1041542c002805800c00101071050010031701034011a10981c5c18002c0c0b812251038801086e01800d014005a00c10b00100800ca1802003a01164029a0020111500807050f414420000e0500351400c484c010300c0c2040b240364060013103010101050300303d0040c20802c4050b80a0001035800520102d901c96400c00501c001d45214 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 126258 1250 125008 125017
    0x3021207080402010206060d0b0406020a0509060a0302030402030105130209040201030b01050c1504050601060c05030307030207030207050405010603020a031406060901050d09060603080406020609070509040206090409060501060302071104050601020303040f050c06 115
    0x141d88080c0e060515000190402d48003078001c6000b82c0001d45500c000c2415070a6031500207600800040e0795043d080c80c11111400341c20940ca902c070800107a90000541e254000c0d50040d130080f80200043e0300c400e004110315009070900250070803c0c25002402540c001d44c0320411404060401615007000c01e0201810030100f4002040e06003900c0040c00184403081000380d01404a81c02c1c001020202915070a60341e0000401100805d500003c450007018400e109050007088050f1082c07056513141c0700058041e4220300c41600000340b9000f81500e04213156128a070150802801071850080b20800440d040c1e8000c000e21320318652036462030710002d00b6a2054100550190540c5512103080040083c14100c02030300f1204c00d0362086505208a540b020f00d0307603820950480d4130655860007180031502905002074003074003061402000081c0103405400070051603104142d1a10000c010104000803a2001c1e00da09006070b0041c40010000761240340b1040c0f456020b00100c0700c14550075400540c03150700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 127508 1250 126258 126271
    0x304020f04060b0703030e030c0a020d050a06050a0203010603050601030b0105090d030903050a0b010e070201150b0306030a051b0103060602150a020304020307030506040f0605090105091002030c09030102030406020705060c130504020703030212 106
    0x10024135a424554984200006106040069890411418181980e1701261240680310741704411000042000400c140d0301250342c0f01d03c0c18400b5250900c440402500709115086c00b007400c00313000540071761080c8a00e0003803110507100d41e41003240c00d5050000900703541200301c040c00010440440452410001810303091b2040901403215810608821404240900701100b0b6a06142e0394401d6651600c400074141c03460303110b0141e01c9030b803040000b030b00d0503202030005841d6000d0560301445007640f00e8100c010080b001e8905100342d560f18002281e980329072503080b030b8800d2440404141c0d02d00d0306400542c1c11034001011200740321707100d0300c415040402c1038400f00c441841070295003041160700d00a481e400a490360082281c1e1404002164586900d816030801c020750020005621311102c1c41075900181c8090300031516442c1601e003480007588800c205540303500c03075000080e11694440040b40e1500d0f0744082103400c0240b42c50107020294010302e800314140340d020302c40300c0171100b00c2484a0b0700c41d44 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 128758 1250 127508 127529
    0x10603170306010f0c0503040302010e040902040e06010e01050a03030203030606030901060302060d0203010603050a02070809010804050106080703030e030106170307060c09030b0a0504120203040503030901050d0908040303050301030605010503030403030e0103020304020f0406 120
    0x1440c00004d090805411080018042d03140a40e101150020090760112602801c103e1882c6a0070070009000300341401c4001d41c0646064800603079500300246c0241aaa00040030085507600c0d10200105420540320050041c1d000300001000c1e410007501441c1c121014000200d101600e9900040140d049001c60000aa80c0070004100c0180d050154682000071210114035103042034030382d8a103e1140c150710034144207001e1301040810400b5400780c40200b080100307803440141c407881d0080000140d166900c3c400d40c2882c80205044001c101502400400c40005525000c0c2030390f034032030280c00000c14850a0013001d18001021480d02e0b0b003039034841c40c4811303000125442c05240400300000d209451400f10741c0144422301558500100325000c1e10701c24200107407140350104944001e0b208814000340381c0c0c100880d0010826811001841c140c034410039003030100741e0301c0340c00749550303400b50748005000107480c0219048554001c0e801160440d0010b07299200b6643c926000c103082e04c140e45d00030700012 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 130008 1250 128758 128761
    0x4030206030408030910020403080901080403110613050c03030406020706120e0105010b070201030e0703020105040501030b04020403020a08010b0907030e0a02010302071103010606020309150301030804030b060607060504030201050105040501080a0c0306020a020106031703 118
    0xc04e01c010341b0765144580086051a09549424003d03004001d0050b05120b00e41c000726080c10b00078070300b8100500b41401124500d03d050505503c10054039041100c00d8814241000c80c28600403055509032149a4000d220007403900104480c01c02c000c08465081c42e40e640b85040c2e07030345020b000382d43c044d00200d4941d569800c41d030310006040300da580001d07182e6500b1059041c40141e03403090881d42214024a4040b4504881342e002038000d10490744000d520900d031110002d01c2c218190402010f00c0e0044850b5030084c1c0c0c0703400041e0700781d80c2000d003c1d0030f550f0400d283c8500158003a9000d0042540610388810440c104d480200382190981e0700000096840889e0481c0300746030081508026005044629045501d10358a21045000c0ca000003851401010006000e40e241d40301500c1115400400c01c3c04541414103002e4002e10003801018062070812002194000380040d2904509600240c81c490040c0780da10784200a4001000d14002c40d52101c10000100300c40103481e503829000030780419070b01e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 131258 1250 130008 130021
    0x403020d080109050405100b03070801050f0402090906010b030402060f1b070801060603020a0207140f0303030c03010302030105010f050d03080403020c030304060504080601050a0501020703030f020c06030103060906050108060c0a030b060403020603040803 111
    0x140304050f03204008860810307042000140010480e005041c81e0b448001ca40c803000140000e003016029000626603628003400c1196401102110078080e6009980c0740195403500180c0380e4440b60240a0400200c0703003000401c006050600040c03800320320b2000c031103007024084180321150010381540c18505134000c00781405500e10a1103284d0040049003001c52030301440c0f01c00030b911501e5a1252410b8400d07500c04000040c0c5882011400802c001001d80360340e0302e003001285103d81c0003800103030300a41ca42000825400c56010400065410062000d100f0b40c0903583c3c21210104010400ca00314000c032900641d23291030400180010f0a1961a141e40f00e90801d1100c0d460000160305c002d00c1403901403402c0180743d802161520599030140fa0003140da91030070300140c1c901800c0c0f02e48581c0094002000005200f059805103510a11800050199036030f1a078142da62040184c901c04e000d58020819881010f00a40c0101d00d0300d600681480e0030940c0d0f07500014101d0300221000e40740140000100880b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 132508 1250 131258 131267
    0x201020606040b0f010806030a060203070801080706020a03050304020f0d020603070c0203100605010e0910050603010303090503010f0605011407020103060503060901020307080f010605030a050a090c0603020405010e0103020309100504031202030403020d 110
    0x6124000751020021a83c680c000107001005814129061110300300101c3c03010b40341888503040c1c60ba0410310075503807810300c2d140081000c41c00b441824080e0207800c3c0e010038010304c042044c0030780c40d4155036a01c0c1162540d0b001c102016035a0264903030300450340000d0703200585130314007d1032241684e43c40302c01c010301e03150050500303240713418204100d414a401d80a0002d60303001600085c00000507502d000403a6100300c4811450510754218550240002c4000001c140d44901581c0594405134000c2c8500ca01490034242611040d005903808141c0d03a010b020820320f80080541442401490080740466440c80428107100055440907801e0350000300304000342c0c1d004845550401d4060184180640c9000c50003456400054a4000c0c031355111408955050b1441e0040c0030069084003a41842c0c0360b551070b01030004c4d80b05100e031038080746401c80071034000d40c001e1003541c0c07040380080c010f043c5044ea0290741c0401000001c1c07084048c001549000761909504e403001c1d603c102e01c240c0003040d841c03407440e40c00f81 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 133758 1250 132508 132511
    0xf15020a05060901050a06120503030106030902060408011107060608010b0a03060f02040b070602040e0106050301080a0201030504060e06070207060210020403030507020906030a0c090203040201090909030c02010309081b0102030105090601030204050603070503040204020915030402010206 125
    0x41c000c102300342010b400a1030000c1102e044504074980020640c5142c800102c49100f150701c2a0070713543c2480041480044610700074910188115010400b107a942c802450917075800c0e40d21154005001c1c00c040000c07540513000300030031119081c001880d194503240170200c550030056013911802d0340490140039241003000040e01510303c5060141c01d561600201555400802a0090401d5124000300b070800c0543c0e0423150703121403c01d0642e1403a00d030a40d0001d6944d5581e10611006200c0d0711440045010107100319425282c0581c0c0d0310307261099680a1041002c3c01401082e010f10561104202245408001c03001070072020034056902d08050000501240c000d0300704541091500385000006900280310044581c3c0c203007008200140181070801c80da00484190a0b80403002e0511940310070019401141640c0c0222207001c12611104011404c81c0258018550808402c0000c00c0415003d03001a691140c4000c00c054079003501d407400320340c2407007042104600c0800040103110466030140b0009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 135008 1250 133758 133769
    0x9050307050105040513020c0102040b0703050306010f09060c06050c04080102040f0f060201020322030207090e030a08010e0103020306010303110102090303070804030308070305040c12020103020903030403110306010602070f15020a05060901050a06 108
    0x25061601704000100c10b00880c81035205507903400241004046000c0d01914001c000740584c441d256800da04010300213600c00c540d05400148880c0605510902030170f546826030b000c0340c0d22146070050300c0c0c0c4c41100600d4082d003010b2860805002c0042c031001c1c00d0000708081d0000440c9585410300c0c000c2c502d1450307001601310805590060003007203803000c0d0220a803100d00c40d007010ba40b0f80b040c9842c10180c0c180103c40d04003d4983e0f040415021681d10700000501c824001a552050540c4e660000c0300003000003800001d605402c001c004001107403081c01c1d1044a114070700001850020001c00180ca582e200d800200c41b00080428104203241e04001c11a40c04003040c2024080b5240c5913a9841c00c810460003520904840d0710206019a442941a21a0040c0107000c0782d50f115104c3c14405d5252212007021486441010004101240702098003030444401c3c5c080420076604040c01d030004011000711120442c840d100c1c0030000b14034200a040d0240f9105400050513003081202e5400b40c44034bc2d0800c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 136258 1250 135008 135017
    0x30d02060705070305070206070c030b06030c0105070503071101140408010603030e0405060f06030c070602030109020d0506010507030203030103020405060d0b07090501020106080102090306010b0702010905090901020307080a0501060206040b0a06090606090503070501 116
    0x10411240c0e0041c085500c3c0c55403601c2c20350380e2805c0900c00607046000c0c40d0742c003402c080c018030310100400640c18880e5000d58421001c5a421115003001103e2500c205035008001d038106000807000218084001c00200c03405050104081101540149542d045a8001480c80e034403060100241070300010f1034004090203580070b1100d407801b0404180f804807507940d0240201e20000020300f220103020251062568040f03020345da6540e491050002a402030b458024000e032400000c81c24540c010b10407119926456000f0b1070a6a10b140c0801004000090031a9040110f000e185800200e5100f4014414992a110000c116061030002802c584468220300220303071040116a6441d500014900e04594140040d181c0d902c1041c40126101c4480f54003854006882a05010f10000190051071207400300c0c4c0c2e6643ca256443c040796105a40c1c0038450840540c000c01d001c940401c84012445920464416010680642d200b0310fa4040790aa60301050006001d01e030144417620b42440010018002460b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 137508 1250 136258 136261
    0x30f09060804030c0302030c0703030207030203060109090c030b060a0504020304030c03020606010e0105180f03010204030506010317040302090105040e0111040801060303080108011103010e0702010e0706030203040204050901050405030904020702010207030605040302030405030d0206 123
    0x8050070300300d0007070405014000614181001c052080003201d503500c0910701500d040741c0d520314020303556108c0c0b408101d20034001c1c500003040070300b40c5100f15850701d0303001290110014030399143d00240660203880150031110314000400d040d1228001180243c1c444d41c4c0300d110b031104c54100241003500103000c00d8100401c03101031034416a40501960084030a9402a0b100303410b501e000200012070b003480203501940080b07400800c0c0640815000e0490b0302030100c2808415800c281005c00713100e140402907100368031200502850420380d0203008010a038100000c0d08880c0c0d03070f502d18034503001540642c100d42e450300400d00c10941d215031201c0c01000848001d01100c0a10030b0705486d1400705018280c49150803500050010f8030035004029510300344420748c2e00e001d80b02e020040180d80200c8041e4003a908000214034034007014842d0070310580c3c00202460030400480d04000195004030001c0e0704506c506117010010803124812507014921940066549a2030441454180401d141c940030a64001e81e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 138758 1250 137508 137519
    0xb01020f0c040216020907030204060906030203010302060f0307020c04050108030a02010608010b060702040b03100203010f06030501080307020d03030b0103060306110403050d0503040308011202010909020c0607030e030705030414030703050d020307030f09 111
    0x1000c0300145411a005a100c40490051000e01312590101950105410080c81842d0360158001d01c2540c0b4241d54035600c403034036510103030281d100a00c8020342010301048904440b0131144e0140d80c02c240680705990101b00e00000080a0b950282c10544d0b4582001804242164091040d00020202c1c0b800034001c1e4840c0e8000290315004128006e40500e44420b0482801e0b0380c18098a4540407080f41c0c11500c95071150340207451a00d4600800300400c0c6841c0012440600000594403250741c0100004c0740080b0b03c0c0d03001c07405040f400c1140d034141500c1c1c1d60084001651070040503214403820740e0300e645403403030350414600e000119007282091010810a000100758000f106070f0641c0c8003c02d1a06849449100480326a680c039440f11030a41c0c070110b408111841c001c12224041d0502d56018070902601c4110310b80c803403142031030041480d0300410080002800c0d680c400c0c400f00030f006003510809541ca8030349500313001d00ca0014500682000a24400301500a10500051901403410f038102d1801d10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 140008 1250 138758 138763
    0x2160504020306010c02090703050406050c030906070e0303040504060303080901110405060301090c050d050403020c01090503070602030901030902030a020301020309030d14010605041205010609060611061605040b07030903020307030b06040b01020f 108
    0x900446014a40001c0000c007030740d001e2509800c080c0e41c050030310511813070b0607400100280f00c1500d0460749582464045216003040701e00b03480c00307062250064401500e420b035098441c512100c0d6942e40501052200080e0303996188204c100460190b00c82006600d07059007903c1c02c581c0c0311120301d034949005000034442d136112041602e055400018001038413168484050b500344c047c0da40d03000f00007801c1200300700c2015800304151000c0d981c20f80b6440002501c0380205501c850345405030380016407040c4506401584640c0160341228005429103800501e640c008c21309980c412a101006a4000903400220013100e1050025003001500f800b2410750400700c0003401e511541c030030704080c0081e8251074428040203501c400c3c01040072004c10000350b81d489001610325001c4458011041c0900ca00050034680400728101e81108641c1e00d46140c00d080050041d85038100d401d0690400150703060204c0141c40c1007040c440610f0107020044118a1b103030b020071082d5544d480c0c0160454020b038281d805240b500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 141258 1250 140008 140053
    0x903040303080405010605090109020d0507030b0303030a0911030313050a0602010b01020c010302070809030601090501060e03010207020a050105030405030f030108030316020a02030a02010302030a0906060306020a0806030706050307050307030204080a0614010602 114
    0x261405000b90746803800c1150142182d50011544110844000980500c15600501c255584c1c1c60b4140300b650b40303044095003151802c1c800b241e01600200009511002160304c094030552040c0300b040d01c24000303400482d00d550070404140c401c42c04c0100d07040c040382c60710403040001080c40384000c1c000e050f40703040005e4272071020414040c140340d000301e01c240802c200c02040c0c640450307025049580d55070351840180003030002031050402080006801c1c0004e8141030088900c1c1540240600500380d1801c00119940d0b4001082600c0c98041440040e000c40d024030300a60007000d4010041d6200d0030002e995100402d421800308056521505420300162400309807001c5071502428016126650b002e44600034204900000b081d09140c41e5002c0f0401581740d000d04840341c000d603a2401142d803541c0034950303507081900a0801088090001400380c1e8454001540d02c500540343c003500b41661602414501805031500719030b210b0300c0b4120041c8425031180d05034011700b0f00b84001c104d44404610700040d003010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 142508 1250 141258 141263
    0x403030203040e10080a030309060506060f040b0d1103040303090203070501030e0606010f03020405040606080a050109020307051204050109020904050a0201030f06050105040501030207020604030203060712060509010501080a09020d05030d06031104020309030403 114
    0xe8000c001134101202036060401444a60103441e454642854014010300800100f110745a1070103010800c141840c806a90504000030400707440c081c00c0142540864203d140b4942c400c41e00d81c42c401032402030080203035000324807030740b40840e0707680b554070400d8142ba00d9504124101468130390b410800100016500b034015400b07003003000c2134201d00f0000710042c0c031035600b25a81190601d08006036990340300d03d40760310030502c1d40810441c60b40c9826010f0107070301c0161910b100003a41070003c8030000301c101c0b84042d04180300740c5c00000c4a184640c080344c00c2d0041110b0642e1070360080c205041c15540c1502036908522003c0c0003c100f0356062000192083c02a030040c0c6041684c0842d0003070454944c14100c0c0e01440d0028110343d214900200c0003020261000300481450307080100002d6503092040c0424140d0320140c440301c0329030b40c03a114450300401c2080004e0740c1c044a0050b034900818404c1c0010404103d6400380030844908600f40b405041c500d9a00640c00745204000304034002d070010095a05403076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 143758 1250 142508 142529
    0x140102030403050306120705040606050408010b0604080a020108070504030203010603030503090c0306070f0c02130203090102040302150a0909020c0102070f051e060103020307051002030c01020d020d0605010806010c0b06010c081305010305010803040303020304 113
    0x15044040c807403600c003a582000e90400e2800ae408207204d50004041c02c115205030001788520503810003403100034040e520400640758000b0050000641c0034240302d95200c0d19901d4403500b0141da90700040c0c03c3da4500e50058021075000014085480e8041c0b1440c440348409800030161800d200c0402017aa2810311410410480742d000e105085541d0000752229036601c50300155141e0510b030090500030f5203d840304a11807040f0143c11002503215000b41c508000464403059031441c5001511400b079408150a180b055500704211000103001001000403d40190014181031116a0614204040c40311101c00b50360b010000400041e600000d07610142d81b03090310790000110754410141d21f54000c0d0040071440d5400030540e21180344456003d8050b84200c007000b80300c241d6407a401034480c1c90040d50321600282d006d5200f800460541c40c0d4441e0400418175202510586a403200e10081c1c010030004280010540720800040d07900d80240c0e809442107201844c03800703142d035030043c4d683d2080e1322500721000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 145008 1250 143758 143779
    0x606090b030a03030506010c0503030a050709050102120405060d060305030307030605040f02040f090902030304030b010e070801090506060702010c020f0409060204050906030303090a0f020102010b120f01050c0309070902030903130e0103140102030403050306 112
    0x87e4072600e9004815071740b10048030f8036401c0a64680c8042d000c12140080082c400100003d1203620014000b01c24840c640e0042d0314041c2008184080b5901040183c035817552075607000000a68104001e51003242d15035030001e0882e0030502004107036440010102901401480140105240490715800321000e541002039031240c984040313419030003260310203080c8501480000551101d1002254454610b0760746001c1e990f070b00d0b4200382044500513145150840381c2480800015402007580c00c007214001400030701c0c405040400a17080d034200b02000c440307140d0046000c0100303060114015412483c2240914250b00d440d1882c1ca0344c400d2a900041d04242003202d0480959000703610000b80001e0140800d10080101c803c81c55441c0f403e00c01d240c0d1a9840c0c400040c000c0900720043d40d0213000000060300ea401d01e0310701180007030b4002034840301803400300304500d41407408154032280041032241c090383c0c030790741c90741c00d181ba4000b0748032000860341c0e40104200700c00250b1000860f60b1003c400c80d41110078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 146258 1250 145008 145021
    0x50103090c05090405030309060a0c09030807020103090501050109020901020708010e03090910030206040b030601020f010603080301090903020f0106060e01020607020105070503040204050405030904050a0615020703080403110303070813030606090b030a030305 113
    0x180d82d40001d4100f01580180014000e0100003144201410300840b402911a01c80020480362040300540005081442c1840080c0d500070041201900500d004600210359440c0c2500b190380a0744000212540043e20718515601440306100400342c0c0c5000304417182c45202c4094883c403130303079960078031030b03076140b000281d02403004004040a140c024040588440d00c802c901c00160740f09540490162041400d2080d80c1c030814002c038815241c0c40500e843c2140d01c0c102510b4080c2080300740490030742c0075040518401e143d003440b0b102c00a03c0c00359164a03440700e121002a007410f8024114008590414042120ae01c2c0c06ca8116508640d05550003c0c003540e03075080040c03c0d40610065268403509107818040c0c12166134015605030303100941c1d088070b400407070030041e40e68082e6407000600c0340400b8031080010461242c0d2070558520090140e07441c20401d680c1d00c02d00d41c0d20002d000d01c881c560380310301802449038a200303000c041e1150700e50821490350008002580c8200001000b0101911440001c12 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 147508 1250 146258 146273
    0x302030c0708030c03010f05040203070c0303050604060302030a050c010305010609080606010f050403050d0801090b0102030c060406020c0111040303020706030c0509030c09090102040b040b04030b090a0206030103120e060703050903010605060c030405010309 112
    0x700d182c208448a4032420100d00007401d50703000384507182c0391000e01640400c140c98035108480c0a00c05603103070914000983c5e1b074141c0240900074515640140d40c0c202c0080135807424000d02c1040391150018001c0440c006c00050200c41040e005001004140c0000384006000010495082002400c010740c40a043c18000c495912540d00300401e00ccc0200320041e45925000201c643c1a01c0c4820000c2c80705400d0000120307a00e018440300200c00380e00160200f00410078580c0105100318150001250760b900400c100700095000364000c50040e4071100c0204000c13a41445080c1d0100601d10b4940c0c540b884402c002581c82d00c0300e6110302c2c0f1507607450021a6050301d00758111402001107144090312155910140481c9412612047d5184028500082c9400d140802d412508a88c0140410b0451b400c50320754844000c01d100e40c0300140007040d200d01400e50b407560302808002c1d01c00d540c0c03e5603541c010001d25003503c040b580301074042c0e4014440c8070308084011094405807502880d0000b00943d0500741b105 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 148758 1250 147508 147517
    0xc050109080a02010509010b01020c0303090f030c0603070206090601060905090402060307030b040e010b0f03070b0301030b07020102040810060305011404080a0e0609130902030d080603030403020409020609030708010507090602030c06070302030c 107
    0x41000704009060101c850701900068850040d0758020002043e0140042e602c0c1e1640d410b065906810402040c0118074003100030140b15400a012600d04100400125506030310980e030101c0541d100380d0800800400400049002d010a072819100b003601d0400407034511500984000c0c8500c4012000580781c500c40c1d806802c604500400c14081104021000307802402e4860850340544100141d100150500048440880b00c0100c3c841d0f1550b80b9546440704003080c040d080d5400c6540070003000070b020b82e08108141701400030030400100300c0d19502d012400c5817001881b405000907403c007004042808841940c940440d90b0074000030b42565000050124451000c010b54804011030310700040e4101c03a0310101c501c034800d40840d004074208540990f11044121402d41c1d155104100c14001410301e9088525070320b202a1400b401c0c120003900090400a15402c07104950b1f40d030700308000b034040c2d10041d088028402070001d54030302500001019100c541c000d003520241600000401e03060410131003203e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 150008 1250 148758 148763
    0x4060f05040b01080709050105030a03030b01050c060a02040509010602010b1e01020a0c0801050405010501080303010f090902010306030602030a05040507060509060301050d080705060103050c030105010605040501020a03030507030f020408010203040b09030301030c060c050109 120
    0x41186140520b000b8003080000c4c0101d0403288100d4070040707440c006c18810300381a00c2d0018000e0a007150250b03001c901074880c2000150422009010b50395007681704014241c00740080500168845040c14140403040005a100808680c1801020b0755a602c1d04a040c044004540028145001d000720050f85080980c110041114032500c8000a1814042d4820360265104078000d21150366240380b00d070783e00d00081c001d409000c0d01c894070400c01c410450703015043c114810b05000c00c145641342c071140d0481e00304541c81c8402c151201c00300010004244070340e002821a6007000d5042c01c809001041c6c00b40414060b80d80102c3c2c4c822030003014130a110303003520300c11603100c411966079684a140107a2a00700b581010340c0690300b803500101d662030003001618241c0e1810390061142c0d0045440440103040003601c808140340d9500740c05221000180005c04c085e000d500005652810185001c451440008000302d41c550018001800003d24100a03201100e0f20b07450310380e46002e40d90074003a0041030329a500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 151258 1250 150008 150011
    0x1110705030a030201020c06060901030302060a0f1103010b0702010801050603010f05060304020301060b07030f030605010c0b0705130510030209010206060409050307030c110402070303090201020f07030b0106140408010203010303020c090a0c0503010303050304060f 115
    0xc0b002010340c15001400d02801400568a0607280c56007401802c1b02c00b130000402507008140041d0180c01c03aa80460320360b800b031301d2012482100b51001100154420382208250085c005101015941c0207800c0742e00401c0251a62855076140c0720b88892401c0050041c14420400000880c095550075080400601404000d26607a0380700c1307103000741420000ca140f4201081c104000003950358061406854016040684003800d075948080484980d840181c840d060780101e030324003140d662600d808080e281070080d20f0041e690744e0800006464000010080351003242000400800503501105035113003a6450304020410a001d071a00840510805040540052011910009140e81030308030366440b6000307809503410010194011510740307400d40405442c42c80c00d90010041c2c0c038450000c24500c200b0388440305042a80780c2061509992081c0c0c020f80c01a840004d9116462a245c8180390b007042c629a41080b95000744c040180c0140414030000d428000084001014004203400c01306200100c80c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 152508 1250 151258 151273
    0x20c0301060914010801060302010507020402071a0702030a090504060305030403120c0609050102070b010501050711010e010e03010207060b01030c020706020601120206070503030403080403030b01020309030604020603040305040803030a0902030d0305010b07020111070503 118
    0x981008120001c2808100c420383d8000060090041c8500000da0350107a413000d21f028050380034000030390302040c0100c0360340420760100241d202100b540b650180e0031070380c050f540e91710401c0c00040c40d078101070300301e14840c51030041c0802c00103100000303ca003181e0380060403070764a50080d901038550b900034100c0504011f06120030a81001810342c000c1c45400e12400300740c02c0740e0b620741c40111054003500b200140040400c01e0301c0742081d0300401c2c050f1a034520501d81500c1c0804240c012a09a81000c030040758041e07114043e400f003d42e018020b1010300482c80c03008009003860498020b5903004107102e4070801d004a40040415520307030900701c034215a0082d003242e5076400c007807130f00400c075200803681035001901d032140891641d84040f040341c4064100130700403c0d29840b2602006640c2d40090011000d200701044000380c81982030020b0b51040f1070317201c00000c3c2d45080b40141400d014071b1090030783c10545002c0060164003400c00c1a1501d070b64080c1782c0700c00404041c0c641140703001050340210354140308500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 153758 1250 152508 152519
    0xf0c1b03040302030709061404090602090d030c020301050105060906040303050306010e040603050309030d0302030105061c1407020a030906020102041d0402040b030303010f0501090b030402010206010509040305070c0303120507080105030309010f020c030106 112
    0x400c02c8900c260102c580c40c5031b03501d007208115441401081c1540c40b9020400150b0300c1c250b00021031046c02414014504034040b00010203101805908a006c6644018000250319081c4580c41c014001950740c540f81005000001781c01d48120b0200609018002c0701188140c1d1245201c001104009041000740702e8a0b402c10030b6580d04542501d501c0392040e54507250700c10b4442d00a89049070030107040c003820300c080c1030001c3c102c001f0f020b1001d100c050360350203040c1d5801c81c0071245180101400e4010b89102401800c0042030703119030b600000d0079a8010042009541164050741d694000015858512a01d40d40300140180802075101c66052001000110b4034521110000c0111303502600d078450940e94480c16080c0b20b0100b10b8020b070145e00610010016401c111072038907805407003803902620746102c0b40d0f12080003000c00c2c0c0099000a40d01c900714880000203125a58019080c0d090115181d85000700083d543c1c41840d400504014002d5004030500d8002c00c86820400d100800901000f034440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 155008 1250 153758 153763
    0x9100201060b0a0504030605130302030f070302010b0409080405010908030703020c040506010c0b01030b010503010e0a0b04030e0a0803040b0702090603060405060601050a020708010e010b01020d08070503010303030207080d0203130201030608010b0105030f0c1b 113
    0x6d000982e54607140101043d03580c9488400900c08540c140c01440c20680c503100a4542034014203026070039035481c1c02000c190703991903124581007144213030130003a142c030704060004002402c80d4002c0359040e8000c10024002c00d4000030b099060010031500450556500300040300c90143c20007000b07086c00130010001c03007005156102c0505980c0282c0c002c10100e14030440050740c903200c1c031078060000007032440420042031041691100c2100040d144420055880305400d14692080d03109410a100110310001145026030301caa81000d0110002d00203400c1c540c491540351140a4613550500400103171a201c218001d00c160001401054000c01c500b9003603900043c0a031091464281c01800383d440c0110055010b100c8980c01030030706981c2c2c00c4c11a8290395040e00298082041944c42d0700d0b00340001581d24540e4002544200007140425031441e24910002d400d41d091034209400b01d074100140b82019076480350560760f000030301c00c050440e40d0b1211074500780e141c4540c29000414565a000c44003211900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 156258 1250 155008 155017
    0x613050102060601051e0306040204050a090501090b04022b0e01020c01050108060604020703020d030504020105040302090403020d030605030601050609010806040e0604050a050706020102031303050702040b090a06050301050a0203040809100201060b0a05 110
    0xa070250b803800d98452004440a01c582035101c02c2e61842c4628599503510341e84043e550045014200516041c1c4440000741c42800c0c0c3d0380407007419038440005002c0d080071400762040e0300c0001da40541c10442c040000c9044810002c001c4424030314060002e850b01c00113504003402c0b1402e07260085550302034482c040c50180100f4002c28a0074800c080c003103412800c082c42180d00301c80d01540a410001681201203001d404050016410010b06210120259862a91050040d0300c25001071070a15007540010b400c0c3d0700c090340714610035004440108550b0300c54004403050a01c00f4a170102c2d10ba90341f10001801060b41c029600440e01c245010001000000224180f03181c0c0110115076000b5642c2d10228240d1104640d0300c00c12070f08103048140001c1c0100c01400ca400d00c004c1c00031030303a00d0082000c00d03a192011114181850788510301002181420b00c00c844d0420b488400551442c5400d8544c1c5c28644170b188049409000740c6026910154802c0d0320840281c011904000d640714a0b60078010202c1c3c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 157508 1250 156258 156269
    0x1080a02030c03030a0c020108090f06010b030702060601020106030302060105010302090402070b040309030b0a020301060903030e04020c010e0601061704050309010810080304060206040201030609050402090402061309050901020a0f08011805040309050613 111
    0x164070002c1c646190000648044c1c0c182540e564403d180355500441c1c1d0304001500c4c1071140d104082c02000c00c200e090010901804030350310791a883e1701d00340000a05d840e03070180070340d07040d64500403007800807950210f03007241500c03000c0c2405030381d480b140340c0031800902c02c80c040038004c1018070b0240810103600641d00011a07000c1c1d0341c4480151a40c484a0080348000e1090350042601e0920800010707005550341c01c41c3d080c0050006040c050b0032031a02c0d09403440800c076000e468205030300510003680c104440309211a0038881c01d220350314080e40c400e0b41c0c2e4415100780e1b40c18031404000189410f80c80b13210040180c0b03250400d0380c1d00c45540701c10295441e44240c90490200e030400e00e02150815140c0b1500d0311135a002005101d140e1500d40038442544d000200200c915040550045881012400340034020542c06000503a03513910800700910b81014003d40c441080541c01c0104000000e903441408800b42e61100010b1799161303454160746480f40b540c0200d0300031501007031840491030300c0ea50b45403c440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 158758 1250 157508 157513
    0x314060703050105010810120305070602030703050403020607050406091403070506070b0402010305060d050c04090501020904060e0901060812030c0906040302041409010c03020406050d0203040507030b010b0403061505010905010518040501080a0203 108
    0x341c81c1c10055400b0780f0115600d20f004055042d0408c07040e2920301000c001c240c003d0610603d0070030311703403254001c0c0e9004551080100c0d84607000d02c0700700b507810041c8a9100c0541d2501c0d078102030401a0007004224144038010484e520840d81c02c009039002e20003480240b50051102d40d6640703a03494031035002c25084605038003003440e1100050050600d0645103a10903400f0001d085200c802c942004024008840705a401350740c00c0c0a030800700d4580340300e00d00203410144036034421840c0c0743c00102d003516a590400a400e8000b00c40142840003084140e0b5000a00039084c40d441e51000d0740030034028059079101940c801e0904090075501c0c1c007100ba0650045640c04000d10071b0f00401c81c402d4042e4072807071190b100028001c12403c2441c246941c0a0342c1c0051240c403d0b5206140d0f00e4407251500c0c4030a800520036080c0c001010400c1180b14482c041003000140c9165145626050000c1d0502c0c1d52481041d061020000d210400840044050040d0b410002c008214a584170030f03681d991031017003e908038001d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 160008 1250 158758 158761
    0x8010605040b0114030a060e01060207030b06030102040302030c010807030207050102120103030e09010305060109090204090203030a03050702070e060105090409031b03020705030106050103021303080903071203020a060b090702070e070207031406070305 110
    0xc1c20700e401804800362060f1a018012400c115100000d9031006000700d4400c1e503115004240d1030801c42400d8000c048540c028180c150950500100424010b807800f40700380c0c410401040140c50100e9040d146800900f80450b031360f558603070141c010303100c0d01d400103003554800a84204225903400107181624045d56440d820380c8003143c00d001014800303000141ca254450f0300100500101a04150342c000c0c8043c2002c10345403a03035404280b45402150040022a40355070421001650401c5444028500016001c1c0d85041010000c2e0484c0302d180b102d140244e40311202c00302858014182104641c0c8000c00110504001c0e0400035250703200c0e405254030035401c0c482c00040c29032090090350340103802c01d0404030350186955188000e582c130070321038160180203c5200044030803200e241d40c92414080e401030325881690340b038003c08480520b513200e0310400b144010f106c0d13001c2e4005403140a5a04c2c200354548244c8440005901d0145260300040060010000100404002069050159445403424406c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 161258 1250 160008 160019
    0x507030b07020d02060a1104050402070f03080603030403080406080601110d020a0201080a0606020309040c020106080601060503060306010501050301080604020d06110408010e060907030305070305070c03021c050607050309070302090c0c01020301030c080106 112
    0x480904000f181c0059024402040124540390721404106854491952601e640c03000460266000090f0a446c200c0c0d01039100c501b03064106401030b600000803009507140900f1545c0326000c50246000d040104a45000006c070300307902402240450100c1007040f182c1068800f00025a0303025071070402c071b000424400104aa01606c0d000c1c050035100c054000c2d5040054040c1440018445900c404085640360380c0d0000d11140180525806030000b41d4440d6aa860104249490702006a03c514100002080108802c000c041030054225a0407290490040302c0c40c1040d07006000400c441c50000c1000050000306003d055100401002101c01501d40315560305011716110701c03040c840070700402e408101130000217200d40c0040a2a070301c61070017054600c0e1640c002c10030032000d0340c40d40150036211a03054400d10000308400344c1d00989500d4010301e107103072140000740c68200c1c80c03000900a44001000c1907440c000203003500d0884e00040000c54032036035241004208901140f0500c003043d444c2001c00b00701d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 162508 1250 161258 161263
    0xc01020309030a0803060a030b010f0819020105040303030b0406210c0509060a03120302040803030106050c01050f0103020f040c0c02030105040501050106110c090106080604090203010906020307021005010315020a05070b01030507030b0702 104
    0x2051100401070b21a03140580c6800d00720f544006c080707c2d030105e0001e2000c8005104844001d02030080449401c90040c1803400503407402070401e9403c110007552404810050ba88441140c041d203a1624000c43c030582c9400219010708030a82180d80c0000c10000117800d4040046903000b8054001c07426082c005d41d9403000c1c0f0220f048107607159a041025000e040c40403030890500d03085420524500149404d079200c0b251415038100382c002c1400110700080c541c0c200882401130542007400d04442200039451070b03000a081d046a441100d0040c2e44801c032540045d400303500340d9094142c002c0c001703100d185010728101c0e00a0609010722004030f001d4210a42030044001b0310101d0028029044031400e034200320082d110036034010101940036444403151740058400707004080380288110790240c0c80342800180a800d1800c0154010240c80c50003004001003418107082c192008800540103a0b40d48551000300d074940705981c0c000e003e5400743d60000080010009446040386e0041308001460313107603030f0000c81c2c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 163758 1250 162508 162517
    0x40b04050906040210090306090302030304060e0303090d0f020102041208030103050d020607050306011805030a060603060501090209010504170111030108030408010c050a050306040b0303040503010f02040e01050402070203060403030b040603060504080703020c010203 116
    0x1e1099000e90001801404c0002d040c001c085068100744071a03e81ea540c1c1c43c03080d079200306400c400680010050100b0002c440c000c101103139140d20061425847e120700325550f20103c040c03802c0708208800220b4043c40d0b00070b6045901605054024030000880f9090042c3d07207a00c20700c42100c403842440140c04810788085a994040d0030655140303485c44c0c82d01401114a0141c811007542c03800140369002809517400c10165018911804001c90301c240f070342c2401c104443c8142e101c000224010480146c03a683d04c00210303019103076540441c261045d01c42c82154010b001010303030800380f0031000001045280000016004445101000380700f000c0e10050102c0c7c8078000d0071010004a8000c0c4003090007440c094000c403051030320107811641016660000242500e10000390300d01c1c200d0307001a06112004050840314050074003a2429840c0040c6540826680d500050019040598682050429a603142c222900954000b0303801d008600f45814224400e502004d000c0300548104140384a00d0750001c410740e0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 165008 1250 163758 163771
    0x50103021201060c0515090615010305060a09020c070b03090307050d020102090603061309050d030b0102060105030d05030403080a060504060608010503010b040504050c010f020a0209070306080607020102030103170904090605010303030b040b0405 107
    0x18407036900c0c0a2041da04282c04030f03c00c580c00c0c01014180c816840c14010210320918044008001b507041074860504140301004085040601300700c100101c035101c07504001e0444903000b00c016550701e24075041a041080c0f42c2c00c000f001d000000b00340300401310000701800980c1d0140d819102c1a51095400364202d20070000c0160b08242c0c1400010384a107400c00c603c503060f10900e01c011480030707116516a402c107811550220046036a40703600c02c4682d681004040e0140005600401d4444400540903010340400ae0000f003c00c25150001101200705400c0400148000b81082c400d254540001420b08002406028040d42c82c0c02130b00d02c020715050041f1402150040c1c05040380041800c011100c410412051500f07500c03c000b603220060300c42c0e00b00f00b44036548940d0000b502d24102030183c0d0074800080c0c46001168011700041c8046441b41c1d400300c2820880341e0540780e4500300b500200c0c02401c40200003811952074840000141a00354001e540964422541040200d000c40c0410040301d09c2130f10305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 166258 1250 165008 165037
    0x40807060509060903070603021809090a060203040f0b0703050f0702030a0c020603060a0f0e0103020102010e03071203050601090503010504030206100503030403031403040206090306070201090314070209040b04060e0f0703020a05010302 103
    0x810040d801100200b20002c00602100c0c07510f500c00022a2814130182d124200191f80050207200c4c001415070100d40194044034810702c079040281c1a030359140700860f4040e00890f4000086410010f6540401c502d459220f014010b0030701c0c2411001c0d00801084442c0240741d030300440090821880070048507050051a25040110308042c1c090100c140c00003040c40b608807540880114040c01c00c3c55000e0014070311080b60b00c4032503040d84002400e40d030986e200c0700e0300c0d40e105010b89000140000700d01d4003c9045450b00098640e203840c0101e0740c068580e40030345e405510302020702081c15400300750584910b51000788551fa080ea80c4c0213040d560310079840003800207882c8403107486030132070090000c5401034002000b4030304001066000a04094095801c000540c3d590b9818a04040d001004c0c0042a000076420794103025003034021952604c0010402001c100f2154001420007249a000309004036000e01201d0300b2401984296903a00303120300003a88100e201d42000070b00b541c402d00881d41d001c100740c0e91 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 167508 1250 166258 166273
    0x1903080f04060b030102040305030706140105060301140103060e040803070207050f01020304060302030a020403050102040b04030309090605130203040201020109080408011401080a05070501050706020403020301020d02030a1b08070e06040302030f0303010f0801020408 116
    0x18280c80303150251049078490345640409030b056400b4005030014600034406140d4807441840c081080360f0f0560782d1620012481d00040001c3d5a0304e2003580d0454103c003000c070034000ca54000480040c0002e0300b11800703040454007840f090000c041c014600c900515002c94098644034000c0050310b00002101e540164000c002c1442040d11980140d900551622005420203860790f4415003641c0080c3c0180d400804082030800c249a40141c0080003094030380c2041103400c1c104404154085c02e00c680c01c10081350004041003c591003580030032849504407040d940c440c1e0715040c1180c0600700e582944800f107021600081401000880c22400c031650210003000154074000040d076054111801c00d03a4060340c20300001000da00e0a00003030456480c0d4050050341c9191140b050b004076586440240e00c010410389c50003000a030003520361a001a014245a070364920301c3c90000304588a01d030402501409003054503004018008041d6060340d07c503101c400f00d010f468454041c200d0043e4881c016650784440c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 168758 1250 167508 167521
    0x180b06040903030603080a020f060106080114090403020c040509030301080c09130308040f0602040305030a080702150408090a0306020c030403050d08091203060402040305011a040b0103060609090e03070b04030201050702190308 99
    0x1807007604000d10904012034042c2e600c0c0c50384807403170300118008000344e0048003403110200020702c0a60f024041c01e0030b128805505080203032240080304000070703003e103260f0400b2406150081140c04403c10000300107011510300110ba45031a60028803820525100700c5030031980c0c9280c26075045100700c002200fa40302d50348098804890000700580191a843c0300c0c0001e610220390603000801c09107000300021a69240c00e24801440e103a40248004119000580084c00c003228140344a40c00580004034151640032a00004910340701562008060a10004d1564403164000c0081e1084a0240c010740340064090002a280c0b020212554034030f94119400c1c3d85412191100519004100900014103043d20b070b956032402c41e003090107111407003920755803034410a00d05400760b84800341e8203180500440346011f0020f020100701d80181e080a03030f01e8103259915448204241c80350241c000c2c3d010741d110300305401d001e802084c0a840c030360b00501403225803040d5903500c0012441100d41c5075499001941c2c954 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 170008 1250 168758 168761
    0x9030509040906020f0304030207030209010f08030304030e0303040801090c080105070302040503030a080408070b040b04020306070f09050d0204090206030103030c0c0503010b0109090209040b09070207050102070f050102060711030c06010303090306180b0604 112
    0x1603400c0f01c0752075081c080c0c11010a1000041c621951184e00208501429030041240c0f00c20140e01070088880f0014050001d101c0200940c1e400981c1410702c60301030f0300502e001078118000c40d0004800d1307601c2e200040040c010290741d41000c50744010000c0081e621440d00c1142a0300c81d5000303103500340d8010450f600c00c4d81d00c83d110040d44503015110ba20b08100e82036403015800c03001900c5c1a5a035007124028041589024400070750040858280511942d095001c00381020300d40d440b64500c02c91107828000250341702e5801540ca010750082500f81d0f07a40c0c40340b402401c0403040000c192018001c000000c100c0f4201441225010507058403403848191400c0c05943c087c0d8414a825034105488035592207040e200c02c21642d01502458018100050031320000900d801000c1c0c1c03048821410361101001141d8000c105990089007614010b085011100d24203840e621451002110a200e40d100000070b01d54012640000d8a201d20002e00000540803004114512400809040100c0d000003182d00c9103000d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 171258 1250 170008 170021
    0x10915060609030b040501090f0c050102010f0e0606010c0201020703081207020d030b06030408030403050702040c0203030105040f0203060a0b03040309030c0b0306010e030307050d030e0a020306010305010203070e0307060207030204020703050405060d09060501090903050904 119
    0x1c1b000850202c00c50750704c200c4803002c240d00c01c41d131801941070148846e40e0203001d9640c8101d4090401c00080130203000d420341da03800181c003071414807003540307503c400b964070a10440001d140c100d07500a6580303d014109500b03440c421660507005001d1900c4c0300b009a4403e0140080110000308000d055440f207032900180c560010f0000c40902100f004008010f0719180201c80085050350051516076142c00240400d030781d07134007601d00d010a00c100200300700f03076881c64490410746007881c500365180c0d500d61a09a071a4541c50308050719401e0701c00c40c00540e80c501032000b54820340003aa6540082d003c013506040d03580c081c50400600707640110b034504240e04e2095000d0106803000f14201c034002d5038283c001c03e04010007078200b030300d143c0d400001b009003180c0c00c095201e0070035a040d401025910b00c0c0c414000e403100c0c1070303020003413040741c00140760000c2c14816401e98000c0c000042c4010342e2425000307002802801048801c8807001d0800d4000120504688917000046816031242e5281c07071071103410040104034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 172508 1250 171258 171263
    0x4060b01050918010303020105060d080304060504030507020a080a020102070905010602030a0f0207050a09020306041b050403030e04020403060c02060402030f01020c0703030509030106030602040611060603060105060d050402010905060c010915060609030b04 112
    0x80c0b141000d1590ba0807032607180002e0b0200038000c0b81d419070030003e09688009040a00440200c00c564002650781c0c070803650300c9a0041c200040a86607031401700c4451207a03600103507119200c2d4101082d0180082504181d41e4800d80031107110590743c90450b4242c5034240b0551026030018016410014000d905080b103607140d510640f41e2850303d0741c0004440100359007150a100b940403081004505142c4a80090030055045120740050840c0000304284101e0000070104241010a03041503180d58054078003070740c3e021405001420f46000002d40e01c1008030760a0b88a031250521101d01660103100715522006c02d8806400e426066850682c0e03039512003040c00350559a2a400013010414a20141000d070180303a6950358a0304a8241062900e1030150041d40300790400c0b0300400c09030b92100d0440d00c2843c40d05201241c2d90351140016181c03c00d0315400305801110014145440610640c070410007548030303002001190202600101c102c811500580c0d02007040a08240045600d40e140c83d6030081c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 173758 1250 172508 172517
    0x4060c0201020f0106080304060206010504020906090d06060302040f02030405150123010513060201090302070f0501080103030e04021306030b030708010b030303040212190303020403020a0b03070e04050a02040b03040503040305070602030403050604060b01 111
    0x4900304140c05c4807a140c0c4402c8407500040303414011141d050181d68010706086401354102444c0030005000c51003880301d96131040d086c8260503010088c40d50051001550010001c0142d060010f07000340c060b52003141c00711040c1c00782d54581d44600b0701848085042e0b03440900301074103900415640604e05d004520500d414008140550307600916040e141002509143d07001082d110024940645040c4160b0004030b08164941000e2080307036408801c84c4c2c1102e4040c90944240214900818000c2c070410000040103c0706400224406030107421104102c1070507012503181a598140c05400c075241d9145259141e0000c10108001d4030301480c2210708400d001058407401c1c00a41c18500b0f0071716080c42d080b40030903004281081545441c40411008044e01c4140034510300d815180140520341200c2d40300d120360303910700100d0300c500490f9042d42c0142c0407011160703503241803d0802c541c0c1ea401c81e1004030790300c0c07140c1907001c00d02c6803010003030300c1c12030360b02500404c82500d855903800d01a200d811565810007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 175008 1250 173758 173773
    0x1030b0d0506010f080601060503040809040b040b0d030201060608090c030703020603070207080601120312020306010507060903090b0a05030109060504090201080a0c0e06040303080a05060103020306010e0105070602041205030406030c0305060604060c020102 112
    0x1c0c002d000ca10700803e4240ca111000764a05011a824800141d000006009050080002280c001c4084483d0040110303800541ea14601d0000390003441d000350117641124074080e2a00c10103030154062000d9482c191290307000c90359076500b015500c025400c611394064002d031000b040182807510103590003070b0f8140103a8100b903444c4da8a4503d440000d900200507a0391002200c4103042e0030410300f4240070b8140c8800d40c075528040001030051b22441c01c004004654800c0032600381403081cdc00010150a281040a60302d0255400c010070a8000780508500030785800000600b9142512034800c10560607111400e20f941e44981c200c0003081c08501040131b00c004107000504039a1064000e002540c46a1a0740d480ca0402020f2101140e00040000c0d051500c100244100d582e0414080c0b82080000d1034115035440301451301a007c1c0c0a16809295800d0407040d0241c02c100000c0044d0082d0f50080d80c0410121201e114100c0c00c1c2c5406686403500001c041000f0b0000b03030710524060074200d0041c011a40c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 176258 1250 175008 175013
    0x103020702130903050304030305060901030c0311010309050102030901020c0106080106050109050603090703050304090e010b01020d02070504020705070801050a0e0f0a020a0306090503070b0405010f060803090306070503100923060d0b010501030b0d 108
    0x640f20150000c4001034000070400080581600c100341e00018162524500c2e90b04681d5000322448480c0005000c2c00050020b569042e0b00c60740000c40101da12800964483c18041c0409001c2c0d0058081451954200078001c00e0f400d505114240444030142e440c901403e252000744505039002030114002401120700102c04620100020402018010030000384401b03000016401c49070814207050454002241d008400c650005519050759000c072001a9140c02c41c0c5851813914900d94001c0441d54200010403801440d16409030b801c14240c0c105032462410790072031003602d5080065000307502401580043c0040788041d84000c200b940700e02c04603482c240481c2c64010f8440811901242c03035a4680102181000c1c1c9401070070020083c0e24015030034080e90b20000398039804c0c018001020003401000054244c21044c4038000140030b401c50810124180c4034040c010f0342c440c2c180d240c40707000e2203402090300c900749039410102e5242c001040d040c41e031b42004011405064010381d039035448482003003e14007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 177508 1250 176258 176261
    0x61207030b090303040311010203060d02100507020909070609080303011203120207020405180c0301020903030d090302010902060f040f050105030105010c03030e01060b0d050609010501030908030106030506010203040b03010e060102060603070602030702010302070213 116
    0x30180180155240e00d020702c6d0040491550f40c0c03507058980d005000340319040c0ca5040580d98082e6045813121844484847c085445028000380650300c1603e0105115400d800130071007205807140b0365504800207496880c143e03500e1000380705208420464005400110f84540d0000090403000034002d4541800c43d00010705a8600b0303120380c00e07448400160403c0c6400c0412895241c82810b40080d402c03d011000025120b0044031080100203807074030420400c041c400e40c040ca208560041a02d80c9038840030740074003072503000340c0180e40b00a1103451003c120703503014009807030403175005075203800a803016a90300f00c3c050301034283c8214566491712270100d010881c200c060001d040a011000615240c003104004d0b002c80181c0c4203505144ca450001c401080c4140110380c10340742d00703040210750790300d40e140100d156101d20f41c444246000048004981888503241c0300c0e014032002da003250f106845080416072140c21511070500036034810841240194002d8018212050000f04a03081d081c50b05000e00c130 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 178758 1250 177508 177511
    0x2030403060c021c0201051302060304020301020d0203010b030906060103060b03010b07030210050108030a03060e0105010804080a0207090507050705010b010e01080a0b060702030706020307020102150108060703020c0109021806010f0c0b061207030b 108
    0x2c000d070f0084001e401c115000c2c02d200089495079440280054100810840b1900c074203020042e014800020001d019034800750102c0d00c400c0c0d151402156250384d9011881030740e0b0001d6450301c42c00d02901c00480c000390300c603024039400d46941145503172940c1d181c601d0014055018200031411742c010401c1c0f0140443d210f00c90640203008075005103a5aa51000004085031503642081c00c0c0075582000602007641d005805071b80c4183d20880307c0340e07200d4000c0005e910346502588215519400c100400c4102640040a8030289104000074005a030301280152440040816414001469040051130045981d00603450016020388420300c0e113001a00800d0500701d5039007080740540d00008600e011568104903000d0550b58030385540c0304550500200988507000540800300305900425402d40d400800e5109102d515801462110502c1688a0b903002c0702200302c5070780e400300340c1030851420900d01400001300903951128840689517030340340400081d030001848010783c5100d050400300c000b8000e81c0c51103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 179864 1106 178758 178781
    0x3020118080303010303030b0f030309010c02010806010309050a050105010305070803040b070204050406020409020705010606030c03020f03060409050a02030f0303090c04020405030d030504020411070b060301050601020304060207030b06010203040306 109
    0x42490900e660003260490000000010405406500401c4d80040079203e4110f91040b20040580300c0c0078801c0020702003906068650300561041d1145030380242d050500081c1c030589074a2f41840c0c00c1500000b220180c4d525001402448800c0041000518030304c002503141c01d082906140d910302034010b00a008540340c101050800070f4540581307002e0864818219103d080f0707410058040d002d580314080109242241203804640300c1d000f1948c071a900001e8062561301d44400f400000c20702d40000f40c8440c0640c448103401641c09005000725140014020358032030506140350b9040c421030200044c4070f94030400081040340c80c080f0710301300b41d004141000180d40d5a1400820080c21051080f42642e000002d05201003124950446d401b408094000f08059030f03591005907901c4c8281e003d91009640078000070000243d0f00c40300c00b035111406106803400c0540da691070005803000304515 = true := by decide +kernel

theorem cover : BRFrame.Cov 8 179864 := by
  have h0 := BRFrame.cov_init 8
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 8 ≤ n) (h2 : n < 179864) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
