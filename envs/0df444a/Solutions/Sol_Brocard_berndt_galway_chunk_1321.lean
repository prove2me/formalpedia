-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1321
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:21:42.38237+00:00
-- url     : https://prove2.me/submissions/ac4ce1c6-cc15-4195-b0f2-2135aa0d6562

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 237410071 ≤ n < 237589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 237411321 1250 237410071 237410087
    0x14071b030e0333040f14150a0c110304051003090c0f0b0c06090102120a0b03150a0606080903090d080d14240406050a1401030905060a0914120405040e1606 68
    0x9040c03004001e0400c01d80d1041c0c50b0703408a21480c1e01c91085190041c168403828201046c0c0103800e181880b401c1c0c45030601d84480380c5624001c2d01d40207808941034494a0015003500b6502c01142010341c028001001035030340c2c4458803105501141000142da900a060006c1c80795035a4200009250400b40001150381410000303203411008681a52195103400541c20700740d10400400352900c905c0000821518109035204000f9081c0080c00c681751484c85410a190980d011256407400d2507071007404104558102c2e1a069102c036055000d1071801001c0d8000030707801154050007404c200b80210300106130203060f90202e0580000e5200080140c41c00004912104c40c060b030041d80c16400c020f481e00300905160161a06a4a00070512004a403d1a40301081a545038010034105034036080c01402080301031001d40e0140e00020750107d1440c0d00c40c2480c070f6510003000361b03e101c40c0c0d001400301d400c1c030801c00c425035064030b00c100d0740410040000d810703207841c1031580c0031000201e500c044400213800b5000708034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 237412571 1250 237411321 237411373
    0x5131203020a0b01060302040b04150c0605090d0e010e0303180111010204030803012c010b0a21050601140c03030c090d060c020a0215090102030f0d1401080c0414071b030e03 76
    0x2221000da8960705d04900341d0080c0d215600c00c0c400207100c2804940a071581d034003c044140d15104c0b480b8035050f15414155070050b118140a600143d0b20782d00007651041c80c40d5a001802e0a040034640380c0d20000c0390f901c1c86400a6000000c1003403046650b2a07100d13045031284001f00fa002991100d850303044c0440654401c0c80369a082d84034011800c0400b20b81c82d0000c0000601c0c00204403020783c41e0035800350f0103a2000c04c0180c10812942c54522500f502d80340400c5241c55455000681c3d0301d0198005040e001007074446280e13281d0240103641c1704c803e00100302c80c2c0c4441e84c00c082d40c0e220200500442d0790313956091401890340c3d080003e1079980d0f13580003409a9125008442c1c1400f11407055084004503c1507501e00e40c01a0001c1159001804510000740580081d1403c005070046104e108080303200070a8000612681042b1400078140c6401d00806aa0011110301c014150030504c20180ca00c1c890817000c1d455884002c083d040905000f0264080403000203000c0ea09100780c2160f0b40c100603000384903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 237413821 1250 237412571 237412583
    0x504020c060a0f061e08010f0903050a030f11040906080d18120317040501020309070501052115040903020706020c06030f040b100f09021b0304030f03051b01060b09040b030d0e0105131203020a 84
    0x448070112354a50140420454254894501e4400d41b030000301e001d00041d041d01040d854071003440c41d0724404403c0007000203140b07060001840500300080c00e0f08086019041030100f1240c50300079800221500c1a4000b00d4681084170301141066140644464056030f81d10301482100004000c2400300c19001907208100f904180c5520b640c65200548190040d81c0c6440d241c03100c104101c0882c0078041010f1b603040001c811801460800c440c000406542d10150b0850051b040300c00b0410007185c04102012040c1c0341203c5050451901d505060300712800200081c3c242e40140f404501000d04107080840600106121405400e40303601c104c134083d621200100c7c4007600c5c4400c0401c40c105010080d907040c2d9520008480c49024580c504403600c0e00406480f16000c2407103101500305031000d00c1500000c12010311003d1b120078105d0204421140c40ca0006ca0003a0050990008040e600038180400072a09003070103a00e88199115000001000380c000d58203c00038081c04038249a000510640418402c507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 237415071 1250 237413821 237413831
    0x5040c0e0a0e101a150a180504230c040b0a05070201050d05150f09010f05060f0d020c07030308010b030402030601180b190e1f03030c2a08070504020c060a0f061e0801 73
    0x1409000c540c180c405c030a02c0c801c00d0000140301c9110b00965170407004106e16980d1100d440d480000c00329119420b200209e000510314480c0c140b00c0d1003100300e80c41341803907441a04140c0340080e081668810324000b00308100000a6240c11a07018400f5500c80d1581c01500b0070181c9044c0c00110b055158103035082d4030451900f5040301c418a40185480e050301d001817400000c2c80d14040a2286c00e4015075a10741c2000400e00c444070f000507640c8082d2180784010001800e14919504000d0103595040c2c0010f80f10b01010410000941c0303000804904449001800e0140c000d11601d04000a0402c0d03d8800d1744100805000341941d6040450242a00d4034240010340c1c5454412040609048100690070880400001000404e0190054184542c0500308044040310000808050441413080360300d55140d50708014040900b0810041e809000d0503076007140740142e134100c0656074840040c03800c01c07220340300c02131045c0c001003030f070030070310080882d8220703c0b8070034201c24071071070951582c3e000e80c100c01c0d8a00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 237416321 1250 237415071 237415121
    0x1090b0d0f020f03071a0d0f020c0a1502162901050102070e0702070f121104060f0b0d0605041e0f0c090506071407080a0b010905040c0e0a0e10 63
    0x44005506525405400c0e66084051a400e02c018000712000c3c041d0715000c1c50310005030804002507a0b074005201a040c1c03c1c1d65111803840403084804103170755040030610510100340302071800601c40030003c0e005038417055610001803110010b0300c01e200d6848102c0e5812010741040080c0c940d1040101c801c0206080c480b17030558040720b088810244500341c0180e10040381084013001d003401c40f42d04045203105680c802038444200b0000e510f0281c2c407081d00c44109101007400c0c410300c1800322800d8031080b1400e0180314500680c011010040e809491444c460010314110361540552000f0000d0030060300502011818146110801b02900001c0002d43d04010000700298140e0ac51016456030700e4565021440c01e2005109640e040715608440c890054a108980c0000070815007009154201c01403030307850150300e001f0041d0f000c1a8040d144803410b043c1400001070a8910703200c15102c48500e646070641c0c0f170306110b5002e0305103080e250380b1174024034032808040c100341e40104141c42c1c1c0450748501c0a02803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 237417571 1250 237416321 237416329
    0x20040f02192019030e0307030f14060c04060e060405031005012d06080402010512010b0301060207080c0f01030209032103011d190c09080f0601080601050a153501090b 73
    0xb000c81c5460050304807000c140e11500301246642e840c0d5002e86480d4149140d014040303480c0040079041990040715403a006810005a00e65040501c45042d02801460174010013090040c0a103020b10410310640840003c4161581c806907002094001c00321955440542c28042c020071083c000e1003a42d00c902d0001d214211148080254200340032003c01c40c0ba28034041048522100c0508124100041007080000c3e4400600c0f4660280482c2d1511682da549042400781c502003060384212030303130b802446856501d41c3d0b03020f880b0120140e00f070034050f030340d0300106000070f041c01140c0284c40c1a2000c2050304003c50305501c0d0146040c0d5408008848601040d0661041d0042c01150714440c8071260a591724136007030711904900c0e844900c03401c11180c0c40380c95481c242c0c144001000100c4260303100302c1c01000354420802149006000c2941c0c020501130820a5140032004c0d4107000005020b91141030b0001d48071040d12500c00e4084145400c1d0382a0840c00315105406c40a201c0d02c0c5585082c400b80010b1458 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 237418821 1250 237417571 237417617
    0x305070203041a1602061810230309120307050a030c05040b0702040b12070914010e010605030112080f0301090e0601140a050d06090203030c03220320040f0219 70
    0x1480f104490500c8800560b0031145500c41c4405100941050039040d00684444010b0b12505449040b41d10720038146905101201c001455204100b0421854110b25003160070b90000300005c00c11042c603541c0c0e541c41040c2e890040500080c3e41c850100000300014107501c030300500510659a84c0512128141240c00c4440717024030b028418148208100d45801441c10307601401d41c2403405040600001418042c50b403e0680310b610054149840d046082082211144a1405012806140d01065061140c020064001401003170012481032003508240711151060b1001030054001c0b8940d00e41e1a079400e80068000036000c00401d02c940347c00403c0c528400001d0040a20010348001c0841d864207007040a08140360b801034030880d03940c905100258405100030a08941004001d4ae03680100078045512100b038042801030491240c5c400340002601004030300d8105841d5898144009000703c00203004000c0d5510b0300c0300f586d20004800000d00c0600c403925500308519110981c0c80300807c546654420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 237420071 1250 237418821 237418829
    0xd0906020c01051e031f060504180501030f1407030204050114120f0c0105210411100305040305070b040212060106030e16052b0c0b12180d1b020307090b01030507020304 74
    0x180e101d102d80f0354000c803071303000d940c2c0701002d514040f070402e0b10601c103100d42c0e0103660020740004030002828402c1613004104a481e2400c00f0100300459071540e200d030061428800c02c01000085070b184071034070703140080110307a010f103030001c2081129580d6980d110031030003088441180250790f00d202c0142125804144030001d030300500302a015580c0724038011902d65001188807803039082c0707002000c0c0340380d00e03100b00c1c41c1c0c4501d20400d001800080c0e030f40e0030030040550360072100d003c00d4240410040000d6018098407100c0c0d80c07088040c82c45072258400100700c020240302034000f0f48220340000070b1f0113605801c4940040f1041d4166100d5400d0186080c040c03003954003409401030010a21100c00501f6100ba00148081900300c03c0c2032000c0e155100d400114503603124801c04600441d000d04030302d6400b859150440056090f00f0107500400000c0c131b07100c103841000302d81071047e030300305940840f81246454128540c1c024142c80380c0355298480c201c0208180d450030350010703252000240000c0e0001044505803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 237421321 1250 237420071 237420097
    0xc0c1205180f010c051e010b030303101e030803070315080f060c0c1203010311030c01093611040f0e040201020a06020306041803020a02040b041505040207140d0906020c0105 76
    0x41c8440d000307002d55411000c00150410803882d50b12404100140f11104003424451035003903465105050f00d609650ba42e00940b0300c26001002840b80519040341000201c40d5070680300c4080d104080d0102c2d660582903880a006050000308102010b94142d006800ca038000c3c02040880702e46800700a6540d042c448010380165001c00c0100d02c280d200100a440d06654240c110380c0c00d0b4102c58500f1103990003c1c1d00480313106007060400172007850b040c003460300303000000c2c640754041c82d2400400d4203083c0000b00001450b4020104c2400903003061041101000030006030030700c00d050002031248100e900c18841c00d4840341401c103000c5517100383e00c210705001b139805038000c1800e0302407a00c0d544003d5001809159005507155124112205c046400ca0441130207034000d49900e200500611044d9688155551b1040c2d203040c0742e980398604c60144a03001d884055400684804241c502844000040d281d40101c0f4480c0c01d112b80301e9070f9401100c40c0b05482180d401e8580e00d150f16030056980d805415955410f03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 237422571 1250 237421321 237421357
    0xb0f010e07020c090a0e0d050705070e060109180b030105010f1701020301061e030603020a060914040902130b03070b120402010f0c030c03030c230a09080a05030919090c0c1205 77
    0x51131400c107070101d030850324000c3d0005150001900d06494200c0d40005180070a4000c5030354000e000c000c3c4215001401511504a0700c2c0c600030340001d00700c500714000d03130140c0e50409d2124540e100541c0c2c00b50100c1c4902030000c20683d615403018a107044800d11400d1841c1c03d0348001c2c8000c45070103009881c120790007a105c1900311074101c1c507410784402a80028000705641c2c1c0200001585d241842d100c014500c42d01c9650031a41401c08110840140b211103d00070b9052040c0d02006865a8190850084204600041d101c02d43c20000e401c2038503039072040601c982c0104540240f80303040702c41e0314002e5200f40c032001b01500021000381e80c110001f604c003502049100701c101d00400c0c060307044050b400a80c1d2030311011050744039840780102c0b03529030340c0314a101030007140e503034046034101e4460390181044a0082031515001d84e070f102d82d03e04c110607005008510942480c0442000d109100c1d010309a00e800c18004d41000a1b0001d240500302c12003907038001c0c00d5031140c14009002e2021103214044003c030f1024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 237423821 1250 237422571 237422593
    0x14218020702150a030207211e020712051506030a03090905060a0e040b0708010f1a0d02040b0c01020309060106110c0d032a05121c090f0605040b0f010e0702 69
    0x20003500304001c2640c00004510900903030a2441004005104081c0c40040c0c82d52128105131034819025030003548002d2071400310314a0f00340c1203007000e00320011120701100181828003049007004026807100b00c020b8281d82c1c1850401c200412200441441020809e0756641d48504040c0d8a0803480c00150104036460414403260726a900002e03030182014103003085040d0341d05c2c11515a40c03001c581c1602c040fa60352042c0100329500c40c0220b40144803c0f0310700100c040c2031407000311184040c0300c681071030344000250b201e00082858060b20001d0100c685600e0b01c401c1c5c1c0c0b202c0b140c00303135100b2591a01e45014007000130030598000c1c0345000102d40b07a6070081400320005e10512013084079407002a03050000041040098a8801c02090150a100c000b04800948a1f150403441d1040201010111840a0022060f03e2142410500301d49020502c01f0030010182d080602200c2c12419000d4106401c220401c000d210409a240e401210140580e0308903030798400c0450000070013518a240144c100f100362803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 237425071 1250 237423821 237423869
    0x51005090711010209061c05010e01140904050a0507150e04020415050c0703140c041413020d030903060c050a11070501050904020f0c010c0809061509040b04050142 72
    0x10001e00140b00061030142507a0000d401a000352040b141840d208541d644135071141402020b00501b00b00310140e00c59410803001000d1180c07030b06030280c01200705c20002000d2013410041d203d0643e03000f60980d407051b0744030070207081150f40910210b00842c1c1c00c1400000b980c1854400c40c0c01700e80c00e86000d41440c40c0c02420488855010360722501d00b6200f591000310109a9000450068041500040c4503c00e044010b00060f6612000340c8007a61f2000f90402107490009021604855412a8041104040c520f01544e100540e9040070b00081d2801030f00010058202c4010031407100389840c1d00b80c64100d0000036550350030322402140e0004800b40729075520350030550094501c041c1070f550303031078200304403400d0442c00c60707111003260703070010b20b861081c00040320091015580000328104130816046010f000325010240240009040c181050006000c1c00300030b600c207407450a000c15888002008240c0703800c0100c1d40c80c94110204100900d13224a0120001100004030b0f103c1ea12001c903d00a404448 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 237426321 1250 237425071 237425087
    0x30b090f010e07030e010e0601060207152a03140c0105070311090310180611040f3602090907110f010c021b03010209060705150a020403051b041d060405010510050907 73
    0x29045d541d00c8021500c051794040c409039010300b41030750060880a20301900c50104c00380d0500e014007804401d00001020000c0c00e403c999142510191a00203681c01d0714003180c0b0380d40c030340b28034034843c3e840400d948600c04410341100e401455182d42c28803c0c2c00c4a03810b14080762040f583c0c0641d265102e085034040082d250341181005e42d50000716441c855034140c43d498140c0306d151995040703000c0c00003070030701071a048940000041c00340a0002e04020429903030034001d14202c0c00710402d1002148584111060081d0100c400c0b0348006452100c2900704000c01a10140300781141d4841da00804602400c070f0101489884100015903000b071500c186039401140384280c452001580554081024501136181c400060664901c00d40040c48100403800c4034080040d006030484d403c85004000400100b0740c0001c030403100004008480072491200d400060052840e12000e844601079100c40481495001c03403078030301c81d0340182d00034003040e540d4040030740d65020280206079100229902044040b0710500b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 237427571 1250 237426321 237426341
    0x1261e120a030203010e0a05130f020a0b04030b040203010c020303070203071e1403041e0303141317100f181502070b010b03040201020c0405040b0711030904050106030b090f010e0703 80
    0x64449106040d10556030395449222400c0200307800000402c14000d42a0031383c1d0780884214020030490808050305d10801c20240340107000e414036001000f0a555600030703444000c1030f4940b03901d0344d034954903d4000c89441084800782c3c86035103015906010a40044100e0b4815140c643c055442d0031200d9841d402c8443c291a0b0145c14030004880d481d000440340351101803400c80c0b10000b140c4a070b1074440404a15000754030303a100580d40070780c0c0c10000660000c0d00c1c2848410b042210035194203a2240b40c03002036506a00c00200407500081c2038201481c0803c40c4025080880410f11040d10040d41c1c04081c0c5200c8400e8852408a201000010900e0300112800e0b0014440000d4a01070340e60f02d40301d00002c401c0e00b00300600703070000043c041150380410111030111030603101400342e072a160310b94000ca03000007080c5030184064400480000c1205100701e84d0b034800001e000700860b5841c3c440c028010100751040b40d000b185d800c0b000c280d04506c1111329034125000c841d0b80f09401e560b4142d003180a0002001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 237428821 1250 237427571 237427573
    0x80f15060a030f0213030c060e01021e0a230c01030207080708091c030e0f090712050901090c1e0e040b1303092303070b0901090312020304080a080301261e 68
    0x12030000840f05800200441a480359004030300500b5410400c45050a6070300c94010300c0356590402c02166004240403000300c000c042c840c0101d80100c032003141824102200100003842001c4000c450210f43c802c414102c43d0311070100c0d0109800140150100e00c18810f01801e02c10b4240210800210ba03c00200311301c12000d0f10030f948148504003946580c1d040d85038100d000c00c40702410f0060300e051800100c50340e04400c540640e114201604041d2444c000106119525603d6000081e420b040035040211107652141d841d0b10b105954102e644180341061003c01c031030103c0008005a0050b0719021a4010754002102c040640c0360640841a8100004400c8003407100602e000209000500c14000644941640c420f5480c640e4508141c1003050700d801c0300204d11004e120014460740d010207900e0541364803001846010000050036861400307070b64041400c511446101008205c543c2d0051030403569202c03054818035a04203140c02c5480324080c0406020b9220301d1000f401d015150360070203800c0311420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 237430071 1250 237428821 237428831
    0x7180906062c090a02042108090103200d0f050a060b030f07090b0c0303070f020613170f040b04090b06041d0a1514090609040201140c1912080f15060a03 67
    0x7002150364440c00b11565131a250b8041030802103090030300c1c020380c45510441404020207000d99662180c901503404e40e1810540d8800ac0601c280301003d201815461491300080c0d02c810072520010054081da0310241156414030300803442501c124018401a2510294501d0455582d14144618820024442420002c094000192041d1000010b0100c040b14070083d5599290140d00500582c042d42241c00466200b00e00b0030114911402e82c140025900c20310030300004400700d08100d100d0088581c400009036000070002070717200e1400d000300100c0e1080390050204034a088100b11942c00b41c0c0c402d44d9100389000c03040d0505014a0004154050486500064a4102480c2d81e080c080442d0300300164100440c00d52a4951600320381083d800f150848000310f20746482d50000b890a80501c117041c00200001c80d481501350340512003201c001540c148520101c2040341400c205441d000c080394001b061800d004540e920305002d191910903620010501c1080c0b005e0410300180e6407010707210204255440b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 237431321 1250 237430071 237430157
    0x7020a0b10050a0f2102030706050a020102090a0807051906090e0a1503080319060f060c0c03050a0503030609160927060b04140102030c0a02040b15030718090606 71
    0x82d410340240c207036031113800000d5052030900c0c0c0d0408241c43c0101040074022000b5001a0340025000d01510581c1c0b80054541d0b485035000d80c00390003850586503001c1c1c8400004a00e9440014018049072401c890701d20b008000c124240300e8108480c0500d00014541d0340040c021040c007070842c0c1d03800c484130070310001e040480406910b010320f10030303001141c03000c0e400014018118621038a0509507182903200300b113694541410300d2103090240c490f0009015801c101c200601c0b034904a064010340c3c100d804d41c0e000419520f0101c0c0c40e40d0045a00c035205030600d2002c100c00d144201201d2911500719110224040e04040380310341c110120324422010415045003032400c2c61850302501008000f90405162110705040e0380c2d6507030b050310008a604540c0180321042840c2c5c000a60442d8407a010b0b10000740e04103000f404103543da4014042c2d019010b00000130712082c16030201680e014818585d0303101c000b2a484942070800d4602a1040d0400908242c514403084407040c0c0d1980740e485514200300d500880c0b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 237432571 1250 237431321 237431329
    0x30e0a0b0c18090c0a0e0d0f051b010302040806040f02040219120c0c020906210d02030409110319050405070509040809010e0906010c030323041b0b0702060304060f241a0307020a0b1005 81
    0x3c0d41000c0310141c000d40d00710300c0c1d1418a0ac40c0180c0c0c108003420158200750034502e0983da240d4008002600084416641c0819915542d04440c0100d1024510351803e83e2034000103009480207036400b0310101d1a040c030300006240301c1c401b06941554010903a0fa2191203401c20800c070b07074448800d90f140b1030b4160050004468020000c600c810201d98016507110391610341000100d580082180c141c40204004000411428410100c0503050030a0002160740b03032420310f1480c1c90351540007682c03c07034890300c00d220600c0503400c094000154266210081c500b0b03c0c500b40881c0b40d80c143e800501050724011000c0c00a40a60484080541501c240c004034159041e020728400d00161010745620b4810941742c0c844211012640d070190049030006890412180e0100d88103100040016091a50b00d06d556a603410242e000210700c2440102da00c0900c2c0d007100400c450300320303052180e03540465070550046d01c4240000e083c0d07842480140c002c0e01026100352034442c030303c070400ac01c0c40c20b19188081001c11103640e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 237433821 1250 237432571 237432593
    0x60309010e030c0a051e0303130303060506120604150609050d02130606090806092a04090b181b09270a05030304060608061501030e0a0b0c18090c0a0e0d 67
    0x300000404c1a801c80b820000c0c02c040360400504a140e462520b003001d007480000449030044020905101818242c0c1030490080c40d00390000ca904c2040024800c440390200c1d11910b00a2004407010403801d80c0306586289469404d106840c0440c034040346c108000c0c50640a9201d03000e0026001c004400c0031a20044220f407081d0b04440302280144c3d0041c001e1010400c6501d1f4894040d80c02007446020480040d84084000ea803201c526214643c1c22036043c1c1c0ba00d800c020045076100444c4071460400a284000b80c1d240000c2100481c41b0307070a5440811190348105404110002e0050540747d107604080400c5081c2050503100ca0a82c808000f250283d02004440c4009001d40041d5441e4201458204160b84c0b4a611440e65584440c041c000ba840c0440713405403a8140134200040c403660303c58065800c2907903810000d4000002202005448014800201400484a905074000002c46800c000c1c0001f426648160300700c100307003e0119103070b0054144c0400218001c050341c1d140103a690f50030072410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 237435071 1250 237433821 237433837
    0x309050109120315060e061b010507080405011a09130f0506010e0403020705090f06120705130e06060301021213050a0f0302030702120303010501051c09020a23010302070c05060309010e03 82
    0xc094100d5544107030382c144a18007645100c0003104800301d20f04170000f80f604020b400710511506001809020525814440c0300955001c00c5c02400341d4038091034043d0400201321000e55455080200c15a602028144040a510b40040003620140c8400280704000014400c085030b444030681c2102020410822407103000303101600d603800c241c1c0781038a402410502030343e00460240c0124028041e5520400108035480001940c4401c03030003082c2054186011061f5028a8004181ca01384900c401c510750001c207404400d6408481d410344800c82494200d214503080d10032080c59800208050300034199078100e080e401801100c41c54001070725010302890b4001401c601592001840720308500303140f6860002c088030f08014508542c502070020b003c2d4842c03004a00c541d014036a02d0381c984011194070140c85290064403043c6103907115034050103003031300c50406100c1d402c4014907071000c3d80d80320303000702c4200c6075001e010f80228a15050501c10f03542c1014144a41554941009003940802003014260300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 237436321 1250 237435071 237435083
    0x10051e071e14010203060913060939080a02060d0603120503041a040819020f16030b091908071a16090501050c190f0c061206090209030607030209010309050109 70
    0x2810307461400100401c2a451140340d40c0c1d0050007008541e81c0d480040e264848000c0784850103e0301d040c40c10500400044000601c2901c10701340300d440c9810391000140000c480000220000107050b688464820355601c203449031a449042100014201107014042214150314080f40c8d99407a81d403000780d4130900045000c00120040104414480200010000701011001042060406440e07845061080c0000486018405882c4c069107500c2009032050201a01003618035208003080d40700d4000c1c3c118802074039030b0080d00f00400c0c583c400119050801003900c03500300b0240d42003660b500300241c01c4000c050310b500c1d02c82890079081c1400c10003000c1c8500b550854499803890720b00405008070710301e85c0045041010502240c42c1040d40024004190308142440a50790360440c6008405034000c1076005050724081d440000304150003071440403040014002c18000c6584034002001240202414180d0691009010500c541c0c0241d0082020314410b1401003040c40c41c40d1902402c0d0380000030100c1d10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 237437571 1250 237436321 237436373
    0x10603050a080f0f0a0c020f100e01081902070605060906031b0103110c01020714010c030c05090409050307080705060702011109060304110102071505031b030112081c2910051e07 78
    0x443c2303440030070000a850101c482d00007032001e1030002000303104078410540c18451240045682c04d0042d9003042c071401e0030380034150351b00d03100340c81c01c180a8182640e0190246001c0e10100346903142c045280300e440307004c43c0d85010641500310011006413000d50111550941e04000d0001107000a000801c641805001d000e0988004002240d08503071300d41d0840d0040610f8190200c0310030341d00c001140c08040c3d003150081890942810268114810794030028140d81000030780c0802c22201107a003a1107400d29400030401b129054003440d45900c42c040e003142d07114a04100050008404040200b0700c60030600c1210103158a0382c00450003091652042c1e008200040104109503807003250715020f5842a000300d50865240044540400303240101c0180391040204005a07480c83c0c10041c00420004580140400c0f24501158103144604040c5042d01c5615511401041d0a0022030311140120950b51750f450001d81800e894140344c18048490050501040480080380710300e03c00e00d1022141c10b80d1414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 237438821 1250 237437571 237437573
    0x304060617150109020f0f071a100e01050904231501180b030d020703030c080708070609060509010903050406030c0207050d051c020f0601030602031801111b010603050a080f0f0a0c 79
    0x2098100513404000c100303004101890350310900f00c050341d0301a8105451252640542e20380301d5500d0710042c0c0c100002e10810020232044182d10041041203e15807001c29002d40d0700c0e0002c0c41205841110090307d00f040491041c1041c0405070f030600821008101a95003001d80d05405400e01102a0311411080c0b4040744507804d41e03100d49c0b1a081c4a11001c41c020321041c481c0001c0a5110510b0748800740501ca000940301091160310822140c1783d603030044240b566980d051a154000300071807032090b40c20903c3c0000003542c400c1c051240814440d0140c0312030742418900780c0d04902800300400d403030701103000301c0400207400c0c0c40d815601c214051240d0b01804102c0040c4085c3c8000e03d803038034003000846d44108814421010041070090560f9002480541d60340e40d20204002001c101003045101c03580392080c4842c2040b0301c2000f0b09021041c0c444001111000c04611030301781d170141d00003d070054000d000f550000421200003040381d1002c1142240c28072206040c46059600074440141c0418216602a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 237440071 1250 237438821 237438853
    0x207061d07050a150c0c0b03040c031a1e0c0d090b04110607080307050f0405030f0d02071202090f1506030403030c090b030c0a0c020a2106050a060e0c0304060617 71
    0x280c050a42501d8102c00c03a403a12071100034013803206035004280301410200ba000d0004100c9048050890425200e40e6804c2030b20b442503c251480c070054501852000400f05801c1000c00a00d0040c5500d00b05034214800601210109110241a01100d200c2c00c1090401510f041c1c06980c1d44a030003440620707054a05800c0112600d1001e250051203032404100410000310300c0419aa080f03441803610070703101c0c0a4000d0100d4503100e2900000e80c113105260707026815400014003a0f08020030340d800e49080540d5900d400300c18244140c0000d501813030520020f041300036000e541d964800c114540001802901a02064065001f42c0781900000d85641000c60100e40100d144001000296050391a5103480c1400700820301503107002c04c040141030341501095580310740c0a00c0141c0b00c0c01c110600716522113600c40403031003100321007140c3c4542030400107041c0004074803038401213070340c004000601e560f281901d002440c0c4c801007040302c5440d59054007088130107220050040007801c0e08014041140310001003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 237441321 1250 237440071 237440083
    0xf200114160809100e010b090a05150f031f060308030c040303020706180e0403090314160906060215100306020a0314180c0d032a140309090103020f040207061d 70
    0x10000740520070b4240082404001002d1801e038015400002e0019a20002e0501410380b5920f00ca0b031018200c0240720715001254401c3e801000301c2c05031282c43d0544001400b1070408250800d03035054200c004520340c8002c0c480583c0d000701d880280009031481e201d5454090b0f40d0400e6400300110040400c1c10b104240d01042140b02034a06402d0500e101c100845045510114038001c0005511021011508150040700014007469000744182c003e9001403e485503242c1c0111440800d050210b00001403114451050304282c500503400b40030192100348401d4001d40c0050100c4c0301402c900000007000c40d000d440640075181c1e0380ea0b40419500c07580030380710326224405880d840f0400350410121100b5600054120b0721a241074840003051030242c00e040d00c003624050070448458034180004030009003d0590003042c01e10a080250002c040b842c0c645949008400c5429000100c900050025243c401100d00c03820a00610162070000d103a036445060f41d1002c420300354010294555090840360078041c3c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 237442571 1250 237441321 237441361
    0x10b0403120509150c0a0f0312060608060a091d0d030506010f0305090709054b1b0706091212050a09020d060506040914031c020a0f200114 61
    0xb000e428a900c090000c1c0c0d1100c4c00c080c03400c3c2c60660018020300300d00014864114242d03080711521024070050308000d440380f01d460404c1584140f508202103842800303501180e000d100007415426215040c140e0242c01015000d02e8441d4140c240c090010b1079030300800060803005030b259800f059905040c030024101039848104030081c0350410041148240c8001040e4044a088600100f0315440e00031402d80d20481035200201d001100800c2c041c1c00d07200f04200c6100307083c0d0501b90200080007101024441000c05d84150900d0000032034114011402100a040900c3c0140c2c4002041c2d01750b90342d000c1196511a51200c0410400059001c0160552007941e40c4405004810b0005280507030019031100312441e00180a26a18804185180c840d075010a0b0309591101c444600d41c05001c030a25a41d0b0040c02040306c042040c8003142141007418020741d2040555922507440b07407030007a1000d490415500101c8a0a102c141d819240004000d001d40e44140202841c6030040f0304045610900807040c4041e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 237443821 1250 237442571 237442577
    0x100e010b0a0305100504020f0a032004020901081f0f14010305061c02040213030b040507230901060f020f07090218030c010f110c0d03050c0c01030603020f100203040905010b040312 79
    0x180070000b283c1c0100300300f140d0301d5642c5000542135070f8510004888282c1c5941c1c45404c480500004000c101e80c503840c041404032594109007070010002c041000380d200f03d180603400030b1007070004508851940c280d0002d00e50040320411420b0b58840c0c1140004004603880700c041002d0701841d070205075800d817181e5604031000f610882c0100c0c000034020708044e00031600c001c0c010703507000580f00c0c1c280b101d5904200156078403000c00080d9042c14142a0354414541c004c2c503003003084640e07a102c2c1840020f450410300f06009882e071441d580c6440b4042e5005604c1d80b10100075030140d200e40286000081c0032020141155200058450f04050822213252046141d054080c3c0d000d400300c1c0f41c582e0f13000110120410028030700b407a034094040020710309082c06a11200d8202c0f101c0c400d0703a01019001006020641c00e60012100d181260b24011825102d56101c085c0d0840321545040b00941401d54401035401003e00480c0d04e0641c0d134443c050100c500036400007031000e60209080c01045501c5085064103240c0d03203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 237445071 1250 237443821 237443839
    0x61b0921020409300f2106120516081005090a020907030e0705190e060a180b090a0528090506090705090c0301081009020f060706060e160e090403090503100e010b 71
    0x6034020b8071a59040c00c00c41c2c00e004006448810712284040580c0c0039452000302441f4055460b0100c80700b030b01c4800350890f554020410448552441c3c1c1e0141f80403200a60020b0030004100f494040082c8400f6207015198041d03071000001580740c2d0450325001d8180b6580004110761891b4000f410124290009841896003000204a0700401c40f9281c040e50035141c4404056215440010100304a0303501103000d0911454020740082c00660190303021590039140200d1642c2c0303070761504c4e044440c2128001075030484107007848008a0004031001c03552040150005071948283c95240c50444200c5540b8090f6008040901c0f540c1040c10702242c01803c5104000d080d0350400382c199403550b102c4c180713503124603903a08288015592405094002c070030000d483c0d0781d42c4082e07a0031300e00007900480c00759450ba21072810200d51400000c50a190340c01510342d541d8000d2200d030b00100003000d00b010340305801b0000c41003400b10321968180900c0d4100b8610310000070301504010b1100703007502c1142c000e0603c1240300c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 237446321 1250 237445071 237445163
    0x90c0503060c120609090a05070f0510171311130605120609060106050703050d02040909030e01020f0a020112020409021204030201051e040f2a03061b0921020409 71
    0x142180340c004d9411184e50460b50358803a0058a800c0300403901422038030901c0000241264015984000d460b01034412041c9040607104c00e031680501e03d80e011003601d05400004100f136062201108010344640c0c52103500325502800104400d00a4142029280e81c0702030401080c42c000d4009010403034110041d180d5807800342580703902c03840144540401c0c0070000981f0820907100d0300c106c0b59001d000005c11501ca41e201c500b032200801e101002100401e04100b5201c00315800010200c4250039410000c040c050708540c011101d03400086c0c1410720103902888041500c03c0107002901040e0620080c000c180d2500d420000e080d640c0161a44000d41e480d2092500b091040b030b5003030380d07000e0303084145100703101058a80109105031400390718005100f0500a00790304902d452250303044034011075091000c2c0203d8812106104a0304001c4004140307000c0c3c0401c00182040c200c1d0b900c10340e510780d4111351017905401240940e050780384100c0303140f141c100402c0d6100040381086d102c010f0b03040000301004590 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 237447571 1250 237446321 237446347
    0x11b170c09060703121406010e0102011e09030507021002010902011205010e060103021602040e0319050405090a0b1207030f0c06030515040f09021216060219170d090c0503060c 77
    0x24140105004038000075154003131502809003902201d0860908000103000b006880160000c140c6015001a002001a640c19803050003110710300120314140740b00060803420380c9402041d44090480600100344070341e030050b80da0001e0401901110750004140f6280700d2000401f90b04801c0d80c2550500c3c5040b005001c241000090b456001a0030300300140d65180340301a0300b02e41c12118800039885030a08000021640011000c1c008201d04111517400241050509a500d80184d004454203d11420f00003036880c80103401201c49030030050a03c44d4880b12041c2c230340d802e0002580040e01c0d92004580c1e21000c200e4030060400082c81c05240070440342c04c182d0120703841120706130b20582c4540c0d1508071400403400103078403010386c0c5a8000c00088001d03211009030f54640042584250200342c51603800520300e400030a0550310101e00e07100600450b05a59640c0c10ba0107802030105640d0f010038443c201c09043c0c0b0b441500703980d0b4002d515004801f45020b0402d46080c0300202030403003e0710107104000440803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 237448821 1250 237447571 237447577
    0x1401080a030c030c0305040302100e120316021c2f0604081e0709020406120b010c0c09020307030204090924060612050c0c0d050310060c0c030308090f011b170c 70
    0x150619190f078640130030b030404481600440c0c20207940001c803410304095003500325054041c1d0342c0d401d640c0c400328516049820364a034042d10982c44c0031500750000210040c45c280207405480c0c4c0703110710b44c10740d803807055100c240380402c0700c081203034400903101100041c040026110102c4240201c8105160509100010b9160405001d641c158400c80132014a407800d000d002e02405801c24000c119240c0b540c0340304c0204000d1290403041c11003890070003903000651041c80300000903500b203980007040c217191000d00f038001c1d403008020204144d401d200c00300b0760700414012032240700c2c000c01c004080d452180a002d032030301500c80314a644203854010f0410a4a0b00901f0107540c500404c1d5000134550f07100d11544466118468000085000315120048100c1d04040550f014841301c0242280054603205c040d6104402c103240642149035108040000034032a843d4164452458016100071400f42901d007406d5885181031340140480603102c00030800d62180c4140383d10071002d58802c403941406c03916886644 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 237450071 1250 237448821 237448823
    0x6021e0604031715060d020703120603050d0c1a15033a020313060801030b010b0f0f0d0b130608010c08010f0e0601021905010f0b03160e071101050a1401080a030c 71
    0x11551001039080740c2c200ca01140c0103100541102d61b07514940d51180001d50060104030040340305a208441c070301500f48180010b417603002c0000d110b444080b0b03031300345e80544d86240c0840da41910002ca0a0a16441c0755055011b061480e07681e04080305048201400c08820a503a00079801d070ba081c080c107803000750100440c00310328001498003031401400300480c154030403109108102d0441c1100010700c0c0390b024024074100e03405083c005d6407503621880140c60078440c5070b40e0a1701c0072409018039081c041001d0001c20350020b94050026414061030081440380e904094281011507455400b04580402800790148482e85843c3c401c8180d07040050b641000301250080e2007840782c8840005685134002c000088060304e010004203040c00080c90512f028218810320321000710b042a50550700d500b400034a030703c00e82c04441c1c0050718450401d40300001d06940207007040200a142a00b04c1c104440a2003a02d002c2c066405004c5003002008040c2c00e51004183e2081c0340580c085181c050101740d100c40e1b280007403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 237451321 1250 237450071 237450107
    0x4140709050f040e030c06161409010e040e0f100501140306012c0a0c0909270809100c020307140102061b07080409090303050f061309050f0706021e060403 68
    0x480c842c207000c035000f4052407070002154031000440c43c80a1500003120746c0310b25000007035511855500700d07040703e4521000c0d01071058040240301401c034075070080e00503200b95000a0000140301410100a03890017000401d4810150451a12030f031014415000301405401a034444414801200f0046a07803000140f00f900641c02e091015013000004500b0900409000902044218140100844002c000c15129903022455510f03000801c5a0b41d8001c0e0010342d041c100d5400f061003842c003c41125200101c00440e0882010000000729031355407030b14101030341120303500d0030703e500703e0b520500d4a0220107030451aa00e4061403c4080c5070303030303001440a40c01824140317043e5031390450142c402d29a002d0704900400099001c04c0c04940c06141c2e40c407910f42c02e07010ba901171005480b51442a48180c6c1300b5142d241d0403001d0ba841010050343e040e0171a00481d441402141d100550700304040d0705000460300202e005070001d82d03250110203908400c409104000b4806801581002d580280424010030544615 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 237452571 1250 237451321 237451339
    0x1a070c030c050c0409050607021b09070c020102120a050903060a0212061e130c17040c05011809020d0618020f070624030506010512010b0f0d1407060203090414070905 73
    0x8000d07040c02079a4002d40f010780f060110740118645152900390403922000107105400e0910224515500c01e490001c4000d040d00d10192201d490032074003c134644400364154481c11b00050070208041006210303c522980d2059101d40c0114205820140b0140c8820721a500605c00011344545580c035150300301000310340e50029641d2212041ca002d1980c2d1440a600c201c4858001740184079030b03003210700d10744801d070b4a80d07402d0110f401d5010402e00b42510f0140c142ca5a01c8428019540a01c1414544844040085181d6562444030f10143d80c42603624481d100d40b0707031004100421510030981c40e81c0108150660400030040543e00441c094240007800140c0c0b038561803032511010000c014500c000d04546858080d44a0a00e1b03a03031800203220706402030030780b5140d8041d503110600ca1420540740040184607841143e500b040a039a268000545044003861001d0480c41d40c00c102c000020f003182d4001d507842d80403400800c0111564020805000390b004000c01403507990210702c1c00e0a84104454200c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 237453821 1250 237452571 237452573
    0x108030a030f110901032a0807081e0609100e090307050c0303070f0f110405090c19060210020c010b030f100b0f0d150b0409030801080c0d0c2c010e041a070c030c 71
    0x180740004804800c0c4244600d120405040c1d00c111000d1040f080383e0ac500065444140302250400c80751800c0b294017007140c2d00401c18a00d000008240c1100c8428035402506480e00903441d00c070310702030702c16981613400000c0807001c1010a00006051020450103141002d0003512010400010b2060090001c1c3d1145140d174108900a0034030600b07220082d00c01c0019140c0023401560f1241149006845101c0b840402203d54802402038016920158040c011903041407071031202941201c4540c41682d504c488516100d9181000010000a0114000c00e6032550444040701201d403c031500e18000d9642030359041c5651110703102002c0c00340d4401d545101550700c108030040100081642103034010f013000141010700d94044c0020b410b9400d1601540c81ca07039130001c100b04415a002c2402440348140141c1040356540c18224050316143c0c1c0031094080c0c2c420b40c2084903403083d0982080c8841541c81040c0b10078425100711102c4441490301100b4180d060100004e0f0000c20740001c000d04100100c2c002c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 237455071 1250 237453821 237453851
    0x10080d0219020402040902040b0c071a12060d020315100918141005130203070b031519180c030b01030b01091208090603070203091801030f03050f120108030a030f11090103 75
    0x2c000f01b070112011921943c4401d14049190301102c00844244142040410281400092234002d941c60303091452034562a621810b20054000b0402c6600041056012000d604c042c455032070300c0c0c200d0310356480141c644441c10340d00b030400980052039603600d498040c0801c6015065207040d055004848010f070860340a81c0540341804004030036400b14200428052048100c90760500d41610880583e200719450700d40100540c0000c589442c504003c0d01141902400c00d46c0c091000c01c2c2c80c01400c2010983c440300031030304038800f070582881c8003075035040036a80315541403080c2c0085034003d00c0c0504c620042d00300001e20800d400d010300980c40601d584050100001e2504a51480402800c8551285440300000e5200c0d00030710718140c0a80740c0c0f9140c14080d6618829428181d951104600c104200b4a4030200c1d11074100f41c1d900345100c0302c1000b40c9070b0083c01d210f00d0180208010002990741d0103c8280c01002e5548848040d1003a80c108600f4500810b8400d06a40c0103500a1800040f4501d4001e044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 237456321 1250 237455071 237455077
    0xa0c02031e16030e0406050303120a0207032c040e0c010c060507020f0a0c08010605010c1a070e04050a0c0212070503040b2101090609050c0f1804061d10080d0219020402 74
    0xa220050442c0e000408064000c0c0c00c074021a00201c0e001c01100303a440040c551a03110303080096200700b2041e03000a00d405032560140c0401c0d8000d01d44096144c0c0441d80603241103482d01d40c021510410820503030cd0743e103410300440c10031500c4040541400b500180010b098608544402400319403036800081c100c07482001005840d1002000300c41086080d400e00e10b9903000d060040c1c07002c2d54240100070440754054424141d826900c1440040c01d144100f075256020359016100e00100b040c80e081c40e088980d40d07802042d000350300c0e2040c001a04c00b03100300060300d882d0301e840c1c2a01000c00b0900a1f0404500c0120070b540c1210000e1244661740c4521503515000700c0d0000c0445a2142200000030407071202ea0782c000016a15120b03020401070715402c4551071107025041000c01c01081c10042c4090580c005144d403804190080d2012800d1a00c035804810190344240c07010204c1c800d003008021403824140721440040c985040904410046000c00a40f608002c400c0d041c0025010210031085449903411 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 237457571 1250 237456321 237456337
    0x201030509160b030a0e06071d04020717030f0a1104060315090213090b0a0b2a0d020a0512030105030a03080907080601090608010f1b03091e0b0f0a0c02031e 69
    0x840d81c150b0b5180c07958540c0542007950341e503403040e04d80503500811140010b1501c1c010704c81d84d200c2101e0007295201c160031004100441c9504160244420800200480c941c480c0101141800544901e0140324503d0062401016003845c03900b014004042c09502404541c01d540862802103140040d02050701016038180d0f0011714441d00c001a504c0e000840440200265501c0c07400600a903141c407010001e60040c0350040d01040007082116003010a215000c91440311501090034848102c00721403170b424111186480d4025802c0744a01e4000c0000034401000c0390001101c6080c11541042e020941c2ca00c84044002c046c00742d0140071031007000040020710000c145c1003040311541d40c0c4440e0328502902030752207081507540c00c200d260f00c070f01503003406612444140d8110640c1d460340d0540040307015100d094010f03101002c030150340c0515441c10488a801990040150161a00303002c841100709507402851154614034001131001c06507030210855004240300085261156901c05401e62a4414128 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 237458821 1250 237457571 237457603
    0x1020708060c0702030f0a0b070305060d050106060504150305090a06050402030f0a030201150602010203240f030102030c1b12030a09031119120207050a0b0a0509100509030712030c0201030509 84
    0x1007109001d01400240520f500c284c05a072111092440400e90700c1c05070343e1008000b625900001382070305103c4d0380090f034007030801000b0b070f445c000315615142e0031a425078003d0300010b10f0003c4d003849024403c0c01880002006440e08220900d02000500d4982012480050800e6221800710f4103541d002c101c41d206107265002500d5550b0214500a0b0084c10030000070b00500034900d200185140c010720035030b8070522507254480d40c400c0e94a01c0d03085100c0360712460a5401840ea080041d100c1e2002d1010394450100c0f54403a0f0b6403030009000107141c0b0390b072080313070951b943c0d0000c01e48103581f0240405490b0040c20840010852441368501501e40340408040c604084c401c4619002e00b00711694a0081c205009002c1d1410182000708100c1e2a503d080c001c01e90842400a02001020140c20083c01a000245440b0341032220b8100064050b52007540540c0c001000800e00031581c0c40d0500c0035030300a210000c40f4211640da69900584000b144201c0a4103055640c000039490080034010351000d44101c0e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 237460071 1250 237458821 237458833
    0x1009051c0c0e070e09041a1008030d05060a0f06140901121109130b0a03020d0203161707050405070f1b051e0124050d060204050423060102010b01050d0b01020708 71
    0xb0b500e001c4000d60031a0701000140424042c0f40050824000550069030404292090b40c40b40305006c40c41981d01501e042200c850003040010012001e0001e0403000c04901008101390501d82d041200d42062034002404c0c404101004211868000d886509040b506100722070715070207490016501c003844480c80c004205d051550400308103001400400004070203c65800448883d00280030441e00c080c0e41d981e801c080c01010510142c58003051080b00720b4401403c0b0369588030b110701740e544c7d01c0c5007036400404120040c14551700c60b00c2d010300408018000556007000b01c1c1c174203800010b00c070168a003402c1c03040c4410300c211201c050f40c809100090041e04031044840344418000001c1394210140380d000340715445d0142d080e0400740380c25004070440f5480108104401c0c180400c00c807459514030300488400b0f5080000003001e440b1401054104182e600d5402c440b103858019080103140006d05090441e490000d80003280d030b81040540d1405420003000241c015043d40040c0e14100ca590050b00340342c4202 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 237461321 1250 237460071 237460079
    0x2030c030f190c050d200f0c100c031407080c2d0a020d120c06050405060402130e1b040e0303040f11061e07030311070507060207051009051c0c 63
    0x2900400880740b08401d4042d0a10b03151404907444180480018503c0d0880c0b02d040504500c68080c500414583c040000e221001c02040d9610b000c003801d0040c80c40b40c00107050039105142c44010b00700c0c4161141000e1540f450341341d03001010340c00c90070311991404202150700c0701031000320000c2c1c5070f54920120032034000c045020404626030745408100c56110b030741840c0304078035418003003107844e402503010b89035140c20000c82e65080d148516031a0b5040400207800c41034008601c003400340b42e01440c040e001601d410308080c01800312407800341840f5551942010391540940000042d24000c4580402040c86190720860000c0c02a1044140540b614130000c024442481180e00b02d10151324030607a803a400901c1828141f02803409020404000008400c01e100300500004008080452080c5000101c1c50700d0700b03440d41106c1d000719074241c83c2c1d94007c07102400720540412905001e4030b81100c42c210052038500303004100c000d023802001c2c0103c0c1843d06c40c0c0040341070722443d4032505078048032902c910394032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 237462571 1250 237461321 237461347
    0x1203111b2b060518030c030409050a020c06010b040e060108041a04060e100515010809030304151e05090d080c041707090617071d0606160b07050901030b090702071502030c03 76
    0x55621112150420304000d000725000021a071403a1420809103090900c1c004a2704014640103202291507034081142c203800300414005540682038900080344c03203d0034044c49900b1160f0003130083c3c0c107100d80a014040800c00901042c440303a503040403000c180350388614180001d417000d6100031605128003110b41c04a0307030480d0009845001d8071010130080c21000f40044070440f0b0241c603d01d04940040001c1004240030502014044608a4021506900882003171403100ca542032440111591001800002c810600090b498081140b4101816040c10003590140c0d03c0f0307500c00c40b85482510308000d04447e005100d03800041c035170a0010020325554400240d491140840080d0f9030340a62000494600d00500368070109840720080341501d80c0e1071030203101859002c00c03110800c0c0303075161698100103603060310b41511840701507440c29140c1c64800e001600762205031400b81c0c4100014030401030f40780e41c006004422950801e24107040c1d070004080c1079045126020bc42106804006800c00c1c01800c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 237463821 1250 237462571 237462581
    0xc0306011103160b090307030816091512050f06060a052d09090c180d020103090c0603060503070f140d0f0503160b240603060a0f1203111b2b06 63
    0x1302403603100c60650383c1c030710002e40c903403081c00c0004012500345000b0038501c901250030b4003007404c45424102c44607902d071804080d0003d40040c000c0d000403004540c80825016070700401d6000303912400300100c203061020000f8800e000304000e5004101012842c102c20019480364403c0540400030710411420403038804450a41c00a103613507014940d2600411500d1070040c00315a488924540741021518045003048440380040c1400d9040546550460300814140c101c0343d001000c09440020b40c0528060906042c00e0544d0301404601024280401401003002004440d02008691201d03582c03503030b0301c0e0100c80c80810f064098600c1c071020411115096050007000c03201c500070880380d0f94a684489061510b48910406049040c0350500da0003044c0c10410051600b1210040111140984403031964402c00155032214142d1100912190241608841121b10b0000403030b0280c1030400d4076280010401050105240c09182c084407084a00d1410803040300341d50752600f050409120141c109200901 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 237465071 1250 237463821 237463823
    0x906040e011502060405070e0c0c010c0804050f070503031c020c03030112030306150203070312060504110415050f040e06060d020c0d0212090d11060405060703020d0815090c030601110316 82
    0x1800c8032265605541c00002c03021710075940300f0000e0021908011032100d9010b00500050800b0301c0501c071501e04807000f03010b81c00713058000799100c07000c51500d81042d80c0b0340500301d1203182081c1c21101d8280300d591008403c03940075104001101c0c0c5403c4d10840c5045c0241300e400e40203101c41c000807001103a4075182101c0c0d42c1d9058020f5034240886e0b80c0303a800780303180301420054680240e4420400d40c000240034034100040c2c100d40e14000140d01e545c0b01e001c0380035112100c40070701420100007000d211500c0c011280b05d405a009191031828590810810980d0f845140203280700c040489002500740e58135801100d44160b51810b00790b4880c1c540c4405c80d5a1204501202005402001c44180c920449481982c10721640108601c1c5514a26140c441c040c041d075044042c2c000710100700201d0b03152900c000401405100c0e9008181c4840342000c010900c03040905050603840908082d230b02c0716551f00800d05d4000d5004d00c0415521748a010040c2e4880d000781b00000900e000c0815200300e085448112a0401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 237466321 1250 237465071 237465089
    0x91005041811151b0a2a0b0f1b070f030b0103050d0305190f0b0909060405060f0606071101030b040501180c080907030b07090806092107020109030204110906040e01 72
    0x1034080042000a900384000407840f0010050002144403040c54524200030014101503655900050711000e50301440758a541d0185005444c85a20f6500c020799128020314110050508200703294a002409200704045040345034491034052840749030030301c9100010a1180740511003d41c3e00d16081d62486805d110549032400340700086880103009004040c407442403801000072007402c0b56001c000500c0c0c440c80800b00155650710074892900c0f600101c500403a0802d000b0f00880ca0245040c40c039004000b071240184040744001c0c0f1180d5290328042d51085603011110304e00b2060f20a004030018040303003400e15403003401c02c400040c0300f25036048440b46070f2550360828040350052110070341c2c40705019600d052480c0d200d24007c10100d0352081056403c420a4640750346c8241d551980d6074900300c0705071280390a5030001042e072000d000000e5505558140d120750300c141000c490780c001030320001c61448003030700850f2030b41c5015103407103800d000303d60801a00420707880d11140c8611040d955150b090103085c8003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 237467571 1250 237466321 237466343
    0x230d1209080f010605120c010909150e01092c0606060f0d020d0b03191a0403050c03070b07020c010f020637091b0b0703030207060902040606030b100906020c0910050418 74
    0x15503400814041003644040e121411000d188c071000c82d00404000034003904c4408510f2f0301080765a010a08035008099081000c1411446250041102c03016040c00000c0484880d481c01024200423800c581c0c00002212956107035042c407408ac84051140c85d8030302030402d1000525040e030b0b549a91010700d002c0c400341e080310351407101c4405080d46010540000b070f006282450022407840d5000755000d0303000d4800c0c6071040c00c01460030a803520319041072508403200d00441080128140d0b042010301c07161913091801c10850740310380c000a903c03814050002c450100c151014041d00038110703103c0c506900e901070003201e0700c1c14072100700704010100381d102203e03407900c2d01d507010080f100b10f01605d00c10317034913918115480e142456900390001e500500c0111141e640f60004480940e446108190080c14143c40115603d0994420010b5030110000c0390000c4c0b100943c1c007407080399800500816411001d550b1028645c80b0110b041130305910701c1e445070f94014101590138100e0890100654405485003a003115 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 237468821 1250 237467571 237467599
    0x150f021509121e030103030518300106081609060b0702010203090111010f1104060320090d030c060c0315060e01020a0308040609021504230d1209080f010605 69
    0x20084420740390150150700c05031114003600284002400c18410201d00d054031101c0c0760004001e01d0b0026881034012520108950820241c0e041c50000070400031201502c1a113180b42e05100110400150104107040e030001d01c84419100354000c8000d0b0280700211120b04418504810740c071640c502a50040b02c1c00d043c4009100006a816201c5a5605030041c5041c00060801194100445006204d141d03480303c4161411a01ca4030500003110280448a5a0303542080005001c2d6110204644580b00e1000c091807131242c0410281c0701450412a00358000c14a0360a04650a001420014003280c0c07034142010500c5406038000d0000205400c0c558000c0d55031100c084d01c0181c2085902405604800110b0700000e10030381c5204c0c0c0c040d01c21900000d1030100b603008600c074030114420400c0c849000090074801d9101140d8150300c5020342c03191651070038100001107070140344204802000c840420521500c4140581103c03400340850310200d844e010403c03a07039a40a00750504c00c83d4003840e280e1801c44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 237470071 1250 237468821 237468853
    0xc1c091a0306010c030207120f06050702060402090103110a0302060f130501090602060c0a1214060a0909050a02092d041101030203070e150f3105030a03050306010306150f02 76
    0x2151240340640318508581d01c0388019500700b841604100d046004403440071a5140000754040a0280500050350000c041840c01c5030072140302804200940d481401000700680d0384004c0030b415607a0001c04088043c4000010403180c4140d0380000f0740c05000420030b81c1844840310050000940d000c0017241c07e040e075440c010765181006d800380200603044400000d410401c22001040041080c0c64030200326549a07099201720f0b00d0304003d1100e08410002882a01c0c98108000304c0034158403003040004000980d20740783e82e0a082c140082c029071080000420250180000b10000400451030b51710654403040e20102d4440201c40440c1c400d0341d0003e010ba40340d4464170a40748a26815103d2006c00d069403c104841c10175001c0440319582c3d0b08000191030a02d03032001400403800700c2c04903460a40800c1290785030034084200c201760420b6031007400f08603940d800101e9099a94050a0a9980380c40d070700c0040300508099000221094400254614015444030b104c901d107031520340c2660f1010289000d10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 237471321 1250 237470071 237470099
    0x105010516030e0a030c06050705060106140d0b0301090816120507110405040f0203010c050a0311090a031205040506070309030212070f05130231080705010504090906020c1c09 77
    0x2407074104007a100000c1d0143c424441d800704018011071007a41d40e41e0303404011503c5900508001140440d20b00c0400c00104600c0c5e025040c0d5040c0324005a12460551030709000781a0694141910f0325091101514294000050285c201e410700e80e40d1081c0e0b104605800e000182c04550a100c4912561500d500c900207550003950b107e140c12280881c442c0400004e4800900150384a640b01c2c0c403038100695091242021042490319040e45403506000040c040341d640c810903510516080200300959515450b001060301e510103003c800f001042c107002c0350340d4015608082e030403a800048402c14507030072030480c0b0b048a1007207403402d05441c00d1607511600c030b1806200341d41080e0004001409180f900b0140346c0700d0840418401400d140030742940010041901d1b8a100f100585880700884e201442034464010703150f100010103400c1d00c2c140000700f1520403480f034070b0140c6070740e0400c0008004203a01204e040b81064812a0340d1a090401c5c1000306d0681c0d00020320202da1b41d01c00006000d80c003034102c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 237472571 1250 237471321 237471337
    0x31805010c021b0607080d0f0c0f1b0c1a07080c060105043c0e01020403140705010f020616210f05010909020303030c0c03090307080303010320100c021f110601050105 73
    0x40c1405c220b51030fa02c440968000d011800381980c0c49482c5280c1e144400c0c81001402d22260740c404522285410003c2c0110386180202664907051a22280c0420100c4100304110340ca010811000100c032000e001c1c2c290701035200001c1c46010002030450520100080c0340d41601e004403420030005179181c41081c0e850750041c2d0a001c8030b130300145031002d0000022075a011101c0d189403020a02c1e00c07803540c0d42401c99000342c10499030346003c044040701040c010000780700500341c00e09142c0010010840041e5071484000c2c1109404ea40441840488c00d12a450002031200e1180700c0d00f0090100304101d001a00303501200d078000c10725000002940c4001030242d101410f4001e405180746442c0d9824400c0940c2c00304558403a584410058062191010403191000b4030b08103018680b254110700c1c005000741154264012000043ea60b0391003507a9070301e44100100e034114101908160b06a00c08030f00c0c1140c8038680c0e034203020b8072105480612038111a00c2c80d113404108090760156030b01c400c019a0f00e4061908 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 237473821 1250 237472571 237472579
    0x1214030405031809150405041118010314060f04060c0c0605010305010509250501050f090901030c03060b0d030e060a020703060f09031106010b030129030109020d2a0c03031805010c021b 81
    0x7401545c43c103050380b1041d0811f0042101c01d811400c0c02d8003041c1800049503010707240e001508010010700001044c40103c180c4c03500d000d40400d003002c1c00a001c0300c42010b40064200b69a0b00c02c000b00e118013550b0840300e02075000380240840c2d030b500c0c00c11a0017401c044420010074082d41181d8607041501c109841c05020b51031080741c00d1942400d0044800da0440c58820701c000804000041040d038a40e125035008510644401440900314501903003078403594107506006421154114000a0b00141c0a80003030300103642e0183c80780600f4000f20702c0c0840d15070002c0c00951501d000c80b40312203115048131000a020b51541c03001c0200140017a56260024410900465401d000522044140b03600200207402d98914081c0b803e80680144000d0751f2003a80114803a0b980000d42c6802e084490241100c04e80440f2a40200803100c0301d0076010500003404000c0410000070003241c10940203501400d114500302c4400c0941c0f080c41d1809600038561503403405c0143c450081d01825207012040040301890b0090 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 237475071 1250 237473821 237473851
    0x60e0a020307140406050310050702070f08060c07030e0406140f1801090c021203010e150616020118032111030a02071a09030303040609060c05070308041214030405031809 75
    0xc08600740c0e00510803c5194020f44400000131542c1c3c0400542041c0246500700062600700b004d40a854500c1c10351156055007041c200801c1002000305080360700004611f003007641d40038545021a046ca0440c54116032003440d2986c04103202c600400c212510710702c2a01c4408000b02d0340e204026440804001b000c0450039400018848654a9004048204c84c20700440d0441a900303410010306803c240c200140c01761030f000c1006400746108085840c280c10542d155850071184030303003d586204808070040d05000040500d91100d45051009000454100d9000003d0075080d41c400603a80800c0c000c2380000400b0617600e8444400013101303c43e20003609030020300c0310b145408418020090380c9154018011001e00400300242c8052005502c590b01c550800550303c3c465140c040c0855280301c0740c0b02e040090610603080025004005681c01030703080508601c00000c910400c80303291001c00c6001107910008000d00c0300f040000000b910181c480f40c158007011003408024800140c004450802ca000152 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 237476321 1250 237475071 237475079
    0x1002090d02040b030f0607120c0c03080412140c010b030606040204081c0315090e070b03060a0b0315030a03080907150c0609060f2d0b0604150c120309060e0a020307 72
    0x2a501403007244201905550b58048142c1c5524102041102c943c00403484000074940704031009d11885041e422141081c0d000020b29407801022190010700041c54510440e00400c0200e0262400b03581c0a444412041e954280480c03095000e0895124014068460003000c20303110714080c0280c070b00340d40c650001458844107003016117104004600f0842c00741503a6658403c20301a91008590103031003840004114400c03406a950703d800b0869200303440320b84051091201594480405000315250401065102d44401c00204291740c540303000e0b160b0511413229014105600000040e01c1241c603e02a07680c196030f50f40800d00034a84803c80c3c1e40020b00c902d9102d01c00102598030115249005d40d40006d0140e910245550441e880f0380394050708618641107001410801c0913681c98420b00580003030051050403c0400c4450045004d50711000f0190388007a082c1d103114000c48914a40c001008050034100c1d01800f800070031003000300b6500c1c01e080884140c85288d0000c0c2040329194041e0082c0081031134 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 237477571 1250 237476321 237476329
    0x705120c100c020d0c240f0c051903090314011b030e03070b040308180312040204091511270102060619080303040605160f050a03020a1b0b091002090d02 67
    0x840051007092180035403a81c030150301c0c0c3c00c0482e40c00030320a150030910b10342482c01c4d030318003030400003a542e040030b01031401d5152060f40408070200031007881c2061003041704940307080b60800c1d100f048a40a4a07021b00503140c14913a00058030f8044074083c1303941c0700340035017482022420b81c2c0102d80c0d2254408008840712440b41d100740d000d03018508081c0c0c10740f8100300313a80d40e8400d041d01040c0c1d0180c0004000009204008216403640b0200410300e00c0150300d06000c0085280b030002008201a00c5103035650209014001c0040040810f00701250b01003000e5004129018190f80160385400220070004440580c0d88100c080d0301c0c50341040507001040c507640c076402004100d00080d0207121801c50f0002d000a5450800c0020710b000d42d2180300041014030f44400c01c1703810300300d5410f130030000c0081802c4c031f40c00c14542110468514940c185405030355214041e00684540c02da6914088820401040c9074081c05070b9040418000d01c40b041c00c1d21110383d005c2003254140c0c020480e03002d0b80010070b0742e007420041ca0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 237478821 1250 237477571 237477589
    0x10f06060306050a08060c070602040801290f0d0f08040e100303090614120903090a03050309040c170a0e12160605060103051b030a1116050c030328030b03010c020d020705120c 77
    0x3c410701001d8034258440ccc105500392034400c03a1881302c02044d11041c0348079440150f141d0101c2002074406140412002c0300003684800d2110024200f00103000c604414082d030740c0102c50103040c42c0008440903040600c030307003c0c6000c042e00c0180c2c00103c1400002c00c0d0107200e8011480780b2100c00080c00e08001ea07010380d95100d000080c00c141c20502c810403100c000c5454209584006500500c00395072250241c03806e1006842c12840300d40e08000700b1900600400380010310342130308014007210006082d00c2e4003900d40d1601c1030600e8254250031000c24404608403105600081280c4501400d0003503440e0710b0015001c2c0d80c1d050721106004000ca4891101850b8200040c5500102e00038000c10041410424040702d607208120038582200c003d8116020710a00f00000001c0341410b900840c40d1910781c416504152034a0344001c041c00c0903680900da040c40c8260041c1d0303445040240208028091480f000c0d598659506100c00540030740400014503185c24400500d0f06140c5c2005012103026207420491044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 237480071 1250 237478821 237478823
    0x6050c03210103030f021b1c17090414130816320705090c1602040c05091f0c0809010314010e01080d080c0406032310090609020901022508010f06060306050a08060c07 73
    0x48100c02300c020550201c0014581d2100e62201e50b030350030b43c4006020a45a0361028030701410341100500411240c41c19100000d940c0005066440700301044107600d446106940c0501350214540c00d40000c2c007401320300490000040e40705003000891600da4580c641d030f650f00c40c075640015240300145501603003900400c6007540c1070001c010b0210440d4005000c40d200c9041101c0040c0010903100e105040200900704e078040085404c2c3c0d01c401c00c241d00200b40b0500050020400a0f01041562071381c0d0090300420b0030762040d4052000250f13142c0c0d0104c00002800d202c0c07012284141801501c0c00350146d01c82c14040c0e800380021501d4103041400580180c001109907111445010b00c19403000d0b44480c0c24103004242c3d21003068241486d008040050382c0c0c0a40019401074810044000180e80001d44001343d84074107158094480100c800b102c2c000c02e540c3c2e21000440d402c00c15400a0542e2a5201d41c003a260349840810405468070203000842e02140504000b40e40904040746c00d0b50001006400c0b06 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 237481321 1250 237480071 237480109
    0x70810060e04020d0510031406040c0303030f0b0409030206071e0503040215190306030b0609010e04300201050612160e060a0b0a020303091e0706050c03210103030f021b 74
    0x104d10150040100d54044840001c1a04801000e000b00080110ba4484640c6050700824031030030151102c0da6003074035510005050554a504e000d0081501e80c111020040f0000c0003003129000340e0401a4403680103c4007400020f400389450343e912203000036200742200c0300d6519141550340d03030741c00c2c003141118400000301d8410041c45109a110030245a0207491140c90b80c0c0490b00318a5407402140ba2403024009500c40c4003014014010615044041940550000c03880d14045051035850f40400d0084d0740070040c80180b00700400000c58054002a010798400d80e00580040c03403420b0016104c08098a602040302c2c00e01c602003021540481e00701c2d0704042d0040c002d0680540c1c411000409510400035680542c10100800c8040300041c4445450070000101c00c1140c901c98403003068440290340102002d01c82e01003801400c00c50100159450074422800b0213a503040e600700c01c0c840d070210074441100000c080d400c40100c4c09101007401c90f500c41d42400c1c0d998981480e1f008015a00e4001e003000080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 237482571 1250 237481321 237481327
    0x50a050d0f06030c0e010605040b0306060739080f0d082d0a050a1518090c030f260a030b06190819090807021903080f0a0305070810060e0402 62
    0x40711405205041c001c0d80b0494400f20007603d0709004400101050303110b0741c24090305110400004800d40102c07075000108070380d140c1d40c0c3c0f002803408a050240c500d840f1841d52151540842d001d4940660051112401b900351145d00d45d41c0303045280e620082c0801d00302840c2c010420000c003190040b01c03001d800c200202100c81548032070340301851011004003045546602550103004141c251441256000031440d4010700ca50942841e150134085124415103512440b9540001c4100c40254010003030941c0c058542000140e82e401c5c0500e20b12090003080c1c0310300082d60301c2100c40c08511418541000f824400050415603040f9055004042c03030703541c85030010300c100304d42940164070820904580c0d41903115260503041c003601400e0200c960a82040d110b500d0000b840010845040c141c030b581175412a01030200c5000420300b1503298000c1c7d40010b103203081c0071880250810280d4042c10000450b0fa6040046507200a012101011300f62000920280b2400c02071000c24807904c1c03030b240c90f46005080545 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 237483821 1250 237482571 237482591
    0x703081c0203040b1005010305091c05040b0408210414041a120106090501080a1713180b0306070813020f040209120601080f07030507090c09051203180a06050a050d 72
    0x81c0d0b4001ca0b41151548484410004c0120841041101a11080c64100301d9450401e02c4c0d1a0307952484401c00700c004000d1810350000b248039004903405000c0c05101992a2940c809905035540703480c040d40104d10f141012000807980203042550110f8a034a00c03071850008100050100903c0b00809a520b05216444464000e45079149440d8000c13009400005545281164490454806030012031003600940d4110340803400340000b1205040849442580e101c11a1440c0ca505080303550051a9440350280c0d215480003c6030b00120721404140c01b40c1341d1a5032102c0040360310180865110001943c09007651026080c90700c8064a10203004e00014540071003440010103024a1100c8000b00b80d2042d0010711032104140071661078008904000d14503141590380b01038a6030030320301464600507031f210700642100d07100d1410040101400b5207a018141c4102d542d09403290300c0100d0b034101020b0221004011410a0b9111804480390382d655142003210740102151268007880705824100c0d101d284c591 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 237485071 1250 237483821 237483877
    0xf280207060c3207020f040e07150206060108070903060207021311040603061d04030f0207120804091803080c072102070e0a020c071403011b0908010b040905070308 72
    0x90000140c6440d104000c4800803030480022610181e41e099510220f42c0714000c2d41c2030f49080d920540ea040355042419540d00c8041070040140321b0b40172045100d610700000d00c400f84907a04846000c030355802d80c2c0c11540c0300c1b40155501c0e001071b524000040d403e420300304003140f0706601070145d46100401c10001d00c5410b0003c6010340b08407000c0c0400300c040008042110a0b018441c040003010486003185c070110041c1c104c00018803006101900784a41102c4542089100b8014840a080104540100d0721240d05050344150006c0c05201401454448540c00c10001c0a007402c0185031325689420b540d0313a5401c080300180e004a0401c544400301010652038203112079038803604e031100030340c0148401464a4018401200040e2041058910401c20300602000101d900c10941c0d82a204a642c548082004680103004204050034401895600e100e102940f00004e442100c0060340203000428144082008403505003400420580c00400108001007440780901243c251160031100b02000030000d81e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 237486321 1250 237485071 237485081
    0x306070c14011b021005040f02091e040804050109050d0209162303040b0106110601060c0305090301020d05040b01050a081504021809010204061e0503040b060a051008010e0f28020706 80
    0x3c1c02d03c0d4140101410070143c2d041000c80036860b0810303801c1c442c0b030a1076190000700112450000e40184000b00014905201041d00340030001c9190309608030514040c04c00054503002800703001c0c00140407240000c0c003407400d1030310041c0310303600140300c10340c0354440c8030310303070703100010302d40c2c01c81c050105401d07032a2078001403c0000042c600104505c99503034681864071040c03180058101109000113404001c45400307001032500c1c15140703136062200070b40c110390a060f1050300811042039403560001036001544003040e00300c640078034070035840c00707080c0d0740c070341c0c04200207035079103004440303d0354484440480744442182582d5003140c0003800790750188401301c00385401c0c02422507a15035141c3d0005010482c4550020800801080340e207081c600c1280519401030280c440a00b0140c0100104030102d100d0b5030782c00345010000c11005018074085144070001030080038003442600500040400007580808507150315078404c0c2450300b007501400d00300141982800601441d01c4803016803d1102e440003c010744a1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 237487571 1250 237486321 237486341
    0xb09071209050c0a0e150a060210020904110412020111060601051206130914060705070b0606030402120102041d130b0106080421050c010b01032d020c030a0c05070f050306070c1401 79
    0x40d03c440c41c040c6c039010307100568088014042c0003000340070007151f0b90104802050159101b030142c0d036120f070b00c0001005400301003402c00c80140c0010340005c1c0030304052104140c0038400c0c6c82d441d9411003105c581548485040740da042c0131820400070103281150b0340ea09541d00240040091f901e40790080c0407801103c100100880d00d542c51084072400d071050401419601c56018034141d440d110255a81203901c5c1c10190005005104c0030002c14110b65419030300c002000030b80c1000b103458035500d046000c15090000380b44205c400309030b03002c5080d041c000101c464030280c10030b010540a07480c01808403060840100155a001281d0300382900c8040c1061320400100d080d95916a11003910411250131240190f1349103051600e082020310340041141070b02c107440d8541c1460002400c004030b01600180c40307500d00d0121180030025207040e00070b03040451001c0c0580035204442e2805d440300c948002c07005942c00b445134190301500018404a2069000d190614403d0200c2070242a00c050040e0a440c03000c21 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 237488821 1250 237487571 237487589
    0x1050f1015030219030c17270a020d060203011806150c0302190302070f0b0304050d050d021b060a110301030c03080a030e011a010f02190204090812010e0103060b09071209050c0a 78
    0x42c0c0d41e82ca0303035001e0303540307d1102913916070810345003406403119507400071181ea4244419580388030300f6500074051046403e069005003180e200044a032601500a6200340141c540c44241c00d5805007440c4061310405054034095000d5902461038110141d444840120003102144600b5101426118894980c0c003042d1703110390010311500f41800400148036580e0b401c4060300d50014410400469400140c3d0300301510a41842580c42030701110000c00b0344120f021040024908032031030140e030100015030750310614102d002040596040010b0400b01d01c028400504110a504e00a0010030003420027400d61400c1410000f4481410341d0815080d00c280c4c413820030030002c24404182d8139507005518810741c2d00d0b041c0b010344640780c2007509001900040ea20084e0280d56113109050400c41904100e442111041c801c15083e9a590200c50312458001d000c120b85050411507001c40c41d042a2404500900c1c0e20740780d08415020004494004150303824090320300344a00e9850b0740c0c140c1c480302154000303400b0007a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 237490071 1250 237488821 237488831
    0xf1306050103060b030c0316020304080703030203040e060301180803060a0302120c10080106021209060f0408030307030c05121503070302060a030e0f06040206070201260114010201050f101503021903 87
    0x5001400f100d016510841d0300a10410030419025400713400c0301c1c1d010720000c0c0000740140105108030715500554100c40318520075402c000c000d03d034001000c2e104880c4481100c0440755980c07001e0500342ea00040003445501006e0343c180f4000380c0c0341ca01030343d844200074090b552229640d8000a84400c0415000784141d0000e0304030341402d0505554a4401c214503051550a03545070000c002d680d264480c5103965140740215618440307a40c0d240481703584403842e20307041c0c0d25241c0f43c64046880c0e900549000780484d1038001360941c103d000d1f500369101c110300303809444080d5882204021162109a0607aa4180110b11000c00186d0302c86001d0f01c030b002c06d15030b00024052200c140d440d140803503035010881c3c1c07603024104100040e62400d048961042d07082c0b800900079810550b5640c00036920500300410194100004540c0c0c80c1c2414082007260401d074000d022030340310309880e62228442a80c521b000c0900304107041c042000780304042c0c0a00040d5140051078440c01118598424001c0104140025151 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 237491321 1250 237490071 237490079
    0xa03111018030f0e03121c0501030c0f061706010e010210060306061412190305040e0c0702040c0807080103061a0307030b100e01080d0e04090213090516060e09060f1306 74
    0xa84120700312090074081305152400c00003d94401003c11000140203000480301904c0d030245462020003a43c40c28184680e585900e0005a0004e2034010111051540c1c1720000300580310340385c404600446840c0b10b010755210100115a580c1305d0044103810361060794042c2da004403251051200a501a100020780c26040544040040d60f900a25900c544601003448524041c04100d6043d040c004000f008040201e038074090b5164040c0b9807213501c00344003200c01c1002c0e104ea00001483e110380300312020401400703100001d60b80c062003504d140e00080c0c04000140002350980d44015811500f40031107003801c40c594000a850f1000c1608100c514500c0e000901055415548002000e800360803d01d10707881d81410202640c5408806450041014280710b102054460744c0c0007215554010b000e07058202611050070002c0c000e07665048074a8070403160401d800c00244550102500d150f66140300241c5030302d804101611a002e07040c40d0340142450700e1451169116002d111010291400104d142490 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 237492571 1250 237491321 237491327
    0x103051015020c01180b180a0b2b050906060d02010207090213090c080417030a0213091d06010609060c0501020f031e16052208010f0905011d0a0311101803 68
    0x45009071845082d04003a01b41b004004402c10b40c0c40d5100240c2102c0c840c502d840001454050941d40401089130380003a08018a000c031507072220000c1040000508c0c41082c1814000c111003040b100c682c0d42d608041e011030348525006540101140c014030440d0b1407141c0307403503200e000c81c1e20a80503045504410001000342e0b0313030701c3d0041400b0142d0604020600d0b203003a40b41c14112a501c0126a820518000005454410036a042d10f03000101c12048031001d603100d07401100181180b048080d5004c0000ba0802d1450000040031811380d05039503510a84035103080780c00d90b201c884080d4120386c15502072200c0c8025906000181d80305200a0321000d100c00c0d64000d03040d480d0300c0702801c0c0840120410f4050900e080e0005e0840344803610300071110100f440031950010400040741c0040140354240136018003140d115402882d8414040d000803c0a584801090140b1f40009440300700e03140c000c0801040401d00504080101e0450b91099a411901c41c101200407683c840350810220507000c01500c00303043d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 237493821 1250 237492571 237492587
    0x1b030114030c1915051c0204061706010e04020708090409031809060b0307050d02070501060b1b011b0e010c080d06030303050627070c08120109050c1201050103051015020c01 76
    0x7019200d11039002201c0300a0800040e644c00352a030803412507142407000911800448a141c1c4000e040b60702031950b000840000780d8040d11840380000c010040c21643c0090246c81c050184c0d0058541d500340c0400c4405020180d040108141d8101030180b24084080d11280208043e85210f039843e404150100350b040c00d014901c5800001c009450100c00f400140821400c0b0b0350090761908089480d080314020a8010303101c0d80c0001001ca500b802030002d84104040064141502a501c43c01e05810100c041e59088401d28030700c40f494603420030321104809004008109051006150201035014a6120031780194000403584c82880c0e40d404041051507454890305401c01d4086421040c641d90400300d0a040641100d40700922044e01c00c003060380c41b4002c0103500b02c401e41c0240c0d5141c595540d13038281000b85109105a4904c24100800a140510340500702c81c1d02e03070800d000c3d1009690810004400400c0300408400c1c6802c2d8000020901d0041c001024190514542c000d241c100305040005000b80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 237495071 1250 237493821 237493843
    0x606042103020f0a110d0c090f0614010203120a0506030114041401060609050906010f1b03030b0a0f0608040609020301090611090a0e0c0a08090a020423130b0402091b03011403 77
    0x180195905400003400400c2c1c0645000040354406e118a015043c080340d00400c41d4040045203107800c0ca11052540340c0c0d005002252030201d401d0940904160040e43ca0388110881d0814580b03440f0002540b0860f564892500318001400005028041c018241d0710300c2d4080d10181c620b0184518508202c12007401408050812468004100751800f00030030301d00b42002d081503041c400112a0750400034030408103208080102c1002101c159014200900100f03040c44000d80200500c0c40e0115500c0c01c10b10140003102c42556a40000307684607201d80000301a040400c030b0f419520744d504074000c01c1e228010b01f000040040c1005940e0440102000b600b0007184e44407812003504a4100000a43da43c0282c0f01c01c18200e061038038042e0340310800541029030640c3c0003036100d454000c10380d24943c0005201d802d4201201149909605c0c0c8084404a0403110358004142400550004d401414580d69258100d00c00000f060060440f801da0344015400907003101900280001402c01a071a00304013000d848 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 237496321 1250 237495071 237495073
    0xf0503030a0f110415022b03140601091502010204120b010e070c020108130f05030703170705040302060d0e031c0e2407030e03120c1b0c090406050606042103020f 71
    0x104143c002502d414015071041c0c1020a160240c0c0449031802400070380c1c69414180d0324102c030039900d400d0106101038072421440000340b6020301055201021048503010310816100c1440c484e25000c21040d481800406220840d5000c0c403000503620414094035045500c50f0155100541c186480c15060143c002c4c4840c003005000b056440c09030341c12608045e001700403400148141c0c0081d00b4007840b100001c0c140180035100001e8100b080c16885506048121100303030108405c1e4481078805c440d00d000f5404003951001c0c0800c031950980301c10341d01a051865064003a01e05002c843c4078a03540d066404c1700c3e0f401001d52118110140d00d24180804003030000d000106001d042110004d0001419006016900b4140e44002c2400980c5080054440740030103c60010814a0812000c0415030000c4907240c6542510144200c2c0000c3e011070640300b10000035000540c2c84e40c9588906000e41005820070b5082041044045420050500d82e10b100244d2040291014840ca1600078a821181040c00e206 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 237497571 1250 237496321 237496331
    0x9071d070e011803150212060111120d0e010228050f040509250207080607050307050a03050c160803010311010801120623010e071404140904050a0f0503030a0f 70
    0x1e810902034041803200380f8141e80710707200c103003140f01d18005540c0001d4a4581c0d04e00072014594020380080c080d6a08501c8001c003251100d0006642d041181d40801c205500a060303100b401ca414a805005401c0301000081500242000794608903449a00c140316800b1401800d82d13044610704c461441c1c800c24502e030091400d20201101da0241c002c5000302c41c42080807501056400d0b14110548401d001d2400158400424850000e55100306600c1500c2c0d1034003412001400e540e01520a880c03164169440b002e10308019a50114001d0a004000b041078410901c10b12050b500003c400c124454072802660340d8039410360504c800b178a4000c0d4031550410000e0001807000d1840781c1240805541d01503030108404e82401c1000c40225007500010f0010680000005026107440d40501d008d040ca03074070b07072500b406010901e015240c03049008201d054007003525034030703100d051210303010345c0c810702a109a0321201981e030382d80b03000041c0004e005e130341a81c0040140030038682c00b0310500070740c011541c6007005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 237498821 1250 237497571 237497581
    0x50d0914060406141e1b010203040f03032a0f110a17130308070c030b0a140105271e07030e1207030c050d21020c06040222020309071d 59
    0x18400c6001d04001c0110f40300c18018003141242c1a585114502e05c01d8588881900800c60360316041000305440780c02c80344100a4039440e0600c2142e0050382c110082a00c0081c00c0c1d18240e0140500ca1b0804048000d501011444800c80e14001602d0f02095541c80183c0b00310194010602210040ca43d0380d00d4200b04c24020000700348140022414a2040300d40351035a2a022102e5120002e075840581010000035004003002440503190382524030580750310905444910300103046840100c0d0507082c603954580140541c0c0707004512041e440a00002900b014900003400c4a6417900640724800a4248041c028910160208005901031420b00e4200b101c40007800419580c0c11450040200c200400503034101070600c52012107074426000005c64061030103034400200180081c080010145844140800320070b1044e00071515000580c20043c540d6448580800032400111420703070060a242280c9848a803141d40007841c8502003440203440c40914026000d8000b04580540b040c3c039000c0441086 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 237500071 1250 237498821 237498829
    0x20607030b01090f3606050a081605040b030724020c010f080411010509031e0709021611010302120f0603070b0309100c180e01031703010503060a09020f04050103050d0914 75
    0x6011540e14641400c0000c8001114001d01da800c584040b05c202e021019109901c0c3c42608507038110350042c1c030f1185c04666240c1816032204503040b010404141d03900c40c100078a140c56041200d61100050035201c04030355034041a403002c000d202601d4101c10240b940381440075018401e08105e0303802802c003c1c0d1506401c00c0020052400100010440d201c0b005400e20164070800c2522600c20380903085481c12200d9104180000040401e800040d210710b40d0302154110380d900a441e5400b200703289407028090103a881040da40780045201d41016030a01c442031451440a014a0140c1c0010a0042d09401c208003410708040c01c64000409018003081400b90022000070001e0300c035090424006410320700010111850800c80d00a0012010b00d51404605201c8154005040300d01c601c94203002204e4000840c070941c0024800c15506030050340000d500208960000c8804034070041c0390f06540c0c5490000141215001e800643d00c0d82c2c40314000c2508039810a288101515240d494103a80c14005000a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 237501321 1250 237500071 237500099
    0xb0a050a02041a0a02011508100509010204051806030a06020301030b180303150f1201110a0318050309010518090408030402120106050f12010f020d09150c021216060507020607030b0109 81
    0xb6040c926000912074038451007036100c4111541d81a8040e01340948d9580c14550314a04442444482484c180110b42e1040741407085604556001d03243c2e542c2e480403411005801100103000715014010742c40c426002034043c0c8025406180303d07840281f401e080010407507802c2c0e10710b4964400964410070501040880d11200302c2c001d410700b100d4401d882400c000201d00348107107502c600710b110b40c01c10107480e641711004400350004104a0b45c003045151a06050104010300c0084060702a8008102c410120b501c110004e0000008070030b003481c042e01140303000c40c9040604840c291500c050110602c01103180c1810b02d801044079440090003507909280c00100ca0b1814022040e1107803043c0706117030041480a411500600e0f080c02000c5423154a03004050018040c001012642ca941c150112001c0340558840e80b5031500c1146d00900400281414541f841d83c00b00c075a0381e4945001c4044200051542d004d020710520207580078288030b0070b11030000b400355120400c24605010303909405200703c54403c000313 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 237502571 1250 237501321 237501359
    0x1e090b220803060d14010606021203040206040b0919090212180c040e0a0c0e0105090601090f06180b03130c0902070f170408070f1e08030307030b0f06070b0a050a0204 73
    0x1c1039900d403904400501c903011810001086140b14000390012001e041d4405400c690243c0c01740c03105401c0d035000801d414402210020340c025020f1000b41301c4801108050411000302900700c0104a51490200314a556558440c405c42900040d0f1810301a88102109812840404041d000034035140c58286d110308a020380e56003c0d036503c0f09072001c4d61400704002010130344c114038003a01a640701c0c5040001c00209028860048800d50041a0154880c15003541110124950036004030304242088500d506200b00c5101c03000442540856090014030007540030300d50840d9854004865443c0501c3d0a15482d40120f46580c8103021200100d03042c1c5d02d1146c12641e01c115189840f000e0030071004040d0140f034002c6241481080342c046111b0302c102c2e0941c4203a813800c402d500b89105034072540c130100041c20300070f00f00f040d0001e202003180580682c00c03410410900404428150022a020900790341188a060725020350040c01c1c850141024412a42c003c20600c105614103403c0004402c0800d80c2088 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 237503821 1250 237502571 237502583
    0x3020c010f0509041409060105092e0b0a0e01020f010e07090f020f0301060c1403160305090103090813170307021507080705060c09090a0c140c011e090b22 68
    0x1c0d801c802030784204100c8a0080f0000c000f000300c8407960035500c004650807104109a44940000801c10346407030b6031618440c02d1000e03001100f09041e00300d6000080c8085201c9010a81c401d0004a00b02c090b0f50040d0007140a0399490004180b43d000009151582901e07698510b6450014a0034a034000402c8034003c1c0e40c242c003408103401410085d102e009104c0e8000103100054040b00101d2850340c041c032421805401020f0007040041720440f40d1385c03240315125a01c40408420035030303a0b00081c025009043e403103030f0505001613039020603140c0c6101e90b4010882c02c00c175034a090390107101d03100290030708100e6035807080c0095007440d0550303000c15199451500c0d11000140040380043c100701d20141118040c0d540402138550504082d2555007064212b6907440b0710407846030f000039104c0d8043d84036520f41510140d4480c03030840304170790000d80c0c558000d0b00b00e0354181d503c540b40c4a41c80402e02d0606590710302c0c02000000d190342c40d0b05085181d41e0380642a40e00d03143d004180d417083c0e0030f00ca03c3c40d1420300d0b400030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 237505071 1250 237503821 237503837
    0xf2d0109080a03020123010e01030f06020d0e0d020d08010e060603060a080d0f120e070509060d0b0408070606061103040b0f0c0a03080a0b04060308030a05040501091401150501030903020c01 83
    0x401a60040115400941148511202e01007055819000080604610f944141c05405d024841c00039501007409081018021b030001040070a8410300100f1019008420052511064106210546d05100300031100c80d8030420b610321940d5410064614002001e28021100d035041141500c0c54100c09440c1c07500c94800440410380320b50300c00c4844002010b41d041195500d0301712030b0b0003400340c8a0318038402000c00c40d400110385003c0501c1c019003a607031080c0030141c0303080d82c144802c100003071001a040f550044c8a4481000c00031f40c91440d0030b8051400b80305040d0700c8003031174070f0440241e8415400020030040d8011220f940c0800000681c0d05498410000310344800c5202d8403205503001c5c1c0c1800030094411030240d28141600514818041c08072004244015501030080c4010f403523040c03000030801c0340700708001034a4103455071010b43c00c24482c50010644200a480e50351524120000740c00c183d942d40d807050340115000c1155000241070070b02702800204c0868a003c1e40300d13030404034101d042c04010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 237506321 1250 237505071 237505159
    0x10e0904110a0305012901080a0f020c0f030d23040b0a09150504020f1e060702030a020a0602150a0b310e0102070506061530070e0f 58
    0x501e003010200140981821116a6203003040341c0600f86c181a196600441c114101a900e001d54040c0501d21206843d5a0300d26110403061000600c1c090000c0094182d0901403403a09000901524443c0381c1e800d0b00941d11100e8503080001181d80c2500564a80802030f60341c070b00440d02d55007180d9880303178200c400841c09503240001c91003c0c141d64040101007555201405801c41c0c11940300e18081ca0090b0b42c00c10354500c41c0c106100140c0c403098000c200c040908075000c0c0543c60903d000f092503501c0074003519004012035020921030030582d0080e5026030090242e16140840000313941e64032444802d000d2040141580108000c0c2c40410345c0d0540c0002640f00141d135000010340018100d00a281080152403081040d05000f504542411501d41c000c860109116190840140c103d04050780320a915145406003a40481c4c18540680c08561060380b1601650140c0f400d6024420b100a032290f20441c03601e8420091609004184103115143c00015015a03480c010240090555491002c9601d094a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 237507571 1250 237506321 237506333
    0x5090c031e0a050f100e0a0209030106050907050703080a0209010c03031a030a110a06030506060a0309051002041202090c0c0d030c020c09041a06030a031b0f0f0c15020c010e0904 78
    0x55648840030780c1121005001a680302603001c3e62045000c00b44014203600c0e074006000b94804c86100300910105840089550a0200d038018540900000c0c000078900d907680d004201031960480750031713011071030125000051617000245107074004a02841145403603030352000070b03144800320301000e410141d0322110042d0076420303501c0381003201c100202107039114804c5141a98030001c0040d2240d01503d41407100207007840c060b0142c0303030041c600102494102001e684040b001089182070564444c0f00d200011203114071540300810181500455000d01343e110f43c010702048a03000382401440340b030200518580040e0114002c41c2c031800a14012640d02e008460403840c2c4a0b07501c600c0c0e540410000c0c14030041200c0c041000c00e00e004420b0082c6020765502c0704154503902d800d407029011070500c00917000015101c1c02d546078154810612100d1000e540c0e03c070740b0070b035035501e08046840340080c1e40c00b0b00450740145030803841a4014401000c1070390b0f80302d00003400003413400c1000c1e0181c03013140003080c20011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 237508821 1250 237507571 237507601
    0x1020c03160b21040b070e0a0609030807230a02040c1106060f0f130b03060a0b030a24020403231f020d09050115061701050117072307030207050a05090c03 68
    0x1d402c000c1c43c03030340e0605050044001000351034404c00701307050903d030701d00314148418000116403c540312890600d19589541c000769005080c00c440311022240c4451010545142c811284030301c0301d005000340780c90b40c0b05200403103e60440c100144203400700c52060702c0f40c0c0018403650000040e036003090b0b01c070f414802040c10f010480107442d40c40180301e09000489801d943c801c1c2a91141102140e050340c5481406200701d409050782d454054120103e0f000201c1d0107108150b10304040c0001607100100075802c1c400803a04190130441e200708603480800c4003c1503200380b0341e81c0f000c0c440028082c3e0342c41c1032040e1460056070ba000d00c001c180e00030403440b00d0f01c03115510907170781a90050000c1c03000b4001c035280040005658001c070408a400a48401800e510082d140c0781a02d0041c1c40300305040c03880210800d0014002001001081140c40340701600c494039103080c1d0009aa004241f0b0703155006031401a0502d08140c02190107180c4e02c030002c0002c5d6584003042030b00610b04212640d601c1e00d071421443c080c24 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 237510071 1250 237508821 237508867
    0xc1d0a0c0c0507090f0b0a0302060a050705031e030105190503100b010c06020a0305040209011a03060402160f0c17160302010804030203070b010305060411040209031e03070c0306060501020c03160b 86
    0x700551400190044c800d8006600030206100f00308040310b203481c10032080a189000194221a05218500f001400341000b012824000c404030781c1000300c0c02025124822403001c5200103514044010086070629014109800d64404c0b18260014100004280e407510321009850030541c035501e0b03054091f400341800c0c42a450f0405820b542d140008900a4081c0078103a0b01240508506400080c90034501003140a180300390808003880d40d01c030f220400006e0340000002c5608103001e0303101800000c541020704004a07100f000c1451440789407058550b0000c10020a602c89900710450010015010740c2034801601d609083c40c81054540d8202240b550080f03050090240c29144004820b20400040c201e2290307104180701c2c64000d201d841480182c0c085c00d00040c0c0c05501103440b034100b030301e1080050200c1d20050341c226410325843c1d0300c0343c818404c0590b009940d425500c0e001845296070500645030303210740690003010001c102c1030200c469885644503890080b0b4010a52074035070012106020122 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 237511321 1250 237510071 237510073
    0x3030b04052a0c15091e150606041d16031512030201060e0c0418020a120507050903100509010e0a0209190207061d0606040b060412060e0a030c0c1d0a0c0c05 69
    0x1c0c0d0401c100313070468000b007a910240030340f1402c15284000070308104084040700c0e07030401410031414000e280703c9840201078141ca03030280042c00041450640d0a40301002d80310301c1080d4241a041c400c1040c2c54500079001c411003054100040c84610000034015030b0115041b00540441400762424101d0040565802c181c8840c0060b0042c46428030040c40500203550030000410412404e80d03140004070711406001002040c82031407400414400c6902035a030058041c00d081c0d2034014035000003810100611644004d4581d11414441c90740303424401d40403800680f9000784101f000c0c41e00066500c2c07000500040d130b98000382031030405028541d0160b549842c0d011009100f210a5203001160686280889034450f00c40c24000944610b49801103200f81413019042ca031405062440f80302601810b140144c1d0305c151900c400a0340c3c100104445030311207001c1e6072400f4604d005460201000d0549a104150085098560014a20f00d8404441d000700c19004000740c4082500c00a40b003c822041c00a01340d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 237512571 1250 237511321 237511333
    0xf0706091e0606061b0204020d09060203130b01120305030c0c0106120819030915090f0c0b0a0801060e01091215091506050d0c0e0c13030f03030b04052a0c 68
    0x20a900601c4501e944910824441d1640b1448101c034454441c02044082000b00c0b2850005420954000c0c0805501d00f800070446c8001303170706c508042e070b40103a07030581c0310a00b44071a00d03040c0a0070340340503405402e0418a00b192314501d51402080c40c00050300c109440d6a0018195070303401b009500c42d1000340f039030713170703007048030000c2c2418015440d82041306004001d10108030361580440c8203208404051382e001d4001600c2c0840c900070300009022013101110134000008400020403012550840108025500305556120000e0700902c5d540d01030384807006004000d01189256a045083c200c203540d8000c0624265590608040210f9000d941001001038a0a40d1000901040320b03c084403540302600d00780036007556081030020540594402501c881d52881c400c2c001d2a0501207001c0d0058400300303c0a0603c2ca40140b1144007100c00d51080b00c1d1004121428030803d03815000300400717902c04940400080c40e00d5100210350081c1d24000909004020204c02c80c4414a0030580d61905600011145 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 237513821 1250 237512571 237512603
    0x304080a060c080f0603071814011403070509010b0d09060b10020105040c06050412110f03030a17010f050619111618060b0a03090206120703020d0b06090102030f070609 74
    0x50680301e0000c2d0000390000c001500051140c0d50300c900074a80039000b412024900b03045040c00b00c5030365100c0c54a00f5192003660031416280b054a40c040c0a200c0b084111902c0004200b51a0000503807101f030103510094010050242d200d010b54064a0014102107007040da40d28080d4000c14280c0302c400d920400840030300d0003003641544050711403445a05400c00054582c0c1080e13515004510030b2104a060303070110140080c030441c610724011030000d40080340000a440000382150005800c08000468174010304914140b040640c90041482d00c03d294021030500c40031450900c100d13101c079506940e40210701340c569446000c50407012400c60066030300c084200080c0442096080c80744110340800101510314004141c450a81118445060285043c810001c10380261403080d17010b0303920842c140041c800b5000c0200c00e0510a81c015540140d94650809108040301c0003826654010881401000481d98000040b201c8080d0640c10268443e0401d02c4e080003d040e440c04000e28001d02c210a010b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 237515071 1250 237513821 237513833
    0x40909060915020c0f011b18030218041203090317040f06060902090109050f010801170c030d03020309060a0c02060106030f06080f0312090309090f070c060c0504050f01140a0305090304080a 83
    0x1000d00880080e80e00803510304038107601f6070342c5000c0c07408005100502d4888090780681c507030600040e0b9454900020540d6500025207000c44100390f001030315925030411041100101ca252003080c00350504000c64000c42c0c800400006c00e68050300090500d00b0040b9090000b1240e6080e2040d034881c00038031030785481d142c10601941041044c00c0c08254070000128403468042c2d1014985074060f0348000d81d41c0c4c41d00d642101c2c503003030502e400b04050181d01200d5809031402c1c050403140f145643c0380980e49050005c00381e0300d029401400815500d28244e01021429030200c2e016044880c1c914000c107504444003a4480103115540c4505214231a40e50105660740d0040060810384034003107210901036403051081c584071722480c10311640c0241d4490020b00c922880000c015002201c40c0341c0285546525511102194845408400820740c042010844d5282507000580400c10a2070004282084110149098000c62522200303140c0c55000141c9409401c00030b58000382450411250b44160500f405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 237516321 1250 237515071 237515077
    0x411150903011103010302060706020906040e070e121504080f0c010905010b010801061d010c030521010503060115120209061611040f0203010b090d05010b03070e09010e060c04090906091502 83
    0x289000e94208040d00703c072080c090003034030b040b01e0300501103d2030000e079503a40c04002e5200c800001d9106005205c0801d0100755401e8842c4110303901d890b2000c00c1e116920801c814986821000310480d404034200f41d0740120240701207a04941d208690039214840b19044020502580402050540c030b0304000c5000d001c015001104d00c0082070300d41c60100c0e600c030310003210100458a40c114800b02c1108100c00c595208114650800d8044c0c5492418181c3c5017646072140306030006d0750801e0030803000041c0020b10301132002e280103040c2c412414004a001c040c02501002c009081002c01c03039400f089080445d00d03401c0c1101c000381c00d0030000e00d05849452070591045030301e0502c0c030740c01503280c81da0b41141d0000310f1080303038140e03100c408405041801020070030164013900c5108131815525911010401e1b00d041007108041e00f800c408202c1d403442c15403503e60848401019540441d8003400500c40a81070000480382940d0306443c011401c03c2985c1459406070540c03642c02044a403105044251800c1a81d0203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 237517571 1250 237516321 237516337
    0x2041d07090507020c01170604020906180405010509130b15150408010b0f13021c32010e040b1f06091e050a14030a0804060203072303070308041115 65
    0x3041025850740d0030100e0b610300c00417a510340410405188901e0780011035480d0f17036000b18010b0000d07292551003404903900303400442d243c400c10104c540045644d07207024090703240540001c1d100725800385002c10038910100c0039610064201201c0740702080c15484810085880c404000d40300c04803a00300c042d0011303034541c02882030400c40d502e4079580d03001c0382c41e200020143c10344004210103144009a0310600080d849580c2c88282c0301841001d00c240b50307403580540341c00384000c464000440c4041d0070940050000106028007841b4802d401442404200656143c100e500146011102c1da554291a516459800c54a1000f681d91590004084d60b00c1483c940c1034440a080760385413072041181e0403041c2c0c00f01d4041d00750302240f44503003808107030010381005206000040403520781482649440d01103600c070b5000040180c00c00141c00c000c0c07010350525564951144105159600c1c4201c10351520303806403185c02010481000041024040b0308180342e81c040100401202054903c4101c1c0086540310942c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 237518821 1250 237517571 237517589
    0x4050f0f03121209030408100f1803050316050403080d0914010612021f020c13020d020708090901080703030503070e120105070906030606140702040f14040309090b09010803070f02041d07 82
    0x4c402210102c2982c0c100e0f1a2040180f90b002c1120360094054600286541c0d101607951910303010100c01074142c69072840c001e40761180daa003032100c00034040d994002400c00a201040000b080001c4c410030032951a1201b6810015a604461900c40c13061100e20703120f01460342c00c0040115411001c00320008801e4401c8411590441d0b882241c3c1144444000c40500540c000d9031710340c00b050a140003030100d4100c0e120001450305920410860480e04074010540342840c0200340c11341d481c100141400c0c0074141c0705004200240c510762700200f0500c402800d4908000e490005600c040d00c51444400343c40b07880000070702c51803402040042a803c0c50788a4a000641402c20004a15014100743c640895038600494508007494003444098602000c1601c500340d51410340c1c1e0151096040101d0240384250b4030340c500c640c541540342c805c1d1940300c10003074843d0803001e0040000000000895018503449203112400d0609c0d800081c0080c250b440e06071b841010030100310540c1c2c840100b5005d007907a0010b1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 237520071 1250 237518821 237518857
    0x60f08060a06150c060b0f040e0f0c121015030204050408030a0b040605010c0816080a08011403010605130e07050907030b1c030507231c021506010504050f0f0312 71
    0x4400c03c404410260144400314030481e41c258041015034000f62101030b00034090048008a5101040468460504c00d06050f005030480000c4090148590a04001c00b00c503444d400d08503c02c803040d202c2e20840d0000002c2981c81800000c2024020315503002550014402c1020b40b8041c281072131a03070320403512588500d1074602c420301d0600d814460001900c82c1a51486035404140c0c0d12201c8540c000100c0f29649507020100400060040c0c1c02080201c0c26661039a00035454545150900e445071660140300c0d0741884403d21242e03c610348003001c07410b1b804e01c1c0860b6048020361130b542010b40582000e600714401c01c0801240c1c0d501034101c0c40c210541136070708014000a008284e0f500843d40100100041c1c1c00304134520216034641107181e01090318140e0315090308058407195140140d1140904030100750402c0c900103290301800900c80d44840000262814a400e100081540c4214099148140b0020403141c5140d1500c46011041d980084c08036401c0c070000e400e2649c842d400201d01c00c802d000100c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 237521321 1250 237520071 237520079
    0x3040201020d0c0c05010507020102030d0507021507032d0b090106081e0606041a04080610060f02030c1e010209040213080706051e25030305070207090b01090b070501060f08060a06 79
    0x20f52803881565040b0102800c0241003100455071540040010380c1103200910541001d00c4c01440f49a0090f10640c0041000280d404065480c000c80100210306052800c401c0c0313021542200e1483d004013005075206005004c0003803100000b0b01ca44541141c1000345100007003540ca401c0644c0d03030300400894403103541c5900b00801c0030008050865045070400c209010411150206c03024021008110f80d01d15400c1684441e0401d14112040f40e00002016100f0010407440e50800c251204520b01d17403014502d003110400c00d603507903011030f1840980b0311446892001040b030b50a6050350700c20301000300199501e04041088180c10032180c040c01c002d60286100001c1c010b4010300c2150303d511465289100c01001030009461150841c420300d1480305524141002240c111840c0020b0181c42034400144a00308807000926282e165000342d444c9900c0c14100c4180c07682c10500d801d0484000040050381c603402032406601400003a4401c01c0d03254407401c404205d050b00441c03002d01c1161504c0003040b0090391 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 237522571 1250 237521321 237521327
    0x15060d09051f061215060503030c01050f06040204080a02131118040c0203040509070804050c06190f08070c0803041106070804170303060603010335130f150f03060b0a0503040201020d 80
    0x4c0c890400c0c15020514420b0010354a440402d0310f0030a610000100190303a84046411540700c141008100c0e5501d40170810b001041c1c290190308540280ca00f141041d061002c40c40d0344000d0044068464410b0020811030100113030884c17580580240d2116445030039003448002003030300480141e0708c16800c144c11008858800000d850441d14010250005600c0b482d030103039080d0402410594540c094171480c0c4c0010b0721a600182900041d042a07022100ca40c03d43c01013681d500403901c0070402c07641405021031264070110b008000c641011003996244c0702d80c980740401030420a00513401020201c0c0d110140030b00c0300050000c8401c400d1f43d0007000c45a100b07441c1d8a03480112111544000140014000300d80110b41042200110054800c14000480510360f400114940c41d40b00c20800000c0f142d280c1c06a40400b4401840340ca6030000321281050303080208009510340660070041180e100d01c000300c1c8203070020070090003200d13041540c40301902001021907104540682c0580700701191100c0c0244 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 237523821 1250 237522571 237522581
    0xc0108010b120f130203070e0a050603060708160c060606210606020607030f02090414190902060322140d090806130809011403090f071d15060d09051f 66
    0xb403600228002c03a510488101c4a8010203032000710060710800071100181c400300410303030103003080584650301c2c1c0c5013140e0741c001a614010301c654082d8200760240285180c0108d541604007520640700340100452001c112801048020094401740c02c0c0240020202e40242c40862102d4000340d00407c112410303021503080e6903551183c0b200590203080050085031299200b9500c400901d48094a00842d81000900781c80c0200c644412065649081c0440200c1841c002400720f20040c00900c0b01c3c5165070001405401700402030304007840440074103030713440c170915000054442d449241c910440381ca22000b00c0da2020a000360b80013080c6440d90105030120b002840030320480c010004c10310703400b03119036805c00c1740c1e04410a03c5042c04000400000a601d00c20003651241007510300400290b15603000207460700d10039030700405030540b512800e1904246d00740c012640c00b01102249441c141c08040200b0140d200c0d00e0321b01510340d40b4044040c010400085a291600d840e8280030082c81c48403102041c040711 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 237525071 1250 237523821 237523837
    0x9061b121303120314090c0f0102070b03060f030109021c060b220f150305210f03220f060f0b100927020a0203040602060c070b0c03090c04020406020c0108010b 70
    0x1401c200104000750100c2a0b11540952510f000314a0a245001072030101d0340c15910042c1c96009040404010b06100b410869000e1091004003d040c0c5440c0140b9002d00c00500f00c903000e154440c001c500b003a00d007500035040c07080d0b0107000c512900301002220000c19048441c01c0303e10350f0030010701c400d0a1510326182641d5000d1011801014656605400d000b0507a4a070b403aa94961118510100c0b452507104000003140181c028280c0c071001c0c07401d2105d800d041c0003491a200c0b0424012440f80d684038404bd280d0202c0200d1a81c04c10b40001c40c1c4052a07401081001000c00c00350041a504000050f0441e081000c0d410318240501003a13a010040701c0080c0c5200440003410801040081d10707508a5800d0340c9076142d50b40f51641c0c0c13400114070070681e07100c503200202582c0300240400c00c682e41000b056905c041441415400c1c28200e5454100e0180050312101c1c0d005808404650042030602c001c0307001220050003159916a1200f0280d150380b2140300c4580410f01c4000002807a0a5200484400b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 237526321 1250 237525071 237525097
    0x10f0f0603091b1701111207110c030129010207030206090613170d091410050d0209040608060108210703140f040e060901151d0609061b12 61
    0x205040c04030031401007803001c400780c4404188503010700541040f1a508005041c546414a41c1d0300c490302086425903280140c0c01e020f104041061003804035104011540020355458402a494a101d410703614002d9100700701541940381c01c460745181c4004198091035542015542c0070280c100c00016038403075000e0710020b904090b0030071180c549403404000174980201c40c2008254119180d07180030000207000c0d0021105a8003070951400001c2c1c100554900a0004c0c8440c0c0071804001800b02c3c84003450056403900340680450700202580107070701603c44c1001c000d002004410f50720300f08143c0e907440a11a0250a01030b4000b5600501d80d111850810f920310039400c0d500d800c10555086501c1d0183d915401e15a90084c17000520301c0e48120000c1c40280544140c2d0121402c1c00405c01c08001c106a11404050504110803000781d42c00c990001a601050460301101001b14000704425201e0b0440007a4010b80c0012488c111518154001d140300560400300c1d01c480c90b4280050226201c2c980a81f009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 237527571 1250 237526321 237526349
    0x90e0c011d0607060f02031515040b0d020903240601022a0a0e0c04030b16020a060506031f14010504020903030d111902010504030f0f09090e030403020a060215010f 72
    0x10340303514044140c039405002c182c685242c0c2d03100c0c001220b4610a25500158001051103000c5856034510342040c2001c0340c407404544062041d0400511541c451201d0740d010102c1c81d0900c0852541c16101541c0e005030940f00e0526442160300c00008030030300b03142c400c0344400f00030400552002560484152544e034a01003004590308118007066000c2154640c8411840d0380130465000d00000c031800f8078107403219280c5607815450400c04030030f801401c0140301d801081c1c16501d0154005400e4034219003025000840707485050100c3d04169030075031100b4091009100c0e484400f90564080c2d03202800030003220925903201c0c1c04010681c0714100400b036141d0b00078409031070080038a07800040110807408040e858160740326200120384418205070b102503591740c8100010325400c44e00310007881d41185001001c080324010007606014140c065814030640d1110142140f075010000c5034061a0002d000070f0115580d801d009540701142221541c0361126034000007441c0c0250305458003520020110014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 237528821 1250 237527571 237527597
    0x8070f020705060904060302040c1e050f070201031505060c072310080a0612060b01033b07030503040e0105030f0307020303070f020d15020a020d020f12030601090801050f01090e0c01 80
    0x30007600030604c0c40d6402940e600002005070394500ca00e4000d483c943d03d170a85602e001c020000e103120907a40100c000e104041154a1900940000b02c0d0a910b034242000108103800070181d0445a20ba600710380d0b04001c000640c1071226100050840071112603903050101d04410300781c0c0901038200e40345d010b90416681500c5038012801051140d40c0001c041000054159540301c01c2c0051040404040e200903039540e40d48580c80d43e245c040c000300130008914640d10140881d041c2407001383e000d1014440c885a41c0e01d40d0300500c0d400e00c42c0800030b50300402202c1d291a165242e8824140080c13080d588a84500c0056070288074000c000da0f20b00e95001005035040c8045900c0d400034001022030120b0784591000100000242c00c540700e05801c180200c00140c07107400008010303240c140041d144000355480030001d0700e803079a000a8000c0040840c3e101c0a1b840761280c0c80161245100c035000702c15554202020005054202c103001030407106104418042c03281d005030001e4444081429079400102d0014802c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 237530071 1250 237528821 237528829
    0x3030305041403040914060402090d060c0903020904081908011d151201051f180c050f0d05071404030503030612031908040213020a210f05040b040308070f020705 71
    0x641c1c003a0151101d2602a00462141425a440703904801641e80d40c81c0d60401c8840d0b0442da03019405403041c1d4085107020400f130300207014030840040c0103201c1e0741c0720740c00345040301d1190000000170b541c0505600d049091528016860307400c015507aa000703503403071205031a10a1248070441e040303076408030400518001300e0500801005009000050001301449914040e8965092041c4c0c40c071070141c00012075003401060340c489106027150415040404000c01e11410640c1503607054258006800050701c85601001503801e8028054092040301d40031900c0d200308041070308042e1180510b40d0b5454142c01c103420780c20b2064000c90001a00035401803000800c0e900300744028880171003106084a051071240101140100b20407044800024103c0c81800114246000d100003001e2074404158200366003180003e0001144001e4150300d10f5030100c24100f0161aa80a010707512851329042c442840c0c6401c00c0174410700d0035101103001482c20000034070b910348141c0d0380041040c01a4050149907180c40104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 237531321 1250 237530071 237530081
    0x30302070302150906090d180b071104050405030403031106070c030818030c030c0c101b0f020418031106040308061504091d0d02010908042c0a020c0709090c030303 72
    0x12410352180e44041014070b108800f00030b1058034040010107092501040881c00d0500007619001400303010f407883c1c041c44032340b00700407402d80b0b02d0b008200f500c0d400e040c1041c035402004007405a400c9480c100500c02406800b00042095a011b5201d00c0741c04403203600701079a1000304a42c0580040c030303c070a9580c0081d106031220340d00824a02100149800c40c5d4000506644c42000d0b940d0716580005040c01c91140d042c403904250f894211040300c4c0e400c50304900500ba801808038504400040801403608025035402200d6020f50041d10030020f66000e43c0c814011484110b9065000c600d9a507894034441000083d154400c0c6d605540f040c0064030b078101805441c042d8500500d4000c64148000b044200b03030351243c10702d0b1820030690590724030003c484150500502c01040c50171a4180010070000c65a200202c900310b40300300d0302044911200e0404080c1a20301000c814040c0d140080504c405040300d5001380c00d003820040c060ba9542a42c0b510750310101c0310301e084000c00c6056030410400101c4d0080d880 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 237532571 1250 237531321 237531323
    0xc06090619111c060f050307050307060e030703060e0318221d01150311030303010b09060a0903021002010c08010f0e0f060d02180106020714090a0905190605010e0903030c0703030207 80
    0x8040d0801d0050f400050700d03040c0c0c007240000850343e0b484040000e41c03540f03165680100401e40180481a007000301080e111291802450140440d0200da16125142002100c0066410910400c0340703641c01d041444d03d07907001180f0703101c002c102c0250382501c80c904501c400c03541d800282c00340000c400b020080d0708094081401c0e084d90b0040685410310b00c040c020302403070909205150656000d6800c606e80b50444002d8682035a000394010b00c0184000c00103003080703d400e482c080301ca00d611440f00c0c110448400c0b0040e00000d4010b050914140c002d075070150042074141c0e1207619284800da0325806c40c41e0444203544078010740f4480302404a104110711030090754001e18042c2c560020243c541d000b040c409440c031541c0a55445405004000d00e990510440002d00908004440c1d100b1100f000540350440c0a4640c011240d51400c0e07680420000b040784481c0080075021012403000d203824000c000b4071003449160301083c0713031200080c4010303000310449114481e0380c8842400d04e01d080c2c40c114000d401c0990 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 237533821 1250 237532571 237532601
    0x1b0b0d05100f03050109050d0201050610140403120503060328020d0f0c0f0608070801030b0f0a0905120d06050609240f04090c12050712090305090a0b0c06090619 71
    0x1101240714031051000b4070185006100206000d4814981246006089a120011a490700c01444407681d40d4660403041c2a0403464551b680d0132681d01203221912540d4802001410b24590409415400c24091403040f20110700b501c0c03040c580008a80301e0490200681c03c588509120030310010320b400c52880c00c0250007a6482e2007046100e90b900845450180c0001c403490180100070006c044d8040d802e80d03448a01c40c54070014551441c1d035405007640b000392104181031415030008170884a43e500660109030403a04a81c868546c1804103855a0300a008c808451810a0740204803400c190040f10a0407102404210401080c40c40c1c7d100c400140c1c821410b292038003005100d40130109500908007030f100740c11000403460003148001c3e021800301000740c031100d07041c9000c000c0710f030303410140c403015803005180e0204d00001a0b250403260380c0714035111a0303800620311601252011200d000740c544920001d08580035900ca0304201591100f048a20303840003440d0314008100c0c880306802c490180c1151074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 237535071 1250 237533821 237533851
    0x1080c190302070f06050103021c02060f0307022a01110a0506010b07050f0f0d031820010302040f080a02030d02030c0604060b0a08190b15060306041a060a030203041b0b0d05 76
    0x142e160050f4844c0070302c050742c2543d00d40300140290314009400945214664500303140d16005980414103d000e51041d9264042c00031002444d418028041900754241d030030304203a9940004008600c50342c51540f16140055104000303040b040000050310222590408001e15450b8645810f140c150b5002000454040c000d6480c2c21106c04400c00046101c1220940505084043c0110003003c59500d00d000000c1c0c442c0206640003c90b441840d02040c1611074824071450407045801a006849036a201d039101c0c9c05a41c00008820402041ea40c410910840649403d060500d8040b40c1d01c0c0240f60034541140c01c00004030300001d0095000e0044510302a14a0f007480e83c0d14880c01d414050310410a44c0d43c030b003000300880100106850b611764400024440844020b410b0400f01d030306400020f1102e4010707544d444c5140d8080741c10808003042800d005181c031307070389101d140c4e0300402030740054800302e60301c15541c0312a40344c0140c110f15510a030381510500d40c0c01d0040c9907001c880908009040d8020102030b00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 237536321 1250 237535071 237535073
    0x70923040c08030a09051c020105030f06011119060b010309031e031509020d110301060e010e04020f030c071b03330501060512010e0f01030f050f0303040c0303020c01080c19030207 79
    0xd101130300c00007503107842d00000c091411080c04071442800003c4038001500c40283e50050307820409403504000104040445991a140141d07800d00f0209048215841504100003c41000300304000c4a41d200748000d010091a500054081d10008900100424241941d2224401e07401118203da100e5900c3c2c04200009981070490b07560065401c42c40d48070741c00044241305480c15000750700d00600607031041c915541c03410302c004210f804580c00260400c40313000b02610f05940d4540584000030124036003076030340317003444600109a5442034070101c1d981041030400340d202d045200b10364812207401200b0100b03802d401f00d0454066604100380f00f44000c0054650308031000f40c0f4803c0394040c11143c0c951035a1100214002070602c03405903c0b070000468548c0410004d0082d828410f411258445d0406004042ea0700e00541000e0405110103014800441000248001c0d00301c0c510840e4040d4003940c01021000d40112030310030046440690000042003c0000c420510103100d00b0003003d443d00500300052 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 237537571 1250 237536321 237536323
    0x21219020904060e150102070b181504080303010e0f07020d080601120c12060e060a090213122402030618130807060f06080d1403040201120203090a05070923040c08 72
    0x10f9a0080b1104010704010004035842404c102c19041c2c07030074001000c04030300d0722811101c00d02c210400d4414800b400c800030010340d11a60650447c204244803038603203664880002c60b0740c03500248544400502c0c400c2c041100da250142c001070060b0200e501400e10003d0f0a40251201c840141c121410002c5105100400140314490342c0034012055694060517100c60300210182c82540d00490f4400c0000c005120040d41e8403901c0b903045030441d25000d0b032200e2184450210001d13255001d4150b691318a081d0f20104200075001c80000051484101050f0040c54010003c078002290010b1700030b1000540440091480080e0710342c0581441d00071151503005680f080c4241c0c114040484415484086c00c0b058040b1902800c4042c020b59002880585160340000f043c0940c9241d4a840e03d10000010400f564420307130710920280d001000030b554034140400b40550b52011080156007a0046c4080881d81d803640d8043c0e4042155100c1482a40303080805140c01c150001500858440446403000102814 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 237538821 1250 237537571 237537581
    0x11d0a0504080c100518030909060d0201020321040c0906180b041d0c0307050f0d0f050309040204080313080105060a170a05010e0706030b0303030115031814100f021219020904 77
    0x480028003045d00d0420360030300408600d820551844a4009100000e400e4882180d01d81e4841000c8541010a10841c001070f82188910b000c01c0042a10b4803600001d5000541d50880c040c9109040d0452015a146c0c000c0c07085580c0e41c01230305882049142000030b4021070303400c503005140c8028000030701c3c0880b408504141d07120958020145400002815a651501740a2040244030554001c03104641074030010b03600004503140141050014221401448010810b4513407011020b001150b6603a1203000701c0341c0c1c81d00b10002c841061124243c3c00326001006024460007aa4040c10740e0b0181d509089400f14422807080001050744110b586010201d2024000c950355081104c0160a0890800c0001000e03076401d00e03860740c0258410001081200c0c0d41c002c070072440f41d03250701c0c001400001c0ca048035148640301a6000e000ea4207824604d5541a42c00b10345c3d0100c100088000b00440c0b400032217090164044c03002e11540048421000030400744083c448040c544004900043c508003d04c80040d0850f9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 237540071 1250 237538821 237538843
    0x3090e010f1a030105010203030c070c0f0f0504290111030c0303010b030610080103080703030b01020a0b0a020310091116171c05060108150f0f0405010305010c0305011d0a0504080c 79
    0x1a100050401000c0c1058103501d1080b11503078101450b541c1002c00207903803480701610841400400090303500621aa050400c40a001800d20085d4031a99035601c40351030209601800f88110328005450214182603489403140c1c0d011700e000705507600b00c81d1006565664601e80321aa09001c1009184c0c0c4c100d00038802180a0030484800b540c4a050090a10030100d841e2100c1400780b0102d00e0040c004509890140c812047d032514000c2007035017414004034204071241a00500100e0711300280b14003039029801841c4107150381041124000d075901294000d890402c0044e503402501007003c0d00ca6075400a5180f01410701454170f0003884494020b104266034003500f05044891811845080e14101e28050141c100100b440d114107141001504110314108124004d8840c1010f0181400304d0303240c0000301441c11100920401003581e59040c400d02800900b00030500081c5840c0000c5601803400351095800c003100502c0302ea84d42c1e5045141030003040c02130300640e02100c0a0044414078003007004550a04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 237541321 1250 237540071 237540089
    0x10020703170a112419051509070306050609120106240206070c151a060706050a1b1d04020706090302100606110c0603040204090605070c03090509040809090403090e01 73
    0x42d69210b030010300442035031002c0000d580040d0940241c3c6070030144036115240f44507002c61041d0312840500030513017003070981e100001810700e020850180100f20710b003d44080c040d14544e2099030360a008a0486140c0c0c014560300c041b00780010082410001c0380c0c8512600140000203180c0e071a82108003509080c003121410000c5400ca0600043c0d034103001d0385402c10110300389685030403420342d11903401e84800780b40a000c803581c4a0120010b011420080a00c054016022580d26a064146a00600b604036401c00303101e4141148825540103003c08122085800e6407069101045103840c0030703002c50240f07149584584c0038460040410310511441c012540300341c0041012420914108040d50000c0d4408014000072a80750305600001243e4642408007c86507a5a00d039158400640200507459001c2c04040c03800d400c100c00543c11404d00401540261941c402195544082200701003044a0050100c075051040c4455800c1400003140c0080c440c0c2026000f150b10f4841d9074401c104241e01c07510382 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 237542571 1250 237541321 237541327
    0x90d050a0510110703030207030201090b0a0e060c0901020d080a151212080705090f010302120906071409030a02101b03031a0a0302060403030819020d020405040507020a050c1002070317 81
    0x30028200301c1c219841c0512036090003d401141c82082281c0690600030b0240f40d000522082098401e50142040d580c3c060704016060408081c480c000b0041490b015902c0d2281c0c0d00800d00c1500040141c60700090164024031013010341210031114000c0142c2520b14a0b91901c0741c11003640c030411801c4c4003400e10140105c404407031509101c4401e4000c0e4498005100d5010300340000c0980c48002c4520414080c1c85031107100d1100c600481c024480e0207500b40442604070b05014030064045a01402203425544452400082401a901c07500c40c4c0c8024551580c09203060000600308030380c3c0701024601500708085c4448000d40d00e0f845150f22800c0450010390360f05c06041d08202e4101e034011038100c0a81d0540810ad0035540410501d21913070202a092020050015406440f450707039104012468000c190b407036400010078040650440d004582c80380313003040002146503100241090340c0a41182c01082035004034014840319003807404514085000d1600044003041503078510b00300d130240c41545955 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 237543821 1250 237542571 237542573
    0x310501060b032d1f09060b0c0d020706050d0c0507081303030306120224040b0d0b0a09020306060711121e07060201020a0807030f0b041b0905060c070911090d050a 71
    0xd418031205445001956680ba20200c00c452102030307038000c0c1034080001c0322103164080050003180c5913000d056010b0411b18080b803200a502c0252044109003400c550b015035040b4070030783e1645080c4c000c2c5c00000c0c3c0180003070664a8074517000312040240c241001c2d460030425445210b001e903c480888032120300055810820558944506001070104501004160300d881d0300041b8a042107900f010380d920100304000c64a628000c0c01c40c3e00034481020016030b030360b082d0b80040c1301501c41813004074841d2810520006050291f03000305d80c801c80c1e0003407403546041200d0765031003040706448039100d8000520425203568001c00f00110048143c0c803150101e02900c4d00040e0920b801d081d43c2040c021039005010740e014607600400007a0304181c1d00e0070b0100310b002c07460090f8030091411038400e641c02801c0c141203003c0041081c080c0c0c01007840d10350385d10604d02d45039814403505105107520001c881d84100002c00c140601c50303200114452000b00d400f0b1402400200158400c200d41c0b40c10349450b04040030581c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 237545071 1250 237543821 237543841
    0x2d0706020708071205192f06070212090a120507030c0909050606030a020f0111100203011502100b030606040b040603050f01052d060f01030e060106180608310501060b03 74
    0x3254984c80c07a00e94645600065158961003004100030140100b111103170084408004801080e14205e01100301e802d44041c10740f941c2e6107015501100903018510280e501000c00c48110782c215070b0042c0c01c031048545821580da180200c1090155001c1c007407240c01000081e06101d1150080040550125409859080690030301c2c80181c0880d100354403c4105c20010384030780100d1102c9080c2400c0c24201d650b440c20849090500160340e10070307001d10000000c02d011840130040000f140792542214418036140900d0421034031100c1d640d551540c0820001600ca20f02508000690708000c0c1010a181d40c2c1ea82e241407600705480a81c00082e5110f0017000048070998001452010148106c084036500541c000c50001074050503890281410301e040007950790081d08406011401142280c12569484074001e04107900d0a940a8841010b020300003441882009843c0c0101c12401001030341c50b002c400d2185011884e9040c1a107002e080504400c0030840a101313560080040c010031683d6460007110031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 237546321 1250 237545071 237545093
    0x120304050109120b010506031b070f110105091e03011e0903030506010822082a0c0301060f0e060f060a05040608011215090501180f14032d070602070807 67
    0x80b910750362034116503c000c50283c00b0001d0444070b003525016035039280c00602030380141240703854920b0004006041d40801c400c1100351030703080703005003014000a04000300440706481034417410f13580891580c2070550342c50103000110310301007001000021540e01c28940340e05504e008100030303103a8903035818142052503010300480e5803000007441c1100f10392034a10146030514420407034081c45070044484070001c2005580403228400301000301072200180c040e2140d03002000b84400c0c1da80a00078150300195038241402254140c0344e1490320780070117600784201e4240c0100c0c002c003400d90210810340c803807004c2d4a82e60010800c0140994589a949050010141c15014183e01c031100c22a110044003000c42c51100c82800c0c481401d200c080382598050410074090b000054880a81046001c80002001506010925514410031004090b16140c014050b2680a07845d415481580c85c0411a06050403c130142080308010181450400d402d0f1340343c140898106000450300c2801c001100010301414070701c5c6c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 237547571 1250 237546321 237546329
    0x513020409051003050706050304051e011a0f01021b060904090302060a180308010e04060609020f070b0c030103170705070b030c0301061101060515091f080f130803010611010b120304050109 83
    0x22401146141c5e80d15990754014400d40e420041d001c000301e000c0002c10301c031442404812080b00000114510307a22070080100c082c074000100d40d104650710f6942401d0688070300c28070058018100d1280843c0c0c0e4420618201030401d41d01110811841d40c19654a10400c074416000340d0007480b040c40c08000c45070455501807001218035005401040003e940301000e0b0f41598070340e84881d44161201d2a01c10f02811080d0404000280081810381c685000384014050160180081c13040070f44a00c04021001d100a0001900c09a182400b9440c01180c000041448911800440c0c114541d00c0d070030000140c00540d51610841800001080b4965000c040101d07203125400c0204900c9151100140000c04c10390f03070407034240340041901031013980c0f0403038240340506440003171842c1e0715240c110080c8540300032501c0c0003013981482c3c0030410a6690105e100981e135800784031989585d090500a071010000745914400341e6481e101c140c1115201c480ca144081c14940000315221810400003400210319500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 237548821 1250 237547571 237547591
    0x2011d0304120303111306020321010806060907050705010c0306051201050f0114181003031b0b010e1012030804140f0705040f0b18010806060901051810051302040905 73
    0x82c0000100c8030300c888281c0358103080c0005c800501c080d100c081c038011740c42c0c2440c03c1d80e916040041d90039004002404c61400e15480384400d050740011443c0299800c1c000c0390901c0e448130300016018200b40108039004006400c1c11400c2c00c2095440500795021442c0400000303454000c100024140601d640b080180e0b030038000d114526248282001c500e105120309039034151741c000e001820380c85001c000380b00d118091303620800d10f15100154412440c0b240c0f0044001443e104074035001ca003002c0e41444540b681c040150f40803640b800600c4210048068017214000243d0200020400c494924100c4c145101c4d0b254504649801e017080c9200711903000d500c0d032080c0c228a89010014502003801d405692048400003100400a55803c0c0244501841c06410000b0302031300300e004035111841c05040f61804021144180d0300c200600040c0301c420700c1042d4001c034035000c0c20300c241c244280d2826408148041e220700c21030368441c00600700140060343c000032654005014804800c050055941c0f00b40c2c40c407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 237550071 1250 237548821 237548827
    0x305010606030212060409030e12071a0c030301090908040b07050c010e06040f18020f030f090d0309030527090c0c062d100f03030905030c01090609051c020d0302011d03 74
    0x441e061034144d0040800b4401e5a0b503554490400d4000d5402e000f10003405000140b00b0600710340b245980d20824006c007900c200f0b0f118241103007000c651048503404030070038004c0c500f50703480c1100c0c0fa80903200c200411562440144400f1030804550700203420354602810040040807100000075145004002c005400f441c0100814807400711020020300480f070741003008403506143c1c021050001e00030700882e4100d5000000038084e40b180e55150b114003510a03442605c2c5164031a82054049641000004000c25814420b035103031038000d00b1100d9490040038208071540e00c0c0410014095100440c0e28a904d8180410031410f030500411041e58404400854010709002035030340c1614581c240f0000240c00c104000000d642c009250075032030010b1000c02d2501003d1522840e01a00c0c80031746014503802849003098892482d8440c0c0300720300489280382c403200342c664100002c2c0080e030703c10140c0e900e4800c10101f030f0480040c0c41e000c4980b915a030280e40005542c10080b044243c1582c509240f0701000d900034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 237551321 1250 237550071 237550087
    0x1210203060712020d0207050d1106040b150f03070801051b0306030a0f08120c09042904020a170f090705010507030509010e0411190f050a0917030708030a020403050106060302 77
    0x31515001000b0781000c075901d071079900610380648100150742e080305001141d42d50400100290110411514ad2100c51149200301c0c01a981c0c0d40007201d02800d080c42c02c17008140c210512101c801e8035124050b050b1400749009801081c0350040c1903009101507035440b0708000e00d00c42c1d1041c1c0b00c02d40585c075640305407940c1024400a0758980030503401038102d20781604113100300180e500848512442e42002c0100500e0700307000e080d00d07940103219030f980039600303103100300409040031411f452a02c000c503400300c050791041c81c041c80000d420250710203042c082620352181502080d80040c034411407401200c8003041c603103085940c1c1060001e90003c0d041c00424025440026000002c3d070382c0c602800e1034100c0d055824900002c1c090045800590354544002038900c1070300550380b07000c00c0c0078659602c030510301900032841201d191165045c0070b00020400c0005112880380d18007204104614401120b040044541b0750000350303401030720650845680000e080082103401c1c02040004e2105007000c5040020b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 237552571 1250 237551321 237551323
    0x27030a0203060103080a03090c0b040801151508071101021617040b03011e1502030304060c020d020c0409060b102a0f12020f030a0504030302070e010828050a0b01210203 74
    0x6001c010174201d004100482c00d28401e03842030240e07607004100d1003e90759842ca00061590302138001e02c0195420903034260400ba0001240d1802c540c0c0d0440305604000d5000f80443d90003074094004000c1080802040c101d101090019050f4000b2515031a03070841601c0c6803000b156681e5188544107a0070034802000500041015241100c0b80b030518000d940e1400359407405030081c00d03080441c01c0c2040c0380154960b0750f4004040c510503486588100201111420240d03a83c0f2211555000180e00411015a0605154000c0e4201c503100f5180442d0782118440041e00d0542c801441c42c1c0020040241018404200c0c0f00f00e080c0004040c5190201046540300c2c0d41e450080d03c080a0840c41d03094554080391031081004c1ca882e280801d056075103074110004020310300c1d40a0b1100307800510840101042c2038101c2c2c18454100e800b102e0040c0101c5101c840542c010004e00100000e801e1113402010300401c905004a50140d8840c0f000d0454560401446c00b449401d0b949040c01d100f480340c071001006840c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 237553821 1250 237552571 237552583
    0x90504030f050a020106032405060f0f0d0503210702070f080327091015030e15070c08041d090a0215030c04030213050603010b1203040603050403090b27030a0203 71
    0x20340e01e001c2c1d80e0b0f8291007030103038050103140c0e0004021050300d6903903015620502500344180440148140095101c0b00c04014016080700e01880e0f01c041e51380c8581005141c9481d020b81400e1044069a007030480365071450000e15012041c0140c0d02240b8010001c40355414003a901c080d040d045240e17035620307042ca007105540e80601e100100411080000c0c0d5140744215a60300321031031000074148e407014a400804100701e000c07140b00c1e07110050801144094494020b00860707415155281c0200418144e1201d42e8071081000713042003090004050700c0380041082d81d0028009040380f180004070001043e550200650801049941c258102420300001aa1014454149170150001c2542c0b40c0c0c0711295a12858800d0740d1000b540300b0800200360604000e103400040c4900002c40c02080341140d51024003041c90300040c0741d034403140c004010030703c09907020791701446c0c10034000e240c00a210b076240c50714110310b84d008903100c40040c42c5110242c01001780c1481000d1031148103402920003110035501080d9910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 237555071 1250 237553821 237553847
    0x305280507120c0e13061802030c0f0f03030c0609160e07080403030b0a06020a02122b12050901022206021e010905070f0806010506030c0702090601030b032509050403 73
    0x18118920018468103c49500c00f43c40740d000340303c4c868241407202c40441904150105c61050409980440d8942d015081d095103540103005050f15800d84000c10294003250f040f0141c2c03180045650710100d071000c00281c031240c0050750081810b802d05200d100d1800060780c0c0d10503a00c0e542e107a0b0511840700c20340d44247d0000040d003041e04c0b09481720b25065018102101d00560401021100003540c0c0c0e42c00035101c41c1c01030080d03500c1f0345400d01402000d41c40c1d03182c0c03c5841c0c446400145482000180d90104560032160503c4c20b0301000c660900c8440640b501074440440c0303a134001c20a40641500c04181d610b030110030b402c4141005141a00294444000005440c0d21290320040d80e24a40c6013904080702d41540181500e0a40f9140c201003c07100b4514003401445205110000c5000c5c280b080417240550701c010b180b5414020707070707908102c19000300819060400d6260103544146071000c0200800b04400c0001101d0307401d02c1d0706e1280300500050b0740440c0b56581080c042c000403d802c200041c0d090 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 237556321 1250 237555071 237555089
    0x21090b090102071a070c1712070f080f07050c0306010e06100e0d0503030f0a0203011206050903131418100e0c190f03050a0207200a0902040305280507 66
    0xc4800c040180c1c1010b60607070091440700070303190361a184a58800c004101903407103020340f04602c03603ca40180401c4480300000e007003683d110308005550a41c0c4c503005070200d00d00c1850850320351070f00d907078610710250415070844030b8810020a0342c4e42040014803c400c11204254000e0800390300d403c40382d40d006c403005003d05010b070110710340151485e4840d5801c2010540d0141a940c10b4024070b00d0641c0d901d900468411980001c200c001c50790713407201802141c1c1207c00c3d6091601c2000c10503111440104005004048584810454a070200040b544164000d001d645c41c1440c19038582018081160890a440f84044500300c04101200407070b15890000e1314100b00902140e66182403032480e851007031003c1c1000390440349406203000c9a00056038119000c2c9c6039010720088c0c40c1d214090b002d038000d800c070042179080a42c61503034007282c08100c06010000002c00000c003096440c6030103c12640705800945454106120885030010040007210404c49545c481085102494440c9500e07003503280285094 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 237557571 1250 237556321 237556327
    0x907030b0f0a1203030507020607050702041104051c050f010603080418020c0f010f0c08040f03030b1c0326130f0819080906010515180a0f1221090b 65
    0xc81e11880d0309026012409031003400402d450703894070305440c00201400c4000a0400c1d00142d03445102140076400740d1420f4035050709241c645d600b00005810703008056929098140000501650384407001d2100700c40244034201c1c54841410128148103c3c00309650f0540c6c10400100002000402180c0803140d00c00b58008a00d100004040d0281c8120799003505240b040440c070080c2200c3c1948000417940e07215100f040144280c0409441d68003003120301a001c031003034034208404640280c03c407a0003550300400400f100c003128210040d646240100a900107441ca020b1004000000491a0040706a1404403801880c20100c04260784500220040000030001c800a00704502001510b074005400c00f07605503011000c000082038400201c03043c0315544500400000c41d806c1c00c60a2080403460700d404c2a107801b5401c500b403000c6000941ea4160400e48c041000510314080303007505000380070700001c0040f4200c100d09100024240c0304e51107a03500c40b52034100d101d42c281c0040c105c80480d0001458aa1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 237558821 1250 237557571 237557591
    0xb0406050c030c010627060302011403100302121b1903032604121b020f0d051207120f02010e07091d0a0b060118150c08041d01050112050402090703 65
    0xc02c0d4000d1900e00d00306582058030120b42074140070309840321b01d655941c49400030030440d5031620a40d441803101a0124513540084c05011039100002d5038007a0300d050750075440a54035808034440c0c40d20003041c01000d400440f020450100742401001c0319040c22284c40b10307000428040e8203040702081c407005040c041c10806001051810070b00441e03a0280e00b034105207140c903145c1407480c62440300900610001c0d03c04400c10030260080704d01e6241c4140c0180c440712854400341c017402a00c0d00035540c161514454001013800704542c130401801ea030781c85800c82542a040300080944a480d41036403070419a41422104440440000b405034100c49000c1008141180c200c440000d0038003291054500c00d020f0320481c081402410842d890003803001783c3e900410780220750321802c074049603400f901c45a0034004401890708c61003403040007141405100040c0c64290384d40c07000b64103c41d068000044651885004224544e04850454140c418a64042c8043d00d0640c0c0080c0440c48024440400c0c90740d554100700c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 237560071 1250 237558821 237558823
    0x10504090c0e130b0a15150908010f1d06040b0712110a090317070f0b06011b0b010f0b03150d0309150201020702040f02122e06050c160b0406050c 64
    0x140148074981c0380d003589003040d1503408140c02c01c82c83c0688290030040080707280152940304000182d504071080000150030016149881d0b4426080e0508010b401100460601000e1250880c91030424100054121420a02c8192200c10309000d411541000040101140483c445103a00000c0d078a0320751401626076114200410303c914000e06c00000105802c02041d8000f510001601d00840114054562103084400140300f41100100b00c000194114000100040c86054004c241410300003441c06828080c061540c21081068441d00001c40042110384585001d1001920241c000103255291010310a140d0490150101c1d000309440d450340300034580310740e20a401510b01c118404501c2da80030200207001c0d4200810030ba01c140d141402c00d80f40c652461003244c11030300a960381c81d10039540383c485802d0200c00340c403543c840344401c48000c441c0440e60302b0010805003131662921a25298070050743c40ca4281003107810080ca4451040a0200a08220646084a1940c40c1c059074551100c00a6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 237561321 1250 237560071 237560093
    0x307030c021c08040606050301020c0307020112060302060f030114031c110703080408010e0c0301020412020d0c1a0304060c020a050715030905100c170f07030209030c10080910090b01050409 83
    0x40c040d0795a0a5402c080c81560103402c4501850040f44203008498660007018200e1181180d419143d51040041100550040c01d04c003480140d510300c005812076481d000b01c0e00e294400798030302000341c80000041c0120300181008041b00724081e001440c004c00d41420381d441d00410355018000340100103a150300000400c00c0b03014040d43d4810403581e2500e075107200c680e010301009070b004105806403112414503428144291001c881c3c09a8403d400c1e4240e40d004c3c8444100310000c1920b02104902022034003074180b4905529a000145406580f407420342441c2c0115201c80160600715000641040c012400026408003520a00c01c900d4070805103040d0164020300350708500078000e020b61508120034000c2640031203107140c150346800351400d9000c090806840d00840da402d4806003500d0104146a1003980502084000035040341c0c000c2a802d00083e08030f4000e1001c110004926100704107250109002c422031594401c034052041030641e5598a510380414050940100e0351881c04100340040010b43d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 237562571 1250 237561321 237561343
    0x5041a07060c02011a1503010b0901050d0c05030f0105010c020d060b03010e010524010908031204110316050123120a0b1c050d080903030402130e070e0103020a1202060307030c02 78
    0x104201c6210810000383c06480c090341094009100b00c0303180c0c220b50030801020f0654902240364241f071a03003002c01c0702400e03810003403480c2d0410000344010070780e4900034440d1004202c895207900d134580c80c00c00c5440b0b100359816080b044c10004068144401611030a85a41e6556440030f400718505001c1404240104030007500700d041c540c2842c0c01d01c2240781040009001c082001c0d14014000040c84006440b00c5030745124001956100b003049134411451580f4881c1c00c01d00c120b9120705a141d40c940041d2a290f44501c08058040c80050700304580c2d82c0082140d0000e01a084500b4600c02d10786d6000801750050301d40e103065141c2c1d054000391a02401d5032100b000d4020090828810480307180c0c0003450007002c02411038080c0300e01e04100515078061141c483c403950064004501d50385c0c8c4d40c1d007400100000c103030110701e41076290f140d04060500180182c4018059403001ca910303540c598010800401d4140d400943c800000004000142e1520000c0740d500404a040210b400310320154201d01c1e010140c51 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 237563821 1250 237562571 237562583
    0xc0609063406060509070206040506041b0e040303020d050601031107030e150301060203040602010b0904020f01050a12060902070201030f02192a060b01120c020607031d010e03090108070507020105041a07 89
    0xa0000100030340303075014030207990702170701c42040d82e6441013401d0340d6030b01c2c003914050520b9020400007000035900fa074941000301c458002902845950b912410701c0240c0c25201100400c0c1c010500d080300703080318032401e94408001d1800348006150030740404000d00c04c0d02c0018080003501000503516444540c2107800d0200500700366552982c0d940c0f00203450360041d005200055003448113124141c07a08020a50083d5001042e10b18000d0905005603980d501035200001800b4080480c4a002013041c41250003c20440e2000b46c1d46180610005007228201c0a05200301031050114180140c00d003070b80d014030588103080c010311084215044071403240c0038201c03403001f0f05266244041003000a802484401c40c0a032518408c590644c0140000d40b00c11082000c016400304c00001c030725030f220360401c0641000b0030b0003014414503070518403420742d100b5030781c00d034100e9000084018255a000414584c0007070141f030200e0500c7d4403940000c00070710413172103030120b1f00c110b405940c0d41a40c4120104e8003827a41c040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 237565071 1250 237563821 237563917
    0x110703030c081b0a0c020d050f1005040819020a05010501240306030b0a050c0d0504060906060803030f06010e0a031e1b0b030105040c030615080610050c1203070c080f0c0c060906 78
    0x124086952702072088040201e40150b245000c0350b41e0b80c502030039000c0c41c0c1c01583c031800c2c4050f198450245c10325030032a800462140d9882d5070041030b401c0c89414040c045415031815000d024205558401c030b49900c0e1101018034085c01000812484010550841003131032011940d40c590a202c4071150294110042e0030340d00c4c081c144000c1140a0b400380c449544201d20900120765038150481c2c690004031100f0b8100042000018070035071044c21035910000000300b102903581d40f80d454850746090444501174106c201c0031456424800240c452303400c1c1f454100c2e0070000541c100080c600e031901061003140e00070b039114240d041c0e0190103504400040c082e80d80c6c160a007074021207001400c5c008261110382c0207101d18441d1405082c80f030401c5519440002000b00110b61194909400a50008010311304000c00000005c1c000313048100204403245500d5131a603216803004002c14141010491480c2c8038041c2002400040d0729000281c40e41c13584a04204031600b907a080e058140c0b501440b6400c1d010400714 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 237566321 1250 237565071 237565073
    0x507150903020a02030708030a020d0302040308030a05061306030f02040e0d0f0e0d0b0f060a0602070803070b0a060b030403020604060b01030504150c03060e01090606020f0106060507120210110703030c081b0a0c020d 94
    0x1038009d99050350308491034164801020790403481a40405802600b0800005010603020f030003d682010001c0d003040078092444180508481035a0422148226030390381e40019880e2500840c40c1e401040c5000d8200c803d10030601502d8558101c40750821b0102c403c62184041da01c688000d80d105400c0b25aa01540c0303801311235003814040c1105c41c1441412074981c0801c4032341c40059428241e47c0018002c0d8903002c02500c3d03014204030300a10004440c2d40320390021407107941c5c10021b180914800d4005114030304044c54010181c40e94525000d04041c500020030000c109840c04111440482e54030004038260040d00440160038903810500d91005d0780000086c000606a000100b21000d0354284d80c0c00450b44041a8281d6425208800000c0e60600914001c145821000441c0010600403258a0b0090240e1402a00c0e44900010904134000c1014001d15415025030010100c01e45004800e030302d880c00b02048040686081d6a84403240410300d240500e000703509226400740c004002820480d12 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 237567571 1250 237566321 237566323
    0x18050105030c0934120e06070c110607050610090b01020d0f020c041401080d111c0512100306230f130503030a020409200d0506010c140d09060507150903020a02030708 73
    0x120840c4d0300e0004001202c00c110900461040380080c010302e801030a11a00ca5030811a03d81c08804003e07600000c10914042d017941c0c420000301070241c4180d001e8801450442101d1080541c99444a4040c03800c062204d0f0309607034045440c0306440f209040101c90661882c1e022880c0101443d0819001807400600307400c109032881680b4101c840398000c4413141c44903c541140c0e8a194008070804a50021480a43d18110150703107242c0e100d400c0c9061401c0c10300005103058406415100b032240032005000500c1848a2030060004401c4110000300c0407842d00d280c0c05200f11802480d0f1000c0d0641500403d1020002c4200c3e0000e86c0d410800701e035124200282c00780003d40c440d120300140c041c0f600ca0040f4a03035030440031034088550140304030303810051a48041c50207044000e00603810444100c0008001400c0341307114201030258100106041c5020200180c00c04100390400820f001d024010200024504402c071259a0681400420302b4121860b05034a40011160003c0d49401400c0c00400c02d840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 237568821 1250 237567571 237567661
    0x2208130e04030e1512040b0606070803010f06020706090b0a030e1207081c051905070207090e010b04053102060409180b0601050f180a0305010f0618050105030c09 71
    0x448925201d4800c84c04081018800d010390101080c4100c40000c0204014a44803070b03000d50003900c2141380c400e041c1c0d25844254400d0300130300121044e82e2424004603a04000d00b2002d002182014807100742044100441ca001e90000b0f4010540c0311107040601d5403040c0b000d2035017107110414094030307080381d071400400366000039407917901c045003d4940c1c884c1c0110301e0081c18006e035108580700e141070000b41028009007000400030001d41c031030140c00180f00d050328030400c120494000000501440c560b010001039031005440c441c4400050003840c4448ea214074021046240c9110f4110452003c600c04a6103600481e8050010b251a000840c05a43c902580c510081c074032803100c0c003105641c6d050045da03090140071010082803030113201b104071803051402c1141d0710413030051040c40c400d580d90f500d01d801d50f0526032001c0301450f12000304000204509030114a0ba480c0100280902e40c10320340801d5589c841040c00c03902c110412008101c411071160303825044c40d030b188200c400038034484402d80c2d61491 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 237570071 1250 237568821 237568847
    0xa050403031b030c0f080c06010605090907110705011d09010905040b0c1207052124030105060303090d150905030304020a06030905070302010f020709050a0b04052208130e0403 77
    0x34004030402281c9071510060346045079490b03196006500c3e01034a82c61405240d02030104c0d10100101f19007403981070104030142c000c00c072650b100e5a07511210800d0292514014100800f400059a180503001348041504003d546080c40c15952000755250810300a1001c2e01101d83c101d030141c2e0012801c480203800c010320032801201d40951503104c0002c01e0009101d04021802c80c10a40b8000c140100d1007079008000c0510521111420300006950314010940150380e90301d146420898941c840260f00031111416000c220005c101c60318000010945910801d03500b1445481505600b40800c41e00b02c1c00c409510b0107a9400b0018020301c4d180076a5241d1058809902c1100f4160002036018842e0085540b1281c0c0480641010740c6540e0064400401c0401c3d440154000c2550110702c0b2030440c45003a20034140c600001c01d8401c1c410f0240021100041c5c0100424001c0005640344c1c59a02104910381070b5201660a0b42c030b1100c0e0459000fa156150400b100c0c00001c4030600080c16404503001c0e52013 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 237571321 1250 237570071 237570077
    0x140a03060e032d0f0f0405130b0a17060a05041a090c0112090f12031e06030b0c0705070e090c0409030c02041505240f07030906080606040e010509090c060a05040303 72
    0xd103202c00c00c50312401030b0a80319180c0b03282c10488540131a81e5500907281202c2400c00312810142ca03040011a2442424030400000d552001c0001d03241c0fa008412400514140000100710240c00305020b032502c030024080b2485a4442d404101040404002072000c40c0d9080080c000c941000e004103510b90134502c1010380014203140604556105921030070300d502e80d1010400e00307038620903036032900c1c4009607008400515945207190f00760b40f100460300145007030800e035000806c10700310301e440400c00c00041c02c070100c65003040c88800f0009074002541c009903143ca404440080d652561040d14150303001901c03603041070410080c10105600940d0007440180300302c805005141801a140d51451900c0c0706890b486408804080207080c0c100300903d0300c1c0050300684c20718240d03800d000c0c010f299010920071030001c1c40403801040076540c132400594000d41c0855015207011f1409080100741c44040c001c07281306d82d58040106850712820090200da520010f45070f035480782c881d00800380550300188015404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 237572571 1250 237571321 237571357
    0x1050a0509090f16080106060806010801060e04061809020310060549150903020316030302131d0c07051b01210204060906051914040e3d140a03060e03 66
    0x8240501c9c6014490881a13544070a240e207466130403199440200c01140d0095506c1502144141e419600e0107284000c280c00841c54180900c14103141c50754610304041d409151245c14806661140c000315a81840f55003c924801d89440b180d5000354074918207019800c1210306042000074001c0b004108a40c0a0029210004104c03407228080c0c8802c52030040050704100181c2c030054007528400d82040b4040d1034010704000d41c41030b1041c460f0b0459048070102080b118031040e94610500c5801c1c1c0d200d0700c2200800c1c10b000c0382d551040e13035540f4141c1175144490b00b08003020b40c2c2d9901ca180e0740b6a2000c150a40c0841410140c00c10038000e502c80e00079000012200180403444134025011a03d0728072440710305a00302e00c0640b0040303488034032003003e030010844100300008d02080708400450141c50151400185548a40c000b42001141038039480920001c80d01003503091b5141103800411511000400702002501c00005003a00a03160802000c103842c0164000c000000000900749202d500104519 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 237573821 1250 237572571 237572579
    0x18040e0105070903060c030b0d0606050a060512013b0103031b05060a0510030c0e0709170c101202071a100807181b020a110901050a0509090f16080106 66
    0x400c1e50400c81c1d41c0804100f64110400020b10a0303413011007414814030780044c048906030001001e09444030b034142c88040d02c441c4117001502e003042036400282000d0500c103240c0b04803840e00c000001da05214207130004030140c92a422582e100a0403c990480d105159020440028034044003544c082c041580060802e0010703203800c074000d0000030405a0000c000f07101c00c0e0b60f07041348440030380002481c5400c507100050000001402049250001c1c2410107003010051400d514001c100028981c00701d000f2018160008132200030100d4241443c1c3ca0a0b49d804021100e90103003601e072111507005840c1c603903100003040418041c20075102420719030184122000354070341d014010180505800303018803e810034001005540f000d2000982c4500d02d044001c1143d50741340658038110102c01c1c1403440903800c52a9280e00b00b00e58900355a070700c02d90448881301d2a5040401180e00c095907405014001d40d0400f02240d42d80340100000000b00400728112a03411a10b1164144074030b1407442081000d60900c0380102d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 237575071 1250 237573821 237573823
    0x6150b03190506041a0409020d0f050604050d0801030f08090f06030109020d0608010e061815010e07030e0a0b0c090d05031306020d030501150804140106171b100c080d0218040e 77
    0x45da00c1085280018484d003c2d104c20000200615039080703034402c254444400000341081c2c074041c0c507540234101500b801e01d41401d0041c20102c040300031004024900c0c0040c000505584075114049410503a081d0311850858046280081d07030000c41d9034012004400080d94241c650020651a0807030b031000d000069a6008083c01e0721016860500f45070054400034003513517044000540d03080e42e05801c035004200d10710030308241c0c4c500030b0708090041c01c0a0810441031a03054002d01c0055001040144000e080c6c544481e03580302400f802c040039545002a0740e01480ea80d0700d1101c540e40d42c202d0107490752150300a03070404020304903108400150159108281c2c1e01c9009201c0c0c14102c990f8100355901c1856040303400c80c1c2ca1302c00140110f070300d0f480380341407000d892070b00f441204081c02e10000e500c400745100072086890075420804a4810b51000c3c141020140c0320348880c020170001a0034801c00b0b041d1246002c2a06000e640b41e03100040b031000c6050701c0c01c0d1007014003071103004006407403c002081c5104029 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 237576321 1250 237575071 237575081
    0x110c070b040506030115021218100809070e07020f030408241003060c0c050d09050a15090504090804081603061103010b390303180102120406150b0319050604 69
    0x140f940118144010064031040620000c4025298030540341c0008000030b4110154001900030410305110480e0000a4204043c4c42c4c10035090504202499203070088510b40c1c0c40c0058040d030f550300c00108022030a00740c003c1000340340c148451419070361616241c0d40d80d0380d924042e010200e0301c203c003a407020042850304816402d004181c030150342c4100da400c0d070f101d00014056040303d030002c00c1402116400403404c2030142c8004022195030b41000d0501d4001048407807005174000841c0e140c42e0004c00c008854205005404846081e140031400c180300b820500101e00071030303000e095a0b000f551349505861110100c40e400313482c4194401c0240ca001d1071409070b0b1501007400b034900d42040030001040c0d40045095000025282051a203000d031080141c0c0c0c00191040c1000c1e049140c0c400b02c1801030301d15403801400d6030404140000c504001c2d034070902001062025001800b815a140000c0c0c0310a10b000945001501c5c1801d4041c0e9603044c83d82e000c402c04d60385440b18010052500008c9100c1e4905400b034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 237577571 1250 237576321 237576329
    0x4090e07062d050906120907050f180408071703010e070216030813090e01020903060603191511280c020a0b090a0909031806020d1719110c070b04 64
    0x4248502d50304001004107070b0740d008000c0074090b040c002d803502070384c40c40e00030080a44070f4a181821828030500a80c900340341a00442c1c8501e21b880c00d80c0c680d40d105c0c1e1f0b079200385d8180c0c0391064000944032802c100e00540716400010f49982880062000c000008600441c101c1d15075180340001c99480c41310403a2280c807013028051442170f0842040002c00d55410141003420200030f101d02c181555840035900303c0c1c0c101406083c1c940d4011070000142c0c40c00b400f00c940d000d8010b401501144210402c800071013030418800070454020b51041071021051a4030901940798540e0f4004d81d1030b00e952024020150b0940c035154521480c00a0041d41544921040600242c0c06800520000e0a2080b551201d4004400c125003200701345100103400c0d0102d00400104e40c0c001e0721070b55503e09089500313004410440e0081019540074807240b98603903070f0014021400d03946044849034540c40c1c4604680c0301072051004601c10b182088850000055800020004c00030494100e54a0550300d06108030503000d9886 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 237578821 1250 237577571 237577607
    0xb0906010312021516181e050a030b270607081b13090203070309051b0108060307060f0c11190609091109040b010201020f030a0b13020723010b030304090e0706 70
    0x1c04030300d017101030b004014603003000f900301000304400f0b8490524031b03500503901403040510050985512407820301890000b0304000e8a20000c407900b5900c5a81d16640007404854403000048420302082105a41c0c0700c05c42e1034044260f920314145150b005100c0710044e15411204402038803034107400b0304040d04a40c20800c0b000c82d41c072495468004040c00941000340580241525803060b500042c1c014020940c02948030141640c515000000040c95844018070b5a0300035401410f0601c049030300003051030a00122482e102d07129030102d260015040700404c40d03203a0492224001059002c086260300004c1d15215915006400e69a080d0002544d440c0e21007120541400c0080400c1030400c0d4014684141c810700000d0301d42040f1070b91200103548101d0301c01089507940c00360129103203401b044021003030b00428819800e00000b502c81e0365400c0090600042c2044001c0f051550443e0203420002c4160340080070369803215900d907090405807500e4511318006d03004010303002c5078941c001c850030106480a58 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 237580071 1250 237578821 237578863
    0x30207120210030b0118180c21020a03060b0c030a0305160e060306030f0d050a0e010e1507240c0e0d0c050d06020c0a14010507020a200402070b090601031202 69
    0x2500106400000a410080c403051030607080c8909200b0300005005030142c52100061081c40d00b021680c188c00b41c2c0f0100592641411003030160040125100303100c1440050f80c5008181c420f80041c40c1c103034000300c8003860200d024000a007010000e004c00000d552002c0c0101c0e62032140071246030704046125008100c0d07540d403501c40780c10044040d56005c2405400c0701e40800c07108a00e10315210b80d9000381c60019000240c3e02811542c00070318007884000a0a2066000c0038240008150a6610107401c580ca1804034076081400641d410a4503d1201800c8455200e1085007000f030140041200c550003041507141d80c40e000f0304040c440b0251494101c44151140b03414641085203548402105440040e000c0c000d800710810280400c420940c410244146881d20162a060a541d0010204019900070618260100d509946920a1040c1b20090545601c808100080c002d00030880058005070001c0104019164006001d6060701e0141745854144209002c0803a6500201400030090059031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 237581321 1250 237580071 237580099
    0x81b011b0807021506220f05010305070312020303010e0612010f1104051503011203031e2d02030f0615070f0b090c060703020a0206070c0b0304060f06080d21090b040b040302071202 79
    0xb8011001103010010007c51070100309240f00040da0b100ba00240c420b030b00029420030401416000c050b0b05540c0d9400038604540c5440070f00216800c000f4680c2d8060650809413040748142075200840c0000889820060381d15000741e6998145c00c18094580202400302c800e0010345807a00590303040311a040360812180c04c030360b50101c01078841aa1040e07801c0c0302003d10003a1a00b100d000b030410200301c4800c3c00c105146101950118102c1458820312054410000e0101403030011801c140c0c004000c0d00c800148050112610f410f80c03003614000f41c510b1850f1400082001a5151001d00172401581150403045074182004070510903000c0c001e016a000040d540300505007440500241c43c010224400030640e62801d14007954401c0b01d08581d41581c1e6813600d06480350522500028000c0744008003030035802074001a0041c03428210f41d02c289840048508035640ca650060958950310210700545414240340c00b80303a860080d0b801300d000d07018000d4041a104440d00e00c4606864004002c1c01803070f070007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 237582571 1250 237581321 237581359
    0x2010c0e061804090b04080706110a1e1101060605071a010b0717040b0c011407030b18150303070807060c0e0108040f050c0306160905060304081b011b0807021506 71
    0x80b101c815422a8a456010340071407070ba0b0291620880c0a014419030b0741a541c6040411030b0400040350034210820b0001440746984200907543d9480c05081140c401c803091030381922a00500d6419000c158207000c0081a1581d104000e44005440b81084000500700d0700b5041c03017081400d0181e08001201404960301180030003034511901c07034601d04082e26181e15060031000603444580400816074450303043e070300f03202c04413009913500c9034645c6401c20007125001c001419568001274108004c0012801044d103c030760204603043c1e0f40724011b04072940c0d26224500f24485070826002a20101c0ca0a103030682c13898095443d030f2500d0f68059480354255aa0359580114040c503058041d1250f11170649400c80d41c0c3c81c100012406090070340450a0a08405a80141030454036001a40641d40501c00c1c040007524400580c0d8001004001d07181420902500751801400700d4814240032030727907200c20b402c0c1c4a608404800c1c01180542c1c01d40d200780c01c072004290108441903480c2c0d1b0300a07462007a100d015041e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 237583821 1250 237582571 237582607
    0xd06050709080f03072d080a0305011404050402030c061c06030c03021005190c1103150a061d04020609010221070b070302070f0204150e04050606010314040b1b04030501021902010c0e06 81
    0x4030b64042500b40203903035207d25225030011112800030a590320011300c03035040703400301d0b60404a001f15018492450580c0c00f10b44c407042907240c03940c001d04010070200301c1841c12000c00c40c22030311140010046250b0302d05024401e501113100c240e0040064100d0241d00303600c41c4086903c010040603140080d8803504c00200d503443c45803c01511240d02c4c0c079112504540d801e0180c5480c1400f694081110360801d0980041210092707400000e060348424002c02021800c480f8150784a0740403280f42d80c44514200050b13040c01000e00c1140141d4606840300f4034404428405400814094241c28109544110040d4201e1240740009064201e80003d44801490715810110400c400c12851010442c5c0e6191a803145580a44003220759401900c1001b510b943c1c548510345154812460131411810182c0b604a81080c0c080d060081e807400c00e0980c5a90340c03602c07030b0454000316032190085598103002c2d45140202e0505100d1000154200021246d0251091072003c03000320703000701070a00d402030078841002440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 237585071 1250 237583821 237583883
    0xf090f0604150e01050709080c040204050307450b0a03231903020102040e100b030a0504021c05060907080f030d0b1c030206070206070912030305060d06050709080f0307 74
    0x9500c480fa0304024401c280150703405140035895403174256082c480c0707035800d000000c40c000d0300891042c40101704503580007a2501c1220701c005845020103800c0c0c004038840c1100151214440d0030341003400740c20b4850511800e007208003a00c1c400c100450b1803408200200405c1c4c031000d42906011540d07600c2ca0220080d40c10004d0010100f21004032894910701901d540a00d6016405030f540441d007080a51114481c865000e0500301c0500c00d000c0c01e00342d41400ca0b0001030681030b8034645d86c03030005045444021440c4540100300c2e01095003030350b407803500d259980c0044420614500941e00c0002c1c2141c0009140400c20803404040c40c280b1000d100244028244000c48941c00305034440c5103d40880038204040d080c40c001e60184c0280d2400000103440c1000207440c5608008818000700700e2280322025a10040c1d50502d0041019100c050008406007900400074059601c1c00f003e0089080d008050302c402ca50510b800d03070300c022a4130402540c13203008080d80600b440200c2c0c295a00c03500301001d4204240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 237586321 1250 237585071 237585113
    0x30a1101080717130201180501050313110d0606180903020606040b031501080102071209080c040906240503120903060103030e010207080105090705010305180a03050a031d060f090f0604 81
    0x1c030b090102105444804d0b1030f03102c40031314240394040540d64004401d100c0d100f60404e840103514a0034000030b0080c84014041007501081c800740c3d000f0441c0c454840d00141000074006900300043d070409030001c2c1410b1088401d801c103c0303270a103018090745014011381d658041d00600400d542e0130042c00054030612559943c503000e002e5140c4a802910760f100c0340a02003100c00161a40c250b8a000e1800382c0160b00a4000e0004903031013048010380014114110f88002d2f00d02045408081c42c104002e407030744903002c01d04101c0302d1019100946038600782a0480f03104800310380f12103422154144061103003c840302d405800100050000c6400350142c50045c0e94103104a600490f580c0c1682c508403a02034411042c0c0380c2003284104900c2da41401180d8110f4203c1c1a40d0f05440c0e5400e03505983c5407501c4d40c0041c144240400d03480c2c4124000e500046003000131101c4190031100006901e512a80121114401d0100000128015410001c2c5114044002c21300030040c9480702e44440e1910103c1c0c074008003039 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 237587571 1250 237586321 237586337
    0x80f01090203090102090901030803060a12050307060c050d1a0906041806020901050f07030c02041a2404050301090503120106050301150503150d0f0c06050a0509090a06030c03030815030a11010807 86
    0x5103450b017411f258001c5010300c40b09d5480c0d041080402890800540c04201c408240e131034098081134021080303031040d035400000000c4064031072006850500030030030191016480e1662200c41503852a0707044124150031039084c400c80e91580100821070780c02c20f120321550124482c06c40005012580202031440301410032030b041640c104d06844d0f0301e500841003100050004d80100003141494040c0f0555012440d80d44042c483e4154082003001c81422015103104a4180c902d030403103500401141c01801d0b02038000d104290440c28071a55030780c4540902a4124141000000c1d41c1d4800c40a1364183c856041840030500071800e1f00720765a810141141c40300044540948849603140c1c45d03c0c2d00f40c5486603895070819203090501c0c0308082c001d68031001c18004200058941e4541c000100e5000401c1160100501d40701c84207650000d10b00c60b04014040b101f0400084145600404644d100741041e05446140008641c18191500c00032040104841d4041007000b01039809420341031f91002132840c000007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 237588821 1250 237587571 237587587
    0x803160311030f1303050c01030506060d050406091b0807080607020304060c08040f0e0423102f1309090305070201030f150b190206010e0103141606050910080f01090203090102 77
    0xc9590b0162150502c0030201c0c104c1042000018010120409002d003420013985ca040c10200c0c071984114902418101d59400015041000d140e1000505a030051717980c2000c0724100c440d110503403030300f4041d048062061000c000758507803002541c1407191100d40d0140d4101440c00c9001d840e241d0121808071400305090201142d110b11441080000b007440704c0d2095290300b01401c003c003e10082d04030f4543c030700407501307000d001c03007540020a80c200101040c00000c0482c030400c043e14a07504a2040360344400e00b48800e15825001c0d4001a00840564000107842190344840103c1100c1501e14000c0204009002810166002e680710b041079a02080e8040b0300e4100d0004601c0303061815400200c80e2620100d44001c50890403152120207280500091066504000300d05849140c1480001d0102e80080300340c4130f00300f07400d208060a030107412440b145041d03103540d005446a00701c200d00d5402a08010078442040f0310942c5510300a0020403449503140e42000300c0700002c0d6100a03d0180d02e59000c0050107 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 237589928 1107 237588821 237588847
    0x81b0129091512010914070608090607020a080f041701090314070b0c1806040801091208070e0f060f0d0506090a090b010b13050a030503090a080316031103 68
    0x50301c40f03200d0b200100d4050006184000c00300c611a0794039a104403c0010010151981911000044d0740c0d0090013540e901700c2200d01d200140c1c001020b40c8046241d00b40201061319622044a00d80b45d100e03900900480c4202c0f03178070403090b07555001c03c20a0640c08121610f01a82c0414240d2500c82503403181c040710326002d0903c01380c003800003c00c0e114440c1203110301d600000000e030466881d5951040303403074002d003e440000c0d9403112a1498021001e8070600441d80f1880480e1555200c042e5884140422108504102070704040104015040c00040d034002d0036180c40030f5035000c0f81510f0442d003441f0304004042d000c1003005042020300b03c0043e240c0c14900d4196815030300c0d02611000b800c036000d03100b414903601040d0010795242c00841070007008801040c84420980c0c44a91203030b982e140b01c039900c7c826028a4030141744c20203500000071384900000f980041464044a0400c0f0001c50a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 237410071 237589928 := by
  have h0 := BRFrame.cov_init 237410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 237410071 ≤ n) (h2 : n < 237589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
