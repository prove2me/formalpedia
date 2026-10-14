-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2006
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:25:56.575151+00:00
-- url     : https://prove2.me/submissions/1ea2429b-9f6a-4448-9f3a-4876dbc05cb1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 360611510 ≤ n < 360791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 360612760 1250 360611510 360611539
    0x105031905150403030f09150c03051b130b161103010b0d02220507030c02071d070c0302071a040510080105011b05100e0303041709131806060e071d 65
    0x499015902c0b0b4441d240221b02082e0440222041c2c98407030508030b03403400380600300040d040035512030700686e50014a002c0c0b100b400c0903201c1e040060210410030107030040c00100b02c4006000000e001e4000e0248580c0c0c1a6281d01f48483c0c0c0c2e50304041540c0c1159154400026501a03160501404190fa00020701000707200d5000d600f08454184148401300305081118405d00424415100340d51091030551808560740c41c220000a0404a643d0000101e10b55a440407a81c144610b0100680c007104505200c1d20740c02590074248d1034000305510010300c03082da440441c1d00c00140d8001a008950381a601c40712902e0307034080b042d82c03842000d008480c0051102c48601d0380d00f900c0756016a40c440e00881c1640c880614413011003081e2200c03080041000c0d4000400e000400c28000070f41c0c01004500544107080000400010311968003420590000607121483d20540804d4402d40c0400960b0014007081180d40e2603c0c0cc0e11420700031141c010228200c000b0741030020103143c9131003040d08401440f55140200c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 360614010 1250 360612760 360612793
    0x15041106030a0e0703061a0409080307050c0319090303030606020105130611070203010f0501050f030303010b030a0221040501090b06031617160f030b06010c020d0201030c0210060e0105031905 84
    0x3000c0000e21511807143c481110b0062102c40d0203140140d8000c212800d21400341d010030a0300542c400d004518115240c408104e41c0001c0c1d035000520391a0055031105140701803859800381c01450400310307610490390214141c0010222003240c0c402d0f2004c1c80465036494099007200c0381203400d103004d014540c0d001000543c0a0313014001c5501002003803400e0403c50b0300400e08544440c8206804555100010b20043c038280305c0525494000310001c40ca950304201040385036000262a0049494000c82c1c0001042442400c00542c3c0014100180a5240c2800d1050181c0480e64081e1941452203011403494100410034203503020038101d580e9116490424542803141e4580c3d000d44050103280600281c03ea042543c1038010103031009850185410341c10a0b240c0090050042414041c0041000005880b408031041c0c81540900340001d100720407001c01e03424041c05400799080c1600d00640803814041d900c02e25816580c050302110314004042c500e0401c03440314000043c160368007484000e00340c100c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 360615260 1250 360614010 360614017
    0x903070b120c0720030f030f040f0f03121b0807081308011802060f04090504080a1d0112020901030905061f1203210213030809030c0f060a030c031811010215041106 72
    0x3005004c4815040403802c031b20f07066401080002c1801e800010341001510703041c00d40080034106070129124000c0c42d503075903003208403071500c0c2c0e0400740425001100c0304001b55a003000300f100d400c1801583e03240891b10700075140c2d034030031080016080000680402d21040502c00c61800f0020080610021032154080000d01e030464250b901c00143c08110120755a0b4403805a0307070241d48580c0a007519515081e1018001c0c28021080700d401c1c04480e003022141760b0340004140d800c000c06210040e070301c103a0000120701030102540060880d114080034060808502d8114584840440d80e81104203070316040080c290f0b01d650035000e000207036141b80040741100140076101201211150040c5801182c02c1d545e0130304c0c1d00030781c01500c081501040c0010681010b100742d41100784115454181d80210400085060080c1030369181010354401518420500070340c0200e02d050440100c4218802c007924060710004014044a4010300030b0940090340000e80180c007601441c0d105010340c084216000503c0126003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 360616510 1250 360615260 360615323
    0x120105010f06121d06010e0f06090103020105090301020d151e1202010e120d08040c0602010e1002091311040504110a08010603150b0a020601050301150b0702150903070b120c07 77
    0x242c0c1d422459448400390a41c007502c40314500d0241020350b140c0343e030030020300c24024038803000e84c0c025104026131950780c00c03e02b030f065070ba09080c519226100070020900a02401c00545c80f502c0ca03100140c0e40f09503088541c4c20480b45038a8804481c1c040c0f0304404038400210b0b01c607103440940361000c1039005600981d10444e0004010702400580004103141ca0720380305c844003d1102050410060206000110758801c000c4c00d568002030040c0006070180507503c0e42d240112500c4558041518411a0340d0030300c02508921108005204100780e1015004007a40144601881545000f154409041e001c0c02601c0c0c109440f03456400042c0c0c42d100041c0c01030249030303044010b810800840800d01d1007031280901801c29195000b0003596040c1070900d800c5a40c031403000c0c213200c018002c04002003031440d41118051235060758095081e10f40c0e20300e003420074020142d1107a0706000e000c8020440f0300750709010348002c1d141604ca00302d0a0b1035015940a55100b0008060012101120f01c0e11984144456440203071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 360617760 1250 360616510 360616547
    0xa0311090a0b090c09030106060f0c02010c05030d020a05120a050402090c030c0714030a0f140403060b0609030f100b040515061c05010807050f060c1507020a080414120105010f06 78
    0x400c98400003100c03103d08403515402da001c0070610082c2414244141000707869035007002000140a0107002e02036100981000303041100747c803c808104003050096810f0304240d07507425911580d0300240688282c00c1172281c01602150803001401c44960303402078034002c1b900905518919141c1c440040101c2d48001c0280c49016801c100c15800110944110320721034000001850f00c514048100801c10a0803142c0d440800094030344211400c0401b000311012250b1080c00050400000e41c00b040c4280580c038100782c2d041c000d150024030300042c042000d04207100782c28030800858144004200444100b951240700400f105001911281892402040b0b480005045010b4200c14403101d007003581c0b0240c0102cad0458100720010050b905058006039003a00c4e0854400c9d0a200c65900c000341d448100c00f41081410341108003042d849030003880320b410142d411120710f40e0b685c0d84901900a078188041c0c0c0150040e030002e22100e20304001841000d0680701808102d0b8102c2d45812412152800036540a1810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 360619010 1250 360617760 360617771
    0x170d0516110a0e0f1e060420030c0a08070212180d0f060b040c050705030d0b0111010509011a011e050a2c09071d0d080409050f060a050a0311090a 64
    0x55035428842100030b068003098040d02d8600300010305200d41000e000005005d007000742500050000d810ba86034000c00035900000c0300032201c682c01c030b00c40300045140d000d801c00000500141c41403820041c1141481510b550f5807a03180c1c3d920413070380c910769003484900302d18061200342148642100300280000000f440c1c9840700c0704540314801c203130a42c81d40450354140d880704950360f9070600303004031070403200f003410020704104580e1100c1351684120700cac4608e20707103a5038a49140341781e0140740343d41e105140c0c0300c2c000c0106280642103180203010307103c0003181c0b1100307a00054603658856007450307450000c0c088031003c1380d01c0c0c813200c2540c00d0781041010130f061100404030098205002074001c440b800e031082034294481e00281c28072520b610007901c54001c00440c4503803008074001c0900071103038081040c0e40030910100c1e03605100b13032207000f146c1010403071a08000a0180c8400b000d41e40380d00a050403122041002d69407020408424a54030000b0305000c03980d450050b00d480c01c0704981d40d000000740c40101c1c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 360620260 1250 360619010 360619043
    0x5070c0b010302300d02160b03060f1206152b0b0702120a21020f0403030503190603050d0f0302250609080406080a0608030909130c030b10170d0516 65
    0x800c0300c41300108a403240d01442c0c00f41c2c0855810841c410100404095008a007400c29800c040d0340d05c0b00408050140d0400c1201070315607102d07003040b42d00920f1040169041802d20707202c91224044920441885150b10301c1100700d42c0b2014540d20201c0c07030314881c08a402e8100c03031356604844050003070154003503004030b0003140e451000e51001000080da0a94514402210f002014a0708280c1c03512841d00951040c08624030207200c00044400380d98042c1021509c03907803403050380c01d898bd480011007942c035402c1040010401800180514055405450300381079080304000c00c038101e006207000c1140c15080c00c291082800d8001c144030321194000c0d10040740c10310a5480e680426800703031380584001101e060400c410810345d0b03c1100054503058000c1d503e00101c00c0d000030502030029060f11203030540c4e20034400c10003186c002040002d40c0e000c0b90380801031a003500d0f05c49041c031291203607003110200712199a40d0844082103040c083e0040381c44403420300400c581c4008845030024002c640309054400f4041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 360621510 1250 360620260 360620329
    0x2f100c020f06220803030403050f0c07050a1401030c020609060a09050a05010606090f0815040618020406030507050f0d05151009050a0906110309070927140105070c0b010302 76
    0x1c03c01d10350912040ba07030b0300b021812400710011507001820781c1e0014803d02c40043c0e40712003103501d07510714032442d03a444001d201e0a090a288240c0e006540c07080089000003142404005110380b40c0009880400c000d15200c10281d85402d401c441c500b019810004c009810002c555100e144c1070341c01b6030201d4800580c0c940e2460b0855015411034004202490010415503450704181000751a149025210046414189018001010f08000d20140d01c82501000e07281d0001071208400d9001042486000c0d5642812600c5040d24021030380111082420745000381040c03422011900e42c418001c0c400300c00384094540d800c08001d081c41c040f004031420005242c3d5528000c06000d1050250005140c80e00ca1907e203003110001d00302001019000d004101484070045815001c03241c030b415001ca19000c0141351100d01d250409031700b0120102c40340046051040e08100c00340d1400c0c5100c020015611820b000360b41d0280f040f900106080801c000500041c1002845060030001455420001001046226 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 360622760 1250 360621510 360621517
    0x110d020c150106170a0c0c1a0f0a02360306180601090c02061f090c03090c0806040807060b030304030f03020c030d09060504060e0a030c032f100c020f06 67
    0x4906592042012098071151400c11070b0060440741003c82c1290141e030310fa00d80602c4014604090325560700c0c041c00385580036003150100c141e4498001ca00c480600b411424410400756180014114030000041584000c0d10071101102c60349030000204040a042044d50144c070b209040891071074004e035440803a05d0401c4124040c0c0010010754958180c0642c441d450240141d000700c04803810410300015213900070409036040b5110b90309420400303400d04425268509284d100241d194640f01c0c402c5c692031b506510018420b8405e001000029603626096680c424044e00c020780400c03000c010301000104603521500e40400c010701074030308055981d2601483d022041c0c00503809600401e0000b62189401d1101c40c00c4c188075403c04500b00350078054011701a005502428042c0300b1460090b854554070321804900450b4450a400342003602d0b40340c501c6c00b9a207860101580080102c20501680381c1c4010b0744040001e01500c1d44800c400d2a80089038603900400c0e003aa040201c0241946880e101d91008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 360624010 1250 360622760 360622777
    0x1103070914090c010302190305100b0c010e06061827060f040506070309110d0302030d1104081501120308060f0a06110d02010501081203190515130915110d02 69
    0x903441e03514201058609120f440103049040510422112080400115121501100034500041c2c40e60781c40d441c1140002c410f810aa04404000c604051490015003080f007800310344001395109911100107003c0c45000440406001c030242000085102091444c0d203d03980c00300412304002c181d000803500d42040c0095501d413211010003010042445810001950022001d01c0d0802000350a5118418030112000c0c507248280c415445003018140b0070010342c1d215083c101740030003003030200e200501c0341a0f10a100307001c964090400200c016400840c0d115048600c7c030a080c140041c0a66011a801c1d280240001e500c05c000030b5000c1c5081d2105807155000e03100c00d45525090f5225182c007a0304e4101040c4038502168140030050018905c040754100041401c400300d00e44070740b01c0c80c2d910485502d81d0329407502361600d4942041814000140d12071070a40e01501c41e0110030b02041040c0f030945543c000c007c0c000e040210030740c00411150354409036210350031010060034802450300b120185c1e80001d49 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 360625260 1250 360624010 360624041
    0x13020f041503140c120402040b0d020307091b08190f060e10140307080c060d14041a0f010501051806090307060305010302040c0314040b060a030212010c0305150d11030709 75
    0x140601e51a800b041c115013000c962012a4100424640540102400240300134021601e8156040d00354552486500c0c01d01e5008041d200d0140d03c1d003414200800381d0707030440c540002c91a9101e0b400d45010702c110314051003002000c0303003510b42801401005000c1c001c07041856190386c1c003800076060304502600c5020300400c49001d00140e03e0108100e03a44407114607030034030035000180200142140024400d48825055514986409410707401800910020104082d0862100d081104020104040f49050559002144040d4803000035480f0307072101c24020140031480410200c803440751001401c441e40440104458900700c000c4000c617062000d20352044004c00d844100600440c1303020f01074403c59100074501080b48040d840300c40519150042e002501c92103200022a000d6100c00e50300201a50b0068241d152141300015070700d00030841c43c1c0701d00c03000900d400085110b101020504046c01c0c0340c024110520056582c961400c2c0103840380d05a60302d80700d00c060000c0c1c2d60015014000c1444000d92 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 360626510 1250 360625260 360625271
    0x402030103350a180e090a0302010f060e070509040e011a1f0c03050c0a06061d0609040503030105041104090e030403050f070509040f06022701030b0f13020f041503 72
    0x11840205074007260100160444010050090010700b07805030b48015030f90340703803c2201e0b0118140d0415403440c40d402c04106807898800700559003800042484419200754003c10008501900550071104203018403520021444041058a480380c0c01800400a0040000400303107136200a2070b085403a8611800c6541b201030400c038956252036806402d05403201c0424000d0f0ba481000020588400a800107080c40390206660022a20821550f03090342c1d84910100066902e880a0060a00c0141c0c0c5440004007400b00091040c00c00003641401623501c0740085045901b0b00d0104400f522007038060340011041031000040b400002c0c0a1040b10f04c020707001030340d80c1d1421070503c01d040c00024107109076154490f00c410007442d1525880c0c00d074420741209041d00c0070010380c584400644248110302c00408001c502408c801403d20201400c01320707090f00c00b000351400c6101401020401c001c0015407100341c00c074400f103861160307400822000c180106000d140540711500c10201c01103088004000a5860 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 360627760 1250 360626510 360626543
    0x2040203060120060610050f03010512100207050604060e010c14030c1e12010806150f040f0903110706090303021e0a050601090c1b20130f020915070201020a0f020f0402030103 77
    0x246c0d81c42012a00c1c68854600040e619007200540b0062080700e0150a0495002118403003c2c040f420486005800c15941c032a01d6041c40341d0303a00c40544c0c013501e04601d407a0204000410510405c0ca110b495070705c4015800c42800441c1d0100d800003041c00394608000c00c0304902205409081c800d11072030320906503484002c1e030443c1d0f48000300140c002500d00d600034004e000030050302c141e410003000d50485800302c045034807101040107441c02e0b00e82a907210b4100804c030742c2010b40040300c4400c031101d100304075000e45032759900441c0c08403c1c500c40500581c000c1c298085200e01c1c5840360041c0f10306590210740703510400e40d07113661505109911840d403043d0f541e81001c459507808803640d60704c10005032401c0c41d12041501c07100a50001442000100610581d8540403512914005404a40fa0301e0040010396403150342040a54004400c481c490402c0407107161944c00303002e041c0c80c0000d0301a03006100c2503445560b134002c2001101416607210103500100b4000351348500041d40030314402c0c4020b40000182 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 360629010 1250 360627760 360627769
    0xe010f091202060603120c011b0c170a0e0d171216080103080906030a0f0e0c15040609050904050f0604060903110705060a030c0903050109080408070e13020402030601200606 76
    0x41c00c10011500208244007456130001800426662851495076490100c0c500e050b004080b046040401110810b000742c50700c5170007100b017403a03250059012681c003000021000286109101483c0081510840d08000c14140488040325481c0300e4041180801161010300090760085541c031405114031301e04000d9400c071408140700c07810f43c0c18103290000e9411542c1c0d0888601132004268060030300030002480c0c0d1102e0b40c1009802e140038000810400f20158503982c0c0760002440403900a0701c044c030448801040d20b03022039080729030907910480c4050811040051040014006407900c0c42001104084194140a010f0040b441b5090006803a807483c903000d00500000408103c5580028402b001544c82d154111221030002d40390020701d001c0c0c0400c00b03941c1c0c11001d40002e84158079012012742080240c030f0080060300d200d402100d40c280e5464070038180c41d00045071700c00b034070000030100400141007907009550440814100000d02039074000c9440890040311000c1c0c01c55134008014403405050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 360630260 1250 360629010 360629033
    0xf230a0308220605030c16021f181a070503040305010c0c0c080607080c0d1508011a03071401030b01030b061204060b060703020a0b040f1704060807050909070807030e010f09 76
    0x100b040d08078240e980341c840040d0071400000c00c0ca0300810340c001040100c4982d140314458499500420300036480d004039040c4040c0d088060103500119002d240c40e206031103200d80000d0200e03201081030034920308011002465540004004450901c402e01010000890a0144032104007455403100865110b60401d0b40c02c00c981944041140e41105042c0440940e0001c2400d50240702d10f442140d4540002c5001c0009151003c0684808180307140301040314031040d0010f0300b40850707400c0e45074030001003c0109901c1e00c507907100c0c07050100c542c000c04401c554082d41003c0540081410300240380c1030540c0c04184503920551807590105400401c01c410491548108141083e095601c0c1d1300303200c015a070296440d10801400b40076220048001000c10201030505005241c3c820013503c4a41611452900150000d0041101145000001506117885501525010714006180d14050340764404280c0d00e060f4064034a40030540c0b02c907140001064240112802000180e00c006031501e06820502c90501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 360631510 1250 360630260 360630307
    0xb0604121407150503251706060d06032405061008100510030c300e0a0515040b0906070504090f0b060a170f161b0b101701060f230a0308 60
    0x600511b0b2075079001d50711203421481045003c0b2a82426155440000d095000e451140384113079062110100401c541c0d00303c00100c407005e04041c4006202c040001c075040e104126038039070b0880c5d4408440481d96118851982c1c00000c2c4200d14100c81e915a0301040070382c082000308001194035002c1c08039003950b201002c44096896208200300e241c1c07150303920714400e0810300b2002003140d0329440e04030b07900380c01407000070122039001086582c44503086001c1c10b01c940c021902a10b03c0e00206001a030702e444041043c034440c1c011555182d140905280c2d4170001008040c0c280c480c141d96480c00184186c50710401044c84800e1070325500ca161071000442802c040b80141900000300c80d01003400f100c0134503c10303180d811114605040d9848805822200c2e06403020f100302a003041c100030148a4084000c4802d003060341d1062071641a03401b0703044441d900f03859052244441031001340d10100104600007088070040f00c82141800041d54825001030135844903078100351080c110020b80d807400d0a0344103c40d00c1d5442c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 360632760 1250 360631510 360631561
    0x50709030203102904060b0a2d050f0c0c12071a09180702100f0609050c28020c060304110102010c1b02041806050703050a0b0604121407150503 63
    0x740355030300001e1300d118003002e4030601c07824200180680d11504071a016002e01400c0300d8642c02c00203402000d02414001907074103c041c4016803880b8050300b40e5250000002503c4091811041c2d4542500f540c1c041d54001145000b11071801d012503644540480f03171401a00018a951814005070314030340c82160750300400819080044032030303d44504000640303118030113084e5103650340c892005a04100e003c000d04050a86000c15104200f0b950754040020388001c250f0400842d540ca03400350700b6911542c1d100306c000c4c500191040b02201c0081c2c1503880400030b1741c41603942d0b0300703603203c0480d40980080c0c400311a604020070300b041c03044d6030901c20780580ba002494158404c015112040c6901e140306840a030140f0380790035405807401320b400c0300701c0004c1e54812800c000c20714000000070300505064030030707540d40c17410040e41c440b00c0d24040c0190780580e030030030081e6072201e2030a5880ba42001c0d00721074600d031140186400003031402500014207154200d10b84800e45d503440c20020801c00032100c2511507252 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 360634010 1250 360632760 360632771
    0x9031701210206070c051011060f450304140102060106090e0718061701061d010503150d0f12050f090d02032b03060504110304021e0405070903020310 66
    0x155820070003040c1550350140c4941d0703075508490409940c941613540016402203040c12496250725845901c40074640600d00503a0351580f64001d91400304441980c00411644562094503405d045171484a1070440600e5101c601c6141251440e00c00e015a1001c0c9a800750000b0500b0084071000da6460a800c100c00d2000e400c8642c100703171010340803111500030010b41c1c201001c0081c00300d9004440c44e05810310902c0c5203169182d0b90700740041c00b0035000007920308089040000040e29034050b8220100313010016a02100d12101000116029080101000848003401407481c3d000d49954001000940c02100030807103004050510032650b11784462460100710080000341d24001004054540c000c504681008180c443c03030000925101006800340410110b140440151141c1031031400d038100300d16202400b4407543c1d1000c00007201c0140501509041081000400620384036545100c0300e500403001d500810002e0012034200c49040382d0150108403040030078802e42c54100b040d60140150000140301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 360635260 1250 360634010 360634049
    0xc030109020d080c0c060d06150c05100207020a0e0c040303080f070c0f080918340e06041701061d040201020c010e0a0b0f030a0606090806010b03060406080109031701 73
    0x60103401442c0038141e400041699640b034001400b040d030310365030001d040d81d40b41c4402d280200000c050354407030448201a41c1c0116040b031030090043d040302ca07412502074012845101c41e01c00103540400000c9900c40380660f80801c4040b04286410302610701c00000c1a101c1c2c1c00d618000d481800090030350400b00c00800c0c100700304242d0011a0074041035100840c645044040e240002d881e0042c80815940405554000c6140d4029560454440c150440c0e60911502040040409254096000206500391407040340482400f41c0f03190000210017601040c605075840311520316400e48452f400820781d449030010403800c81d45441c070050b01030070080e150b88541416030004c2d603640c03814170901d410712400888119007565001b0076a0024603028003140d60f40c4107522200c140b540d00484034803616625000d80482d1280c4588180c0007540c841c1c1c0020078031a4200f12038104603802c01408070394020344500e4003180d090020700a03050f400b03121351155148416682c030511894107058108000c900d002c06403212 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 360636510 1250 360635260 360635269
    0x7091b081015031b02010f15030b0a0b0f150408070b03010503030318030c03070b2a041e030218040b010512070506030621060708011d061c02210c03010902 68
    0x18125070a00802c0e01c810290900c05a000e81508a000c5084940c3d85120840305501900420305211781e090b800c00044150080c00c9070010490b001c041c004004800001d01040074540c400303060800007d191300c114140789000901c4050b05a541c40c1100003022504102588040100c41c01408080d10305a003550305010109030b80e808000e0061034040702115501d0f0180109004581e40c21382240161b0b03580700c48038103001002010996030020503c1c07280d401074072041d0036010007521001c41d41404a217450311304110311003100041038070403500210794140000165249480116850414405c03801c640c502410901c2e041e0405030b00c40790041c0030180341291400300c0131400c0c509880702107460984948494005c11424981620320001507071003002780c00c03a0342400042062085460f0354600500e81c0c0c031307802d800352002100c7d5540c481d0700440700701154003031524544c410490500d032100000c5081e0a0340000741c2400664800b0b00c400203000104242800741030100000300c40040e8028401c210b1190b020a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 360637760 1250 360636510 360636541
    0x41406041508060f1e01090b0a0e01080916090c080a060305060a02070807020d0803060310020702090f07120c051c05060904030309051603060b012c10020f07091b08 72
    0x34108038211002508558505004c08180314018045400b5900c01441007582c542d85403c201c3e0101d041080009848046182142c0010102d89da403003665071800340040d02c02d0070000d84002d00c0c2d800340ca001c091424829100140c0200402c00c00481c51a00055014100600280900400301d04060050000c01d00c000b96150b0400c17074058005a5a540c6c81c20310448034010b0346402507005003070019100c240a61000614096041101680e1264051b00340c050124442c803c0000d40000d1900001000701d900075165a034001018180300c4c4003100c11515000c200c41c500c1d917410010540c040b0300001104026103800c203500c0042082001a400c1c9540040c6000f600100010109a15082424100b010505c01a13a2541002071050502500c03442d06001130001442d400c2e0005002d5100708140085040c64400120240c01c040c4d0740c4c2d49407070b10500005000d410030701401d62041e45d40741140c000040080b5402804100310000e40340044080c40b5442400403826002048180707814803001c25080e1496 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 360639010 1250 360637760 360637799
    0x1218030c030a0803190905010c080609040f081b03070605070f05070305030f13020907050901120204030f1416030507090e0f03040b1c052404051e0a060f080304140604 73
    0x116620ba45c2d9541d580d0302080d1a1500250040381400c044404004054100c255135040d90784802c001580c541d010f021a00600300c0d0058050401d0000e01d00203d008480204424401d0003000300743c7c680108503d525503404074030229840c5035034000300200558088682c80d0304207210302d015031030400c0030786000b800c502028025082c42450000400d04000c0c5c4880412030840e0b024023419420b02d0035070000f07081ca0300610a485d010840c4040c14840012480c03007200e0541ea0b000c00c00060000302521030304070303152864643c00782d03a00c1b609003117150001c0511031640c01148548010120035062800c07c1c4103581808508030030513402002c0d10081d2300d40120980f8144e1740c1643c402d0341c4400780340400001c54104901d200154601c1c142c14825010654910380758100d40070941404840380000c02c2c0411101c04a440c0c40713110007240001e41b200c42140400390381042d1075100c041102d940705d2900340500d010607800f0a0300c1c0d03400020200013100505100c440c0d4004211501c50802d271504082040031600c418a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 360640260 1250 360639010 360639023
    0x11805060303090a2d060f020706021c0c06090212010603020103141302090703110f0c0d0807121503080a0f08011505040302060318010f0e0f07031110111218030c030a 73
    0xe100481099400703881c52122001c440c80145a55035180070b01f5220314036440c8030043c050507901244550000a00340007405031026101c0081100c410100d4044030010011614141c4460616000d84e45103c1e03c5440d0068010002910601d544000340c126094a5a0344007800300000030001d00d01c090407281d21501381c0644030380c00b865039105421002070440c0d000808a51001050300b1401c481c26102510083c0d10040c01c0310340c030800052094400c0754086030300c50b00080c02e01d113210141c03030381d6500305040082e90820806c3c40b4a07180c0c0d40705440c2e500905104000034070070401843c01194401c0d02140186007c1994031003801086000402da441140000ba005804c0040441c03003019006019800010314074000b007003d44440c1c0320401c040c080c800d0103180e00e446103140c0031051401c00306030300302142c2d0700c4170021020301c111100b03100140046034054000c0c40001002c1d0741945105001070106c1c04000c410340c5584108501c0845141c46081020030b00030340c000490110300c0d440020328a08161f80144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 360641510 1250 360640260 360640289
    0x305010e0417130e1b0c0619090203060a0203062407081612021608120d0908091c05072436030c12080703030209011403011805060303090a 61
    0x6602d28010f200b0040c1024949041000004049154060881c002c4900081c0810711034521140c103000790040b0a0114841c3e00414040b85000c0c09800480c1d801c50129100441d86150580000c0e0903e08200e0302c5483d81a000170420080341360442040201c10b0b82c0180303008120301e040092000c240124080140700040010304480c180c050300205208030390388010b1166517884007004c003d4898021502c0303854a020707400404074a8080101b4028400d0780020811820000d5030a81c45010f406120300a40c2c5e4100100051500c40e00d4085500c43c600c0150300c2c112412400900d0309601c0c03c10310b0381c0f0555507410041461304100da84458820000c1c029803400c4119100c11445500b06440c031250310b034286103290500452012040300d1018102c0380606035046950313540f91500c070001c080b280310061605000b00030120010b40264060b2910038018503100c0c0812001011180b01d03a070083e00320284d03140e400543c13410002c0040c060b044d03100da000c1e0095402c2000ca080401c0d1155100d0041441240c5c008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 360642760 1250 360641510 360641543
    0x30d0f02040504020721080702190f080406080403110307030e0927150105030a030801060c1406070e1f05030112060f05131b0303080103060b0319030207080d0305010e04 74
    0xd80540c1c02411004004560741c54042c500000c10300302076840603c100b0351500d80248018081c1c54450320420f0590050000d400d40c030328100916900e1560f040b40c8500340758001368042009603000d00048e01d1107403200355a50403d1b05005d00703030058180c202030b0340d91b204015582c006540480e0009039002d007a030350000c03252201641034802955241c41541620180d10300140b006c14001401007090700441081e5009903268000d160b1600101d40c03001d004034010f00b004102081c0309019218809000344984c0000000306101c490503c1301c15909007000a00210880420780362031014070756100d01102402ca0384c40d2002402405602052089601c480c0342c190014080c411542c11004580c0030400c400c02c001c0ca003d440c8103d61402d917083c2034800000c001c851114890b444c00860b42501c2e0181c0703c91a03c0d030300c1c0d0b50f10380c00a013400054854042c080c403d87d0764003110340141008081ea219801800250f07040080c00b61821583d801442c5c10542804010007070200c46036036803074001e80c11561303101158100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 360644010 1250 360642760 360642791
    0xf0f04050d031a13021806180d0309080607080f1f091d01021c05010e010b031512030703030608060a0618021e04090903030b040b101d030d050306040f060305030d 71
    0x50301d03441d600500405240004d00b590f50b401000210240018820f0040c1c140d01030003880e015040381607403607400701c100701d58061030080000d05003244a894006121510b40103002c2c20700381c007034038400003091207541440b400118501a9941c0001e4240204d1128240c2c0524101403400c24814410712640d9014080c184250403402e60000d222040000d550b102d207800d000308840100440c0d5901d01520303140010032456852842c00303040f40c030242250307411900c0f07614003070b801341c01e0a40d001c0f0f9008501e400d0402c12080c1c00d002400101c2e0082e01d00040e1245404206803d00700020a51599070749049800d000411600301d20800c41c80d052200142c48010300b011044000204801b00b8800d0900410002040101c5800c42181d8520031b59003409000034200c1440280c41c1d403141129404028031640001040c410702160180d00c012507150b106070380303450700800e0904061091000001d0000402c010707480c1064003403811f40c0c0c2190202000980d04c1c54907001d482e0300504400c0c141042d1100369140b4642803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 360645260 1250 360644010 360644051
    0x110a0201060e060132041d06030f0708071a04170f01150503150a060f0b04062304030b06010e040c0210060506040602030f0a0c020402040909030e040e06010510050d02030f0f0f04050d03 81
    0x2281001041c7c0440403140b2010b504d008a48180c8684070b84040940340d004041f5551089a080d1030051030401c0c2030441380c0040d88041000024020300070300000880c03005016a07000c11200e80c070041e000c0c400000603c54259500c9900904107070645c1c1d101044a5140010508002c840e25000b40031179484038010007001d059540d02220a10070f00310008a114410100100704031034041d140d040384180441c0c1d01d0010380ca000046c0c3c02c41e2074018442080801c90100440364032850501d00700c080b44030742c0740001c1c007210101e90110005034040000b0b110310b801136200381005444108c400c2410070303140810084da01d01c5450344264031500c01060780301e40203014145028034194000c2081d51203d4549c41d20328004d0405c800b09500041400850380f4440c1440c1c4505400c80041ea00504403c0c2c4c01c01c1c0901000c40b1041d05241e0401c402041000b4400caa503102a50294100040d400f00509110500c288a25405440500240b4581d014080098000242d100c541d5596003008184524480d117844050003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 360646510 1250 360645260 360645269
    0x109090614071d1206041a010e0c0406031a15040503011505090c0c0f0a0807031b0f020913080408070e1605040501030504150f0b03010f090222110a0201060e06013204 73
    0x10a080610042004480441c01400e0047e8220300c0c00fa81d82d482c0e071b101d02c06005e48591b5044001008280002071183d0010b00b207400d512610b00d0a2070605001044130003d07055004486030401240611880ca42070280c00400c041340b01c2e0b6000440e08140020740c504102a1040e01050000500340451040620126170041c401c9001c0e101e074000203042c0401e079507108540450014102d03040c11140c01d12402c2c941c040320768010300c0401d46c0c0000c640c00e011604034041d258000b0328010210305000144804020f0014081c510081c080c098506099041011400b0b021001c0211602c0100f180300d85d44041074030205e0b082441c000c101903d460910511851640050495050030310400702518006600b0203450340c1c82c250000c008400031032220b0b400710740d007480700294014008404002641195000e4031003e0100c100c00003421424481e051440c3ea000040380c00c0942d44522080112111440007654004400e081a025100380802042c800e00d074a40d265150303034202c00703a42003403003039a1501750703405017 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 360647760 1250 360646510 360646513
    0xc0c0715020a1208040308042d300c1104020f0f0c0706020c030d0806030304080a0c03060b01051201150c020a140a0f2601020c03030109090614071d12 66
    0x2403916500948442401d00180c455143c400340074900288a103081d00e2084c5c1e01540d07205100d4980356500003281c5039078529248600b4015803800d21720b032450640e40d0703c094401c1c0400c0491441c0602c0f03211140408101000c41060b1002d9481c800c103400c148020b90aa41c842501021042c6d040b0006000780908005443d8185020a0411880c4200801000300125440031201c417103550f420300302d075140d11080301583c058014038000c0e11100e000b00d881c15080000101030340d05241e100c000c0d840c5404038040058458081c60754040007400001d10072910061428a000c4d4540001c00d0b007021131900040c424001c443d50307604212500d9902c0748100c9120b95900a241e00251950b40646420001d00c00d6603803807007100e8022000561518108445049074018056415015048198140e10174525a000d1071195020010419041c0d07040c80118040c0240d001c0c002440c10660801004495044048005070307141b51042c4903c03150840407041c050391149040b403108010f01f5010600f601030701241410b01d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 360649010 1250 360647760 360647789
    0x4030305161a0a0b10140901090e0a050106090806071e031503060203100905092d0a051e0c0a0b030a1107060203040614130215040305060702060402100f02060c0c07 72
    0x24042c403034000034003c11520609001d80e40c0600704000429030020460700c0442d40d044000307050300c01c69002402d1100c105040c1801e0150340c903443d00040070740480d04010f40781d5880c0014030036141c0000481740588000b41c010401807424120240c510100c1d00c414014900d4412074468140d0310039001460780c000b180f4003050640361307030b80f4080d400ba4000741d52900304100f02c4000401c64030603a01c242c51140441800400c1604401e0017020007132000e03a42117050300e89108001c0e0440b00401c1204401c00e40c0b1900c020001032000040012460038503007248441500128501d60003940c0300078442c2c0c25512008541030350798841c8400d0310010300712042d038a03038491070204449041c0b08169003d1881507004440c00d2040e2400740400d05a4080c040f10f105007800340c2c3c1c2d10720743c0150034401545084014900c01130742c602500ea032909407403c8012250f110050788003104000445c241103120100e80c21003801c0032501d501c03190f0b40107910345100070b002c0c515100c0041180c4001c10810807696004191000400b0300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 360650260 1250 360649010 360649043
    0x219060b1201090b01060201020f12041412030a18120f020c0d051c1701030609020f040509010c1707050a08040f0c12060b0603070c080a1e050a030f110403030516 71
    0x190064090596404c45a0000040d9150040c02182d03000c804000c03100f882d10303042e0602428088400782064507120390031310312110481410080c5020481103901d00e00c0d207a181c0342e0100800c2d21079071406c011141240007084000079045e0b05207a00c001c4103600700102ca00e01e0058003289410512289250302c03030000354010f4248440860118001d203042d121803072040c040020152030005801d0882d03030409074030324010004111a58841c0303011381d100811495101c6040b078002003c6e200d0907918003109940d60310303100c8002c075006192030500b03901c0200b103400b441c6080440513140703014841980c2c084c00301c6a40000d003000400c00841d03428a5100f2141ca05554a0f506800c0c0150003d010446c0c2652611103600d500b4034150080e64412101342da200200b1080076910484150803e404030014010821000c00c0c0361040d00c11580040e80d00c031340ea002e4507080304502c003d041d2000480104d00781440c10130f100407003910401c02c45081c1c1e501800c0440e0351300d5007900d40741e16210955501521025211000e2035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 360651510 1250 360650260 360650263
    0x60409030c2102190314070c050d110301050a0e2107050102030f061216121a0106030f11030609010303140c011410050102061009050c04030c1502070e070219060b12 72
    0x400c000b0503070382100c940014450011403141c00c2c1c040c0240c00300da401c0c1c04410b04400200c00a0a0080c400d00e00544c00036611000b046240c1079442003102e400c00036687d40c0c0e0250409100e450381c48080301d40180304165062414989450303142c1c1e4581880b80840b011a000c0300c4200302165603160303100008559a2a10310301d5891011420f0350700c20300c07850b610124110101000070301c01c400d900c3c0c191305580c0100c1c42d250100700d25a90645d000c4800c0500c402c0c00c0700e0804048451036000300b1071905d001c10604c079010a40001c5601111000d5007400c809c1c4140001600c800d080741d0305595060800c510207042c00c6101c69014003502101400940c00c000408600e02e0711034123031901590780c0400010425451300d005a88400b01101c02915800c1a0b036020072440f81d29400041e0014032458001703241179182e41b04c0c00c0c00e0042c40c0d006280c05016004541003601d504000d86002440300541202d03c81c28003000003510381c41414940034056210203141400e000c0300c5d0740305240406d402042c0700d4080031509001e6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 360652760 1250 360651510 360651563
    0x3020d0f0b0c04061413051008010e18120904020f0706091b0b0306100905030304060503041124070c090e1e030c030702190306180c0605040608060409030c 68
    0x21601e4849441c0030449030250003043c0c505403040317902c4503102e01c10404560556900090701046041350000c10008050302c1d2484451382894a59440204c071350b04060200c0f102c280c01900034040c26903007840d81e401b240d0340420106e00e0201210fa1051755800d100e80001c0180c00384101000488000141007410000310f0703400400d1462044007111000598055103031a401114452035014150400000b100c900d03185d1204800041e0b142040c1110507102d0f13000c42e00d190050342080c0080b540010070300086c0614502c0c44085402d00702c401e0b996101c4203022580c0450141c00c89821101c50220741007080262a0764440c0107070011803020070403070055070310495030798071141683e545c580305ca2950040c644402104450320090030300001c5190503c19820f010802091150702d02201c040d000021002031b40c24050441c01d080341141a94107800e45043c0030030821200d500030000c0c0a410030040010640000c5d0003603000c90300311400902c1c60081c2c28280c3ea50420700c2c100500300d52082034443c060f401140c012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 360654010 1250 360652760 360652763
    0x170a0e0106140a090f02120c0a02101401090e2a01090b09031f180303090b06010305010501091412030a0806150702030a060509030702131a031216052503030807031404020f010903020d0f 81
    0x2110b0001804a100b542121008ce07298403549406000510a04031242c000d4400e4550000448038200109090074010894049014103000d0020055004641e4030000710340140070302d641207600e804032501c0080d80c4c030143c0c1401341c540d034004200a12400c5403161320041c0d0609290603403040300240d17854000d0040140107022150b204008012407101d501c00d20405040c0d84042c1c4074102140d00300328005030218a02035401c1e0340803c0405010054180601c00760800031074903140e94003a8280790007040b9206044a004407207650b401e021100140e500001c0d0b41c0f98640e0440c5000403107458a0030164214419814040c0d00300f120702108201c0420079a004030410046444100c40c85d0340918200345c2c42e00b82070414103d1658050201440440c1c00c0b05400740f0303c0c1d1290044038600c10100c080a4030740c4400341c070a640800c01c894000c009054012190580c40025490304000070f33101c0c041c0b104001e030b802400c00380c06a200c400301e41043e42d01440203040515001415034040605a203010751000d07201c0300c1e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 360655260 1250 360654010 360654013
    0x60207080901080705030907270609090201110a0312090c05030f0601030204061d04060e0c0a03081306050c0d14131806060e01081501170a0e0106140a090f02120c0a02 73
    0x91513591084065078000c08425021b00300e01d40c94108507866921a400480b000c5580c03500400e8425180c2c2c0c07080030004c042072100400c100c1602d00014008480800c40384006401c140000b4001a41c8401484a80e03040301c1000180c0b00c509081c4100c0b40140c1d50080da4151250000d5400d00040000d00325040784d100701c0301406215120103200d00c01c904442154407112a00c0e034041000108182c00a03542c1a0700d02c41280c142042c0340000801003000c907802600ca400c000590b07a41081c0b29268904085d00c5241050b900c0c00d2001442c05591301150b000389020010f800305981c0d002200302040310f806035001c40c04002c0054841900c0c010b1050011034001d00703540790140000e0f0040c040d032101804840c051712401d2066079041050318500801d880594100700860a0040030740740c0d6450300a000d070300c0c21803000815005441c035050840c0c42d50341292918450401d10052107070754110050f4213480d0208004556926441c16000207400b44480103105019600e08001c00040404050400c1d000746a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 360656510 1250 360655260 360655277
    0x90a0905150102241f0e070e06130b130306020c0f07050307030f170c0109080a020d0201110a0f02011814100c12020f1603181406030f060d060207080901 67
    0x2005903555016101400010b0b4101d91291381100403822541c3e60041c65880600e600b10392400a00d2030582c03880d040b40203440f03400c009100889510040307a60042d031094074420300e41044014139012024452003070001b40b6500144402108403c0302040c0c0055030f2104007036450f107406503091078840311065000c0c2c110b0304c95a400002c0703c0c900040d100040301d4201f0340700301c00551300740c41307030814003110107500100c0010401c01c1d0303d003046091054010003402134000c1b1b911540d40140c02420022414000000c583c1401d07050508601210708523666001386007080c554041c4690800d80c00b62003d00c0050840791200704803401400171444881460020400039140701c1c01c0c50020764021200002c0c640c2c800038555491000c00301c00b6590090886509400040307007001550000c0403034400d400b040c100c0c00207407607285a680080402d86488040d208200c2100103a510000c0421010301000704142d18a56220020a9a64440713040d40c5220703d0f00010b05550307960042c01e000c0c42c181d01082d0f0132400070300d002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 360657760 1250 360656510 360656551
    0x10606110115060804021f0c03080c1207031a0307031506080f0307021903021c1403070807111801060201060f12021c060b120606030f0d0503070c0305090a0905 70
    0x18410030542e100c0c1503200300382c07180c00e06800b180c80d000001e208070f81000381c00200030861403503004007080f4a01d01e50344446d002200c070718004040d04005000c80b04034100520540d48508601c141c11a03000c029454001584910600e07454404600a0b14440c0c150043d07400200903c080040301c00c911200f004407e000c41e6035151300c0555505c40d510b20418040d042406000300520b0b082d020601000390b0b02d0301d04140d16440c0e400098944000c1103001e500741425a55840400101341701c81c503200030840c0c1c00b41d0705040d180d40b1070118501c10349200818121456244240554600d42c062030303000c4a00040504c0fa60312064007a008107d04e02a81b150324005403c009101703402501c3d0032040075805000c9010100c0c80c082000d4a8076440c480c01c403039554030f07045080303076079110024000c07000c8074800c005200a0901c50241410002240c01055441e0000c10741c2082c5030360803000312500f10b081407615081d14022400c0889090050b600f00c5580117400d1400021041e0340c940046000d0444c00c20305681c0d01c00036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 360659010 1250 360657760 360657763
    0x20a2703120503091614010201060801021309090213060608040519020a06080a110a0e040e0c0d021306081002030106030b031609180213020712050301030c12050102120901060611 78
    0x12844010441d002101c0ca0114562044024540245242d01212036640081c10a90204e00301c0340c02c900d0260343e002c08442c0e425a030900880700103005006c001c616010190801c1c4040000e00c1c0200c0b01c8041d00c1e407210307400710345591410b40c0c04c410b00c04a00b00009603c803007000f05482d0b000d40c2e090703940384280170300850840d81003844041e0f050360081001c0200b07890100161105200101200072a90b641c8164104605109008003061920f9948004205448800304000ca81514102c3da610b0790011065610036151003404108490301110a0200c03040c10722141c0c1c01030815034002800034060200545541101c980255060b1219600c0a106a40c1d8600c2070664a600c1c2130141d610706040301400b001541025442400042800c88040c0008500d40d0041822000300d440403201013640051090240b00055108d054121994a8080d00d0340d455503c4080e03c0207007902070b510070008a00000c008100c02503046509032810000390360011300d003902c0360a0007000c90b841110045185c0c3e8586030080c020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 360660260 1250 360659010 360659087
    0x2060307032a050403030c0f141e070e0103020105250b1e1311040b1503040303050115050702010305071b0b0601020c0f060304060506011b08031f05180604020d020a 72
    0x42e955200d0515181d520216500090044151502910b8284800c08074a0382c050300d08408102400508019042c1c0c0b010a0581c010f003000011190002203003070015080800e40581100c0c1c092030401d0b1580d1420b689106404224845031710740c0c3c489120301108019186e2381207485690b03c030f80d800780341488407040e200c01344c9402c84032200360141070401480040d880700c481101c00b9802400004040456201150301c010b000480f481024601004100802d03505014050140503602c05030a20200e080d400601140a01503009061586400004030070034802e011090741000828050f040070005428088408001a51074a0060140e002804514202500c0b040401d0001404103490b59546459940041401418481c1017081034071020203147d041070341070312010f801540078503036034141840c0c2d00e4a81236079a5081100b00d5403076a01000266901003915081c2140c0000694956031070200241c001c2c0700d5261070b80f0708948003041c0c0916942d44280400184225100603460150742c1d803454003107900 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 360661510 1250 360660260 360660341
    0x10b090105061b100207030503161106040b07021c03020a08060307230f0613210f0809011e030207020f060304050a020d08090418020319050d0f020a0206030703 70
    0x44200007a100c2031400303002d15001c6058030340a84d0350903d9104000010703a4009442900058008001d01c08031100400b40d002910340e2606140400c0086400b00c82c4c0c90381c00082c00542140e08450009451078000d01c102c034400c1e0600c11500100c042c44000280c025080580413000181c0d40e10300280e0303203040009000081e81c25403c0c0c00313a82d1580407075020071403024005020341c001c400504020600d844d84c5020304481d4a0070003114048506180084620360001e20250310f003403a004120002042010101c1078042d0f4200c11080d42c0c0307208100040c1d4607080701c6040ea101d44452046289a43d07030b4140c2c00b42c0f001310f208032400c140d00c9500f90104074103400b05442c00342c010f411008a58005180c1440c2c1d0044083c07088003814101014400000c0071140c2c035803c08600100990500b00441c5070500100441d08000500034002c44225100d181d5110300a140c0030091003481e0301102610340c000c00504a0441e401418152381c1d14080c8401070140905543c415001c44566401c001d60249140000d0800c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 360662760 1250 360661510 360661519
    0xc0801230a020705030d02030109050f070206041a150d120906020c0f09041a0a060f1d01050411040e0c0a0206090307080a0305040f020402031003150c020a020f1203040f08010b090105 80
    0x40c1c40309418800298424a03085443d48010070a000c80603c060001d14000c291010000460b85480420070600000061160046400c403c08010001d05107075001c13100c8490751580103c1643e03034107000d8203036030000b0108a80e12034140309041040141e600c00f05903000d070580e40d038466041e40c0d40c601640d803440c07100200c40d400002e1210b00080c1d801c100c1d09a03a0f1190040380916a00c4144860842d101c00c402d41c0e034284000c4e19103406001015003210600c00030900341001c2e466401d4208242003a8110601607030344900d032521600b03005081c0160a0750003408101c0c18442846c244074001c1c01d825070107082041c01502641c000100c2a80c0b008c0f003961901e42e00320000c603140580c00207085004040051088aa81d01120aa4009600d591024620a51840d400c00b1581401d50602e44600c05400b40240810780c00c129113482c007a42e0105504070342d10f41c16180488103c200b100007848000c1c00b4001d1960314400424001000c5080c00c00280c1100d460704001c2010742a45414400c02d5202401210707000b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 360664010 1250 360662760 360662831
    0x504141b04020a0e1002070311061c0c0e030d030f0b01080c0a1103070f030c170405060d0207150c080712020a090605030a09050304090222050a0e090307050a0c0801 72
    0x7070815030020b180600301403510a242d8650800000c005542d8a510000183d211440900c1084000c41d00781004040c100c03600b908104004500d1481141c03008412103003a601e8484054996004080b4400441c0c4003c00340c0b04a00802240100201100c2d11300880d01402d006c22000e555000d0342c0b040d4024550b40140920704040044140d51002034640362145c144000c00409002c241503c03c10240c09200b5a1030302003400c0d00c0e09182000f13050b101a10480808100001c00c8281d4603102141c0080c0e441040150320365516007411405a10300503400366026003400409030b01c50342d01c540c080b403090019031103012030200c01d450120b08901943c140c0d500440c1c140041445524010006541d03c902c2490021030140c6060b51000e00350303045540040009900445d000440c1d036410340f03445407115a51510254001e15000000d03e241a5a1060413054141030001c201c07020418400c440302d8a0b003000849814401c0c602d00380c60250b01038441e0000c5035107043d601d40040b900500c01c00c80c6000c2c20b0030b0381030075 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 360665260 1250 360664010 360664063
    0x90204050105030402100908030a111b0609120309210601061407032f01020405150c030301031707050a050c09150a0312020a0506190b0604031a1008060a050414 70
    0x10301c454103100107040c0000c000340050088c8003000240b07407103040c60b81c400362880784103080d441c54070310403400c9001e0509041c5550078036600d600081c3c0c1c14a103812100d9000719004a1565030a44c45560007840c0c10600e0400340040b0010940c3c10896000c4600081795011783c1d135082d04403040c1c40940c1145c60802d10810200c0c0120b0b1081601c5140b40d0300550104145004000b08441d036141d00c414002d8180e500858100000d183c4200c24440e898216a01e6500c1c00fa41500c03955128401408010403a489002104200c02d5000381680c601542c4602210804003207420300ca990381c080c0448080c07180f159800000c8010b0040422461112005850304046170708503512800310828583d5110300b1441444092004220201b01440c0100200c0c1202d00501c4c2d0303210b140c181561000c140b014050f030f0702080100700080c0110b0f202e0a07040007651028a80d030700c2e0071030341d04000300e141e62202180744504024480e01318400c0d840180200d04c940c0c0380305440703000c081d0001e80b6111b06203a00c010544070a1074181 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 360666510 1250 360665260 360665269
    0x8010b030c161110051c0e030f0c0f070f260f0d0806192403090f0501020318010b0112181227120609030201090c12020901090204050105030402 63
    0x503001401040000c1c10a42c4191441461010035602680c0c54603400100003524103004151009a00c0a440d01c149810071092402ca40c685100342e0050580359248190254018280300351a583c2c815008616945e460001002e66035500300145024580906440041c2c50103451000100300e6220181d21503100b4195040440c100e8030301090300b80c5d10b019000f0b02002c003080c180954010428641c84160207806c10030b01784415a18625010305010b40d01c1d00c02480540100c1105248d211011512441030513089442100580a50308000300500c84440d507160401c00c040d005144500102c0b2005184502c0703800d02c5a080c1d41d00020158080385038010042d000102c550071120080403c40202c04070b2000035550b4083c0e602031605154001011185c0100003400305200482d8030441642c000f100701410007261017205400414001c1259951301034000805001707401031700307031136411405411000740e07070340581209140701a00403031141d0003000000c40c14150500c00c2d9010741c2c2e01a901e880c25665a5420f20 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 360667760 1250 360666510 360666517
    0x303060d1212050a0e060609070207030b0405101e200f0708070203100204060f02010e19020d06050117210a080405070b0a020a030801050d020d15020f0409060e0f0708010b 75
    0x1d4082204000754000d80c00910b0140c540a03900354100020031955480d4102c1c145400070307048910178a40701d0180080d80390f002070518241d80d041030001c13155880c1c51078114509201f06c4491600d15051040d01011064840f868040040c0c010005020a5544540442c4802c60300e508584001a040c40003000c001c030040c000d02110f9110f68421480d20740b603500040c4c9441e000460820003150001428440c0581c4107403d002c01c0401800207024400060002e551201188100205022060404074007550f5403c0c40a00540b904400f00b0412540c6032070701a4004403042500d00094401c80445150041d81d0356020010720221505940c1810b0000200f00d50181e005403040c1c40b0f5201d00200401c80d44c2c031040052400c145103130001e0150038158907020788041d80c1603002e14820702134a851040035846400f0001001079110b0798240060020b880d140c002400742c0160015000004203002c100300081d54014000c1d52a0494260020340e20300d071011240c00411900040014540401000a010b03010041d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 360669010 1250 360667760 360667793
    0x152206020901300617031602060909090f07060908060112020103020415020102041a210c19020c03060a0203160c02150304060f06080d0219140d0c03110303060d 70
    0x640300307251040154010541e070310780c0305a0607603c40c490754412840361403190b200100100c4525036a403504650441e9142e0003545c03101d6603030161203103001c0119907940040f1400300100a00c0c0250710304013a980e484d514a0500f850604920600d000030401034068000d03101141e280d00f00512607607090018040320840000802c9050640030702011038404200d080c850410b00265000580b102e11b0051001c40c2e011107200c201c2810042008a0a41c5150141120704000c03070f039020075030711525280b20701c9100e8410042d91880720a00740d40328010039540410034001c850341c02c03000c49036540c9030200d070341040307110035615280300381d01038080e034803085004441082e145800140381d501102d09145806010743d0089404489581d52048407151000e454801c900240c030442c8010004503c45610203559024001c0c00500251500d8082c041006072044c41c40541c4640070007911110981c040b006004008950b10460124854001d913018501c03001054a204400041500460102170b444203094111074406 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 360670260 1250 360669010 360669017
    0x5012a140d05040813060914061b0601090b09061008070c031403010611100507020c0105090a23010206010608100339060e031615020304030506040302152206020901 72
    0x8030280c521001e21920f8030540c015080c807070751070300140c0341d101d02d2010031340010040c41100d10b800c1c00120041980c10114000a980f01c80c0d0784d8032000c420121150b21000c240c4140e118040002c240702d0b07800d8002034401e01040c0c0f06400f140d1900c0d0200540000100700c01d20008444400040c045480f07400046400c41c0642030010309500c5100c1203240e2035000b6000940481c80300001c078513112504000c18400c0703001c3c40d4401c020b58140194002e480e2403169102e01d040050125000300c0d1035a44810040040c4460703603480d40034030203070b01140301100c1c84d00d44414058007440000151081c044c54401d4464000c5116082e00c140c01d540d140752406108050317083c0c071800c00c80019204464940380d400590005c0c039a040d0103183c54074400501c1070310801c181a0003904034030024174110212024090071382d804100d0082d8075005140f0100d2444c0076907800034007a44a1070003840240b54003c289105120742c0380800f42c416680d2061440503c0d1071003006240c040d40e02050310408100705034080c0151034814074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 360671510 1250 360670260 360670267
    0x6030c020c1f23030c0f0f042702070309090c11010e07170d080105091302180405060a0b011b17120405010f090305070f11030f100b010c021507020a031e05012a14 71
    0x74004e402900f1540207611800403035800f03034600d2701c0802100e95100b09440003c2d4640f9409641c01010a181803184402544e100c01c1c18030400d030300480440360303020340071070007008080c480704019030fa43d4000c0d204021a00c698036294052007040403c40c004032803082d80350b140b02e59103000d00f0301c100707560300a018000b486501c42408005a0701c40c0b2a441070502002c14040a80c2024200a41400d10260844c419a85402042281c590304071080c944075209205c05000007903800e05012070b00034030590100c8a07104000405803942c6000c249003501450041008014503d102102c0e6011a8240503010700070400c00e005110002d02d03101d46400c1414070507e08204440f0802c0d021900c1c103031048140c81100d800c8030020161419542c411003030300725070900e04040b15482507008150004074080307451000180001703800c1d056440c1d90f0206001107610404400c000c01d07140401c000b4244030400c0803942542043e43c010440d034980e180031050103003280ba40d69a07801c0a600242c0306032561032000100c00f84140b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 360672760 1250 360671510 360671527
    0x120327090405100e24130803090303010f050405060a03060b04090b010603091b051807020111160b07090506181206100f0b0307080106030c020c1f23030c0f 68
    0xa1040c1030085201d100140a05410f400205080e43e1011900600741da00c2128024011103000b8000203541d4803e04000c401070326100400820f13554081d102801e080d10004c02c1c003802d4040000114121040014440700d415280c1007007006075102070f1615944455981030600c007040c29507004000722a001400000e00103e9a80d42036004403090f40105d0110f0390303444884080c040c00001c41e07a01da00880c031001c400a41440005401080f4a100c02c07061054600e0014003414003d5210f0800002403007421521140010110002c02c0050602107030503045000100c5c81030350050301482c0c15500d000b0001820300c0c0c0003038018070f0001109042c040c2d02003906405101d400c0e1003440340358098050411145e4900d4145107060701c2c550307a19400b10341e00080401c1004a05540010f01c541528440e1801003180021080c04030f00e0120664101c6034015a41c003124000f0110120900441c1d20705511003c841c0d035104000301c24005100883c06411910410004004801420041c218552007000343c90410115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 360674010 1250 360672760 360672769
    0xf080901140916050f1008100f120317131403120109140705030c072010031d0d050405060c01060e04050303041a060609090606040b0a02100b120327 65
    0x395034403010b076000728025030720b809041404480580000e8030701d04058400107001c03820410410a62508218040c2c001c66060b2041841000017060000c0301c134038480e6101c8600384550041c850b0202c0210340c0350f041c07840340803003a20740052249100c28904804505140c94051080d40384001d0b5071428002000400111518022014060301c08044001064030003148050541600a42120305100d414000c00c1102c0095804640b003d550004500000b501004a0b401d403a20a00703024551184201001002656141c0d110b8840c01050380380b11620035030322000d0650c8a02c5103210309800288104010722090134080000c2990425040000550541d03034454075280b60000e0b03d040310240c000000340300501125035a00c002506144500080d6410308800054191194441c40d44c0251200400a982d030340c0e480e0156030041c84207490507503480d80c4800000f5103c442441c046072501d03203000c1200340d0a0500608607041e40441000a40c9007100701035203009d02d034030000c100300a02002c02250051540307a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 360675260 1250 360674010 360674051
    0x19031806031509020903100905121804060510020a26130609150c111f030b0111060f07120e030f030f0708090607030c122a0306060f080901 61
    0x205a5000150540c1c2e0110091064580780c0c403416089005001d10041070b50f0104d50001050030103040090300c507101707160403818200c0382d2400714070248010070264102c0000122082100340c0840d0704100c41900e0b41e007004102c405c141500f000507404102180001203c51400410039402caa202d030204040008200302c1c6a8811001000b00e08050b5004210030740c1c0000d4504058441c204260904400311a00103151141626019001c9100700400d009207440d00c00d203600c00380c822105070060020b90002c4c06400381409000c09800176801c040c20401100d070100b286405108042c060003003e80701d21a048402c5500c820440105560780c403410b8180080030001050070120b1050710039140d241c0b5410980b03124000420072014402d440381040b00d046004652141e10001c41e00b400510644207810495914500c4c070040070400d403400001800d402640e01800d40e035401c82c407507010b00040a03441d0441c1541e40a12910000c621341c0c040851007180220020f551103101c1000005880785107055459076200f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 360676510 1250 360675260 360675269
    0x1a090a0306060305030c120a020c01050f130e090c011d04022b050f010519210605010f0906060203180108151e030105150a05040f1103040503040801150602190318 71
    0x1171000030002102c15042c060711714040c0c0d0074458141888003500780a5214550301d0380f110304005001800e01c0030001c01c1020b036100241d2100c00007110944484400d68501d4003610a10040c1c400d840710181d1030361003070046400b0312038088482001c551001c1c2c1844080d4100860801140c1002c0d5602d180c0d882c0d000410b150303210556080801c1c03904001801c0c0c1880d15041c0c20050148124a414184c82c50402603090101c0700504100101c0d8143e04501e0901205030200041110707041c1000020583c0e142606441510b003140300c00c10138660f480324166500e20400c909483d6048a05240301450b60003240b8180d4080c00e40780c030040c152007200d4000350f450001201c000030780c08900120503a081c00e00b4030546510480003403056071846080303000074000c51101c1c40b0301d900c13903030b10355009002c00000e80e00311441205000c00b04648a04080c07070499180c0e003250003195819031070480076080f140052510340045420b07076000750026103a800450504840804000e4052200302480320050313185040c00f410041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 360677760 1250 360676510 360676513
    0x120f1419061b141b0c120c090603010b090109050c0d020307020618120f0c03040302060c0609012a030203090c10030c11120f0d0603060c0e090609011a090a0306060305 73
    0x140324111241d000b1100702207210081014400c004900280d0744800c582e0071280740385100b4a001c035061400b600d441441d074500342c4c00846000c01014204030001c1c1c0c0003180c2c1c50880d207965041d40d410003454200c2d014905142d03480b685050041040c02e905500070381e0050141515240342082911540c000c3c0c1e070066075002c0050340281e0400ca4110545a8041e41c0050a24090000381e444891200d025018040c0c000701407a50001e48120584420411500156800b501503034032107030302d0345d01c1503180c401c103c41207035580d400c218191307101b40c49410000d031a480409450420f84410103404038000e4000400107403180c450071150b12440d41e542c4101011200d0165004901c0804d513100c0201900814040350240d1780c440201ea00c1000c1819041d82c80300080280039139101c0c0501c108400182885a00140007a0f1602420700111a4400d6000420042c203407541d030a20b850b03030b00034000804024400d8800d0740400e441a088a00d440e170005004140c0009c0031207034600e03242d45500d0b08903881c40d481129207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 360679010 1250 360677760 360677771
    0x11030d09030605100e22050d0206040b16021b040b0a0e061309050a060b01050f0408060f07020307050d050d0b03070b0a0201240b0702060c0d0216120f141906 69
    0x1080b48901440368400690b00803520000e180009245600e80f01030404010703401c07032010311412000351010241040c1e42080881f02030100300c0c440651644001d41307050341c6d81b014003400200800c2c0c20191202121109a00074000c690440c84800400d10100b40c100307030310540782c1d128280c05aa0301b0140002400f400315100c03a02d802d051042080200300232030740110641c140341c00034002c80e60100b45d0b8a0000e82050f000304003114880c0040380da920590044a20b080f50100300410324220028141c0e210740d400302c0085d40c954845803c242e0f40c9002d03502c002000780c3d200c40303411039501d440382024000044c1c0410010032608070210020f400e151054000720380e4060040303404425141c3c24000e10b81d000030412000c400c1910001020b00c10500d80b40070300c0d404800c3c0000e06108544030b10742100d0700d6007030640a0780d030340b0000082e001b500d4035070100c90051083c240c2c060109107103614a00c0075030900c1d0b20002c079201c031080c1561600102e540031092402c01d4000c103d106170034203000000d91503049122b034100061 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 360680260 1250 360679010 360679013
    0x70908120d1b030b03160b04050904020409050a150b0628180e06030c010504050315040201020a0f0b060f0103020a0f140705120403170301030206120901061e0609080610030f11030d0903 81
    0xa440940b92046c0c0485006140421004044a0890301582c1003a00e504c03030f4990302c0e030011802400480000034072500c00d4400b50740900a00c54120301010903040302c14402100844204000f0340a0360402c040d0210b80103440c00c02e0246407a40c441010b0240342002001ca8114207140c0c0d40d803d07004d51009003914000c00400180c1e113024005c13548545030900b441030400341480c000c01d0341c0300c040c000001e50202d46040464107580c000c0040300e42180d4030001d68010100c2c2440e004001101c00d071085030103210a4103445006601030b00a80348440c81d9980d8001c1020007000d422150b41416107c8035103400781c200240b9020072030520452a4078a0f1241d0480d03070311840c61424100d4100c3c04118001c1c0a1014401440113964541c1180d011a04c0304a8051071521400e12540c01007031140c1c05000054035182c0c8019507185048044411108541c80c1c0104566894210030b4403010210f41d00000d00a40e4402840082c1c003020061440740d0103010705460a00184020900c2d0011001e14070001c20482d420400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 360681510 1250 360680260 360680263
    0x61b1205060604030804030f150623102a0b070f0f03020f030604020901170f0702150603060f041704090203100518010b030a0902030105041505070908120d1b030b03 72
    0x641000701034414034070300b40c91500c425800d40164000240048180d0104000b4000703032802403030040044c24000c0200c06d070340342c070741c0b14001080d600c20a10301a80e00500701e45500c3c00b84281c4001000d5500c1d400ba2240f006c100020261003040070030401c000c0c6040290000c5500c54003040d128080b551961803020300c03902009000c1d05103815004007054010010048880310103000e694010300144d80250f01c0722001c40061340c00d416401c5a058001ca007410030400340c41d402c101c41c00d000d012240c0a8490055030031381c0d1000111412104c40390141c0c801000f041108404070b44807a80b0a01071319211a00c203140741408034140e84550b00042c1c22a4010042c4103082c110000f043c4c0003003000700c070724050100c1c100392180c003610414410802d0100002c40061241c44041d008180b02d00d5009008000c10320342481c0045d60120180b0204013194038100c0000c1c2110b0040f41d5800a0320140b200905090044862803c41c1d86e00001035558040d488611103c0d90f014036041d8040c00f40000e44002c10380000a60915 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 360682760 1250 360681510 360681521
    0x7120602070203160b040311130c0201060501031d070e0a0b03102a0e090601260f1b0f09010513030f061514040902030a0b040b090705100f0507061b12 66
    0x100138040c249200704070b1460300000702c8089903070000030304111451a90014004109685500020340d00b03145031400900d5040d8443e805480c42602c0400006034400d880d9091540324003084c0d501588174900c20320600c141503820550100a40c01c010441082d144003007070401155840c00b01c0c0d807545a41100b600c83c3c04c24a1000072800740001c6403500070701003600c01001c0c0400c01030000c2c0101e1215002c80c0081c3d110326034540581079154034454990861700480c60303451130102c8050603088000000701c2c0d00040e030031020031084010b40e000c081c1010351002221a441c2d000314402030500404003d500c041105a54040f0700550250154402400c1c80f401c2c0402075410340c030301007280c840e101c01c401c0c41a121515051030b00200150782c000f4421515201107480e06001013005030020084500304001c110004d00b10600c240c0c0142c00385c80c14159640288103482c00203115102c0400c0900080090840c410b0014101090043c0c0b40415400c600071110034400c41002c1201d000161841c0d0350444507001c40c010b4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 360684010 1250 360682760 360682783
    0x2040b06040810180308040209090c03010c050a02010605040209031f0b0409060c0f08060109060c0606030804150908030f1813060b09041505030d2610170606130b010207120602070203 80
    0x9134103400030b01d41d8020068040103000a126444e0400030402e04c04080150568a00e4040d0003080b81503500c010142160304a0000580158203000c00807036a410a8001d8500b640700140080c80b00c08041820803204080e60007488c1d0740160754030305c00700080e900c600074904140d002e84400101c92951600040031344011103140300038400030350184912664861402d40c110b84491800f6811803110345092000303818140d10140c41c6610108000c0f8100c60842c0b10600c022880c1d44603840c000395030f05012030300c074012007a40c3d141d109000d2215411000c4104d08601307640100505c48100410700203c00c004640803500820450f074000703d2403034030303070305240c818514801d40c010b004219092034940001d036150030b00c00b10710040251040c2c94402880c00102c4681c00d5001190040b00c0d01c0c0b03010044200a000b0f1407080c012084000c40314003550007070102d500e0f8000c001c041c0c0302003694403542140030050008104d00a04500c1040300009103049a0300061010030320802c400350307981e0b10900406142c12000b042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 360685260 1250 360684010 360684041
    0xe1f021201140a1829090615030a09020a0503010f05060f0d0506060d06090c03030c03030507050a0e121c091e05030d0f02010908040305060915060a030f02040b06040810 74
    0x31560100e98891003c0310440c1c414003001c100f403070010380190b4041c08510058004640e040300a1800e0301065a45120140e502624140b07a140c2c1da000030000e242c0c4424801410100e010000300b0303000001e940004402e6030029040c110600d5651012900f1035114040e040b040303070759902c144041898601040342c48050308480c03075501101c5503116207882e01c101403c5144603c1a9503905020060290040ca00c8250000070480c03429980b420050325002680c0000c038002031034007001828041c068020340714005141c0c0d68003a0706d0401c24040c018603d410361600a04c61080c11140f803606a9a0040c00103501e01c1c40e03644814040c42e140c88400c160410507202d0740000713500c07103081c0081c0e1030020343c0e1001200c541c40d000303100401100b010790041c94803c8025103514070004021050100c005403880c01030500b0401c8942170b01a407919444010000d03141e03240c0c0107046090410128051003034484052713000501c00500c4443c0380c80011682d520039405aa01c5400c182c505c2140d004007445040c066040c3c1c04c0c1d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 360686510 1250 360685260 360685289
    0xc080105041109130b09090619090f020609190801020d0f0e2104030f0b090c030607080112060609020406170906060d0b04080903011d0c06070c0303030e1f021201 71
    0x3034002e4680c1c026200000e0207000c1c85091161100c1d41030304181c2c0d01200140c050305181c05c1007146143c4850044444228225046d030058110310b21070b00c100c19803545c11a102c0e107107603003070f9508000d1540d21071540f01d9440240c00c100040008158624500181091000140c2d204814030901d01030316100c220014515203001c5e1003964070000172032001c024400c000082c41c210446140005d06502541d0400351220f01c003a80901c0411602d0031881e4001c20190040300d00d594503a908044e500c900c121500400a8850801003121810307140f0f1150b0310a124010100b41d903078880308c0c4582203801c079a000340002030a10041070382c1014ac1d1150aa0040c4081e405008039191076004102d0809106100074602c08001e0300040910403554141c0f070001c40c0042c001c0c0300e07250100300646107540646210484901999980e003504e49840740803181c1d03c5502007014116545951005c0d802010305d40410402402015542e08400740c21605110340070070180320040c1c80c2c1c201004030704080f18058106490b41113051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 360687760 1250 360686510 360686531
    0x603100b04150e060a050909032a030706020a142b140c0a030617070302060901051c0b040c090311061b0d090306050604111603020709020d020909250f021e010c08010504 74
    0x401107510ad0a03014003501d01880c2c2282c0c0641c0c3d580364541066030340740000b04000d0708108841c0c00034400b00b001da0361401000f0b440c0b0150045d840c480e02e0903909142400560348905007042004542c84507404602c00105030203002c441d140c1c540f2040710819821440024500c040035050705c078030806448a0011401c24004210140e69903810501001c2d100b0440414240040e138421400c461080d02d4001c02d181e080b03960755806101030031180f115180b045d8101168581c400d480340f90b407403003140d400c10000d0804158400511030903a00000c00007404070265844038041810402503460403070521f6555110503403542c10030000320345d00640340364030076801e000784680e10a00c0402915140c15074034550780b9903c00d41e45810b070302c0c1000644c40f1003001400410401901d00f41c0e0b17806010f00c1d1005a882000656a01c000d0b01403005141c00d1003c3d902840070342c040721f140d10a01200c41680510300498441003080d003c540003141171151541c0060391100c0e0b00c8140c03c2c1d841240e560040005450901190012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 360689010 1250 360687760 360687763
    0x50f07050306070c0f08120612010b060912191202010501060c0804060810080712050f0706170a020904051005040c0f02030a050d020d0609020c060f0603100b04150e060a050909 77
    0x140a900030050701840c0d104c14405a2171800d070740554001c0d1090395414041c101841c0d00f4101711a0071340304000b00014248401c2060144102d1558001c0810b40351200e448100981c603145889400000e1186441030607002c5114000340706102d0103103c103000c045100b01030081c20344005802a0080000900240001940e0101502c2c1518140d02304100250fa4280c2c80d1102c6001130b038010703503440c408d4240c00034008046a490101c41070164040e07030008240d0302400383d9140a41e1003184c000401508041e2080e10000c3e000d5508081c0c0138401510309200d190010701620001d079414002800303851410456880d00d8480c40d00e40c80c140307083c00d40ca19021a10040d44038012076242105202c40021128208022981180c084030a58901089250746805840c0020b402c0420816602d1003010082022415140309861003448010001c0080d10f44c0c0c2076907803014005010b1805c0d00f054661880300601c0303038040400c0f0064070790405010024500300080000445442c1d01c00e40c0036030940c40c10301a09000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 360690260 1250 360689010 360689023
    0x1809020901120212060f101a0d0b01021005190606020a0f020625080408070602062404091e030801140105041703070c0b0316030b0105070b15060c0703050f070503 71
    0x2d9400c081d0040070700d07400404c46030501c21a800d451401000104400c0a50100010740106140c0b074038500c0741900c030800c1d45240d08990742c4100ca0814284046075009580b504034000c003090610541e00c076902040c0303400c010f50340d0076202801545000240300407104824070a85c002000d140c402400881403c0c0c942d1000301d646104042e000b00000140741001c44000b541840300810201074100850f00c3c9418030401a0300b05000307a140e140a00180025000c2c80055414080e840e0680e1030300200d500350743c0074044a0b0158000c550050346640420700891001c514906c005030f001159140203055501c1d0090184170305810001d40b990400161500c6640d0200645003039410f42882c031090643c80c00503651442c0100313030006100b0f58050402040c1c0b8001040a14055084420000c1c50344105801c190250b440140f41280003070f401b031004401182e220b4a12581000b281000d80c44894990342c085581c2d9800f0301c1e03007241c1c43c4c1d2000904008001081003101c40d07520301203000e080740398107020019448a2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 360691510 1250 360690260 360690269
    0x18060e040f0612030809060105040603031707140409140702241b03160306081f02160510060302010905040207020609010518030a030903031b1121010e071809020901 72
    0x107030740711011103100c070300e56100a002c2c05882c1422010b081040c500100700d80c038200c0300500300d401038400010b0103040a0244506681d810384078404103a00c548e24140161500402c1501008910708880018030380340c20042000c0c0c0741201000c10040403882c00c001c09a58040c255400319401060360b2402e0b1000d2008600800d090300000340707a9911945940d00054954044540106000200b0301803503042c2d500c0c0c220190503a0f905d01b886910b40c3c0b00e0a807615031003151314803944500d4203051075503038110a5005091101062074140d030a0001074490318504085030030344401150f1f40d00300038400d42d82c00c882c0c410000c04044400b5842d185155012900e0350181c0b1406505005001c0783c04104040384100c0c0d9511018083d0880324601410708000384402c3c0a48401d50100d10131080110803903060000a0010325080144002e2007820311090140001d10191800c909a4400030b40e101900028000c6070306251901000b091200c0c107100341060003035105005441c55500e0440903200580302c3d0703c180c40c11903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 360692760 1250 360691510 360691519
    0x61a030d1e050a17010e06030d090e060d03170408181c12090306020d0506090609070917031204140d0203120402090604110304050a030f0315050906040e0f03030718060e 74
    0xf82000c1500b501c0c3c103030303c01a8910b50082408004510308140d00f401c03500c943e100300e086036004010031070300360b604151a01600040b24001d20000702542080810072281c903220707280001c2004440c02c100100c025003510b04440c41440002c508842000006a442c031422044980d03131641d140706585001e441c100c40a006249680440c0c401e0f4a46014819580045401080a565a04c0955141c06c02040111601403049407940c020034040e0070306d040941c0c454200e640700c151026044c07c01240710644106a199018072042151403030b09a002030030240654800c03c801c840800080701030340e00380088401c448086500501c8946c1e00d106120842a4100f9015a1150419100c80c00032170050b0041024480d0140c400205002c10481c4c00215040440d00035610441c80b030003650411003d4030b042001c40111010100c130144140d24083d0f5806410000050002038002029105c0c0d0341400e441c1e070384002160b0000710030041d46941040f9101604030108800d42d040343e0a04102030815248003031082e000c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 360694010 1250 360692760 360692767
    0x50f0303031b09130b010306060c02010c020f061c0501210b0708090c0d0809030601060503011d0c0d0e070314150115030605060d0b01030e280302010207061a030d1e05 73
    0xb8003010b0301120749152001d41030701242c21100f00400d0180c082e54203560300091508000154045c4121100b0764203030f605a4862100c401c098082001c2020300a42a90f405101008500808180032600d08804420a440400c4662511048002440c9100c9014644288412182c1c1c0014081001680c2c0001c1c13500341380130207032034500c106490502c04501139500b014150b481801840102c0b070140588a030f007102118410303038036110202c0d9140400c1c418007100304001c9400024012a02c062254408500b20b0280d00349584071a940c401e030350007600240d40c10b81103140c00713109011a822943c080348d0000c01c02010f03001c99048003c60384207814410285050100d001c15220ba43c4207801920080100901050b03c940443c2085d800524418094602007407401c0c051200b01d40e0045400c013400c000c00d1140c081040b0300c6002e00042512403103400c80440d5070030400340b03000a1305440780202c40700b06180328a82c80502d950500d4942007421481d641030120280b269034200e562409082c412100e645001e548 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 360695260 1250 360694010 360694051
    0x12030609071404030c080606012a0510180c0902070206070605130605010605030a0608070503060402010e010915030506180411130f0515180108030a2102071b050f030303 74
    0x30000d02d00800140301d0704001500000f44081d070740080e020354204000791001601d481005540301318000481c4500301388001407003e0028040c503900d040290084064841034907244d40c02d80c0844820100d04070340011420840070a02c0b610030640000b801c1710000852501e41b0b170390000b4102d409242e03c01440d4130346450000352950000d0110300e0032203500603c28425541c489101809540048802c01742a500d440c0300001d40601c005203903412600c0190181041d501e41f5001121041c64400100381030103091140001c1c12100140b18241003006075600003000d09184082002b0851000c004c0c0342c10040603424400030070803d0480e0320040310102c400089207401c0c3c5800740043e102d00600c443c10f0f40d141c001044900700500b0b0000840000880340b030304400c04154003001c51038100703010300c494030b80c018448142c50074000d61444802c10380055590310b40b000500c0708903040c0d83c001e141c100c0744c9950304000441407224041c0c1d6078020b04000c45e20480c1550044000c45c0d52400010701001148110b6803c405 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 360696510 1250 360695260 360695267
    0xd0c0b0c070201090801092006040506180a051809010c050403120807021606020601030507240309031202191e0c030e180705032e18140112141203060907 67
    0x1002800300400030b010220503814901d1100c040800c000042ca038119000300c0e0a450004101ca0642f200181068200881c050b9080744008a003006a50008081c0030003180c0c565800051003c1300c44010518421440c02d9105c0500b9150007102000c18088140300500000d03103601e0705400c101580f440d000380f160b515418202d2a203002548041001401c0d0340000c01c42542c0400d08078140e13805030080380ca034103075100c0b004481c0f003045400c0b01070084500301007046001c1c42a007100d00e2060291811021880206e8000c2c4126408420016540c41d00e1620a0301071540149482154284480180c204000350800140c0b6044d0500e10040c10040c00682403002c980e16241c1c00c0d05510311340403d109861804001c0a011640305803540f408480700d12550319052849003039000302c01107100f0668200f8501d00402031203c0e00c80c203e641c07e1055154200d0b298070300144030360b1500034122000e0300c0b4018007460070a003400c445061008048e50300907030391001d000040042202d80016094403070403155030320342e9000c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 360697760 1250 360696510 360696527
    0x409050a0b120a0209060d030f1409031c0305070f0906230f040e0f060109030213020712270509070e0a030803010909060f0e06160203040506040909050d0c0b0c070201 73
    0x490b4000b0041003110114100042d10926051080d541c00c00d450700c0d101d0400200d0301e00258002c0014202242186680d41310341035101240152030305060904c0e682d1800203003003080a95840852041e102540700100b54103004840d0025850305100036032982c00c0c3d1004200d040d49014400074400c01c6a81e0b004000d80f84084d0f2894182c885c4000d40d00c0d8500f0513103101c7c00d0f0380144200001106104003140d803418400110030700541d81616002c503061701d140e00348103800b80c04d20650a5134507801d100800c003141a107c03c0741c1d2121b003156111202da50840c8440f03e5900502c5145031031030415074405102a0312030440c1c03150802d129040000040902c0740005500600c3c50b00002c0c112200440000f0b41d0356401d411039004030384030f0401400305840d41c140030070459052a040841d145c1c02100822f41213040004d1030303c1c0f46003851050324030f8503440d040450115130099100700d403410f84c1d0322842030601c401440144003450b641d19004c5520b41d10f940b01c07002c130554050401000d0f04400112982168060b2521 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 360699010 1250 360697760 360697781
    0x106050913060e0f07170103060c2706020609010915020c2817070203060a05070302130305070f0b0307200c0423010b0a1209060626010b0102060c0409050a 68
    0x80c8002915041403004042c0f0560360007541810080204500a000d0005441d81141d203022440342a860740d201c40c0088c1c00712094807404d120b6103401d00000802c0403025940041c0f20400c100d03401c1c61400380000c5c60080001c0c6044a01e03454001002c00080840003810581600079402585541c40300c9556030034641101000c0321010340208814211385400100050b42c00c0c0144052006401c01d000c8408151048230340003503068210380d0000340d008141da0b101a400024510f801030424074202e040f40c070310081d1508240c0b92940401020410740642a0f040b10144c12101400d07070550a1491010b0314461031311000f070750070300807441106000000c100842d0310f40400007007040c012080c8001e4100a0790071034911442e2403c2e0540004290700c210300d422910007402a41e1200c1169418601c0c4200504c0c5c801400c41d515a00c501c000280340c62010150401c13420a00c100303c0c681e0444040d20f50840301000d42440c150b42006007040a4005400b050310f08450b071001001c1026951140400002d1040416 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 360700260 1250 360699010 360699049
    0x1f061e031d03131703070305031f18140610021c03110f071415010605160f051f200c19050d03060801020301030f060b0a0305010f0b0f01050304020901060509 69
    0x481d01600c1c55406000030807140040741307144504256480303454491040300b0b000740200e4010004076003000c0c0c200655100e02d1040c8102c01c0001d80d190b1100c050748071082088146042e40312002c0540c410751828910360403010171030b20991a110740c2d9001941740c8a002c0916100ca40c0c0090307840064500a4001565100c01b0030b602580c0d1340300011742c2040303907008070f0001d0b1948074503061071203013000e0001002c007a03038016289080c40e26840c14000b00d509500818203613926541d103410b80360000b5804643c0480c3e562292000e054444450414080000400382d06880100d0420a0340a000c8140d462440e00d0912070800455540c04442d14492402c41c28005504440e0080110750041c010701241001d80d04c0340e03940d4144005507a403107115090b80028040640700b803400a00110000780c00f0362001c20311110180100c0c090341e940f80c95680c00c6a001c008068041511130800007240d141c02c1c900a0030800b000d00b80703036055040c40e401041c240340e0140100000c0c00b04c001901d03002c90b900d1007103000550b50000d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 360701510 1250 360700260 360700267
    0x2415300109090f052e0911040e030d1a09060a15050a200c010305091612030905060d02070b1b0a03090c0510020a06050105150a050a05090402031f061e031d03 69
    0x480d8049102100b220317056600820700304c1585180d82c140141000d80e03400510442c1610300c0102000028082c044982034144410400d6403d048064000c4510310342034400c1c0d00d621b10311146c05004904c40d0040a82e48a800f160745c050201e41346254074009100032624060b610303081000002e032a02c101603107481b22110030f071000c0c10407000800240c0808406003a079050180b920340c010702c1d9a40c3e002e0090746420101c0162014000841c0740e805d4240101d00a25003030a81c20380e2100400e4081c5e020503038032440b40780c0002d441c10130b104003140c400e42c200c403c0c50754040328000800d048401c5400f0710f200c80001c0540311004001805401c01f002c5010f0000207040000e1480b108030b0207580c0d0200301b0001c0700d000b030801c0d0002507249051a44001c001d41d01034502450400840d600f00c4440d03004036004418004144042281902c803440903501c03171030007400c0e010070002c640303002900440f400e58000c0f010440442c107155401c1c50300c00907035090709465007008200860a01d0115005981d4030012050511022 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 360702760 1250 360701510 360701533
    0x70305120a0902041505030a1b150807020c100c0305090d0501110703110a080406051c15030618260c010908030601090e07082415300109090f05 63
    0x507800882241d1086134200711624031580c610ba003120f1240304d2903038580c10481601000c5000b203070b1001e4004280c000740444090b140d0345008000f81e185108900020f8a4104204c41c0030380400400700300680480704030500b03d0210400400da103100840080400c100455088010346480442440a9030f01400a0110380c0c165682c404454012040590008440e04441c1c415040041042c144082d0000700c0c6034070300350902d0340a60702d590084400000c15414a10180914841c42c8182c400c4042c01c0d612242900745541000c800350780b0300d0084003060f8401c44100000080c00540301c2481c030f039042080101d040030440c0c4090301034082d0402c20354095007031102010400030486c0c002c511a103407d0304c603500d4081d1a889090b07141907040340ca4101240c804c1003c035034a42402d0704070549008400801280d0070010001150a20040d84200100c030b031000b0174601407040b00d141720104001100e042c0302e00c1e181c00d00c840141611206100e03c240c125652034a580a010f40ba030910880180c010040b21460b1030203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 360704010 1250 360702760 360702781
    0x6070c031b05090906040303090f0b33030d0e010212070c050316080c0609040e0d0c060507110a0204020c030f0c0c01021515280902030a0b01020f07060507030512 71
    0x7021481440d001c60810204040c82e00886050140241e080103240369903031990b0030740040c80840c034243d4102c16030010040019001c02041c62041300e0100c0141012410320034071906d0440e04000b8a050450a242020099100042c2800000a9a03d0804411014480180c1c20403030130089114441c00005810400e010401c4d00e04000ca4109a0484884403520b14640c200c1c5d5009024010700d54200c2801d08a0a03c0c0050103000341c10002400090000c506498072450080d0b19544180890b40f92504a001c1c0100c07413040542c000802e0411240c1c2402408100e9103903000320400134401c0764081140f8001c00700c00c0060300c080c100403020380d940d42d4030450381255a030007080c01410700501c6050340701e01d074603119184410b00403a00c0808130050300c403000381041601c00840d109003103141c0c1e6031606422000a10484100201224000165a4140b5907400070590f4400c40700a4155402500f5140c520760000848008481040c5440b9440b00d800340303400c0320644500006c00c1c440d120b200c010720101845 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 360705260 1250 360704010 360704033
    0x806070c021207260706140f09060712030608060603030f1b12071e08030f060f04021903060b040605030414010209060a26010312110c270a0e190206070c03 68
    0x4000c401030082c044074813030403942c0301418014040081c3d000c8001490b0498000c01030402d03695940d0401d420700b0242c1002c91640c1e04041e0041c0c2e0324041c440381002d0b2583d0988184006020fa4074017600c0c481c0307401d60120703580f842103005030480b0800c009460340485404010710814601540c3c1070740d01c0d5803001012651180c1100301c060ba60044141d10b030a040c05284035000195990040e4100c0c11503452a840000f0b00c080200a5a048020300074410390595480c4020b00c0d2030140804100005044908001d00300c0d011070300010030749001000140719090b080743c1600d0b4042e5000c16503085072404110f245019016031550183c1001c0c01007a80710781c223038210180b060314004150015000c40044800001c1d011828800601168076400868a14600c58002181850b60402c11034a41051040204481c40d1408002920f080c010001030401083e0100f40650005001d4400380041541c3c40b41c0346840b414100c0884c40034060b441503103000c64071500c0a5504081d0800c10b188503a55807410141c41c42c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 360706510 1250 360705260 360705299
    0x11030106060503070f110c0121050a240305120309150a0c11011a0f040213030506090f060f15011103030403020c0906010c0c030b1305061018060806070c021207 70
    0x1781c10038620f0100324480c90600e4010312008000303283c0c0a2010b8010356682021144105983e03424064a4814a829000702c074024110b2600c00035202e400a07a0340070358000201c1c1c007098000ba40300b0040000c181c001554000200d141e00c686a50f03511500061813a04542071100750f2000031560811504102590164081c0b01c000d8403007024001107030342d20900720780c000840310f440b5805504d4144c08a041060044c0205000504014900020041207113034013001a84110b0300380d400601005151141444101c100b2440140109a1800e110540b5908014010a0a00301d4580400c4044a0340c1c0710700790259840485c001940d07524205030070b00035110b13030a0708606405904500080390141d481540448804c0381c0210180e40d002e0b04554904441d00300c06806055043c01603083da8020400c103019250145011440d005001340c40c203070360315508040a41040e83d84604e131410400600c0300104015a101c10186010082901d083c400600030031403400080b5001e02c0799640110781e03040803151020410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 360707760 1250 360706510 360706517
    0xb0a050603070e0a1e050c0a0809190807020a0f05010503010312090b0a1106060303030c040e0604060503070f0e0c040f12030201110a0f02060c07051911030d0e1206010f060c1103010606050307 84
    0x80000b100c05d10070303030300c09990726080345004201615a040c481c41d0816049a0984d00303445100591481c1103242005d00c0c0f0060304c0d45c40340000c0c00070851402c1e240c0c000060003040ca051500c00c2c1791000182440c001448041c000f04292001f460880740700f210503501402d010070216031910342c4101c0040c4440841d07400041c983c803612003c0340d100e107400030070b4a01c50540c04640d40c3c44c05042100d08800552b0180645401c02d8442c00041030582d07080c842c00f0b01800312030f10360740341042c40d000d40c0440c0002d01a062500d43d032001c110a015428000c0d442e08141d411040b24103043d5469490300324010068281c0803507070200c1c041034032641c9950024004443c10050342c01c854594482800104c0e4906c10340600a0659021141c58512320352070001e0403565900552840c10808409808242002404502070b000600010408640d61402012045d100500c400c01050700798140301c039400000d00540070700c60034001d0481000c1c00700300316482c0d506d83c460740141c001d2154990742c4d4000f034484d41040c2c0f0038a010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 360709010 1250 360707760 360707801
    0x1005011502010525090503060c070507230f0d0b01150e090c0307080702070305060c0d0e0c300304080c1f0e060a1101050708100803070b0a050603070e0a 67
    0x114070502500c1c1c00b5640764405110408000c2201d01c603490b144c600b01c0d0b01480341d42540000d031998144200c61083e44180301c80c0b5590806031603c0d03400c011a50300905503210402c1d05a0b00b101d104803188165404068078416501c10321f82c0000741e14898240002007034040b1040010840c40b0f10b00c032240d007038401d007a00c98041ca001480f0402410100403104070700b0002007440018012842518015040100f50060716117041e107030f0719405e003800800c4074ac0390701c4528005280b6164941c180702c3c1e903c0d8190075001402c0c005462400085540440b180b0f4141000c2414019054901c00611407030500c4a40303801700c030380d19581e078000c00e81c89501c80c00c0340900c00c10b42040b109641c80121618000300d200b8580d166610002030000f0400b4580210103003004100c0c03c41a01070300324009101d00c0340200d6807900d6400c00d03032030b10603040340c01e0780f0440d0400305160f0401e01c45100002c52170059540c00c9060307100c0100d2680e4928012a15108040c0d1100d11200b5035101485160905070b44035410180d1160f40c203c02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 360710260 1250 360709010 360709049
    0x3052503120c0503040b04080f0708070b060a1805090f010618050601050f0406050304080d0c03050619080d0e2404061b0b0613090b10051f05091005040503100501 71
    0x44403540b03814180425401c20024001419202109620510441001e030510340c1c1804082d80b25000400111401580040c650041c020100310740ca5102c00b045840006460820506001c001d01c0804071140444d2188007080c0808401c1c468031340f2580d4107c0080080b6580c4400c039203052003540040d01849403500e004103440d540b00d00301b00c1d07036aa10f0405500b0314240c0b42807800c80b455440108207940d0850140f21340b015080050241505000c42030341c0100341801d1040c108104048a8804034203075240f411810040f0907008550918000d9050031302e0701c0c540904401140d0003243d00740c1b0001c0700c407501d46030340344209100710b0191040d500d50303594500490190400e05170744000c90344400340ca1035014800042d6907280140b007a030700030000703424045081903c07965403040e100804d8450300244441e607442801a401c0c081c0104a600c00039180c48031203040c3e840340140c201d01c68180e000d401074820405d04859140524103c1d0010800581100e80401c035641c0070701e0091200703004103601c42c524001c41c141c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 360711510 1250 360710260 360710297
    0x3030c031c0608031b0106030807151a090612030927010602010b091b070f1101020114060a0b0901111c030b030d120b040f1a2b02010c03052503 63
    0xe0039241c0d43c07001145080c03600a030103400701c0c11030340441040359260f00d00480000d004c200a071072401c0c0700d169505040680d4400003025280341c0c10b06084000d4030290142c946030303206226240c100005a5030340034070309001005103040d449803902041d0000d94180c668443c6000c0b84015246180c80344190340320590f00c46400300e090345c2c0a0040d5542c00340a01010910010f024000c41c000544101c40c42441d00d1303c2666441140103010341c0641e00f1400e62405001d85580a0144001d81e52801e08003d003a41303020000145070603043d004210b440c02d070120300c124260b401542c2d404840718030401125505100e407035490001c4242c50361a0070000b8100030900c01682000208003d480031140c45902a01c2d180340e84c040d00821246107007e070b00584803400e204000b484c52144e2881c1c40a81c07030030480d441d0340d010107104c64031085165401e1a041104944280200310254803081c49e907092a0000b403203481410f0494071801000255079180004107a18030032030307100310140241c40b486920b9114800e6007000c07040c1e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 360712760 1250 360711510 360711521
    0x6120108011503120e06040302040f0618090503040b0c010905100e16081b06040f08012003040519030309140a20031b04090f2301050c09060d0b03030c031c 68
    0x5113120b03001e84807000340324020f10410f08003010207040c0300d06056907500007a066411110b1900000c3d13549580c184200034401a2500400c0c1c0450300603c1918460303941d1695034481e80c491080844004a00e60700109002c1d0010b400098019045541c4500c41a250800a0400c3c1d0440b00d0300c3d11614160303410349030000406900b01c41180d4094605180000710020011000e2004203a00440800010801c5404040d6540140401000004680d07002c0d1010f01c1d60045030680140d802c4000f4000c000004000050313203840d000f610b11010041c4c0078103140540151041d103030010a04003051300c03054651103001400189040c090a44040c1c0604010498195800a1a00242c1682080d060741c002c1507500d01d166583c50f00090700c0028054000e4581d03040e40101c540781242c07600c0c5583d50100083d4040c002c0440000181c40c020000d90a0403054252103204500c62203002d002c010418040201b0306600c00d00100f0030280540b1764400518250a03100d50082c0040c3c1612141c2c0f02d4102e02400310351180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 360714010 1250 360712760 360712763
    0x5060709080d08160e090a02131a0405220908030421231c02040305100c020a1502160305030a06061403010504020c0f0316020f01181505070206120108011503 69
    0x2c500c081e4403135a0141c260324003103004a80034403180e04507400d0561500766215215803020310f0b00688411020440e82c5840905502c455181c1004050350402e148902044404950b001c452944426045000f07005400b4002078a03410400e00d01030f031031303070901680000440c0310b0752090484640b1240f52140340504c00411042da50700180061550700b81c40042524454142d41440e10310390f04240c030000800c50505400d100c216007154000c5810001c00804108041c005084da5a0038440303030750b403144000c0d626200300d032014000c000082d42c2d0690a12050741201c94901854507140303100f0000742005000eaa100381c0303420041900c3e003440081c00303501c01e1803201c1000e001b181000346540d28003000c20019400c2001400b0680c001e04c443c5400d0300104100408040e0325040601c1121b41c5240100040001d915000d41d040c0b050031544d03100314400640001081e1000c40103081c0c1c0d0a4000d100c00c6403036001ea030600035080b440010310f03003042d60704410205048510060082c0060480700c1284207041c100b41c4070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 360715260 1250 360714010 360714017
    0x60a050c0f0724030e072d17120a08070c080715050f0618041205040e01060e03011a01050d09050c1008011404020906070305180d0819110c150909010305060709080d 72
    0x2801d000d000ca82ca503410505c01d2010220401c4210350001c036031307000c070340e41d48c07203124111070540d03848100560601c0001c4542c000f00c11480d06000c15540c019024500080c640c01c200034800075204200030035001603626440d00300d101070301051072044130322004120603100d03000c0c05041500010040e1030725600d219406800480b03a4074054a41d950f910003c0d103440d040e1582170001c180008a00440800b04050080100b65504280715200c4801d050031503099001c09050711010b81c0c16480c01d40d810008540b1540414040080ca450a0382809414940000c00b0030380d00034074071400c0c105601d40c0032074054160b030001d10b40c21128100860820080f03128184105030007070303810720060012a014002408031040c43c54007622400074500001088828822001ca40450001c100c460300307040902da40da603003104c03607080030324607803450b00340c1c036941c440714411b13000e2255013282090b8880c140c003842558a5034001a20304426940c4a141841c0c84210441d80d020004400003000135506500042e203a044400d03545 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 360716510 1250 360715260 360715273
    0x8100e010b0901200a170408060c0d0b0402040501090311030f060a0b0111031806070501090c1206150f1a0c01050a09031106010e0105101b0b101202060a050c0f0724030e 74
    0x2a600c000c415113406d91441212024080000e0107042401101c0c49003228440e020703999201c03400d00c0d02c1210b07003042140b4099881480b0500c81640c200700ea082c142da4000d548903186c100c0010009103803010180c10041e140c0aa4003d1000742c0e04c0d2500300c808016000d03200e19603171b030602c414559a24060440c3c401091507480d010041c1c103050407001040382c41e0141c0d001081c0054651a1650040f40a84c42399827400c02440c030110501007940704225001c08e8010030301a4680c40c000d104404080240900c0300078080740f100d87c1d607040c030044e1300301c41203140d02d038000303104a181801c41c1c0741c02050858410350203e14118a003151100c000300e04941a1802078140007400d034240403e004a0b9481002c24a00f03119104101c6800907640e202015002c5101e00c0307840c00b030380c617100c140000c0640f0243e012030446420720036103c0c01a66414162100343d4560310b850360322003c2d010081840c00325203605480c0c49004202000c62681d40c0d106d83c200664450010114003030b812040110129032700a072654040d90040c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 360717760 1250 360716510 360716513
    0xc090b031015050f0a080103031b0218060613080705190b03040f031b061b0507170705190b01080114011401230d0504060605180708100e010b0901200a 66
    0xb150a02d4050094989103041101c00c481d90200e44d8441088000480c40005c0100109a07010700121400080c1d918000c00045069000c02c1d015400030750300d52204800c020001d6056101c50050304d00350040b8509030426141c0e602c0030b40380c83c0c0e000d41c05603601a0002c2401514000304898000040f642c0b20310b69685035a4441d142d10740721011b041000c070b08012502c035500c51040d02c500c0200d42c00344c1c0141d000146d0440980520300001422826540601c5014005000818001140340348010a010511a9205d00914140381440f8500b407074444c0200130300210305c051081481d0814107a0380300f071008101101ca00707030068492071001d2082e550a4260760807081c01d04e5101c2d1031360961002000d079410070207880911400318150041e0f400219600d94400c2007000b48000c5000d010020702c4207036040d81c1e080164460188445400030825000d002001010440002404400c4070003030040984421041d40c40301c00c4004141c0c4064001400155240c94002100120f07140350034074200c60100900300003905 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 360719010 1250 360717760 360717779
    0xc15020d0c030c0206070c0e10050406150309020d0b07020609190c0501030c0e0603070c021c0206041e1a0712020606132004030b1009020c060c0309010209130c090b0310 74
    0xf0500480c3c020704140405800503804840d080050310360b045403501e861900c3c0c0304050541e84c0a1340541d1046041200420a10802040c450f0a2030403074034001c03803441f001d8004500190340309070b4014030b0315080d502003120441d80498210f00654a0000f943c01918000415a0108400d9140901401c0080348200034560080d4026801d1100034281101c1c0c00505800040c2c49401c211703660800f0641c5a030000d0214900040c2c09040d031041070402080545040d00490070f01c1c041c034021481c3e030b000405210301d0352a545889a82c018080c1c1a041014070007601d421b098180c000c0b500407100700c2c400c0356014501034000b00c1c2240c0b003400301506000380010f2210703904026040300d4a2075590201030b0b403445201c5400000061020714051940948a8200254581a905020742c408150544180422903c068000c10f4694000d44020740c8251a41c1300c0d04401c600901c41c107412242c0c014030894900300401000d4010621004003500c076940f00c0c40d542d124845c00c9100c04c42c1c801d00380a990700d40a000740c124 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 360720260 1250 360719010 360719027
    0x5031f0905010c020705192303030c12070c0506180f01180806160216030b061302070506160e030a020d0309030503041806060e010e04050406180c15020d0c03 69
    0x1000200814498495100c0c1800c41d5940c4841a005030011030060203641481d07404001860034400f40349024a29050305088003c02d40c0b60480d00c90640410340c100c0c40d5600300281ca2502c0303180c00540e00ca04078100c1100c1c026038403000c0c00312000c10341008001018a000400e42e4090810301201d0002c0400d101d08000c6407801d2130030410705021502040315000c0d07c00ec009a0003400e5100014081400c0000b444a00f0074442060350342154080c044a8070500c00e0034164804030ba5000c1c41e1075000d0785070034000034142d220a107074120415101181c58018000001040c0b80580203401d034942e212441400304030b80d5400d5074403071075400d54001c1c401c2e1401400d204a11907030344c41c024541030f10320a86941d916803d607401940301401d0f01134074035056048080b07e80704200007444030703080544400d034290001038114440a082c807889550b0310800102446819041102d450740140b00c0709640801501d01088145040c3c000c082c0c5e520010524808011700025131240346040b01c1d00e80081c004030380c1d07500b00c42e9100c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 360721510 1250 360720260 360720313
    0xc03081504060902070602090a0906030816170304060f05071b02060d0e0307050d0306120b0c030601020f07120b01051c0b070c06090308011811040b09060418050f100503 74
    0x5682d1540010083d48a2001c0d00083c0d100751000340e5550905000c00c003c5503c150400c42c8082d20b000300400018801400300e03050400042c440f0409041a400c00c520903400c0c4035107030442aa4000f0801003004030b164400701c4480161401041280c559103000c6881c1070a01030080900c120244031180980b821401901c1c40d42040700c004500501500342260840e00144400c070380b507505c800d004060240e00360044001816030302c002e8000300c0d4425200c07134200f90000b616601ca0504000b022485c01c4c2d00c244001041080a84102d81000e0b94036005040d00500145058440c264000004501c500d08241200004050030702c030802c0c01c4a10380c0f6032501c0180083c0020051140ca680b031000050303494003440740c9440c0079071681041da40c5850800191040b0800410181e1850302c450070701401e9118083d101698107001400c0d440b0711301c080101e41140311302c0d009200d801c0801c210100301c10303201c0d40000741700322411a0b4401e05501c4010340262420554058941c1c55040b01031808034030614000441c0031034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 360722760 1250 360721510 360721519
    0x20091918110409180213050603030f092806030608030c0c04240e01060314090601140109080f03030106180b0f090d0b09010b09070921020103090b1302100c030815 71
    0x5983d034620f020450324184506200144601003000c250702d40142d00c2200300b42d410704140460714001000a4603441004401052001c010520510984844513020740068204901010610854415804a290f80e00c039800c0000c3c10b040d0f0210320071201009031006410540b0007020300401d04400c00001d0300d40440e0314803014000351590310320b001c035600030f80380140a10032043c5603c2d410300c1001801d446800c006d003983c1e400c8032014071000f40310014210741100c8452007405001c0d81c41c1c10049966004c190b1004140b0321800e2030000c0f403a03002000450481e00c8980b034241040100c0c7c01da940c80c04e00144030309040008c0c02d20002c403800c400d0600034111100014501682000c15a40f00340480d041520740740240c0e13640303003078060803420078009654000900e0704100e05500e16164044503100c1c1c0c1c02d0310344030800b1019070382c0b1400c40e402904054000c41d444100c0c40042d150562110250503114502603204024915908a0030350280ba0b020300b0150300740d1ba910300a42d0318203106040e140810968103820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 360724010 1250 360722760 360722767
    0x2030d02180907030f050c12060f040f0f0515010f02070603050a11070501050a06050405130f170301080f0709050f0f100803190801050603060108010312032009191811 73
    0x150740c514858520035030341600c0c0017032400c101d24201001c43d90018074000111804100f0150500d520310100341d413040d1b0846440b40d20001c0640840c01518102c1c680e42c980c0c3e0b0030306c0c18034200365803190041841224444941140d007a030180044494452030400b040140e0440007090200600c00c0d0402544058210000309480b00c0d900040c12640c1e0040070103403901c0c1d42d030381c00b4809442918010300c0f0040c00212818091801c24040c0e0800a2106942c0100301d25034440c40c15081000800512004000d5904085e45940c0d541d8009030300d505424881c031080b802800408214401e0a20400d4002e88502140c000d40781d584640301c84050401400d00301010038261000100c4503c208024419280c0000000303103008000c1d640030300f0084040e003003948151000c3c0300b04400c9036813040c0c289046039040071409141a0100e01d007500103040884014194148410a000182445600400100009541100e0002a202025030344002c4034007510020400c40c490051003800250848201241894002440c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 360725260 1250 360724010 360724057
    0x50f040f050a150f05060904050d050d06051c050f0f0d141902010b010905030703120302031e070509090901050f060108060301020408010e0c12030c0a0b0c0405030d0c021c020102030d02 81
    0x140c3d03403242c9543e41da0542e15410b40004094031406025001030064130a501c85040035610b05442c0c1c1000c050135020410007261454400360b0b9038101c9401000040c1c03c42e604c4925060001010080c1024140e820b0b1140c1c1007014084000040c413405401b2007000540510700e0707088400c0754000c004800c411042c0e03c2c207010700340b1000480c0d100282d01c1d034160f40000030241020f0f8000740680320194032151080c0c00401c410400301d080f01c20140d090550714900141c4d00c1d0395210140e040d40e60101004e0b85028098003c000345c20741c108004011400781210901d0046e59910303015804d90b04100c50305001d5160700c80209103d0f5020310b08094011000070000f40c00c041d191034005003100e030001c0d42d07101c540c0d00c80181100725003030080100002900450140d85091038602c4036035a03401e030305c0c0402028909803000050044841c182030710003600c00102079687c071514030840209140c80008060348505100718072100e522001042207034400394180c000d542009a0751030340034000c2d0070040e007040d9086401690b011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 360726510 1250 360725260 360725273
    0x9020309010b030d0e130f020f040605030402030717030d0e010e0f0c090606041514040306110a1409100305040c090507050a0210201c0c030204090e01050f040f050a 72
    0x1489844400e00008000d01034408061414450300c60000c140310218000c0c0445441e45250030180c4420000c001c902640200700d2072009118034038060403143d101103804505164071800450246000f20103d9251540350344640a00c0c11124600d4800d9074000c0045620800554002500596000000080400807030021a042c800000611155504288128800f030f1824006907a0032003c251a110b040c01d0800c40413401c00d0070041100014000303139844038001c1d80301507002c85c2d02035648404207100768060005155555000707140c00502259900c110755140c500000140d0b81098030003410b026500314035220503001401e002d0800d580d402e049190103d001012401028051031055487d565200400400203050011400000c411681004400225041c440c120004880c1c4a00007040d40e8940700f40105c03440c0c481204902d4501400c0400703240107640c05078041c0080382d03000da10900c102c40410724054200c6408448050400300c0440200300441e940e22100281d42e031040c0100c892031038884c1c6400c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 360727760 1250 360726510 360726517
    0x9050a021504061d090403080430030b040c021f0e0d1e030506010e10020a0c061d0f030a03081911030717060109030305031e0408070302070816050f01090902 69
    0x21010120002010000ca0342e0080c0c1005008040c454030746201310b50400042c08490026002078208404000450240015a003880410120a5162000d50300358050b502c08400315000103800032925000301503505091134007550900800d1580604640c1070654450b5038150700e0500d4059040f9078070780202d041d000d41040081c000107821b80f18103d030340306500031950f202981d4a09110425040c2014007289982242103c1c00c0010221080519210189000ca18107558000d02508040131745038001016a002000c5110101c040c20003a10f90201700d2083c4190003030212441500340e0301c1118080c0129208800168010b5005841041540005061181a10100040b031004044004280400e240d08007020031010301c19401e11042074680700001810b1294140b2001d414040c0000000d10014115442d007445441c04081000103803d040c14410a5a0040c00044015106829001c00d98003000030340105031040c1c0321803032040103060030280010860100401ca050041161000c502540e050001c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 360729010 1250 360727760 360727789
    0x6010b0c0a020d060e011508060705090f03060a050f0601022811090c0405131802090403020325020a060203030108120c010213060c0b06060412060506030a050a0b15091003030309050a02 81
    0x7080054031480811b0855009018600710300e180803008010130100418820b500200504145450b6681c0e61701240c00390030418412030b45401140d0803c00180c00c540e1109000f180b0341e55a1100c04c0d0b032854010790703480148000205024640e403070401c10b14484180300d0ba000c00d01c01d00b02d541030100781801242940c5400d541c0c144030101e0107d03082c4454140000c420905540781c50091050303a20022a08005481c4043d02900461141d00000c0070305000f0412a0f042500f103400d1030f00361054449903440e800029010480c031070104181c0003d8094400000d980c165a2500c0c05000c000c5030011031090740b6482004806901d54082c4888a94181c54115800c000e040039201e41060000700d1904516802c1c00a200d20701c520340c14007040c45404040c00d9800700700f82c7d004034005100d4540c0c41c0041c4c9002c10f1240010800d103d60520300080211102116008003800030800c15100d01c0601040492401100c070301c0c401441c00c41c801c0020900c039070040c15145010380240c035640e00c06a0041012004099103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 360730260 1250 360729010 360729023
    0x905031b03070c0306090f0503030114030c0301060806160c0b150f0a03080a120b0307080d08090d020a20040f15060504050616050f0604030906030e030c06010b0c0a020d 74
    0x6100c0840d0050841104500091034051460042182e507642010304243c00043d0566699441c07110401207260025102250840e08581c1c80f513940d01e0204400b8201405820b000380100c40e50124142014001c10040e40c082c0005480d5998030900c2c505201a80c034401c050400542040c40008241074600d0540030713084100c8007004500041c003d22201240040c006401107440703070f4040010960f008c00342c1e0100c0c841d81c5071070545d15180890090141c56144160340d0305004030240001c95080008000d0f0072412651a17204180d5644911103031a0403914032641c0c05130700035000400001c0c800c2d0109481c2c8207803a10700482c0506440010508440c465080800351543da074841031011146c2200b44001070045182c040d00d8241010049019030085210348000b004032144408100142032010315083c900700022143c1c14509428010140c0354980300707080101c0d142078000030503200040b080b90a150700c114010a0203920705003120000d0703805100c1d00034917802000301c048010b82d150b04451100700c1c094103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 360731510 1250 360730260 360730267
    0x4091103101203141305100c0b06120f01050f0a050610020a02042c150a0c12181b0e01090c05160302120a170a050106020a06090201030b0d0b07120b0d0209040c09090503 74
    0x5040c410140d401925a8048c043c01d680340500080a80c40001e0b84400291409a415510b800100f8903229159801c03d07029428030041003107400080c00013521174202d107801401261284814040742944c60180c2000580242522801609090300700c0c0c04111203040715055000518094074107801d00340410001160002c880c502d2819400100703860700308087d0390b0304118940800001402c99955450700350384282e02c41104a0480903861400c401444d003000c44d1540f8140e14a034521741c120914002c12100c02d110703600206040149100750043c2e107183f030b141d040c0380802804200a0a120b001c3d011811485840d514919120b200c0c0c000d40040720341d07500c031001000074002da0408500c00040c1102000381c5000300400c460343d17000a03000f03149070704070b034000442a01900040380940001c040d0307150001141c56034001040209020688a0110f5507109000103180d0762040301901c070202c075455480b1180f06506805843c0c007010242d040780c403d0301040311095645204c02d05031551013000b80d0b13150b000407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 360732760 1250 360731510 360731519
    0x10030507080604290a0b030c0c070603110315191403060f070c02091509070c050c03120f0a022103070f0903020901150210090602040911031012031413 66
    0xc0542000088800344070641c0b040d11000459a084c440b01100040401d86040540c0ca4540e1544040e1182c00030700ba9030381c038001c003000145034007a240c04a00385c420301d000003807024428450362a2130b100038240c01c1e1968840b007142028090001103d1903101d49401d1100d520000b07582540d1000f0140c40e40c10a034000c802204142c181180103028051101402d070800800580c03000546108580c11642ca20300b41e1112a0a520380650710b40b03256410089131070500201c980c201c4100c00c0380c0c074444c00c12244102c00d0101410b41700c0160500400b9448400e211200d49100d080300038080b01c542603c100c030441f041c2034249201c854410004950318080010912494a44c4020f003114103910904003684500d10715070101d02180d605200f00c0c604141c10305001010b041c82480f45420100104606012074511824100025409841686680d07884c1001818071000c4240a0300d10a07242400f81c2c01100d45840280040b05804080490400c41c80e50380310001d100e0400041e0590400200c610151981030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 360734010 1250 360732760 360732767
    0xb07030e010b06030c03071107080c040c18230306131e0b0a0f180c15020c06090d06090803010b130b03090c010c03050c03121f030b0f041110030507 65
    0x10454120190741082110b50294407908210b035002803504030030a580342c1d9100011564036564481b116201d01680c0c0d00081e1141d00013407000048081214200444500e1a01c00d9a41641e40c03c0303510904903946030104007402c3c03071a00c100c03405808181c01c070080e0700078040005d007802c104440100030740394924102c0052040c200821628444008507088055803075448840c58040000d144401d0140c0395102c10b414a02c0c1900114440001c1c140b0b071044800c0645025040c0c08018040d000b900d1000d039106004940c40020601000107025004074940540f000c10300c01d00c0440620b040d101e841d220403100b00002e441c24000c3d802400d05480d6640c80e400046896500a000c507440052000814414440362681c0070031240321303000003401c0001d02103095240c1074030f45011300041941f26000c04161226411b4020300410310480b40051030342055414248074801240035030001400310128240060550030220319040d42190003541101d21700d030b454800080ea07880b0300c2c0b408000042c2e161814816640d42 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 360735260 1250 360734010 360734021
    0x312291c170912010b030c030d0e060309030412081e04061b020312030c0d1506050301261009020315161409061305090f0c090103020708090d0b0703 65
    0x42154803400c0809000426408000300030406018804010345015071031803681e084550260016041c0100f84500e81d040301d000345800000d9a001c3e01503c07400d0b918500d4045041500c419850720b44030a0000702c0014003506400040401d249407104000c04288101817101c035081ca0b030b00c2180e44c01c0d0756426030f501040c410000d5000c210380011050009008450700001c1005600b5104042900c10402c2d034000640b801a003852481900706000050001c0e541990300184041e001c84c41042c05100d122643c42c100c5000a0b1060100040041c0f0042c0021f100034a03280070600d091628100c0600c144c000c000d800c20070844810680256600203220860400f80021600031420180440492800e191481f000402c1d0030501d008104400304a11107246800065400c421809071034291206840850b001072a0421f0040510848100000401c0c16440004030341c452807005031103a080c0b01042005601940210384101c902141c280020481c070340311410603000e03583c0942030224075401c058001400300e94 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 360736510 1250 360735260 360735341
    0x102072a0803040b030402011d18060328080c0f07090f050610090308030604180f26070b040816060b04060b0a0e10090b0309010501140109050306130312 67
    0x800c188403c100d91013000d01540c0d84642c080c00c140c8080c423110013a503072a004544c103041d03511100881c020f0000801d10760036140b0595060701112041c50000340e0100e50341c61081400c90925480b641da030000a0004405403800202180440340400500c0c510a4245001ca801c005242030359110041c44442c118003950b40c021100303030707030040040c852404001c019a0407400060402800000403407102d45540c0e11100582004034031841030f100301854a883d9440309100c080d9081e0b030f9200030311203500d00769069801c001401c03002164584038450703541c410402c100a0059450718400d0002c51815070003071501c690210311581c00004c1090349070341000704480303003904810514074040c0032003e2160381180b004110f04008403015018404680011200320312982c000101026011041c00380b0041c05402c0745041e15042e1503581e8071044403100442e030803040c42c4203590b4940c1c0040c01081d400f43c00c001180c40c0c00350092424003010109503607250292800120108200e4403001064101c5500103250503140381d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 360737760 1250 360736510 360736513
    0x319050a0210030c120504030e0607081b0c09040b100b07052a010203121305010207150605060708030109020a17010609050112060312080903130909020111010509030a030c020102072a08 81
    0x4c564030403000b40131101800c0c544080e1542c80011909060107000803007041000200300c02d0740e414452801d2850b40c1c110062005250140204141d03c9480c042000e060b940d4000d000303d4000c0d42d86460700507490750090b10703518481c03400300c00c08203052101d90300920310b06018800808082c030000da6100501030070f80103100c1e440740101410350b400303a0f40407007100c40b8030b41944681132507a111171002520103640c1a1008007158800518041080042c035000c04000b1102ea0f0b08021440d0b90303c060003402e10440e500140544c20800c0144501c0140d540074061098141c501100e00364000111419056020b80003103000c00c113251070411072356a01034141c2e05110b081c58414440140b643e542d409a0304460040c803014494418009000e5000400c01c2d50424201942640c0f891030f9030350410001040807650a80c000340200c0460486050705001346401007051000031458820344102c1200103000303040c03d480455400300f0050003c10905242c511441c00c0204030348105105204410038162400d9004003402e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 360739010 1250 360737760 360737771
    0x51009030201080c09030f06010914011e0b0a02102405061204030c08160305030703050a14010501121104030b0f100e0f06010c05031201030507060e060313020319050a021003 76
    0x60742d000700c00325007008031416407941394170450001074109080b01d0040e400512034040002400c05098006c00c1203059081d4209125980710004100106082d0304404507900945101704401641000245040d11040c0305645035952030207028020350310440f2485c0a00362041d02c56001408010030312900401c01201c240b403500701e01300b610303105480000700082c0038400b6100e0b081c401d01604008a48801c2c040e0307480c2e90480203180c5806000c9400980700b000029244c0303800104004074512440d00c140d0b0701041004410b80c0781000440310460845000f003000c6803a440c1c20000b10341c054029102561281d80444800d1400641e41328075804001c0a1310000c0c42c3c14281001000d0b0b0388103585811102002000c9240ea07507520050742c003510400b40c020401e00c4005003060400001015450683e440f035000c0d07410344e075601e03602281e200e42100652a40010204041610035813110038a101252000c0c00399559201d80008420280c032080e442903034076070000741c250030861400f0b4550740b003103010a003001c001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 360740260 1250 360739010 360739013
    0x5090a06090c030c1d120f010c022e0c2001050f0f1905060f0a03030201090c0f0602100207050703080310090f090f020103020702010215010b0406080934050d080405100903 75
    0x101c410032400c2511802d80ca170400c0600752039254504001c450b801c01128620781d203008410340244840e90f20780c0014080d485a1400c030f140149500803007070584107001001c9030142c01c403010062034819100414081e41500030303460301119002070480514184000200d900d05071205ca8101b0700003d0070200f00780421410400001c9115071000800a00c00300000b401c0d580c2c420108484070305882c140c9500400303503040002010750540020303245a110305e2604a465941d03004146200303040e4042c1c039000d60402400500d035200294094030320140640116900c40d44c0e2626000f0459000b5610703000e42e5400c1c4442401104294020100b240c13000c100108440b102ca038850540709980c07800300a04042e00000e40f1025a8402c00c207500c0c04c2c1000d40c01e9121596034503509668168894851748011801c0400010035140e00843c441c08504070002500012040d081012801a988500080b045120804000c141a1280f035543c94001e4802e25002d80d50364200380c204000e5942c2d0350301c0a0b04002081c4410300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 360741510 1250 360740260 360740267
    0x1230603120c010603060204121119050d11040507020312090a020a0b0d090c0905060102190b0402150d0c0801050109142209081204021009060c0201120605090a06090c030c 75
    0x155941c0c00e401042e03100d02041182c103014040130b0344040c020714004034011030103031410400c52510764403800d4005d0f80100c24800780000e5400301c0c43c5554003506000720030001401c0c0001c54140091084a81c10410101c0000007800c994098070000016440400c0484508162210342500b20305040d000782054402507000441085090042c030007503810208100d44143c149800800d2196441000d05000d5070f110070034200104401c0310070320300610a075a01140707416080d030441c3c054580c010700b0f103036041d82d100e4013170206050200c0c2c040170505000300450b40c41240c95114403840c1c82102e65480d042540f400000514000058200840c09011810301a0ac203507121108821113441600e604584048000d00c04801000da64074040c01c01103002942c002407500050707103644602d108540304441e035006200101c2d02d49009014074004a84000d4020740590300500494429003443c080201e2001d031260041400c512094603881d03442c80d140e6005010201c0f1900036a034180d00b00d89402c00640c401c030f40004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 360742760 1250 360741510 360741523
    0x11401032001051b0c03070b1632010501060828151205030909010812030109021317060a0c021204061209021c050606060a050913150801230603 63
    0x140a8603400c20344401c8180d020b6400c3d075002c085040c003a940d10100c3c00041e076480f40c10201496119024485000c03d1480862090740c0c01c20704c15510820b03e003a060707514404140e0303441445d04100d444111400003141106c401c0e218000240000100e0154074158001d0060100039240080182c41300d1005920aca00304440f4000326124003901041415280c0d0700d04000304800d411100c140502c3c02520024004000020b068030802034840c0905aa0b8440d8000d07116075841c080c0700e146180c20401080f0302c0750590080d109907445510701c190210b82d142240e00800b0480104a40385801a00400882d400c0310701c54500d100341503001804850b440c603110910148218040e13202840000d449407021034089510048602d9401b03400b800f001070684011854030465603600300d9031032040f44c00040070303414910250380300e03c012a21058184091902000140d84890b05082030180c0da4030300e803441d00310314005000000c20410000091782c0034110300c4c2034456401036072103800c020714210503c02c20307840c00580c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 360744010 1250 360742760 360742793
    0x212090f0120070611030705070506180a060306031202160611070905070908071205070e0402030109230d03050c0f070c0b04230108040b010b0a030b040203040f0501140103 75
    0x440008480c0c100503034100014030280094200300b040028852100010018241d5106480315894170b841c80b03031016924440c680000300345420071481005981064405040070744150116403c10403036503404255811103030340c442c20000381c0f00c0a0400a200d10041030002500607440a86250411509030a040001381e02c1550300300301405558900452092041d000901003401e0244840e050000d40201a00c0e56409400102d02900b0400500d81070a10180a000c1d80d0050140c25000d2401414500c0500c0c0203006036019500c441070300c1c000542400d19841d425071480d03500105d4462040e07072185030404482e8001c0902d450041031004204082c015a000790140082c40c5c0e5a81440e850502030780d0700c19510403506141d0228011802c56016104440f84003401041d801100f8082401110214000d035005046c03441c0d110b0060080f4500f8800030400c2e107046d814041454001100400d04990040754103954661700060340300c0412800b030090042c900360901101090b94115220703031140304544500d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 360745260 1250 360744010 360744019
    0x703090b12280204030c06090e1e1308030901051b130b1605160e160813170412020301050105090903030f0718030506090d090b0406051804060305100507021209 70
    0x30540e030301e0030b2407400c044105080c0b20295241e0355285028039244155028910124418040c0840d0403100142e01030b1098841c103c404280d54041c001450000320058003c034801c011004d25180850ba0000040d8050036480e00002518944000c10001d854440110b40c5500340080208000301071980d034404060703500c00c0120660726085504100f8450b1502070009156014103841d4a0400300303200399140c100e881c40d89003818140c1c1c0300c2c21031240109104522601284014000ca80c842c903e00b031621004920554115040e484119100205604030f0341c011030804008281040440c20280919401001c1c00d5030358081d00c4c104200300301d40700d0000400d0324843c03541c3c00d00000e440314800e48500c503c40c80c480c00c8018030301e0340300c1c01e02c00d490300c2c0121446020b51003800e409069261065000320121a54107100394181414002c0444843d4031480403007003c04103a00d100480384e521482080011b600c41c030700404c2030b1645c0d1a17a0307400341c2b40300505031421340d00008030040185007054100c6105501c101c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 360746510 1250 360745260 360745291
    0x4030201211514030115140121020a110601050a03031101181109060a03080904020c010204080717070f0b090d05032106010e09061e0d080705030703090b12 68
    0x1c1201110041400d404010300303082000955881400386a600151050281c585451526078001d00d426500c07440400104000940301c20040c1044409003411242014900954080e414040d424055070340701c0301514999034009841403d650b0801c03013201d44031003000094041c40d858980003441008061001034180080c040d88145141402c1d03101401c02454610382c882004218101350240d00920b1202c2c501409203003011882030320b00004000103c940c09019140340003182820302029404c894002c1d405917400740004030b00c6010910800000d4151821000c55080c03400707900d01c0c034082080d4031541810780c002c1400d00c03c860320b0b002203441c254016115044103400030320341036103144602d2001ca440b82880c2c0350740c10814054558128011182680e440101088543c108418008150f0700304d80c3c001c050801c11000e046409031800728503d00100054800c201c00d0b1203800c49540301040844a64100041590406420090000c013801c0122807980c10200d500c04890028540900142c890f0314040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 360747760 1250 360746510 360746537
    0x1d09040302030f030c0d1109030d03020a02010e0a050309010305011d01090213080d08040b090d020309040b120a060501090f0e0c090903090a1805010501021207141c02060603061b04030201 82
    0xc108035a1815101c1c03ca550392441d000d4000038041e0003036181c21880b1401c0103d99400c214206080c2d030895070000b406040004500300c0194002c1d805030340030400799525825403a03251a0184820300515005901843e9100103a8000604440d0f058000c498610810030603c00008e07840030701e00703040da10000d0005945261441e550500204c1c1644014440c0c0300b0004106801035121003098001c3d84610503109254440340620794442e00448074102c0141e005200c8140030f481c16803c0405485400b60010000c200c1c0303820800e0404448202c2910300b40e031140b004101c04d10b450701c40c1c4c2e98110340c400410866241307214207a036110918840030074403032816a804076441040c248220742100e01e0062481c4280b9a64006600c0d0031030f580403842c0c480c0e51505000103035550010403540824442204400d00d490381c10f07500d0148100d007100303a54490348100c03204401c00800c0e6003100d180c80001600244a6860144101494440d0051034030140302401070881200c076915500750707415a64242400b1131303400c201 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 360749010 1250 360747760 360747763
    0xf050c0a08030c0702030709020910030506270f070306030b13030905091906051c0b04060e0307030e030d0f052a0a06050417070f120e030d02010c0f1d09040302 70
    0x80c25001d81104400070500c003003280e08000070501c062013a01515440c5d69103413481c000306d001d201d80f1582c101ca00c0740c0a074044c0134401d0b40040d620035001440108081080c0340d47d0000d40442101c0508480603140c02c0c0902012404500e95124099141c140031480c195500e9880903503000c5e0800901c05412540b6500f0036000303600c4103000e0300010341000240c3c81e100003d00d101c0c0c0444640700070130318a4400f0100345414010380034428540c400c0c1c01c00b140c9a03003580d03e00380f0602c0c0c000c0040d2105c6965050800304400140000d0410600a40d55001c035030000c1030800d810a10080c10420034008a00b58940c80184c221003960810503415440e0b11042200c10701909040b01c0400075800c89001d20940d080030000940c2c0075500550044c840e59288142c10342500c4194821660044c0c40b40e240c06825034001203a00365003000042e2245084848000004046450892401000c90150751a24003122803e83c4c8142c10081d800440d1410103038075014440812881071149180c10b000342c00000009091500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 360750260 1250 360749010 360749023
    0xe1b12010c1b060e0f0606120c0f12030d0f140108010b01020c040b0a0f03060212090d090504020a1b06061a07080304320304080106050109080c09151003020301030b160f050c 76
    0x3403540580720413800d01c0510741d4441004a0305544240b0100b0036040481c8000a0503412700400600070902011101c0c04016285100715031000d0b582c401000b140e038180c513883c019404070f1940c418010a011513607030380c07020f42c040058004540c40c2c7c1c5401407140650781d00090a0014400a4400180d0340005001094000000da0441018a41d01044c0007040003150ba0042182d60324070030003c01a074481800b100d03150018541c0c4000080e8070814140300700c2c03800e07078001d260020450070041c41e100d600c103034040c0007030040348000d5828035603441c82000104046514150302403200c102c882e10b0b0614545d245405404042c0019101c0181249480007406919086000000ca0300c0c00c5900c58505010703405591350701c18004c10304103500f04200054903500580352801070f918070340090014200041d0034400f4503a0010840c0d100b40015002c01c0c0300c184c440201c0046604019038002da600c0d81141000c0070200c4010345508810055030204501403540200044560391841c580560354240030055140784c040d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 360751510 1250 360750260 360750281
    0x507060f0f110d0f05040213020d0f110d0b040204050105180a03140319050703080403030f1119090e061021020a0309050c18010611010e1b12010c1b06 66
    0x40c03820300c0301640104a400540080d80f45031500307000c40c4013010000c0e815504161002034016683e500c1c2210100340d00d4020b03110442e426000043c02c3e034440d825410030358090480011a00c10001018028030303425010703248138284141c0d0254641460b040008200d441041c15075080d0343c0028010780d100b6070b12090f825001f0b5070054100c6031001032608c081f589a40c40b44030240410301e0100c444a03c8140568165204150545c41d445001d55440c2ca082c0c0240c0146ca03844081035a503124031a1503456210080e001c01d5085a10038a18036039585c0001d07004014541100030094030850800941d0355800d00051038030001403030320b5003101c65041c01c81c0405903210366001c0320980c00446c201c580c2580c1648507411181c015000c82c0e504940700c80c02d105010b141c0e0703440c051400740441e0040c42300c0c038040c0025100b4404180000107581c4120440039043c0781504603007640c2c1803080300050700c0794030700031503102e0150b501c6030000c00011000403000381c1000485800401d40c014494050020321441d0386c003524000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 360752760 1250 360751510 360751541
    0x192601082805070b220810020d0b0d0804090c0302041a0906041d041505150906180118150605030708060a0b1308010c091d090a050f010902010f0e010507060f 69
    0x319104c0185800340c0d007210700d00f0070303080040c1302100c3d031601143c601000c102c4805501070a4806207030030064001c1d6114810200005072103c0e0111141c3e101d0140500c20a4090045245ca4a080a000f0304c103a80000011408160040c081441050b800c0b901c502e10007159040c205a88051290101c4c07c83e0160350701c0b401d814040407050f51045850390b40c40c01d21907441200c0c02421540d801641c1e0045a4064940800c03002c00404021501e0804010545d0000310081141114080f00c01140d443c004090f04501c101d5150a2000b510115043c09040510f415019210b40054100400103219001c002c104004200000010039403c0d21040d00743e502408a5000c16680d42481b1454219007c62070720138040c00d98039100140d07403564411044501580c01030211454210380c07581c1c01d002c03240c2002d400d07507001303003d054031a40004200300200303014150040004250501d0030300001d0100208a0400c10500102d030585d005035a03840011170380c1541d4007480c000b0751902d4840b0440000c2c094010f80d80300c9c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 360754010 1250 360752760 360752773
    0x1f14010b031e0a1e0c170907180e060105090402060703121506081f0b07030e0f03190b0c040e07030c0c06050108010207060624050708192601082805 65
    0x4400d050b041202c0c04030301041c0d00a03420740d9001071402154681d00d80d03000006d25040c00416004240048030b904445000125142d994031004206010510074450f41c1d00c041c0d6441a00700010070030b03c002030040a0845900c1154a42500420040d00c01d0f858001c01304240f02c4000703181511070354010064a0310002d101c1c02d007aa118a0041e09642003510070a06101c098680600400030034202142a02d402c40141403d1060964050b03500e29402c505031070b4000075008910603291404c1000242c004901c006407065401582840b4503806409806d04040d902d04210611012881e0807550382c00640502e000030303001030a01012030b15400d00d01d40081500c3c4c248000010300da2415006801e509000360f104008581c2c1e40d1101c08078501a0b2076422041c0e5841c6d41552003003502950161240501940d2054a007000c0700080b00f0394a030b002ca51140105c3ea80080c041c50144420107545480e1070500940d110769414000016500c80702850304c1c0210010410490b50b008511030300840724180c3c0a42294003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 360755260 1250 360754010 360754021
    0x4030c08040b0d0b0405040302030904020d0f020d060f0e040506010614120c040501020d0e03060708040804090e030a0305060301022a1006300f020418050f1f14010b031e 74
    0x2040e0701c0064001149070411454219500c1e20341311301b9001c2c6605400462601d50440f05010181d0007003520000c0c1e0961ba81e0640d1449100c9000404884204003400540141005d0341c00382e00401c1500b10040303286500c1c04200000e280020741505650f034905015094401140110f0705a00c01c1c072003000540820030701444404040d81014000f641c40c260266151000c0f000d00403205800e16035001c40e810382c000404200389a010b40351140d0028080c44c0c2e01480d00785c880210340241c0d0303d001540c100e5680001014002c081d4144100e42e080f220440003503280c042c02e05d00d41035401400c024104003c8034041c04425081f481040915000001c0d00001c1c04000c0d5684051107281d401030300c416000448801040204260a4000c07000c1c1c240d02078101c0c01d24084036000e100c01068002d0b40a1803074a40001f2074000b00300100040907420700b440300102402c02d07440c030361009881656044c0c0c0743c005007030031500840c0311960207072181501da24401c40c54603559044484042c4882351403c07002644850f405008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 360756510 1250 360755260 360755279
    0x2404090f020d060c08011e031e0c0305060109050a05040503070204050c0d0e06060907260c13030b15030607020c04150510090305010c0813020105090310051509010f0803070b04030c0804 81
    0x1440301401d62030345040c50387da50074100004040d07030b22030911103403400e4400d000040c44002445044a0100c0c04c8030344c01c0300c1380c1e0f803164503048440d042502d4030703846400100591705190040d1039100300c0500d814030041c14250780b8940d5038000c550000b485a9201d50005580303800410585088140600051111080c1c0e411215140d01d8103503201806030881500051000d0301801d00741c0c1c400c0e441030344140b8600599007030417030308543c0160000c03800c041c04100c114102a111000710005d5800b0b0792181499041c40c0040c60b0058074032042c1e450003600306d001086003070b940105041d41e1001041d20b010034218250003035034011200540000f50311545174180141059070280b440d8050f0b030b21450007008100c0e5100b005a078081c02c100d400b01c00d40c100302c0c81c003000107502c15806000d0b200300281c03c94940842c4206414241c43c1c08031003003c16196080c640341c0080ca4078000a0740101a1400306045850404441d00c1c0c6034820403a01038555020030000c507040503c40e03000400a1908034855644460701c40b440340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 360757760 1250 360756510 360756521
    0xe090c04020a0e01032d090c141c0c090c050405030c0109151409030303070e03120720190603020d060902030907032a030317150f120102091e04052404090f020d06 71
    0x1d42c0e40903400c523404101900c03985146502080000c1035001c02610082003448808801d01080743d41a450540000d9810106e0284d1440c2004c43e80b40c0c1915142014149031600d03150004442c10070010b0b010401c60103d8105411222060f41d150442c0076000b04034a400052048018050701440000200032015503c2441042c0c2c12504030300782c5111881360324103d80b20b4045d0603001f400b1402c0d10b080b4038001c40b100c801c1c21011507901070700b040c0c0d481c3c10411004070304c0e801c070758001e0000c40d07000101103400c541188500009007d01040031411800c2141034503903280010700004100840d0400035090000c001c0c00d6440c0c48404020702c608181d512031070f0043c95200f0381d0b80404504500000420703200b03042c0514100039142c0c041d0240c5085d146032410003007886020b4051072903555080140000036184c2e10450b2001c0059140801505103135281070000b12003009001c0900c00c070b104426000f001003585904901c08900311000700705440d150804500d903000108000758481c1e42880030700204851500f08 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 360759010 1250 360757760 360757763
    0x51f020105070507240f050a050f06100203040e10080601081f0b060a12061a07121e030b0a050a03061b0201050601050706020c070b03010e090c04020a0e01032d09 71
    0x81c001a00e40750415070380d0340100c0708020034103014040708105880b20540c161030980807020000c075540a03070744034843c100c40095480488050b11202000001d0203916916500540d044e11050b4003c620400025100e01841c01400c210040070f60102c4c0c69180010040d001410b51202a160350307507901c3e26003d60b40c004007031415144000c8256944d0009800c1d102c1d010b092840509210319140c0100011508242941003101029a0764007010030f0410240540d4642c00d00300484480d03848505003070404000400045440801801019a004501d049002540404807509011400810210004104031619000540c0044c4101e2001052240c6238000399041c01e05842440701800c85198102d0903a942200c913a030108600700304a4000410550080951141031070036100c2d100d442d104080c000781c0c0280d00094580540c0001c0c805040d4080c0302381c080010085030704501c2c000d4489400b8001700d03030215020341407540d40d549102462a280d45191024881c4080d451907144c942d5062030000c0c60784000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 360760260 1250 360759010 360759013
    0x8070e210303101e0b2d16060e010606021c170703050411030c03030906070c09090605192307030f050a0c020c0a0308041e0902030708041716080a09051f02 68
    0x78008041c1848542c00310540c0c030f05e684404d01c0c05844944441d4000440300b140c40c01c500c40207a034001c035000040c1c0a0b00c0e41c04c002c80710444201c08036050950070780e01078074540004ac1e407424000700031858001540c042403000011400b101003c1580381540d241d10799a0b51005e400b040070003004600d40c1d069014074400c901c51140010080450014140da403118884190b80607802002400501e15100001d030840d00d200340315803000c0c07903114400d502c15036030b2102007119140e40720420300081044801082c1c0c245c0c10300b903a08001c0101d40d0402c200d0400060415000c0c1c100d400030104039440e210750011403078001c0c100c2050019085c50607205004080c160754000050091640f001000c0c508404a03000301d035000b03100642000d04014642000c010b22401900d80131707240b2140040c5268540c000755100b0040d076112402d01d49000d050461120400d80100f410000080100f020a035040f160b003564616041500e4a03200c2c184004191010030385a04415440071504900e01c0c2103441c1e40c019041c0c445920350 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 360761510 1250 360760260 360760289
    0x90201020a050f24040506060111070302280b03040503090d032c01080702070e0103060c0c020a0311041d06040b0403140d060914040201050706050702010b0a090b03010c08070e21030310 81
    0xc641031300c801d0080d980100241c20001c0401c6482d8071801742c884501508130705507800035640b5400601c0503040304945002e00003003107210030400b01200788060014030b104040986149030542c3c460f81c5070300c90003003034a204004592101003418031604003181400054454100422401d00da01c00003141e814803200d0025100100080700107101113085002c0340c41048002c01c0302d07400d40c1d40e0440034144821080040242c100902c202595440079550021401007440e4411107400c41d081c0030684030302c1003440c050b90010891001302c0c05000100300e0307031150704200400b490f902c442c40c0c11140440004038040c07085001088000441125a000340d003280d0303000310200b10f548078201c80710030b01171411100030703011400601490020807242d0f0000c1e64400c409100000e1074002003c0010002c030515080445459500d001400040c00c091265075030f811014109131081d07207000c6070014111030003e8030080c007640c0762400c419124851380140f10000034200c0d0aa94481c0b40c481165020030a0900c1006402c5078074a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 360762760 1250 360761510 360761563
    0x10b010905240705070f060215041e05010e060c091e012c0901090609240b070305040302031c0810030201020303070f0e0d05011a0114030a090201020a050f 68
    0x80c60654101da502030403910b207880c0c000c07442c0c0d5214840b0700320325042c14500300301c4000040c0c0e05001880c05462820a00c11016040080c000d1405402d1840380d940d1001d88000d10021808144411002d0601e4040909a240880c54542e000d0040710b409035070544281400c0c40080c00c01000681081700b070035940c0e5598803004282c031080c10100d800b4598007041400040c038020384540f050107610300e401845215a95041790001c0746c13065009902c500391a03a550300c024000880c0754010103000108003100d001c000018a0380c2c101d9410b68521a90f0f486410028504080500400039200110b80040645940e6540d94108400040c2c4480c1c003100000c903004000340040403074048200590350181d00450965a550409407a07000c2c040a0120521030030240c20340710342d62a41600c0300c0d0700e4400c2c0c0000ca551020b0004280c1e110b004d0400080c107111140002c2501000418181c0e03620100b902c5020440b800030f0300050f0b040200400000c0c10074060030090701d02e0500d0016015002c0800f58024460040c0403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 360764010 1250 360762760 360762767
    0x206060411030609071413080703060e0309010905010302091c0f061d100218030616021c020c0402030c12091501060302090105090f01020321191b0f1e030509010b01 72
    0x844486a202c3d00603804180f6591040c06c1c412040e10151034440d141901105084400170041e900072241940560400e0007082070354055031005082c1d440096003002000030001c0d001c1142c80c061035041550120308818580c0d1101d800d036207201e40e149074065030302b842420a40c2100100c4e020560710b65080500311400990100b0040d40b00c050202c0140142103503506400e80a5403260740b1450078140c1800c24400950350a21140b03000e410000c00000c00940700d500041c0c140f030544d81d010902c004558102c4085550040342c82c01d101ea4040300c0c016501ea851010401c072030f0007040c100c03480c0011140c0c00c221000100040c50107251502190350b80540e03030b992100310160b10070b10442c9400a00207102c0d081080c02d0000301c1200014050050324104010032000040c80c1400d511241d621350b0010041c440d5800d4007000506000070401400e22840c01c1281c589107012030110b001104222840209451151250085204068844290108050341c5240050241c0800e0f510824907501c0c203c4020615800b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 360765260 1250 360764010 360764017
    0x60415090f0605060f04091a040c03020d0f0c0917120a12060902090604090506040f0e1b030f2104031506090513050706050a0c0b10030b0106020f030405130f050103030206060411 78
    0x10345c2c0e04164680341c00c181c0003e0162800803844c1803810664004000315070307a03500070b40d4080c0f00155001070b25402900401c1040e1000d941c3c00d00c00003450100d02c090000e52001195040e101c10500000103070356954071035031810f041c404210500a4003c6815401036078403100c4c03000c000e05800001d215450b180c030009000c82c49501c0d11158007003820041000945440d810841e80904010000200358018101d002c3c141e0390401c02001450f080304004a8001000f45400404140c00f0b0b4010290100880c90f03440d41c0312588485902c004450001242600401000b1240650340c45003124858900e0307159044041e248074010304002d1401d100c0002c0c0d03009440080315807501d401500030401c1d203141640c2619254000c000600403c00221001000304004101070341c01106201001007030176107142403818042c03a046e000b650131074200400640c1f250070000140ca042e0340f01120800440c1107c03000c808010440d01114160301800d01e0000401d040d00841d0f028840c2c80c060341d05010104044820a20510 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 360766510 1250 360765260 360765277
    0xc06050301180b030a0f0302010b10180b122710050a14040c060f09030f080915070b0a0c120c0806010315050105041503021b0318010e18060415090f060506 68
    0xe010550507001b013061000d08500d0140240000030381e02d141c074000b140095001680724008a4068050b103849442c1e0300c60b400004250410183e424495802da107000c200d030015103071a5040c400c518140282032039110001842d50450411145042800018000038050844000b40721030300d86013503803039410225452180724560007040320601ca0309115065640101b8403040030104080004044001a400803442034502d0190065680300c000810400a9032880c03007505102040043c0800e400054060b003803103802c401d140707001090380d80c91250200c640c507445080710308a803070400e541d404c54281c0003040140202e001707a0b13052103403001d40100e0030014001c0344903042c0052800c2104100c0c2010340002768480f103442d450003600e03001c2d98000e000e6100c001c40d005600c03180c00025804144040580040c032060200707007030011040d0102c40020f6012100580447c401d00300010015119684542c06100984168040d420620b516082114010300800754412110ba1410b0404207481c500401944d8145 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 360767760 1250 360766510 360766513
    0xd03020c040f060807080708070803040614031e0f06180112031b05120c01050604110409050601021e010b09090a12050708040b0a0302030609130203071707030c06050301180b03 77
    0xc2030640038040140321521080b442c0b41d0790303010049820041401510014800c0c140101030345400c00c03d0031402c0c80065031250344590f104000411046070014400d0800601d1040d51035103d0360340e81c088041d00c01d40070900c290050038100c1040301c0700001c05800e502400c400e440300c18521a100b282c003c0742c40d000703010312020540300d00c81ca680000d105405805c0607200000d0400050042039540c0e0b807400c1d0015010600503c004114103ca07460240704d0654864021902404500880480d01d1403070720482c012103101c203071518002040d0381d00030010f101c507501d4000c002c41010000d01013918000c1031001d020f244101103010100d0240100012625940d40d003180719542c0c8000c00c1070050358160f100210803a0414000d20000404041e41009000d9603c0e0540740940d507840d000c000c20a0071a80186807a2540d00005c040c0000f6840004800c01920340b52200c005038509864111803a020442d440103181c15000000072500f40e03032140140d41200c4001d46c1113516104110528815600a0328800307805 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 360769010 1250 360767760 360767773
    0x904030e0402070501090507080114070e130b03010b180117011b0e1c0803060405010605070f02010f1205010305010f0c02030406140d0e0d0f020d0c0203030912070f090c08060d0302 79
    0x314901980201010340c400c100024444c18240d031006c0c24015981e00c096140d1350b590405400d1420044c032566070184c1e251030041c002010300000201100250240c00701c100396500c0107081180c60960200303003109801492518a44481698000c80718401d01669070004690581e00703184006c14040c4c1c010124020780d201404e04600d42c0100c51112034001c0855000d5001e00909000b40007110340000d02a001d5081d945d034a03d0a00e00f80010790301c0607400b18040003420801c000124806002d41d01311103909107000c64040320f209508a400766100c6d2a021010f61501c4000002c0000543c040111012841c1d410700c00d2000408080ea01c030300951095a010450348104c80303440e400100020506007181d580300151a16400c0c1906143c0035050741c94101007031103401106111031f010000310b00300b4007080c13415031808160b96008c65105e018000c007150040d401d600f0b545080c40343c10b10560b000360611644800c010341c0d5407501a0044c10318450b1301c0e0081900d05000c90010304000e11202c0110760035400a185 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 360770260 1250 360769010 360769037
    0x5030313051309080c010b180606030a2d0f0636021308010c1205010f140a0923060604050612041103070807031703010f21020415090b090403 62
    0x100c1c06102e91140102d240d6a88641c4000703202a070280546903040400040e032100300c18180002403184880c1e45002036915010010350744d4808040b2a405440d0580c085142c204c020b0300980d03107019043c010f5028010019554003031926981c0560003c0024800c18080180c0da02c10b04483c01500f180100b00740400d140c60742040c1d400010f41d11034411104500103203041c0000c000380d03403a203c0c1c94200c000140d440d0500d0b141e031282d016510b000c800000d15400c1015500d0314a01401c41c820602c18094001d85a00c0240789603628509000003e0010a07002d1003092400b226500000c4040904550111812800b090f424281072095505580e0b0180c901880d1aa894000c1d41c3d80e600020301c01c8552413092a624001900c0c18003468004000007030003010043d01303600e400c08200440c50403090000070180f004014813104880003070121404d05a0161700700c0c0c043c8400c030002e240a00e030007039001030401d4180c2d082c4440381422202249d80d0400200080180b41040003c0c0900544010b030009040710050074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 360771510 1250 360770260 360770269
    0x20a3f0f0510050406020705011b02030a030b03031315080c0a1202071b0905180c151e04060503061f022d010509030702120f1f060b070f0c0503031305 66
    0x110200d0140085030142c84010a0720340a0301c1044804884194000c10340c0010030009001d08010303440e8810707a08810142c0600029940c2c0200007100780bc054a41c000d001d003644007481241c0c4140e0002d8440d04500b91079102030389500c800035455400003003441e000614580110003d64000c816550389028610002030803050107500414020740c3c1405141c40e580307206800302d52041004011400c0c003c0341c2c62820b085000b00100415412511640100b07200890300c1d51140d6050140c0d20a6400c0c050700c603c0071158041d5050103c89080c041c4450001d00450313403641201c09140b01d080e046070100c0702d80400c10a9031400512a01c080c0300035a00100e42111aa2902003038000c2e00107c00850014403141c03501007900395030007a500071400341c00005480055050040070b050048030a07900402d40200440d50160f5900a02440b4000a90210720f0003044082c0a400040041c00e850b100c590f2981d8582c2801300008442c600d0031545030b07407140c1d0001400e08010050b41c00d01944015058412890007043c803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 360772760 1250 360771510 360771533
    0x304080c210d0c0e03031306031503050c12011e06030c0b04060203090f010201150e041406060102030a0f0201060302120d03140603030423030a03050414060f070305090d020a3f 77
    0x1030081c4940028204813030744003040a00098a45070b02c09519075440c2002c064120b500940d4410340c401d19605090010035400105c021070640142ca8080b041030320100040d00503c152525020502040b00b0b613803c000d85550003440c145da0040135000303452580d40041103041e2083d0b100d8007000d600140a00d02c5145091045204c2151045c0004140c001c0c84545d00c4000c0c1c4600d0f007004940804000520051081c1203407461881c1250200800a509003180040d64a000c0c0c014000104464a410039001500c03e4122744000c55000d4401a4071140c9440865100d100040d551b00000346040d82c0310010b040c4100310103004a9026003c0c40ca032904088030350420904102000b40c0b81081442c2013980798504001c4901880e00035942c00b901c031814000d03419513041d40045194880c10043c040c2c3c414490b0b084044400355641828220b50703039900800440e45d801e0504902a52003084c691001a20002c3d81080380a020908514001c0864602051080d03081007451502c0700c1d441d944103807400241d080d0703500c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 360774010 1250 360772760 360772781
    0x80103060504110406090f060b07050c191505070b07020d2001020c030d0510060503040201050a030504150504120f02010513020d031b030e0a060f081f08030304080c210d 74
    0x3070218100d03070803021600340c400070b0b884016200d47d641c2c500383c240c191074410800984411035141d860040240c683d03d0341d400c91681c51601c2080802d5506220480f8000640c0c002c00584200e4141c0c092104ca014005802c41d440c01d40d000708240000070b06585c40880c16240c01c00c100d0302d0740b11040300d1101710005680034080c240d520359135003000030a030007141c2007024101958034001f010989203000c007030603407007091181c2c0300030309004091003407000503a0030000f0394500305160300d0700040507551070a03c81c007a0580b40b05500d0f0102e1400717003800b092041048503200310b00441e0f19803500000841208138229503080340c01c0b121482c0d06448000c0140303010006007210500030310300f442051111114034240401107290440200c2d482d036010300254209480e881c00104460700301402c101c40310b0b9001034807187d4000c0c216480e0380c2d10050180247c0368003120740303000f4083c0c500132030340c49181501d00000b16a01c03803804104a0b200344d00110120045805240d496198070b13584060500e0f88580b040b00140ca4031044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 360775260 1250 360774010 360774023
    0x30307080301030b01030507060804150f09021305070311090f0d0309050a06080601091d13020112020f04180203060d03110c130207170c0a08250c08100c080103060504 73
    0x51900850250400785010314014030f08540340c0e5145241007072420205c6da129209000030300c410032021a44107014405004008640032500b490f0304d4200100500d95000c00a6001e0002441398003c01240d80c4014032072803140c0c60800c43c0550003134103409a4004d820006503c8054000000c0850802c2003003011a6407007801c0000000d5119030002e6440c440e241c010000090011080212540c1d0200d4850001e10080d0003100c212080e0004507030104000501e045030000c102c0c60000c085901c100000f8841d0040320004540b2a00c15440d0894154031512079104070fa866198042c095120620890740190402402c08030100c20342d50b002d80300101c11b804900ba06000e890f5181040d601c4000c024140c3c00c0102000607514680e0703281c00760314036071558885d444000c1e0602281d02c0e41840001c4243c0c0c2950031a12454407240d2124039114100700485600031703544481e030011420005403111030780c250f94881707060300c66011524407448100c400855204000608200041011440f030380e00035038221b8001e80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 360776510 1250 360775260 360775267
    0x150d0213030b09061e0130061503020a08010203010b1b030d050a0c1205070206010b18040c0201020a0f0c020f09070309020411031005010905030d030c0903050a0c030c060302031b03060303 82
    0x40b14101c104000700e442101c1c81d00190300300702150407820102525990a0361010f41107504008124440e110807c4c508200b02c2620b003102032404c1581052010059880700e1305120f9001c2d601c0c020551101c4e40c2c0700c101c0c001c034442003001c40c0d103482c1802a68140c411503482a81024885100e80d04020756003001d5403c9404200000103c0a0749401040e104526600380460352038402c0300028010503550881c880c03140c6c0785c202805176a47e80450507504565410001644410300340c10980c40c0e9195410140341c2c002d1501014422094041d0060104c00b411500c0b43d001900469400341c1c1c41d80c40c00d503c000c1d4021105062400346180110082c2e41165aa24000909924a60100d0215002810401c020cc4408810086880716035010b18020744030038a072055080d8503083c042507954081052600034980c1321918142c00500c504151030003150804102c5521050350308001440060501058401c00110303103000c1041806802282d018600380c07011210b2145070465444c03011b0704043c041c01d503d0300041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 360777760 1250 360776510 360776513
    0x3040c080105011d0a090b04020f1801080a0b0108152d070903150903021c030e0a0305070b0109020f0703030f060f0b031801050402030a260408100b150d021303 70
    0xd21030b07103000e094407a641c1c0c0141a807220350b8110740d40000304155901400c01900b42c0010704412545600b1581c15100190305074002d1000501500f1807481d01010310000c40300015000a000941c2581c00e8000e454100042e42c0711407046031100c08030707030703550340202803141c04104606000d2507401c40c0800c0125034042100d000c0e000501a04105549450009611204c103209100c00c003109850168105882080070701c0c0c1c00e5402039194010b1140c1c0d6508007000b84529a030250003030300b080320080903000c02d46064200a24002d84540c100460039159607a006002207400c01c8a03200701c86506130268286c2d03003884056070301200035203800750087c0d80c0c0e180c850500190f800c280c08005006014600d1a80d902da10b00441240d000c0c50060303d0b00c40c030b541e041c0428070003d600c002c520b01c0b592641284035202c0001c1403003110f44507281c0960500d01380c00b4002030006810b450200700d0040e0110540414405021864100139030701581c2d1070030240c0241c0820518000103a9a4010410821039640483e41d03130b9501d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 360779010 1250 360777760 360777763
    0x30a052104261c0c03051b0303011d01120201080a0c020c100309031106070917031c0f0b030d022a060c0604051203040f03050a210b030c010c0506060603040c08 70
    0x485510182d115400e60021549070000c2c406014102d002c0700c0f203070340600041c9900620100410101030f040c81800116012070354009800114640401c4c02241e44d00d50f541e030496580c080003894512460a00100040340101c8030912641c010344d0165200d035440e446900c2c80340020302c1c0741010b12080d880340c42c40c01091078580e08007510b81c5101d2510001040d0b4907a05010704018031154013814541c01c81810080381c1501b081310070301079820307003400c0c460b1200ca580e114a18510641d084050005c04180902420b515103400405100410364000c0c003c00700c8690a142d83d4101022100c0c0240c0c00010f40551103001c511807048907480700c40303550b582031207030f00b40490610750041c0c0902c0490740000c02000140f11040202901c009641c0310300d2803840c0f40c072fa250b07000c031114000b400400300480054000300c0c10780b0412134005800c203150780e403000e201c011040040041901d10340c610700030300955440c8000c1d98060300c840044190820b02a0425584001c1003000c90b40c4000c0040341c111032030b1403010824160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 360780260 1250 360779010 360779039
    0xe03070803131e03111201090c03060b060712081308070c03060605100507020f0d02060d050403030f110d0b120f010f06092702041b02030403020f030a052104 69
    0x8000d0051030b40e8426040d048040a0980d0300f19880d150310f240101002c0c0c10075540d000f003c03207410007101c0780729560500c0081c01e40650880004000d41c2480494020300c0300020032001160305c036100800018990f141480072034007849030090016900c10450440840c0504542a030042e0403409140b000c103040d40d9104c0d03031500004130548803203c40c02e501313108100062141340e0240904481c2c50203407481c01c00e80184580300c0d5540081c015090304c240201c164540044000e020395008013880d0b140c0d4212509035000340800c50302500024200051a060b011071441810820450001203d05c0c11041842000140c02c0d0350300981d40007a40e00380c3d03400c0007907402d01541c0c8040c4091000418400507540a1405941d00e64000c14801490800380080807a1088501c0b0741101011095410401c29800054000e1450060182100d01c1c0650001402a4040000c0003528401c460218101c940c100615542e00c400140042085d4040e50440382020440d8825001112903c0401850180c035070000c03011100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 360781510 1250 360780260 360780269
    0x111070803040b01060201060e0106180f030302010209040b01030c0e0f3c010905130f1b050a180510050304060906140103050607030e06060409050106090c02150c030903090603070e0307 81
    0x4030302106100c01c21078103580c15801459940300074800c440c10005e2410440c0010303c540c0c0288690000c1c1e02d203042c00300307161020040c0414855240910350b00c1c00c1c0a8003035070219001da4815844c000c08081198003a01c0b03000b240401664a1205020344181448144840300d800389600090200c031400c2a11030050300c03141100090200344441201c6001e000c6aa02c03c0d6004c0ea9050020300703601405030b0f032180d0006a82014910101013100b00c0e084203400010100300403140d4024021426180b203184c0c00c400100620111680e85d8003480250700402107001009028995001d000b10701071340744451091001d91341250090200050f81c1006645050071a02090420b5194120700e40040080c0b25040c490036610903170b2810103002c0d246910710b0440e01c98800400242c810742c4e44491030014880c0c00d501407005000c3d446810412400f50042c080d507034030b042c01d410a20300b0807101300094007039140606803030140800714015400c3c0030068003013050940009100c90108102c2908010859404000300710040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 360782760 1250 360781510 360781523
    0xd03050c01020f071e050a080702011b0302010c0908030c030409022b1a0105090a091505040f0213120c030f15140403030b0a030506060609042c070f140d05011107 71
    0x1c1c0c0c07940ca03207010041206840103405c2c502d40072007000031800100394081c005601c000c02c80d0340c80d9040d20040c0d03800c1106414500601c0e4044d03c400e400c0640560000b02074541a844146100385c0c0d820344103650307104010fa65100380d00184000c000c03072441c5070013a040c0c1603141154404501003081c0a00450207800b24012907094480001500325400c0301114040d064081c80c00519101000c00411030000d000d01c2014030040ea41c0b52a000b01d200d11048840103010010700502c000780d224a9140080d402050320014210b101d00307400105440d84041c090360030b96000300e405a0b45851038440105030b207030b05082590b00900e4584040d0790310308107104018a521180f40030703810508040c09c0c02011607607080c51341c60141420500c2440407600002c0c010340d000f402200e00c5666960354601180203001450303200380203840741c15903e01045105000070f003400c019400481b50482d59842c0c914500d030707066203d0074000c0500340421600900b413504011400c83d0189001140d8840c520402d849164050101500c1d031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 360784010 1250 360782760 360782767
    0x120c0c0d150c14030609190e011b020a03090b03060f1206090d050f04120f02041404030f090b0f090312040807050414060f10020f010c0503181b0d03050c01020f 70
    0x15049114088a002c554030300301030480c0c1910400200d0748000340c0224402c2c00007070005a85106d00d08161a80210f034140c06200c406440000507019104240d00c0040a54803201600c40d818800a086442150155602c040d880e00d85041da500c81c1d8405442a5044010072502c0e0b0f01a03255168414403501c0747e00020715052901031039075414442d0036280340c2c0811400f0001c8902c185011020340d001d840f51016000300003006850009906032070f10700000c0d000340c200400a0820401030700c00e80d01c61402600c030380c1b04c0c3d1410480c04540d0080a80913441c0030400501814803030140040180001241c05801c40d142c0c6030080d40e0581c010f07001640a0701055100074018405401d25020ba030394049075403181502541004000901d2400140390402d02654030000d0f4092401c0c0308000ea40c8440e03085c1d034000c01030361074000c02c010001d40c001c030703903600d00721816041d40b43d00d05034000f07000c0c1c08581207084080c2c0b0f10442c02040051840c0841811381c10842d060010306215030080c8003d001c049403c1a03030564 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 360785260 1250 360784010 360784043
    0x40804030b060d0c1a090414010e0f041203051815010503010e0a050307020105030c2b0c0e030a11010306170a02010e010206070c02010509042904050a090203120c0c0d 73
    0x415800070300490150007408039401c0002c50303882100007030750182c0301559685940d602005c1c3c4c00d400f51038000313075105040c060360311000d5450203543c90680c0e02c8882042034503a00c803014a07900c000150340040c405010700d0004e094051003540b00a40126074280d21200000c9101c12061500e0381450011541c80d00400040103603240034414202d101000802130300e0050140d842d82c030f440303004a0002034141314001000070300b6a07010310200c460010740254200c2070a000c3c0300c580b0b10018003040700c081e28903290411040e0254041c9030200e004601c0103000b40000203aa6691041d50300b82440d445042c591203103000b19039070640c00c501c0684200c44c0320043c549015240001469849181c0000741950003580900003415401513560b00000d03020700b050741e40c42d05084040b400a181558028038a01e14101c00020040003419100541e06011074051010344c44400c2035200321103000302e00a60691040c0d8140d2131901000303010b04001480841500c0f181103105002c01ca04084000c0b0440344543c06106248 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 360786510 1250 360785260 360785273
    0x1020a0909150f140a05030a050708060a110712030b120a050d110d0e19080c04050105030f0d32030907090506010e040902030115061107050d030c080c0a02030604080403 74
    0x1141155501110702c4024540024204000b019000700d01d06000854200384050310b407810b625000b40005030490301d06181d00d04105894850600400905004c1c002c04030303100c018103008840030501100750013032505c04160394582c480541e401526040c19181c80519517281c0d03d85540102d04850100500040c17a181d00d016814906c020b243c80051240c40ca480f403603061000202140c1c01941400e03c10100f8000350001540c2e1458612842e9501541c420081042c100107d420300081009a80500c11a40c0f56003c0584840d01e00f0404141030740203c04001c08544288507070b40da01c0c200075900c801b007514000300307072048070000d1540c0311142030002050003240700081101d1002000348040400c0581001d40000b04481c2c22220034030320540c0c03900c41c01d409568003035220f003140700003000c2008159a500c02018000d14145440d1a07058029140000b846003496560610000d5059036140241d0390982e44602040c2c12003c000b50940c030a9200650058408020007805180500c0400751078610350b28061 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 360787760 1250 360786510 360786521
    0x9020c0a06061e151106042102070b0a0e0103090f030527010c020d03030e010c11010b060c0601050913290105030d0c14010209030102041508010b03010608040809060c01020a0909 78
    0x941412411500880c030f425802900f41522148580b60b080100d04803000c444024000b207841145014900130300042040c0c9960140500c101e02c0d0811100003a02032041c4d031203564034411210301620070001f8040c494811140d0340300d02c0c00141000120340700603840d0580300418106044012500002d5201619500c5204846030700d04d031004103800744552400001c050209080000303001c0d1103004184001c06000360060610040c2884c003c02c450364059000900000c40400c07104440c0d40380c554801c0035405c09004480b61101c00d107000b000c0507440d00041c4120300342c00074442601e1030349600c02600020800c030b108a03d4034500040c4101c1850809420500c601e8040e40494441e0340000c0c1c230409896040307000c1c02c0c078180d001582030364801d8140101c140644102c8005030340c0741d403002401040e14000742d50410b01d16550740e551403425030780301c035001c40d17440c13000380103000200e0121070018000171609802410210b001500c2142024082d104050980e0403003c114004a544081c0500a40c699032040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 360789010 1250 360787760 360787769
    0x2121c051312030504081b30030c0304060219050406030501120510150f030b0103050607020105070818030906030109021e09100e030111070b040308150109150909020c0a0606 76
    0x20440c80ca01d5554a48140d201d0204050515840e80002400d106000d416a401c88480340c944400340b0a03a540741c281c80d200780441d41c21420603113000e0b0f446104041d04648584d003000703201403440c584503c07910301c90540000b0021240141c00b040f42800b2280c1c04290021000d03070603103c143c0c07150f040400c081c0648005800041100400d10b4101d00400c10000700341c0e1141a90001c0015140001442110f81140036001001c1149490200204000141500504030f900500580d22503440d100412400daa9007500c034600062a4000410407080c0c05014034140307060210200d070b1620b40180e01146603600700b64850070805901184540441032911819006a100c01041c546011200800a4080c2c0440040d04042084800030b009036034900758000000c03102c0e40120180c88048030306c0d11440d859000c5504a0001d81000b01123018521643c51400c00d085050b118108281e0034458002c28070200d00c0c400c181002182500011842c049100800c4150740590140801040d40d040190030b07034680c0e910 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 360790260 1250 360789010 360789031
    0x13090c0905070201150306090c0e0c0c0111070209010302090709030b0f18070308040620010e0319080613020f090d12140304020d020607080408010f02070b010e060d0b0702121c05 78
    0x1c0340c5010b05c01000c2e180660b80d0040000410301514203003c1d070320744500d41107200e804511701d0038008010308880190410b0b4580384000e10061606100e002d100e405048002504101100010f100600d04014a540d011f44c0ca0300d00340704136550b0ba85401420314802d0f1a4110386e16030709010703c01e50000c0311810308001e0484030700804041c1e14654540115204a11600302000210070f808414002c1c1e112154407a806500001d1111038503103207880c0e0322170340b081860207400c103450301140c541d503030140c1099481810020506444540b40f62500b0010f51f1045c00c0c44c105009080006c2e29583d59002d00320300b4040d004e41c01403000381020300005400542e413040343c1e40b11203400303104020069aa0351004604558159a03090710761000e440c140425014541000d803141d420824000c80c1006540d01038102680034400701c5640d640e80307449490700c064060ba40d243d00800c503c4000000b05000151058200b611441200c04403c00c0304240e250a800c80503007981c803800f40701c031010140300fa54010944c00031144035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 360791366 1106 360790260 360790271
    0x2060c0a021e030d060e1302040506060c0607091e082802061c05060901050319020141031e04030e04061202030715020c0d0213090c0905070201 63
    0x181c9001003030345040c000080c44a004480540645c42d4102c3d11002c902080e004d101c06010010038036034000e0b10070400450f0607041001400d10680c020b4350750958840c100744180001c0f00d0391124000b00c08000d084148030b048004101d900403540d5500d0624402c0c480b441d009030140e036842101942c42000445d450040d510902c0c2c0314482d44540207820011907840e0801c0040503c000e004035901640b000000c000c01c00709100541041900505100b40d40c903511812040c0004082480c40851540c101d1042d500c8140c2900c084100000ca091075504528080004082c1e084044404c02000451140481c1c2070602071110b004116001920500195803110000b48601e9441c4c80128000d00c284000022007503202c843c0c542c441039469001c1c0071381e000c150b0104014900c41001c241c4e0300c9aa11040188401c58500c240401c0e503101d001c1031f003484c43ca0052401c0441d20f0003002c0382c09590516 = true := by decide +kernel

theorem cover : BRFrame.Cov 360611510 360791366 := by
  have h0 := BRFrame.cov_init 360611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 360611510 ≤ n) (h2 : n < 360791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
