-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0877
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:21:36.951569+00:00
-- url     : https://prove2.me/submissions/8651d001-7368-4449-818b-6ba2cd6ecd67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 157553956 ≤ n < 157733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 157555206 1250 157553956 157553987
    0xe130203040b070e010512061003020d051807091404021302120c0909010504050103080a030e01020c240a06050d0b04060f090803060405090f0304090f06150203030703060603020403020f04020304050f06070c0201 92
    0x502d40b090580b018a543d10003c8d01c4140521140580c000c0f201d4400ea040c0c0e100d2100e0808c0a11150405001d01040f0041412140d15940039960000420000c1885180b03084159010000c1c00c9a5440d020081018004014011469001c11221442e01a041d080074400d00c2c00d0190a501d4a81d072005001c20040140c10060280e0328100040c0041340841c015540f400c800ca01c0e02041040c82c0302166406401072990480c07003032050510708400f114082160061031705034018141400d82d1102c0943c001e82d0050300c1015003100c400c84a0030041000300c0017056100c1c0c006c440c0070032189282c05400088404000c0103480a580202c2030111520709070184070b40100e000340041500741000109503881e8416445400100d59403030880b4510b40415130020401841c8070564140554800c050203500d0f6481140c01c240040d140c400c0100b4028013900c00e072025250040c2c650562800d0304810b000085d407000d030059074144a007001c0007070340803010020b4501c02c0c81c0070759800c0042c4403240b00152a80242e10340d002d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 157556456 1250 157555206 157555217
    0x405060103061107030507080c01240503100c1b030e0d11040e0601080d03021819030b0a020f040909061d010204060e0301020f0d090804090c0305011505120402010e130203040b070e01 80
    0x400481d5006d0281c501582e0403505031582d03080c0c40340040d0700621900d10501661580e4000c00b40704101603046442c02c5400036015aa202c40e03a6925050813104000080d101103116100240b0030180b0111400c0c200d03610a0a00e40020410705001698082d1518411102001007441403c62400c0c00c1c000c0c1c8481644141c020482941401c001da81c48540361280541096404100d070200f000002c981a07200c250081c1182d07056610075192108041c1c15404140c401c0510503000c58200c4855100f110950020039030240d0a05041010305000383c25060010b44690307845004400052143c0010600090402000103960710300e04180500440d600000700c903c04c0e44140600d00d11003030904100c2d00448034150f800100c000c114901030340700380101d0700480350180c030341541040c501e40c141d404141a50040c2c1c01025903c1c043c040105c03440d125080100511045213130103d0019402180140100c01c00104986454000b00700141c040b03070005c0b41c09441c0c4881c82010312821a410150755100c0c04828600f2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 157557706 1250 157556456 157556467
    0xe04020703090e0a14010b07110307060f08070905060d0c1b0803040807020102070b0a080a0501050f060d0e011e0b0f2403040303090609030c02090f071b08040e04050601030611 77
    0x60300d0140e0703503c914025078806038000341d100507040d44031300c03030841c80c1c5130000c1d486507121140d101d100d41103540216081010f84c1c1c02c04800e4603001a000c412528a551092400704110394210384059014141c50305000c90b811021801d80e0340e4501074903100b4032840000a0481e4842d80c01401c00c0074603503a5a9010920740c4c032010100305941c0840381e205400104550f90f5007010320040b8a48969603000070415000403a006507000d03449034420b4052448040c044c065030740c80e003041000d59030b0901403544e4003602c100415240315400740c00200110400d03000008074412106820410044010265401681d48558a040758030b0310005085d84c030441903545440c160a001d4500c007140c1c404202003102c80c41c004c0b000030b080502c6504a844c130f580e88036000b07000d810649d10300a0b12803043e00c50128850071102002611340c01004080521440b0541c0d00e07036040000b4039203800c2003d1007082081c1c07807010741004045070668105003c580101d104000030101507240d4105841121051942802c1d4200c04011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 157558956 1250 157557706 157557713
    0x3190c0e01050c0a0b18060601020d0e1903050d090f08240a11040f0e1321051201030c0e010f05030304150309060501060e18010e130c03150504030e040207 68
    0x405818030207080c03480d82c4a1541c600c407032802090b03070700042034407518208000c242024031503104c0e00000d0032130488510780c4442d001a0b03100c40e85800343c0c6001400311a41c2d41001c0c981303051072610070b410180c44000f0f100d0f02c0e500d800e030802c001001004040382e51100304020401d41c0340c441200810914020707180100d514240320b040c0b40481141c5089180052001c101340760007a5101d9210948071150131a5501d54420500302c00284610811103400e481100050407001100c24001c482039000400000b80039180288002100047c1644002c1081c180210f0f41e0b005210072810380618001e0754168080c92510754bc0000d910b80503041107011010340361040011b0740380003080d20705440c02d0030900000c1c0c120b00c000850003018a5080a403000f805c240c0001210b540080c1c0300d0f200b6040c02d4512401d40302011242d803001a001384591f100b206140000030740d141d6040801c005046100d4070741c4144081d035a450b0380c04140707440b0f1701c1450090742c2d90040c8010140c0000303d20f083d440090b9403d60800d120f90300c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 157560206 1250 157558956 157558967
    0xc07060f120b090a024006050a090b0c07120f0b01080d050a12110a03061505090f090403030209060705010c0207150806090a060b07060501030c122303070c03030503190c 74
    0x13004c0402280e00405c1c014034040416041c001d9402c0384070121204414100c03011044481485103424001c45d00c0c039004034a40307108a0440d440c50f0100c2d110440c8041c60210381c0c507440e501c50045000c1e20300551a001c55404068034244a42e2409890814051341950401c00e42e8800181d0107886550310071024140840e80080584040004908003912800d0b02c04900304042c10705901d180c8540c9500040350154290194040d03001c1d6107110105150340034540c0f1081c0d4052284100701c59000c0d1040700d244480d45005009103a00a01c64a405401d2081c01404a09660400a412180d59454502d6150156410092480201000341880d25245181e0102410020014011314003804165000400748621038004900074503d00000e56505e40c01070802c140204803e003c111039400d84800001640010001c0d820400303900580c2c015a41400c140042d130842c01d60000c00e130047c2c0030500c00100400d4803845000000c40c082d885040d560329040120a02e00401a02e848001c145480502f82c070382c2da4482c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 157561456 1250 157560206 157560211
    0x30c09040f0b070e06070b090c0f0102031b07090203040c08011406010e010806190f050f06040506090d0f170301030605070c0c050d0212030f0c07090612020f04020c07060f120b09 78
    0x442c0254450301c1d1050704a0324015016401c5410800009042c800c002c18818000c0c031501e40320081d00c40800d2880100006d4400e00c40030036005a00031300c000d882e01c04d039100c00701c086000101c04541c500c55039103240e101aa0011a0141d41c1607980010810603c80e081c054141c0d1580c003904200382c07500e8a0000a441c058100c0b94045c1004690780001d0380544030450b800703984c5020445894a180d27a240a00030b40840e040c0207407030003101c80c0c0150183d98100001aa001e480c0001c01e0681400c4429090020080c049002070f07900301c1070066001c1c0462114610440290680c4c50141d60f00c0d03041d420400184c410242c044010012110703d10008500420207150a84108803010300c0c0d8200340380000750304a42103100d100b4150000280c00300d044501035008107508644081a60701c9039a0710b003000c0c422101c07280700e455a5000d100b44047d005190415000405040c024001401c0c1006d20385501d21f416215040b4401254144050044054114104881d020140d038410302501a075400480c00780d4101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 157562706 1250 157561456 157561463
    0xb070f1205090f0109051b060c0d030b0d06020a0302030103020108070507150507020f0709090203060105030f0c0405060d05190606050d0807110604050d080301051807020303270a11030c09040f 84
    0x221004203142620902240341c0f09100840244810049410b015407500c41c40c03441d2114022202800b1085410401c0594820001041c058940000080030640c054400090425030040d4416144400100c461024060440035a42c0c0140c5a40c110310001d440c3c034901904103801d002040c0a003400041554001441810007648082141e4031a4074003a4500000c0d21902e00701801000c0002c0790048207580301c0529180224116103a590703031002850340300c5080800707242c411380080700104940e00705600400c2e0041806820080300f40b00d01d0300c40b1400e0208084001c20701c4400c01850805108260041e4000390000b11034141e026290343d51041c219110301d0000800940d40c061281c0107075039686081c0c40050402501c00140c9480c24544820302ea80240242e80c4500b20306403050703030000c9a225000f4441c40641d001586503841c1c00c4800d501c4580103c482100c030b01c032442680511034500340310a541507445100c004181d0b0702000201400c0010f280b1000d0300442c2c20b4800c11000c5207641c504c1d017000c15017 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 157563956 1250 157562706 157562711
    0x2060a18030c1112240f07030e070e0f0907090c0e01030f090206040b0403120801060f111204090b01110c091306090507030308090c0d1203020a030f06080106030b070f12 74
    0x10501c0d000a80240743d40d40258401e07074500b0f100900306030109020759214078072107880070009001c1d180c9031403e66059449080d0a1000e40004000710300a50050009034080001c44c1c00c05079a41c0e0044131f07060320454442c0409007100090281107042004100003900c060b00e414411095920001450102c21004075070415071243c60205008801d03500200c951900500501e50b540d4958181e00400d512500c4101c490306151200861854841d000190580304541d440d2404066000f400701c0d40410b00300740d618000e01030314240c02c00c03581900c0c00900080a0070f84011a4241100001400307400207090b40c41d90f280c1224407000d4a03542c1b152161b0380e108909a0381e994008240e4202a0300601c50107200800b03501c5a4070000c42071581201ca4144110035000880340e00e00749040c11712070190341c1594020500c0340003240242e141c0303020360064806c0b0110b92400050080800510105030341c400d42c00710381681d54518051003400011041c1540c00881414140d00181004078020080744805589103503169 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 157565206 1250 157563956 157563977
    0xb03040c061d1e19120b070903080313030e091f0801050903030105060a0228020a0b07020d03050306012604020103060614030a0c030605061210050d030c1509080a0305010602060a1803 80
    0x91342d44680c0c40b0f038140140c040c54521529103130080600054400256064071468001406251043c84d607a8203881c1e004806900710f444400c0d48108225404000700c09014904001c011641c540500244c402e881c00f0904000c424840703c0302c51a00c10658021410b0303641401e0030032810207400012681140e005071980c990700e10500c0c40490130180c0b030008060507450402d1400d800d6065146170792840380d00845a00030741d6503981000c42d6452090784002900213456407048070100e80220302465200006050500c1410a0340041c2802021502c008048050b82e0300240002c0d540e05110b000c01030321003409c1000c4181c1240c065040140002401d018680746ca9407000012140b00340c0100c4010000500ba0341d84444103045148203d010403130b405000d84058200003c1d01d4a895030120601c1038142c2c440850000140e290a564241d4100c640c1814a888500210004d00d181004000c0500180d400017015414100020708042e0050541c42c0014200302c7c01919500c40340c4020340307074507902d07003001340084 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 157566456 1250 157565206 157565209
    0x90f010e0316060f0306030b060409030e0a030b010305120403020a290a0201050a0e070501050f0c15042004050103112103030c0408070e01030f0b0c040b03040c061d1e 73
    0x614403080d4503014051000820201c5a00d44001c10555440b62103505558407211001c60842c1c00500c000341030480d611002c1007150920b075000b1310b80c86010b8500300c50b00000500109881c035505500807143d00c8822001041442030034802c46070080c18007070030305207003d203103800141ca203035014000d103640b03614a0080032521a02c41c0014849014510744619214000e0907006030090908039109d41c11103080641c2c40b10080008504203090f00c2d0141c485c141090102d1110030100e8108202c000418401e150f00e00f00013403071000c8428459803088005100303d405100410000444030f0313002c0740c021030030300005000103255007070162403c010981c2e00f80001d1111400b400680c20191201d09000d000010500c034000e4a03e800800941d51440100d480540e5903440d4604062403d110140440e01040c0070700c0005422000303010b8200c064400c0031803c01d0307120b84101c1000d500603181150061041c1800b00140303500b101200741040142184844076090901c045031204455000080350000c0c0b140d144036a9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 157567706 1250 157566456 157566467
    0x3071502010e0d030b090a0e100f0603080f0913050105100f05160b06030106061107050d0f0b070512010803031501080702120f0307090e04050a081e0d0906110708090f01 74
    0x40304a110704440c81001511000340045c440401414011104803001440404036400f4070081c4209020050031052429007100c401001e080302294050b68075100300001040012014041e20402e44400c03d50703503002c07881008174403c0c5000c08070321564148801000319940d5504070304103500d4035092515610480243c1220a48284100c408800451410380c1c0140070011445a124031015002008034035114501034400c000030203da01c1d6254071030f40040c801420030108403e0700b81d00c02e880d80d14550038240d0f80d2002c00c2c5021511100080d00101e8103400300c5041a034094010710f5154045c51543c01c20a201c01c412005991f00341d0f050044e4038022560881c4200807800105c2c440b00051511610740181d6100c0c1a402501c4590004070400b0004c5205800c0200b200d0050703610400070600c24038a41c1c1c410f5a2a00084041e2030310f0345202e2407607a02c0707204c000c00600407454028000109911031740b0b80202118000c40c100f80d14080306210010003d00752508407601e00d003088a0345583c2c11680d00c0122107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 157568956 1250 157567706 157567721
    0x504090303060e0901051b042706080f01020702030c0616020f0a09140402040f0506061b12040810050a06140603040206041a0d05061f18050301020a0906080a0b0307150201 75
    0x800f01e0709800304000c814045d4001d81c0105a88400281380016601c6513090740e0041d802140340f0100010b220302c0140d004102980c0c9401890000030170b4040d9a044014200018010800400d940000d1004214582800501d8107020200d07021800c0002401c2540500080000028010102e10749003032402d070740380340c2e2200050005810a02201c003041c203104921300e1098038100d00403410b01c2c0440d6003800b002e01a292041d81e01800540c01c001e500e48081901d804900ca0fa04028014011910028240e000003007003d0400d0300e004054400205100d0011640001c2003003418924009051190000700c103000c54aa80701110a180c0b0703503e0700d0001070000c5c4110390080c646c1c4c0101290f20070030001100c001d414080c509000420142d42c0b500c05100001500807240e00451040700d0390030841901030518400c80c1c0f0481c04803549000e0300c400c082400ca13484003c120020410300c0004001d015407102c10a82c3c1300720044424401707c04000c000c660b03103120342c0c0155008200c02c100100c11342c0d4401d40c8900c1d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 157570206 1250 157568956 157568969
    0xc17120a02030a0305060a05090f151005070210030c1d01090f0905041401050c12042901210203030403060b03150f040209070c030c02040510050d1b061404050409030306 74
    0x9548890141010b0750725403004590802007414040011107a00e8060300c100100d520181c00220260780d10303110300d409810000c0000750030341c10826108099848002044030361111340e46406a4403441c9004002c00b030703503105008808041c103000c03503510041d40c047c20100c2d07444103000130008034a6480c030068880d0011508440160402e004000036840203d42200d4012405802c41c1030312502d0400300c8500340c4204407030090b90303030070200f0000760101104c4480ca42d0080c09540404140c0d660b4088c501408488a031100b40d212845400512060400b00c107008001d0141e14035610352441d00341d000c02d840c0c2c09544005003c0540d141261140c90b10280424103199580c1c10b408040307450100c5c00d6000e4010180c4041e8040e0020000140e00180515030072036040d46c2545604800c200550700701f02c060800201410b01c90441603800141c2500c40752242c00f0b00901c541c0c180c0c02c50b004802160b01212100d61301600401805003103031542d00c10210304841c16240283c60100d41c0382d143d42410ba002d09169800741 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 157571456 1250 157570206 157570243
    0x513020403050f01020301031707050a020f0f030604060b0901140a0902071b030602070308061813020609120c090f04020907080603120f0d0606090f0e090c0604080a0b0f040c17 77
    0x8055842045d4002d50607030703215000c0c42d0b4000724a03112409550003031b054000c102d03911140a09001d4505442c120844602c02402e20790754440d0307040400c1c182081134a0465255403140f540501900c4c1249009025201e00306603a9111044500011700c00303075681c03260000c0302c1e40c00a043c03c284150414100300e200d404c0309100d05070554a1800d2002035000600640025102c100400d100303141c60001141000d10380444400c141d203600310340d0b0400644e5080b00305d9109070200040d103c691582010b043c1100b03200009011040070100c01e10440890080c40e01d98801c0540c02040b006982d101a0683c00c049a480e11020680d10000403d2500004034840080c50002280b00f0f0000e00781100204010829404107001050b80d0341805d075180e0b000c501400080080d558000e010704601382d42d004d640200c1040071500d1544031100410242e071b100ba04888507540000703058405110000750700940005040a03180e0442c5080d0302c074440002c0d01f6014940094404001801090070100910400110781a030701 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 157572706 1250 157571456 157571473
    0xd081302030d080a0f0624230c0601090c080c0a020a0515070f09060e06090d0b04060903090608070915110111030106120b0303180105040b07050a0201031410051302040305 75
    0x3800403c0c1c11584d0780c3c10310b41006030410403007519028500c103c030381c1e2051344864005048a84c20700e0748a04007040b41001040d0350102c054207440100e070840c1202c64080b20713554556855405042c850160032040240d803c4c40c1981041e1a4840c3c1400e62002020f80c00544a204a5200700d06050102401800501c100d07581c4c80c0c141d1540050060246131581c443c010320110f052030079a204015031040300003280c0700480400950600100074031004e203004092807da114141d5885041e100c05580c1a224295501e21032401c00d40c00c8001203001d0201818000d203a8508980c0082c500c00b401d0266020801d071401c0712403070032401054400014850b81d0024031003c402c8102d00d00391904244244800119802034441594540f886900e01d000e1007d406503107048401c03807141c500050003044640c1044010800040c583c030b00c0401034800d00d441000505224125400018252910a80d03185600c0605000f800b00011100f2041821208107950070f0400611250034800240151b610140280c05000744 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 157573956 1250 157572706 157572733
    0x30c130e15220222060f17160f030b15090102060f040c0b071110080405010c180e090309030f0a051b0303071403090a030c03120504080601090213030f030f120506030d08130203 77
    0x1c003100310701b11594459078a03003640380d82405041c40a858110085811ba01c0d810801d520618200d0030805281c200464119140f10114000c0400c14064240300c2e00003180350398466a040c020b40741c00800c0240f140c2d40f1818607440e4842090007078402c0d202107020004112003003010b00c018420003140001c103559841e40404001403c3c1810444044410354030782000090164054200e10340209034080b026101941031100c1e06802041c0a4000b00891105000c20f403103550f01000504110840d4101030850b400c03c91400520704485010600c10401088102c143d02e0344000060350903a0b07801c483c00c01a800b1451518a00f1481a0120203030450b0700c1540110501c0005001c0030200d07881812000000d03694210f085030980600d01403400c00303401010042202c08415000341c40521048200f1082c490b5403682da1400e80e01140c0c0c000c40104104400c1040055000300111004070030420003030105180140003c0d0f04d03800c00104145c2445040c1011411a200c07100c90316102030303800380413200d1490050f40c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 157575206 1250 157573956 157573967
    0x1801060b0d0516090b0904090515010b0c160506070b13020415031e11190503010f060602010b030c09071b0c08010b10020d14030c130e1522022206 64
    0x851100038910007000415140c4d114041c03d20440c0c22000d0618144039111081001078154800c080e60244910070300400d0b41441b42502c1e50085c800441c4c001e039a4900120300034101507009a070300d143c500c07801030104603a03200c8074101c82d039046c2d00401038011a0740e05101d078000341800c0c3d04080e4205261036000303414002002862000e91713020b000441020608074a400e004407160000c0103000b8800c4a04601413800d1a40400006901e08000200642d44500200e421142070b01c480c069040e4032010b08000181d020311460100c4442030b03000d00b80740304195003c00c50920000d8410004c110000d10348590444101154410041d4407058442c02c0303940d41c034403550203442040302c003d2141954034018844c040c00010410710824503078941c0d00301c2c81c074030312040505500014002c80411908001a0348441c201d0046100a0080181010110708011059000050744060f00c1801003291811501140310303241010001c1c00151900540d4610107038039095078500c64680d5116444c403000c1000300740300da01314 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 157576456 1250 157575206 157575211
    0x14030916030c1706010b07110303070807050106090c0509090c0906040308070812010f080d0c02130207060c08010506180d0201030b030a0501060303030f0b011b110312040503120309061801060b0d05 86
    0xb20f80c036003040d0300d0014103d80c4540080c03060b40c24002080006000040c0110070001c0030384401802d807410804191100720441e408400105c3d42a5907030102403242160f107208010b80401d80e480c1843c1130041680220348044009805082d01103004a4038062554822007190701031948440c419032242d00d24170703100c0100e420081002d000b141100e00007254074240300c8078030801c07914941300401140540d220700307840161075000e0a0340c12494142844044040c14002407400038410900040c5094514100034000c0d074060f04014450181000044c0000b0740ca56101d400c00801214800c15584440c80142c0040480402d000d0705800340681c681d09001041d4030650440703001c2d403011302075402810005021a481003003074902007007040764a24418181410554401480740340c035498185108000a0714008411013400c2900c9030004060003a400c00b40001d0442045d02c09042d82141410451151111801050100c4200f0000d40702d2401000075000480104100f504143e5107203091040304000e04004c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 157577706 1250 157576456 157576469
    0x409050712210221210c2106030a0b0910140901053106060b0d0e0c10080c0c0a060c080603010b0a141903060e030309071514030916030c 60
    0x2580c204210560010480030500992001c8581010b400c84000d0b80d40c58210130b8400e4440810180d240400100c0c013840035002d00c40c1040381e0b580303403400036020f03041449180081f200841c40328420b12002d03840000303480c032440c1d0f44901c11300322955862102501c0e10401a1040211a040902203e0009510992070b409134030840700a01c00359a4103c02c08540d58003c1003208038414440400021490607403148500d61807048001082c0c041c3d881c0ea03880308603005003226041c26550b0b007410182c6000c0400c2959402c3c0700a480c000c0c8844403503007000d041c515008002c100c4d100000159641120000c0c010700e000140e0186041240c0038540d540140030603400c68609000b58078084180515103408407000c0c0c12610718044110f00c01100c1c07400d01c501c141e80000c00303005d4444101004400500280a0101c210403003100840c0c480c074146030b04c0c51812940d075100100f111495880400340307661001034030014020055580e652901d500d03070304034a0440c0154416046400c48078001c41000364200554080301c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 157578956 1250 157577706 157577753
    0xc020316080a090602030307121802030111090f0a0506030c070503190207031109090705010f050d020f07030e060f03010515040819030f1812080c1e060a0b030c0409050712 75
    0x413030b010b00307070f81d03a06c026100304020456060700c000006801d45c004c80360500d2690f540600300e50707256000c207007503841c0c29a4001c0c40e0403012451004500700403403000c218020841d01100c0d49441c020100e4920303c0090311000109130002070010a200080045034400100c1042c084050011800001e44070042e9020072079003540d05a40e15080d6240c528620780c081c3c2d045c0c80140003450300c0c0c940155a0010310f54202ca040c0070041c00801184a01e5201400e219101d07078034030658545951030014610032849003542d1080c0014002075030058000400d41b0f055072029110080200303030549140700b050090350b2041c41e00e445210307100051489941004070003103100b030701e4240c41c10345603d000741c9004911000e5011140740480b010090f0300340003e26088a2402100840d10b1b0075850340041d41003068550b2402c5001d035211340745420800040121907800840f40c81304005072694140084e84800102001a00c10b9407502c10038000c0c480103115444c010302c0c0c030121114030380710940b500e903050a00910360f1000842 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 157580206 1250 157578956 157578959
    0x20a03170c0d03020a020c2101060608010519080604030e0a090606030e011d1207020a08010c051306031a19080706020a03090e010506030112080f0708071b0b09040c020316080a09 78
    0xf0700900039102601440c1d00136000c190254014840141901c042031407000d42040740a4030765141c01c3c0304640c040e1000d0b40e2a501c00b581420103004800c447c40d15a101c440e1340001e802c201c09034000c105503810650620700780143c01203100c000707007411080d0f800a204481ca0800c0c00203046070158480c48408041300000e21010110750b0aa4440800c44440130201b500140c00070604070305080d0090490910041a018555071507034941c50031030f80254208808113400083c0540400f0714000c0c0344005105626007840041808450b0320345103110044444d0195520001e424600305110f040c45001d04914401c640e40076941d0040255070344200c03402500400e01000f404545610250030780e50590314064155882e40c2d2804a90750b085501546003035480c0c100510400c00382d08400d42c01021520b004030f8403982c45101504209540c0c4409410380b0410a205a00401c600c0e000c040a503100d0040449000541c4980b040c0e007a81548911140e0f6040400194000010450203901415420505580b014100e5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 157581456 1250 157580206 157580233
    0x20f120103020306150a290703080103150e1506011e03020d0e030c060408070201050c0d0203030a06090507080402040f09241103040302060c160b09070801110702010504050904020a03170c 82
    0xa50320b000c032280c000e07140380f8080c49030301000e000c2c0307c0040040349075440544400c45550f4019400c031000403400100c921004005118100903025580509084200b0000c1e98a98007150b668510764203100d040044bc400146e0300d03070f008175405001d001021001c1c0030240b0b01c0b01001002075000c103000c0c40d00c45207800312005507101c000040d5914102803000504041e1195207540310030b6040b400b802c030304101d800c02806280000038000c00c0903419007034000f0368403801c00400c101c0961320f494002070410741c40c0c00300700011260b216250940058040d034001070b642d40c03c21a40e00c040c100d5004003800041116075107064803092000e10381e202c4242200300304482c0d080c0c0306003504148002d480150050344100049004100a00d004014400c4400f11030000c07100b03d6542c0c0c080981048542041070341003030500300420308003070140500d20055580c80d1441c08019a0001c4c01078042c501800d8001c1c2c900c580010119202d032101e12018503003228106000e031145019141140d07000c080c027083c47e806000c6068880 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 157582706 1250 157581456 157581481
    0x6021605030709021803030f0a1403090a14100e0601030c06090b030c181305040b010f15180b1b0c0405010e0a020705010f0509070602070806090706080901020f120103020306 76
    0x1034450060140000520b041400b00c0030b0b4102c84e079210750901d041200086203a130b040000780141c00700c032441d190b140c00d4441c002038500145070000102c2c2c0b0b0f200b0010041c3c5440f01080302c60f401e81d400881207948401c8007020030719291220003622a9140360000c0c40958a4000a15504803442145440ca0300c40e150300b0101c0d00c101d928800c2800203001800810240f02000d809800920b0440d10064079800c90280090700440c00f64030030310806a0754200740010f2040074012207000d81140c54410b28114545603400d0b6042404031703111020008034003410f90804007428030480c01080045121502c0c0c00000c0030040c50a1440042c81c1031a2080f800c5000050405001ba18100c07a19084100c44540c0d034405184041c2d23005010886441d541d42e054007001d01e075a88280c034010040d40000348115800c00704040e1a1890b40d400804071383d404a010803910944c00100801511250b190140e010344a540410b03019004443e00840841c0d800b04007801c482c6035024409040328000c900311400740c0c49800c4841d10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 157583956 1250 157582706 157582709
    0x2304060f0e090a05070b030c16030c0b06040908040b09060408070b030601091409070e04090614010801060911090f0109080609100f0b281701050a0e0613020409020d02100207060216 79
    0x2082d00150b45c00c00c4080c0c1402c02640d80040700c000c0052800c1215213044109d0042000c0443c04a01d1580b810024080e1060003540d00000c00e880030088410725407500c02c1076000310300c41e2035200c0500091030f0b580c03522201c0540b0010100e0000700e400082d16034801c100d641e081280c005000648a070720019005213071412261080305c01400e40802921040700c1261440fa100c4030a80c1c0198494812a0025869100c1d640c001000c0b00d8080c29594109800d0302c6c00d551150340011480e60401c0c14241a5580c10b030304491203060201c0e20107800c83d00e00001a900030301c060b0700820450050b00100902082e001c140040100d52100c001c1007203210400342c2100301c0d2460544940c1029550702c02c10b0300c2444644213401000320003505a0402550b41008250054170a6044c80403651140180500e5006501807031005034401c0c00504280e14000d417039140104000da01c017038891a228080c5e24199207840c05009a00740e0044d1a001a5070001c103006551a001441070301c0041c820310f1202c2c01e044051004080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 157585206 1250 157583956 157583963
    0x515040302130c181a07033605030d08060f030a0f11010320120405010608010c0201090209010e071e0c0602030f0f0f1e091606080106090509010f2304060f0e090a 71
    0xc4c900321760240c4e401066080885d0440900220020703000801e0400300440010300841e201642141005502100ca05540d5a002d240a5442080c0303104d4002d4110500d00d600031410344141111700012800a441c096004802802c2605216401c40c20b00261022010020800307032000d002e2000240041135001d0300c0c100b06010445000c1c0095042c0c2d8144056454001c0d01032000401c0d001d4503199500d084554003600840941c0d510901c440843c01e21400050040408c8182404640b51040000d007661000403240c0922382c02c4100079101082c091191503c4281c1c21180864407441c04510090083c0d0041d59940082941c40001416509111160511842521001c00c034084031a0b807001c840c240c2c000d040c42e9850b0040c040004000300e060208580103000c19a40c0707245a51400308090400446504028001d858500041c070032201c0c054110400c681c3c100202a0101c542c8080000f10071090044156010341001e000207290102c0e1011903099410345070f003807136481e1540400540d4482c942c000c0107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 157586456 1250 157585206 157585229
    0xe0d08030105091f080d03111201050d08120403121802100e0d020315190501030f03050702040b1302031603020c06060f0604121b06030b0a0515040302130c18 69
    0x502c4941440c200190300070240c07044011407180080f121801c0c2012a400c00c95240d40708885001d01d543c3e05009180410402100c018a032079100c4a0301040640c0c140109400f40c075000054004000c2140c08407404c0d03c0d00c0f80755000706420280390041203201d1903090107078028201341420080142e80c800d1001100c4d401040800c24081108041e9001e804030009961702c178401e0403661015031000d10180d2001d81404810a00c41d18203003951a00c5405034001c03100d15185004014000039004042d1505802e8050521540b982514400200030300040c03081c1da43c0000710070030303c000070030f45030740155008040500740b4401380810303080308908038001d184082000c3c2c2d22140c080b0310300b030504a1440b01e80d0400a000f1303038035054580f2203010a40210107000c8800e4204140c40a10382c444210864001e02124038003800480b00010003c0e881001500401e44158074805c0c1004c00d400c0b0a004076002980c3c0030380b08507007401d01201c15800901082e1178501c042403c1d14008100d0031207961380b64050b94040a6038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 157587706 1250 157586456 157586459
    0x1406070f110304050d050102070b13030206060405040c05041b0207081501030602030a0e1920032512080309010609020f1902010b09010e25020309060d0b041b0e0d080301 74
    0x45410380100d00d0400740078007040101241d56181e4000314101540200009030b641c07485881c080400d05030082441c680b228403110f2100001707501041d065000315080303170007040319100d504081e41e21a0f4a548400d9215260801c2ca445402d00d555080c02d02811940949141039961000280c69090407071010502500c40001480000d21950185400c514141d40c005904520b2465a07403414012a46100d014409149003a00300a896604010340c088210b402a8582c094000800e41d2101400040446000e90f01680340040790482c1c2c842c0002c214001803040409100d040402c03440e4030607030f010040d55003014004500c1c402c440c000c43e21080c0c1c0c0d07000281e00e804621070306c42a070066201c00c3c4208554840c0f00e4003900d591010802e50103010100200386940c108010000e14182c1e8a0000b41c070400c019104002001350080b00380d40581c2400c0c0d0b8141da5a060244e98000141b05a0040c503030f01c41d2a0501c035447c6984c4e41300e0801074000e407646550040000c4003082002d000307205c030740051480008100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 157588956 1250 157587706 157587737
    0xb0c0316120902060a09081606050706020a020a050d0c170c0309061606110307110a03021b01020708010e010501051005040f12020d061b0212030f01061b0c0b0304140607 74
    0x7211410503405800054500749680055540da0041c00e8110026420000501203e1414851b1070f920034400561410010725048024001e8000c0140151050740e001c40e049207003500a02682001c0366004055583c40d80c0b005601402c0114440750a40b080c0c1d200805071400312604808840301c1c1c601c960011070800c403c0c0703801c00a543d13015a124410981c42240150006002c0c0d0080303440c40581ca070131042c1c491428034002045814003503c08243c0358050190000444e80202e0a1120340303400d803822141c16484900143d140c1060359110030380075840c04100c200303102819444141a50001c40326280700c003524031003c81d02d0740203502661000302c0c41c02c05c0400c40d80b060054600c2100c0e101410a422110258450804039032800c0c004400c5041c0d1b040d090491070307505010344901700e01c2c16104a811070801c070b10281e900540c140200418015840010040e10705005142132300e0301c0c1d028004852080c3c0700d81084c8040d400907a0200d88668001080103800000401c41600c580310315542c5942c0b20f1042c08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 157590206 1250 157588956 157588967
    0x30402060a140c0102070b0901050615030a02091207050a120819090b2b06030f020f180a090c1211010f0306050a23040e03071106040504050906040b0c0316 68
    0x1014102400401c1040b10032554254001e0300598050360001a2205100c0c03c298022602c010414440c90345000104503890f6640b0401c10100314108001540325594110341d80020701c84c8080036580304c5075100400c4100b140001d24801650303c284eaa40b0b440a5650480355004444080001c0880c14244450404110000c1c000c603105903070791600360690356403505016402e50100c17407008807100110352220700409160803298a1583c241200704074180c80c4d41c407504240070040d42c0003403050141c0b81c2e044000b0b0341e07a01180084074140814003410b40c10004281e100405c0c0200003142d0076907a07000d001462a0b2203c140c1d01000360403240d106003810f0040011501c510031208100d05055075060040b1381d984502045070003402d17802c481c0140c40f00d0340720011131010341c1c40b03814288201d003081100f200f0050040203640d50751341d0180b03000d2411681400051030a00850304800c2d001072520040082041d4001509406503015580b032028585400b0280845880100c52482c6100e0020058591103403082 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 157591456 1250 157590206 157590217
    0x10090b04080313020d050a05012405010503040f06061205010c020c09060405091c031406030316030f111516020a020306070e06040801181205030108060402091305060c030717010b03040206 82
    0x982c00b03003a80b030f0703036680050364806a100068585920000c030300c401b000002d00c40d0320020403403044c00e200342d5244040c992415501901840c0d04104002c804a0204900149a1100340340d2002c0140010340d110301035000040740409007582c556080a8061f20400e0000c10002918040542040101e030788080034040600170180054074a8826242c141e6104901c0c0428410f85c09080e942c00b00c1c4480301512001042c02000c0e000d248242c1003008150140c0e100641e0080e0010342c03608198012000c070b144151020740c1c0350f1135154501d0081030212484140680000342c4200a0200072580a00380004100d0b40c1d001041002034046c1e020718007141f402d90103405070900714100148030724a4035864902c11402c2d20341480c000060b41e100f24401000300100d01d40079848003a4285031503400c66240905003591801c02400190241c1252408070700315280c1d007549489407a4005048034040e0422240190b1035600c00c0320704000154010b07041200d00c104d5108580d0484115851240c1542c5807a002c002196124 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 157592706 1250 157591456 157591471
    0x130e010e04021c02090901020904140606120702030d0915054005030403060506030c06070309140105070b1f050301090305040306020f04050915031c08070c020609060d050103020310090b040803 84
    0x41450f4103005903a2055050b1280c03940300c00250702e0b0b050035070610054074050f1540c1c401600b00c4c00b0411080c2d48581050703a07039800c1c0503080401145c4806009900318440d0700104040d950400100200380b0000035a481030030380300500c0030170980e0342e034040c0b003d21003104d03000450980d011252420280009469100358480d218410303000e480c80c4a6860501e0b40d4401d0340304482407038031041046000e00c1c0c14016900c004a0a40b1510315150203540c00034981a00350040381000380440c1c503404003613441030096440c029404110041c2d54142a059240c144031030301403c80c0d112840b02404251400c5c1070141c0d0039425419180c01d03042608640e9040013940005101054410052000048940c0c0b810803450248441e04030300d000707500c000800d1508207102290181e14480b0701005e10014207074890409035120a00d4906506414017a00c0010914801d40031000d42c040c0300854141503455655005134100d86c401c50880344848000001c0009468901f8005490310402900240c00704000b0002164050036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 157593956 1250 157592706 157592749
    0x20607031d060d0605030106080d020d110709020301091a01090b070f060207060c081b0a090611070e07020705120c060a0c110d2909030405130f020c0102130e010e0402 73
    0x10040d0214001d908101c0040050740d4550344c1c01c2000e41000c0c850103000e84001310240c840f40400241c040c0d07031101d0300202d0004004025084c2e00840b441805102c0103072034007046c10755807540d5609180c0003501407005850445041050f01c8003043d801f075102ca00c100d8200130860780c1072010076203034184003500140060f11400c2d02001a40c1c00a0158841d0022804581d00d07525400c2c1405500107101a0822a01040b4080d04010b00c2c000c840d0441c20050860701140b82100001b00f0300000141011050f5000e00e18040c6400148804141c01040e02d4003900c40941e070103040203039400407a030340d41c2c44500c507281d401090801c802c1d00400c0c0703c1c0722106080d17030141000b030344400d000c80082401094600130a56604940c245006280f00d07184100ca5034a1104080340b81641c2080030707089072684101d110b024030410a0030240e040b250701507000b11401408021003191038840e22550395010b54048107810040600341807010a110304202412416242c410036038007101c5c1e4856013030083c0042801c80c11a02d0340e8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 157595206 1250 157593956 157594007
    0x14030a05011104030b0c07150902120109140d140301050907021905060f0c130608060301062606010b0c28050322060e0603190905030c0106030b07080402060703 70
    0xc50900440e69603840416025a40d14a54140301c011110090404a1014010455440403512803d2040c8005665500001b840d406610001c4d5000740009103a403195400c01a20030103221807000b14400421a000503a082c3c0c0201071740031107410012000326412008140014000d80c1040901594410760900469001400405138280403140a900480c0d40e0381c03028013080b414001c4692102d400500300180907091006045205c411880e0301d003d510304001c40600001d1695409401c203100400e01e18200d803a4800d040f1b45070300c0100c4405500a0f00700d10541c000014a12022422507800c0414000584120174280660704081403030300e9903120390b070442c03c4200d1001c504c003031009005008c4408581034462aa00d448040304100c40e504c400c00307111045983c0781c00707520b0701da0840740d011001d9a0300904442280411400a0240c9100541184401f042035007005030151b02620a8038002c2585980d15900c41004586140044400a400800520039030001034010303010000305070b03944c2d152140d841 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 157596456 1250 157595206 157595213
    0x1208040305070b1801090605070210051902010b03060f010326041a0c0d080105060a0305040c0305190b06030c060706091a0c0702090a0203061815060d0204080d0c030914030a 76
    0x1140340d00308060b140d030001008110111100401104801300b0700703042410a180480140c118062040c02030300031541c480c01c02041c0c61040c0111005130a042c0e542c3c5c00c07046035012000b4024065900e001d8000d105000203c0d81001201c00210304aa80c004410300100002c40070000802900620111000006020224000040d002c1355030741a18a841e4643d182c2210241e414a000ea481c0106001d0051070310042c0181e845010031160702d07968908000c030b101d4030f0b5413805200c803031040d60001d452809000601269100051402c07800180220088045500c42100705a00d0b20040c00c1c54592000d82000160002245c0c0e4001240f0180605030149100003010101045141c046494901d6201e000440c0c008501c0e01c1c0d50300e03d40040d00ea20085041d440c111307012030201e0040a004900510103840081d02c40455054640110000504110b450701c0082c03252074043d400900400400e4044c040f20390030014819900d0710501a0140c1e60003c21910b41a00002441040c000c01d9415000740e00454012 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 157597706 1250 157596456 157596463
    0x9140603040323070b09060604060f060c03020a14150903040f05130e010606080a0c05090a1e0306060b07061d0607050d091e03020115061d0a1d01050114070b011208040305 75
    0xc2e18007170803040c1d0306860480505810410b0003401d40e442035242110500811000c0711541c1c2c2512034030f042245004141e82026440e04402d260000c0110100d60603500c0f08a0012a03165001d03038020303102c0704080d101c2c2205280c4a0055010b8400a491203080801061400c031480c0011503054030400905112110b8095003910000d800900210300c4150620040d0086880340c2e480b00b00451401c60304102c042c2c2d00141c8048400d00c00c885044400c0442140e580341094040b900850b40440100856956100404410340040c981628001e00e000307080741045a48038050a21035032890040c0c265a5074264090341ca5811180d02481010780e201031510000b0081840c508000c80c1410b0b5000000740e04d864000d0a40362035019606012051007400c100540d0016850251455800003040c4801c000383c0100303052540030b91000304035121900c2c46031010030130302100906940080c4d9070100c48c000c642c055032089208000c002810b502c03e050040000510000700105d030144952401898690f0343d480d00d514 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 157598956 1250 157597706 157597717
    0x3030e01180506060f18040203010e030a0905010e040209180901020d09050115050d030507030c1104050a090201030f450309080105010609030b1807170307020109140603040323 77
    0x100281c141007841d0901200300240d5610010454060280014240c04074510074000017a0107050458000400c0071550300390030017102c40d41c10700100c030303100c0c2d42402000f031029071544a50741c040394036041030320b0079814603000301c0388401d07006401881400d480412849070700c4c3c001440d407100c0c0d541c20700004641d881d19001e103c255502540003ca2000145907580c880c02c001c079031080303100b10754a008910009410000b038807201c40e01814000c0900c0d94a040151081031861501903020789450104206103070b69a01013060b031741c003c0e81e0800401c0c2180740a2000ca40020039800d54403000b0284002d841b8843c0a510290003a00000c8203c00c281202c00700341c00d11001c0e079021008103542031003c0c01000000d2040d0b500400b054900346000ca0f2943d10703074000042c0040c140107201031407d40c220391080c43c00c00500700181040b601c9d1445035a5210115034580d0450b100c101c3c0040c0903400001925041001105c0c1d074204001c02e02451529a5a02036840262822256032202e00c3e910300f900107120200013411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 157600206 1250 157598956 157598981
    0x90a06020c0312010509060d020d03270e0f07081315050a14281a0a0312020d020f07090b0118030f02010306080609060f1503031305100507030f080403030e01 69
    0x50f1216010300459908200580009006101050400c070321079541a44032211160180c0700c01c2d545a140d41811034904240b01340d1009046100c00c0c0b055403001d40c0c6071001007140c032034103c04001500c8520360018580c205969440004241d040414400700c0e030749a15100c0144643d407021501c0c0084980181540e01c200d03029501c103503071210f03d051038008803250240e2002d01c6422807807018050034a10408503a00074400914599586096007654094032111248404021301d84d8504076542d2902c090b1411103104000010b0140c5032040345003038000140130300e0b03200c441c1000d07103001ea060218440c001d050002101d0704000310318001d082500c40c4071854001850082819007048026400050140c0d041c961101c140e551041c406c2080d514400f048080d049058028400d496440b000204c03040c076480110465414000000d00c600034002a0a012003221401d07240d40c20704a62011003680c0c02c0c0100003020340403c851035270700c042d0507109001295020380300b400c1c00a40800991851802c6840288011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 157601456 1250 157600206 157600213
    0x10914010911030a0f060b0609130b04181a1b0a050406020706090302060714120f1306020d1202090d0807060903030b04110a03091514070e0a030812090a06020c 70
    0x2003050249400501c4001d042c01d8000706401161030707940b400d40e240c2143d0081c00c203d40d40e1146480ca9580c800888882e01001410300c1c0d042c040703d480f000001e059130144540300d03a00d0003201e084000c03241c580c0311000a402c0702c1503848403191884031002e8200700911099200c1049062100c4004207500039086003600e903650203442d0703400c2c0030010b80f8003401a00508248507140758108010780c0c4180482d15a10ba02c00c200e140c6000405100a2808004061481c2142d001056500041a00102409005a500c2c0d1105003040c1e646c4000d1b40c0300d003000450302c000518243e014190700c0e1001d4000741040d2402500d070004906203070312241050f41054000702c40164480c1540c00c245949401880440c040485042190102c1c1455041241c8680528501415101d0103010140000c91905c101d002d1601801031082d18020002480400d904507100c070f003c200390040441007404c01441010640740d100700c0039490b001c0200b80d141c4035820f00600940c42e51040b042108002509400a40b0010001100a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 157602706 1250 157601456 157601471
    0x605040f06080114120f06010b0c120c0a030c03020c15040314071424120f01080f0304030b13140304061b0803040206090a032001030c050c1e01091401 66
    0x540e20650460307000008100c50b450042c02524032120001c2c0000e041241c0c803550384036080100504081c090400070482e806004000510410346900600944164505680c24115080e902541c0b5000da0600c024855111a21140000740100322030802140240119020004c041000600b4014101795014031b41e20042010002c04c81c820140d44801c2c0a0180503000840c2005a0001d600107828a814442c06800e02e02c0f90144070407441000003804100b85c407d5680c90181090b443c0318ee01074913103040c01092607000007540d005c042072045560301c42c000a035151518645800c4c0500304042e00c205c00d00d892255071b0000041280d08019030440c68403015644851518401038110000014008184042d00c21200000741c000c20880380c2c01076045802c181c030340007400c01040290b0340b9031300000d111030008000305260302000030b0341c40902c81d000d0344c00b0310070517030307205801c991034000d11b01160801d61210080710b846d00e90101c0006100f030862400018a00c1581e00d521818032080f000c44201350350744c1c440c2c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 157603956 1250 157602706 157602719
    0x806041506060c051c050f04030c1d0403080103112707022104030b0c09030a0305250f0204050403031104120203070815011a04050a0303030f0e0105070e0402090a0807060504 76
    0x1004020300043c1481160b5541c1500e40640380c1c10700d00040b8503040d0071100c50304241401002582c206c1c00740c80d5000d5440b99220f00d46864403200c20700138810030003040d201c651581500e21408a03c83c5506550711078503070346140e403400a0000400c0d14180d022202c490215500704545500d0350081d03a000311134031078600b0410700180c14664401f0390015000c000385400c540012000d4110f800300c0e9400040b000711a92808400314603409010000b95043c0200400b00c01495840000f43c2054544078505c0040d1600e2004514a00f4580c040020724802001d6075460151400f03500147c5e005000e4140451080707020080328070b140e4800d401c0703401c034005242e6000082d41400c101110240048000800880780240b0200c0c05017001480358082c0102c00c81a07620b246413004040c2c0300100303005080c2940c01a01c2c0e00c1c002e0040d0100c0c07200b1400042c6419100d5a01403014002c2e0750140c110313601ca008100c05a0814400070358000720819401030200341d400a4040000c21001000b00400da41d143c5d02c2c0e030f09101c0e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 157605206 1250 157603956 157603961
    0x90b0f04031203200406050a08090f060106020303070801080d090501051602090a020706060b09090f04140d030506100903020a0501180806011502060c0a08130201110f0606101e081008060415 83
    0x1310404d81a040500060202d41d4100c8210b030098043c9090481d0643d54100300c8918144510804107810300030b80c000000c00079000805507000d070300c80e61114811030784c0f03440c021550b030301c2c3c10380d01c40d0700242c0d134030b20100f00711b5006000816000010499105160480d40c020804544042e560090a903600184102c14000715101e400050f0281070702d082e240c801c445002400d465405080002821200808542045402251001a2109102a83e00f030882070140a030007400200d40c460b0080343c004100e104241d2240c03d00000b66039005002d043da903400d00b401111f800c2e940941e4802403044101000c200c07140d04101c603a00074682c0700310420010400400090a000c0e024007401e0203072501380985010590003a8645502c40c80b21041044450218001203072042102c00d25039070180030710441c01e5550b00002c502a48902e00a40341c00400c440d841d030003100d0100451807000ca6122034000c8040c0181d11459440d900300002003140c00c8004c1c0c6900c0709a003003136420740c0c0480f45c44000001011500c0103a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 157606456 1250 157605206 157605251
    0x1b0d0f110610090c17040b16020d0c150b06040e010501180f0302060901050d050a0e191119150f170c030f060a0f0e06120c01090b0f04031203 62
    0x300581810b080c00380c0c0804903a1a41e00030502010b4503600003407000d070710402c2541080440402040310f00d09060824100b024410f81c0e51341d03080d1003520b4070602c1284c0000341d5807030024810b6aa41d1150350503529001030030307104038070008540e0b44c0f9400c00001c2690382001a2000c8c3c4075807030410b0100c1d4904000580302c05841121404400c600d00d504000001040c4d01d20340c1101c3d0155500d90b540d13031410004030703110704c00e00c40c01460191800c018890340f940c41d50b00c042c02d2a490581101c040254642400c40c4601d10500c004104401288203082907052150680102c00302c241802441c09442340f0381c00c0b1620b0000c80c204400655907522409130ba9512500c810390039580300101c5001d504004105148510004245a901420402c04145151a0b04945000810107040c00c030b84a00d442e1407070b0b41310300d10080c1c500a1140c0c13407100800c0300484001c110742c0c1230200e050f12810300c40352505180032419007008440300d41010b07081c400000891002c1c030100100d0704460b5000105040d001c41040302d081e020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 157607706 1250 157606456 157606487
    0x3408011409010303230f040b03070206060f030a0318030b161407031e12060b0a1d0a12060e0d030509010f111e04080a030e24030a021b0d0f 61
    0x601c0c00401c003194002c07004100030741320180c144c0f110510340c0001402922552040c65110700c000038000030170f4181d0301c1c044c40c0030301010750a48105440301d1007000041d24020445030b5054100150b0030000034099205c2045980c9420b040c0540b8035070382e883d0385141d6002194040406500403207000d04e10b50b4855018044180e5030a1030303d0402c5005d450090030182941d14440c0300e40c42000300c4811244c059110783d01c07003d486035018018542c0b510006841500071341c1d00326010031407102d8852010040c0b41404e188005016101500d06803602414281c4400118000c0c3ca005075034091280c01d200040c40300400d000480c1d1030100d001e042403038025084600c044450a04140f4081c0c00b180700300c80100031680c4580d07013002c2d1005045800c40f0411094031441d80b201c0994400c1d03841510816411400b1031400050071151a640c11040c091205e1060b141d4a00c99445543d04100080e609101503000c0d0014404180c2c4405a0f03a460b22115458400d00288403000300740c6100f044103520364422002591200f0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 157608956 1250 157607706 157607719
    0x31603140d080f15130e07050103020906030a0513080c01061d07143001030b0c0a050f0d09060e100c030b0a03080d090203030d090b0604020903030334080114 69
    0x41c624010103500d00503010f460455503182c00314901040e80c1c507800500b1940100390210035685000104001c12014450301010702655800003940e41c0a842900d013040000341c01c061a69683c10380c240c004103001000300e080126000e00d00400b18414034040c010b8501e034400001500c5003824806000e01c0c00c803901416014021408020711103034049880a000c0e03800315440c6407100c402e20202402044120081e05190142c0c9051054203c000b48019048a006519400c5036407600c28080d4403511400d0300c60b0021a0702048210310901954005166824002000140c015420340e41c080584000000b030220b9940521401c03060321090b44100068040c0c02c2c1000c00840c080d09000c600d11540074403020704001004030302c6020a00064000d501d1036036000b010b6990f03840b100840381000f4070703540100b43c410741c1044000400605092080b1820b040c00203000710b0541d5200124140620001d0300c1074038081c1d9804445004000380340514a03000c0300b032500d0360222981010f03e03554121401c000801c2c4a0103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 157610206 1250 157608956 157608973
    0x14090601020a030f110f011a030a08040b070204060f09050405010f0b0f0906060d020f07050d0504030b010b0706090203100b0922020111031606090201021c09051009030203160314 78
    0xe070005458800554541414802d2072002e10090701c814101218500c0303d4022002200022207043d1321516004140c0c1d41e1800c5000c408205243d42c0782011000100001c50401087c4095504100501001c0d031000b44042079030707600da00310b032050003040c0d6100e808880e031a10144402c02a00f07000d40c41031108001e00800040c8542400940d0151150171214003a05402000c51a40d840701d00c21681b40e02c40f0b4402c2950380e190711194a40899010040c1662180510f022625100707104404903400c898021044814990030310500c614550f100d0076048030920303603d421740e0005807820300030184c1d012648840050054024014031050034001442190034404105401d040480d00401c1400c2d85602840c0c103c45510301c0828087c60f602c01c0c0303400e42d18001d03918000c00c4204103031600100c501038402c2e4240d80851912032110050b0040b00c0940e040854400041400b180c1402040711107846034614103220b0540d40c1e41c01007801d00d0000d103c03c01414101c0441401406812500c0c4415100c1d19001040e4a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 157611456 1250 157610206 157610209
    0x703150507140d09082a0708010e031905070c0e0105040e03040e070f0528090b13030303020c21120105010c0302060a051503030d0905010506150d0b06070b040c140906 73
    0x24811400c255036800e50711341c030450a01c000001500e440041c2c12044030182d0f2115240e0000d40c0240c140c210f1080e01c25042d010560110601031803440b122004015410100c8080054080c001d0900305102048020b00400021404100040000f00320f85840d2034010f50402c0c0c203000c140d034140056400154001c01c020000003942c40c0006921100d103140040c0f4800c44100b00326920321451078440080b003011103500c010058621049400d5a0254980ea060155500031140a60040e511078001640110781e041002c28001c0e0002c050b01034406059414016044107100012100c161411154110114410a502c01500e401902600c2c007420881d81d45101c03650020340e10040100307201e86981e00c03007011440742c000d0b042d8a40a611002030079240c0300d00000c09150000e001a0005035030960070b1001050080c100400045e0109100070421031404e1f41002e421b002914484071429000b4404104140204514032562400f0360310900000e00f015213404040b801280000900038414000d800500685 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 157612706 1250 157611456 157611497
    0x60513021c0b0f030f06010e060108042004060f06020705030d02011503060b190905190c0906182606061017180d02150c041203200703150507 62
    0x410016000101c0e54074041c0002c1031541c070780382c0c120139003600c00d00004c00306044c0c011820324180c48a155203d2019520200111000702050700c002c0c2000321641950a0000d002c60300000c850107015001003000c644e940380349200130585902090060300000e0050095213070078801c0e503625420510003407001c1c050360704060105090328800289103030b68070350160307840351501c2e040c1c21072000c2c1d40202a0329a564070000b20001d0b16080f1100308044918090303855001c01c03648128124402c40c1e50316580c00900f400303401e4440c100c071940e8100b80c20078003140c0004c0310b591b001080030410941842070a0100035101116140c120040c1c403051042d00f14806005440d80d02561210783c00010504c503c0c0103846200c00784481e0050220404950700a03c9450004980c00040c2c0d4682d20380912a40315480d940c10b0401501c50260340648080c0e042c8a44c01d002c0406d10504000090b49a562407a50308d45680c003c10324031389001c0d584101c03840c0080c0044d8000d450b440344909070b03020306e0a041014220940c148070106 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 157613956 1250 157612706 157612747
    0x50c03060d0c03051204030311010c050d0902041407020d26070509010c0203121902060108151e0907090c080403090504051e2a07260c0d0306051302 65
    0x34400318001d0002e100c884180b04005680000c02c0d200103803114503080c403041e48640026400301e202c0e0024908003200500c51100348042d503030350310740c242191088900080c2680c4401607038840d4841205081c9400108800d41c0208029001000000c220701c6000d09281c1081c00010003064520b5035581e101c6241241e6103074803042600d801591080c0420068030141c111501c041d426100b1590103010861707240740100b451041ea0700074131101c000b59050488e5201c80c00d004009071a04610016081e400d1a211010303048807209120704495001e00141040e00c2c0811035418005e50702c400c1c3c042141c00d0182c070030318207000d0030392425031014076080d10040c000c84a107110f40781c0990360b9800050500800240f6400131405410401c0300301d8241404a16980042c20701c500c0c40101141d80f181d6404100032003100c400e594400c851102400e00840100c66100c3d8081e40000300e11020080c54514a00600000c04166000d071000030b822070400041c404035a4450380036400c4144100141a401c00100d540e800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 157615206 1250 157613956 157613959
    0x1081e01030b19051501110c01140304021f0507020f310f02040305070305060705040e19060509040609030810050607110609030d0504090b1503070c051e011e050c0306 73
    0xc80f501c03444000c00c05440494070701e01c1c1c464681420b00401051030550100900026a610154420548000741c1c40700081205c250226814485c0d2005103001000a5540240000c0480c6840c04082101c0051020640b070300394009075000450f04c1c114a0a0340c00034244400594103d482c2010506050401c107071103145085403c66903400c50040d100e9150049030078010a42015034a441e41d074074000c0d0340c60020b80000c4075940100e030000b5aa144c441d0301924103d600e040500f091a4a81700340ca07280d0804603140d02c4222a49818020030241c40d20b00e4483e000360b106110000c0c1c80700751070030010701c83c0701c1c00b0382501d030aa101d44030208560342e2840f043d10401074218104034445400c5c03c000410921404100c560580182c544884c40d50790840060011906c80c8041804080d10390001c01148000e820300003030451000b4804148550b00c51440420302c40d00c11030850f102034407012070340244040303050300c20383c2d16a4403180b540c1c8010058942c2d40d0b61081d841402400355051400c10100a0b000040426 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 157616456 1250 157615206 157615223
    0x209010303122009010215091e070302041406040b0a27180b070207090903090b03070203070b0a020315090408092403090c0a050607021003051911030601081e0103 71
    0x71070b42d03803565200f5000c070004020307003c00c81010b01c0d0810446030400307030700380c0e000d80128103507103500440d00b2031094070642d00c01001e00400304411441c02c070411007100c04681c19200f000c201000603295441103451500b022240301586260440402064940500031907000d10500001005941d043c80a44001090755101d513035a0070b400518108000c00c030180a1120907064005070606100404c032400d40103428942c20748083c0368403003000a0985242c5100280095642c130004c000c402041400f458102d1000e10692740f40c40b4194440d41c603002400d44110b20055400400e02c880980c4e80c400f10200540309030b645109a251540f600c050b240180320705203004000da4031095500c5504008041011721414603043d4481c00c000c2c10302c9a44020040e1820300a44030300300081200c0c030b08201580e00456005056000b038560340c600031800f620001d03000e0703072100b52620215040500180105407100e41c400504546904d03155000500107079020b031089000d0301400c41c065105422010003103040d41d8000d0b402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 157617706 1250 157616456 157616477
    0xa1b020d11120d0b010e010207142e03140a0c0c060203060a08030a03090203122a0f070603020d0b01090305070e0403120504120905010203043b040c0e010902070209010303 75
    0x2441c200208000c1c1c2c0c01042c00b000030900c01d43c40f1154481141c40100ba641c0b081c81c14040d20048e60760f200c9038081c4020300386244900308514039122200014a82e021800700c8840910800e126000014241e50744012a450702000c41c001ea6207407084c6070388032110b18403d010355203424401505000406c4030181c003081c0c0000004089484511421004201c000100da50750200800010020669108228072a000e42000c503201442100203940c00018601d250b030307022074881c0c0c1d0315a00c468450046c0c0c960134010740e5030008803e02c1c184004001803c07151805a91034420788510012105490b8199060041e94403041c808640001102001e030b901d202e9118443d92034a05080d02c00c01e403c030400380c06050500007080108204004c000b0300c0d40c1c407152100142c645c0c0302e400580e00c83c0218020030b1401c00d44105030b45d01200341801e064031805a0807031a01c3c5072008555084003020400c83d82502e810845807800c2028500c0c0295550041c40185d800314200511680010300340a8184809020407544814 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 157618956 1250 157617706 157617737
    0x1b060f1f06030b0a0e010b03100b07020f0f040b03030a0c0c0e04051906020702040912020d0e0f10140408070e0711060c0703170a0f0c0201020304111005070501140a1b020d 75
    0x409001170f09031098450301c1507075554511021644200e856011450200b64000f80d18020a01903403002980140040101030080c028046540064142140d0182d110404041c598405000400126409a4500b00d0707040660070312a0881e0034a034002440b00d0001005c10022a40201b007000310320001e1ba140c80c00c0001e8074103214010380036640d4081c2d4001d14100790340040210401086c0310100c820780a603001005103000503030b45010b5101440ba088007603840745200ca46440020005109500c0c207000e850100815211866500643c01c004500d80c0000000c0c001c1c010040c1c9840ea0091a503c8d01d00e1803c650700002680742ca002a003030b90b400740030204c0d0800070140103c000540415000c04041d400b8984941c02c030300601000d5445180d041e24161100e0321092042c000c6038400c1d03401c002c42180080c42c017402d0014200e4803014001c01c001080c0030b5000014003e0042d00d003007048030603041802e8104051920103c5400b6000d60a1444c001c0004000c040d0b00460108480441401d180510000310003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 157620206 1250 157618956 157618969
    0xb030c1c050f0d02010f0501050904020a090b130f05070206010f0f06030c0504150c0b0a09050613080f0301060c0308070f0806150d090305031e070507080d021b060f1f06030b 76
    0x12040c9120780200b2403ca85440c1d0b055008440c901c10302d01302401503982e9502031041c002c2003034901940141065405000c901c2c0b194008107640d242c050885d00d0b42d80c0030141b4190440703048202407a0342c00c2d1104140b00c0803960400c500c0c1d016007490305140344900d1510000c0c480712021841010245074072a1002010140900d0680b401031104049a148614944900905030703901d40d0021500d10303603440b0129071409100e11401c5130311980034000700320319150740b1800700078030294600c102c840c0c03d000c0004134008420080514020881c6031580350b609803191030040c14120008012004120302c0030310082017503a02940e2690171000942d450031003a041e00c2e03101c60541c0f103018000a050b50a100c1c0300c41c200355124004603c0b564820b20345031155410300284807045001031f038950b00092010700408002c07400c00c3c0c006000c1b224002a0061824411880e00b0180c0010034030b10080d036400030020840d140c8807036045642d02000d00c0d042c1402c400048031a41c3c0180784e03540501e000b0981d070742102400300d88861 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 157621456 1250 157620206 157620223
    0x102030108031b070f24030b18060409081204140c0901091a1011060615040b0f040807090f0e010c141b0102030a0b010f0306080d050304081303050303060102010b030c1c05 75
    0x1083d01401c1d164000703080c0b403250b0100b24144d801b008180f4811414441d101c0c103202141c00401c4403c091010040c04046c6020180030307264860703500c000510014035408001e00c1c04011840080a01e40750074107000802202c1a50811403070340000221803202d54480791042e040d9202c03500001041c403015000c80c0021007150f6400e9400c101070800810a0a070807400c1243c031030700d000046031490341d90341c81484411114074000d004800c0c400c2c4420b00a620607640508583d204501015041582c0d80888905e00841c0e54070110711130b0340d80d450030300c07116510303004540788000004000c1c0090961000c00403c01c1000d4a4403c6000030085161001100400c5040c101003201304001e6450b4180100c0c0302c00200b0744001c02c04c1c08501151f00411100c0e0081c090442240e00c0d80f0042e1603074421404094a0540c0001e000311546402001164102403c1344160005907004c1c1006546900d0003d002a00311402400d016209500c4039401010a6507141451310810a0b42580340301506001c0c50058640301c40d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 157622706 1250 157621456 157621469
    0x2090109020d1b050408071205120c0f0a15050708060a0302010e1528140f0a0c0503030a0501180e0c060c010912020307030314010e16020304120c03020f030102030108031b07 76
    0x1940d820f42e041035841000343c001d590303c2d0030998245035a00d040b1205541c01007200140190423000b068008098420081c0240621160039660f11003010400107040c030440c200c0403603510f02c0c0007200100b0941144140c90340541a41080c00e030508040e070020701c060803903100003410031008420403400d6895128035100ca0303c458a0f2040c1d1146111108514280d52200004846802e801c001100c0c8030f100d8025000d04590010445242c007890b96a059260307070142e81d41e042400360b20400c03440001c0d41040218416003200340000b80302e504200c142190001c100c000c00b0b01890038420780c2c40442e1808100d26066106c02c6400940e039141100c509400f40452280291140d1400889607812075000301c01020010300c641d03001c1203c2c1c42003d00c0d402c04400c080c00303040b80b618140c00000703c5030181c219411005800764011a82416540e006600f42c0004003042110201042a010802c604003520390b4582d40104070000d50442d03042050a5680e4000d0010906280c04564800b0104038001e0282c0000340a1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 157623956 1250 157622706 157622741
    0x3150406061a0d0e0d080103060b01020a08190212090a050d11030a080304060c052817100915030305030c071a0c071b06020c060a030204120311060a0902090109020d 72
    0x2c000e102000b500070500c894201c60500c9120f80000c4d070045010300d0115031544610743c041e400e50302c410008140c0301d0401c50540c07189000d140007080400340a085041441d4201d000c01000450000741840b0385108004107000d01402a41180d80e40c0c401d2070b6040c1d40040c0c45120040150b810300c841c0c0c029404443e01d406005903082041808071101c010741c071a5000e101c061101422144c02211507101c1c1c40d00c801c5140c014036440c40b9400c9041101e5408440c2d403813a0030700ca03c54851034403c12011081e40c8094182a00440411201555000d0121100982035070010170900d152405403071840b009000c0580780c80009500c00c10800e44d00200714001010303940600d0289005900f929156110f884107072886070440d2603070300540442500c214180c0340e595001e0f01c1d0402c0d40d0001d00c4519040410340c04281a001e000c00301d40ca1107501d441841c0540030f41d8460740f6090041400a08041000d450811041c0c10407565101607220103203010304607840242c0060b13840b08001e4070880186010441070f6600780e03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 157625206 1250 157623956 157623989
    0x1031d011b08090303010501050f090907030606110a080313051f020301050f03010e0d0f0201090501050412090b04121b0e100302030d020d080604150b0703030204090b040b0315040606 80
    0x14055000200c1005008801c07030901030342540540754080d080350b02081c150700030401802554490009011042d130170490f00c40c01c0003040130008901c000108d070034000096442004210640c0c3c0301c54018406002000a0190600c0da91190202448001c0100811041030a170490400a0070414038500030050000005000100343e41d805c040d40c800c1c41400d1090b070301d6160050462030184140c600302111140106003070030070550240e60f406406003003441917550b1405840c010078003e0052038400d0303103d400590f80303d1102840c003520030340d1030ba00a030034407110912042c03050301040c01c00100600c0e04030000d81070307248a0001c403802c000700c241c220074001c81a0f1400d04c640440029003880c01d4034421010344100107040242245c0d600b09070551503000400ca8400310325207050a908c07030240c02e0310443c0302d0014591a60241d80c8035078070014080b00080d5001404200290142c8903002c010701040b1000c0c841c01c038803100001d070f44428104407164580c11540c0810200f003c0d0754070400040480b080e5002200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 157626456 1250 157625206 157625261
    0x6061204030906090611060402040906200304150b0114030a20130e10060e0a08150a1b0e132706060801022b0603020411070204380103 59
    0x1d01c1031003140040b4113450008104130b03010324146405040020000c0241d80c0c1c0743d408000241000302c8080d502c0660b070782070301c1c04100024441030b258042081d40031560303810705140c01007043e00e41501d4811000d2800c00604820ba078000180320038070060714401a125101c1c605010002c1c10303070b03040c5c041404080400000300041064084d020a25070403481170072842d51154003540c050740803205200002051181030000030300401e444ca81c0902d01400300c003029038a03030b0442d624040c0d951640c100c1b2420000c2c10002c2198082c06240c28034030046039200c080c144903d00103400310440080c0d06201c1d20704100c0d0282c61104503484000d4184880c0705246150345038050f440005008500306803500b03404d00402241c0d104050003200c11522590205079848a080203000d49000c80414003101225107810700007015079614001c9032078000c40294960758075840c1d803042000b02c40801c90341c603402c01c800ca28000c0c2ca80e2240e40c0c50001c0b156282c3c0c40c1c4090003c20b040102c00400c174120354034510746080c40340701040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 157627706 1250 157626456 157626467
    0x3030307080103050f120a0f02010204080303040803060916022d070b09190e070302070212030706020d0b0d0506271515010503010b04050f04060302130e06070507080706050606120403 80
    0x100d81c004c070b080d1011204804001a12154850b4488400d5402004002001489442180000c02503403000504160b282c0e0015800c1d61300035039059038000b0340842444910301c1d0040625401444008080446c14a003844c06906d550342840c1e03510b880c9190701c104c00e00c0e01c0400009011f901c20f0490a448003281c41d42110320301900100426806a24103541c1c8400c1c00c40640c80d000d0951f480c10030f00d11015580d11800f240a58844d0400f01c1c0c0002266002d002520000c00180a03010f01c601c4015880740c10807051441200c8040121030311803850180060b01042c40466a00c0d00b02c0c1141c00c07c8001650b500d4065011342c2489501000c240c0304125161096281c1000c4090060101c2016032691241084c01151140000c2c02803a205040801081046107084bc03100003c0c1c3c3c40240c40800d4031a40c0e80c0004d803010302d90204403240141c50f80b40d1031403812014030620b50f0000150070300500b090099250032015024030301004180568601c003084055031a2016102d030502c54001c03c0d0260710340340c82c00802c1c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 157628956 1250 157627706 157627709
    0x302120d1814160e040809150c03030106120c0c0609050c030f03030a0b010804020619121b030c0305101a04260c060301060c0305030703060b0409090c050402030606190e030303070801 80
    0x903502586422400b00b5514038200e204135542250549001c3e00d5540b500b10b9103a2044560741d0b4022144040c4007141d40c4100c002d029000d0b040030180d9280d42c90010003401500d400403484010303034903018034030306444e030401c003880002c9401450000b0200c8081c9070a42c64226030042440d4144602c541800c0140d034004000c40c810460f140d0b060101000a1005440703004003590000e501c010140590810941003150032090a0750a280030038012828101900c21039020724442c0488111028400d80125014001c0f03400350342142c6010840c81c0780c0a1505480402c1d580075080c0d0f01d0791008c0701034031405d1480307040e100608505841c6582d0140300c615182c6603956400c03000d56450003000100074540c54042c099a04903081911581c00450742503808403520b070b000802240074155164000314901d08410041c001803c03c4040010309615141003c0b032014031fa9900c028803880c0108100a000e032213200940325080c40300300080c003500c00c44600548402d620f1162541c1c1601c0040104090980e00552150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 157630206 1250 157628956 157628993
    0xc0702040b0301020910080c190915020606030304050402090301141806070804030c020d0303090f0602040914132405090319050a09140d0501020408010e010c0c0302120d18 75
    0x4074140040091609070b01030b040100e40d1000c032024500604038003521210382e1000283c09410b00e842e103042031400c600c0e902c1e801501700065540d10280008200c51644040801c83c5000070034103444c204000a0340e91249000b0f9900680e00030070840c00d20b45007500150550540400c0f0400c0710302d002610300c6040c441c283c42c0c014040c806d00700072172600307405602028080e40e010350700c0c40c4187c80280c0038001840980740040b070815641d101880d0100d0039040b581914a44682005a9920b140c00403803010b442001d9a007001d4007140d00709100380100000c4450a83c11740c4001c1d40842282700042d5082c2081201c100842c0c070700d0400b17041095131440030000b041c5400e0500c0c540154031340384041c00c4801e0f0080480c90004500c11000c107104100c40c43d12031001545004155000301601565900c3c04e9820070f5010718800e80d1180f0780b40c40c03426000e002da00070203400d624200e114030040340c80007995101c2441140280c1380002800d0015500f0641004c1407a400300048100140f04626148480018500710789 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 157631456 1250 157630206 157630211
    0x1502010605010c0b0601051602041404150b03030d051b0408010606300519090516080a02010903060c090308040b0309250302040506030a050a1406090703080a030f11030c070204 77
    0x3041d158002c03440d01c01516041540c120709681c8007401504c20b58070890342a0460090701c540300006035105e0141d44440450800c0900580c1054075004510302c900c505041a0b550800e0343d5007805850000030350f00340550035000480c0c00d4440210701014070041c1c1c0801c03002c9410004001c10000b80c150030020272203d00340c0c0c46030105001c1e000919003c0c03582089203540d991a02510304503007081904070607044020303000d98a01841a00010408682e8108404c0b1204c4d0000180c40c0d55900d06140e01d200203000c040080c0c40b460800b540000e19140460000405065940300c100110303501c04c82c4580080d542c065119642d0320340b03a2000304040e4200322480340c143d10032081c1c460002c0f003e1144009100d900d4800c0000c4060a43c0c0c20000544401000341d6018811084d00c1404641d042100080090150015040c2110320183c50f81c10450b00038040182a0b0090b03e042001445000484004056038500014900b40c6103000101038850440118000040031003845454020a4000d00d45684201e0f400c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 157632706 1250 157631456 157631459
    0x60d0903020604050f0318040213051e0306060d03020a1b0f030c031e02010210020c01020d06090e060106020607090e07020a02030a0c050a06140304110a0305060903090108091c0f021615020106 84
    0x1a690f44904650740e0040300f680c2801c0903048c100307500600341903c40c1401e490701c40760319500421822503440da808031001c0c0c524210000c007400c0900c080750b0000d10984803091254115100656102d00204006141039014009566940142da0071800a08001d0401d5544543d603070604080603203960005071290284030504100c6070b0300c0119850030080e810380142c0090544154007030025040f085450401d03540030840202010034071303c81c180252210000008001c0d002c0305049141c0780d0141c10003404c3d0361001c8140000f0781e40041c00d8204403140c420070705c0225929208200d040c514201d50080d05032203120201c01c2041140c22a40090380c4058401940c1f00b9954a01203540f201c07019004d4110440c200042740202e103260030103003407000000d8101041c9076960b540349841c200b4125803100350768001066100d815a4002c010a422410690003041c2c80034004907400c0030300300c0d080800e60500c00b44081c0e0380c00a500034440b08490320340303112089891641d01c1c5110b458220101e20454015441c0c0f410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 157633956 1250 157632706 157632733
    0x3c0e040b030c010302030a06090e07031e08030a0522050a110a12120201110403050c0f09011d060f0307170d0c03021c0c06021603080609130809060d090302060405 71
    0xe00201910020000c0406890038001500254400b400d9140b0f00e54490070085044242806040c0454198200405400d0b2540c107140ca03048000300340f200403501079101248040780b924819a90001d90300440003401d83c070341e00c408481d20005035002d503182001404402052040105841d66058020036103444048203200401c0101c40d49401201c101400c0841190b010902e940c02c0005004140d000004990601200c80000390f0019402180c060703110b91110200e908100d48661242101511421240d50529150845020748443c07400941ca1103180050340c0c66880c81c240b080803144c040c00740c40e0307015240d04090003810f0400144039060320403541c01c0e1040c0e503c00c14401c110103030143d01800700d069140411030f0116a194000360304022220542038086070513407000b0022144000400082000580340240903c00c004000d1b0f0300c184c141c0300400c1803c545614120642550002d011503035484c0907030005245001e0311a2040c40546030104400c01c05400040d40c2d80910b00501c1143e45a101b241f4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 157635206 1250 157633956 157633961
    0x30812010e01050303070809041503050d110a021f0309170c0105061f080c0d020a030b120d0806040b04090f050106061e0903030807110f061501080906073c0e04 70
    0x858260590f00400c1b508001c00e02000c080d01c40319100900c085054020000d0500d008481600300745c50a8000c2c50848405503041004081c4148001010b0284228113400060070b8a416043e0848040c00f6040c401c103400c1c2c8660301c03400c0120f510040070040301c0310004880c0419004101400301345c2d86410007042c51031800545050a514081000f0311031041c140d0011501800007801c00c01c003540081c4040c41c0ea40519002901070340e8181e68000954110501c204035401c03c803507010415035049401c2c05440164880fa1165106400741c40c041441c40803000030400074242c0e1407010b00b40c150074810010401806410001c00c941e05666140292603400c020100710249a1005d200424000501000000d01489500340d000820f41000c0c0d103510b480c200458108061207548145d682c00402c00c00100300703401e810040c2042001e02c1c045002e03142084003e13a0f03415015040d0340c1444100800084414010300079110303404480c082240d4800060a0b142803180c00003c0d01c9804144503c0c0030b611241003c4c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 157636456 1250 157635206 157635209
    0xd0f0506090615040b1606240b0a020a050a0b010608060618040914030d0507080c0406051803070807080109150507050307030b0a090c02030306040f02120a0b01051201030812010e01 79
    0x510103041602e6241c1000400e803c0c4001c034201915080c00300044c00680310018195166004080542c0d0606a2818030111001e00e804c039a4944c0c80746114105140ea0721001405694184480b959510111841070740380140f0f140c00101180705e0044010100000514134030704a8a4645641c20036407a50b030b00300102c42c0074548020f0a8401c03070151907502803410780c001450702d0340148070103c066003102143c28190751080180e030040d00e8aa40a000f4001d50050b031280d0700c4400361a42a040c542024001046442112803008041c0000445040d1360769050019000611170070084502c0155111105406001e0072482544d11008011060041001d94003803c2d02c100b4a40d035426156a880100540080c50041074a64021801e0800030a1100d028070540030b80005a070010b5887e4504902008140c03601c00c0400301e081e40c01800f5450b002d80d020301c10207811626000000c1420306410004813000d0040310000c5d4004480b841c0004240401d543c010261942c25000c01c241c03603a210340c103c48009034203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 157637706 1250 157636456 157636459
    0x7020a03030b010909060e06090a051006081905040510050601020d0c03050d060e0a1a030a11060307050f040927080412020a050604030b072304050907020c0904080d0f0506 75
    0x26660800039109900c035a0707410740c0c1418044c802903200c004c00021100170707811032a5100504402e01405103005081c0a51181101105218070f20b48802d100f15a0076940c45010144042200422025120742c800440803421240c80dc000c1303480c15041c480d5850b20201d61003a2031b1072401021481d25480890102c401120a4035101c0391b0380c41540d0200d0b0300d6807004000c10801130759400c01040d00700740d840d4103074004c9860784d002007024101c40c800c01030058104c4c123005200c1e5100d2603006001944c2000e070035000180450b0050b0701c0b90f076001015201841020601c203803007180001c0c04100c0d48011b62040c1304031030881115100495040310f03022817088021001616012040c00104850160041510002c500c090300c0204000e17602d80c0070500c40d070030079082210400040d1041000150340510240441c500307503940b54001c1da01511100080d4071680c000d45004404540015007501d00030810b5440e1603e000c1d10480b403900e4142006180780e040440c0b02007260b410410240011030740c0d8081c16005500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 157638956 1250 157637706 157637713
    0x30906040608150d060f15051806010203070c03030206070801080609061b09130209010305090a0f230a03020705010305010803090f2b03030504050c04051302010c0201022e0b090702 79
    0x4104080d42c1c4444020502910342508285401d030640b0307000318000c000c901c5950045114008044d010060f01c0c007041c2001d207070390440c0388100255900c3e5115901c940303030080d07402803081d10703000d004134110b2045000140c40c5001400b0004101540060081c2c85210306545805099032241d0f0710740e44604082d1501101a880f2001080c2e0402032911242c00c0000030354030480c44c0c900740c480810001500d00c040076074003540c0807c40c81c049503014010580d0081c41b08018040d2400c2a55a40c2c0c0a0000d13400e028001403100d0382d0003070441d034101c3d00040745c4007185403c032128009a0700d8025914000c60040314002800c0a000003054080041074441d030080043c00700060803a04002d002c01c91070300074011411001c504c01740c401c1040080c101340110174040c0d40e01040d1450035040c40c61405900f034060902443c90320342006080302241300b07044180350782441d04035003202e584d00040f4035001c4080203509442c0030040c050100310a1028240c6007103003942a040c85150801d03c100008a40201c803603501580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 157640206 1250 157638956 157638959
    0x70e1602060f07020312150a0806090d050705060c0d0605040603080702010f02030301081509160b0717070f020f040b060d0209120a1e17030c120901060b1608040308070803040201080903090604 84
    0x10340003600c2e50301032038500307ca00c8112400000580b0807411780c1d1100020350410fa0500c41d0011042c4542111140c00b030416a01e811030030364503d580c64100034403081100d40080f5140290200e02e0b0006401884000c105200c00d0361a4180301a081d80420340490104180183e0b419a041c00403064a0494460038050110310050864900203860002c0c00d10b503040c001e510940c1428500c1d103041078054000d582c00940c5811803031400070760f115401c03810007299580512580c000681003105580245605940e05100d0104c02c0001c14050100030800f170b0b520a10114028083c8602580984140081229900c0f0701d4440800f100f5180c001c0c0140150004034507201c0d401076180b242420000341440340303440708240e8080030f4241e650f81d0400d07aa019255400012034041d028110130025030403066201c000c00050340791203c111790901c52040b01d80320b151072042800d0240600320050350011500036490761f54038442403810149070307801107808030b001c10402d00121310070007400029503c00120280c1128a800d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 157641456 1250 157640206 157640227
    0xf0201093c20010509040606180608090c010f111c121e11040906030503070b092a0d0602070605090d080106050304060f0612150b0d05120705070e1602060f070203 71
    0x216000d000c0030f03062200c2004940c8154482d03202d181c000f01820380d03c0503080d417082034030350388600300d02d60000c2c0401940d5000c0c0540712102040f040201d201c2401c00e964040c50000d0182c820f401200c2144406000340034000341811411640c4442c1c045880d03175007201c0d21012207441c204990513038662112070b00050300d4141c80342c12036500020383c415180c0c0c807281c28103903101040c1007500d0b0ba9030000c89068002058540800101054050b08200940c0252995109908402e2039450444512030034001c0040c030061400d807a801a90031040390026030a55464015040074009048152586080b42c86014080028a40700700b400605840c100d0f0b940c10f1842e1a1610340030050f0040880346100150380304000110032101c2c000524842e4441c02c140c0c40c084601032015402c80b01e400401a008003640c241003c0000c00101e4294402e10781c030000c10340c4800c1c003030800603d01f003250303003021015041303280c203210031407a070f030511000340e040142c0c01c47c0e0031590b5414005c101d00006a400c400940d1040c072520080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 157642706 1250 157641456 157641503
    0x504060e040b0420070209070813020918010f090507050a0602060406050402030319020c12010507020a0609050106050306101502120909090c03100207052b0f0201093c 73
    0x110ba0028804a11440542000d0803020002d889152074424001a5a000c40c00c100e061a80c0c04a000d080402a034580300c0e801e1000107824100c002d02c00c0191100056442c10032040301038400c48144002c010702c2031345a80d1b80703001b0001504182c4041c0724110000410340790411110b030907122943c0c040c100c43d486654405000c5d010181080340e0502040c000030f4600040201000305015041d4010441d0280351410300c0b460b02c4030003800c2074480c0d06040410403031a0b000100c0d284042e51080f0002511642400c2213801448581c02c05585805218280413103000c90901c484144d6481000344520300485000c1641d07119241140d110100c2c00c140282082440d05951a03a0300c0002c040c00d4420115101c2c0029003848501c1640000c6158042080c9091000421400003440441c4030300031031400b8038401c0c2440c0c00414070320b02010003820000682c5424400c0d00160191913000361015441c891404040c441400d801d00002020b44250040300d806c95000058800c80c5500421500350006802d10035410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 157643956 1250 157642706 157642721
    0x51002180a0b13061b05010504080a030509060126240f0f0712020d0b03070b18031f1d121e030601140d020906030103080706051b220e0f0708070504060e04 68
    0x582c450402d0031714080707102805600e00c0f647c45001402daa447c0940c601604840000c0c0000d4501d034802401071000c80d0034016880c1d21a1500c80b68040410000c0c1e41051500c029a512403d215202140c0d0458100c003810b00207000306440859034882e5552106070030079403103080794110005a42841e601414403510390040281c00c20880004c03c114802c003000c20b1500392075070b0240c41c080c000060300c00666500f009001000b030000f200134254828407004c9a4001544d0310404a03041070703841884480000300c410000610320300d10b500b0380d4491440b20749181c929400020a000711400d0340c141d014030401400040b01d102d902c05071190354080c0c081c1810000150495610303000c0d5160f00300300d4668280c1d0754001a6009501c0703100326030ba5a501c140b40020540340302409022082601b010131240c25681c040c25254840507200300a4009030040c000c00c141d081c110b80c004092440724000b48500340040004013071003100103880d180e6254a88102c01c40b40e80c4035903c6080000790211518440d1840c0c03a800654 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 157645206 1250 157643956 157643987
    0x2070614070c0b06061b0601140609220204031205031e01060c06050405030d060305010b1009050112050402030106030206120609011a0f030a0e0706090e06010921051002180a0b1306 79
    0x504100401102d01b0181c000c507468007549a1003840100800c40e240c1c01c1c1414180c0090304c2007420045447c001c13444030301c072101050007030000c4a06039291f070112660507200115004940c00c50305054840c6c010302a0390094408025016445442e40b100b020310041d410704880b0180d407901e10105061303c03a8002000081c0c0b084600d40007c0102030144641409113074091402840000340f201199001c20041d43c441410f004240400200e00300b14030ba03048601c121286d80c03200130100d03860b0750320b100182c014001c5d604002d600501c01706044a51503001c8550601c201801c2e5209085a626101455600030710b03129500c005d94010000a0004108000a19040152100d02050324000d80780c84908004040e00a40f0018041800800405150801444d00b0000a00306040c900d820007001d10300300a004c5018040741c103038800b0440c04001d800c0142644250050b84119190030310300c3c11411070585006000c030f100708180c00c0081580800d10048681800242c0c543c640f1551800b081170703441003013031420b82 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 157646456 1250 157645206 157645219
    0xb10060e040c050711190f0e0a181223070b070c0b070318080703051309110403080a180e090d03110702090c0f13090e30090301020d02070614070c0b06 66
    0x2001b0003034070140c4a1010340081c040000c000d40c10300c840c080007048000c03c0c900c862030a00a43d4a103c1003280d1000c0c1100340c2020345815800309004083c0e03100780c2030503011000000c4081c19181c1e001210710203403150030300c5039000071020b032a4000102c2d440b49107018003418564108010980c118000d5110710980d4003070080e20118456152101300341ca0700164015004100c000a001c0080103039003440102a2030b1401080004000d0010035020b14041e600005182100018024a055000e24a16031002c12041c3c03a03501c2130358481c2101d0381044819a903298039445a01621a191802802100b80304024903c6050030080184c08103c2021000b4100d084490001c02840b20442012002800300040841e0700d02d000b036190410301011181c0454240c403064121008941c2050804403a840c0004401640159052040c00c0048803500c60411215071542c030004d0b59040030011a00500708580c06031004221202000505411482044580200140c10985c0d503000061041a01540002014142c0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 157647706 1250 157646456 157646479
    0x51f140309150901090b220303020a1e1106161b0f0510020901081608041704050607150609060b0301090e010f0501170f010c05090d0f0b10060e040c050711 68
    0x80da50b031100340c2e1140c07407030794455403603505000c0180706003504444c2c5100c002c094040e1581e002e0002e00f610000c002c003010340020303072007050b180308002c03400302c0c815810182c0030392040011000d04210b84164403581c403405880000340c00c1c0914000341c203480c80d0850303c03801c8103a1900320070343d07500d5001c9001c1100c1552600c000350020030400c101c0c214201e041c0d0300c0b005070303540030700301c00980b070403c0040c031010019648005c0c100c0d9482c3d00241503508554018440fa00c10969400f10202c50b0180b504440e40040d00445d400d420f1000200d4a41d4080c40c10358020405c039500d03030314003000b620542d000303038508080100010000351940380c0c040703030128440a0000520801241354101070702c0d02a0b010000443c8510100350400809001e00940f070388000e030007003109154034034010303203507028083e0118805e001c0f01c814003041c081c802c0c3c90b050f1801c1d0300508501d01842c00c0700c00140240c032507018071000501c1c8800d0b8a0340c90b0800740314103982c0c00710503122a030510315596908681c014201c9031041d0041212000f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 157648956 1250 157647706 157647733
    0x140f060409140405061003020f10030b030f010207060608061b0c190f020102100507080610180308190309080304020f0d060e030405010311070b060105091503070306051f140309 77
    0x505100c0344102450000b15003081e040c014588100604101d8900346401020001030352004031554909a042d11700e55180c0d140c0c00410790003441112085034050241ca0050340e0303110b10660040242910810080204a4840303100307503540c1c035003103540c00311200d402440c85172854801070140c03403004091402c03159145000b592440380000407220407074580f00415440002c66805110301269020918410419450700420040010070098201d40c0569691504140c09921521400c00b4107448000c03402d2203280c1c0c0740340016040d441071202d044414110089a60821310a006900049410224550450b01d590f02041040b07d01200350b107078800389001e292000510140035064001d00c0c40c101558039a46840005000e80c1c02841b1590714400d001c12a02c070000c0c40744074190b508034100f0710b025a10b4012520100d0050114007003840c4902d0804410003c0c0d4583c550040c0080c4d80080e40e184601025400d81d1307038542a40c0c0d0325a0b0300070805512034102403446840c0903541c07103e0420300f2112038021007603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 157650206 1250 157648956 157648961
    0x706080105131d030403080a2709020d0b1f020601080a0b0712060302040e070602210d02090303120406060f0b0c25050a0f0512060408070303020904150e0403030c0504140f060409 78
    0x7072081f1a801808548220f03607e42000c002c1500c401e070b04070100c258042c6031849c01c071084640d008030071409902041403901001e19a01001140c80040e00c485442801000003003030344100826032200600c07412001045920300800e00102069100b03000304400c2c4c80b841001e80d44001d076554001c882c03503601c15000025948900031404000307103003009448614103120000f41040070ba001c20b000600a04000050007054140891b00c480ba61039000507201c81c41c0c3c4000038298882c060056000340d51140901c81402020352101040310403d01e030700300b480c41da070300d51126607409072540d04106508404080160b0314101c88141c002c41e21064840c1c0c410f5500c5200040712050142c020321100c1c0d00040040c40701d42000c18080b68106220002014607161507560032005115084004080640106441c2d03841d4132107030060800001411303040341c80240c8451800080c01c3c4112400e500207401c02e00300b06101c2c0c2c0600c0c02c4405850300722a401e070340c90f040a8288642201e11072242070304003600b0040000c982d105032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 157651456 1250 157650206 157650209
    0x310022b020a0215060a0e041b0b030109061d0103060902300f12040501050a0909140403020c0103051005190308030a1508010203010803090d050a060e0c030706080105131d0304 77
    0x4260040c0c41e4040b41c0002490a401401c0c071040d400424020302c009030340c40c100d14a00b01c03500113072054030f1561145131450030104c00f80c0c4108110041a0408292005040065416a501e446c2d08205090342d0792001c00b6a120301d006c5a03100001c5000060020a0168215803200c40c0090035400038130321014040c0c0a400c0724024132084448900c80b811010950903c06400c2d004025402809202400c0c2001e18203403055110340c5051102c000f85000c0d030a070084080341d00409a4100070000d001a000300c40710454402c6408070014020103140b140c456009202d000d000d00001c190481e1054101814001c910011803600d1020007c00100000040c004900840c8a40000080803d10307070341303090070814058a160486241d6900510040c411903400006440411604642c1190b030000c1d54282070781498000840906a2401c00100c4055480c0004455000307280581c200e4400f55540c0703104558146c801c0c040d0590180103118070403100c03101d40c3c0220000c0c85800a036a0030010b00180c0745455980107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 157652706 1250 157651456 157651537
    0x150f4809040c02030319020a110a03030f051f030b060117011e0e010e0a0f020702060a0207050a05060a120c0203040e040f02100905010c03030e0c0604030602070b0c09031002 76
    0x902100d660501d409903000e081002d0009508500300a40c0c10300d5025541000642a0390b4049000c200d503030300c1400c0360150541001c0c280c40c80c809072810028081c20202c00b107a5111070409010600400030181d01051010201c18201491411030356500b203860f6000e00440d040014080f09003005406d040050f074000c01e90614400c10f00250341d034540013449440d501031420400b24000401c0980c1c3c0c203040c43d0381d115010200001d550710314401c11100902401e80080e4206a02060503001d59400180400585800710303120504039a84208000c0c15208010700342001841031000f100103026103070000a40c101c1c0300e0050340d0502d82c4403941c134076594000b15020b0390090040725170a0150704080c000c841a000062034a00080c1c1e040c000040d120070b6181c0e00c000c040554854100e62200d070306019401c40b0701e10003405a961103a40b4142078000c0c1d00041400d40e10501188003050015502c1d204072542403901502074024074040071004c1d4000e400031250150090319083c600d104141540510413036040d01c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 157653956 1250 157652706 157652851
    0x2212103090c0103110a030c210506040f0b01020c150702120d030b01020d0801050d0c090c0e041d21090306040f0302060a0b0901151709150f 62
    0xc2825040b031414011580b40c6050600c0e01e01d0030650016080200c4501080342d09012038a075250480494814801440400346402c0c14207284e002c0640f1034000318001e5100f02e500740078100740c8048e850200d540508005000d0f074040c1c00203550b241071119241f80940c2c0900104c905005494001c29400300340000c02c11001e4000420601030590544034a421a000a1004001d440c6200401402001040c0145403181488032440400c00c140440707032030b01a1100010902c06a840c1d2200a86220b8034111701c1b078480c608003103900c8440d000b103080215020301c585004100304100c40310440c2c028a811002144c0b4110b0070814a039843c0c80c02c018013030103580709070b0fa81c120f2a84103040090600a014007018402c0b400c103d00742c28150f0321690454159500c3c8149600010320141081c2d43c003910b24008100700040c007608000d15190041064801e05002d00c203030710110b6a0792110444902e80403030300b51700c181481520900180009501810390080303220340f40318074401540340c4030b9005c8036044148154043c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 157655206 1250 157653956 157653961
    0x30b2e02070f03020a090b060c0a0c051c11010302070f05071202040f090b070503090106080601080f0f07060f0c0212011a0a0518060409020d0f0302011505090402212103 74
    0x29030400003640186070341c9580c040da0a04550006088a10b40d100b2100e14075220351413070030150366050403207203040c3d07483d01100d0342c8194524015a24002d90320034144105001c42400081543e81c080c0043c206502124a41140d1410320041d03000b0340112100350782180d810514500054000c00c20040a41040c10f14165416201d2042209560500c04058100d606020740840068180348406402101a0034202e0b00ca42e500b01003d801810244d00603009441000000207c0701c0700031480301c0041c01540192190898024405aa14403075445490000341c089803691181c10310a15a01314000e100806e030150702401e020405080da03861a100380c00704070025107985854905102c004004041c00e5901750b081c0c15440b004075000f100000d0a203401291941d901104554601003282541907200c102c160b801b03049403c00900a080c000e020714181c00541002080f02c0c540601110700c502e900500d03804098000381100d1004d2410304040084911400c1010f513071101039040e02010405e00c5e00c01070341c3c403031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 157656456 1250 157655206 157655299
    0x100504050c10090e13030e0d080c010c050706050c0703140f040b0a050315031603060911090f040b0f130f0c05030d021f0c0804120e0301050f0711120307030b 69
    0x2640f01511803005170f203003a0640e100181e04408091076a25049940f0f054215007810069998405c1c071101300495440e02100600c3ca0307030085d0182000703900601082105961703d803011002489490009400b0032a11007006601940140040c550300300348440d0741303040594a08030002c482d0024010a40461000300401400c50803428158501103002c17401800c90f11015000b0b0100e5600c0350202800c043c4e00e82d19424240a1700350290300300c2050207000e1902a02e030125084a504006031000c4421300d0840020414601340c8840442c05a41c40c0003035042c00c0c01c1607507a61001100d031060b00f11210400040300292702c2d034041c0010103090140d9000380c901455140c1c00030860203081101d0550301440c00078880d0580354404040703540b042d0720804c801040f80f00c0300005d580d50081200c00340d074590b00346001c11114058200250740600e10a4a03612083d12103450f82c0350b25203100341400c8400391020300c00648a0303842038110366511100a0000b55044c10751b0030075070f51285000154040500c45440101c1c020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 157657706 1250 157656456 157656479
    0x6060a03090501050115170c0f07051212010608090703080316030f1a28091503150f05060303090f010f0c05031b06090a05120702040b060c0109060b060c100504050c1009 74
    0x28201c001c9020a01c074238101d0301c0c0c134505009134400001101c0300404d4800400800300030360321408044441c1503403900425104585180b0090241b0000510780c400490000c003400525101a82c1d4005902c43c1035640300e1081442c0c081004003080304150300c0303076044180c942503441740400198001d4030307403051584c403c005e0004042441c640c50210105401c5030304080c811500c42c11054465140006c2035403200842c5070b034a90300443d00060244200c00c4004c09800003148d00854268046070303024400769031410109901c134025500115003042051340350100d03943c81221040249407031800e0003600c00300c0a45031185541c00c40d44a000344d0301d02d01d0b110340100e048100b1200360b1150805c8010f049010a41c0c0e65070b9110b5506590b54140d8402c0400ca280841d504c82d00901a00440a80300c04d40b100c012281460203060403070006d440213031828800a525091800455403080c03401e03c010010400c6e402c020200901e002041502c00c2e024018071307404580d84200d0103510314080b03503841d08041c0e800c20240c000c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 157658956 1250 157657706 157657727
    0x4050105151009181b030519090206070b100f0314070909121218050312060402030126010f050403090f06020d0f051b120c060c040503030306060a03090501050115 71
    0x411080146000040e6600a2240c01900e130a6a141d82902d9007020780d0b031000e0160b13850240180d04400015082551341070b4001489000c0302d480489078010320f4002079040360100100070f500f2820801013440490054045250412039070070030500210751301d03010142030b03103080e8000b00c40d036840e200c05d08004001c00f00028030107400a041c1c2000440095a240200800c1c0c0011920510407040c064010b4403010358498042c80e00140f02e1700c002d000c039525249484e5803240100c03d0704421a400411a181800d200744c9050320f5446400840e000b81031242c0400b0548141001c00e80d40d0740b03c440300e440700e100d1800303168001c92194a036024a10306004441c501085590000000c5501400d04820303030319484001004440380f64203049a413041c4072000000c503825011080300440c0f1901e85c04a0010301280000e1410b903008609480654540c60108503080c0308030f100300c3d40d040c2e00501c0401d68510703042d001841d10501d58140052800120341d2864291002644211114604546a80780c4c40b5008140000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 157660206 1250 157658956 157658959
    0x903020103061d130302010204050d21021507112103060a08010905120919030339020111100603080315030c0d06052214070b0c03040902090d06050405010515 69
    0xc0740c1c3c400e00d00548410b04010501a11079081040000600d4001c0d41103e02030031010707040301c07466030460600108440960481d00714480d819115141c101d440400d81c1d0040b11010024034105413034200b070884121086004460003070140741c0d90002c0350302101c10810048031003241c1c460740b82d15040c020010805002c2c1c0c000f03c0303282d043c0780000001070f0001c1005585c6e001c08200703644e180c4d59510082140c80414800080903143c290740040300b4160410741e2803842e50400c50510301d1203003c0115125410358514451040c961050300000010760184001e5802810401c080300c500081c03681c2d450058800380d6100740c414210001c1072000c01040903000440000c0240d00400c1c03d03140785004650400100d14002d00f0280d5100d022904410740c1c0c05440600c4003461818030f180b0742040c00d00b49078000d01070495105a1085001c0000c22a50207800e454407503a000d800740d4201480d00c05d0a201941c000c00403260b00200884040c400a0520310400d80904c0c05032000203103524000b08414640180e0350080c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 157661456 1250 157660206 157660229
    0x70f1e05031207021516050c03012d051e160f05031306050c090d05030d05160f030c0207050604090504030e060f0702010e0f0402070b0405210904050414010606090302010306 76
    0x800c1d41c03600c0c0b001101c80103a415503c100c007102c0c0f2440800d01ca800342c0102c08071030341c01c00380d1803506011001034150041c010850003042001c4401e20003440040c0542c10140088180340082124803929a004682c09441c0780306a805101c1a27503040e41e08a4011161002d1691815581c5007003a40c5c0480700101a08003070805901e1401c200d13000940c030a00c0d07000d00038003880d15000020340c500f02a10980b09003a04c0a03040da0402d201c1d0b031800c5502d1780c001400b050305c0d5a180000007600054a00101d5818200e9030b180c040302d12211030b60440c00350402c08003c1007580305400c00011750b5150034004200a00c01541d00141500345450b00034403425026410600c80c00d820320107100342180c50800c4410f801ea090034074090350b040303200c04100884052801968403e101051400520a22000440c8541d11503015101c004141103110390342d000181d050710080b40c200b131284048a081c82c0c0c0c041504240a6260018400c066480c2c8a080d05c5060300308000165252a04008550b054052000a0094403820 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 157662706 1250 157661456 157661473
    0x20a03120204060e06090a0509130b0f0f130c0b030c0d0c0e0609010e030114040501020a091203020a0b150d2001050702030307020105070c0306140f09010b010f050c070f1e0503 77
    0xb0044c00201c241d10b889584002507065540d80c99103420001800098100e02c0640740c41c40101101b10400d42c801d5400d0005180000d50701c40c80328100a1050340f001400400030b40f25003060361801c001c4107030f048038900c183c41000b20b94419440003039445003002681c0c2d142d45030300350309003c02a600c5100c0f659061040305c2118118a0752000240c0358821800e2034000780c400034050000b800340c0780d50341e0301c100e111f2450b03410300c01484010740060203065010b4542c1c124072a5212030a040c9509540360280c01070700103e0807040026240c80e441c0d900f0084001d440080c0301d06010000701655003c8030210707800b031424000340c501c503500156842c4030114242025402c0601c113802003034880c03044200c001c3c100500040d000c0200b00801c41484007840c0c21000c100300d500d150a200b280303a40c0341a14a52480702c1c0550000d4a209414003400345400c1040c0d4900c04c3c40607528500344e0b101d8000c0643c0207414043c0c40e40204104611b000707010700429200f0381082c6002e001c081780218081068000e24040d0308034090 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 157663956 1250 157662706 157662719
    0x290d0203060402010513050d0804090b01170103080f0f0a0906030b22020a03020f0f180609180601030b030f01050f090a1707050115081e0715030509011b020a03120204 73
    0x81c038661080c0c081c01d00c9070341d844200d641c80391031a40c0c580020307038000704000707035041482441400390058988e0207600b0400150b0000066800d80203c000700d02c880a030860043c00040c41d8600608000c000c0c0c280314900780102d044070001103801403c00040051071484040020680c18013401c0c105000c161000d6000d01c0c0b8442d00c0c2e4800c03410001d4802500758001401840a501c41c2d070442c4d00300319016000c191101c40700c014100e480d03804401e031519400290700200501d40741040880d440c01e40c0080221440030143c070f484034011100106224140743c0c0e107220742c080307546080c003114109001042c000500f62524040e002940d50000d402061182e100c1c003c618006900e20081c00d00788034040da16aa01d84606140c55400341003034410056507024007100001e044540015002c4465100c0b880c020451501502d00540c0c83c25140315040b100c0c1d41500d05090014082e07440103420528650000c1840709840584c1185804451550742c0180d00501c0f014090661000c54025005000c5205501c2c0070715009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 157665206 1250 157663956 157663963
    0x12110301050d03051821010e030906040e0411060f0705070b190c140102040314010b03010b0f011b020402070c05090c09091611010501180e06090307140709290d0203 72
    0x1d0018107008000843c10301c5d000416001d00d8003200020110515440c81d42c0482e038054100600f500c40b550f00b41241072500300ea0110540f030103820054602810280380070b41c4207680c0b5a000d030055804210b49411340c0002c4e15000014104081d80b917001e0f0b0340d00e4689291144c60110380d41c2c4401d0428000f0720062601c3e001c005a00b200c2d0410524042003c074440333091401010540b400054911361000400000f0040440084c036086607a284c002c021140080c07007030500340d40054400d9039001001d40384c8400a5800b0380b281c00401420031091310b1100000381d0200c1c00701c0c0e0001c2026904a85030241c00c100e245040b40e5030035400094224403a080040d80004030380d1004024008001003a2080e0040d04940c1c0706200107400c1c400c040009200a50352a492509000d131b14134241c0c048242004021813031131600003582c0e4010070b95180218601746540c0c6400b501242030380c00081c00e5001d82c29001075058068083e610038040b41d900c451610b000c4117495100044403250140e0300070020440d00401613079020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 157666456 1250 157665206 157665229
    0x5040b01090504140307030e04050f070804061a04060b0d05060105070c060c0f200307050d0803010b0309010914030a1e0807030e0705041104030b010e0903070f060612031211030105 79
    0x58078003250039103840c604010003050142c0b140005101c080380d4803051652010041c1c6040c0d1055038200582d0306da00b140d02a00881c01c0360307104042a20703100400c0000318198481d4140025012903070f01c4c800540000501502c603c0c1d800710710200c0c0045150010340c3d000b485a070750040402d01308149041190750b580314607504203100ba0005d0000c46101c80090108886451007055030080000074440c05601c056000000e8a10440c3d00030702c9040c00c0441c19007042c0400c404034036001994541940e1810350200090340c8020300c4110555269400c41d00000e07051011800b604070102c015580303a03981101c0040607840790000000c0e6200202c0c00e2540c1d140c0e0840e0005401102c00d01e80070510306510101103240074050703171006070001d1a10201c489400d0b0b040340074000303880c0b080618041603640c0b200d880382c002400b6a01d14200c1d070810000800011800d90422805c0ca11130b071000b0500a42c0c80c1110304420480c040c054020035007155510300d81d5142e40c411600034022100c1c0c0d160840d4141004103d14a007003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 157667706 1250 157666456 157666469
    0x5010302010903031409040e0105091231050301020c070602100b090109090f020303030109061701020702010e060c0114011401020d0906020d111f02070b3111031e0c030105040b01 78
    0x64043c1d0300170415001c1201d500e810058024020f50744d91401311402080126038659280c001d5400900404511804544007515401c0c80505a0411007440080707581104030009148614020000703140c3e1406e0028005002100c0c0c06004800d250000290038490146441e80704103261142c141c0095442018080c19640402e40000c0c081425160041d00e8240324600a03505101c0800002049500c5811080039a8a400403b100207200d41002c51b00340c1c050050000c0c003280b138140d11841076060a001411082040c0e80022500390100c0b169115030703000c2078100108100c040381d0107408558040004014050301850b1250002d17260140081d100c0a40d002d201c0b013000803100b0701c00c1051608201c0c0500d03004042c40080c4040e508200001d0080d0300c0041d044079868005000036500441c41b41c442202145196032a0102c141c100d0805c480703145540c1400c5030808a2410407a003643c80030044c4014450068040205c6500c120062918062001c403440c1d100f60f04003410031000868110805045480 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 157668956 1250 157667706 157667717
    0x140f0f060604210f0c1a03090a030c1b030b04020a06230a120e060a06290f040e10031502045015090904030c030e031006030b06040501030201090303 65
    0x100d07001080003070f6040c150080c050090358890b080500c10030034810800c540b03a9011105400c0111007020140e800202c0f404003c640240482c00c000c0b90040340001d4045200b02516404040e21042060614000303410a4802c441044200421424811400c001410b001e0510704045044004c13200c5a02003001a201c1d00000041070503400540035003421a0782030b001c50000c0c44a003009040040d5500302c1200c2420442e0f0602c4000a0380800a10a1344e407513450040c1010384c06c003003408404005501c003c01d00b1036949420000012403494030180d890148120490311074005245091015010948811040f03a039441008200400c22010940200109544165640c0d48034a00c2d4440e41003a000500304101103841c140070300e20030450692589205508071091500c4003241951480207000b515a01a088600c410115004c203005a0685400910a190818004400fa404282010209000909000d880d46424410400a1200302d42d109105640c200810b61440c0c0008141c60f01751310029082c0103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 157670206 1250 157668956 157668989
    0x418020a03050f390a030f060504020405010507060510180f0e0f07140a0f060c1506060e060c011e140a0e070303270b07020f190b09040906140f0f060604 67
    0x11103a401ca403208044100c5961240741104010340a406440d644d41f06451908002248034a058408d071801c0cac40c01a511642001020341c2ea101c01000b01400d800591840c0740c00014144200480982892105800c0840c400580004001c10303642101c2490081c0c5e009440070340d074006030000c0c132071088400e41d5482800b06440740c1e000c502001d030305402c062400408140c0114134142c200c45c0602c1400d00c1541c1819030b0b802c0803145902159428000e040014020815204481c50800c0141002420003030000525501c4090301ca0704491505241c000c071543c840003400210301201aa031503200e11440001d1141144408070592184034601008051040a448160000c20500112480c01030103125007801c80d6140c0c1c00312000c540056000700d10031201c0f1704201c1c51504040c200141401c4082d54106a940d060180c40c2c46903401c58266250405c1e92411002c2c08903101d4000c00d40800d003424541000d505110111000601c0d008040c1c00d400f5020303500b40100c80d05c03410101c0302220580e081f81c84040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 157671456 1250 157670206 157670281
    0x203030d0f021312030801090c1704140d08060a0f0807171e03090a082e020c060f060405060114030609060a0e0406060e060102120702040e030418020a03050f 69
    0x240070f9080c07074091226040d000880e0001d02c2490761480d042c01703915204116a1b8841303180050301c003040940c1d030018062040004c0000212001c040d0004d2284104040545020520500c1c00219000300c40006552409000307107403c001100e54040c0441d40b58071031465051500e0941c5da00c0d900d10901305c54500e800d00f9103185e0742d4180241c441040092020200d614609689130360390703070009207145216000c42e21001455280001f03075051050411b860000350002294101c90b1748079601010450b4007a0200150400b040f02800202c0c41075042005814450800005100482d0002458035050144c44501c071b400080400094070380c07022045030500c0069940002141d8001526801100c0100c0504140070411129030032080903980c0080e60441941c1d202001241d82d14410000c04140749020044400541042d8010f488a00078540c1103a1403e45c1d600da00404100704d8900c00300d12903034007140c0c0840b80390303160003902c0e00b0401c00c40084003982460000c1d454a50031001c220201e01080700340d081c060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 157672706 1250 157671456 157671461
    0xc08180c09060f0a03080403060c080105030607110f120c0706090f030b091603050a05250e0c0903030c0f0d0507031407170f12010b07120f0c0f1203050a06030203030d0f 74
    0x7012400341c582c5180c01d036240b42c60146d503003280c0801c542d030724105a012816144102d480e10f04a55006008084a4a49903804d45004c410350542d840c0300d0260344401d000c8424100104c4020706508a082e55a03507000034a02418840c3d260001c40400c040d291082044420040808042d2501b090480290b52154440c0d1860104007112159080c681140e000080c001c01185120240740160700b1340305d01d4400840b02c1d00180442c01c03162603007810291000d0241580f5800081c3d8000b01e003d0039980340c041000300085c9150086419800942e001c8079410700c0c1c0c1e602c00e100c2c00c00080034504100b400d160780356601a001c010800784012a1000101d0041c050180b1681840501d01d55540b0387d9a55500340d030b10b00d002d81d44c0402c0c0e951003a028550000119000306c202201c0900da0000d1404141050104003241e02448110190040018130480f18000c6140301e425040d060788a641c035410303000408540078055a80003800740b00d000745442800c1001d40c03408001c54900d1050160002942c4491404a500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 157673956 1250 157672706 157672729
    0x18030e04020304030f18080d030507030e0606031c0201090506010e01030c08060106050708070510090303061401021504110d0c080307120201090309090b0607060509071a0c030d0b180a0c08180c0906 86
    0x655110b2607230190131a42e05070313001a00825290740d003417081c6150306040381d641d5003042e1a202d030185c0c045c14001c181d0b50150b84032a00513414078400402ca02c1b05a44800345002003c0e0400344101c200400104100203010414100811010300074000c19131604030058500d00480b4000390010400190300c42c10000c0c103001d03504000034111010452070f50340341402002080301cad01542c0c804040420301400325600016500d44040c042c01d8046803036542e03c1c0d403000644403011a1554119401c10b48050010f144011280040c0031a60b0040d902c1e9509410910301c006140c04a110641e4508030200020a502401c014169100c1d1580031420041e2040800e015100314080030b80b010b071801c802c0c001d07601c801243c0d600844003644851500c10401d42e0010b00d0318410b40d400003a040d4801c0061a0382001140c001e02c42007000142042c0740c2c2070f180e6548001e03454007244c210700302565801c0055400342e0440041a044002c1050310031101c400d11484951f609000c40c2c500f8400c80c0f502000480640e07600a80b1038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 157675206 1250 157673956 157673969
    0x18120304080d15181a0d0807081216090b09010c140d020a050105010519090903050d05160914011d0a0b0412110103090b060f040f18030e04020304030f18 67
    0x1c82d0039014800f408070740180c0c415104070803441e11501000e40940c1011a48801d811241440c00804104110745c03054000c42e180c02091003210b0120b9050f03005044554440b070311000c00c620380f02c61802182c0c14062008818001d01c58018801c6040c590b007500e0140c0000c1c203000307205502904101c4007107441000304448600c200c202035591543e000c282480003900c690002e20032a40c9600802c10002000103080c00a0105100c04011605858200588850103410503502d40900300d592902074400c11203180380745480300000c0103507256000d80360310014075914014058000154000a11006020840b21502100a6405507280d60f500009e240203201e41000203660b0f81d81c8000c1c4414664075100305a580f601052602d1006500030301a2001003030740554025025502e460030440c113108928402600a5074980c1d0000c41c1280b144200b90320840065601711070f6104d9490000e1000d46080d00250180f0700610501002035000649079500d10000d007400b56900c20441111500300b0015807128 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 157676456 1250 157675206 157675211
    0xe04150e150a0e01090b18060a060501020a03180305150f16140c010e030a08010f060c021815131d010b060d090f050604030503180c0906042013090518120304080d 71
    0x801000700d241f161041500c1228151111a80d0380c03c00030003140c034213108150168016004020010b40b09140c5c0c0307003c24642a003c0081b0b651203494441c0740015480d04010150055000d110004104501180c0d010700d4015294110300e2100c174001307000054483c140b020344007000c610315a81039001e4101c500c0300300358901125102d07968904d0003000703e0f00a12400510138119900803450b540b04034000f9503603c2c1c019180c400031a11007035841008030702c021306407180101c00030304051041c0d5460300202d001151028000c121441e460b0828445c1c4100200312440a03031404050101c07070384a110035110a510104000a4400c1903810050300d01080b114004046000d000c040004054008002d035018a001c3c95800f10080360300001103035503551244404c1e90000d9000001509464960040c030014041a000b40952228100b1051519001011011400e45c282d02d803c0c000d08281d0310605030b200321608810300d00141420840e90700c50404034600080200008001401e00c0001405c540080300340d0b2804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 157677706 1250 157676456 157676461
    0x30509010f1103060a060912020910120507050a3302030906030408180d02130c02070504090311012a0804030c0c0305150705040602070605030a060e04150e150a0e01090b 74
    0x220b01056108a0f031852041045a40100786035104001a0044d0340c851502442e11804a400700642018010702c901301906042d5804100d0000440010700b545120360f004066160800713081048240c03c94200400c0c4502003013410014400c8100c4450b40703410849100440c654580b0350407401d42c03003420800c03604007000005000810003c07000405850848920900000d9000400c10100018410000e503019004100c05010412541e1240d90b4072040c500440342503d650301c000c142540e0015000340c000c154032803c0ba000302c3c4028003d8040703442d195040481c0760b00e051035000e940e10100c030f0800030401018100140801d0b014000e540d034004d0704980810b10240c0e43c0e161266542040001400d00300f001c5101140920780034200b80ea00340c0340e10780c015000c980d0403c0001c46132900002c01c2075490300d4a580c4d000ad00e822502d118640641d000b284c80600310940b070081c3e80195030180d4621440303584104803c0b030103003070011038483d04a5600d0b4800b00c0d00b10025440680907101c00f100280040d0680781c00e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 157678956 1250 157677706 157677731
    0xf04050d080d02070b0907050409020906040203090106080f010903090510140a090b040e16080603060a11041208090a080714040f02090909030a1205130b0c07050303010f0512190201030509010f 84
    0x5107210700b0140040351f0307407191220148019120601d40081d080034684000c5640c40c0f42940156074800034070000001c46a40d6020130740e281203082d04e124501039648500302402d1550201d45500902001d81781d001c405002e0000040c00520b44044800a0110224880d804544110740040052900801560300c580c1c59208c01c42300603030190f0340c1c6880d01d042d04c00030b00b40c82ca0040d081b041c030400c2c0003005082c007039880d40084400303403144140d200da000700c00b04008203920107186044020700c0d00a22038152540d2405003800701034070310381c8c10400f02503021507810041c07034004a5000380f41c0001502c0101e0f1041d11401c0d2000a4010780004a500080200070410491000009800b98180558400d9400751007504c10740120b90003a50301580502640c02c0c03c10118408540040e08001496062854584540c9500d402c540080c0c0107600f585440001c10080c61070070b00002d82c428100d910182000b800c0b01d4000410301200001d00a040c143c4503400900742007021b50205800b1500440f0502032501c0303403030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 157680206 1250 157678956 157678973
    0xd21060305030d1a090103060b06070609081b1501140109080312090c06040e130201050702030a03090f09050f06220c020102070213180b06040207060e0c010f050f04050d080d0207 78
    0x100207101e84e2901c01a09600e000c8500d149080e00c07130141c28460070741d0842d140d40006d0301008100729007000c01040b051002540c288035040c540d601a10b40c10380c8903940e469007105036640400b20216142d00810444203070540740c0018038119000c1c0d06000058046040040c4c8210a199100c0a81d5000108004607142b0504500030303ca2001d42d400c3d40d0a0040034410040e9038091030040c2400b4480600001d0b81030822603c501494070b005042a508090143d03000074904114000c049000810041080003001c04903000d0700c020f0000703c2c0040c4580d2601d100032000303429008003458070400444240000c01500e401051079405031252040c040c101e4000d03c087d020350301580301280500d0100309900d126003058031032104004e514220581100000780c403140c203031440c054141c560240d420445080041d2051084d61500c0e8003000c080c0c030040727001e83c00150070b03982005940c00502204101e0b0714120325021086609840085a0402c035228060601d03060380c2c0210b400d0311071460310005d0000e06002240 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 157681456 1250 157680206 157680217
    0xe0403030f0507020102030709030f050102070b1008071a0d0c110609011406030c181b04090509150402010e1302040305030a0305180f0c1c060507030209010e040501080d2106030503 79
    0x1c000707000c0c40d15066022802c03480121004000039580d49001c0c40040c00c69030161100500400025003061407946901415200907241001d100100c08420000c154060200c200101341c2c455605000224035224803905c2d204580c0c82011440e80c50392070f50242c0d030166510144041000d02207500910701520070600804889450350303941c500401c000780f01d9240000d10001c2e0688094131600d480385429044041e031000c0640090010b0301d80d040c9a021485100002e80010010f6000114541c00d00e203000b41c2c1040c04c550407002c400d241150410000d0703608104c0c004285842a110a40103800340c0480000a0203203800040007400000750860803a58143c0003140194902e07484011114503001c0704555600e0b0200160410350440d01305801036180c01e07a0b0045041c00007032a11105840700e955800c1c1158021103007000480e6000c146d03a800b0b56407121101c1010346d420344042015504041540d03955031419000d0300c08104a119185280c83c1d000000c200e030010b8454414000f09417a45403103512900709 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 157682706 1250 157681456 157681481
    0x1312030b03150615030c0c0d0f0f1106071b140c010813030e0114070501020310060801050d020a05040c1112030403020d080f19020c190c090c05031603060e040303 71
    0x92002070810542e018009a002c2e43c3c000303041e1a40d03c01c405400b00f116810090061103005014405c258a6003402e11848052170a195130300d403498110800050035060382401711104018044407585a50040001c00d15003081d8103041c40e11030720f000810140c029040700c00d4028082c1f5001c20351218500c3e070015003841300100980b0352a025507906801385a080c070108401800080329070045100d954016169180000c1c0210000c40c03600c00662105403d99105589002d000c00c1c060504008980e03100d8200c60140c001101c41c4044d8080b250006100c40a103801107074441e0f99694039400819000e9102c2051404581c1306842032112920250306040d08100da055025004020b44c8106152050000310b104842e604807000381c90711140440c1c00d03955440030640c80c0042d030030072104841803420009591310311318450020b20b81e40420715004239031102c20360001843d1410505036542d40390f001070649a00400215160b4412084039604401404959200603207011010040c081071580c03580200e02c0c90b001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 157683956 1250 157682706 157682713
    0x8010b100201090302061302030709050103120905031207290403020703031704120c15020408010204140d030203030106080a0603080706020c19020603071110050a090201080a02211312030b03 83
    0x203160350180d0903104905401001604140002114008a02100608640007504950000f03440300c1c540421a5020b1b0000c0d2134080251028042e80765203c289040542400c1d4082c08025a9803c1042c107103000f6014000c1c0f03620703501c0f20100a0100003803904044ac21800411410174102070802a4503031841e070000340d0000c2c0c2900b044141c09040a850b181c0502d520140c00c1d03003030803600417003180c80c13b4085008490501410700400825440c0b400600b01800743c070f0000503550380c6848880c852101744201030b9402981c841d030070031000c20f03001b2055a0450700b881c280204640e640e0210301c0000e0045400062800390b02150761424054281d01510108500204440110728866483c003080809140029400304003000069401842a0a4035010b01103850031140c0001c00c042e41403065800c1180c012802d02d540f40c00c090207542e402044aa003004000c03a00f10b00e8410246d0151049062650086460700c4024005c1120380100d54403001d405904105902d8141c027090400902600401e00028071920 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 157685206 1250 157683956 157683979
    0x403060e12030603030a0e030c0904061b080f1503030706020f1305030f07090f0b0a03080d14010e0112020d02090708090c042901020f070f030b0a1118061308010b 71
    0x4001034102c82c05410024010b5003031120604084421030000c80c15640c141c0180721070303085591901442c0d01c0c0a41d11445011444010a024400812010315803840810107030105100741041d9a501c0c0f1508041480802d0540c142c0040c0880c0c507610815400a10031840015500003044282d00640b5a1016000088008955500c205503941d540403554242c2500005420003400c0203a501c441602e00003050049480c4641c100094002c0a5a0348180c80f04800003032201c80140d52441045201201100090b10950521240912048050054003100f155102e203800c199070310703e082948050b50044c030325102d0740b130002d030000c114580c25150034801d4451400ca05020b850135008100c01e11800d50612601c0d40c03110f501d02034541112012072815800381c0c070351116005900b404040c0290400354010822249145030800c1d00000c003c0144841601d00802008140100000c40360a110a00321a00c82d0307454420000f005841210600a090745103940c0019901a041d0404034001c502161404a01c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 157686456 1250 157685206 157685233
    0x8010e06070e011b0204060803040303020f0d0309050d120f020a0534200306040b041202060408030415060f080a0615050f1003060e0a050105030c0a03120f03020c01020403060e 77
    0x20741d0b0800580d01054081070369601c1d411510740b4a95146000810200721256160401c5055030b00030340041c3c0050304410400d4a0252003003142c0e440111013803808101e032090070b4413110384400c14801c441d802c0105074285280742c8401d640190810b146441c0c011581e07500301c000d0182c4aa8091010b10000500c140e0100003110780007500315151407041c0f03000f805e40c44180d59070041b41d000c01e05020010b4800e00403800c6882e480401031288198030a03881094142090b05098650b405000741c4d80007194840420007001801130410340c0d800c298401060b04c0121a4409040c001e4945608402d01c8039031045000580356000082d940702d024010801000a040d0222180c6815101c502416402c28000b00e889215400d000301000c201031501e10300000c0c1d16846002003070b8051026150800c0700350325100144914942800f0a040d0303100112001da5905140d6a21210914a0490346006010090080100d0700c0d0090b0100c4450244c404021036a0307540b0b0345007407001400c1a1802104520510b5100101c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 157687706 1250 157686456 157686467
    0x112106010801180c050c060903070213110403030c0206091002101d0304051005040806040308040c060c1220030d0509060610020309061c0f050601080a090f0f0c0f08010e0607 76
    0x5070b880b00f03150b00904072068100000901036a04450041101c10010050802014440203015404d000095541c580c0c090041006240384658041800780c50004013613140380d6014202d0301200c2d03250a0004c4041403900006841c0d008428441f80c0018105060003140c50340402c200d03010040c404420000d40440d0542a099504040484081c07940208020302c403902c1c200c04045184d860610b0602d140c19202d5819604000040c6c40803404140d00f00107110402032000c80c50406400341d07141a5002c0141c0b5240c08100c0ca010482030300a04c01e0281c0c050080303110901428000044003070442c0d640b01c24000d1184004e01d0210380301141c500415001c0703009840c1445000382d0706c2d01d1942c0114248107076102088140e620506452601c1d11540d101c00080e001035005008668012a40000c0c071460682c0024000240060100c180a450000d60078000b545003c500b50172141c110080500300c107035038502120079070280c2d0401c0310b10000c000d6002565841c150025a2154410403d03610544c5810a0503500e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 157688956 1250 157687706 157687709
    0x903050a020607020406150309170c0d030509010b030a030c06060509060d15060909030f030b060a0914061612030e0703020901030b190221010e0105090f0a112106010801 74
    0x1980c00032420320000d403500e02c02605845000600015003950f490345410b00004200f045a07010a846007140c20a01a0324036a0030241c1b000342d003401c3c1c41c141a60320708940710061021160706141c2d4034008103006920950048501900c050110746200e0160306005d09166420641100d01e5414a8004240d41c01c0101803903014250241c5000c1c40c00d002a0345003418003c000401d0802e05580c0c0d080003802205c030f80201c0c940a402a19030924036803400e0001405e81e040542000d004843c100000401194019405011a100188815081d5001c0c50019644d0304c41e038041d1002070300d054103180c2d00f8000c01800103e00003903e510b0400010b40a01589500c40f012440081d5001080708010404601081d0503503078000c000301c4c0122054a44d0403850f400300d070031603480040b076440d40a050101c01028043d803940940074a01e20001d5030341c501400201e14800040840c0c4085500001081111a16800282c0d40d81001203d098882c660000701e005d50000ca155244410b00c03d520116801d0350198021030f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 157690206 1250 157688956 157688963
    0x4110f0301030b04110a2c060a05100c12031b02010b0906041d060c03150a0315090305070602030103050309010801060302071211030c0f030c0d020f0d030b060d020304030801080105070903 82
    0x2030a41c0e180d80ca030700c3c16980c4000c00c240e416911540100100e5078608091070081c2951031540b090541c0000d0b19841c0d0092510922050603095400340300d0b240e65400328100480350119456003c50b1849202250520310b0850024440003003280d0030140190950000d22801a0207100303800d41c601004012801e84401c1d40c0310710f41100c800c20104406080130340100260020446840c203803101412040b525007281100c045851180110a00100f14216102106294401c0718610250390854580305c007682c0882c01000388031a40d07118900101400b03503081c0c1d801550481011900c03580e40e418901d031030b90301c9449180d00060b010700000c01d00314068801c1c0e41c00103130000c0009407a0f041c4108280c0300e0413a0201c10f000340c6d200501c06e645050404200c101c03003a107010300143d41c03580d0315003081601d4040390005280a54004c1181d08101c80c4d0000380c0b058080c001c614001c03c90780904004906103100b001544100703540004200820706412030f211904880101c8001c200603a68640200d42c542010b00005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 157691456 1250 157690206 157690237
    0x18150901060302010e091b0904020c100b04050112082a0d050a121a1504180e01110913021606090609030801061803030e060c0a030c1502071a1f0b090411 67
    0x2c0740a00071031f020707054440d0060801481c2600075520707075240068400c080250300b42c1341d40007441c4d1810701d070141c0c0f03004110140b00c00004d502c143d85d45c1429801150048035000c0781400344005403c00e65034003040040661000d03241c8400c0015002007840d40308020150104441c14440e040046043c8a10001036414410032040301d00c034813041003034090f500c81d401c428842050201040c050f8441811401c1400850000907881844020150035501c03802d915a41c415410b1010307042c643c6a5010400c0741c3c042107180165280d4503624004a4800242d001401884c0340001c0c1104008260340300b0310009000f5114015141ea80d81c03802c480c80205003024404601c1c15440410000340141c20b0403c0c54a4001e20007410301401c04151440d000400c2016030005054801c494148088a44c0138001ea200a103415442c0161688072141c5641e4403010000d0b182e0b130280c00140c81452080040803400c9070030345000081c0f69592201e8807458102007030310b42c4102e03c2d08000c148000f2141086880c5040032101c072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 157692706 1250 157691456 157691491
    0x8010302040b0102071e140301050603120c190309030b100807060c0501090b0f040b010905090705120a0f0303050603010605061e1e03102102030618150901060302010e09 74
    0x24400982034040b011410340c07040c540045901220319200c4059650484091040146080509565556617006550203030345808180212500c000c502880300c00003200704183e0300d0b010111080c1c0b90400885006039081007001034001003607070000310042164000c040000090b20703110501208005c05104026807176004001c100042409881100d8180c2c0c0540000222050a512540034000b070440b0340c1850240160700304010001600c038401d02500d860202001240b400901141c1e0701d030311038080d46101341d107048480e201c11f0b001081002d02c125449610444000401e1501402a040c1651824030035401e10201041c182421015245400451100b0600246040c80c00d00e9090707020414101803102c9010a12005000b22001540545108100c2005242c07500f80100d100420000c102c50301a007441505002590340010b42c0c5821074881c01c148290080001c100d41d16001400316054000d0307034204208280c0c03c01c103502c064212070003a201d0052140700c8004000840070112a2042000d562048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 157693956 1250 157692706 157692709
    0x4052d07020f12040f0614070807020f04182303070605220f0203070501090e07081f33050a030b06040906080109031706012109060e030a02010e0d08010302 68
    0x2149504104903005403014401c028401030300b0b0103828951004183c0001804004103a800c2c01d03100000d000c5840c0211038100c40ca241904184140b51000d40380c0880800e4034410755444405100d00600014001c003c1c2c7c400421040c9a2000c0c10360059800021012000c02e580c0d001d581000840301c440409103103005126654070004200c0500503120300740710f5082400741e51045080000c0440e02070181e40e4520600da204140c80d16002d50000c0d070400130742c4034081005d00603032640305410494030704014809540e0041d1424400d42c8402c0f403a18501b00f10030700040c1c501204140d107840040f84ea0f6503582c804400c0740c071841a6407a27040780a400a40100920000316110707500804400a00410180c5050f546584800030341d01e0641110001e65541c9040e241050342080320a03800c51441c08810100d86440c1001810011240444041d90642000c032404443c041c1d610a900c1542d010808000e05a803502c3d11555a4216444880c0075601c0c202459900c043d0025002024502e9669031980580c05e650 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 157695206 1250 157693956 157694041
    0x3030c0d08040f02060c1005131703060f0402040906050301050105120312090c041103070225091a090a0c080901090203070302150d0501081c0c0507030f020315040f020405 75
    0x3070007600c803102c6034803d810059803418010060765003164000e1481a107050005c00840301d010b00044d44181400040034001440c99036210302d130029604410b030f1a0356071035001c200f5401c0a0904140e126100040101e9000d400750302550907a08150003c0009070f8039071045c08002c800304072194040764814003038600c1102034500030903400484542514a4036110b1070100d401e40b440381024021108021081005455042200400184003501c00c41d45600c501200060342032018042d103042c40c0e0310b6103090fa90b4102808140d581e200b4020f06031800a00e404407000d0020401d00c0c041100090402000c00c40740e41050003200c00d8140c00901402d082842c40e42045605400c0ea17402c031020000500c8440d00b16100c2e131081354000c00d81d402c043d000e1a0009807080560030300284420041c00700c003601c0b400c0411000180102605d510843d00e21850803580002880c0c4054061010305e00f9081030108030400a80c081c2009005200740c600348030913110700c90212481c0b1130384240390924840281d10140c2003100c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 157696456 1250 157695206 157695211
    0x30c070212100204140d0f0b0901020705030f0c01050f0415051503160e09010e06010b0a0c0c091401050906010813151103060a080708070b0703030209061b0c03030c0d08 74
    0x41c6415034000440154030709000050304001da01950200c0d0802c2510442c0c84184004101100e020600f0f146682d20071105003c3c2d10303005000c140c150300002c0c1c148442503044800d42900001200d40702c100d412880c40071035022a01403030165080c1000702d114a9000f05105024940c041c000049040c0c0001e2840c0c0108802410314501c44d01c640c8504006440601c01c050003600a030301405c1d215400c021212403180707805840c668160380340596002d4605070210719a03064a88205800707070742c0d00c03550400302d946081d4540041c00d40c0c8400240040c0104007503200300f00304041c0c0c00c510b625584c2d0700d40407c03118445c1180c40300c0c08101070000049039018524034400c41d4a00c1214440c5428514110b01d9003141c400b0a481c0c06921000000d20840d0319242407090000c1142500614419003400c42d00f584805561090115405020440c6800c25000e90140c07088000081c1c01030303440390a00194000c10000051350301090307014451100c2110f08003c01260100e0b290312004001c88480000e00711100c0a00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 157697706 1250 157696456 157696459
    0x1112180a180903030b0603130203070614070201110c04020c030a020607030216030509041103010b07020301050a0504020a0b0a03020706020d050412030c051c0e0601030302030a090f0315050c090d0c0f0801050c030c0702 95
    0xb1100303028017960315400514010300501c20b110301520064414945402d001d604220248081c06003928501c1c0c1410003115030050742807902c984c040b01420f40b02c80c0340000c01100e070ba900c50300205000c00c07030f4080000502580006070303088515a48841a0682c01c070301c5209101c89100318030b500e400010a00400040c01140d4000d07000140600350103010403219042030700003c485810000b0360005625007401410b8120003008000c010300d041030740c000382c0c01c0f1303440d03108401c039070f04010610021107130007503054806880d00060250764a004003071180d8007d00080350211a40c204e82402441218464800c8001000e00c9403140c074a0071040122940e4101968051070071843d8850210400400050200c0c0f4000c6109800840d01c414075080c014020400b160010700c12220202c4042020840600444c1c554803c40100001c0b5511030780c0c0b02c18030611882012a03005100810840304000603410b011084038000c008001001752074268003400da50b02914180c488104c140003045a4420041c010420030740f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 157698956 1250 157697706 157697711
    0x5040e090313030506070e0111061b070501050103050109150510140f03010204120b06090709030201141603120c0203090105092803030e10030c0807030c1112180a18090303 75
    0x2100c2c034045050840503002140c164000b0402c1c841c1a9410a001d145582c00900b00b0103a42d0210140465403003000805840d10840e0100e07081d00582304e840c0460701c06941041c004c4c0955a140e08103035020b00200581103605803100c034141e80341500c0700d10405000709030308982c9400880c640f0708849014101fa1004a5010001c0c40420b161940d09200501c0100224420021254424101882e107100010213985c010503040c0c04203c8540e0b4400d242c6d0054a07130908148200034004055035905002c2c0400c2103401d50031000d500401e140d00003003402c0c2d90710601c1d0801c1c054098048802c0f038581c000c0c60a0540400c5090000a029152944100c01340000c49602040c14034030841d10034001d000b041c1d0081d00401c8040c43d03814210305040003590403001d0607003070500c003400740440010403802004216600f010342c1c5a125490302403040c4402d2080b0598041190300c40040020112483da21001c00d05805008a91814805041030307076001003210300da01d42c120700d944c11158103040a041000c0d012020180d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 157700206 1250 157698956 157698967
    0x13021c050f1b040605010c0215070c031a0901050903130e0a090605070f1205010308040e100e01090b0109080c1020070303030605040c0212030a1503020411090114040605040e0903 78
    0x140c10002440100400707500010b400a0301000d12045075030b075800207070406c0300c000f040b00c0140e1101c500e01c00e0b02c15a1551110390360380e02c90401400d080e407a0b4000a11304540000003814443c440074030240140c1d038900007080b0756120405819036078410307645505406d5150000c20002d409405501e02e51101c0b01c0580070800c1e04c00c0e50381e110700700c070f038201c81c218041000b601c0384a91700d50b40102a0045025580ea08001079410b541761004103000741d200740040302103000300048009408015000040c44541141d82807541c6400200000c2c0403000c01403400a80c43c10b04c0080c3c58000022a01e580900c05800b200b00d0095561044075285603140a103803090855952001d10080104040b10081d8040d54002448905100410041e51101c5c0200000c561000c00d41a204c4180e000031240c01281094000034001000048010040c0d000d5202a510618015040100d0480b00c0006c00078644d09a84030420b0444c1074905080501440c05a5400100e007804107012601004011030f400080f0382080781d0605 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 157701456 1250 157700206 157700233
    0xc0a0609061b02160b0c150108100b0a050d02100207030b01060215090606090601110f01051311090f0f040309051f120b011b0c051806010813021c05 65
    0x19869500111402555a1200d4842d54151031454403000003610203001c58640d0036104185615081c00354148086000032038241d0071104210500c021507108180621a43c0d4031481280c0721113154966a001604010300504245000d9161100382e0300020b2960891050580a010000100070003483c154418684080301150781d544295008150541c01041140803074202a8181ea4003e8041c904540c043e0307007031040c240c0d296444c0660200082c60308031089812454414904150445540881e51900041c003800b054281318002065004680e00c40e002010002400780304941155004040101c650202d0001c0d90940f403069001400307440d22000a6880c1d000050301c45402c0c0c00812400082c0358400c072101d5400c00118210680200b00401058410f9000640540010519285812019514002000402c1c01ca9002501e000741c85034207200c103001c4030109801409d64034680403851000001d0018110402c0d910308080e40503095040c0168202040802204945400c030740318028520f5901d80d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 157702706 1250 157701456 157701461
    0x70b010e06041515080406060f140a05061201060302031308030903070308090105100501030908130623040f030803040f02100e1c050607120605130e0c010c11060c0a06 73
    0x2a09161158100324100082000704854801050600182c01d0101c100865480422500c0080529007889001942d9900d0700c070b0300524150300700ea0a035003820100030401802402e03542a0b40c020030760702040c4103519001008800d000c3c040d0588025607022005006141c0f00b50042c0d80c0000030000248082c0843d9034034024290000ca841c01348507072001c1101010f240d40301ca907040c0c0040301080200b103141440307554254901d2060040a0515460704844e00c00c1204490448405000340e00c08102101d4454130001c10601041d0222154401030000e080d04540b000d50031070301241c607160004203c203455983c1d95072082c0c00080c015500d00480c0c2c1e107100056243c00071f0b408442d10b6075665206601001034100030f8501060400100401281514600000e00c005803c0382c0142c510300313103580310001003000d001c0949480e0700301da0382180c041d003840c00344080290004400c00c56424256021082c4000c01150310700700126010300030700403420a02d10242004002807010590040959003d0b20fa1604e4403c00d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 157703956 1250 157702706 157702709
    0x6060d060f1e0b040b010e0d0302030d05010b1306021f180606290405091512031c0c02030c0d080718080a0606060f0f0806010e12010f050c0906040905040305070b01 72
    0x440750701c28490490010110300c503401e0302c0001100d003000104202c0e00007c00c4009001403646c040c45280c0c1a00003494000c00c10f540d003a080b0341d03030305001640e107070881b50525400280c4201160071081e2004500c59001007120f42050424400303402d14002c00c0001580074001030079808080203582e412003400b089842c02041d028000801c85000c1c0c40103000c00000c04900d040c804415400b006000c1800280d4810303a515402a109040421228618078002203c8050710340406046100004602002d04001c6020449080c1c0f084810030100031001020303600ca10841071002c000d504480754149010b402000c0340c5810607030034980300140b50f50070850303000280001e400080c40380e40060440c004100c26401100050a82481c040701061540341d0003504403e0152511024014240000354250344120b190080740d24005002442c8481019142030081c02c1074241d00c0000307070604001950907140350088030041c0102070301031441c16190801c40b4004140240007101044010816400801c1001e1100750 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 157705206 1250 157703956 157703981
    0x60a030b0702160504090804051908060f070206060409020f0112020c010603060f180b131e080310060504060215130501090305120604050105090604020d1103010f0501090f0806060d060f 81
    0x1d183c0030080700c080409240d13601c12807041d8103140c43c40000941c450b096504445055074030300000761108890094001203500a215540329900410111460030112a401046140c0030349900e42c072031030103110030b03a1141c80717020390403280c400001c00c480d502c00c5081c0041e40307209030310041c00c01700c0441c1d10b00d096841c03c1e0b0055032101d440310107024004513144560340c0c414110f0321180045c1c4c04160f42d01d000e403202c0144580d09400c0d40d4198a420b010710b2075010a054261074500d01e48540107442d180c0c0c81078005881026443e0040c000c081401c40c001c80c11541921001d80061149240c1c81c04000c00c41c080c0140300b5020340410f1540c10000550902501040c94842d46409480303203405280b100d07039020001c007001d1103030b803c010040142d912025505600004c0944e805a541d81e49582c0000113082d810400030600c0303c00000019142442056207800e803030099075501e000c44c5c2d41c5c061480445d2100d00451030640c1001000c81d00c0d501e0310381d0b5000d0303c1611485003c20301c001c501e140700045509401ba400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 157706456 1250 157705206 157705213
    0x306030c12030206150f0607110a030609060506040c0e0f1804060c1419032403060605031239100203010509070f02060f150a090c030c0c050606010503060a030b0702 72
    0x207408058060080640c040196803141e250450745400240400c68800d01d0390740204000a105d100340b10740114035040d8000040c042e82e03c210b50300d203404401010382200030f40e00b4914010101e445450f01e4006c40d241d4000595840c2d2001020782d040044c0c0250014500740e2024440c440d10304204142c182d424031640c01450000f0b1010301c0700038054800202c400442400c5c000400160510418469030407040850a150000e180014041100030300e0482059892101c140c00700008100710003a008035040c0c8000341c0c02c0e600dc1d28110403140e1068010251017010030f81c9242d0b000104040b5240400c003041410080364038004c40c1001d5800d0500d000700700c0c0425000c0c1c001005100c0342c01d0146102d034202c00c1518100403000103004c0000c1d10360303074054070f01a200504c00d07001c202807807900d0f03a50103c20b100c01407609640f5540d50503400c0003010a46031590100e03040011040c10103004220b0b000b5400d4010001d00301da540e6171401155554801030485906c404000c5010000c00c104850441c070a040f550002c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 157707706 1250 157706456 157706489
    0x1305070e03060709090c050d05040f050705040605060915090603100608181b190e01090c03050103020603011703070803160207170717010e1f0f060e15010306030c 71
    0x2403801896600e114020360000080c00081c591000505081781c1600740300180454003100112100d11401c034154400a080005108c28804604c40480075944a00201c1d20441d82d240b060006440d1301d8030810f940042d040c0b007148034a04103c011880d1015601c400c02d4a003a410200103007403508103884091f66919510310602126130403019440c3c0180604100211100b552158143e41c5d41000b071880c49400c1c5141d501100d81d44800c81c146140081490b19215810b40740d0110540e0080309202c0c0c0110340e82403507111514507001e4030405040c1c075005019a80746a0a10441d41c811480e80824044503110400c034100100704035401550081c03000c1000141c0c02c41240d00024034125043c0c001d00601e440c03d400303944501c44d0002c0c4041c207c1c1d07645905007141c003410302ea601d8014038214121603900d0140b1100c500003240c20084038070485031011010004282c42c140300408440107030080f0161448c0d494042050360441105d1010b40c0c4105140c0803a1140c2c995407903041510345907201d000101c009811 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 157708956 1250 157707706 157707721
    0x71805070503060607060e0a081b120a0e060a02030d111819050d0f02060d0b03060a0207030807050d0e0a0309320d0212010c08060109140109090506040b1305 69
    0x90690404214a03256085050101c009103252003140d40040c000c41e901c030710300042d6840911401035038a03000241c0a07114150407c1d0342400e810b40d283e040400707010300c0b100d20100314441700c2036607101c0f0425900d0311000f84156080c412251300801c8440158032080c041103800e0340090003900c02d0b641d01010600e844502c8602520303041d10040c2d140a2040c90740e601603100420710803140004441c1d08580449005809003030142c0c0c01c80c4012406500154001099506c0750540e401c020003910094086074890f03510304062200324081c50310010700142884000c241094499000340207170075984600060503038185070f200351038150501402c83c04100c40140030000180742003e0950b00355040d01e02c140440d088111700c281c200c50b02001251040301c0e901c40d14419034907006031704c50790401400e0003000034075100080600710200c200c0e001030009851840100d480c082e45403140f840b03c4410384070400713501d0810007108050a00189410b800540d01c4001a05caa078a40f46110340c041081e013000916405e0804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 157710206 1250 157708956 157708961
    0x402031f06020a021f080a050c090d06050601080f0910270c18091a091501090912090e070e0102011b120f050705030103030e0d0c0e1e01060507031107080718 69
    0x8407113401713565109004c0c00070342d400600b120750084e031381240003510340c3e1528800c0c034076170049040c0140c00103841c2d100c44040017003580c0050b0041100340c840841d40daa030020704840d034000072030320300c80507811000385180c1d01080f43e0818074000e10009600009007646104102d00c1e40c0c41c2e050252405042120708000d0080a03c41e0303245c6c100d0301d54100f0303c10300440d40c42c0d641080d0080007001d02c0e420564000900080418050b66030200c40840c0350714102e5a40d0080c03100075200c0d200083d034448801031001c0310600d000d1030f01c800403200d129038048000d540f40394080d42d0803900f2810144c1035548804505481280c800d0a1040b44d00080d116a03038910041c01000c0c2c115040800c101c007460f0724103000d005010390014242d9044a42c507140000c82000c00102140340342c41c1850004140b00f100b0714012483d1035101c1e1115118898441c2882440d00041d660440d82000070300c6108041807042140502280c403800c85145010100e008a40300103035503d08481c60100c10341c0c0326508029a400400e1802001c90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 157711456 1250 157710206 157710229
    0x141e2a0d0b030c0303070f0c05040504050a14010207030f0c11060f0406030e030a020c060a0c1e0209160f050d020c06130510090210031802040c02011a1504050402031f06020a02 77
    0x180d00808012049070007180d1769118948002e402030b18202c08820411020f841310101501c0301a00511080c10186415070350b4141e4040101c820b00803282c580c1184640501c2915515034041d51050707030542c1c45078016201540120320588616241c40e0301074000e03031250001054001c803d405030980d25450800010222040d002c80561107400401074051500da000843c510380590407100d640d51882c42c0c40d01690300b002e900d070300202094a9203400050304880326000c0c2110724026102605142d664131801d208602c40640c409011619400116210500c03a6000d400801c01e04040180b90211221100380b900000300c0d00f440ba618400000f10080190610101c0300c20080e06006000764413551f400601c44d400110000c00405a80381c0350700168200103058049150b030090800c2003803a2014bc4024060040c2840100b0b144d403100043c10f1132400c1544001a5050109040300c0c1007904003400c01000c4e610143c0164030703c0d10072805040302e01c0024074040d0002c00c442d80041c00010361074070510a80f803a96 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 157712706 1250 157711456 157711459
    0xc010605030a0b01060302032508011d0f0406020c1002190e01050705030f131508250909020c0c03070602030405090c04080c0d05030d140901141e2a0d0b 67
    0x382c41c00000d21070b90a41415200a0700f0003503226501c03040903101600344105401e440c140c0c41d1504a40041c0c0008202c3c1c160b401d407858944d056444154101100307002516040034081c1d0724000100415556030181a000d040c00f000e80b044200c04071209c005a802c0001411018084511380300354081d000718401900e22420308005c1d0402109440e5140c03a402024424000c1361000580380b8950104110004082c00c1800c1c4070a40304540100010b02c110011100d980940d004400d00158031941e624440c5a0a0f03140d80d10100b2031820250700764007a4104900c0c40c0203910400ca11554681e8040c40300707001502e402d9004688462a040400c4940e440107880282d10310000c00061041541c00325420420703c1040d908128135003050310f0402e01c2c504c240c04072012040d02d810108410074004800c1c280c0200d2480000341f001c641000c9a010300300405542c90451101004401600011660040d6a000ca1303142800244840c0c40381c680c225500500040c3d142152001030b81d42481001e034030800208850 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 157713956 1250 157712706 157712713
    0xf0215090607060f0506041e0515130c08060109080304060507020a081509010b010f1706030a150e0c030706050901180e0109020309010c090305100e030d0e0f060c0a0519050c01110c01060503 83
    0x1c23983c181c9902e80b645040181c180e841c8c1e80001c8040d50080452101524040c08904405000340000001414002c86403000107501001144c00340d88180803000070388800388091480c083c80c000713040d50203030b1109800b01d0300200040700c0010380b541c05110348103100d50f0300c0080c1c40d001e2034100c007660708442c7d1899455040c401042d004c002078603800f07444107001a41840c05012683c640600103890a4900c2b0001403000208005102c10920035820030400c040200c4c0440380c040f85110201900c0707140303a004000015509001e21512076100d03065420300110800c24105015880d2894088540c0d401d80051200343d8000040c0f150604091040d8450404213203488003e807030640c2d5886480d00515040656030300d49402050050907010b004a45001030900010094442000030440d1500360441d00482c00d405107030001003450081400315840021280c2ea092300d00070742d031070b6040202100440340504000c0184584c030a1180d09100c1c0c2040c59043d500742c0ea480c5c116062400c1d007075841e99000503010b80c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 157715206 1250 157713956 157713971
    0xa0e06060d0204090b0a0c090605040e0c070312090606210302060c0a0201060f0806100815040609060e01020d15120201020303180c100306030b01120f0215090607060f050604 76
    0x1400426000d8000c141100d002181008500005015041e4013201820101501c014899203412036444551640101d803103030160070b035858106484c18000e501c02c0200c100c02d0741c40042c91a440c00703401004200c1c42410031500110003110f9401c00c84505000c00c13207446584500902103881450306403901070302d075414280d401c401c071a80e0003500c45030082c0c41c030051400d000c01d050010750700039003100c001340a00301d030780c2d00b00c07190390b1407006070707188001d544074080035840032808103000ca004a82d240151980d00300c102c40300d4035180c1d1410024415008207684080e40d40c204900700b00420b0004101402d0600004110300c0141e00400344880c165500c01c1c213a8014640d041c40060341c02006030390b07010f09000310784c005080b8481071850420625101e40e585c002211222040c505405034000d20681780a00d4000a1030fa884000400015107400d202504610151048000518000b90107410039100e082d00103040122074004a11950460401110304544940c03141e2688640c82c070aa55004d01d0840b820b103d2038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 157716456 1250 157715206 157715231
    0x100b04060e0f010e030102161b080d0f0504030b0f0411040507021509120f0307020c0a0e0103021002070e0109060e0915010e0405070803120109150b0d1d0703030e0102060a 75
    0x900c01c2030000d9014180c80301c0320440d540e0240c010340e220306001a009540da4481c031750141d200100140402c5911444054451401840c24011901960a2040100302c0141d80007810380305d84c0c0d111858402044010003010001802e480070769402140c580241452a0419107040c080b0601c1580c5214090303486e240800c844141c2c00076000c10b01c0315848d201d04c1034944616103680c0c2456901908100b02c05000104010407104070340046201e4481070b82a10103201720042085228821440340300c1d892008500180003601c2e05000400031104140100c0e00d4030b6507640b88014032040c00342c0c451040c0c01d90300d4004100303000e2050240d540c0000540c0150000401a000280e000359060180c2c070703690700045000408100e000c01c1103801030807548003220b49507020a0300c001501542402101c4072241000c90f0282051034801c80d4078280d0b028500c0140c20b1000300c5600100801d110781c0020401c3c91000c220000c1e0750b000b4006c18014601a9866505a403510000645022005001070300c4981c94040f0f90420b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 157717706 1250 157716456 157716467
    0x3081e09061603020f010e0d030b010212120601120b0d03080a24050a0603050f0c0f21100b0c0a03030b030a1b03060c0801081504030e180403030c11300d0203100b0406 73
    0x80e03c054100005e800d0314ae280101d1400710702d070b507003402004800141a072100003440c0d8014402d010980e10300320b0b240c00201c102e605552190070000c0d0020884100a40002c5c019a500399020011000024440082180b40034080c0e21000c030030046004c20a4050115003803000e00c600103040203003020b020a003010b00d001a002c0c03900600c420b1071108003054840f038045802003211003c007417001c8a04440301d4040e07a06c040c5804160340111500c1d00b00030000500d54076660aa03001030480002034254140309441c1503020702124210079034140599140f880004250903c81d40c038003502d8a49200f030f00e60a41c50a44115400c0110000c28080c10b10300410407810002007003211136a035106100c1080d10342d071806440c0c40803000100355000035a118070f1090b11004020561080e1302aa0703050082100400c000c0d1210200c0e44400300c01074004140e5410341541031100091100c0207401ca0909804540a4500041c1c0260b0f8021181540020601c550000031000c0e4601810a480e40710340342c10310300070004d4078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 157718956 1250 157717706 157717723
    0x50d110a170a060806131a0108010203100f030302030a0e1c031206050307030206030c1e04140f19050d050703050a03050408060c04050105030708090109051209180103081e09061603020f010e 83
    0x203110705d8440c1c0240800000141d0b6007400c88000e01111707e5940c641320418081d4008507054442e0f01000d4000203849030070071031a001100e8054000d0b514115048008886c210160192117801056001c41e040107904c4541400f80e0660103a545e040c60804c08041140945425038080b81c40b9502101e800d00140e560700044940049a2140301955060035000e003089521841c0ca1503500c0b2000442c0014502c1c80c480e846403256501140c240e000d0210840800200212903d440c41080e0b18800d014801c505040e140080d00318040c5007100d4006e0f680b50b0b100c40c580380d480c2c1b808500060004c2802c1003484401c04c07640e908002c59001440c01e02781401c000038180e000082844040165440118454160a60202c0b1086070080161030760781808040e11165540060140750203000e641c1d51450404400e0b0b10a541030302d900c07240c228035241c2c281c440c0c40710308480d403c6a900034034020010708515030b03540d82c0203002c55030107c000c1940348240380c00c2c00381c2070140f8846c00700e8150341420031000c50980040760b40c59 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 157720206 1250 157718956 157718971
    0xc0c1202030d050a120603030f030e06010b03011202060910030617060405100911090a0e150402150903070f091a030102132702030103060e07080f0706050d110a170a060806 75
    0xa440e070700c04c803030304440f4500600441d0700c94500d044000b105041c1d01503202c401e0600551028824801070321a0a03a4464003446048900c0c0028401031046071410605502d0f203600040c000c608110031200003c0c401010b48c12100080b0703959503000c001401001c07210402400c1203030003400540c64903403a990b07103841c44810451701b119643c000c103200700400d41d40c0368000350300090542909450300c000c0c080e0042c9540000004a03100e0088241c4221820b25a401d00c0382c1d07030103041841140c0c8040030903040c4d0741000e20b45580c0b42c011044041440c440100c00c500007016401804142040f400c2e02a01d0360350030700c50019019034010002c50351074001c510401c00032102c80c0c03109080c03104003001d140b41754036003e013502480b0f85000100002c20311586412841c03000c09050166200b1560300d04640f6910361500725070042c3d81e001010304000c414020005000c400d04050303800b041c00b9030080c01c0510168070010641010a0800140e0b1400c0c0420101c543d5121091040401140303003403a40b5255640b80050554 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 157721456 1250 157720206 157720217
    0xc0402090a0902190206010f03050316050f06070507060c05090612070915030605090603030c0a061503020a06080907050f030304050402030c0c0303180f030a1b031e0c0c1202030d 78
    0x40d403003500c50180c690001c1c04400c80840d110fa408401c0103038010540c07113094006204001c008195091079540032801c90364440d008501c1c1c00c0007401c030034402d420203640035180c074052660000380f60030060084900c40c11596486a030785000c1d0b464208111031034030040f502004003d200c1e410041d1100c030f04444041a5010b2002d8040d07680080403607400f210307500701d501007003031000e948981150180c0201c415500f04941601c2250345d000185952802042d81034541c50348507070400f00106006038080b056035804a41660341c016101c1e0081041810a1703441303000007036440e0b41040001c1c3e0050207d9005404211030074051000c00740c0000faa41c0c01180a010701c100c0d4000040f0740500072020840c1c07101e501e24425243c80e460b00d80700b140c801900d4940b040e00f180c0200b0506010092000c03003104c1003120581c89050162142c2c03002e001c05448400c0301101445501100203100c8094011408141c800703d903500c2e03000c20400e02d00030701c026141e40e01402ca005101c0028200598021680c2004100c0c0c0f86003c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 157722706 1250 157721456 157721467
    0x708150f0609031f0f0b0d080702090709080d080115030603030f1107030605010b190c020a091806050f1b0906040b071a0405030901080708061005090102010f0f050106031b020c0402 79
    0x213080190160350408811041158000b0003119900501d542900c0403034108894800081445100044800014550038007000900d0045c07400206203034001c82039280801d6a1500c9095080c80c201074100503a012442010040040700c00c01891400f0922642c50700f401594a1654064003000ca00c00c1c071401400300206200d0743d0344000b000040002c5800910a10165039107403d132820b65413188078a448802c01c202c00c3c2480b4140160210228a54003074040500382e807404904600908186d0000d4035103007018100000070070b465000300b0780540c690f00000e09403424106059003003503461084002c074102081c043d022041e03550b00309680c2142c584102e2a6566038a900e848003a182c80310103442603c1071401c092006000c000405820155404e0322020b0164440c3d41003078501d0f9004451041e0b000c511105640c00d45442980507100d480c0041c000411224502511001981e4264500001440d40d9000400c003056150180c0d13803003000d10380c541e4418420039001c001d483d90685c58080e40507a800250317 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 157723956 1250 157722706 157722709
    0xd180b060d055808040f0605070509030a110f031f0b0303040b040806010306110408030d0c0e030d02010b090c120109021606090b04150b010c020f04060f08060708150f0609 75
    0x81502d203a10481c00700071070018848090340740f00c009503c0a10010600d80c0020599074040e10b40d4a0146802a50004050640d40e036400b024001c02000d880410200340310704540c5481c10403030100f2117071050070400e1401c45c84200b48802e410158a03a140319612031030040701d00364088000c1030314000300620301141e11482c00020903d0b501c660303804409400d5002400080c90500887d00e28140c92240009000d1000203c50421240c00380340182c1702e140d04100080180c7c00740d00d81c007201c07807644241440d1042078038550000381425100d1003074101503511002110101d241001405a004031544195418925051546000440705000c4c858070300381c5c00240014015550304031074004507030000c0c0c28008801a881e28014848050b80c044410241a1f099058818041e0040c5100f10206940760035103202150200074000f038111050301c0e0007640d20b08020a484e401c0d0390455020305240f40c000c080034141242c00501440e0020f0404141001012651036030703603245d10134650741540c00c580c140e032242d207241c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 157725206 1250 157723956 157724023
    0x2011b0506040510050105030307020f060a0311031608060301020c031b03040e0c0a020c15091c020402070609051005010e010b09041410080d0503100b07080d180b060d05 74
    0x28040c0441c401d00d4100000c010300003803000d244156205007440180da0380d90500d82e40780200d0f01c00a41c01b46442d2030054117400c2141c040c1c0741d4000140780210b04651500c60f110866070003a00c6845480b0010f1840c00d440641080c0c259403c030005400031494501d01c5142036440703015243c00005d40071040c010300720308003808000b520007401903035001c04403c1c2002d00c0c0d18021940101505009030291094007042c1c5c1c030b84080c09140d00b20048414518124500c0e00300011000c0803510358002c101549125000341c3c94510241132083d2240c10002020350355800d000b40f402c1800d0a5410329242083c0050201207a014016030440300840102900e03140d6003400100a4a1030b244001b401014400030071581007400103411003140c0900d000d0703401300b254282c0203c1d150b1004542d00e03181940801e00400240c0344e40c4000b0700c0c800340030b003410f2400d10b414140e00000352401c0032400b160f1201d00111f46403c1c0304041407002c0c0c12403809c03103555040001540e40d068544060040241c1a81800b0650b10b1042c41c108 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 157726456 1250 157725206 157725257
    0x3070b0a0c1707090e07020a0525080304030606051c050307060b041e050f0106090e0c0705011b020c0427020d0204020405041d0d0e150c010b060f030a050f130201 71
    0x146125402d80362007040203081c440144a0b40c00d140032484040f0348168004030302e0f5030340c181c0c10201525070008044001141002c4215032401e500285110025901c0010720152015621549001c0b902c0307803a040800000e0348950b112a02c01c7c9000045003000201e0010440b007800b68000320100718207980200007001000c4c209800440c180180340140d0f0074104076408030380b10b4076010504804590301c13003d08413121031050050080c10088000454071800307010015002507481007001007450080380403140900c01902901e070b80913030b2058141e4520b91a20340511203560b03071003400e8454080c0c9400340450920400d264040e004020303112022065489680440f4040d1101400620520303018140030301455810311010007039805400c0d0444042e80c0b0951600e0307000d01000703012090030382a8507214001036100100391000c542d621166144540c86841c0036109028019031180d440f850310998540640c0c3d001804192856502c0e0104281e8400c0e03800e03040e031b01c95020300e0610f20b16945064001c0510141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 157727706 1250 157726456 157726487
    0x1b0501061805091903090f0e07020f01020c0d03090c0b0429090d020f0118170606060304030807050a12060b0c0114040c120c050a0905071806050d090503090405090f0705010203070b0a0c 81
    0x500e5004030700c188a448d01c527805902e495080350118040960507900f00d0080d02605169908407040d0101014800e812560749140100c0101d02425521000180c150f841507020f810581400007030200003a882c80c203101e03a61240e18240f01e15003105c2c5000105183c4121000038031507490144141700c0b0703910904d65622542c806980d07213950107407141c2481503401d1125440d0540c82c81601c0000d541402c1000549020701c0e8107840301c401c1503c84582c169501d4003c0031a6100300613443e0300f181001309440c0200d40c024010b0400981d900c07520b031010242508c500b01d000c2d1103004c074201c050000080b0400303c1d4000311120311700714100c0c1011300d1070328001d6030350103500c1168845141c80700410352400b0784e801907005010a485140d81c21364100c0c00d0901454841c4100004a4020700a40c58010800d4002480d82489481500c2c601300126000500310792003540c0d4003040b907210100082182c801000414041c0000340001e41c2801160364921044982c0144103141d400c3d224924a06114000e4084141d0030340c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 157728956 1250 157727706 157727729
    0x5180406080622050604020108040201170a1a060a0210020d020c061906080d0206040f030915111605030c0f0117011e050402090618011b050106180509190309 69
    0x3074540406070307110001c2d69039024280c4400c10009111501c070740c21603103540e03002c8054899984c2d544c0041d100304c000204281d051084017083c00a292041550183c41004c030080c00040704041d00e62180c03002d440c00d4090038020001000040d44080d00080e1a00c000380e00c0400141e501c03e039030031640e0080e0103032803060281440f0b4a4207020940001d031f100c040c900c0121142c1040350320390740e5107400e0b500d1007440180130161b040440442e000c104141e040030f820501a0510b03041d00790303071519101e9101421400c840700140039000301c000040414000c1004919111f03140e040c20504003400642c8034404070b41c1c07051080c2c1400c80b0b94801640924802000d81103071190744011507a46405840548403d6042250789081001d008107e074a401e100f91070300c11002801d2706042100382110554403030103c0c1d00090501840844102c404040d1071941880320b4414800462002d1404080c404c00b4000900203c0e02c050500b0104171041c2000600300001c20300c1101c805100c1c088604094807076011503000078007081c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 157730206 1250 157728956 157728959
    0x90503091002010902060d051b030112020f0f0307051201140106020703060b010801030c0504021303060e0f010509010603020603060618060f090f01020a0c0b070311010507081609060f05180406 84
    0x4010025192203a01511032821501c03000d60200c0c01c80342c1e1210001e51200c0203004c040d01c000296440b19612007281c02c81d10140c580300794510010f60300264490290100340c05a18011810324400d9914200002c3d42d031070310142c00f00070000e52105d840b07018960160413008411250404d00b5000b40b040b03800c50025000343c1796142e9100a4960006000650350181440c1c500c0400d5440b0315a501d04030394001c1080b00c00c2c14140b201300b20103548010702401c001002c201000c004508039200303507100304e42d07c00d00074035000d9512b110b01800d40d00d00500741e00651b450400d04002607180c0004803640718000315000c40d80c0d443c41e0002d0320801c0b40c1c44001e5942041e008528600f00c002e09200601e80c010046a80b0350180c12400012a555850348400920402c0d81d8141004407403142009003030b070a40300e400c0413802425002200d60071104203c0c1c0700000600c15500380310589003200c190800503500b52911710085400c1c40409040d00303080347d10202c2040400182031064806c60b114a96100c03000a10602c8420b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 157731456 1250 157730206 157730213
    0x1020c0d0c080f062205010e0105010f230d02010804080c0604050a020127090c020c0402070c140d030e010503040309210b060a060c020d051f060305120306010806090408040909 77
    0x40c400b40501a494490b0806007010b21000144551103a6103402c0580044c407007240c60100c2001d20920b040b00d80f0364841606518400b0280251406018540130461440303142c1100c0062404001c030780000c860451050070f105503102e00944596150302801c007450192a80d1401c805240704181e940c1c0000d00404060004010b0b0101e504540c0e14003d030b03144002202d6030540d001950b095503550001161058070100304000c0d80b604100102c14450056914621035000032074140c6e4008042201d44041401062208080d007402c1d00e807800c1000c0e5100e582402d039030380d009461101c41c000b050741071102c0400014100340c4644110401b80000c00c444290145c0e107a000c4005210320014200d481d5008040052405d00300403440e2003c5a03055a00c24188440e81c2d0240a0290314851045d91b26000311909001c0e80c150307580d4088008500c2c95800940d440c554186241040d02410002c04420f2041040c8a02c3d030381d000b4402c07500000115070100c900d454528040b102403042d517111100281c10a040d11092 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 157732706 1250 157731456 157731473
    0x60114070606091103161202041a030103120305010e0a050a0902060c062512020706110a05040e0f0402060405040b01020c040f1d151605071e02040b01110d050901020c0d 74
    0x8a5a25920078850074413080d91240560200711258452402a1000100c4442c070848219004100794400180351030b413145801c4040c136640110a01c04c0fa8400801081003150140302e00c1144101481d00308140d5062011340400b01130041c013421a49074a070008160445042d40c86030601c0ba13401030040d41c0d00c00304500401d45881c012605402d1596040454507940d11240060400f054016a84c40c0c81040501ca464802904162420743d070081c1d6076002d00f40445d08541c0200000e0f0a6074586507103592800004210000b8014215681c060009041c0001a00c40e5402d4500b610021900410380c09035020040b46004800b442c860340c031a08241c010718050580380e018416603088071310400d0743c420703414000039524030750310000d0a141114000054a01d4113101ea1030307001c403825071524503e02605d07501d402c4025249404490700c0344041081040851a042c8142c8124500a0800802c080320a540b61511882007210340e20502c4800500216103038800d00110039030060040a00728548401d091513801c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 157733812 1106 157732706 157732709
    0xe0f04110d08090a030503040503061f0306020c010905010606030b19180e0703080d0515190605030a110309060f09030f18010c1a06030c010309020a0e060114070606 72
    0x1090350702c008a1307000950040006540b02c5050508150a259001d44400c005041c1100c090322081c542a4152045075040000142c46000c0e046c1094094809000e004066500e000800b061a80d0142e22401c400c01c419601088081004008000c186100c2d0007012a0080480403c000a40403500030400c8000518243c0700c65550b280e0340c0740c007123400c100c0c0304520203038035142000440c40d05e10340b018003001c0044401c1c00c485150200000c00c1c4903010300072a0200040000010401c00c85a0042403a06111110140c1d403032a01c0903500e030f255101595030400e0b1100c0400811100c0da07000040d11604d00e00c0c20022403070481c00b02401051191032101c0030341440541d0750703640e01080520b50141d00d0240152008240c624241e81014103000000d00c40a0601d858070b1a0000580c844201082c141c4030f0a01c48403440362108001039501e5600c02e6111900c1510004000c400c102c140d8000c0c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 157553956 157733812 := by
  have h0 := BRFrame.cov_init 157553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 157553956 ≤ n) (h2 : n < 157733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
