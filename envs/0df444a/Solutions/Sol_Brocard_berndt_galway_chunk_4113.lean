-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4113
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:36:29.824651+00:00
-- url     : https://prove2.me/submissions/8a705a30-51c0-414e-a139-914eda32e80d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 739568345 ≤ n < 739748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 739569595 1250 739568345 739568377
    0x604060f0f0c031b021c0b090c03070e0114010908120703090e040f0627050f2109130f020a0e01020f0a0f170403151512030f12021b03 59
    0x2040c2001c551641010b58040d0100300d00c02d811129145520190103299070015015a01220384c0c510b40d0505c0070302c401d500781c885a030900300b40010b0240901010041003c110003d01280741400e000c02c21044040c03140502800080c100102182d001c0d20300200180101829540da82c1901c0a80860a6000900172000180c4200000c02d004581040d000d011741e40080800303510301060313a0b418005011002ea6160034510342100e0f00d4950400420f2003204502c41c402404ac01c00800c490380340703024a0400a10780044c078500d07503280ca4020a4040c0c0341038035030481d00c410b0b003154400c003214000c2c110540d041030120b00000b1078004e6140c1003081131141d114280c0c02ca80348085601c0d1450380740c041751140103011440e22444000401d42400100300c01d0003c4545861a0a0b62a903c102c0400e0780400024040c41d2580001201ca0f040110104c0050031010b00454038001c00340c0d00141b100720449091300510000c68952803100030700c1e50544059030b00d0348411280202d0800700e01030707880d00301100709000c1da05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 739570845 1250 739569595 739569617
    0x3030d09021801151805040c03060905090d021504020105070b090303040c141309110a1205070501020309100f03091e0c14210a0812010303080906250e0604060f 70
    0x5031681c0c003641224001000904d400c100030f04111002110313048492004404114003041558881c8201110030031582c0700051010325003c009403d442c00200754000c16044400035500700d0b50040780c8128180d80002542140b0354a46c80103940600134960b0141c04503c1e15000c108211400000550040340500d48502c0d52070f44d42c20806c08514143c10003e500310900002846a15102d40c10030768000c2c3c03140c180c45800c0d008500209a80e4803d035444008402d48806101c4140202407261801400c000c1c4095440d003044100801c440e586800030384001c1003c28000d9280040c0310b035221040442e4412210308425079802d102e4000500020002d882417484e8920000340b198602e03034502001d01000d0840301003110101c2d00a42c00d144411680e4038a4001c0030040d4001402e04402040300019245c40541d46505504006050b50030040c1000c29561205d014081000c1f07402c0132920301c1e4091000c101140d5008600120350304c1d8516a00075422103000320b008101c1540180060f010010b1540c1c800301140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 739572095 1250 739570845 739570879
    0x302100603030f0509030703080307230c07030b060301020c01050a0b04140f010b071406070201094b0501052403120d020a030204051903020310060b030f070e03030d0902 74
    0x103403980310040100b072031000141c165500443c040c098500c1c0c000e090707a007042e60b40d460f071280340c0c0c1c0211801c3c8001011074500ba00840b8503020004400f5010302e500a003803103100e8a5695035440d080c00701800400350302d40080c04517a42501100c0ca100e04000091149083c0000d903034001e4908400d8445c4503a003441c01401a0141c1601720500c2035200036088a00d13a4070784480f00c81507a100601c00e41c0c03812514209070340ca240b010000680100c0f11a400001c64880c68203000591a460092003201c8055141201c49480f04070020007030b82a01c0c00c52907003010002d07180b0b0038074450a0740c03400038601d50811042200d03000c00c01208482c105d081d5403142461414160405032900b40000d80e414a1403410700c01584200303a10b5002d40f8248411f8100146400d071a48002030980310440f021041d0040248814811810706000a164041190030180000c0d801d00080c03074218000248000742d010184400522003d1203601c040d0040040a4152a615914442010068266190141c0c000c80c1503150500c040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 739573345 1250 739572095 739572101
    0xb0a05011203050d051023180114040b01120903170604020304030c0303090c0b04080f0723040203220803090d0c02011d03210c0c04090c0315090f0b04030210 69
    0x41e0307a15949107441d0544d8200000010b02c4041e01e05c2c0b00f100b421240208121201110050601403c061402040070034542005900b00f440281d011419186000400081c1c045039000c2000310700442d4046242146800100e403195001c2e90107455171424140e28800b4550800c0618030540001c403a04030031580d5075001e01003a40300c00e03500200084c07013103040040842d100e40d0215400f2480b4000a40840343e6490030604140c00030381001c0300f950400000c04282000401c0310300020300d920000c584010740706840d01c55501e403620a44500940d0000006590344000203000240980d00e20400310b11503506040442590f00121421031251090a981001d254040c041d80b11605505a550b445101c41d1403000010b02080350f00740c40c0d0184100015109500034aa103550b800213800d081550b10f41c188080428544501132031804d001d0f5240080400200d000d04000d041a0390300604a01090080c407100b0301c0081030b000074080d182c003503414141d074200654610392502442c000d030308440903410022004812 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 739574595 1250 739573345 739573379
    0x300b10080c0f04030203032a0f1f020d021b1204180f0e0d0210060b0c0d030e030403050a1208220b09012405180415020d0b030a0b0a0501 60
    0x10651820000700d8490501008100b0103821402d414101562035022910b19005910440d17035041c105030700001104542000e40c0750a01e1110020300104100e901110b844800b026501400ca00e0103801d10707085050581c0464078000081c01e400c658403484548070841001105d240c2e2141402000548102c03c0449810313182680d0302103480603ca0142c1031039020007841d419580c2d600c1030b91546041c40c0b42170014480100128081d80142891011244241089030306136007015907420700a2020b005104800204240c1d01107031818002804514030300020300d54041c41d40020a00e203d00c0031800304224035045054140a21354850f072130305440b01d66058500e044000d0400d6500100314406001145440300c100d0303000585d0b000001030b8074924a4003116407102140c060310b003d0803100e00800c06800c244800d621401092000d1003841d003016600e03140050f10350f0044085150300030502481c1514540d2000020180080c201d0b610030a5900d002e00c80040c4c12100e00040600d4034000180380d0401d4841d0500b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 739575845 1250 739574595 739574597
    0xc0607020d020c0f120328090b0d051302100203040f0504051e0403052101080f12030f280c0206090f0304030f060f0509030c010f060609060f300b10 65
    0x400b0a241c3e410b11043c3e07561540003036448803280714140c848100034401400c01e286544090040b403401c0c4503819842000c08008007080141d41c5208000906050040d201ea00d0200c50011400340c40d0700c12040010300c05c00c0c102940c0720010340c00005000d90000020400c0740c0300e000f10000c8842c0ea4108201c01c0b200112aa083d004019480b42d5440c0441145902c0e4428401e041403070400d1160a4825100c8080d000c0442d0410502c01c018805440200314007516907030b802005001d0001c0030301e030742d080030f0201511441c2e0602110340440c00045102c048081c41c99002c1a00950034515036145c0c001130000c03400c9a00241c021140170440743c0b8800300760030032903504110095103800d165035a003a800079540d01d4113641a40e6900401100b0200500a9600640451004503141da00410340303e402c41e120100181c0695141603002c0001d250807003005012510303d42001113203003400300826a607481984880c031915803040400d64100310074002e1011540148201c0812038031421009100054107600300e144 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 739577095 1250 739575845 739575853
    0x2010e06071b0606080d030b03010b04111606020d0906061706072019060e070b09090601080604151e0b07111909050c07020f06120711010605150c0607020d02 69
    0x10003114101d4207115551803207281d001130345903a294501400d00c402284010006a103458080702c042c50700740110b11001104036001c01c040604400a020944200c020401042404203c40700520400d41d05a5030480740b81072081c8504410792030000020226405000300d9640000800902204001036803440340900d81c640140d00000d019014158003d8200b8040f07091103180c01500c2c101c0614000c0104841c0701d03e10100d030802c03402010a041600f55042841e200c50140840c0106560b07480303405421034001e0900748544d0f201c2c4400302d00034011043e040640030358214030004041c0e000340d2141c0c0c40c1402100b5040f0465445450190991142400107043d55040d488a44a42d14201c059042604080350100581760703500d00405017a51b201b2200300b1a6400082040001d606000c040100f82e080100d40d4245414041440c031541c004006e0951030401c21049101c081105095200c5000382c00700500342c0340c0080c0034410b403041c0d0b50710502e00320b00c09006040108020038000a04500c0c100801d40281c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 739578345 1250 739577095 739577117
    0xc0114040614090c0910030507120c24080a090b1501030b0616110105040e01080610090e0a060b040b030f010501050f0904120c06140c0a11030a09060e060702030607080702010e0607 79
    0x80b9214003921b06501040c0740301e00080090350030000c5500510149154022685050406010034105540104182c1404568a80b026800c1002c7ea00c0d90201c142810100f60b1144070501d0002d05519030010a91140541403180c18110b00720046c40e0030344240c0c1d00b48080c01c0d850052100038055180c1c582c00b1a1000c0b10300f0070018000f840c0040c440380042c90118149a075603001c2c00c51044007a0300484454110f0010300007141c9440842c0806400d010006102d082c2d450f5801c3e944e103240000c001f910050391801c0c031403815a15508040d81c0958010704031a40404000d0b0360900070300342813260b01c1c480e50b90680000e102d4108685041d05c00c036089600304420b1000070034203803514942050708942c21907903000980400400907030f205005404188460361204c0c08498064404c0b24144034540c11a4401d0100030542580005110213540440c601842981510f401240450081c5034000307500d130280200f040080d0b0341c040308051064103280d00900c030a000c400c0d00170ba1240001d031075440000342c85940f4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 739579595 1250 739578345 739578349
    0x318063f020711090709060f0915050c0f030c0102040e010f0b0703050304030e0604090e1e07140301020c010e160902180f01020a0506190c02060c1e0c0114040614090c 73
    0x600490b5000b0221282c50384001d20000d1110310b021540c40c404503d00308014050790b680100100d0a181ea01d050811043d4107028081c060308191004203020070100240503460b19400748481001d103c60b01e001c50f81c4890f80003003100e010390450f0040d03038841c105d2074000240c1260340c500c2810032150984075151506901d61800c13244c80e40020410303402d100d40c0054800d801d8660380003c000503c01c400000611a00000303400d810200c1a05c03842140c4c01c3c074040f2002e980c80001c43c0d65000c0b9819405000c0e036280c10395000c071707000e40540340881c4901d528200350003026a0b80840c0c110072500d401a542c8202d00d4503503030140100d0141d841d0100850a07841c030341e01a41d01b805d8000c0808980140100c82038000565101c910304001210003484190421001d031000ca041402550039264450010345018900322038908094000e542070030044a000c48550101421800c044843c1075190f10000e200c40810060800b00c5c01c0415501104e40500d0140d44049080c9103204050154032543d000e4072400d00b00c942 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 739580845 1250 739579595 739579597
    0xa030203180f100c1703010f060906031e05060319060204051903050309041119021e0d1b060e070803041d150f031216051e07030303090318063f02 64
    0x7108076096101c0e10407a844170b4003030030b0140d8000c01900060040d05030410800511074000c65000030706050610024a220320341034102c0011049240c500007404d03030385487c002458030881c5001405180041c3d000b800610141e41c0007001a16002c0c0c0d0300e4005441e0001090803c041c0510025042d500b060001c4030303003480d20350401d001c14861181190304066104005941501c4001c2500e00940e0052802c070507440c15071201c21403505803080152000d80b50510000e04a001c038904132240c40744583c8a84401c11410b503001d2080e05003820100c4140c0340d224511a950381c0d01501682885034545032903005001c0d0340c046c28600c03a00b68881c0c5042d48003c00c1c03040c00494048507081542c10b0085e443d040c0e10960210003c1c0149986082d13035031101c40d0b13a5080c80c0381444129424020151103e00003143c041f00d00107080130849a1519001640704e07003505040f02c1410503200314402c1d100e00314200048070707903002c140c03e00102113988940352021200301565000d224010021a500d1480c2d09407046489641d078 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 739582095 1250 739580845 739580867
    0xd021c0c1b121415280f020d0207020415151101020d0507021501082a0301060506210a09030e120f06070903060507030b0a140112020d050f0a0e0616110a030203180f10 73
    0x2e20120301186d0b922216402da8100d0420010280e074007203420000c0d850710303005803440c7c615810b80010b19036003455544a40c0d1101c0c00c8504043c4603512107503e034006025412900c002052000810043c1040c1c000203440e2084c2d5454603990341c140e20000718020170041a40b94603940c8051500f00384042c490380d204940c014040e0482d9140d5624580054181c40e640c1c024602035009010b00c0700303d03500300040c211030150060812200310703140c210300100198001da1405242d01c0704440c0000c44000a4031450701d0010310211594190043c0e606009100b9007100015007a13921425042c4250b5071283c41c00c408694441a4681c0d2005042004000c000c2400c80b049980c50010726019050188465540042c2c0c2c0c0154000e04c0103a43d00c40c1040041403103100126041500440d0502c854070b09410f450741d56000141075168100c2649150f0901c5070b01924100e0305803202c03041941d0b038910340c0c2e060103034803500001d01220030828801d0a015003441c0c04d107401d040044000301018080202d034082155006003030307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 739583345 1250 739582095 739582171
    0x712140915070605010f06320304080712020c1c050d050a090e0c190c08041e030209070809010c03060302061b1e0d021c0c1b121415 58
    0x401002d00410701d1801094044e02003111040065403034400c00a05016400c00c184e440040300c803160170104141004114050803504240c1d036140d440d503043ca0100c40c8117214009200313640031074541d0344d00c03a00860b00b10100c0e030b401c0b5000e030000410485280d08a6040f840000c0458000c0d80181292600a03009051504081d2400308280350301e03080c1c120b032041d8080d00c00c041c0c0701c540495124200708411200b25804d06140c500b0b424084601e80d5a42501d02a901420014003040702007a10301c1c54400c0030310401107400400310615400d1842002d410b05005981031801542880600510140207000c0c030400c4070360140c036040ca401d0061011240d109852000319070107018280348031004c10070550640044440100150120780340045002e0b103041340142c00455004460a80b4654440e0031021030b010040d0454942503043c0d04410f10000002e80e2500f10310b507802001076510044c403400307110b9144040111011030394200850f40c000500c010302243c55044d82c0b5848088a1004107000c0c4039080c04402c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 739584595 1250 739583345 739583347
    0xc050a0f0503250c0f08030406030203060316060804020f0303030c04030204240b030f070206102315090405010f150f020f070617131101030e210712140915 68
    0x340749845003030b900083c4840c00d032801510040f00c24030802408450041039400340b5101d94034942413082d070301c90045205007014141c2c0400029110b403014003604010104481c1e1681f4516120040589004800c2c1c8041e07007d0f100e03461010303500c0e0400104481c01540f014503e142000d1a5500f0440900184810860010100b80041000f0804134503060098070035005400d40300c2c6041c0c411198035140080c1550b04660021041c80241402c041520042c0c03854010550900542400000c0c1c14014400c40c5a0b0040c0410010015010000f006861104c01c102c9041c0710030799903075070403c010501501502500400c00025003100e00d005296041e020816401070b00c40040030907100c1c1d41440c80f1980690081140c0e070342410201080c60300801e511007250003c50200601a45030920a550012103a0303060658410b081c0c1c02e440810840c038105040d5046400340700d0400c120011490b50407104048588410110f20301c1201c0e40079003c586d2503000c100d0942410980d6500411155080720f6400140c200d0b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 739585845 1250 739584595 739584607
    0x1050a060f15143004170a030e0d090807050306041505090a0f08030f0115021c090801050a06030606050603010b090f0f090708101a18151602030106060c050a0f0503 72
    0x8207603020f0003504c06a10300320140d03140c480c2e040022060100246001100000041100142e107543e07118540700b100741807164443c40421000e0340104480c00046815203e511540001e26510041c20015161600d040c0d035a9155610241503548405441c0200340c9203400d51301981d11841a070040798000094400c41e01d034500b06842e1b0703100080038440150307401d0f2400000c1003045180b4a00c0c4030300600c00c0200c02028101e0101c4000d46403c804d0070030082c130ba0202428000e1a074840c0035a0300c040c2c41200001c024900f00a000007005080610007214054101800000d161801c2c90540781203e1641d0301c4503203416440001c00081400d003804c0300b61303c0840090b200d40b030b5441c2c40c0c0c42c861040107541c45190650130210050008108698480d0b4480034003041c050001c050100c095611043d95000d50250008018001403114180c85c004200d204102080b6054050040c50542d02110300a8008001072900c403071044622241c2c4020243c0b00b68005070341a030000c0c80400c611103895002e4025241042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 739587095 1250 739585845 739585877
    0x321120c031803091e03050d1d10020601180b01020304140406031a0604050c0c120325020a20151305040e030913050709060c1712070201050a060f15 65
    0x100d9409a00203100e65070240404014250303028031000f40461005c1c02d5601c0d5646041c2d4131034040c040d81c01004065802d0045107206018098042c050040205600c0c400e00d0700003d665100074450a40c08690100d040081021544140110080706038003541c902800c0003003081141c40c1011a09400560b03a010020125080c80c40c0c50810b00300c1d80e5003507030442c108201004252080500b190700f15100400543c6581400055549001802c03510b2150312656200503480005c6060080507080020b061660f0365016804951040d80c075102c4e041900e013203004414201a020b0610840507040034a1070410700d0040c0120001d80072200302d0001e90020302d80c443d80072800346c610900c6541c3e03055102054020341031905078031400c52106007660400840c50320704801001f0710a41e10a400c20701582d0034100302840100c10b540480e142c44942000c2c2e1300c0010320b05160b8001e104680120040d40307024007089040c2c42074001da204a07103024581555242c20f1428040c200da240b001c00200b0712a03101d00354a801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 739588345 1250 739587095 739587131
    0x8010203190b100915020703120c2901180207080706020c06090f030a0804110d051006050319020f01020f03030c0316080405150c0c0a110306010506161502070b100321120c03 76
    0x1862059032405107012b89031034401d00b51240d000002801051880c07a45030350020404481c5d04403856400110501b000c500808802407041d14405414070000080d030300c0c188016900107007400700d5407804a5000760380b02042551a0a400b40c0080b00d107800810010a0f801d00c10602290014061300044084400d901c0c0050408869403d0444840c1c00c900350340200c2c40e985100e03010080405401400d650311440c4160b818041400c2d10080c41400752405811441e4800c001ca003411186010469581c0c4c1002c3e01d5100882d081260009428800d081c8500f503400c3c40b861074075000f1680302c0000c00019040056003944411b000f041b5180313540040c800c08002c4c4a00b000302a031003d004050614040405909050070b111050300654020274081105220441035000c0d02c0c640e00e5013001442505841c09036182010b03200300080985102c0c0060184040c00b040b00c1050802c0302c6c812602c2a01304501e02c18001916120b020140000c00c031a00d03c524410440d40e000512624280e2400045c00340e5050040c1c0b00b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 739589595 1250 739588345 739588373
    0x1e03010e190209120706031104080c1201060302102706050304060b0f150705010608010203040c060c0312050f0f0a0c051e0c0105040b1b1903090c08010203190b100915020703 76
    0x1c03c0d03001074806c004840e09072203501981468000380625040c00e007090550b440d1800361420303004000055060751103034400c0d40050090350340108405442c2c460003030f000b40460402104103052488101d199004140c0c1c2400340000c0740c420751200c90660340c8a4480f8002880c40c10001a040002100a0691a501c250700e040800f8152080c203600c400b120b00b01182181c0481d0005680c0e84e10400901001c508007030a282e045070307441e1500801d12602c61402302c46c410b4440004055003410324052009030300306001e02d98031451400064400d55521409044141d5000c0500b403400304008120040c0c01403200c601400d07184654102d40740c0b0f1b1615407990142103500c00c4074252100c0701c0380f0060040b0071030030510f2850300c200800d100b2800c0c08004017602005441c2c11140d2000d040e580c03404802009000721981c030060460f80e0085490749014901c696200f403c0f84030041070f0615002101000386441500444042007540c0c1d409441814040002c03c01d0754801c0d940c1e0203600c14481f00100241000b030b0300b624 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 739590845 1250 739589595 739589629
    0x130b0402040b13080c0609090a24080d09060813140f2401031208090c0d050102030703150b030c160f0f020a0e0405120a030e03040b1e03010e190209 65
    0x40e81d00d820f640c8a03448400140c1041c1e02c0c6400c110700c407504130390b100400d49141c40f1041791420310544070309030590003c0000c0c400c0000c0d1011500c0444c03424800c0520050203c0345d140c0161030b500e610480d01114103091b140074007000b0034004808141512010103149041c140310700c019040f4000c016549901d0003600d03c07078a4905511080440544038030304a44c01d13010056004a038074040d415581c505400c195612800c4d0100f1044000103807038000c0800c81d9082041c1c0103040419031148606002d03010354012215103003c42d041c180316405200504035982d003210b6601b0309041c15616211081d440a62142d1007a10003c0e10035007041001c10100074000d14150312861000030606101c0c4140580404a0b07480105a881d40204000200e00c020403080f01c03000201c2d201d03594981c6118000c3e40180040c1503c503150748000300d400300355a008100148401b00d0382c0c85000594901d041a0f800707280c4000d0080500c1c0001510100b180c038092100c8441d0300510107907001d4103100506010071400c8000d061815 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 739592095 1250 739590845 739590847
    0x109081207050c0306010806040303090606030f1505060a03020319061103101d1e2e0f08030702100c080d052e2303010204150504031101021b130b0402040b 68
    0x81004410400045143c0040d000383c1103e62500d85800d4071507500503c094245030702d51100408100c2203038440409140e0106042c07401e4107450030825440607880403c22207039403610000c078881d4a0500031140840350b0040040944130244500142d03070382c2c202d00c400c40310542c4980c0305489848420300590300c1580302000e07211042d0316204507682c0354510010301004070b070b03494010300c54807055081a030000024001c941003569181d1005464080c8507180031208010180c004003850703448110100700859117280070300c841242d00d401c4100e44900c40e40c44000c2d44000000d28021086006071b0803028000d0044070002e0501203504030301e9094410440d00020350402c2800034441112600e00d02031107024109411a203058146074000c41c0d8610300501070700c11840142000c002a6400b501180d018040603e03c022801c551004007800c6a0400e00007182d40450640c26035019510016801d20340280307640801d2141c0c0516014808030320f840d103c40103000e5813104489182a280e5000800090030781c56103803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 739593345 1250 739592095 739592107
    0x2040e07050712030b0114070201140a030f1a0d1b09020a03090209070e0a21080724090c05040f090f081e09030d050f0c07180c0f0c1101090812 63
    0x400d95040350f000304801850318210850070540d0740405080029000700100c955190308900041c3c0e003014407510b40301c040480004081c404a90f140c1c01038407112781c00200901800760f050b51103a0140940808468011300145a05000b08480c03040b0407078145000c817621100c16488200202c2640d0105100002007a1200003507802c5003814082d03135030f00241a00d02524001ca501c0001402e181d102d10420801c5242100384120802907221122000c0e5405190140c0d02e61191611404103201901d51021003a400b0504014000c00c5015614049a000081024507400c3c00c0801000b031480c0d8202c00b418555403088000002c0508441079441030007650043d03161488001c0042c0c007040d243e080000e01c0c40c400c1c01942c001e91030020b041c1240d5256406c080b034807210040d00c9508140118024001c092180d00000526040307005080da640884409041c420f501607001c05a42208c0744050100016a4015904000c950108590b040f074050500d40107103443c0d603550003e850710045110310703072916600240c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 739594595 1250 739593345 739593353
    0x110f1903120e0102030c0a02060c0c040e010509060c0f0403170f0703020c10030e03090418051203040308150102060402090c2a010f1104030618081909060306050f040e0102040e070507 80
    0x9000060001d20007149886c40c451324040d1608060100280601c2000c03c81508100c0d0030302c80c80382d43d45005070041000200710201c82d4041d01d01a94000042e014500100c1c44082403241102e80c03c0c11107014040c5890700e1955061004240d21002e10307500030b01400740701d880e2a00907005090040c066801412040303843d40070080c070b50510344018420300d850300c5408011500302205035103889504450014904101904280c144031015a00401500440755047c06002c4181c3c06035010780d0080d03031402074560b0345004e11408030b50354100c01030160340508001801440c0100348140c1c0540d86003006402e00030100c080f4000c00048100341600c420311200d82030744e200000d11407120360f418602e40030b104031805000781c00202c1c4600e0102414154a54a0a200407106030b44880300103031b4800d046d031796130300c4080c201500e00c3d29585c808600001c00148001a5a0b4480c1c06104255040100711400042c5201c1c1080000c100c0082c02c1034065400b80720000f010304103076100a20480e40c94444559404062174 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 739595845 1250 739594595 739594607
    0x9010b090f1003060b04110a0203120c2a011d011d060c0906031e010f050f04060b0a0507020307030f0c0e071b02121903031d0109110f190312 62
    0x7007400058040069080040c041d2400f100d0b0844000100b6a0b860000306010b0950074406d0011528001008903405034000028418041c021990507041e841e10310340c0b032010303105010f80c00030714469101c0046a00d9980c2c460300b4142d82201c40001401c41020b03954107911001d040320f1010140d5444c0680000d404203c1108003150000d50f010700034514100380e01460785d003d840c44450043c0800b100140310f0038042d141031b1001c1304000d010250b10b50ba444201c1240c07102c0d6402054001c0060039202d09060030240100f07815200d2420b481c2c0d0030007500e0003003142d0319003181d00183c0c1e040c4907101c07000000c81e010a102c480b4503805441c03a0703001c03103042002d0b1840500c406401e090420440c0c0000c588181608280140707000e030b040f100c0010700c0c0c21203040580b81c9410f074a41844000c0300d41d80140308154055024004075044070010068003441c1c1da080a00701e4600d0306000c4c081400c68542d010051910003280002044020055102c4901300a0403c040440a4100f00d80d10000c0da1540440076030850 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 739597095 1250 739595845 739595851
    0x90b03031201260c1e01022401150315150e0d060507020105070906020a020108071115090c0a0308180d0b040503031e150111010e01090f0c0f030f0b090304090509010b09 74
    0x100182406802c2c03401040c40c0c200c001081d10200c4145c0948030b0752036072007488503002d400c050312020310155074002c0a4000c42c45082c450071041412240861a0340b0340a4021b031001d0102d004080850107103841000b42110381141884030801140d1a00c0c480c1d0b0750394000c400e0031801d0084030b0000b000c2c508140080d0031500d01401c10400d01200c1c0300304000a03a400039060051030707428681081c00c5c3e102c081080d9011000c900da05805405000140900941181d01c1c1c0e034416034090307046034281804074040c040e1804c2c4500003d001c0d49001c00c500544000d0a408521146c02c001d00700480488183d1030b09155400d040d14101c4036a0000000d00c25180040b202c100190715902081c0c803d1401e181c580038130581c0c560100b140c14400000341d0148443d1003075211003004180040248070341e842602c5d0000f5900440d010446041625860221340211064400b0059035400105102440f26035141e1301c143c4900100180a10700c802c00c000320300c90b03083e4007a5a0085c03018100200d4044201810012030803401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 739598345 1250 739597095 739597169
    0x3080c06010b070210050c011107140d0504060f2d0c060b04060f060309050703170a0305090303010e04140f01140a0b04050708061314160f02010b0109090b03031201 72
    0xd1260303801603a1401c0f6940c170042c842d81801c0c0d5a13685000d240c1809040441c00000340000b02103a103900b0702c00140100340800c60064141c511400c100e09090310940220b024180001d2042c43d4480c201901038110346003200c22503004500c4910003080c1d50040340140c2207880f400504444403001c1000a1405500017001c0e0484007072003658201190b0404d544100d02c03900d0209a12041d002c018032906208650145400c00141280b9105404c1c03a00000d80c8101c41c840000b034508000601d0949001c029a4161001012111079607142c1e51229020011010603000080c00303408940310001030244207140c8000003100c0e42189078900381000300c04070b0350000802d078000e034141001c01503441ea01c04485980b0100441d01120416000c540759002003950449081c20f0004d01d0b01070102c41c1c0080c9802031001350050740c0342c0d503400c140f1140072403d942404480342d0200303501c400180f208141c41e4220009848014080700d091801a1034481c0004070301303074000f400c603031080214901000802c5007070320825180c3c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 739599595 1250 739598345 739598347
    0xa0c020a02031c140702090f13202119080408100504140a1a090a06020304140607020a0c0308031b1309050108341d01081c080a0f060801020403080c06010b 68
    0x17464005c12015500140140d1155032400c0020322280800e0b6010741683e40c001c0c003a0b064840400300a650100003281d00da17481707034042d0210518010080049829180c4440010b480d88940e8080c100c1007140c2c272b044040b2054081840041801c0a0030416406401c0e215500402e050030301342801c5040d01c68a04403200c103078000c0c605e8100451281081d00c01080081c0105001580d81c082e405820711460800092140b030000090009000ca000b0002185240d040c081e2000d949406038203980c0c41c01040002400a05500810800f00740002e02555011200c81c5030384200e42a0760039000c2c06640200c20390707030340c01c034003248144081d503414810680508075520051a246d0b40c01440d400e6041c10880f01c52250301c280300e00c0c00c155400c42e113514030020005280c03406806811114a445040c40034041d0b6001e40c800c5c62103900e050b00a01880d0100c00140d40c403840314a0b20b2b030084110240100c111200b980c0f54a030b0700300080044003403008100035401031044c4d980b00e141e02c0141074102201a8403552400d68 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 739600845 1250 739599595 739599607
    0x90603090b2a0a0207031a010e01120f0204060e16110c150403051e0d0201020301150507212a050c091306060312020d030c05030a0c020a02031c14 64
    0x2640414190852120144035841c0e040620a09640090750426910b099070045504a40315400042050990b845040008009441d251004800720030902c650040108800010807101e418003100e481c800d17000d2807034482180c02c1c6130085015039009070700005440c1e80e15401c1164400c8400460307074500040749400f03290206031050581d90352904000c0036200d014a40b41c0710056462a5044178000d6900c10241c0d034240f1007030000c0c0d00e28225803189050f1603014030105402240d106208490503030309400490240e07114910b800f00c2c0c458000071000c07240040040304000d0945d4a510390b5000d246e04960302d020b400c41d40c90205074580c1d40e00c0c07102c2d4100d640440515070005503012070b030804034050654801c0c10b15604c2510420340d00200740f0000d46001d00d0818040240030411044c1003a103025078085500819055000310221003510500d078000540901c04101c001c00300c0e4201d40c0600031207104550707603260b56800090070842e56000920a00a03a6200403c41d960048404800c0c0c0c0c41300b40420342410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 739602095 1250 739600845 739600853
    0xf031202210c150a0501030c090c050706020c0102120114030c0d0f0f210504090b06070c0b0d230109060f0821040312020c0301050c1e0702030102210103020109060309 73
    0x8030800c01e00c0e122404590062941c808004030004990fa03400861181d0421000700002041c083c0015124424403c0c0c010400358500c2c000c51803602e11540e11070340340542c680c40703140081d00403000006d0b2a5400b04076240f0491400d039038240c0a001e000406415400100e000c1502c2c2c00b403035141c503070b0107041d1030780604010844c14009610116080754000103540154602000d00999403585004200341103004448020b030b2180281081d0750402104000320341051081080502030707034000400700050540c5c148400390300d542c0540000c40c80b9000110317410f07442d510220080c4882840484444a440380108514802801501c00078000505100802d03420a0142da0b11064415648043c1968588c10200301a809004641c010b54002e4103061a2071000071000b511440c10b07290b064402d41c08c14010802250b4008102c88a04070684000003290404400c1c00140760030607203003640e065600b40100000d0349c0d0381858111103a1845003407100c00c0d40c158400900340070b1864011800309072030a40180001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 739603345 1250 739602095 739602133
    0x30f04031b1128050409031115161b060c030609020414210a08130f090e0607080603070303080903040b13090e06041112070b0d1d030c060f0403031103010f031202 71
    0x1d14810b030307030203d00840319050562301000080c81502030381c80b801d030b1440040d40d1003131901400345c08110310301622603000f4081244c122583d80446e25044902d8442c810000d030482c0c1c064441c05c4210f00b030100c1c0043d81d5110005c203c1e0000d600c10b00201110300c0c9190010726000480c45050b8400c1c4010019400e503103d542d5646140d58070b002441c1071800a411144152030145e500010f003403003102d0344001621100c4960107080c8a9066014130f100314000300c0c8005024645041c0b060300082d008003852841e645049030808400b81421465000400c004112a442d4000400407001d17150707203c0c10341520304003811084030300d03072071451009812410910001542132041104400800c413085101c148e0407170781c001d00300321403a801700c00d6850340025245a181c1d65034103c002c0b801800048140e0b0804032006560f02e074030a101d003030611034001000188007894000035480e00580685000254000b0040706155180d100380c00c603103101030140204008001e0608101c03106030015101504c22580090303961000d0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 739604595 1250 739603345 739603349
    0x12060708010501110a020603010b0c0606041103191404030507140c0f090402041407091d0405060c0f04090c051c0e0615040b04051302180c030f04031b1128 68
    0x10064244c1a03a00d1410007080100c071003540040415640c5c0d655111020550307031102e04020700e42d005180019165180500ca0341c54030074000101d1525640d075450503816400f00c1041c0d014991030f070350b04144030320804101100d8852803094440a6850005003020030140308001200d0100b544102c80c40500383d11841e141c0092280240c0780c41d8107944452000034040c15428182684079501403042180103a030103407410781158445601d424034000181c03012560302c00101c0d03010344598440c1c0007280840341008010541d1721aa034610030305085d03d503001001901c08021001001400c0031030750a9046007004e030120b4240c02408000c02001091611007a12158000c0000f4110b106032010003000f529560040c809600e03008000700164604050403096610a0241c00c2e40030700f13041c6038400f0454044000c05070054500201503802d55850b2500d100d584e038801001242003040b120705e60454404007a158407515845034044030142c034040c4040c482c600f814a4442701d03100d003041241c21401c002154404003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 739605845 1250 739604595 739604597
    0x15010201142217070309090e1908130b0a0306080111040815100f030b01080d020a03171e010b0c0f010c0f030b0a050d0305030f06040903080705090d05010e010b12060708010501 77
    0x4084100c43c10048034502c00345080c00401c0301c0002d4800e0425a01200c2c0380300742c4003a9102045500d00d4a401607503141024070341c25181c0580000584086201d90010700038800d9485000401e035030300c0e2000c403009904592002d1020980382c58007400040303000c0c01429a076090a42026042914090340e2540d900c00442c0c40d5a03a5a1102c004140c036144803500040181000e009408a5a6500e1074000d4034036100348039128483c01400180b20041d4800300c0c100360300e00c1c0c041d030711740003d241301403980c0121040152800603264400320407440c6a625844665000700000158140c640c0c5940368010300740380001030808280c2e40b51210303410b1103907003100203090f01c440285000562240c0c5003000c01c00070700440d04400d07400000c0800d04010558040000d40c03240b034200e440c100741d0780c40d49014031040d1000301c41c00401080ca100001800d042c0f050029000503080140b0f030982d8865030341c8603d4211625030159040e1a511759807003204c1c03400c00c01d0300c840224410304000c240c20714044400504840040c0580740c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 739607095 1250 739605845 739605901
    0x90105060f06090d060b1507060b03010504030921053f0a0e0402130801061508060f13022101170304080316030203070803090606010909150506090301141501020114 72
    0x642417002541c400b00f1042c6000d420b01e01010041c0502c0201504001004c8503001c1c00c10084c09154101030040e98021645a200d0710801c40c1011321008001c044101c1c990907008a003840392004c50410001c007404008071040c0d07104e001c4c2c0d00781d00c410480c0030f10710802950a146a035400038003004400c1200d51407243d034507000f07624260580004010703104141d81e501c40c2400542002c50f8000d41988203034201e80054810003071100c05140103076400c0008603402603104011311224000e07410320b2042c1a08030011590014902103001c43c1e1131240031000300010b01100703690f070f0060000050846c0c1420302d44581c0130046082c145090200d5669110301600344c0d5008080342d80c031400701070082058400865020101ea40c49281480e50700b03507a1081100d015000480e40000051148414403584441044044940c0049414035052020550006c901c107a05507603202c0c8682042e01301c000c44280544030042c001807611402000080c207551060100c0082e502c2c1c0c03401440020b41c0381c281809800701181c0840c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 739608345 1250 739607095 739607119
    0x2250f2906011d21120c01050603071a132408130b01050f06120403180501030b060304030806120106031110051603180e0a0c020106090b0d080903010608030f03090105060f0609 77
    0x103181224104d025010b5225680140b0400810a00540440c86000703008000a95661040681e6980b9900c1440c4031007803110014016844401c0052450404010051160583c0d03002110080060210b13114010100c1100d860005036005440030b800c00e60400031021a501d240d00c400460401c1807041610074060a9034203519a2210002e0342c542400c21000c5503500d10380b500b400b40011518001c0c400c1c40f24409400400c0c90741c082d01c10302c90600c0000d04050300716515694259400c01c1c010304078991010503c102e459200703000740a40d8000d1031081400300480200c00c1c0902c0403c2440100d61410f001c0c090140c9814900f00c7c00042e612035405107420360310880844e081340289000e68024510740300c0035900300074800e512a040b4039103100c0d082d4000c210b51582c80e00e8400864840c500c3c4035a0112030911541c000c11040c4001d0129100d008000042d00340c1c0d10302c0c03194503503480207e042e81c042c038010042001140c003e10900b42c1c0000281c1c1e101c49071076906800940301d44078401d01ea0313218228044070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 739609595 1250 739608345 739608379
    0x251701050108190e010b0409141507081f380316140c010f09031b03050405040b040b04020d0903090e040f03030203190c080603070902250f2906011d 65
    0x3000e4000030002c2c20402100c0e0041c10011084045900410f486202e22b111050314000560240c0f80300e0100d03560340c44103949503008116040009036820307902d820528138000c42c80350840c0410301d052820503011030320300c00c541010943e0307508034026804e51858801e0040240310380360b0108444036102c007807401260a03215580d4055450088264042440d03203060160b910880d4283c2c0403a40b414042e84a4025084043c8568a00d00d102101c00400280043c0820801030519400081080500500c0030031030350884404513081fa00002e1401e100b40d40c0325040c100605401807100d40c05091a140d41e512285450f032905601c6018000c03000b01010750010014480c80c401050400d501111682c003849140c40c82c10005110003400d6800078031a003d00280015500100c3c400c540c2480e00e0081c2d964481c0c120158502400c201d505415030704030701c0c6280c501c0700040c0305030040c00c50a0405400120603090780ca0070769014400041241d4148240d64401030310018600031144401d41c0e044a1b0308440b1301050711 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 739610845 1250 739609595 739609601
    0x201050913050a1a030f07210b0f01050f01050a1e0507050307051e03070f110102030708160627140c060c03210f0f251701050108190e01 60
    0x451800d5452400341488180d03c0d450f088495002d024901e0038141194843c1016211801e0924400307055010600401c46407110081480c0e0303904501c00200c0c1d08003642d40b201906100102d80341a407861107400140190310703110010944010003882c3c4203041c00703495500503245002c41b000344c610903400c050024801c03138859401c4034007255220095039102d0015250207581d80035400600c03021566101c1c0c40700c2c9500c40000984420720b410070140601a0340c0f41d1a25145203541c0714a0a0460004000103c0401c04203c0108102c0c40c0107510103030228601d0030410b003250034242e40f000d12406a1143c010075817603100c03402c800190f001241e01c2c21030600303028410304e01140320020640055002c01c44031481c6101202803d510100b4102110152258900d0008268003c58200b030443e0910030105912031212003000c3e50161140700840c10006071220f1101a184e001e5000600103011400c03203007030a502d50110107005041c02e0801c600f00b400c011003001c10290301644090f40340c650340d1000c0c00c0d811380250 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 739612095 1250 739610845 739610869
    0x60405090d050f0c1c030e060a0e03040902032212020c0a030c1815120312060602070303080a021e04170120091302040608100f0503060a090f020a090203010f0f1202010509 75
    0x10007504605c0301e06014026007803000c0c141c50540500c01c00544800a00e001e000e140c80c0301c01c4051844c050900600c000250005480d0000e420500218141140300070007800812a010703051512403d400c10381c1c02494a6405030310b40d4000c6181c1042000010115001e81c019182d40b01210484000900c912a005003280b202a04404440d008009500000c20056500d814080e9650b0440981010b10328410f64506109030001a0702c2440c0400110780b00e5a011354101070700e02000751a119400b070400184115138440c40224200c00507040200e40d0b640c640c1c181d40759080d84000e0100c43c10f004031a00f4041c09040c5816a042c03c00034100c11142e07036140c5a4030303401c000104115202c40d165403006041080458154840c00c6500002083e058048007005045640c000e0007000d565481702500006040801c030304403012000b0700303000340041c2d03a0001c02c0380c00303400c940000680701e40c90601501c3c4424443e9011450107101c000080c4040d103404d1094003000358080c2820b9540741441400310740d07031842c80b03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 739613345 1250 739612095 739612123
    0x6030c0d111c0c03030806060d090309141c0809030111030a050a0e0f030304080708090d03030b010f0912020909070e0901060311062b020d0e010203060405090d050f0c 73
    0x200c00a04100c50640311014080c810b07141050780c51600201d020b12022110405030038580c1c81c900800002e40300e03003da6075012002810881c2070906140164055401002d411030101c0d10f5680c043c0305100c94501c0e0102040000c0f143c4c1c0e04c521003038038a03428890440303001c060040b080c0012805601d440940011f080030f00d02222840e80ca24010300a83c00600f401d03a1012941c6051182540c0a00380000f9101e00b0803085c2c1000c3c51554072565101461940310400c101c031051001e00c01581c0741d964101031011060b01a8030080b400e80118000140358594242242d010311151000a1220031440a001910664180e0340c030713001612007885d45480c0000541c0005110034841007040604201904964110703441542c4200341000b10701d08200550081c0d08241c1005152a100e040103202c11076001440150f00c0d450051500102080300390564203001000155070b9000014054141440e11900b03600c2501c10024020603c04210010828802d100c44100342d41008202800240703000d00100b120702d40300c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 739614595 1250 739613345 739613359
    0x31002160201030f18050120040b04060f0201110c010203101a0f09040e060711010c020d0e0d110616020f120c19080a210e01050d110d0e07081216060506030c 69
    0x418a0100c7c06050b41d4940c10860101254401010002c12404d6505950928060900702410040100c0d2b1100ba0003243d10110743d2554091481000880010b0080c0ea042400141c1e0b40d2500030085558049240c1c084164041c59035800501e55180d101034804040c202d480c00c0b40e56007014030024015241c0e02043d940381d8041c41e02803051030341c3c2081d5200c2c02070b403200c8024010100f01300d509a03182c4284099600100d00c8040711948589005c5020011142c8a104902c103d1490940491a240c121100e5504145000c0c030101d825441c00c0c4400c104030240844050004d500307806030807902c03038a0300381005024800c400344802241c0180e41054001d85444003c0741c90505c50750505040640700e00ca0444414580c4d540c0000708981f25848585a100b8181c44040c80c0a40143c0c5c0c0340c00a0040301900020300c4400d01c8580e2020856005000103402d80400803e01c1c242400d0507103042140110f032484004004008460380c2c2c50440000380c0314181c103c1400107541c0c0d680c04c0840e043c0607050030450f42c0415 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 739615845 1250 739614595 739614641
    0x110c0f0d051c080f06180405010e1f060b070c050405040c2c090a020d08220807090606020a0f151805010c08160503010308031503030703030902031002160201030f 71
    0x71107800301d48102c03a50742d942d0f80c190382c07038100c1e00760710441d0306a4420343c200106d580050030703803405030503000c0d0000d02c03038000041d812119212081c208502031140c050100e82107044030078090802c0c0544006000949202c92030003215960340b0801004612642d40242d4440d0300140a0003454a9144010541502c85254038040000030010100503050081c074001042d0b4041089204009070000304158040e089881554094482c2c00007904101c1c01800d400600034900385940c04503c1416009200c4c40c0300400c0f14501701600007041d0b03000343e081142150700ca450141c004c41c000040002d20181c0000504580c21051107441c0e01405801d4100e101052a50502c9004c01c6015801035900511030f03035526900307440d59942c07440d010280040d1000000c00070700040c000300b42024005c54000c01030700e80f004250b08400004c00e0540e0452441940800d9603034034010203506042c0050058507030a1901103103019940e4280b0945c80b0f0421001a04259880b0300d20302000c00076038032501e00341c000340700c070f50010304 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 739617095 1250 739615845 739615873
    0x180a080d09031a0103030503070c0618030c1202030c0d03020f0f0315030d110d0e0307080613110423061305131a07230405100503090c01110c0f0d05 65
    0x1c140d88011211002550090b81c407121141c0801d0f81a00d80c10b60300c242c40e640b2200b20480b103d4031483c005880e501e9075411800080c400c01f01f9407442d628403d03140c0c0c4460b0301e90ba0500344030b40c41c1540d8181043d0340080149420302d18001c10804070801c2c441c01d0041c0c496010a001e140e99019a425038903031190700005000080038140764800340240101e00303d40241112040450394240c041d0002c4540381c0c4480748501406000b201003004ca10300c00f40071169a1a6500c1c0020714212003078034440d110360300010b01c80c000d0003001480b00703034201000e603028800244614102000000480003110403112484040341c05592140a20b40c10086080d90610241c1010b08070101c407142c841c9422101001c83d0005017142455101220b44036403502c0e01c030036454130600050014524418024403401100c10040480c0070f607101e0800741130b0a9000d65425450b49000c104180c40c100d5111010382c144510850700900390000002c501800110540300c81d1440d26042d0003040f02c40014480007001c0b4041c5541d031032007a03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 739618345 1250 739617095 739617107
    0x90303080c1330020f04020708120403031d0105070e120f100c02010c0905130b06120c0406091e090f09230c011e050f0c0115030209010614180a080d 65
    0x4402201c6421604210030a042d0542c070b4070180e8005d402c01c000c203812440618059002e0310403203005009191a1404d000c050304620f400456044003c02c2d078a0344801803400354144400c1140c20018020841400e001e0809080b500d2654400307845060000c494044010082c42001e40d441c1050040701d14586840f969100a000116206001503182402c10b10409203c0c652801c1103c0010780303100b010684011544010780300320032495070448020000081020a8a031040c0c3c8a80d840c030030110b44507070034228010f01410b96940f020f03800941801103059a10341220b407400485440c881d001a4a840460012010b4200b002c40501040d21803036508006078400751280c2404040320b0b094500300242c07040191100c04030402d06a001500030b42d0142407070f03402100102040041d00e660740b0300784842c002c1d000c0d00790303005844a001c80e103222013800c200310b04103110380d80d02402d1b131400c02e200708440d01105050035010f4012040340d100400520003090380c07204034000d00641940800d6813661818041c000d456 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 739619595 1250 739618345 739618379
    0x4110405060f031b190e0a020c030f0d02090a0b030402061c060b0f0316020d02120304050313030f170307020a0f110604230a1421011505190501090303080c13 69
    0x1a291441d002003900103e80c40702064a00d80c0241b41955155030b68910001d40045d0051040b0b44810000c4102c055440405864140400c0e0720150b501d91800c010302480e544282d0002c5901a014000c1c480103a6422003a21420f40840c40c024140402144510010344829032040115010000e0906005409040114401c0154010150404192440032030b80c03000101c03d09030050300009000381381580400000d542041c0604100c0f03007011050234075109140c0c0b203640210350f90b0030822102010018403810400741041e0509a1901b145000030380691580501800140085a90600c080400042018440d10200042c140940b12070321218030340464819501c101d040b5403000b5000900b00d11f4040b10290036103100800c81d00400c031005080c8807103000c00010000704900b940400a0b0307001c03000d1007241d8520424960032100a4604024010300203040b218004803090341d180280000d0340c110710340b40c04899040c90018581e07540c14078409440e001798210146a03002c420000030f00e104c840019201 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 739620845 1250 739619595 739619599
    0x18060d0903031d0607120b0603101502061909050a0f060605091312050309010f2409060e07050a171f060305040b0f0a0603062301050904110405060f031b 67
    0x228181014001a03a41d00f40c20501554011000030300102c2c4510100c0c0d044050324000481d0341303101c1d440000d1854000702c802203c0240d05580030401d184511504c0005002c01e0300181045042c0f4000c1e401c248010b585445000d0b6444061078420018100002c104603900310040e09442c0c0b6141c9801070107401d06102c0e06110303180300d00c00704100c00518440101aa648510300b0340380b42803a5281a206504010a0000c00e55650582c06003000024081c4000c800350440c080c40c901480c03803403500310201d0542c2007441442d1500b4018000d100c098800150488914241651180c4c0b25000490b03080e000603101280c160104000d021520180a81040b015407841030a01640350b12410704408543c402c0720050315078921940416030a4a102d06410741000309220f011450f251280c4400c81a9aa08040c1a42e02e03212204488261041d2166040c0500021648815141443c2d00d85d03080c910496038901d44a80e0f030345d03404149250703105074010000b01c101400b56616190b556903000f40b000015101c0d14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 739622095 1250 739620845 739620851
    0x6010306020c150f06010e1521100503100905011104080304090c110a320f060a090c03080904150b031807082e1b02100504030c020618060d090303 64
    0x94030f9042c540034510410710840b4001c0b0668501004413900402c0d03110046e0084d004001090100c0d8100000f40f0307005442212103017440c8050740828081c1103004090954289003000c7c00e10030360340c0c0800c200d90031140700d0748085070003c224180540100701c03007200f8102e49240041d000a0070311022000d00110b0728070b04410066016020810740d4540c0d80c0340b084440303035003060b0102000520001d482c0b0000d6450701c60030b1030b5110003074149038411441100e0180480c0e4071035108002c2c0f4041c1000142e900c40341c41d00341030058000a5540c0400906240402007402a001c00c004c0041d84881e8032101043c1c16074201040302740d954408130582940143c0d00120344609a6209841d0b40d18009100c10490b501c180c010044004d44120b41140d143d141409142404018101038141c8100e5009048001e250900d82c00d581410298010b807400f41703001407001049040100300408250410f05080203140c05403061551841203008500000c0d045c0406c450b0b01c4040429591040421a802414241e100c0d417410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 739623345 1250 739622095 739622113
    0x1a07030510030b07020f060c040e13030c0b0a0f090c0503060f0c030601050901110703050106150206090c04020c0309030a0308150405221b03050a03031118011b0506010306020c 77
    0x46064500c225600c8040141c80e04003000001c88449196510100c10301c1640c40729603940001d54201075003a80c07807440c0c0c4080030606210012940c0c401d990000d000c640c03880d03011040c1d0790300540040d007031002c082d01c4407400d18001412a003540d0010a02000c00e9581005080400cbc03520000c90412401894041d2149100155007412000c112501540380000c600e800e50b0f072034800449140d404101030604100f9075030300001c8071180400064014510a10010030340c68100010320700440f000c440f86004652014041c03040741c07a000315010019032010384d8056603651001e04114070b18414818030640500c0b4000007001490791103240907000e0b0456103001e0141c10506001c100649100750782c1c1c160704940c250303d201600984960690b0003039219407840d600c044a0310f0404401804c0d10f07030042d6944c0d044400703810109a414410708107108020f83c2502d0502800c43c810f540001c028641c00381c1446040001d9001040399041e0482c8507030340c010200d032601e41c4c40780b07044006500042e205840e01d00c580468 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 739624595 1250 739623345 739623347
    0x1707030f0318030e040c030605090903071205070308013b070206011508130201090513061508041a04260c0f030f03040611090a03030305040209070f0207030803090c0307031a07 77
    0x12101d4140c040c2d0b18005500095003c00000348406c46034002030555400d00040c00d81c0701e1501c100c5c811101035000e5a10340056080401d01c1d0071003e0106020801c00b0045c4030002034000342d02070705440340c3c80c1031516100c20104100269541c5070724a104021098851700c08800c0d11048020300c10340700c0d6401d030380c4a40d0382c5185481403115054000000304420500081d504000840348125050052600410b00e40e501d00124503e085410050200c058030344406101404008c0c25100c03040301c062070184082d00e056203a40112094680703103000202116404941884041d4050220146000003503050303042c081208200f4990101c180d540540c09002003240000ca808810340e000320307000c2d0a2461541d601ca5a8000003419100040c001c5150280f0411009440b04011040914440e40700007032142018010864190402030003401002410b0098026169001c11041e0890380e004c2481034481e110300d0041800c091065135015014440c0b0413002060101c1010402001d031510403e0001c26222560 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 739625845 1250 739624595 739624631
    0x10050a0c090b0906120a09060c0c110a0b07060506031c030b1503010f0e0903040b07032c030319020f060403200c06071205090904080306030c030619091707030f03 71
    0x3900d640110180007201c500b17841d1602d80740e80700440314800a1410060b607a404100e074110340e03d10002803000000b200421100441000000f40300b25a862502d5240441404039480741b00b0004044c11703160008242691003c01007190b62403624094070600407854500140100881901a8810361401608a03941d480c0c41d412241a43d950040116603a41844008076014a010300014014031082000060301640341d000380012034801c1c0c0d1040c14174a14410401412600000d0034030a90f985d241102505503000001c90308200d680004052101048420a07420125580e003103002c10b0180f0400c1004045c1c3c00301e0b0a00c11648203046540180018615003076403641020811500034030100f2007400462103e00c85074481052074a00780d1f2501d68038402083c850700742941e08485080010040c051780b8541405031246501e019401040a4509819012542e010703010340b0301c0084e0f5884a0b102c051103c211034040f0121002440150349246a01d4000c00040201c0d900d28002850512080c42c0e448070b0072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 739627095 1250 739625845 739625857
    0x18090e0c0f06090405091006031101080919020112150806010302090f0112081c140a0b030102070c050f0609180a1401060203072301090804080f010513060e10050a0c090b 74
    0xd00a0ba0a02030f011051100a02c00034000c0012442018003024500714140140e5000d94072410450344807084402c00900300c184047c0203140d240c0c020b400794000c07541d00c6003407080800ea02441c1503060200c04424070001070203959002c0c001103080600204010706c1c00510141201c2c801ea518109603a981c40740400180340a00030343c04070100d075401d5040070481032130180c0200c000c1078050400041820010a080700c140800300ca00445400c001c2182408452003405418402a0002d40c80c2080702e0342c4000c1e08981c5809058030481c3d0301f04044d10251262401d03102e44540c054103600205031850508191a14100c422000c040e007850101c1c00700c0e0a001c803603039040300c0701e940007103050000c1d81e92074a0160107041510480b01c01c2120310a0211035090141d128814000c1c1d010f103942e0740c1043d084034140300c0180c00c002c00f5681000d01740306032014a62124481e044d04200001a000c0c01d01c424981403048a00c590302038923040c6028089103582030703405040e4400035a10342c684d01a654118142c0240540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 739628345 1250 739627095 739627099
    0x5040603080a03020c0c1809121801050d0906020708030f0109020a08060409141f1b02070512150f0115031b1107030203030403120f05030108120a18090e0c0f 69
    0x24010415901d010b80c015202140045c0240c80c01d0402103008200e600d6070500501004d01980024862800300c20300ca03400400b148900080d242241480024406844c2c0c00e4801e030402400090303c1070f85800c582d010800701644044150741c1c90f081d504002c1c503550030644150095120960000948615034401c40348c0c200d41c6901c40c032505503181020440108049441500c0c01540c00e4500c1c2e203a07020a202800c0004030460f60130750042e8200c0444411504e010200391000d1000740c0b1800c8400350000f41d04c0044034400c41e0006a00c008a02c04107040a0481d2040c41586803180c040c01082d030401c1d92024140c480340310750b43d41180400c039800c9042d43c1d034040769650600c040f5129640141d01c6003032211180c00780702d001c4940a41d40c90740824075540c02a0710554600c0001e004000c0c2d0f40358010318008c414103562914908650600318006c0e20350104500004284400082d100b0300f00340107556440c03a00221203d07418000d90358801d8400505104039550301c00d4014650003003044d140c06e5508164203c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 739629595 1250 739628345 739628347
    0x609010e0709050c0910021c03151401020a05031303120e0a03031404030c0b13290d14150a150c020d02040908180a0f081f1104030b01050a0504060308 66
    0xd40703040c0c0401008080d04032800c88074100800c10703040d140e48141600d060201d600405036800078803034048d21388020081002c205400c0c0421400d141c20b002001c242503400e0804428100900d080060380b5009848000414034000410941e0b808400003100000300c07805000004485600400c0845403465181c00b1690700511b500018004680300d960b9000000b031074241f41c1d40c0380c107840340ca600201d40050382c8020300c0d4180000b035070b000020b001c1401000074030010840003841000c1c845480c50381224592119480030f07000c030318500822980e40050f410311252075003044050502c08100214140c0c0f515040380101007843c000900c030f4080c00007500064425a0382d1203a103400729803c010707405081c100240e9005071500014008106414000c0546014060302412500607030024090403859030703440300020540e214401c01c04040080b40d018040200e55162001600d501c09000005108003004518aa1000f0801204011800c48264140c030344c1220094402991030007003100f40c0b01280401807207520 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 739630845 1250 739629595 739629599
    0x20c011713050106050a080705040605220c0e0405012916030309060f0203010f090c0f0818280c05090606040e220803070807030e1b030a050d0807020609010e07 70
    0x80a650050082e205000100d100c507075890000d0010340d030303680180540b600196001c014a14240c8a000c00406081e02d07482542070341d00342100d50b01380110403075035085622548500000c0348164084824074000800c10401540c50300b4900e044200750100d40010f030207113546022450700c0c5442c1074850f0700e03c5209860742820115501140604159803084039101e4803903442003403000c40740c005107010f05482c3c41c034054941d281010800a44030485640001d00090031514811290f0012465a20800c440340100c00d1143d848103043c50074a5628020034043c560f40007034a011448406c5030004940613008030b240742a101c5d810446031a0b000e68000c0e500220401041050b203003000d529a0b07002e10204040902d81d44150140401e10310ba030a030454152100004010381039400c0540b1a4022041e0301c1c081201d02c4103920805d54070000e00c800d481e0519000e4500c50302a039010040d801000c0d901c00c050f103244518040c00a00108801c2d91100007600a20f07001400d00001446580303907540000001f005054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 739632095 1250 739630845 739630861
    0x2100305042103060e180d03050103023f1b0906030d08181204050a080607080c0d0209032d0a05061b040302060c1501061b080307210c020c0117 63
    0x4585180302c8241a101e81d40000c10f0844803905a10a012001c1c1918480316000392290070034201581090a040c603100042c0003686540320001c141c08030f04401d44041e95685042c10401c00b105c00e21241c3d0410684441c01002c1d04c0102d04a04a08008066200c410b01214100002180c084030016010390100d4090440180304141d420b40241100c05400518820300d4842c5007071290500380c1080481c0c0000342007100742458982a0700800c07040b4050281405e0200009240a02c081d002c410460000b00eaa121030555507030403120703540fa00404841c106200380e81c1602d80b41e038a15490001d002803148030300c903203084041003800205138030101a08a03980d410402c03151000240022001400d014030012005803107405c01028140140c2d03004042501e40302400b5100c4180c141c02010401c03c490041c01e00e00d01e080c2c21140c4140e40d00614941c0c50f41d072400d07000c4820380d802164801540b9850340405820008981c0402c03c101d040d0350940b001404600010b40e0928846100d000d9001620710005a105c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 739633345 1250 739632095 739632143
    0x2040506011b030503040b0a11030420061620030a031119050105091b030c06030408220306060e040804050418060509010e1e120a1701030602070210030504 68
    0x180d414180510280d40e4601030603000b1080807000c5021550000c148401d100c00c442001e688940340240602c0a4100e180360a0614080900001d054000c0c6645881042c0300000c449100c0b101c0c09003030030742c440c0761080e101c2c822010021015100703050003103055900c07580d10150ba0440a00302070000c00424140e0350702218060091407505030305004882c4042e1880703c007500c00d94086401140003044904059a0315030400340c0c8080c401d5001100300403000180c0d2000314140000d4102128540d449a480d0f007061382281c82880c0c10201820780d0180382002e0721b800c00016400ba20300842007006000d072118119594072a0645000d000c0c060308bc041003041386820f4000c0300440001294504039900240d44a8043c3d510903100b18041ea5101c1c1d00000407400100007030741d200360100c451010100c00d11320b0900e0712104960b02e001e103510030000792038060301d00418110f0284070a038003c1c081d196035a414110f00940110381c0881c0b00e05601c2d240707607408034401d0040901031500022220284c550304401c08000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 739634595 1250 739633345 739633351
    0x61006050d0207051905060f01050123040e090d0207080a0b0a0f020c01050412030b091b03091f0605041d100b01021015141012090305090402070c05041104080a020405 73
    0x81c26000c110000000d03100f03020b0078003000c0c0d40085c08003404100b443c10b58200000140036a1000e01198010841a0303884119a40002000380003a003900942c52444d11840c4100c3e08940b441c0345074501406980e000026010b6070113a103a5090f03690b01900d0305103035510b071141d001c1e007d0159201c0d8004203290395501e500c0f41200541c0d200f801480e01d0b010a4802e0f0a584042350140e0300c4000a03800359a000f500360041901c030700c2c0e0031074403d003103803030081c42c2c0800900070b07540d809505000201c001003000004011400c003031007400d0a8085100719010549016089070302a4601550410b5440030f545098440c134a40d9008442c400f0740303081d09a0a080d20007c10310703d943ca031f046100f84454071350600520b01c81d001100d454140360362201414544400c0301e1060000e0800d0013609000da0244103103a1040d00c1c002e00c803402c801302058100990030b04881c1c0d8080e40d0503503039110b4030000d0603204000d030030f2a8002c21540180d07818802e0410340c0700c0005041c0118828102c864000101210040c0760a40c0001e0f4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 739635845 1250 739634595 739634617
    0x70b091c081501051303150b0906101d0411030901020310060903080d090c05060705060a0507050c0d0e19140a080c010f05070c0e0f07021c0e010f0918021b06100605 72
    0x44172941d0b84d1545050348010181d441902a07803a0755100c03c1c0e040002d54103034001d9041c2c0d0403464214144000400510001500070080f034000c000010103a40c460300401d07510b034240f01c680303030b00c87c1001c0c140c40e4001c0d40155450b06000142e500e002807068041d404950451b038200070350a0a041c0100c800034013806000300109c816140e81040451342d50b40300c00c09820214041d8000344043e149c00080a01100c0c0302812150611206204441c004030001810303140c010b41c2407802c504481c0d00040403901500344020480a0f24070040408544461001603d1490420484050a25030ba695000300d03160340c00510201d0000f0126011006101c0c010401031001c0c40c800e80d0013a400507512120780f818040280c5454000701620418440b04680c100210041c2c000b4602070040390400d4124060045805000c80030306001962071034012482c091422800281404440314088420a184940c000e5000b00e00c90604455038400f0741031a2200010071510403186907596080c0c250400e00143c9450f002059680 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 739637095 1250 739635845 739635877
    0x105040b0c0307140406050a0909050408070206070812070c021f0f1b020d0305122202150c01050f071b050705040e0f070b03040c050907080406050903070b091c08150105 74
    0x990071413041c00403c010300459030b40a8075840600e00c000d044040540c00281140d04100c10b21000c60400d508079005698104d44d003641d13942052410603041e0158021300c0b00c440040741c0130080c9142d001003030703040164130031150030308048042c0994011800b0520141d00014221500710102d8501130304100d10850141c0c1c00c00c102c46411a800070f908044201e8045000a60105082c5440340700409500c1c0c1162081c0b12940410b845003108000c80c5400d224068810780030100c4492202010208a480c180080350003400079140c84001109202801d40381d000c00100000a00819080f102404008242d4070501a00c0c60518010810014010400144589002d5903140035044141080000000d0070190001a201e1a2500b0541c00125503075201c540210883c03020485550307403100c0c07190380c800ea01c400c00081945605c03142c0351440c042d4070030080c01600c0c4a02440038050000030340082c01100b481030720300b004241c0d070f40032180310030191541d00b10300840c940001019800352010300415006070102c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 739638345 1250 739637095 739637117
    0x906070e01030e0a08040806070203040b0d0519240914011203090e04060c09120f0308040c15090e0c0406021f020f0a03051f050a0501030b030a0204020415020106080105040b0c0307 79
    0x290600d0200d1310125000c0100040400c1840414401e503584005c2a00256040610306104001e2500c526448406c6840d5120b0000d18801c540251441f40c04000383ca0400c0f1141042000c29040b90340c04030281e480840c02080054008100d000701c4e040d2a00c01c13840c1c0d80c41a460300b020a0400d002a41080f424000c2c240004110312002c2000c0034400d13030048001041c12484031102030010640e5410202019040d581c0b6140890000f500c0000700c00ea161400012554032410031060302d84c8540c004c2402400e28102d001c14203680138220009803842d5051082c242e4803054210f01c0b25104920880c130150b003100e0140e14a01c6070007101c2c1031880248a001515020402c92169000ea020902a0020941c0c52080c0300c450340d2040030b00301e00220140258260503040c100043c4041000344a4141003603101e401c2081151018130101c1c0441d0b501810a41d1601d4031105a003002c0722282c041000158a4100c4c001441c14050040600958001c00d441240d40c4942d61681820340c4010b000ca001e021001d0a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 739639595 1250 739638345 739638371
    0x1090e1302061306030e03040e1906081207020f040501031113090804060309141f021c050705071407030f1e050f06100807080d1b060609051605030906070e0103 70
    0x10403448203c02c0310326880c0307402c00d00702904a0754112407031103c6034002d0105014515190000903004020304a14141000c1c0810785c1c2e03009440c0b41d030458401401807003021200080e0343d4010b444102e00c2101e200c030074003009509000443e4000d00c000b41000c0200300409085040c018407050035140da10201240c1030003d600c451516038410b45c800d40020382d407070042c0c5003031100c1504024a0100890040e2441e00c0c2884c0b00200301080c0d02c200110015400150701d0b0f4009150042628004441d0000340f00d0380c901202d01078607070b40040e0000e58410020303201540c0c0001001c2000401e8070740c08407816034051074070f4503031003103001c003c2c45090708040794240c51070301190341040500401000c03003005000920300414442d01a04640e8026000c41d40700000500c40c030080801c80191084c850700d0080c4401c0d80342c0d442d05003841e02d4804080c1006103001b0001c1041e001d01d4000c94071036507640401e00c80010b42c0d550111041e00c000c035501019500004040f5190510904d4a000f181c0750515020400d0500c2d105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 739640845 1250 739639595 739639597
    0x2030c0f0612010e040c08010c0801060e1201090506011a070f08030601110f010515010504050a171f02090f012c03070f0909020f010903020102071a04090e010207020901050f01090e130206 82
    0x513a401e421004104400c018a1841c400040c22001c8000e1120240440d4050190f100600500007400280d0004c0d00181d00c80000c0040c0c0e140d43d1200034030511980d420500e80b5800c00b8010b462859107a08480400c1e0364405084694442c0c1c481d0900d054188242c0303e590242d0070182c0040d04000e0120b203102d0350307440d0402100101800e10310000849003040c1d038030b00c542c40b041190402c0c140402444100400d64464074864112040c6070048010710000000d41401c204443c071040207100401c0c030070303c181d0301c9107079014020310130041d1001201c8203011360064541030302c0311100f00350301801d0300391850b0801d0030070440c1038500d60058220303a4695203549a110060301d858000204080d600c80b00c3c5010b614004509420b505400e08009810500b140c00003910b892089c0240035418801d029a40300c0340192604a800814844000b04500c541d0010001d005c4c1d0301038407050784209410310010489103060708603481c0801c016114a0440781c50054000c0b02d5550042001402c81c082d805140d005d81c071071030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 739642095 1250 739640845 739640849
    0x909110d062102120a020402071202060705040f0b0c10022b0e060c160f1101080a0c020606010e03010e03070b01051207031502310f1202030c0f061201 66
    0x5042921030103540462000c944895020000301d45401c010110320320303020310a102100d40c054070f44035194018480d40707a20301003030900000d400601c0010300d0810700800602c212459021035084c5d0314030740c40e02c800407680c1c3d000c2c5005901240584134000c02079170411100a000f001140e20546110070700d140d810008981041d0090f071013252140f0703201c1001445e134454005a00900d5002041a03015002c0c035140d130707440001d0082c140d450300010007003079202c4c03002c070174120045c0e1042c1c0ca044031007118a8031101103014200600c0c007240049003c140341002c20f000740d106030100d40e8000c183c5907503030342e004654030381d0900540740e00355584420007201510180000c00c00303d40030b201c51000c01d500d000103102c24099148907515082c0c100b05410b10000341101c0440000c0e04840720302685440f0343d02030500a401c034504107004850300e03102c01c003010013a000c041d220450301e100c24400604e9035214412200301c1c841b003600079450340107441904594540103024820004028100fa4144085a616086030311820b07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 739643345 1250 739642095 739642121
    0xa0501030c0e0a0e06031603050a0b0c040f06031b080f0705030a0914030315011403040b1503060702011508240705092e050a050304020906060c0313140d03050f09010909 74
    0xe50402049040c07c00100050b503046030070400c13203685140c0314036440da00d0152008141e07210030300100d2034820307114050b0307006040040e0000310b0490755040302400605012804040441d15000010140760080c400030344106a000c1940d515540c580303000302c0b85644010982c0c0b181554500180300031032540398140e040902a1401142c1d6400c142d8011f40b03041c90003007000e03410400b100b209400c1d4070a02505594205900c000c07108426160740c0c080c0d503140001580c4481d05807040c40b040203006541500410810300016130544500703074403880265114401c0350500c648100d10382580e4800100d001c0e0555910039640c0c50501e081030180000507102028010280c200003043d0240d462240d85140e0310383c1500c10050400b54980154290090024000204086d224146410014241d03846001c2102d04450310102034a82d104503a8411091191090182d08110240060700030004d003000f000700c50381d03039130940c544038100444030aa020f00c40e0302140d4114108016414009246902405807070080d40311 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 739644595 1250 739643345 739643369
    0x102040f080f0708070e090a020d1a09010621020a0510050c06070503071209020118060306030b101a070519030302190201060312030b03150a1b0e0a0501030c0e0a 71
    0x1074641d00d40c0c038190214082000c2c40d00000000c10400000081d040b046480c0c1d44042c004a980b0010307000d0a02c11030190180d049a0b100150004108484031036204459854012405545659001d18201c1d002400b4082c15038400c0e0f00d40b010900d815030030318503540740300030000710020b521a000304640e45c5003440602c0c08a0008a103900e0708100500200d5440130780d503c1c0040c11840c05450007014004205d408410f41681c0e503080d0000c0d6482a0000b203018003408130800c8000e65136a000600402d41c510040d9286e11040001c56034020303801c003890b0100d4800d520141c1044000700c5586a03254080c50045406101b0140d001c02540710007120408080c0c000d4500513161314a1000c1c0134030364100d40c81d8030002c42e4584001400029001d444d131000300388040c600051600d0407040481d01c0c004a124965410f070761040c08102008966402000c0d95540c074000c48607403080501015035802d004040c00c2e81d401600f10606004070f520962008081803060728004103010707003120115611010307903048054078040e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 739645845 1250 739644595 739644599
    0x3101806090c030b15240c010e030c0d18091104080114070f021617031303200612010b0304022101060302040e0f071401032304020312190c060e0102040f 67
    0x100c5051764000649041544d6030f540d070100044181e4852601701d100000d1352800da54640380ca1300182c4100c0d0400c10020040c1e03501c070300d0a0681e02d410609180c40b0f6403141c0710710684101d11a100503c0c4004a141c1c5000f051418001e207a8050320700c40c090b004110200f0f01002070186424000d20400f284541607a48035818031110081c5203c0b8020305203070070755001d10024405491503003101021955034070703400400d08003100c4e031090451040403843c22021503602004420711040966440042511903902c182960a0000340111400783c803c8401040d08800d00411012480c0d2000b541d000c0d2000b0030081c51454410b20b0b9550fa800d034210b400609030364a80c018001c5003403906c9909102c0e00d0210041034140740103601c10b40d9030005801890500a8a8020548540d001c1e410248155010800040212035108401140038204640c20b070f129114500c4200c1680003920100d074840f05148640440310381c052603060344c002c2d81280c004c035481070381c402d00c032100031300e081c40948042c0150b0030752160b02c0342c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 739647095 1250 739645845 739645853
    0x7090501090509042001051e03160f080403050f040f06120501060e0f060d090803090d08070e010507020907090906090204090b10020c240307080106030e0c03101806090c03 75
    0x20748070340105000d00003260500c400304054102e06120210740300c0040120400e00c50040390a406510052500d0b1581090600c200d52010001b45104002081c95075000d00d102401c12906d0854049215012800300c502090200b403183c4020b101480304e2120681c40c03d581c3d185a015051141d40c004400034500448544e00c4000502965004103002d00c4d00481d001d40d040001503108a0b544515807041c84001543c031108400c0da005150f5a07034000300500c1d2240b4040c0505910b0700b01070400b071710005041d40c000850340c902980c40d4245406040e51541d04107485d5500740a8100170161952051203001d4400140b035003603602551001d1b00d40c42e03c025031110316000300300301900d0440003440d114940e124000294140c3c00901841e80d694201d501d00404c4101509005807842c01c20301c41401484000208a1502c4e08030785803d048900d143e0b402c000603030f40f00c80c7c026201c10000c51100e506401501110b801707504141c001584d0002060b1030800e40051540e00e070801c90311003a40071a0a56400c5208100b84 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 739648345 1250 739647095 739647107
    0x31005040b041e020c0f0105010303080403021c080a020a020c040e0106231509130c1d030f0a03032d0b010e010809210f120907091109040b030a080307090501 69
    0x740d10140d0b014070001c1c1c148084082c4110344071258502a039804a142d0f20310030030804c2283e014212440081165584a003801030402e04121000e17400351003441045540d000150b0100010005d15542c2c0d00960b85606020102940c80802c800085118192201203075980d00d20401c00840d03070074000020041d02c0c0c1504102c00c4c01d0749580d80118102d08000300c0c6215203a011b0b0540c1c0903040390800c3e40c0d036407052a0000740c03000c50340300d02109040d191a000c0c0d0003e6800c00c000c0d100c01441b140d0030b4003c0210140c00c01d9030360107025044203000d030041804c080009010741c04c030341a60190b80c4410010884161010920008000d00004c034035034031002007032050350304028440c024031000c1c0f13801c140503c1c100500d99a240a49520b100103481c2c0303802c0d01c441d81070406050b5400340a00c03240300b039078644804904005011003664000c0d12400303000c600140354100340c0704100004c00c030030700b015040c25400c038100001001c08040041e094000c1d80d06040010310580d000b584a551140c44480120741044001004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 739649595 1250 739648345 739648361
    0xb03270705241e070804140901170d0c0c1a030a0c0201021908190207050f0c09130204090c170d080a0c120b010311030a0605121b0909070b03100504 65
    0x945a031841c4010000503260088030308048014181481186a07000f00c01c0007403141440241c00304170046000700300052100c1c854816140b0071038409140740d89800d008c8180e400340c0e0720030f44a5940880490b03040e044c0590f460018290081c1d803041c0705203a60301c0502050081c0310b1144039640100000b0800344140d90700c42c0c01540882c610085050204648041a07944c00c1a40c1403024081e1020018cd0243d207901c0000041d1070707089005540b20f031281e2030490343d5801100d07100c2c03280340140100c0c2c800900b4401c0040c0d01c42c2c0500d4250030b280c2c43c515001c1c0401000da0035030644402c5249200030545480071281480c820001c140140700700603d0140c001c000110140203c0616808d00d0b565000c602d502400b8140c89034880a0005016111040103800425092440d41d518802c04020071100c0c56050f800582220415030781b004240c000b100d9030684a1607007070b0800d00b00d00c503610700b6082682000c0c10301030342c0300020104480400b929849110340c0c0390011100c1b08102c600340c840c14080c0d400c0500541c81 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 739650845 1250 739649595 739649629
    0xf0902071b030804170124170a030e040218040e0c0306150306040b0603010f090303021908060616140a0f0c0803031b030a0b060d06050406050a06090b03270705 70
    0x1c80e0354250b035160b00b020310481c41088510950120445ca44000a600c4155a5034100020b03c102c140f4800e01c03161505202d02c40d540c01c02e01086403900c5402408940404d000e64550303602c01c0c001e1a81d00400000f0b400c4100c08804070007201d42056855140d6120700d42181c0700c100002c0c0304c0c0e81c202c20101351520720001c0115001d0260224202c4003501d002076402d8201c0d50081d03d26113150798a202082c010a078648440a4160400c0402c1c400d044d0141d005164203000400080f00240b0001c0055508010507220540c102504104002000d141da03200d10081501c140115078590301e50500361450460940c0c0140e41c0c1300c081041c4035040000c900080c81c0201101405142145400d0a42c441c500e40319100c007080089000001404820f441e43c8004c5207a80018003054842901d1a0000300502850280311f015520b060720125441c82c000c43ea41d412143e0561740c0c458058240182101a600701a000036011001c001c0003514107043e00c1030301039400b0200700060008510305010030400381b1010841e08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 739652095 1250 739650845 739650893
    0x371506060f0509010813020d0308010f0b0403230111070c2c0703200408011406060906030a0216120203090f1c08091329091303080406060f090207 64
    0x109459402c9819258078072000d0a000041e81d4401307009031403407100308030029400100401640c1c00c02d504460f041c3d041e40c010010001c2c400d5280c462061242c82107002c06050040362511aa610500108000c0600b107942e100200d952074810501d4200c40c2c02c01c0302c0c1110003411503181807110940c2c8005d174001401e59640840f440342e0700c115078001d90703100c05840071081580f07800300b00342859941d00740b4082400b49400016501c90351110918000c0a000700b940702025111004152549055001d03940c8080c0c009042510b107031a4400c0c034030b009500c1a250001c030b2002c1000c2ca0004544014041211703000b890b000740d565151200304121080c1a040021362281c644240e0090350011020018071a0036844228143d44400c000c000a020303c29220b803890801d401c3c1854446040303000780c000450b00540d415070604c6184008100803c1000c00c4070906180d0200044500110f8070882c101500a401558005600c039201c44059580c100650011502d40350002061030800c41d01d02d103101c08000384800c000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 739653345 1250 739652095 739652117
    0x5041508010e0a18020316080f03030c0f1b010f090b1e0112021302030112170f090d060212040b190902100e030304080604051e0c010237150606 63
    0x400800c1d64043c114810042e9100500e40d84004074044051308240c006013101c202404402c081d600307183c41d5015203d101e000b92042900c4c24600001aa030240d10800e44140c00c10070728001520b070035001450f020704808284d00780101444d00c03c5c400c42141010000000c14951064100250440005024500c5030042c894000c04d07480801e00005064580c100c0d0b403244480407a0000035440044003002d02189803000000041802c00c23b0520092148a42c1540041208190032403030030340240c0c0d0740381104140c200310a41c071170301c6c0154040c01954032610b801030601c403032502c0c03521066504035001c0320644580418441107072007240192900c14505407092102168581c085103804070003040c100180940c030a23003400d2568007402614054824002110141d1030113041c21596143d07406003220010200c60a182544180840c0c1c5c451001c1040e001824100c0349000804900d9400c09000aa080000b02d000614040110000c010380b41c0101c0701d94001c0040c00485004446450740041e090003852114 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 739654595 1250 739653345 739653359
    0x3241603021e0327012c070608060a050414090c031f0c1b030f02072102100c0b0c04051906020c1011030d0b100f02060705030603010908041d0105040c0e061b0d0504150801 75
    0xb82e1003230703c11500d0420516180c1e5004a1040340c0c1c540c110300d90040c01c068407001524109035015110703000460442d101d4844090a07d0344400007180070540c458884200945001c2440d01f0000000d04185040c5e04003d403000501780c2c98601803101180015081c1e41e6400c00300c0c0c3d041101e0400b4000e60341c0107485031103880100e0000c01d01400c00c002c0c083c014404001d00740c58007c09800d4900e940101c84040140f41c040e007480025801801214405e5a0789520341da10301e00c5608803c030603140c1580060020841540c00c003c00001c030080716404004440c0e0742840b100ca418005484240031841000c102b5050b61130170410302120034681007080084031091415255800a281c641001450a09131b80c0c2c1d03100c9030080782c00341070760800103041600c1c005400201880d80c07003016040351002541180141c2d0300c85040209407480b000c680c500141441100403900e00d00750000300450444204000c0d400f0701030188a50400741e045042c81e001c168041810010000c01c0b0301c03500e410904a2a1143c01581002a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 739655845 1250 739654595 739654603
    0x1020304051e030f030c0d0f0305060d200307060f090b030408041a2106183c0c030601090f2303241603021e0327012c 52
    0x407001e42c80d45008a004005600d040c0518012528440c069070340d21806c0a8a1a590300d0225004600180301142155070141c400d21605020300001011894512515180c2c045c82461101c04c00782000d00c2c840b44110280c0d41000940018012512038014044644001038200c00340341d1b001d540754030740070820417000500000c100c9058812500d01d00811080002c10541c460042c041200c500e602000c0c8040e2421081034520342c454181100c00c961601e81349604e41107032880654218140d5900d0681012403281d03807840a851803081c000e912403000c4003c00004c0c140032410707100300c44841c4000007400440e59100d02e00c803006d080c1c20803102e0307840745c60000030036000c100c0400403800c214815110442203030341c244680621030003003081c84546c2036003036513500c0204001561900401a2403214400c0000d0082c025102000101c4210305a4000c1e048401c102541c0000c04181406e1825050740351a00e1a075180418075250020000540001c5031010480304500075021180f0204000c0448000c544009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 739657095 1250 739655845 739655869
    0x90118020321040801050c03100801020a1e050d060b0703030c020604030e0616080c07300f050304180504120914100504050409030302070204050c070c090b060d050a0e0c0102030405 79
    0x62606202e1a031202050a00f8001c6070081030703582d401e00040c44510420f5002075401440605000e1850927607070203455080740f18a030000000301c2d44c041c0c01c003007903c496034100e001c400b0380307034142203140c5189402c2d0a4112801034000c0d121841d00070541409065040c4611612852030b40000d00003810142c401808582003030006030311030800000d803407010b10b10031803038003a13804c0d8440300181d100c5502c60009078603025035014001d1403407220700601e51054401c450360119520050407402d189401c0781c5910000a8880c14107440c184402c020026410214000e46400c140c140740c00069903007071500e44509110131045240d4100444808140228071040d040d0246941c1e08072246140032440401c15100340c0500c0d0f101c0343d40035240144400501d034141c6c004101c0544220790410481ea1034030244110381c068600003038245100ca250078000d8400d241e20070b80d65004010881e504150400107075400ba60000c6800074030007034039001aa601c0350720170484000c2d00e81e42400a1401c0c60f04280224084903901 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 739658345 1250 739657095 739657123
    0x1003050a11221b02160509100e09061801020a09180f110405010225181506050903190201020c0418021807090801020412080918040b0901180203 63
    0x180c0082806656501c0c50340440c0c042c80e2240744020092803030900000e021655544141400350115051110302c0810000541c040c0301c84200c0c030305400d06062002c1600c00618000e07038000f4000700450b030405810880341c810150300c0010540ca181c091404c840d82e50300142010f955a0050045030b0b10543c100c11405c0039500110000901e048002e455100980354000c41039a4003894002801314084104004001360360f070a800700c400b41400040c0c0e030840680004a9213085d4200c0c0301c0d040c00000524a0a6a030680081d400462071b0030305c0c1d0588800c490301d1a8480404100c0000700500a0b090a02c802808645203000401040340e03103400103520b4104180070244950755804003115240120a102c6102c0ca40260200e40740015045200700148400e4a03810701280300584000740401050017244c2c241c883c00310420540c45801d03904c4119035008034542c2d65110f8924081d48180305011000300e03100704c2c0100035000442c24008419801c41d00c0100c4400c0d1703182c0740f9801d040007503140060704056140304 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 739659595 1250 739658345 739658363
    0x80109050c013f0e060609010e250207030c120c0603020d0e0303160314091908040b0324011b080c150702100501330207120b010e1003050a 61
    0x200301e00b002150b59911054480f006000301c14100f00d080e005010415550f05002008040c500000b41652081704994590380060040014000140021b000f590000e08542e06a0f2010240703502070550030319038404460059108510420910507080390002c0240180418007150700469102c0c580c03070481602640003859000502c0e42582d0710aa03000d50480308642050380c2d03e034204103903c2c0c01500d101c86c0380c040c0000d09140d00001c0c1ca5126a4a01c0e0040d0212030003803400c002d06c502c030044040e05159003500c08520074000011400c1005000f10b101c1d0003480d440640c05018000d130700c03600680c000406070400481206141000100c80000c0020a40200510f5204c0d00720100c207529101c00c0100851448024205006510760009541d000300060b0b4141804160f0702c818501340010000102c0c003155440c0214540001510300007011280302103441600c41d441e4840310841d07081d000d054400c680001c08000100804031035030032807941011000c0c05004c1d00034510f0700e44071790b0f401800c0001703002048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 739660845 1250 739659595 739659617
    0x5090d0309180906050903090105030a090c051f090b040602071e09060b04082a0105160209010b070b0a060311060d0b0418050607030e030301060e03030c030c070f080109050c01 77
    0x1c0a007400c04024158201c0c003a282ca0744001d401c4018080c0741c9400c986281c10b04000c02c00281000c001d0314008141a502c160660b81e800701c0c100068a410103041d11601d5082d1004074840c3c50f2240150700c21140404250214040400005c1605103d940700f041584400e100038401d080e40031034031104940b83d00045001071581c20b1010846515584c0c069100145449800221944810090700448244d9010340791004e000e510700d9002d45c00a5a10090502e201e03258050040d8081c40c060103064000c6801d86118440e20350120307044403001e8000150307801000c55280d00308400300c0301c0513a01c900044010310003945107541d01020b510300180218800c15001c5411000501194080c41d02060024010701451004400304107114031401c034259070134001c80b80040d010034001e001e01505000c060000314911780c6000c80842d801c5200480055140c0410040c0000e0b0364801c0000e030001407841c03400b6280c3c0c1407034403d03910464600b07584203c49617418010300074085400811218508076003170030190314141c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 739662095 1250 739660845 739660847
    0x10f03202733040609080d0315030204020c0f010c080603012304020121020403030c0314120f0a180b0f011d041203020403082101050406030c14180129070305090d03 72
    0x200004202d0007901c070007090000b0002c0d03201d0100c0c03080b07685260a546c0901210391013141035541012000f0840081d8140800050515500401c01100d0350010741c0c041144030180603007501c0c1c04e21a184001100300d001c0c4002031501703120309a00c8400e40e03042c01800450514104007a82c1000308064148800c2140c5e41111441c03400e182d00054803445000c40d912500c0749405461841003000c145c00055070b5204600c01d00d005038080b00d50701c0c51074034440b103160380c0c4405404128007070060000070810340790070780d10300c0c841d411240c000e14440c401c00300e542107454400f901e00305001059120070582d414450f08205c0c41182c5d140002d070410380103090352048800450059010b4803880d03100610f074100004038040215809039921003102c00c0c5c0c0c0c810001302e9030b80d182000150703000d40c040900001c8070300c03c00300104ac544400c88180351001034440c0c0c440402c201d00c10301e4442002d0340002c13005206249201211500310340d032240845007a495040c10061540c40041007030054110b01c2c0d028016000c0c4101c01c0c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 739663345 1250 739662095 739662169
    0xc070519030f030906021e060a09020301020903071d060301180b06010201110a11060c0a0e01121401030c03050c0907050405010e120f0c01080c04060806010f032027 72
    0x295421002c2c0c05020482454001d007240840e200b04030060082c080744d68220076001c000d5440d2140d070341d00141115200e031200c10b030007025600301c105c0e4559420440e02455403418460070008103240100850305030a003c1400d01e850f54000e082c14032030303450f103002c01190210078541e00c04040e81081c10f46003940d41e141c005030700415210340118424640820b0100b81c1702c1e0b01070748500f815100c3e40e080d03903001c1c2c40782c584400450003001c0c5604041030711042910681d500c80c2061154004100e03c0c0480c5000030445844595403081c0c000340d84541040c207050090050820468800d450165410501c0d803424890003001c1d40520301909042084401c4020301a07500d01e281200c01c0400c85064130000078080c09115507500f03101240b00d005c502d9680000e010001d80703000383c2d4126001034903494020364513a401142d0050b0800300303c000345075603144080b40ca4002e90740c03800c03a41030106042558076681c2c0e0004182141c40480a10003104d175071000030f90f00d521003444541c0c0e08102d100c10400f00d0440b0f18001a00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 739664595 1250 739663345 739663349
    0x2103020a08180a090f0f05041e03030609060b0a110d051e1c1a09040206030f070c05070b070314161103030f0d060e010503491d060c070519 61
    0xc072056140f00440c28021a502c060030741d031943c0c0030802c113540401d2041c00a41c1d40c1150007400d141800d40c0c0342c4080001d1410072916140c0b19282c0010b040b61100c801e1022a016900700d14810500070603600c04903a00940c0d40d00314140c0303520080c403280036055002001489000a03900c916080d011041103c0c03c00001501c02510348d2004803220500344003158130090440c1410f28020100011480b0490b090041100380915006800c6501d159600710b6155900440640301204224000400e40f01281c01803200001801902c4c2c480303655a000c6e4140182500b00e000b92100407071004100078012100d60703282c2d100005500c101d0581080182800103400c6001c3c44680c074202c89000a0302c00c44100780d5a0000c403d80b01c0f85412200140d0b00c07142415038a188041800081c0c3c2c215040070b81c4c1448483c420401010304119290401058940c01c42404c142904010004540108401d20b00036130031300030680301e440c1c0988032a4105101000300c16501c44103482014000c1c09602092500c413592a034031240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 739665845 1250 739664595 739664599
    0xe13060c170a14101406130f0303020f060a0c0203090f010219151103270307120f030f0b010c1e051915090c050609041d072103020a0818 60
    0x5550301d403000825000c0d043d02c0d82c4075102c26901500140888898040380000d460528200e0f2540700025000d200a40d03100740c1000071107a000304400038002d0300c5c140c078510107184a175001e1b10280440300b110342e14050000e8091150b59007480140081385030300105580591204803201c0700c6a40b82d080050b410900301103800e000c14000c01c888074081c00a80d000307101c501d510758082000100c40d000114451030000707a401500300e0a0242e0241d1040340e440e424503441030744400960b840c2c151969100040c511800c41040042103944c2000d200e070b80e806110b021403c404905c414841400c9400c0000c101014600004240301e44c0801c076810341441c840e0b060f00c4802c0d44102200c0c020f80d103000b42c603d001203540f40d048544145900300c580e405100c6000344101c5640c0b092040345d441e03042808200181c0c0000030f5264009070344404040b0004d0713600b10340040c0101c0d100040c0c09903a00b4004448240c40b00c00030441e441c1b42e18900707000c0009500003003a000c036540001641d525030119545000c14059203a2040e5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 739667095 1250 739665845 739665887
    0xc0a11030a02030705100c0503060d05010605040207150b1f050f040308161709061e13061e0201140601030203041b0f21033501080a0c0e13060c 63
    0x20707980a80000c014400b2900070070440303c0c80750712464604c2c15161140c0720b2a00055003030000c6401810a9643e0340c0304188513200215416031118081000c0b6003044109503107120704240058541d0120780701c0d507083c40000342e8601141c429402c900c800c0d01a00a440102009400101401c62044a1041e280910f900c551000e1b601c0008100d04102d406040d507090700d0b02101400038458114200c41103845900c03000d018241811202800c58200805050710256180390410011500d000b002c5000380c05844551100d203a02412010b12140c02503442070300500703580c03411900b00551042641a264896024600582d4a0b03541c1d14044900032418580c0744d1001021503400704040b58203400c01003d54040e400604007004c211091072001030302d03075280600495544030407250300d000090390f4804542000c04401c0c84403118203c442c00211800d1b030006400744c009920f00c1c010001c810060000038510102490001d0804010704010b40240c41c000801003a900c060060410380500c039600d051601c0703c50b0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 739668345 1250 739667095 739667107
    0x8070c0525050a0305070608070c0f0b090d031107020d030c050604030e030d091409060f1207030203010e0303070f2d052a0a031d030a050d0305130b0c0a1103 69
    0xd0540c828040818159400341440040382c40d062882d086001c491700440281621740c6441ca0075103240401500344810032100488a00109800744024444a4031452070200c1c10324024140e5070501c1d01c550420342c00c0604111f003500b20000f440042e10003e40d012240c2910300c0e465803806503070410568070700400314005c070002c001c00c4c503400030048031903500140c0542d8480007002c0412109080c982c020f032612001da041c1c05508a0400307842e596071103580504424200060a13000440c001e002c602c40380c03082d50100b0028811820203000d10220307003441c2c5000358114106040050904a10b01d541401003290841c00128107007038240e00e016600e01050480504480006001019a80014040350031000300040160200400401e41842c4501800107440ac68203941d4040f60028051a5221a410002c941600e580d81e02400010542c81c460f00082c4911480f000d005400d0750b1000306440300c0c3c0c1500c1d82c8007a010504815200c0d6100300b49079150b5031b07100195841075410682c4480d0410081c4008100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 739669595 1250 739668345 739668373
    0xa050a030905030c2b061b020c0603060901030b1f0905090f120a0507030e0310020901081f060509042d0608030903100b0a09180209070f0e0108070c05 66
    0x240880034066074405200300d4559081c155503002140070701d81c00c1400d08a90416a030480c40e00b038502001310f1081c0c803806400a071a0302058448800d001090b07040040e802110468042100c003030325030030590b1914158a00240007038160b982c14840a0480050000040c66002d181d0104040c7e8003060001078280d66107401e4041c0080200700c422840c5031007480401800703040700140f6510303100b0b0f076111040e02d0402c5404c41100c4a400ca030314110140f203041d0400c0c3c0520b580030b005580c24409020001a1156006400103100c1800503104103485940c92082c90703985d00c0a24041c1080d2050b0782030943d550050800450000c0c003030740101c00e45c0807804864100c50b41c00c035042600b011340740f1105c05207c440d40750343c0a6a00c0b80704410009a0541c4100f03050023010201750083c10601e04010040c4980d60360b1035400d48251a41928104414804044074004600d0b0001405400200c1c07031510701c100501c01c49029050921201c4c0f074905008540000a41045c03003010019080c551000695100f0b084d6007203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 739670845 1250 739669595 739669603
    0x100306020f07060c0302070f110a170f0c0a031a070c0f0c080105150901030f080c0708010903021605090a1104050d050f0717070b030907092406030203100b030a020c0a05 74
    0x2d01107901c182003040300350741e06100b4000c0e030381140e400c406c0706c071000c9465275101580c0403041d8001d075030481c1c1507000c00200c41d54119104c051000c0c0e508090070801400b0803034607040600c440303c0580324403d41135003400415040f80c46082e24044170030070000d640d114103000351820310404000400700f4091030000b80800c0400ca80d100e0850f5050b10083c8103a480f10392412820085941c4000d40141901004202040741603480f40600c0c0e001c1c1790070364a0024401d903074070b007841c6c5244c20007040d42e9150070305a81010382c10030036100040702444020036203d040c00300048403203101604c0c0184c0141c0303074006403070700c0d210032000c64009085c028808004c9030002c1c03030b0a94a600e0100007000c1c06000f00c05000a4082c480340c0381401404044018002040c03c004084040d41c1000e032140242c0e1003410004940b0949500c51103a402c0090101d84c000154042526641004183c115808040c010700074483c84040b14400c01d42502c1c1540a0b0688030b03039641c550075000740a0a86890038510a881200d824020042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 739672095 1250 739670845 739670857
    0x16030f090e06181e040506010e130c050f2101060509010801020906091c0609080702101812031407030513060305010311010c03021e07060201060509060612100306020f 73
    0x91100d08005035909050040e9500496400e0b8000c00f04003080220001d2403030400358484003c4ca168000038007a10000c0000803800c40302160103612102c01031040c02c204031072080c0e00c0505940b4010344114550303249020a0342c1d61003445d0082d0000706410809a8034034001c000104940e00d01e65081c00c4040d101c01e40a84264824203014850620000ca4824018000c40d20780300006800b8618002c4400c00388501202245803951813030300c840b0101d000050890050399a036a01075a81c02d5102d11060040000c542d21205042c400e02840982c1c000341064201c1c1c54074202ca808201c0085120f4071401c0586440c0341000b400c0480d06000110441059044400b4040d9802d0103000314030629107c001c1503040300c1003800b01520310442030700884003a610500078401d0041c0b0a105940031912105c0c09400d042401c07200400705608000c0741884410750920481e030040c00111516281400c0031004110148694601055040080800151450200400b00009682c8a80215911140b6030309112003a0049 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 739673345 1250 739672095 739672097
    0x1812021c0e040e010e07140a080604080304170c0a170c01020d05041106030106080402060f0903010c030e060a11030109090c1203020706120209010512040507090e03040302103216030f 80
    0x3002c3c2d0b030024034405128483da504241030041144e5030078491300040310340340a10043e034410b85804010681e02002d1040c0c60281d0720441d211070302c80c1071900d00819941c001c070307042e4070400105001c1492482c3c1300080c16000d59800c00f100c03952140b85000c18450511800321610a551300008606e19200266888280b0441c020748123265044080410088644003c0c4110f500040e400b4000c00d000d0301e000d0004001c14012030b0705452410300132901090035900c031520804040f80e0b403140d40c042415014800039601c001c003404100601050044c50020a01040c010014110780e01e4450740204100589490054005204100104561450300130340c1c0b0000ca018610000700e40d0640c0010320030b1f050007650240a0140c440e10b00f0000401003450007110b0040c400e58180c0720320a40041c1d400480d00c980d408031025003014658403403c40c018003a0074496000010b041180361140703960680f03030100f1407100030500304141e491041c1d403250040100303004035039108074192440010380e800c00d90004500c40880c0340d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 739674595 1250 739673345 739673351
    0xb040905160801110f09060405330c0703060f060801110307031b0906030b0307030b2a0301050906090702150709150f090b07051e0c0111011812021c0e04 67
    0x328000c0e98207a6132048078040400f90103000c219a4500c1c01c1018000a90010b054141455170b43c5002501d1080d15034078240310442e10004615200701c0f00751748040b580d114082040e02e4916012622a0355401501c8050603069031201d035250444503542000e00208440c8000380071007200790f070144007140c0c003d54101d00841d20300003000071681c843c891480f0050304a40c6440c603505185c00c10507805000c0b05810140d05000302103010000a00c00c210f00f030300030040c40444420041204045003038030071840d04500c404280c140f00400c607613070703490f81c1c0341e580088145d03051402502c8a0000764500b1040840c403191a080031020000041d9100fa65602240c400c2071881990070140c0c20107440c0da081d11170a000004010710001d101761980302d401004000d11030001c50703038000c0c0000221035500b130f04080101440c0d0002145403000c4e40e0b12a050001e0400600300070001d40c2c041500e03007203944c0300a1b00003c00d03902c10301b652800c0c014005c0c84081c0e609005405039101c0d40140d0348004080c1c152201045211b545 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 739675845 1250 739674595 739674599
    0x11040905061905010e010e030102130b04081006050603040f02032103060f01080702060a020a051215040e1501120201120c0f1d010c08030c0708040602070302031009120c05010b04090516 81
    0x201c10034914100c0743c06031103200035950040011141031118040b50b5030190f40070401c0d0281c0c410304002540c002d210101d502a03c03103051100c0d450400401244201d920780c10300c42c040c849990349504580d002a0f0098002004c940544003003420130024400041d071401c000300107400c0c44c040340e10056114040868900070402c0c09034005407071058040d2403103001a0700440008840d12025801007000000c40d0a08500f4107880150340c0850440490b4960007108514903000c255003000d00481e030139800300c5009400003480e030175102c85c0203140511039002441c03001c3d1141402d590052031360141b0310140e00340c184132904d401d000243c0718030b070b40446110005212148140c000400002d000c4c0550303105039a500e80c6041281c8a100942d080a48205941001040380f24001803041c1c00030802402e954010300001d03441d45c010141484141c0b659202e05505110459001582541d04003c2007642e50071300900c08211400c2490041210451454200d40383c0414403003032140020301c2c0c400c0580707580c000c9050b4035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 739677095 1250 739675845 739675879
    0x105010806090c030708070504360e0a15020f030420030c0d02040504021f080103050709091e030c0c08030c0f011b1d0d081b0a08030105131104090506 66
    0x31402c9424250b440c3c01031000c55009440b074a0f8850b000100d074a05282495142c0c160070208206a05441030715820b0310600c010799010035590503d403c044d6140411a40f0542a0820b0f1910102d1000a10054240103032582c11682981924008070030000e05949900d0180b60160a0110603c0d00001028040b40c44a1040c5800a1480f42141000e4200044010b5030f60900002d0711025001301e03444921403003460740715281c0c210380c580301e10b0459035503000b107514605100c0d0401800f90030031a180d900b410a2038011410111880350071030744102f00000016a2401d003241ca48802d030000034280030341e4200000754200004090300461100d02c080d160700391406c140c0d4078200e0308034068940c2030220030944082c03114051546440e92804511000700a1856103002940bc01e400c1101125102c8005c41e0545c5400c40f4207043e40d90048a0000401d400101900d51101900051040030f1003248000e045241304032194100340c4580040d01501038551b5190350400340500303000c0b90000d000740c0303415034079090311 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 739678345 1250 739677095 739677109
    0x302010f050702030d090501270317011d0a15090b01030e03030f010302120a06050907140d030206011a071e12051303060c0309050d030b030c010201020a1202070c0305150105010806 79
    0x20b101d140c005614020440b52034001510f130b040e00941e11550381d089040b804a40d00c0203941d106c6105c0c2c80c00342c503d0040070324000e00314001e0b4000005006000400600021041c041100340e814070303c0c4615a402d0b5600c00c0c0d0107006e061a4802d0702107010ba0344c5000151443d46030840c00b90302d40d090320140481d400c0c6010b007951760700084031090002100e003401040582480070768418400b0031901651504d01080e00c40c0c1080d500203072101a0540e004143c2000101140708000c0d2518008403148080303000141c5000b50348200600a2140d07802610340190a80300e0b90904580383c2e95400002c1c140b210610407007000c0d2881c0700c2c1c4070541d074140710b080010b4040c601c55000c44540d9900300c0c110502482c2582c41d0b000040038040007000c00c1c103607a1503184001c10409c10041240846603034000c51600d29440074142001034a2a005055a00500c142d0300696009086100301040c0300400589804450605103009441540040c006000b00c018107661690b030003900d1070596a003030b2100403094440d00d080c4124 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 739679595 1250 739678345 739678351
    0x803040807020d050f2a1c02060406181706070f020f100e0c041b0806270a0b09060f01081003060c050c12270109090c0e030c120a02210d0801030302010f05 68
    0x401b64028112003950328114a20491b2810320310030503103601401d44d011031303ca5030058001e94045540780c031500c0c81c20858000342c0300c0517041200c141d000e5840443d0189984d610094800c2081c8070015a004403260301c200014400c04108004960a15a0040348000200380c8895103001600a03038070f295000c6d051078090310100c0c03640c0c0b0440d08504850040201c0711040040e2540d0b51100c2d400081c2491111102200c02d8144000c000c90381850030140d005000300d80e01a1011070248000c9010440c15503034520380c40300340040030b0078110b07041d507504240d07071144512a400090100f80362506000b042640500a00041100902111030358488601c2804450150b54601248000d01c40558034058000350f038100c075031640604220b01c12580368070710740042e266011000700000e10148080307603803858204413407002118203552000c407e6903d040c87c1c03031700c2c2d40d00d54801170f02130301a03c5004480710b112414500c0f120341c0e00b002600d0b044088074400408120342072009800540c24070b8806001143d4038860180 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 739680845 1250 739679595 739679653
    0x1c020102100c050a141606060504240b0702010903080a030b090f04020307140310090b370225060c0e030d080f0a0209040906061d040804030803040807020d050f 70
    0x8140344d052541100c0e105110710a0040112060214010001d82d000309448054800c07030300031030074600300400d00c01103612180810701421742107103445a1051503152480d007a5403107041699503074221030005881c0e80303590f60700062080f6000100380105a40c15031201344406411961828251203030002a000a0703401d4030003a60540000300b0070000500916541e42c422071018041d6150800c0c40401242210804e010548480305154100a045640d5000190300b400b10f001a031403034a060444118841020300381c4814282d07a00145840c1c50150000a10844007a00c610901c1044414a4010040c02c0c44102c017401241d02c00b601c0c0c00841c80c000c281035540c8080c03503650360341c65038603448009034105000d04120b070b03007a90801565200d0b844900a8424082c040c2102062062810341f442012141d1400f44552131900907080c8000915450101e03011650429615903c9403114244000705100f4040003d502115a02448042240104001042d00e00007415030b80001300d1004686016000500d05503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 739682095 1250 739680845 739680847
    0x6020601081f060803030405060a11040609090207050a140d030f0506030a030810080114061005091e060d02040602010f14100513020705032a070302090a020702030c1c020102100c05 79
    0x2609040c10000002c09160180700c001c2512981c40d610181190b10540c1c0a8074150440010010340405900600d4600700b4403800c080c0c905840d10700c0042101145000c1d62440d0780e00002c0c0b10051100030041c0344511904441e102380c2031402040c0f030030358403010040110082400c00c00a683e1100341c1d440f0342d52207500c016000d00303201702096030304640c0b80800a00d00050403d2042c070202c0c04080910610008456103c00121781c0c1c1440f01c00c001420883c00140001c101d82007100c80c0941c0c4616680d6a507082e24851841c0a0b0f0041d0030000e0300f20f014005a20701d4036440400c00041070703981500b145014044030b04c0d0030010038881b00e10782d5540c2074003156800c0901100380003c010a080c610700c0c209a545134403a0060a107038055440d1410f6038009c0425001c295640020070000c205180c0c0841e00a5040b44000c0900a1455011a000f0103008101180069003c20b810003551818480d0b40032090004044110405940f40c01c0144d0320001401680144130300f1441c0001c944d110301c19901c0d0700c1e4450b1102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 739683345 1250 739682095 739682113
    0xb071b0b040507030b070210110c2104091b1b02152503030c0906030615050a0e0a03030201021e070f0b0c04081b18061f021908070c0602060108 63
    0x2034006000060011141071180714000400300c0e10f540f140c00e00070745041e8060071140c1e04000706082034a0166a02c1c0d03030040302c07c2000c003403044400104088207060010854602200c8055540414021035001c84076050030103550001c842e008103041610080c50b921020490940070700700302194803421900070f4200d5075504195005214030710240005491100790030501000302200c0b4802c010180a0840109803a1754480701070b00c1d00402e905015041ea40b82c01c104140c81c00320001e40003a01075903882c0c01c0c8140043e03c49070640c480d038460042260050600c5940541e00c0c980207000390721000318400e0b07180d510240010142c0a000485000b1074001180d01c0c102d010a07140d02c000e0510243ca4090b041604202c0046c1c1408203022400d18080a00b42560781900480103114813006003141c0c0341032820342c5e1020090706541c0c048001c6603e54940c0303c41032529a6400ac00d84c902071812182600344018025050201300c400002020a01e2142d801c1c4c80c442540ca5070182e0750b9070801e0080d0340140c1c000c6106 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 739684595 1250 739683345 739683353
    0xa05060d02090a06050402042903190504030e1801060f11060f13050604061407080720160b030105100206010303020615061303080a02060f1003151113030b071b 70
    0x1140c00c100c04103030000302c540c2d0b28800107007240d01c00d0f40070303038004034038170a0781d0f40b070a49c048441c84044611a0000ba20314980304210700c100b00c0414021780d4403950794801290906210324140c1c0024440a0000301c2c943c04e056401c074100c18400d00c04e0360b0000d10024100010540f06000030030b0030301c40c03080080441c1d4681e0042602c104800a00d0a032011580c0740c45100460310401c1114080c5020703940c001424040362080c1800444010410010b104c15002881003d0794002d039140c400d8001031251126481c00380c603525041001c0b803110030341035500d44c04002c5100f10503a001035048900c115056076180d098080c0c180e03240d50b400d105c06009600201e00050040010b1840010124002801c45240407020313040801840790702d8200f5900c508000c2281c400071601002099041610150741c04001e01c0c0c03d403804015410180402426140d103c0c0e11001004000e41060040f1f482400c0e609459a6110080c041c44226910098685030340a002090099000d141031881c0303804445114810b88001da19 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 739685845 1250 739684595 739684609
    0x150901050f030a09120c031202030c0d021c3314130204030501020703051c09051b1215040c0b030c0403030c0201020319030e16080a0f021f050a080a05060d02 69
    0x110110009031510013844c002940b132030003c1c0c00780d03060752200b02000c00703603080c018840040700d10844402841001030190710a9440156403c1c7c0701d0560003d41e8a122034441d1312000b11151014900190504010a42d400c54403154a0080c030203e41034007000c803a9401c1c0e144aa850144079101503181d160b104000c45c1d042000e580720503050410005494141c1d241d8505089a12803d01a4009000802e200619234605819081442d902243c20310082e00b80d500c8031034492140000042110b441d4081d0546203494500d02180c0000008085d41c482c05141c0400d01b40c0c0c8001103404444041c041400071807440002401c1e240104400c4421070308050840d0307003c0d640c40e08030302c9040c1d0640c40b050068a000c40c4880c0115007640c480c40e40c01040c1002c03610341300b038504581c1042c544a10030b40b443d0b0920844c0d200190304500990480301c0c8822110700c0d8000301303128001103010754200c0c50310b0403000054160498000c18030507041d96916a210303560a03030300100b21041958050350010000e01c011016281081c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 739687095 1250 739685845 739685851
    0x30504050307080d0605010e011d01030b0f040501080d0e0a061d06040e131401020c10020904181103190f03080406110a0201090c1d010b07060609020304030e150901050f03 75
    0xc42201d14000c100e03100c07008141c010640d000030703040d10b0f400148120f590000045410010a00740340f1207520040250b10010104c4140103410942e440e0022100b03603640b4011484a400043c0c03041100317507118090b040d224600b40781081d0104070100c0c0310f42c00c2424400c141400310f9426a59002c1c0140a0700610201c41003482c409031380c840003d00002c04c0c40c00c02818410301030307810310a03900001001490a10038000b13185d000403101e640305001c03003030041a0203c0d19004071000007030010b0b9184c0c0030f040085c0003130410081d2568004900d020301403c02184048a64185804400711412110340c0303200c14a04100204004182039070a0112000181c0103a510a400c02d22908000c580100e056450a1494000010a4005030344941001003400a151f030690060030441d54859000c52002c8444d20600006100f00300d91580e00140179400e10000d40d00c40c10240021407010342d90703420a0b0800400d008031101d078040c07103002203124400041841034100c1e1405101a19003c2c248500b0041c1040e150b0001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 739688345 1250 739687095 739687103
    0xf0e040b07030b040e0a02030708010213090534080105031c08090703021002070f140616050f010501030c05040e0f100e150c19091805131b0501170c0406030504 70
    0xe00c000c0841944c03a070040044201007240100410f050600400d0314050300d550004649901c100a40c410400700400380400f512544500030505403a17000707803508142c4040d41c2508c00c40c820000d050060b40454000c2d248541455511300110366214070400d9150a80031202d681c42c04545070501c00c80a01444100364417038110025510129035940128071030881c400c082c2001600f0050f014040301c8402c14044025040112140c44ca000a040102d02203100c0c144030b040c0c0c030a101c1103890b400c20104008400c08221004000d20503540e5a00c0c005010914074044c691107a404e0035401070f800480041d158009148980003070a0b4010701c80380c1e030070003400c2c2c51500145501445404540814480c4591030040b8030070300d1030070b6030307001212031450805036a104400c0410a00b49420090301c003880503140d6002c040c901000810340c40d100003100c40c000d1040e100400140403040001440039481c02c02c8000c0729070a88035200116040c181a029001c4104c032840c4c1d044409000c00e00c1003511a90100e544644a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 739689595 1250 739688345 739688351
    0x110a0201030c11120301090c1106010b0313061a010f031e0b040207061103040501150e1b0409151a0405060708210a02070c0509071d012f06010f0e040b0703 68
    0x103241189420000d00000c01101d108000004200d510024803852032340030102c1c9412190014004055911440c061250b42e0501d103003c000310707200100080c05010f07800d03808807042110843d0711400412071140005501d0219510001e52340c0a036001c1e01500848101800e802445521030f046514001c1a50280454116500384070450003e210340c030907d140c0e0001d4411544c0c0702c1c6081c1c58184d003503c0c5400d000c03045520f4400c5042241410203401c80303801415004608844007000c500203845409203501004920342071020244c1d04481004060040e034145072400c1418407000c40c000340c4944154490181c0041d000c10030381c070200d80e009015000392980501d0400c92146038409010703d8030403c1d00c44580b02680000d5140c100500c1c50517040007402c0a1b508a113103031a260f80098610b805030280da4821100610004000e80e201d9040c68503441074620b644544445400a018003c0000f00e16104e640d2041c0310010840f070340350009801c00c60703084544130022540c0343d6584400500000e4069400d00d52 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 739690845 1250 739689595 739689617
    0x20031f12051009051c0c1514040b0a150311030607090f1a07050a0c090c02070b090607020a15030c0e0d020a0324050a05041217010920030903040510110a0201030c 71
    0x418a44003080084603555100d046c2c6c640743c208109141800c0d100b0050441c94104980c00a401c18000c4650082c2c00c0710417240380d5540c04942401801001019440701da000700f8010041000300806c01024a60aa04a41050ba80c001054030048514040c503413111392454002c01880e01500303800000725485040c0d642c1003c51581c0c8007450442c44141c12102408200820b0080e004540b0840382c103028207100402c811131401d40c8594051190310300d203a002c0c0c1c0d0009140010354540e6150903004080b200129590031102810050042540c000c419001500708001551a49410104503a1a580040040d80183d00e1a9078158650120a52803c182c00c0203401c03082e42c05207580b040703921070218403c01040a24281ca0015180380381019410240b150410010b030340640d00340300701415222100400502e140340d1182996002340381d038201c680e14030300c0042000f41124010025008491042d1014015038000d90350599070000346541032000ca9012002e00000b5611a800c80440300c041e40c105443d80d14 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 739692095 1250 739690845 739690873
    0x140a080d1e050414010825030515010e0a0b071401020703020c360603010905030c0a0606121716080a0306060e040b0f0420031f1205100905 61
    0x129035100500085045240c1d07150001c01100221801001d2515040c0d02c3d003030400204a042c864808201810450804002986403206450384038112100c1c40d4038510001c40f503c030040241008642160002c0d043c0030314507070a94003e41e10200d90340002000c8801950402050707140a81000380261454035052183d820713600001e1004116080c0a80e010703220601040c402d0180c81008900b1440c7d02183c480d5843c0c910900320f00340c01004d070200c00d5401040d0740b100f20000380901000360018002d170000083e9192555000a50032500620610050000681c1c0d050703000350155400001a20382801410503d000189950043c407603d071300070001410000c40342d21041845e41191081101180d130750401440801c0c0c004110401149046400f4405550303690f0120340c00a404600c09400b0741c1c0c071807100e604e80000107695107103101003250540f5242e140c00380d0550071404a042c840d113048200c09a01141c6142316220444029421200401084156101070360080400302001e44081c0148141c00e0086 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 739693345 1250 739692095 739692103
    0x8071802070203160b12220f0311030a03020c060c040b3702010c020618030906180d0b1b072111120d060b09031f060902070804060f0e0a140a08 63
    0x2d411440c298940350704001410001c1586e010385250180090300e00c64080c1800740c803202071a0284c1c803507688070600406280039078040b07502c1a08078440b40004154003400550607800b030300c110200402200c006866400d8003010a1280b4010f00075171a10400500c440220211081c60500c2117140905d0200484061401c201c0e008030024000180d44490042c1f1849504102c05a08801c11110360b004600f85020180da9130300ca448401805900301181000940340e9001c2107007111180a03007000100a4246406148108100c0388900442c2c24000c620110801030800d603040c840d403014412203928050b00110003003e0410145408200880c0c04501d80054144600041d603074541490603220100030013030200f950090703013001c550b0316828450f000e0150340004d500c40c4c0c0e0200500c1e0316034981c21559640c0c0083e10160b0084150f8070300001e00307030080044002c01030040b41d19035518030141c2002c0540841c4c0552905011a40c0150100818004d1905998004c40b02480080c0300020381030740c0b000c0243c14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 739694595 1250 739693345 739693349
    0x50c071a07172a0306090906062d1921080301031410090303061a0c030304120908070b030106030f15030605130b04050703050c0d030801090510090e0a020a0807180207020316 76
    0x8503400200070b111141c06d086a416400001050252080d8030f44440070604009051442c0554420f00101c000c03070700114060030f4041c0d510081c0c03007814400d071025513401d854012480340610220001e040042d607802d401d007802e11010b0344013002c1d40c80d507441c54856100303650308000e01c064036000c2c10780c4035000d01c03425110303000302c00d4404d45011600514041c00c504110702d0300004802d0102d01004a0840c04101004503548144c1c0056180200424154110703200b68844e0091a000c1c1f040034400b2891222082c0510304841481c0d90a00084881402c0c40c410b0703176045a03400d018003a00040500029015812030342c0e109181d8203101c3d28143c51629098403c0000380ca0550740d5402076030782030080c4001030241000801040d108000d80002541c0d00a102c00d40510460070b000396174502041300c00c0d140b01302c40c00040c0b04088081c00b00301c09171040c45441c0d0002e000e00300d00c42c04c4e0380000054903d8010030000e0071200c1c00d4005054042c0d5200f0b84e80065403201104a070b141c01074680901c0d41850030040440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 739695845 1250 739694595 739694671
    0x60e0103020d0b1309020901050f01020c040e010e0304060c0c06090810050a27170f12040c0e0108030c07050103060f06050f090907080415290a09050c071a0717 70
    0x1481c0c212401402028030301a04003500070b050540d02030ac45640c000440c070944080c02c0e60001001c18118850b03e0041c00506020140307800002400540190f022203500748090140248a120aa1700c4006980083c0d441c03240c6500e9401403002001105071590115501c41c800e6540810003031802075040b036140040f6010181808090101c00c020700c40014188140021640d034110b151001d40300c03000c202030050750001c0c4035100c0b94400140070070402403c0c0900829a00710040d0865860365030701078482c1c0080c00503805601c202603002035550300c00c1c001d80e02100c8180d09030b90740844c1402801c6903140d00401850309040c03020462a4003035103800035582c0c81030700707039907110300c62800d081c501040d14441c002c1a00084d1814908019518038002e454488400191884402c2400c490404115603401590168410307510700400c001018400d28024070381e0354803a004000102c900c15070814407500044d1074000001c0d0048090a011100080015400031001034040700030391038041c0700011890890302d02407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 739697095 1250 739695845 739695851
    0x106030b0a0e1f0903020f07050a0e040f080a110c180718050303211b121f14031006030b0105040203040206070516090b0f03060a050a090b0c0304120504060e0103020d0b13 75
    0x4d060550521043c00901d07131200103403110501c0c090009540544034000c017840b01c180400850100410182c0122105a000200c907460f0100d66030050140c00c000c6d02c07604030b50f015040c3c02d07803078030716040c05500c0070045191b0a00d04140c49101085030503100b50784100101e0901d03080d0100380c580c0c08002819641802d220280c0801c401602691030b00350000c0c01c807022000c2d10514108000380341d1003e840c028a100c04200c03d082d0784151001c40003003182141e82610030788101010030642c46018186107910000d0b07045401080b211040c0c81d04075a0b01d88005040d07580040010b10070780c54641c0056800c640000c00b45410704000d91111410115042c090190004e4194400c10141d0304500a88842c0201280c000403103000c10400b080e21510b0083c03100088a54400000f1800f80f40d0380c0c0150420b17500203000085914100c8180d46440d4015502070700c10442c011808070405d4440c004a5050352415503d50050560090040d00030790090124820b23800e840e814401da032a2100c580c85541046161804 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 739698345 1250 739697095 739697111
    0xe100e0f030d091a01060e0d03030b180103030e010f020604020f0303071a092824110301030203060606040323070905090d1d220603080f0a110106030b0a0e1f 69
    0xe0700c4e80180c080c8200d4110901900410107280c12000351000309006881c00c4008065907c0c1c11401001c80b4046035603c10742c24826001c0c200040150035051b40e120f500d030500740c0c127803000041d00c40c81074408800340140d02c1f1f80e00240050034000d000041a00014084a04004070b0703070385035100302ea5507916400c5011406001c000011400304544500031000d1203041e241d2040d1010741040a2054a40180160030f0020450711030303609440386441880740818007002895071071418019140d1080c801a4420301c612408543e41d458540111012603900c030a03c2042120544101d00c00342c5103c804031415409034510010f00c140b07941c0a40c0e48905100c0b4081d0610641c8602c000e0300e61028027040e10051110040d1401040c0c9503000f00180c110490801202110344205008014049680008007500000b0914000c000c1034980900710020150f100c4104012550040a088400a00c0041c0060300d00002150400720264040d020004c44041034a800c40c00a00c0e5604241c0851b4003e454010340d14448 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 739699595 1250 739698345 739698353
    0x4090e03132c07120204180f0e07050114120a0903080a050919110312070201200307020409150c0e12010e030703050f0c1f050106030e100e0f030d09 65
    0x44407000e4044440080c00d5000c10000d10040c00c038401024460740c440d00d00c040b034040c41c06110400704212040c2415543e0b1500c031059064141d1001c0c0400c04102d04001c04c0071002d00044c06403c03203601d10780b4000c21b0a18a04001142c0d0011680503000c21000100807210b0403404041d24180314101d1140c0124042d2600c0c0780c000c241d2003000b4101000765151a06010b8280d03004159055000040c181c060750070003240c200311050105a004441d454810012003a5295568038050b201860017600c0300014914000c418052204080c00b40c00e103150410040742c0300500d450f91090604a000342c515030742015136081004104c2d0741019104c0081841d240103840742d480c0416903401c65680e803500a100250300908030035601e00030300340000c0c02c0c060081040d02c5840d00c0f03101921000018802141d0b05030b0000041109801305d5850000e00950a24001040b03480c000d02812200e41c09010007054200b00e03400d4024020413084001039070314010441e81130308101040001d821500001500002c0448903450 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 739700845 1250 739699595 739699627
    0x30040201080105030c30070905090c0d03050d0903030f02160b15150705031c270209060f030c0a0b090a06020a0b0109020a0e0604080109030e06040f091104090e03 71
    0x44014413940c010426920700ea05d500d96001610003514250080c40030042e144111401c0c10b21b07a940101d407141c000006409100c54010301c0c052442042910328208044048c007105014040c00038000c04d004104c0709442032003d60109003814000d1030300003242a409080003050381d2060708128059084106a00e0a0062801d40369412288451081403261101004515401000c0241c6800c0010100300b681c207000e000d00817900c07411002c3c20034940084030344689100400300c007440200b080488031082081171414040500700b4603002091400166034904c03c000a101c0030034400c4d40c160013000300381d940940300c0c0c58100e000780c00500482038542c4030340d100340054a4032a0740402c0c111340c01002e035540440c0f02030254506480721840056510a1122403d80304a03589022483d002400081d001981480650080075080c0c0b090741c803090b160f00300c001088440d00560045502e00300d00c4c1071080042410039800782d00d418400c002c25034102650741003607004550f100b031001d142942001800c104000f811070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 739702095 1250 739700845 739700849
    0x504050705010809100b04020904020a090312050f1c0e160e0c07020a05280e0910050f010506070f06061e09090f030509010c15061d01150302300402010801 68
    0x860b007030600d80351151513107545503501802a00c01c3c6903104070343e07089619560111a00b07044003400c19991900a800012702e41c00841c031003615080c410700c1801300f80e1407040c01181c034003146150085003003509040b5583d5405000124485180d9511240c0d02c00c895024402d04810f01c83c10641c0050740391a101c1c0b400c508210007061a600d2a204001030001aa12940500c0944e601966082c10315a04150089002c510441848002d1a60714400080b1100c0f01e913030040c414111142510070052000341048140c0c1c80c1918600c0d1607a100c20014425420007030b0241140d64021115403400c2207054491408403407a42e00310440c19802c514521b1110122002100b00500a403202000049600d41300d400c221501128002c040000000381e810b516031040241d440d1403500a59404003e500425051006003940d12428051100333414180b0350410411590504984255100c50414524104110000c0d8015845503001d2402040c2202e003031100004100201c6a0518117180c60303007020f00024010500503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 739703345 1250 739702095 739702097
    0xd090302060610322106041103090606120106090614040c020d0e132c010506040e070509220507091514040b030f0d02070905070f0f110703020a0801050405070501 71
    0x409821a050710a01c034080c10807000b2131000d5a9200444040d050355102d21107407084001c159844134a070408032010518001d200488041050101c20601503015001c2102c0e0740d911500117800048039803d0094a02e015030142c0c800021b081d070b8030348100d24200e803001d401032405480c00c981501140e0a0511500006480c5030005105d18900810004d05604d10b070740c4101c0c080c104410884e02e83c0981d5170000c242c001c00880c440c4080d48210255407a6515003894502031075800d102c0810800c2c10b0038841c40b0b560080080140880a00b040b0601151a030701400803d9649801c4c40c0e07440b20004850b410f140b0540c464005000c456241503003200695020990304040300c0e10044c4100002c500311590050702c05410f41d400b00d40c503c007000009050071815000c800d002d00803261f43c011141c1d0b004c9000415698400300400c403903120340c81e085401c040714409560101ea413040504416501402003406120f4010089803d140d403281c0c0070400c075070724551040420b0303074542c0305010801100344400c0b0003811003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 739704595 1250 739703345 739703357
    0x1507030207050d12091703060109140303040b092b0506070e010905010f090f1e0906320a030b010612050705161a011401090603141501050d090302060610 67
    0x19840d02d41c0c6401c64919280140701d20000141d450609a0300030b4001d403900034145021416040c62041e140360701c1203801e40d000072000700002c5040b0428064556440c180a40110b0415080200340042540580c0001e81d00c0070000801e411018110070904241c0b0f40305990b001d21985092500c10716200c030151000c014006612030408060364818100c0040b1242407174102000d26a1010540304021a034120a20101c0541008101103603040380d0010038045503021a000142d42c0c2c824501110ba540c040d2840d80e40380a000003042c09540120b252400c48003204540003d40c031200000c0d50441c0a038801c8800040b240e004001d030301d8001003c148000400d40080c04107142c489001000c9124411500009003d001114024800e02001d0300b2001c01c40d50000d4030031541c5880c240e40d40300ca000070802d0f0000d04c40d09804629240701c0c0c05040c03003512901c4841c4201d074845d0104080300e0405d028025041090500c0101071400b403a01644916600a801500d0700e810305000303004c0c42c54051080007051140c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 739705845 1250 739704595 739704607
    0x181230020613241a0d05030723030414040c020c010903021210020c0705030c1008010905130b0703050a0b0303040b070809010908030c060f060a212315070302 69
    0x500807440e01ea2041d0b580c4180d8400640500d0102452039103000044464180182c514491070030a6200841c0152204000800e054007101005000011008000e01d107400034040c980010307055164401002201042180070442a0180503103035810680c0304a0500b00004c0342c04840c0d081510845200e10301e14406401010121700010780300200500c80207000d00204248803900203401d101d82500443e59402c15503490721440403d0707690745807a00550740300740035603d00b910b0607103455405005011216212020541c0c40c0031304100003040010507108820300701b0090300340002e29400500b071141c10152000180340c1085440d01045411081120b4043d900c01c0006205400480e41601d00c01c035802544280c0d902640307001210350071000d074880f00c020321001c5500380d0319075030100b030003842914040c1010403981d940e5020001c44010520400358045c0140540081c40502e84407003250050080034000ca40d548800040604416400c2440102c1c0d0170442104100880c003081e0182c21400d02c3c0340560a040f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 739707095 1250 739705845 739705847
    0x27100b060f180609043803060a0c0c0b1311040c1403060307030804031a070504150302090102070b0c0a0b13020306070f02101e0b1e01181230 62
    0x122400601e0b428540c00445146640d680342412900709500103401484010781c00c0380707110f01041c0e00090385110040100300b200031148501c3c01a0880034002001001c664a840710100002c0108039140c80400c0820800640400c1c18185042d00858410000c0414090903042c90b5014654100a86110b00d0030300b000e01100c503a101042140c2a0f40c070250f002c0d966141c6200180c0b4110090303100608001010a00009101840326000250a00c800c3c0c0b5610035658443c00316000e10a03400b03544015488040ea800c0c0040c032070f601800d05a40103004495007152102d071010200d404c0000074400302ea1148010740108101d540c031071a00180110310b071112501041e030004e900e03003a0080601007081980c803103040b011340c420818818100340c101003c10003c9100526941c1c07e444400010b5092810300240d0561030070402c0d9400c145516013007201c91132000e05001120301d1350300c0b85c0014030380310440007020411054000ca898809032240b40b5000181d50540c89034808880c0000f4100c8c0c0001d006c10381c80d4085 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 739708345 1250 739707095 739707097
    0x1518030b01050609130f020702011b03170c09040f02090301061d18100507020d0806030f0706030b031002130312090e01030b04020d0609060c09080d02031227100b060f 73
    0x14402c111541030311498400301248a010520240000030390501131241c440340c4170795005044242c000e03600c01d00781c5149904103446481d0800e20090000e6103801da4000300d25018500203401110781c04500346031041c86000901620395422106824503800a0540794500c0c1c248110030090000c0810b000d2840481a10301a0544008140e0344401400440b00c00c1d00203014011042900f092590402031420a00c00007980c4040c800c101d5030100d800d10000c42d02500e000205070910030320082c0203290300c41c14404100e020b0300c0184005500b61041c45108003005c090b50018009501001110028107450345c18985074440c844e203170f503209111200e07805000840300761040380e055035004050703188180c90b241b01003240d541480801912041c68840f8000400c180354000e04030341700556458051161310740030090788580c442201640568020030410625441c4c08072207517440640829800c655640c0e12500c0c010f509400707002c220046e081051b0a00003540b41d4030969400c1c0c041a5031107414022403600011003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 739709595 1250 739708345 739708349
    0x91404060906060f0b070501050109050f3126070507030b130f0b191503031d0909030d0e0c130914010c09210b130c030c1518030b01 58
    0x10030362184421024010306401480c002e2030200007a151055440d032a44170a9001030008695550074040000740301140c60260354000c16200b40b00d0300d41900c40906d10011580311965000d0f08034511a00300c004546100301c2c01002034020903c01c0da9005029038040c019160013400010344440500032080443e02c0040c000040c1c9034081a2810151160103110b541400e24440041040150a02801c20007140707400640c0103202c498019041a0403841d4044140c68984c5030300e9080d15102c01041001c40d02c1076141a05028061038494440c0800da000b04140b10790803241ca038541d5100061541024055100e00b0714032240100c041c11701e50710320f100040c103005c00c103a250000d499100c0801e003092003082500b886031058000000c20496444100113442c0005074400c5181d0350050544680d0844201c40e10000d8050344040790600c2695103c0f01d010440c142034070159110b40e001040800058032042101c005085141055140100c0b0800700409108000a821807174040e5010104001200241800c0c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 739710845 1250 739709595 739709603
    0x609060108150a0b040501092703140f0f0703030b030f060402130c020c03010e060105040b0103020f0a0c03050f0d061502030c10020f0c12041a0a090e07030e0f0d0801091404 76
    0x20b40d6200c5110440191010b00e140e00c0d4000d04d88000060280031941c418907000c08a044043c8a02c01580c0d0501400070f85850040c0100d079034801480300711035440004001d060712922009080c03140002801c3c000390000354048010999a07050004c01d841e0812102000105800007800b05141c05c0c1d002c02d941c0c80b102064070701055141c0c416071612074024040d107603180308041e0007000701c06488038002d5520507080c07240900451520030892400e512900842e000d0282e40da940c60718008a40c1401c80d25500190010303010080d0030300c040d141d07610820004001500040002140260922a01c04080071003a00c000e8103561040295a42041c0c0210303841d14048001e002c01a01d5460f100d00d01c100034415000032041070300070400e159403031404040281003910f81d420040700c04000c0039440080103105040c0d030750b0042403041d00104102e00e012550b5aa000b0600d207004601d1906a50303d051030601d0b0309801140c560443d11004004e10750011201e4014800340c602804404085204c02c0402c11003d40050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 739712095 1250 739710845 739710883
    0xc0317270a03020d0605040c0803130311280305060604020a0e010e0a051009090b010e09040b190504051b0a12030c08040806010b031603140112140f0f0609060108 71
    0x56560789150090006580180c20351540c410686031260080c10119000ca448009805020500b40300c00000d440c0c003110b1040c21100120300316146d2504600c100c6c0707800341c1d101100d0344a0640c41e005040a86198541106194a00038103604d040760400c0002001c4034010341c8140044001d0079800404d01403045000c1c01c100c030900341100086036260585400c001e8006074008a0700d045c042d4401c924034100c0d1700448041099060200044621408601c8000e40c001e81120100b004074040016482c0c0285d0070304801502c00000080b505c1c2a24030859041c2c865401c4860f060602c402401000760307001c00c040340e0100910381842c4a4003103000300c4c40c078042e04014200b03400c4410410100b086401600e031160440b495981e54150b444020b0f07004950f143e00c01c0d0140d01c046280b00e8040e014150705040c200102c075907141e080c410b5a08440075003080603600d1072010101c80603000d0f000d203d0480c943e5582c0c8058054052500c00c50f0b894102d02034a5240c3c2070340900c00400100d000030074200701113400d802e109 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 739713345 1250 739712095 739712167
    0x815010e040e010e120406020705060304170a1b0f11010806060d0b030f0f06062409010f02192f060a05030408041710110a0206070302091203070c0317 66
    0x280c0c0149240004c081030f0748100c90124107003e440034090402c5a1566003103039800713074580b814071815010a88000301840f0a094040c1e200610b5040680303002001c6241240c0d4081a400e07005044842c01c1d0001d86540a20301340a1040c400d441002010904081c20804028140600861003d104100340000410b560b9640410196420701603000564040d0b012a01340c4446010300e9500c0c2c034410380302244581d01080b0b84c0e0640007240b5a1200302651120011404c04121500558a01607661410400c500440d001910140031719090b8210380c0b13000700840ca040000341d420381c60303020b41d548844c0e08901d40d0012202c19650342e60b40403128265454a4183c0d1644c5482c42c102040c1e000d1500301c00041440d48020f0381c48000c0010304850000240c2070203200c440181c10922045204000348070340144c020350006080301307009030000c04036a680503245044145501515500755000320104070703502d02e4480d4041061043c5895100606100842c00714a40070300e000d660807947e0440d00000c29095169900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 739714595 1250 739713345 739713371
    0x513030f11120c16081b1e03010f0c0206060105040f14041107050d1d0f010c0507080706120b030118030804170c0303160e01020a1b15020d0815010e04 66
    0x992039003500801c502986030f40000b010355845481c100e03011181c0041c16240051a1100040c210b285103003011000d56101e030608051104868801c0c00e5101c40494004941490762003d108043c4000099480060740b800b81d0b0344024200080500340728100300003440140800c0a201c0c8038541164100714624164284070703c003140c050603d29100100c10312010511034184040407440c0c40d400711203690b66075189202140c0300c00e20b8141280302503401c0310424440e1070300755024000d10f01c40780303020b00300301c41081d5515034070185001819000440068000744d00401c03440200d020b21540c021046000b4002c256042420300c5009608200c041c040101c484c01040034480f0300000407001c800c1c4c459007150b07504540d101e201c0e640c3d0b005417554601140e00e9480010094800c800d26160f20b0416809844441c0681d1589135245510700e1110820341c1102c000000da120541488200406e819009021050010103015015040003026417001c0240002e001100e0f0ba0300c024021511481102c001500c808502c0c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 739715845 1250 739714595 739714603
    0x7170a0e03070f0308010b13051c120c03090b120609130515072316050102130e0702070b04291207032405030d0804021906050304060513030f11 63
    0xc510058000016a00144000d4282410f03105009844106141c2d07070b113502e9040548130712204040ca1000e264000c1c0480d20340301c1030000041401d1003840004503060b45801c0b8020500b801aa00405c807160302507402c043d0045881802002d0406249040c0074108103246048000100080c0c07040d80f402000403040f9440340301201d40b044d004021595032903002112130f4619042a940080400d801044070911000d11107c081c0b0f05c5900a03280c1400c111501d8940f240b00f0101c010700322500d540900c0b4003002c6c0c0301c100e04004c0080c0380c10428100d160520700c02c00390070850f458200f0f13144e0300c0b03040200303100301c569618242c1c0ca82e0304154800f4140841041e11300340030b4001c01d41c3c0c0c101281c1174003090007400ea51580004c0051180d01441d42c14640a03007174051680320f04c1d4882c05405400c0a04008105405504d6241c2c1c09400940620034101d0341049111401d4015048030000c15008000c0c8000d0189900ca403982c020340c104c004200200c0c2a4402a14408825980340b04100c07050740c0360780d44044140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 739717095 1250 739715845 739715861
    0x1030c050c1c090b0a0903061509020f220e04020f21010e0708010216150e0304080f0d030504020d2a292805040e0420030607170a 57
    0x41d050320a441c400002000300022010302c000001440e400c0042802d2140c20200c842c201c0041d19805601d61440e07480c4406066442d04000c1756640c4000b0020300c40d40940010308400d03459500c1300340d84d03008904044460304074045042c0d40c801c0390600140281c0a46030615504590100c0702c101c003281180e800607078956411495030409c030201c90034052803500150005c4640d07584440660343d01c01e8413044864200d00500b40d43d0040301e20710081e640007154040c0001404500100c0d40440d85804202c40f0307614507031099001c070013030f60300502e21005107190602803510505030600e02804942040d400161412440e08405042c01030741040ca01000c042e9817602c081c000754000c4500402c2c0740e80710304841e0424180c0203140d1100541d44c10000c0e45c050008102d41c002b80d00b440900c0511620106441d401a84803007000c424003200300408074450f071400c06958421845862181103c030f920401d00800c204000d440c2a01a5000100307201d9166008400f01503081030f001140000c81e5140302c42003014001d01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 739718345 1250 739717095 739717117
    0x18031e0912011e0c020c04020702030a06020408210f0304030807020f0601060e1f021903090506390d0309170f070311120d05060d0c090213060503040c030201030c05 72
    0x18074416111160103410450a064018808418441c92200400e00343c450b26504100140c0182603400d480740341c25805866036900141c11607000c0c1078240d0300e51040303030301c5908a04556804a003141c40726000e90706203980124400e41000c0c3c2440d040488054482c00050002070a008000c000180d51b1842049081c08a4004000b02c8c0c0c00d0f0350351010090503201412100070700680354010051060383c03440240001e0501c40d5401041540c0040704d413914002602181101001201600011607a0f120006080403a40005c2504101e504002e22103410300012110394150000e003a40c038015480f80800d01c0100c0800034100030a0792045440d000c0410030740b4140d4004d2808011692030308001403030300070302405403094490b10b0b686000079021a644078001c6260a400711810407180c08800e001c0d40020b0342205000c2d00e54651021990b90b40a01800243c00141d14a54041380c00d2203515000c2000700000c202c28140a80b45040a84586011200c00c0c0070207410305480b40c44032135010313129504950340c0e03035030f8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 739719595 1250 739718345 739718359
    0xc11040213240203040807170a0b09010b04140609071107050d050a0b0108060919140d0e1c23070b0d020a0306060f02150a0609020705060f18031e09 65
    0x16180b40c9500200002e0207056112040030301100183c0c0004210380940300b9070f00003042042c1c60400e2003461800300c8a118265402003107601030001c0c82c00c5048a0143e0140000844c2039003029050204a88000b40288443e840000c01e02429851700b1448039001000303403a2030940c62071000c50a80c50841d9590095412113968901c1e01b0900c040810300e03040315441007100146999880c0c002568401d029a1404078607085204482c41040c860604001840d00c1000d01c04840b007400e0000d50b05142a140a10010032031491b4021a24641110341000c4040c4280d00728142040300c0d1282180e01c0070113160080640e0414182a103c44030401142000300303003003a002070740c0e09021040300010703403c807140b80804242024008070303c540c090842d080c401d00035580100b4101404042c50421803a001d4840301c101a9a0500851601c0c0030303000902400f406079000b0440c030b0400400400644000818000a40700344c01a00d0302d04000200444980121b051108456034000a10b4074100b0302c1800300c1a030703000c02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 739720845 1250 739719595 739719599
    0x2030f040b040e01050a060f03020901031518060b0f09041109030d170108070b0a050703090e100321050a050a0207050a1202040b09060a0909050f06040311070b0a0c11040213 76
    0xd4400030700030b840c46200c4960f89a640e400034041107a20741d01400000c43c0301da004038080e09120343e001d401a041c0504d0081040041c40c0a0500c0c00303002030304614510011320490b0f0748400850300a820040c03108141003881c018035115480d00c0c50148814144c4280d0702c0c0c0d07584a0900b0a02e0040d44c80550b030003010f4410455030f00728080c101d40003204951840030b4001d000042d9954000c2800000c89201700c411525003003813101b0480301a400708004405002266a02003140e075075405440d48920070a440f990125815414030301a06a01d5440200004415102030b030401076001050360100001402d00c6502e585034004141d0a003140341c0c0001d600300d80044800211060500070482c0c00d18004d540030051901303402d0500c82d5601d01141c1c2c0c03a800002c0410200300034280d0b0750244610900030820b5410740404c0d402c80b2402d000055a00380c00040e00c0041000700c1c0741c4103008490062210350350140c0381801c0c80e01e02030201a40c14401909501c11240d4417481c1c3e442c0e9804446004290200703401e055a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 739722095 1250 739720845 739720859
    0x70513090606090807080d0c0611070b01090209130e07060c150e01140703050420151206090105030703030c1209080d0909060609261204031101080606070312090302030f04 75
    0x1410f9205841132840364040c0052a00341c0422182500c17440da5031410600345942d02c9030310203424624051031041104101348404902802c06d1395010700000540035070b480070762104101c461540280d031002032a1911140c0c140b031200004281c800c030390603814140442401341c1400303107440c0b01084083d401d03031b03062004400600c4010340c020100807016034045d81e00342d10340c601d088044581c1120300401110550100401404010b0300907009000000c0959036141187e00108080c0d030808520b801c01880311030284038140c40c0c00d0307038000d001d00b0040e00240041817941d1801420701c820300d40003414494641c03880e812281d1043c0038050142c050042100c200542c07680c00203003101098810042490b00e040c5002c07a40c01e2060102104031036001c0c104011b210309480d000510f074020a050a0700c140308920f0b1280510450402800040d4020710b0031059840d0b100d000035124810007040036214a03800c10900000a800500030315041801500c0010b00e40081d18042e4039610640060140e00c1c240441c0002d484 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 739723345 1250 739722095 739722107
    0x402031614010801090513020d060e07030309032306070806030111040e07080a0b1003020306040902120f010e0307030527190503010b0406050a06080c2115010215070513090606 77
    0x3500c0e00382d030b940b0075030307a680c481d450120b86c1c041e11f641d070703500c41da207030149016103014000c1c0060300d40182e00001d080f0305000340c81440c005050b4811400718802450400a10000440d4803941c0d08000d141083d00d85090304070640c68201c020700500611088802158094409502c5400d05800f40b41c91640c1c3d03180c54200e04214401c04988080004140c000000c003144694010074000f101e001e04481070340c2420140540180d0001001b003034025903a203031803501603618100100c0070030f50f00740c001d0035240f0b04500140b425140c10710038101e590342c010008180020341c407108485d00110041021144000340032001c10640704584101ca46c0031001c2c1410500b49007840200b5001c540044000b00110b400400c140001c1d0707855440303007503030200801c182004814060120310741c1c44442c40380031601d0a854481303a03050b1281104c4900f843d0341b94800420000d040d805038200d1558009000400340380c00308418401401100800b44002c000010401112a01008410038050044210148112603d50100404c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 739724595 1250 739723345 739723379
    0x504030c02030c01020c030309130e010603060902091b0301140d14030a0f090b0d0e1f050a0b090411130f02042301050f041a0702100905040e0c01080a0504020316 71
    0x2c40d00802201c0f510940c0009540030a02002802030340c00c01020344100240c400468151001c0b4984904180d4400300c000c1c402c140145101e0036002886184a0052000128004084115070011801001040c64142e01601d04403204615004040d480c1880401c000001007400244090104c0400855400010005d448103115541c4d0b081c410003080130044800c0ba525100c0e031085010100f010459520303013a0000c070240c424140450340c070b5030704880751541c10202100301807042c2c5558000380b01010071540540c0303411b8102242c3d0703114141010f484d1003004007001c4c00070703e02c5004040e032096181c3e1003a4102800c008420402151503503511100018500102210342c58103881d01404480e0315130082c0b05541c0700c84803505e0030b14100b505242c8000c0e00002c495034404c0340000140302d80d2006a481d05100300e209040c40d03541c801050328000912060b182e840080c200590070180750030300e2503640080d02542c00301200001007403e84490001c80e081c940100c0400c0003004c1444004240780b41c42a005140c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 739725845 1250 739724595 739724599
    0x21e0a0e030c010e09060f0d050d09080d1d090613020408030426030d0911040e03090103060f050f220c050a1412040813080628051005011d03010504030c02 68
    0x54030440e0b00300450300d00c440c5100d416402503269001c01d409041050031861500c4020303104423405181038a80c0351410400d420b03001c00240e4500020300080b8010311100c3c90304511818180d40003034008505404200f05620340c0303401415654006180750390790603040542d82c41c11074401c655951b00d40031a243c50785d00c0381c060390381c400402c07e01d20b00c200d04014910306030442c0c108016605200040ea03245000d800e0754030007654043d501e01c560042980d15881000c2c1c00402c814011a1741e006202c0000d81501c030b440d03001850341c2c125034900700125101c44100c0f00c014070046400285102e08001e001c03d1240201c0404500d191511581c5040d940c1c02000400c0c509005840303060551014201c0d0860602c10744e61440703020b0b143c00000c01c0c009600079014080b44400d080007903003c41c1e1900b0013685021000c41c1c12080c45400205001c0c803043c1e100302800010351703044030103002c3c03440d0801820040460b1032203501d0401420740c02004a2000104c141d01c3d402d4001002030105092a00300101403500d01301085e8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 739727095 1250 739725845 739725853
    0x27070305120f070b0702150c030403030c0f1e031d03071a011409060301021603031d0106230607060603030c0b090105130201030b06070c080304030b0c03090a0204021e0a0e03 76
    0x100d41d11104040e101507440b030300c01203450308006075110784050001520b0101035103d0310b414400c4c5100c001d0131035442200000c818a4481c6014100142aa603255500b541440f04a040582c88150b20a540070094401414a041030300706a130030403401030100b81070414580c0c54901d000d1400e00c0010000f080d0080c091761111700c04220281c416160404280b18807202c03070110030381401c620300704481c00c03690000004000609003c551020a49031402882040f00041e50300c0a404000c0700d80410070f95807141c9030100800c51035080c00618120000c1c40980031044002c0e100d090412651010f08036080c4980c0034405020245e0340e072501030312010348c011040760811440740c00a85005414400c49100d11031500d0380f000c420143c0d030010340c010800c865406070404002c220320310101e071200007000000c01880c0025943c503031450600101072a4042e03d1480d1500003001406075009000603d001a95012035006079181d010002507801000d00b0040100c1644021581c402c80b40d4003c14030180c040c800703a06032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 739728345 1250 739727095 739727113
    0x1e0c010e070e1005100c060905160945060c08070f050901120204082d0307121803120323010b040909060e0f1e0712060527070305 57
    0x480c000008840d00b43c2c1020389a0402c0055141a0084101141c0141000050341080391103140903103e13810350903113496124882042ca1380882c07841c1c040090080c0801008815000d03608000388202041c0c05c80a400151f062000000a0b0001d4140717400c640c15094415103500d51a110020b0021080010041448080044c10712401005a030340005042d40d1001d160a00d078000554003085030144105d180b660900001c83d043c8410000801e007801600130030555050070003500490a81281c0a4072542e410074881280010308131101c0303440d901031074106020110190480060810b0003030388080c002000301c01050148940590000d40503800460b640407803c50f44500340450540700303205900d1050410401048001d200d41d00242040f03115400214038010680669440c01c0c0c0250000380b1580c021007000c0c1c8200c0e003000c031198414420200642400344c902001103188100030840503042c0c60711a40001c00601551461b00000f0400004001010480380c4c0c2c400e945046600003203c1c28400c0c0000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 739729595 1250 739728345 739728359
    0x913151401080106080c131505090f04090206030103230a03030507080a0606120906090203060a02091903052a09040c0f1d0403110708010507030b040b04020c060c1e0c010e07 76
    0x511070603562162170f13032609600c1d01221a0f01640c0a480004580d003084100400c43c1d081c1e42c41a801c0c10240355a515403240d080108019407040e094000f0352189260071000c00041c0c84030800d0b241100e810008406c001c060840600c99203040780d10309a4030328003640101c1410950158042402802c2d22f03038581200da0b81300700c900c80837540c66000744400b2601c00035880708164511b410030852284500d00106500c181a8042458180207440050401d0740216a01180341001038450b0f141044c3c002704180080d00d140c0711141c49020091803030307000c0700c1d0742c01c1c1c03011200048041001e00c070100607217400080d02d010300300750104207101d010312012f41c80c8038000010803814078001060300350746642913032090351195074064402c1a034203400e00b400c5004182001427a07070070038072405100ba0200d44010600b004401c0401003110b64007180705102e0361052040c4540c00c18000390856210800001d02079450030b032540d545410811041882c0c21420780003c0510220b40b064100c2100503d511080307500042c0c40c0e140c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 739730845 1250 739729595 739729607
    0x14010603050925051807020c06191404050d03030506030c040c170a1407020109051501030b06041a0604030528082710020109020112060b07080913151401 67
    0x140b0b10003590000c071610f81c007440d400c1140e03c406524031806070001c96580700480e400010040c4949003000e1807400300640d4070703014059100f03001d1084803544d140103030624000b24030380345516040702000b180e501c0819210621000f10f501808001300140e08160403490010003a107011218240603010b101c001d45141d091a00a0103621146a211442e28080400150240c00402040321141c5a150701c1c1c50030380300c0000741805004204950020804810364204241f401592180d409402d101580042010400f0081c0a070b4000e182203401140c3d01c40d04c20a603d20028014001c940d0041c000540001004030004000d0040e1520209032007807030078400b01e01c0e020701c121080040e0982c003041004940080003404030401800c010135400c112030000c400490381e08540d400503400903039520f00c4080f080d5a0004000032403a00b0380b00c81031207000d0400d00c0c83c0300f03d40220040107215a601045160b5603030382d240300c5848030080241d0208182c02c0901803039008840030713220749120703e0318100c02509503500c0382c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 739732095 1250 739730845 739730851
    0x1602040b0f0a091e140412080f01120f0b09030717030c12090115030c06030e121c020d2a0507240e0d0201020c16030f02042309011401060305 62
    0x10103140e04140b0f00b9401c40013a040c400000c0d61080d84042809203600c0d400d108007618a9052000509949400e180c5515400c151644e04001c1c400400c0c20003800ca1601040b2905440401001000180b880d18100351082d10011000f00310056401c204991144004060540e030f41c002c00400e11490301184440100c3d110503180d010010a04108800d2010441c1a0072908030341342c600009142c3c64000c5000b20301c09443d8104131000e84007a8020450244e1500894a60751511000b8007890000380725803481e24031690554440241000c0e0500e1407454155060340e001d01c45809003030000c407007a00e4145101420380030030401d10b0b0035849400b102c0740d4031402c1070302c00c2039a2054100540000c9370381140503030201c141c003000d42242c41e030b40c40d030342c035070340288000b2500a601d600050b8954607507030f52403420400c19440c403018540405100704003080c6010105c110780c03074043da800100f8445801041e6040c4c1c0d400f4127034111000b580c106101401c04154080e1080c28030000401c2020303604e8260480982d0340039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 739733345 1250 739732095 739732099
    0x30d0b04150902031906080d0e010206061e030102130909060c0f05122502010506120d02030702120309090c12064e03030f070c020303071202070306021602040b0f 71
    0x80c00074400c02c20154000c4d6002100d0a07501c040d030a032501c4441c3c0035078110b5005a807084d0000e81d149070102d50090140c2c41000c50074005880d4614208002c0b03410020155a000e00200715881c038117085071030039411600d01030f400c04a40582d07691902030b103101414258408403003091030301412004643c816207019149501507590035141c0034091040329008240504651501107984900c0604501c850764420030307440290b0004038240c80c08004001c142c0c8001540d8002c01d0b00f0211101030701590100841d10016411207001c05010002c0d00d800b031650141656094002880c1ca00703104007008000c0280038102800c1c00d50324030581e981002c0c0001c1c52454034003221130b40070041c040c17051040982140c00c60308147c10100e10301428a1101d180f1044c403486503042d0b51f500000140728000c6090040154403807102e0603c114550010750200381c0e24800e480b00540b0080d0b0308074086810300e2003404500015600b021055466505158414540a20b1000100c6c859440d20003c0e201078105045d58602c02900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 739734595 1250 739733345 739733381
    0x10201140f0402010905040f150f120615080d02150717041e060606110729030703060b030f070f0807120b0f0d060204230a0504090201020307050a05030d0b04 69
    0x40541c0480c041d031024000303d05001510134007140301d03140c500c100302c000c00d0000f001145100d4a02c186001c002c60941010540d0b0380d505605208291440301091034941c0c1c0f1070400600e413201c20401058802c09504135880c60701510039070b02070540d400a10300c4032451400c902c51060b6100d588050311702c9081846401001070034480080d001c1141680c003c0f0000e407080304d10010b2000d4503a2800100d0f139076030700500b0200f059081021480f0400b082600007600180913403480f141c0e110320728046803034042800d001d0184030010006001511a070450b000402154075115160b091849050305054011186500040c403000c0d80c2c40c10b400d12584220f030141c40b8689814a0445a800080024000a240c41c64200b19454208803ca03141c18840815050082400503226030400b41c0d40e04100f0840d005558000f86d00507a07250080d40c9080c0020100d900440b8002800a55840142d0841c018018080c0080c0210601c4c40d09201002c0010f000250714071100b0071440042c0c104100c1121005c0c401045d0b0411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 739735845 1250 739734595 739734601
    0x120c0403021e130501081b040b0603040602070c030f060b040f0902010e01080c0915040509060d031704061118090601140d0e010209130f0c0816030507051c061401020114 74
    0x182c114900890030740c0a011107020811503480d9030240c0d2001e038094240d65000c4042480e0308010240d0803440f00c04101d809010310540034001074818000903101030171465000400310100803d41d40c0c004000c3d80e01142c00c40300c403401410140020b180b44501280900e0404040c003103010002c0c442c4482c001c0c0e0507112088044603e00045030001c40042c074504144100300840d42c4180e40d295100b4402035660110301d69114200814000501c0004c1c0415001c0e00380c1209003400260400b016210785076100d081001c1c0b40e51603007030030f50140008071030301803495070009000d03039100b03c401d80060005801600c44518a07200c400044909542ca0385a425001d40305000300081c44016800285480e03551000144c100748000700040c0700392102407100c1c139203241e8941c07100e44520b613280102141070106040c03c02c820320301803120481e10036501c11400105030703954002440303c038043c2090703820782c60707041201e1072200311402c0f1010b0003090540a4520605403841503000c1c25841402a00d40e00200e014071404162 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 739737095 1250 739735845 739735879
    0x1c18030302150c12070c05030c1204030501061a0a21110306041103130818120a0308070f050702090a0f0501090902011112071407050603041a070c0305041202060c010c05120c040302 79
    0x807903206d600311410302003000400d01a4030108080660369840c0115540e4031851460f0481c2103400c40d9101c5090f01e00039858501c4400041c40960307281c020301c2c3c244850403051840d2007041c1c6074030a0704101c28240c580f00c030208400c0480c201031407040c4015241003014005205170078903070b400100c44904141d00480e051303100041103074029002d40200d0290700c1d04064086070000710342503250700f60341c4480d60121221009040d400743c85140c100a113070801810000c0c100100600f20300c40e412001e4066001ea00c085050301c00c03a917119850500007a68100804d50319011079201810036248140c0c0010400b0210329020034002c030388a65500e5240b01810300c0c114050365540802c20b030f2502c55141600800c84001610340781c0d0b030b00541c803452040e0071084401c1541c100199290383c0251000c001c20058011101c0040c2d001012201078480c2001041c0007000607100042c068480d603058140e03503500f002c911080c102d03040300243c03c00055035080d101650b520040e13000a02c0c003a0f171101a62040040d0b80143c599 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 739738345 1250 739737095 739737107
    0xc01020a080d0e03040504050a1413020306010303050304140106080706090e0c12070903050316121115180111070506130f0201050304021219051c021c18030302150c1207 74
    0x400c6002041c4c0b4149603540700050b084440840300314007403d8540b002c19000414210203140d20040e030b2420703441030b802103801113640c0340c1d0140401004e0000000c00324043c0080c4408541030101100d000707111143d224203140f0344403072151140c100881d405c0350003c03800d1485002041d215052030703580782e82065240050030800f01c5020780030400b4440414404004964140002d12040d1034100b04044030000d03e107000800d072480b044041c0104040c080000c0da010402003441015003400b4008060107441d41700047c201542e0b44d54108410391300c2c2018480307103101d1071000381c094a405a410380d142a99000f514500200f9402401008070007540030b01c4005600440241d038000340080c4c213508060035203450b51840c1c001c0003024402140c0407101c0c0b203804c004082000c81d540072141c0a2001010031030640180d07a03036044080c00024801184801c1010350720070301c450812a0042001c1240c010380d2810069224813154040314010711001e4001040280f4000490303241c001603001000386075841d28412550 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 739739595 1250 739738345 739738361
    0x519060819150b040e160219020319030201240f0b0d02070c0e04021e030d1d0924030109081c060302041b0e04050f1303050c030f07050c01020a080d 65
    0x4503070780c6101c109110001061110080c0030343c10b29480e516801c0c089000480b9100034200c040195001042c40480c640c08199503944903485102070001c0d1016100003802d0140051080050200901c0000d041c5541500001004040d000c0d0980c5014010012902c0b558114045c0e106c282000c00c800b003103041000d8008098140904600600384151a0740307a403404503480d031110006401c0c1c0d0050109520344896005078003406d0b00035800003056444007081e19216038090385001d00c24034081010202c491080d00400418000b0034101c83c074a0003541114480c003821040c401c900b21450490401824140301d1010180e4001d141d4030b081007100c2ca608032000307440314072140549444220000042c0c80311301903d01c88c21000c01c02001c2c00710801e20001c19001c08180014030a504260902c82084228520b40e50804809030030310306802850b007030903142c81c0f091000c440c0951100180c150221340307400d00030b00300962082098480a000580c0120392b01d000c02480a0206e0408221100140c7d43e542c3c17040c09 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 739740845 1250 739739595 739739641
    0x150a0203090a03060c02060901060501080123210f0a050325051605130203040b010905130b010306270b06040506031501080109021804031b02060d1505190608 69
    0xc5400381030300101d02d150b5260340c0300302d807000c1c0c8034016001c0300c6030144070700da40c8101604004c003c0e1504d170000003030241c64180728690182200d00900f84103031076159172070604004046c1c0b0780c0e445000603007566492240144118140d80c01000c004113500540031680308d540e01d170010000d508210040505001491094a03465000c4010740c102d8800074034240108075036103a00c8000d0a00c40e0380340c0070510032003030091000500c40700e20400800c80081e1001100c075041d1000750300d000030155601032000014205010b0003a00f03070102c5d10000010007883d500050001c6504501c4041010110155110a5038002000800380080c210025009080aa1010b030b44000c008040f40d0451070042d00c0100e00001c00c1e00049826516194200103506040b000a0a03400505440c5440c5180c01e0714000d204100d4051061108080c803200c2c1d07010741d910141510002183c000342000b520440040303810011029202d0a8027446880d01009003006442d40182c04480d800d459008550f0346820704501142c0745140025 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 739742095 1250 739740845 739740847
    0x3201080f0c0d06170a0b07020703020a09050a0b063906070e0a050d030207051009050a03030c23100506060a1704080c011103011701091a090c09070e0a0e0105150a0203 73
    0x2540741d41c98442c140050070704d6805400c1115550802d003a8850005040c10b0941d8060001080140c60b82c3d141d8000b100d120700000613071916000d69220142c4038141215030700440c00f1544120340c0e000e10480360410403001c0100b1403040000c801c004407805c4600311703460b515080760002a105602034500203803c0c82c00140306a1300607031142d0001e0000640210b060740180c0c054030080c8140d003001441e080000307103642840201c85d442c020004209101c00d0000400300b1448902c1c01003001065400d54500184213040d01580300070300c0c00c200d0391705c40365010151115428080803c000c0c0c01c00078111000301c00701c0d558804c08840340740050903c0a2001d001240d40d02c03000c2095080c0a4000e00ca100d080143c8401d425076694034048950200411002c0401c1040c0d152200d00300c0000c210104a500781380500c01d980720941c3d200b81d80142808408803c0e140c200d00e00c1c00800c00030643c41900030500103030458035103c515403201d034140802d80b001d00905800c02c058101411691000d00050300c4080600d00c11a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 739743345 1250 739742095 739742099
    0x121a0f030109051002040509010b0327070302030a2906060906180306010924180504151a04061211010c0c0f0e1608070f050d063201080f0c0d06 63
    0x25444c1580280303200540c0f96000c20140142d20304a82203030b00406500d01d1007411400d0100036501901040d812000108501258400f48404188843c00c001c680040588000181034242005010b515047c00c00361090380100ca070809081040146004a07005048a41824002c509211362035010701d01100d00c1452824002c002c556080008a011b0144075001180344118108001311010451260304035448002c0c0085c801c90307480142d0a4080144104003113084c0c1c8860501c0c1e240100c1c034412040400d0704080d12480c001e0701203002c2000d0f00c0310a5500f00704c11581c4802078940c0701113080c401042802c00c84002c02032584140401008a40a460045070070340e84d5442c00c01e2041000e912414074440c2c03500c104218005d00e80041302c0d1944850500d01240e01c7c1041e0700521020484400c0800d1040c0030401c41d0061000b9440702d0044c182c0445c01600d85c5110b98050800407000809403900c481c3d42e0300207140a035100b00c9005000c1c01d42d00380741890b50b0702c905c4942e03105900310b6109201c090350b0795500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 739744595 1250 739743345 739743353
    0xe1014010221040501140a08040641090d08190204050607050f010c09030302061f1d0a0e030708030708060d0f0b040308060109050f0103050a2a121a0f030109 69
    0x103803550b040c880420199240d25107400503116000c5800c4031040c4100c240030103100580c02c503200e9548a980900e0000e1a02400c01010103014051020150340007030303010802c1202d00d042048500c0f02c000040b81045280c3e40d40b5651a66144140d0303014001030000404500c00e0100a0b6107078002c1c009010016042c1925900480c80c2c030b800c40d202c140c0d02d6074807850001c3c03104602840350f05040c00941c030344644c0840c210303140a552144090031011580c0603d0400c1d240d081c42644046010703001c0d661240e0401300c5030714075425828000b916503400103442c21001242010002007111714035540660300c0c074196500e09006072181c030001409150400000e80070b107400902150040340200b0310406282440c0d00b000d0a0040140030020400b03814404444010312413a07990740144020400c0900e8003007915540e42589201411a9422000e003c28451000ca40981c2d80290059a948980d540e8480641c1170243c0a006551482c4296005e180c483c0405001c00d052120700210221005030021801544541d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 739745845 1250 739744595 739744633
    0x30129041a0a0306050405010e040f03021c090e01092c1903050304032304170307021002030909070806010c06021803100501090b061c09020a080601060f090e10140102 73
    0xc035030041c6090002d50300c44102d07003520541000e0311060301c00b0000c3d581000c3e04c2d400743c4840648054a2184000c50700c4c01054420010041c0d408420500b810643d000341201a00d403446170302a51031800c08850001c40c091030b01d8810030112104800c28859960f0005d680024030304c52200b1120b01a005a00800003c00c20581c0320310070b024481e0703aa00740d6174505414001c2c074039000c0b5240d09403041680002d008461014070705480603514100c4400700300b00a4099010302e584600c02d0025002030804922650154002c0041c00c0b1452003039800302c24981e40c0b4103044410200840300c650104121500042c0031a03816030141580d11260381603400b500540700c0019160102c031154a40001e0348801c014040e5840a000d4041c1030003058421a0600c2d07c5503140d640918110390155103415920002c010035035a66070b48030702c0184000002d4811030758441c10000c000d0a10f28055901040c03080400007003a0307200100c2548a410350004010a517810144051400c00c207160311281144100601c072424a88854 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 739747095 1250 739745845 739745879
    0xc0804151e0e0f0f0a0504020a0c0c0e06040b10020a0b0705040b0d06080d0c080301033003290d0209070327060b0307064107050705030303012904 64
    0xc0c80d00d241d0012900c0412010b0728080a0f02030041d1840c036104601500c4282e02142540c008440150701c1c2c4050210440b2207059509d00074000c10740b180c000140062201d06040c1c0200c0c010303901407181d40a05414407003181c1c0002544c0005074000f80089000c03d07000140542c000140749030191400790791b07022090168201040c940c0c0c0065588408015480c000c00c80581110b5882c1401400c503852901c0320440b6002c148400307003903641c0d248114034001303081610410240602400b00f0501e0342100900500900b403010b240c0c1803491094560500d041002c200709150312600034200c40320604c40340d09112510788041c00c100d0078980c036171841c90b03001d003070f01040c0c0000208480b030380e0b6500c0d8a60b424000c007036900300048180680c0005005111060780088540c0c44100c0156851104200c08464032507641d0621100e50300c00f071031070140c1c2e003413555881d0000c1c203090f40140c085403085038907201011b850344030078450040780d5512041852000340040312445010500c2010b400c0c1480d981c4c40350340820403846 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 739748201 1106 739747095 739747097
    0xa06110c0f180c070c0f031205090103140c0717090105040b0a020304050319050606010201060e060d210903050f0f03040303110a0c030b060f010c0804151e 68
    0x112075000b01400300000294901d0301190414007900010b00132240081d07481c0002074070180308a003003000c0c4e94000103101d012009421044c0c40d5030781700c400098140351301d1740c41c092109508036202078403414803070030070b181d8039000d40c40d2401e202c180c0c01740094a4000244080003260364008140ca040d1501c642078076650781c00251007a842c5010f075600c00303030b07051080d4604c10380140c20350084906603a1041c4110703100d5440c1c1ca00168244c60040c06100079070341c0220300051480c03500c0c80c805041c0307a00550300504800248610080348003428201c40c0e02103010380808004000d002c01402a04540481c0906041a45003048a807070f4421448080c0030003014581c1c0000c20101480390b945003990140b0f8441e0180c0c2d5a26207149654000c0301c400d84580020101b95000f94000e0407030b1440350f0383c0510340710701c1c0608005943c005400a207032502d007000701000d03c40820310041d44d046480001a = true := by decide +kernel

theorem cover : BRFrame.Cov 739568345 739748201 := by
  have h0 := BRFrame.cov_init 739568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 739568345 ≤ n) (h2 : n < 739748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
