-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0587
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:36:07.350624+00:00
-- url     : https://prove2.me/submissions/414b26df-dadd-468d-ae95-46c6bd06a1e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 105395683 ≤ n < 105575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 105396933 1250 105395683 105395701
    0x3040609030512190501060305060a271118090103030e090a11030a06030516141009090203010b030115020105040210180b07061407031a01031802030129010c050a140f06 74
    0x100210f21145c140300001980a0090040e40d000c1c00d4001c05503140075040c0080384131141c3d28040d280c045010100781c0c01010f005035101e95103041c41641d01965481a03600c0c1182c503c10360b4100703458003401c01d150041005c02d9000403084081102211181c4141c1c5030003100c2d40c06007035401c4085107000c1000040c070014045581c881421280700e00165080e0401099403840034820500c1441c041e001c29400e19002882c00506e80540300f05182050700b41191070b16030b90740480c2c1090300880000da10000062140c1411036030b001000c006244001d202c10314155020480c004454151501400b03010b0800600400f2188000c0002c8d00158020507144c02c00ea0030500f0150003052240e203003500101e030100e000b05100303004cc0b0324440e600c114200c1007420242c00450082628240001c4011215042580180d4080c0a00b1903c080c0119905000384486414540101079203c3e01506201d0105003420010f000810b0141c081e50300807240710054000440c0c1030741041c58040505907a40109010841007203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 105398183 1250 105396933 105396961
    0x40b0a0608070207090908030f091e070603050603010c1e0e090a0b1009120809041113080c06120103150207050703030215070908061501020c06070501020304060b1503040609030512 79
    0x30400d50840c0d8210b541c9170040c10840e449020301400d000d80400014000300550381d4204e4002e544e800032140408040b2091030184240210740e1141034104a408000c095414011507070408804c80013049030050115010344140018181030245442c85c2c518642424011501c02020300e00140c4000024540b080a0300c00518010721914440c0c101201c460310362500c0f418000d42910700407c03022603019000c1d2182500c40d000012416801521044e04415800388070019080d60070701d1101c080c0c102414840c0c602e0a0080090720030740140d8003071000008050317000030541e0459030040702150203400e00c5450781c4041d214028000d4682c0c4600c2d074002041540c0025000e0405030380b181c0050007030b180c10f00220b03102841485000c41590040c0086042107004890811400c94140101c42070428a400400c0c96a001f0340c509582d940d60100c10001404a03600030982030000403a981801c0101031590001c80340400303040074200d50307034441199003014010300c100c9000320009804034545246c0400203600d02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 105399433 1250 105398183 105398191
    0x112020a09090f0905060a15120813061b0b09070b04150305010905270c0a060306050f1c0305031f0b030603010e1c0f05120106030203180604021509040b0a0608 70
    0x154680510300900d02d03044d1290032641944800908a152668081070300681f11803010054100044800000c101c0d508180e4035013003e01c5080c0007511603100400b49500c030300003a440002444030307401c100d2080000303522000b224598400040c10711515107040e80f51038461503420001804500041c0403c4c010a900f0700c0565400007550300344007036a2180d14407810b60b201038906e8049019903089120580c0c000d40c529205c0004030b00c003191030b6600c00381e00003004806654004400b090b6984000d00003800c0507030300c3c128100302c2a602e000150712040031402038088040d0000d0100000400031501284040541a40c18600e0800c5000c1d1252074144061980e80b054804520030741c139141c040d400d0507001003811050740da2844851408058804816190758071550384000170400c00304408a40b40d2080b242d5075020308865580180c481c03a1080124144480f5070140382819441201004010b82d02d04100290050003c00d0444c0c8801c94480440d020700b400d00101a4082001c10340400c207a0f40c00080c00e841 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 105400683 1250 105399433 105399449
    0x402041706071b060507120f02030a1404080a0e0a03080a170609060f061606060905010311011d010c080405030a050607031112130c0e01030f020415080c01030b0112020a09 75
    0x5440b60101079a142c0d41920350252040e000008807000302c1c2d40f55201c1580041d490408219011030703491000101d80300b401d1941070555012040c042000c09510a070004000181d0420505042c2034951070301c5401012000c2c0200003101d90021030980380c0c0c030b107203000031680615499118418018050030843c0c43c421003500c0449102c0010f041da14101990500035070f00682040c0301103000c50140b110f50f9000c400e20f010b00303500002c410310002d00c183c890000182910000010554190701e405214030105a130114100261001082030900007c046040d124000342401090000e00d46001540c40c000c0d544180e625000c0e8142c03140c203011020039444e01c5290540c0c1c04010b03400003000040c17041d000700060b104c0c4500a1700f0000304821540602808003500400d140c6980c150781d0b504401400500743c00455200704504074000031421b00f8000c41016105208114454505002c5555600d041c502042c60415444002ca00d0440c0d0042c03140140c1444602c2055581c0d010b1104080c014a00e6031240640e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 105401933 1250 105400683 105400693
    0x6030213201201320108091e010504020906030115150c0804170c03070605040b0319090c0e070305480417071505030c040b03010303080403080a05160302071104020417 73
    0x10900e07000d160400078042a41d5400d044d14804100464160781c00904410440c4221014610190484c011106402c0c0d040f100206403481e240c41070000301140580b24900a0381040741c441c4180c10f00d04402410748c1c0050148030718001008100303e55480c000703040a80031000002d80071070030061802d880f600440000c0c044460240d224014142d8407081c038803075040000d070300f80028041040004d000b1900b013000b001c0800011151101c50008949e041d200854007540c110b80100860084d200d5040e900600301c0c201080b9a1900282109221181901082d147c41c50b245086140d00000d1030b605801d04400305400b8000c801c980c2c503e48403580b0500401d2255464088040c039200c44c0011a0020380d050b2034802c017a404c0c00a00d00b501d640d0000307801e070702ea00a1706102c00b107071440780000518021400303659490b049080c18100076082a001500440446040604000c01c0c203030055003a8546041030314005a0300c0312141442814060030008090b030082c0001000155660015000201440c40300f00303840c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 105403183 1250 105401933 105401969
    0x31f120c03031e081504060b0d020c060f01080601060305181c0e06190e0604030516030303140702070b0a02012301060201050c0a020a080904061206090b090106030213201201 76
    0x30081d0a0030105030300000c04c8840003640a10001440038202d050260000c00c1c01c40d00c5124400041d0468250665034076801704003408003610402103036400c0345a26540715002d5041003116904c48005015207024540c540001c902c400e00b2004011500001c0c51081d40c100d03c0a0401d40054944030304c0c2c0e201d000601d40d1004c607003d440c0c0700040307038020070174040501e1611008107825542c0804000d00706901440901000000c920203000d481e149400c1003820000c0e0500310f1501508031480f0911000103009410100000607400080e00d13800e440084030740d40c0e01c0781c443e418100e0140000c00070042541c890100b54280c0581d10011103416110660000e000b15610100309105a02031000341e03070016403000711403401080308500100080720002c1c00114000ea04c40740c02400c2200b08070380844002d82e58000c980184220802410303040703071392a00280842c03465500011108100c20808107103840c1d41d0314100711b0250441d0306aa020310504150140c842140d5000c80716928000d1080d00c641c080713420703052 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 105404433 1250 105403183 105403217
    0x6090825031a0708071b0f05031b01020c0d09060e0415050a0303200102070302070b13090c050a020c01051305060310030506041b060f17090c150408010609020a05031f120c0303 77
    0x413440721080d9500c00c00643d00b0707142d001c41041f450b9010358243c0001c0121081c842c00900004018a1040d0005079039801170f609803c0c40c00c0005410a001c109851303409010150b4841c0da8400c8285c0c00311004151a02c808400d25a2031400da403025620002e20040001090b42254148410107256074802c00d40c6c0e03240703007046e80c20f030311070a400100143c00079041444800c0e2201c0142c64610f8544801e03001312500c4021040807291107000c60004208045084080f5590410169801c030100f843d000e070805008025044ca0350a66000d0644608004400a2401d0607001d24000c01160000101c42d01c50405017441450b01140c01d0f1240500c200c0c0d010045025801f800c6000380c01000d50b928480e40315001001041c00c030b00c0c0030300304403214010245103030031568801132001b410f021031404590b80c40f4600403425023125010380c070030380219005109a040841c0c2004c281e82d80000c200d00f5039103410f91072070004042d041d010b8020280c0d04030080452024000c228a03a081a01d1098544210b400300102003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 105405683 1250 105404433 105404447
    0xb0a1401030b1504060f05090301020301090b030d02070303021b120111071403070b04060b0d0c0e07030c090e010302010f021614130504051002220806040b0106090825031a070807 78
    0x1822280f4102000b040141314030456903541d02c00d040380b03080e03400c12460f01c001900707a0380203a224070325068481c0c26440d4149028002c5084e01846400108030709440d40d54083d4075000401c884440000014268008a4640910040c1c0d403a600800800c011400c20030b41d04500c1e0403611096448050075001003028810000403100c085400a0301a40150394a0359440e000d401c06541a50700020403048980024403040e0000c0007034000410603034003e241100700202241e1a450b400c100300b1135040420003840100000c0030741540d8083c600701c000e002c500744051346855443e407011000301049640c0080c02d00600005044007550858141d40b42c0041141c054059400c00e40e0003a09641080d030091250b01c026500801c80d0b20011807065040b10151803103050600d6540d403180110340c00a10422040003070401055002d020780d81403d55002d810300105a03510000095a20242c03101a0810842d01d1200782c02031000307681c410202c0c01e2015603c0c000025400341522040c010a440c400490044c07402908 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 105406933 1250 105405683 105405709
    0xc151104030204060e09121c050c090d0606091802090103110a03051507140a080720010c020c04050901180b070e04020f09040501210807060902060c0a120509010504090e010b0a1401030b 81
    0x3d012303001d210244258100030b003030190004030056001c11924006449811140307001d21300524001519600d03100c116419519007442c00c0d030414650f40d800000681c1e03042034450540e0f4000300c0c08625140f0500c0821918143ca8001410501c201040000116024a4558811781240c3e41d0f2480707038148440b402c079541c001c4918400c00704c1d020700300103003806100302e125030900903038009208902d8204603402c50843d130820010900607000b450080c013503428580600c54005480320020820389440b034100301d10320459940002c1680340c880001c100c0c0c0c1c5114030708540e07404400400442d510010781d040d0704450303030100d14020b009038101030000803a4625249541c490b0004007142203250702ca10307910000c10364440344046402690320b100c490f000d62600d83c06404500340060041074501024103240f40720300c8400c225041005005c1082815a9a000d400d40d8221145040042051400c6925050140100d42c00198100780118400202211440444400c1460a80742001a101c80d1014412400c800754 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 105408183 1250 105406933 105406957
    0x80724140306010909020a0903030806090103020102030901080405030705010501170610150f030f05100f0e090a030809010902090901021e070203120307051303210c151104030204060e0912 82
    0x150305203000c4a114004542c4a40305240020080307849080a5080360000d41030480000c0c503500c1d05200301a0800404c41e04240c04a0721004590f242d42d000035600c1c400e044038541005000b00c04541040703020815160a250f0220090010f580c5440c90303440141c10b03d07041d62146101c2d0801040130f0f0b08c103040482c0c0c01c0c0c2c0c10032013442c07100540014003034030014602d014240405541d0700142520701158491140a030600c3c42c1095070151074822801441c8115411000007100c0c100184143c02c900040c0c04580198107080c0b80036544c0d282d1f05800c1c010542080042d410a24607400c00007610810740c02030201c842400402141c0c81d22820080220f80a20b01000b901036000816070340a04034820080d5902040704d01c0d020307140040d64521615006103d600c11502c011801c1c4a2000055a10900b0100c200e682d03d00b854240b112921001808000c40500c5290b0030b64540702003003105800003c0358003850300a407061010300d41ea4122402110411610180d960048031480f035035041201e4215900d0030010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 105409433 1250 105408183 105408197
    0x3030a05040b06060a080c1c110702040b10020d0c1a0403020c0406080a0f15110703030606261503010f0e060103120801030503030c03090705041802041d0703080f0d06080724 76
    0x181170001c0c8154060203208881134039074400d01c00480068040c4c1c14003555000804ad85805c0c0038414003040d110b2142030144134244c01c51701612015800039010700c15207507a1420084984040c10704840702e00d49a001d00501480c0c1c00704000600d500080d0711032550704151001c004903551406c0c01521104c403240000e206a502c2d201080200b10021100d1500c9818064000b54921802410000e582e112074411000310340c540b0760420001d500051701e040841460580103c80003904032001200300301c010590184400985a0f03094030340c400354043c00c00e4500703a41080104296151400740c0d07501091104442c4c40009601d02e05049100381c0f200c2e07040700c3e8064020350a517166000c5120141d003004250040c18401c0760790009050307655019403004422110703405a1420400c0c01400243d0341d64200d84078012030000030114820b200004c0c188100da811058aa85138032040744010b050b4410310101d203040301d04020002c5005030012559404071181a0307804010003404445812807820b1500d0100c010a4076 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 105410683 1250 105409433 105409441
    0x18070909051509040515160804020112060b180405010b0a0206220203030d0501061d0a0510050405270123040903050702030a05031c060b0a0c0c030503030a05040b06060a08 75
    0x560401500b00241c51103803200320385444080365181200700e41c15209540041d02c02080c5141080c150340d00440d1604000b007010303c40707201c00b60a420b4043c02c000c1c1003101010110070300c0c00071907100f040034000600e140c41d81c032818007840310000740111090034851440c150000031002c1402d0100e40d4046650780280c0311540c0e0f9a0340b04182c9070103000320000e10074005104903005940a1005240700da04d04600000c00f5418014000d066550034901c1c6014400d00414040e469940c540040d011280215002c0010001e03034203080b101c60145a00c03194115207040d01030040300b880d441c00c406d0302540f0242c1070342581c2c0c0d035008040811000410040f484030207161b82c809003411719400003080c040c0203040861600c4020b42c046881c11107502e50540d0503400205242a07402a0f1041040103444000e03002d00005042c4003811a0603c107c401d40401e01002c1e444040c200030564440000458200017603c1d100e103401a9410054031080b90202c500d4000c0750b0011700545080001e803404144a40c0d681045691 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 105411933 1250 105410683 105410699
    0x2010804020303040f03150c02150c1c0516020c011409040c090803070f05010b0d02060f1e0f03010518090c100e0604031a090303011a070606050603040f02180709 71
    0x4000d001a03806000800c804103465000662030ba00031031058907500341164141c6a40c10445002d070b0b803001c0864101010380b88144200d80480b40c0c21694080c659542c0303482c0075031801601030f00c621000d40c01c00d0505d4200009009541000c1900c1071442d0240c0b0b0010803040c004680070400040c1d01d170502e8074240000c3e22141070a80c000035664445007170114219454a00944c5950059401110981800c840043c00c0010a014034041c00030142c841d038903561482d17400208503009960b07c0c003080f5000480d45842e030000d1488055001a401480c0907621000c81c034848065600034000e2601401d0880c60f60b8580502c5071002500c54646a0003800e58a1000420400151107a00c401410400001242070865440900400c029071160383c803101081c14595111140550050603012140c006200402126440040004403c01c48402c0f0036954111442c3c0500140300a421180d0010310100400003080107401340b002d0310700c0c02103505120806810f808888410030849244c0d001604070201084050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 105413183 1250 105411933 105411947
    0x301090f1512020a05030303070203070305070f170d060501050315010e03010b0603090a020a050f0306220c06030506040b030d1407020a03060c0503010e0c070c150c0b09010507030e070807030201 85
    0x10840e100c007003a02028081d4100455503242c0100c0d0446005a150104603e48014402c000300300580c042d5080d40340c004006916401050303401390500c90009446d40c10401d2600e81c0408081d801842103100d4506ca0803100d585810240114a640340f412001141960140d400d591040141c1514844419035130001100c0c440d040151941d015901c1d20b0613041580d86500207035108038401c1000b00329500f15801000201c0c09598070a0f4011200003075049c00c1920086100d5a0042c040c041034008045282030f0503042024850b400b500d00480d8039404900c080e4103400c600d00400301100d00b030101045803005c00d40c8600d45204410007007000e000489500c0110f00002d000d08900041a0b441b00d135540341c65500c15100c0491384c5000083c2c00000610022800403030030358008003174040480c2890041d0744d40b9081d850b0b0303901800c00c103000003244164030140314103d00035000340e116001c026142412449940a0502620900082030400d0711240010400040c035000b15042e1800a105d03252958006480c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 105414433 1250 105413183 105413201
    0x71d030a0210050d0c0e030106050613260307050703030306080c010c0b06010513080c21070b070807050f0604030f03091e0501180f0b060603041a0c0d0c02031c060b030109 75
    0x201c030f0180615910881144942d010800742d58684800e040c10800402d07007128195000288500300501c0706040c2c448050000c0b00503030305414034074565104006411024084004400080c62100090580400102140840450b4426113081c0020790700c42440719256000d18a0031400180700c9200d00b070200754400c0c601c6400007011304002d460004810817000d43e200580e00035400c980c0c0310041c0d400003401c0c41c50750305000f00504c00e00b07507141c40825417415803030710080e00c907805441001241d80e006000d460030480f042583e00004450007080144412520381d501106c041e0007280714041070b819014081c0c040c40308040d600c141c1030605c04200d081c41030624508403a00766225980d481600071100030503051001228064200342d50700100b6464444024003004000380c0c06048103000b4080000c1c40060401c41c603042035080e40c400c2d55101462a80c00d4092081c80740d120b14100359280348850340110080000c070b484030100e5510310007284000c0050724000e1040800c0208200300411160211b94005001c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 105415683 1250 105414433 105414437
    0x50c0109060e04050402010e13090516050102030a120b060304060b0a06030b012307120206010e0106020a08071e0c0605041d040b01051002010603050304090e0f0706020304260304080303071d030a0210 87
    0x24448c06400480d062902e19600000220b550750800380a000013003208482480181c6140d007106820400000c0d100d014100e1490709104441160198450840d040100468809440c032526480c050811030040c1042c400445e0007002128000700d442417180c0240d160032841a102c541001c07020701d02043c1080341e0000720100002d0144100400100580c03042e00e000c2c21294028003240d41050008640074006a10960039035000d1100800051495800d032901141c000500c5080c0c0e102c91060b080394619040c50003071021010080110304070380c128010300f056400c01060030f41928400402840d00310004e81d0060420010403004102c03e1802d00200e00380d541140c400800d01c1d0759a40d40e6107203140c0003504800758203925940307441e144241c10896060800e03603410080c441503140c040d000c3d4a0b0f21840c01035040c00041070420390070000c80d41c2000c0700b08103d03500880b41d44541c2e5a0038546c580c1c0094900c40e00050040403408110034211013049030b000802805003480003000d50810240c1085000c403102 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 105416933 1250 105415683 105415697
    0x109110607050712031e080105030d0503071e03051911160f0b280c0e090912030112021c170a1209030206010321120b06040b07030903050c0109060e0405040201 70
    0x41c0204c0f07070109504518400d4580d10a078001641115000d4420310f0440410005034000401842d0b50024000010095604005035283c9810b80c08a0b0740034031a284e04a4810000070340c81c405550705510030f900c01c8031924204040b0f5216400c00700e045e00c90066811f00c00744014084101d6221000181060881c03042180c86d010b00b8060341c1d25030600340d0407550030691004401d01000320110900304030380c41301c00ca44000c02200d207240d840508a0001b00403480d00840c24080003500e03d40040045c03910030020b101d500d644075a9580b1008201c010a41401c030b0040b840d0318005800e00f42c442c10700800c259805030000010002d9468001281d801c441064010060f840c001c48800039064170512420500a40c0501403e43c11410a1983d03c0307a510200c017000c81c2d54410031201c055100c1c41081c402401d14001042031102603001031030b10301907600441ea40304000078080342003507005400303001140e104400355140400500c0c010750382e500d2644120b1011509074182d2078010b140c286d001e26070007441414409 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 105418183 1250 105416933 105416939
    0x6120203031210030b01030809130c02190206040801060306050a060b04060f0c03050904050103030806030609030301060f050915040b030411060304080403020402070203070801020a020f06010510021f0b0d0809040b0301091106070507 101
    0x8101d0305c1d800e0340700382e400700f5000079543c0305414210740c05104002d10800170b001551030802c00070f5407020781690361122074102030280411540c404080300c00928072000240842d40d03ca09200000b008203079240c5410900c2c1440000d626188482541c0849140b52140c00c1a101c012105845112603540101c2c200a0200443c403001c7d0f450f441182c2c040c0d4040d80d40c110ba00d19140060600d810000740c5034132110b9009000400840340d200e203012039402840d291981d00c4100000101e404010742c181c28001d030728004640440c400c400803024501c5240101850294844480144800e0b03200c02d44010305140c104000500141c01c007900180041440907040b529010f61301c0e04c1d01422030b0028070f5240016003001b04c1954990408110190140030121740051245141e900f000c4e41e01c902198402d181c0f08540c2c00d8403110118603901c05000d40c40c002d450400904440e140185181c2d100e100303a6841140341132904903050605114404407654080d01a907103100f009410000c031904078440456040c41510004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 105419433 1250 105418183 105418193
    0x1202011e0606020d0c11010e270712020c072102040606080601091403060106031e090308100e1311031002040905010e010509070c110f0907120612020303121003 70
    0x180c8a04003442034001801e07801c0400080c01c2062041e8031600700031551418a02142c000c6603e480000390908007600d0802341440842c4054070b00d607030b80315550200c030740740446c0d500d44860300c01e4400c151031f40e112180783c40081e050400328061070308158419800304009110a9004444c001100f01701a00340e9544e070b556a80c00141501d250b84c00031030018202c00c00340206541c07c6a034031005040c148698099490244000c43da5590051140800b01511000002d501d6110001041b540014006c0180300346034503810090a1b51100b0b5030000c2c41008030031000194402d041903040e0250b010900c284044802030744407040791140400a141d4540a0071041c0e00c18410544014001040b28007004030702d961401d40b03c0040968144d1240c0e000301585400c002000343c0c0700c800d40b40c00d503a00c940300c80c0d120045030011840ea040410345898200041100340f0942c0c0e60807000780c101010a03240c0c140130700354071400b10b00c15004a442000750981d0040c0442d03040d8052480d5810b40c03010412081c003070225a207440e4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 105420683 1250 105419433 105419471
    0x30909020c0d02010b0d050c0d02010c0c08031207030c08040f03031104170111090604181503061406030708030a140c030307050408060c070c0b0703031118040e06070507120201 77
    0x40e20580c0c01107070022002c1da02070040240780c14080311580d1420609031903280c0c5664111400510400101211f8011a070181200c001d071301d42c2100466803070726203440505a803907214199070301c50741175500700040502d40702c0e0045050264a0380d83e10f8056803030316030300c5452041c0002e6089051503121241e0300e00c42c142060280c00182084900c91026104c00540706007190484161240d84500c00c01520600743c5031501100c04881e041d80381040c15055000c2801c00a01d081034034007045902c40f800000501440d9048510081c02250b00d00c05291240c00c2056030b96012886285a141c109110700010302d809a0303c11881c1025003280744e4135200d601410756003964400c03940040440c1000c107042c02000c404000172507100d0300401c0a07078134011184d140e1001070091403140030721019001400d1810980300b6044080301200c2004407a032a414008003c078007224800e280a4040c034a44812020b025030001030480c010039241d1500741c40c181c3c40f922866400c48000c8042d605540d03d41000ea0940464030344 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 105421933 1250 105420683 105420697
    0xc020d0503032a132c0109050a0e01061a0901030204030b0f0103031101021e0d020909010f0503190f060c180b120c090109180603170a0f020303100302040903090902 72
    0x1000412284482c40e40c41000f404420700c1030700d5641c24040300440c0c504c000c62400036241c20203805a890010040c00c3d05009600d410429480f41e00000001603a003065002180900c03c4201d007400329500700740c40107003207416a100740300721112103448aa0000520744010071240206160141c501501d82d1541d901344003096581d841d4ac100507074010000e259000c040301c020916907800a61810903e103e40450b885000b5031400d01010001444440e807503160b41c110b1b24294805011301145680d0b039200e0300098075180c0f04142c000c0c080c4c51a29110368201207929500e00e80d01c901071075486201520f45100401c41c0580007014440140440d095450a40251000520600d0f170300702d036520321072a0400d074106000361501c0c061107424002c00c0386981c0c014503c2004d83c0c0d502c200b9061300300c05144080000c0c01c1ca030b5001405e00469000001184142c0c0d00003044210140d8a564085003a00e0004903980e01c4111050500720f0021002400140b600350000e0748124040e19141a0080d16038462504036440f42e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 105423183 1250 105421933 105421951
    0x50304030501050f070e0906040219030c03060503010c0c0602031302030604060f0b0409080d0e1f0f0608030703140d060b030f06030d0816030b150f0705060112020d030c020d050303 79
    0x468104200502401102d0344181008100d03061802c1c40200542141e10350303030349980324034070381c00c00a00d060700c4660590b48101141a014207170002200400390092255203031910000c0d0400c400800d03141814000c0d50a98041d03581c40721540c40c000e484440003504007411051640724120680d50140e80c0800c14140241d009060020340424800410400c80350020000c9000f10b09103900e0f00c020404180a032042003e82010214808910029240c08d01a2610b42c5400e0ba100d03841c541280d41060350301c60582e20055180c200710035a15034088681d43e000321603006000a5804150b2820001a18090400c5842c46100440c40300e8a429079418607400c1226642c40030300705241000414030741004404001005d5041860341400c000c9800510038a034242440181130702c40100c00c10326201c0000342c6a52032100103d0340d448040750034011883e91301404059079144959000400d601d1040341160325070950081074a0010600d56405030386010714150180d90080310900ca03003002c14810710085100384246 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 105424433 1250 105423183 105423187
    0xc0e060d1b020714030105010b1204050703061107020909030c03040b0c0a02041e0b010e09180703022701271a0409061b02030310030209060a170706030b1002120a0507050105040503 79
    0xc0300c2c00169000b084c0c54900d2003603050900420110140703104440031a80344411411a0790f41d41e05025280c80d040350310082c2401d00e00b913008502d600d40140507101241c4200c031840c809440e8582e61568a00980109070525001000f003002030164400040c689003088009070b502040751500020704a44500d001d070382d0707010541904404048400d00c1400c110440909000d801c455845001c2501054020700180100d00001c1d0285140030080015800455004080078030440812000402c0b15441700c040c01c2837811040000728100c681e086410032807020580c1c01c000e00c414804014800b82c4030f100142ea100c2c00e0346400303014140e10349004001c20b943c0512004115011044540c0080340140c0610030115003050003807201c40ca0b030810321a4112601111071003940d803144000100212a261700c4080c100c0e003040780080032070728080b03043c100b1078a40f0b44007042604104014014014919025240181c00c04904050241a08400390401f00400d1600504029441c0e8805007150021b072003d030340d15480 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 105425683 1250 105424433 105424439
    0x31205090a020f1903060f0f0608010b09100b0f0d060b0307030b01080604060b0d0506011e08070f0e0102100c030204081f2a0c170d1a01030c0e060d1b0207 68
    0xc200f081c0a44405984002100d603844c616441d07215050b00004241d162114800864000b854200074044460340508100456a0351000c9000301040b450803030044180e000045c0b050800c2420b034004443c00f5803019807404030351003110201c5030300c41070050441d50f55803040416030401280c0034510071195500c0001d48214440005412000300078111171140e8200241806802064810b484500340c1100c2e0215080d182c900c01a90301030302048003c045000202d4143c0315156200c943c443c0034900307035110308410b0071191004a40c1000c6a00d0503034051b0740446001c2c20700c01c2191348403000d005010300e00142010b80742c7c00c0560a00441407423942e01f02691848490508445224084a80019868040044028000122602200100200501c0003010020082c810100c1007204c4441c84403400554030b00c141e01108000349000d80b0403074003c01c0040c2500301194000c4c40b4814548043c0e481d1a00310f907106004100c6164081d5003405125a25008502914009135410400841c210b8000e4424542 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 105426933 1250 105425683 105425689
    0x601051614121e0d0e12030a050c0a08070c0201021e0f0105090d0e010c05070f030803090d080f130c0e0f1602070b030403030b0d0b1005010e010216060804031205090a02 74
    0x20501d0b05082d201040124101c40290702e07101d9200c2d54500500c0d251500d03195400b00c0c004000f1000a0301c4180642c03070002d800b07500ca4200851041504000400094880c0b0407403c0603806800d000801260041000c203811a0041c600c0402c5603105204440030b03900300500e11514246111410b01c0300b03500400d06a0041603003806099801102d90008042906100000074040b124a0740e1480c18001058181e83c20b0081c18052a4050504291340c0e88020f60380340341c2145164401c481801060003125445001103101e541040d0041d552000a000e0310348134480700250040550104444001d800c4600154031a003030704c001c034454640d901d01c1d6005460404851001d03400252181021900a10002d2000d0b00804c2e060340c2d0055094640003607008c1c2d094000c41c1800c440c0b01000341041c01500100001070518103801c0e8207650007a41c1e1411101415401641c0d0f0700c420013010715050150703010038480b4910407860554028000d2409560301c10030306010008940c01075035102901e8001303480c04c00540c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 105428183 1250 105426933 105426943
    0x2150c07090f0e010b0f10110f10050708070c0b070306030b0406060e250806061b07030201031a061204050a021905010806060c19080c0118150618050601051614 70
    0x449610001d004080004000460406c400c0041c24450b034070242842d1461481910114840320f070803000c403030304085103240c010f80d41ca41c10840300b004203003010002045648205841c07405102c2c0c640b00d410303c01040e591040841c14005018000705540c03103000201180c0c460300d0300b501890060800003000c1e800e00308080c40b84200203000308402d040c4401c10721401810045250340c40c03c0213140280e003a0311800700084d100d1140c2c0b280301000258411003592003520102e004030889200341c07400c21110850303510312084585d20f5100e40d5405441401094a01c101441c0080d60242c0b044082d0f0b40101041d6000403118024654500c0489000c08400d2085582024903250880c0b81240d4450416241d1500181d68034000304403001e6514034080041c00300641b24066907010310004000b401000c0001245030b81d9044445c2003030701c0080f1010607400b1070001e14071640d029200b0080c00940c1e0004c0102c80c8001908000d05178070704204080003501c14040b2000107010050380303d00810303440300928400051400e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 105429433 1250 105428183 105428201
    0x52b0c0903050f1c11010603080706021801030c05040e0402130203010b04090c03152d150315030206120414031303020118051c080f0301060203090a08010c02030702150c07090f 77
    0x103a10041005560070f4605402004056017482c100100a0f25651054090b004c160300080c1815008654101004516000341400310340c055812402c034154180111300b0f44241c3c600380000300303000f00f0050201d41c90000030150f0180c00508000d00e80b00740c200f13030a012641f00742c0c40110329050104050140b07008901511000103200e140030b1242034421140c01c0d1401205103d030300301d054200c202d41c2c035400c14900510500f51070303001148204184e85d0f810340c01c0036040e8001d00300006468030a042d401e10307502860040c1600d4010b0f10712410100c04a03004241c50401410a58038048810380d00514000304000516800040309044000ea07403940c80050146c5444210600640c2c081883c10f115548901e2a8078141400300b18451014406c1c2d804c0600c880d00c90034215007101d2900100125039580c001004098810b400d64003144000e070345e000f00b942221400b82a48005030010000b200141c942840d407058a501508402850074030303801c0d0750070324080099100144080d1610440e2100c1d9056200e0000c04c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 105430683 1250 105429433 105429463
    0x30c08030717072102030301060207050910260109030c0303060905040b0406020901110a050a03020d090b040501140903010f0b0f0a0608010e0907030c0308031603060501052b0c090305 80
    0x2810381035502c07002c000d00703031000721040b07070b8004640e5005000e80000300820b10a004114000000c4c40140000d403607030304c24016840076101e41100000c1d2400c4c140203842c0300349003400034000c1442c181900b08800360b0101201c03800740301029070904e0050744280310f000f18880c400d40f240f104a10840c68054161382c0f1a034803a0128504d40400c12006c9001c920b90700364030a0788000010b030340c0d8041e08010389419070080503c1840788900c02140041000001e014010746029400710b5100c0b000e814421215003885020ba41200e0a040c8020800703940246101d40b064540d07002558140714100006ca400c481e000d24940407440e881303c04101c19030401c0034040c01a41415241a18401e05141c805401c00c0e82c18803d550b41c104014000079180101400900050742d030118140096a540f4200150560030595015030070045d071004060199001c0e11454007210070684032103091108601004409500c109011042104d9074040340b00344001ea4420900440e00b036403200510207056041c414945a400380c5031a003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 105431933 1250 105430683 105430687
    0xc0a03021507020a060509010f021c1404020604140f10080a06080c0307120606091d010b0603041a060a0b03010f0f0b040501050714010204121202010f0507090501030e070b070606030c0803 82
    0x1c2c1c00f80c0c00f0034000d0010350050000310b07480d112000c5050051242d41804182e040c40455000c2900d6040001d03402600300c480701c14803d003001c0050b212500041030704c1c0258089404c00007001181111014900009402003003a0305480228001c141e42c0e10420076900300160750403040124500c194480c0401404142c4020191564110b003c40d81e1140c80303000700300e42205029071400030040c458001d0005030145030820b1018108581405229401c00e685a58a650a06613102d025040c00416607100740e80086418820415000c01101070307010240030b0716041605100e0124200e1542c000070f41c02842e851150007680c6162031a1b82c614000c00c2c1e0002c084884040008200c5aa442026180c0703c3d038120007001003503039640c0d80c00c81c02441070f40e10070545030004603044014461181c1c0c0c05000b00c485a002070121990990b040002c58408032598004100802814040781d44240d019106818010301214a4540c89002d0100c4c01c4c0c2140c07800701c60160f1101d505004000202e15440014601a00214 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 105433183 1250 105431933 105431941
    0x902071a07022a060c03070803060a060e0a0b0a03020c0a0b19060312030b010507051204061b02090403080a150b09010f090e01290a0e0f01020307030e040c020703080c0a030215 77
    0x1465034460b140d483d401d80d0307005a079003110303600d400481c0c3e106000d28085035070b11502440c04050310b8104a820510440c1c0910002410038024174030209901002042003643e41d007800c52048050304025510420161300344810f013609001001143c62090040709800c1683c604124884951408902682c10301c1d400d1100c108005200e80403000003d040d03034100402d4402d55140101c0b110301540501410034862004c118646c00c5c81d00e40100184c950640e50940106440150606412100c40c0020f4210061400040204c8d104040160300701c0c0c2840d4010450100000904e00185090f030001805804002048812980c018214074008811401c20500c4680780c0100d802c040541403180b4802294450512824542076461803101c41da0840d080c80d4139400c02e4000141501d404007007140c01100001d019291540c000419a4015036150340d800c10030320814401c0c00094240f5a5803030095105002001c00000c030320718064192000203c0003000e0600c3d1609000b4900009054030001da004904280 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 105434433 1250 105433183 105433213
    0x1104090c15050f0a03060501020709090f110a0515040e0f060306070e0301090b0a0507020c030c0f120a050715181802030403020f07060504050f0303040501080103020d0501060902071a0702 82
    0x80c0c08460707001d0140c8200324604541039501d0310600d04034109a8030005515020b007a05903001c0e000341d600a030b089441c8d0580790121402218021600a802000c0c218034001c0040c074107401c98991a5800b5283c0c0c0340d102e80c0d07240440d0583e2006a1003030951900440d00f885840403000c0c08990182846030950640d092000102e6100d48020746808204000800d04a202d51025007168401d26030049884149260144114004040c2a1100320040c001d009020344030b803400042e07640507480c1c02002c600302c034281e181c1048a441030712341800350079008034003e00e030200c1c2c01402071100815400c10a0030040500c900010f01c4039080400f010002c00f4050b40038480c8100140c1410100a05a400141c0c0e9440ea400c007649003100c42c0e0b220031907174410480041080360740403018108a0b07000f901c0721000f80c1e2190040544034003807801194002021540100701502c0c0903511480c9480c010b100005000c1c2e180c0d8000c9007668407259041e9507010340e41254120040075040420307884140c0c2d1000c0c043d20000d5282d9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 105435683 1250 105434433 105434453
    0xd0e19081b03070b040c1e140607020409060212010524070201030c0309060507050c07060e0f04180807060614010201020712050c0f1c020d020708030d11070209090604110409 76
    0x55000282071a4031840180d10810448a0079500704c06446440d00e858544042034608900690703011140d0a1081140001040304407425a40030031348162502000006201940e0041c0302c00b030f40d000e80c0340c28101011500030310003007260558140d6250080c1d0b0400c828051108140d41c68001185500b001d030307030881001c02c015941c0440e4240380204003841c0c20402180508034030b11025100600e004148041b86801c0300040c030303d00c0440010340d00615510788017914418815110960003c0b10a100c4400514045e44400400c250000c10588501000e0701c2e524101d03005880c0842c0d4550361002c09018605602d0590b422659007440254941440e6039903500030303c0482e401480038420003080803045604c0c20f110038501c00c5003142c101c0711907920229503200c402c0490340b02d17140903014211500c5000344c0301040640c29110400025480c0414225010f001030a464542a00e50f810030310a1400590705c2d00c810600a400c14401050103003400e0500070014401c0d02c00d00c3d40318601d0803003150002007200407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 105436933 1250 105435683 105435697
    0x50a030908041502010506030609010921050418051e04120809070506120402040c030c0801180b0901140306010603150e090f0f0a050c061c0b13020d0e1908 68
    0xa004910140646020400c90080e6000003e003401e10f0b062004210f03034158003491040700c0c110f0848120f40c40d0035107403030f00b00d802e07205014000d030448240324502d01d040c800715000c624849160142c6030a0b501c005940610890007a0001e08540342e9080c088080384030072640518001d01000010340d400c2c40e0340c9191a0340d9403140c1a0040c007000c10b0004000010600c1075000401e005030916a07640030b20a0b00784021b0f030341103408912451801e071064152921901c02c13024030410329120402d19900b0107800043d070800b892207074041c4c50740b21740c41c500c010f0b2030b50b140c024000d01c9214401003d42034040201414520160007400030940350901904500c00c00101b20307000c480d40c0c818001d4030354840e28402d40c00c2c405081e80381340c458820032081c08002c4c480040e442c5c0c503690050080d2034482c1140c104100c241d10a549061000703882804007420b101c48503901c070100480b40200386581b000a400e01d023000340d801c0380812044050b0f540e50204010036080c00008207807600d030b42d11340c552102c59a9031807186002d405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 105438183 1250 105436933 105436937
    0x60a17040309051207260303040f0503131403010c0f050f0a0e1806031507080402091e0a05010617010506180d0609050c010e06030405070509060d020d2303040303050a 73
    0x24010805050194501c800074000c0500a1883e5090100c4015562205440b442c03002034600003076405681e00d043d14103c00d02c034401c0c004e545551110345822000001e198801d5560b4041003014118606516901c2c80c01003d400c0c041500b80a611800c050071110202c40360014407503024600c840d542ea00c1008c4840b40990229000e441c3c0d015070b1001c480c444602d60845801c500c02d444540710103402d07161442d1140c00c0403811100724041c0e04002d0321080606542c1e8901003001100410018502001c14540c0501c44140710701c0c03060840b4000343c00d0040280c4001e0302941d9100c00510600303510413400708001c12a44c044a42035450180402ca0a1180845043c8550450030b520f0002c0e6580a040800464000741c2c01e10182004c0d06000f91661a45130800f40482c2c0c50350b41503809400c00800b0303a44207541010140a4040c64601440707808c006c001e0849600265000c14000180c1c1c50b00c42000744280136102c02e0311841e68004880380303100700c0b00c5144c80c01c0b54014082000069484000c0301d864407224 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 105439433 1250 105438183 105438227
    0x21050712020307320d020c07050a150503180307110103050114030a0602070309050d11090f06011b02010e040c0503090601050603040210030c090302040e03120c160303020705030909100f05060a 84
    0x502c411007020038500307051301a01c1400003803001d0b03584807540180c00c08550010984a44a944000704080080c4032300c500c49036281032181ca0343d101c1d40644040d40c0c1c844581b19598004101e804009030450307110f500c084070300c94480074500c0b1055925104541c05050304855010340f00c1500e01c0000c4d5107103200300c0001c21643d0002240010544108051070062401074032440e0140d01d075180c40440c80d01700c80b281e80e014400580c009034212084090b01030061406031940304d042cad0700b42d0110740c00040c40e4110a0b4140070840410300d0311500d8510520380d40d81280e945441c2c0380e040101481e410880c040e40581e1180e0002c1c014030016035034200001c040200507040c0010503081651003951410841c0c0d0000c3d5110345401d40300205080c000c801032484400381c0c007404c3d110342e82d500d021400f1402030001d01e10092000328189e00c00a030103603004040c0a40100304481c101014070340018050314044420700400c003188102040300120b8500110050326040302d003181041c000340c000a0030b881c40b03441c1c0800e4000792 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 105440683 1250 105439433 105439487
    0x603190203090a0501180303050f0601050306330405091e0f10030803010e2203050d02090109050d051f0b010806010806060904050408042102061204020121050712020307 74
    0x420280b20442d038451300030b001424820403041c0450598450940100b4185000142d4109040c401d007840742038161100750454541809000c1969940a0040100002000f00442e281000c50485074a142c9002c0e13915034407414001030001d00394001e4032070820038007041d0f1140c0030f0b04640068258071800b02c20076400c0130f03601c0640c0c3d00000b0b02d0715800079040c00d20020021420b101da071189a03108805144100505014810113100342d0301005c000030380040c40502c01915540a0368001781340382e0700e051409a0000f40c5070070001d108400070840481d220750004100d2880e141e0070a1400c40840f0481d2020032403207041900103000290014010360422450800150103a912102a511031490141c0200050310300f62400501d20303803250140300c60342280000f420f007128814035071030348010303901401241c20284025081001e40001034000c0307043c0405109018500c48003060000082a40c07140042007904090710080d0005070043d80d03101d03902d4010002c01151a800c15a403100020702c40c001240b01d041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 105441933 1250 105440683 105440701
    0xb0408030415092f0307090c2a02030105091204050904020409080307170c07030c1716080403020a140d11010201020c031303020a0f030308010e0a0213090f0b0603190203 74
    0x201e4221084100ba20b06541003041c06000d81807480e540000d0820419a0180100003100e03410030b400c40f5a078594000042848601015080035a5103061414030364032480011442c2020000303201003c02e90703c1e050b2920344042d03203000d0040b25000910080600b154008076075240025100301e0003294011543c0401203011500c441c0e01a5003115000706005c0d4903410407142c002c0c00001000351030610f4010400104060340c140000319011160306032110a4403180c2c96407450701e007001e04078010401080c18410360f40b20303a2900103608035a610a41310303980e81701d05510402900c0641a040030203a0169500003002c1901c80d0390b5401c07407003034220701911940804e580040740039200d0b2202c1c04805000c041010200120035880c928107480c421601c1500141d29103000b0006c0b8250703844080c5c00209041c00401c18100118403154001c8503c0901520340388200d1240141ca481c10ba014807405540c9a007903041d02031582c811040b800c181215054a103003441d580102d1010034510f90805a69400000324501103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 105443183 1250 105441933 105441953
    0x3050f0c09032404140303090a0b0612030703080901112b110f070303061a030f19050c0a08060d0312110d0606031b030b030718140c1b06040b04080304 66
    0x4443d00794083ca460500c25010440800251803c8480501d01c12500303003458004416248110300039801071401004a072160065010003520403a00101410301c01d4120503001e10040040601a44850780d003810841456401c41e5034403ca854104081404400f081ca0011002500c4d60442440360014040c6041e0701007004042c0b020b01203500325400605003040480d9200500325080c003a450030040c0c0c503900c15684910314003405c3c2280443c6000c00c002681092003000c96a000000b81070800708624030303924820100d480959000310b040390b0108643d55059880040907170310510548010007200903e94003e003440c9541e040705c0d50303105d4941480b4070043e49894151041040c00c40070921800740d440c2c601800a110406140181100f00802c80f26400e0082c000d01e0b0070b0f0080600101109403801c51000e290b1442880c0d40e000840d19101409030100301481d002c0e000345202080385568051003c1ea040c02d40100440346443c1d908560b04010101d10409545584103400c0107035181c0d40d9460b450700107610 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 105444433 1250 105443183 105443203
    0x1f090302012c010b031b120a0615090b0f0a09050606070f1101020105180706030c0519021509070e151503011e05040204080307120318030e030105010603050f0c0903 72
    0x4203086610840406480811500200b550080100506007010306840e20801d6040160403404448481005c2c14082c94640e405524402034503a0322089070386660607181c6a21050907400c2e5115000d000c040700d90710910300b19080c200d6503054046d040d180810b2110758544141070402e541d4030000b402c191105011a80499030150b00350080d42c0c002e00d00842000b514659a600542c0f80030000380c00500a00a030f41d94140c82c11000f40280d9103010001ca000d0702210700078404200c428850400b103242c00070000c01d290492078026010004503601c81c504544802010304090398043c00b010005200740409203504811200c0011041402c2c2e0300102e81d140301c04070954443d400d000800029a8005102505030500c80100d040c41819500c01c2048140d015500603035100340c00070000d8000160002c001d10207001000e050115500070001188000a1030142c000d03004030b4018409480c491a0a20650780980751300c1c24108060304094024804040c401809101c50300c0d00020754070030320740d010841c0c001c80b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 105445683 1250 105444433 105444461
    0x31504020a15080405190c031104090f080903060a05060a030b0c0702030304080d0909020a050405101206091a03070323121305040b030606092a1801111f09030201 71
    0x4070b80880e0000e00852040360240c881b030203000315210042c0c0080107035240483e0001c04591b800380c15a1a60103080e01107008040c0d03c43c1d80c0380c001000040d00200e400c5441400741e1030003502c030a83c0e401854104000188144c03040b5161074100002ca40d1000300342425240c0003400448560b864840c5820944030b03a0343d0180d13042c071001c00c0003d0b43c40d10020311100b10800d1942e0711940c0507a42c500010680c010b2140900200d4805e00081c0304a007061000c0104609044c903080c445407050340c1c0001e0880d442d036080600c0b800d441e0045c010182c1c05404044100c1c500c2580200051071454403119180c20040004e15240072486a2005c0c119404003c5051807080e113016940c0d48514140d20040070246500c502c50065041801c1e002d020726002c00d03d01d2080001515200d1540d0701d03201002e4075808103009400041c0e50320409240d541541e00090091180310604800c0074110540002d8050040e401c009103041e803011000d03004034040c05088203940201d1410100d650741c0319240c207a01410880000e070750 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 105446933 1250 105445683 105445709
    0x301020c010203090d02070602151f031101020c01050c060c1b1b01200c01050a05121509160e01080414060f011a0a050921070905010810020702031504020a 68
    0x111500d410b40c0150701401107041240d40000103440282c0e00d80340d0b10f10500c00541c0018403c61405400841e0302a1b215403142a03200c00c0035044074840500400030380040d101902040304403a100e507010880b6051040b0242081400c0005150400360b0703524000313016030b06e10740c40810326040d5036050a80903402c05540c00103448550000e00003400804131900c50301c90004d00341043c00000491481155202c07a1001d9000d0540c2c142c0540040d030300355100d00581c5041041c100191040803a049000c540a2100e203035040d00e14000c036000b04030710500040c000c82c202c610007040241ca41ca82164504601c10400e0074458615038030f904083c100c840c11044460128082c0c40104013090059800b21810b981c03d046c80c44240710007584048500340520560271001c21410800303601c191609140f143d00800b003440c0e01c8070410513080c24140c10000d142d0710203a80681c41d000140064102030001c00c8101d190702604504220540c0c0000c0e54a110907208a00e415444a001c02c4c00d40d1501d0503110054401081e07001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 105448183 1250 105446933 105446947
    0x102070b0405030c070504020f070201030525081501020d1713060c031b02280609080408030a1101110a030203060307170c03101107170c0a082101030206040909020f030102 75
    0xa51650300c22600f004ca5401030b443c01203036620f040c1c425215041802411141026110350043d0000d2030094080d07c82c2804051400c0a6045550025160048260b444803031070305050f41d400c0400c07181074180605541002c2d54074003030b09600052480c0102e00750a2000c0311a1980c10081d488607812031005083c240c03d1a026a0b007a1b40c05401005680d0410b20a101d0170b500002c00483c0c84140c41d600310341030300412800c012161200a41c0807142c8a0140d4030000c1c40084591f2480701c585d1155006081030380000c14010401d41d0000c1400f14000c075a4402400961b07401081c083c810b12030300440301e051650110108505440800050001d0000300c0e100b08007c003091106107a5500b103c1e940c4910920442031100603400071170083c0ca40c1c0c0c685d04420f031800e014095984200d0080e0000d20085140b405004001283c20100320f414822401070b0349071980d0301000e034003685540c0304102442c04400324040c010001a258041240d0031503501c0d400c00918030540f880003c1c00d506500324031680c10b40c0042009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 105449433 1250 105448183 105448193
    0x615140d0e010c031a0a0f1403010b030102030a0e0f0f0606041107141617060705070305220f06030506030c0111031c051602060112080304020a0e070c110102032a0102070b04 76
    0x161003c0460504414517180c02400700b110010450081805c0c0d4040c140342004400190b07860545107050040000c158400700704013107400ca81080350882d100f0303515800705014042041c0294250200d000f405003140100e4a0b00f91543c030100945103e014941d03030385040c200048502c050313607004c41e03024510016002100800303e50719503043c0c0b000038420860403000510400d4480401c0040b84805000d84425610404195141c0d0414034040d401d104080191009048044048009804c00f03082d000d090a801c200032000d41d061960020403c1c180b81006001c090750340091340c42c0c15810b092919201002c021400b850460040d54051a4025200d00c0355000c00f00c09500b040348520510760098928050420f000ca90741e00c420700c64030301458070240302180411210300003541e0050000d424885115625070803100c403403004403516070000344040025130410203010b00300e036001e881c24402141440d070b0842e9014103007140d203d1688201804601403d24901c800c1d016101025000903000703029140500701 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 105450683 1250 105449433 105449441
    0x20f0306040c0e0105060c070e0606090d03090905241002071a071401020909040807021804030f030f1104060302210405030d1107030e0607020f030609010c030615140d0e010c03 77
    0x10f0450000005001003601e003026000c0d0f038400300c80e00c07000748a03461500c080f64290b01406800203030025407c004400054171605c442c01a0706110f076550301411460040c648084540140841507502c01c100032440c58114602864942050700300c81124040c6c4000005900d0207040750310010820005040c4201c4a001010190132200c0c0210003244d440300d4030460440c201c4c1718509890703903c025100045800300301c1000c058001f031840581200039682402c030410348080700841b0201c1c0050342890070f5045060b410b0184098146030754a00b4400340d00c1002c0708203560b0155004800400d036020611842c500c40942d03001188900f00b030012103050a00e800e103e81c0b81e510685c1c614442c41d0030702040d5000384502c0c40403030b034100d0380640e100f04d220f0342c042d030421020b0707807000000742c1e849076204000e2411a5018000309008042283c000241c500b0500000f4003541d2141c0e1090418010380e091f00206150041840c80134110010f00d09640c0f441c0d10191a030050024550b800d0442d1319090400c0704440d01548 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 105451933 1250 105450683 105450689
    0x60901020f011b1b05060c030a090209040b04031805010503070c03032306180f04060b120111031902070f031115040f150902010c0b06060706020706050105012a02010c020f0306040c 79
    0x600d149900320b0450100d010a0f004c80c0004003180c0c0441c1c00100e00300114000b5503000982550085500060350300081c2c001401594251a00d0920400340300c101508406003280d0384100d0407550031001d24060000c0c080b4000203041e0014030140111810825210394840c8210f03c0c2003d101c100052100c10141c00c12600440d10940181004070306507440181901146101d00202054003925640c0d0303554000103071400021585d0055424100703580d402d0000c0c09205100e0341c0060203180c40e464811000d46800032444844202c5c01d01c1000f45030080b0740701c0780901d40780b1500341c1000b0403000282040f0700e10381201c007001074070f000c0d00340400c1c4404c00c40c088444200b560301480303c4034043c0c007034000c04030200d50320700f20000d001c85d610b015410005010081c3e526030004005200c0741c1405942d488101c283e03030100504a402c50303601c000510640d07800004144c00f030441c0e003c1c0c081d0302c0d9885d044002c030002071006019041c0806c00d203540007113641d000107107020480040c081d250f003410f0500d0001c0d442040c41c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 105453183 1250 105451933 105451937
    0x3905010c08060a08060442060906030201120e0309060d0212071b0212070911130f050117100b070f1a160e030109080a050d060501050301030c05060901020f011b 70
    0x201c007080390b62500325110f8081d83c0264018040c581c49603601c0c0902d01e17481d01c4000381040c00148410103202d880c0c0d25500109510000c010840700d4090301480c08455503038002a006525000301440036036800070300039030002580140020030618800809203035000f80442168800f0000030480c43d400c0b40394001d00455140a40d880440b80c4031b00400351002d14140b121501e403a090a04640054940408002d01011100040d245c5040d100d018580544d034580041088030100007075600c0406070f0301e9541600401c00392424000c01403c0800003880c00450400c0742c4803000e4480080703541031480510b06802440783c00b09565840982c0d16000389940307110711040c0c910000340042c10148494000c50385118545140310042040c000036429220590483c00c0980c06658410710b05000600410040a0300101511080c3c1c6403100f404986007613422580217141003180c18001040080c020243d0042a079004881060b103a00b4041c00403490189140c0195075550709000075118480c150781084142c0c4000e039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 105454433 1250 105453183 105453197
    0x11040b1e0406020a030e100c021e04050106020c150c19080c030406030501180902010509060d060b030103140f0d0512041104060e09010f1104060f02070b030403050a0e03010b013905010c 81
    0x4220401f8808241d42020450b4290082c00520b01042e00b00b014460b0301c080b205894a070000070070700b180e500b6000b00c0d000d03a002e10541c03001840e0501c211004100458842072030314200014241c1c6551a0510720310a0814116461040040321403d41d1041007039081101d07180c940c7c410008000d800c00303200340d104440250130803011410039805151180c0da01a1605880c107a903000a000f215030000c120001c3c0c0c1c07607813410081898448040103500a5014808451810095041c40d509207801d0b0300c0343e200c59503c6000c4000b59150050283d5810b01803001001030b02d0b668504258861085815903964807030f2421401180c0c1c451119900c50044070110020130a425000e075074807003251507500c641c4038401f0003800100805032207001200211400d40c0706652015580b0f044076080c0f0f810070fa4040300401d102180103c1f0302c550007040e032105a08110020301802e842074001030188101e4844c02c0105051460000c4a0311802a1011a05069003080601d8000ea00d0070030900914005d40010001015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 105455683 1250 105454433 105454457
    0xb03030304050a0305031503030403050309041409060402041a03010c090303180605090904060612050f06060a0b1e130303050c010f090b0a0e010f06030f050706020111040b1e0406020a03 81
    0x100205480c8515488030041409120f55201502c16410003004400320002a0030007060b0303614140090130085105100454441d03c0c560100310954401c00400d840300c1102c24108040080009112134000b41c041c0d8000908015810a40a102513404102e940660a12007036008551f0300416807012a030096a031100044c0362450b001c10212914400c2c040002d005100d610710502e000e00365540c01900c140030000b003a0742e0720080f400c2c2000440030180d529800c54041c0d000e8024003407050560248080720b0009500d400c1481002c0300307000700080f2069650807543c040c0400a03100007107400d200d02d240c403e05200c55491900030100e900145502481d54240007202050b043d403030144504003a44080404940da85002043c0024490302d4000103503503499561100080d981803054102840c0901c0e602c82c00e088883c1401d500c1c0292543c021011a80740807001002e00c400b00d0162002c1d15940c901c0103a444154030b42d001c0c601c0c000407043c40110310740000c0028481d03400190801555109450390054418 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 105456933 1250 105455683 105455689
    0x3060406080d050702011b020a0b071a040b16020f030c1e010e030a0c050109021903030206063309030f160614072a0305060105012a03081803030a0903030b 68
    0x800e580d42c6502089040c01640f00540c01010410b0b080704107012410702c2401940c000601c0c1820030b5104070407d10001034070307009008040f004414584905602c80c4c0280c2001c0d0f07038840c0d2340040200f6000e035070703040c108800c14031030b100b800072030780501002046944882d10094115120034038401041d204034500d00c1401c0f100107041c040c4100b00340d0b180700035504040ea0030000390395080a5800c00c4034103543c0d8440c200700603a19050802c8000e0b0418107038211044c1540b80c044c2c43d101e0041e03c0c1500c501c8103c10004500c52480c05202d541020f04940c020703200381011a480301354042c500a03507038540a02210b40307506403000600003030825004504a8441585c4581c25a07519035858003a0100e11410002c071380c04107410040301000c1c0f01650303120504050400c145604c5401407600101c41e02d403c45001004030350b9020410184a4603c070955038082d08280109015243c0004401424000701400180680300c000c5281c0c1101c040d02800c5e82d650746480c19910700201a07491044002c0382c80c154000c05141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 105458183 1250 105456933 105456943
    0x507050a1a1e1012051005180d110a020907050418021308011806020a0c0501020706050402030c0d0b0708070509030f010c080a0b06040312020c060309010510090212060906060d0c0e040605060a0801091a040e030306040608 96
    0x2000d0f0b60150001c65001ccc4c09005850704002c0181d014800100000a0782001b2512061900c0c11007050041c1c9403802d0442202c500701c0c5a078480c0d0a00c0c1c2c10020341c0414616002810507002d5031003140181d0b6115211011394044d0320407003024006500c04214441800240e810261190b4800c03007d40d841c0c0848002005012009100c0c050580d10074400085c107a1401070b101280c02081034100b441c01c00b091480064030701103002101c540c0b50b94544503040001ca801404081e0030118030328007800000c1c851000b00300356010320f02c80901000c00300c0302d9104c41c1038001d10585100a002900c40c0f95a80b600220150182c40251544100008030740c500042d806003a100384c0301d49c2c111020150101d0344501e41000758611000d0b105a50000301000304250005051050b070340c01d903895845510000c0114030412045030880c5d8441c42c0681c00030024500101d52081603141524240781000501d14181c070005c0c51140080d0540303d400070726040a410b0340c220008003861203082e086400f400000e8641c0050340c0c0320 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 105459433 1250 105458183 105458207
    0x191712061807120f110a031401050a0b070803060612040807030f020607080a090203100e0f0709020909061c0f080408010e0f07060507050a1a1e1012051005180d 70
    0x2140c200f916400c2078500e030090500c0c80103070741001c41d1407800903440c00b8541d4040e070003080219603550110314a086400c074206004200880700c100c01d0303600d0000d5616080c49000c100800396500040015000d9480005a40d268101d09900549901d0f19142100d055030080d01c1c15000b1500791750f50b000c001440041c0341c612403085541c9100c026112000b00102900303207400100d030716010340c403801d40e002c4400d40300d0300d030407028004018602018035140709424140715800c14148140100000345c15515040602030300060140d40c4090b180d40411010780c0034501d02480140300381e02c0851a18203002c00000070340165040c2d9402008030541d00e000b500d980f0b94000100d44055040030070b04102481c02540503101300c6005030281c80160302141e542110b100c550300008403900c490300c1c003404074541c00800310140700704030408004c0440c00d040e560305001149500c40c20100351140488441080f00c107014000c441000c444046c070260400b9402207059101c1000200c1061144200c003c1c1407a01c42e059120b11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 105460683 1250 105459433 105459437
    0x501020405010908030304020a0b0a0e031b040c11030f130b070b01030605010b130b0c0c03070f0311060a0e0f04060801020a080105010e0414010902030403020102120910051602191712061807 83
    0xc40c40d02600c4ac4181d001400c02d001482000c600784099510300380031170b006179038150a66aa6100201080000300c90700c1c1c400b44c604002e000c080c00c504400f03000080f1000c4111885616031a034070445100c4803503480076000001102808507a00013042480880b580c10f981c42900c040c404d580e2a06000e03e50740c02040e4645000071100113041020480307181c0149103034100304050b1007400c03401c100071914240c082c1d842440345110b401820414810901d010007032443c011521185010100400105420715060801e44902010b104108555880350b00c118014004080255203034020107001500c840c109224580c003003051a10300541d030303181a2040420100840010602c0c1e6400c00300c1c0c1d1402074100030400c07010756500b008007540c50310320602407a1140a004d801031860301c2005a6000903202c3c060000740a201040300308030240b0f600030031310314004844621050355100c8a420700e1142031840d000c490400c804000340318a1000365402c40703030780b0850701502c0030b0510071003900610300c2c210b00403100000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 105461933 1250 105460683 105460699
    0x30703140a120506060405121006090e1c1e080907140105040905150402070f1209050a030311120408010b04180c06080a0f0f02090f030115092007050102040501090803030402 76
    0xc4144180d9005031303041640503010728241503ca0300400c0c0b0040c150003012003039038002c000a203084d00380f45c02424050040c524040c0801024022001c0d0755241c0644481104e8001c82c01c891402c1740f040c14650b078010364503640141032401c038900182c0070341020b030340c91506401942c0f800f25101601000c000242c0106079516031500786042c9180c4000c0401800030742403540c0380c3c030300100d483e13560b400035001c11402a80c507a54003078041d1030410304890800e0203050078445100d40030046070395080e80002c2141d426043c0751403040c888030300e2181402154503849a0744030002c45c01242c102015402000c041c0b1046d00e0400c00c0d02030003c849401d03103120000081c6185010f042c14003000d4859065241c2284240302c020440d144007407038210075202480700200035103501140344156031038070018010a2807415030003000721246158400b503003118140a012401500c80c10503140d01d0012144041040e1800c040d155210744452030064080c0d0300070302c900c03800980c0c6514040751540010003100c0c0501d50007801e4030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 105463183 1250 105461933 105461957
    0x1080705030c0a1404080c01080f060303180d1b06020f030301150c05121804060e04030207030b150405010b0a0201150b180103020c100e1c0e040513050d02030703140a 73
    0x80c0340e03035020f81c041408100c50040c2e004107415040002e0b201510020019059441200c07000500002009245105103c03900f000d0100c03036100441191580084a0116840c2c0c64140d0b01251095070b403510000d203000b400e88040e04003a40584001019502c03580c1c00c0d01d4041c04406070450f980d010070300500d0b12481030321003d00341c41800b0790b011240551085040d030320712040c0d9040100c09500440c4005030105440d4000c26090b1034507104140183c8100800c0c040c1078141520000d550f484140001814510400c003c211000150201d4100705280104180070668640182c47c0c101d070010a40e010156080c924982900014849240f0a454044010310309183c0141006110359404a03080b9050507800c000c2ca000107241800700c400003005d80d4102083c2e02020100407031801100d200012580c140084d0481c1c600c1d43c0c800c0303043e0f00c5914101e40c0032520383c0f02d80c0e00304004205a0f0342d0003091480307003000300850550044050000b05019032180700026040c40d5003000544689061200043c82042c416 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 105464433 1250 105463183 105463201
    0x60e151e01120b0a051009090624080705090303070c05030105060d051c03060b0c0a11010206010b07020d05010b040212040c05031204090c0e03060a15081203011503140a0204140108070503 82
    0x800110f00200300e201030300d030360380089a4526101e2061800207008290103003c400014010b1200400004203041000f00809458261202d11340c3c000604110160001c2003050340304038203032171030114000c0a613a510b41044c80c010f44844030300d2280c80c0c001d500700000105d0710f160988407455040d4001010b8a2001000045458007286a4402c1018503603905408034841042401900090781e80b4801062900460b0800700110701c8810040c0f41194040c00061100c0c5002c1c00139540c490394103172441c1f100340b2034a01d45507000d021140100c80e0054800b20300c1c0400030900c1d10945006078043c0c0305084148d61148145602d50081e0040c131070340c03442c080000700b04441e0694031075400c800d05072900b0450f43c542000000e0030084142d074422049a107450085011080d00030a000050225000601642815030424160303808144915040420440384042010b07010303410404040c1e80b1105142c010f071604030540f0700250004d0095502c050b140c500441d1455008114090040d011307615503a003140d940c1155 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 105465683 1250 105464433 105464441
    0x313180e071205030d0501151803080f0706060e092a06030414030c0601150f0801081b0d060908030121110402180a090c02010e060424060e151e0112 65
    0x8121544d1008100010022425204184c060000440481d1802107221402044592410618250080d400304104005411001180d081410001110340c4030201070a1180c002d100b40d520000901d8882c2080280308440842c0c020303800d140c0d400d881402c1c8980724260704580ca001010301c1c3d40002d020008a80814540c0041c00e221100e00821030b40f404c0d142d0300100381061000c0e800000030f03908000010710b809410481c7c0500866091403c0300b01c96140590440e071392580d40c005290300140c0703080c1c0080303240c031002407082d00300d9000340d018010b460552914505c039510910031000c10340410318070f100c0480d044504810b2000d40101c03540c440210780f8001c00009500100402d4002c0800164440d00d175107030190160004c00030320800082909180002038251000c02c2d10444003604424104800922103161181d8000c19003041e05004000c1001c46030000c5c2820b80027080c2d000d0040d002c0201c0c4203066480d45450b0b01c0c00b51200059400e0041c10398003208600c14506012030200700102021000c035500c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 105466933 1250 105465683 105465719
    0x5040c05120f04060f020d06091b17060301090515091b01051806090d030503060306010e04050706030915020403150c0206190f02121306060e06090109020307030e0313180e07 76
    0x135000865289105a02007240d001a840d100c245031a0b85e03081247c80c1241c0310b0000390744070010080c5420035281c04000c012840007140070710f09030107400228132141c40c00d611009a15074060300b16141142132141d003040c5840c003268004242e10a400d031a10182000381c40c252400e01040c0c4816080c40c40c080480d0035503514003503181e42c0040060204403015620003925102e524004e40796603540e030405809250504005800c00c19560801d4400c0c400005d00001e080c84c1102c0035450001403444891030008250405801c24050950010801105000c50030b48101744036561200100043c2100c2d100903a21020104c540c4484440c10000c210a1030002d504041e0007140d94020051802c1c82e03070000303428992415541071010f1883d0540e400708000f21481508040c040d42d1040c00c0c0c241c07030401d000800481050045020701a0080701140c0c000740690024004200d540c0141e031784501055004120408040c0324010140e21054a04402c001c0341d88200c00e5007034812405400301d14100503800c128464401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 105468183 1250 105466933 105466943
    0x100311010c02040e011a090606090604030b0c0d061401120c0206011701020f042904051c050a0f050303191b051c05130b010e09071401050d051005040c05120f04 70
    0x6038884d45005020701c0382c0d03c0d01c0b9a4440420f410755011a0520503c5100213021500520040280840d65079640c01074030101ca5200c01901a1a6030300c442a03403140c020648035038001c038103110021580381c0780740702c03450303a500d00070b130f079401d21512401c001441940c613039030400c10140e04200d006001aa14004400744004034000000d0f1810802c0a49080381e43d219a000090030380c0300c1892a4442c80700300c840350702d05d00400001c090505042a0004404000b030300c0c850588012042c20300d03400c00000340880d0040c0c9422554140c103082c100d00305640c0f2a8000c4502900100c000c00300c1000c80a210310441412903c000307070381820007034041004c1e26a9031000010228407030307a46038200301711119409030902c43d058540000d403c03800c8030b1070580045230040e040030560101da90200040d00c0b80000345142100e0b600a403051244147d4001031705c0c24410082d6114030981000e08100020308511094030407a4030a41e030400ca07200e448202103406002d000124a41c000511000c1006025018602500700303003e2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 105469433 1250 105468183 105468191
    0x6010c02011817070312020303011a09123f040e09011b0903020f0a0b34030201020301050307050901080304090506011e020a022d06070609080703020f06100311010c0204 74
    0xd00c141449140d140b02c3d6a12039a026160a2003007040c41c0380200d2010030320b4002503045506007800300010161202d00c4415209000c101381c10250b030f607000c0c18002507000d1019190b41ca405048810001d020114041021219500440c0d0181084c0c042c50004d4940022046007460300788410802260405000400d10b036407034448407070940b1201d0200d54040c4803d0344031081c0c002c1c83d601c10300c61310521007241d0501c5890000030401400307000d0001c950308401007814070380040c2002e20f08085503200c2401032141400c0180104410907405600641c182c680460403111000d617500704208144c1c5090046200c00d4005001c00c20030f641190700440e8001d0380504241c0c07040041003003502098000300c141040141d0011000ca825400d20100e8003144100c48088400f68170f00620407840c00610f640304482c002e0800003203400501c1080d9114400031a0b0000032a680c4010b1401c009558143c610301a041900500022800361a07202403910100caa03c0440d450501e501c000055403405103611060784c05ca515 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 105470683 1250 105469433 105469439
    0x5010c0f080d140405010f0506060304030c0c03080f0705010b04020405151b0321060306090c010507030e060301031b0e06010c0201030507020c090405030a02070506070209010504020304030c0c08010f110306010c020118 95
    0x290083c1c8503118108a24110a840e00e03041c4942500e02041c840b40c0c7d820b03d007030140403060312034004895026070942010442014149041c440c503440e1948090703c4948041541800f4200500080ca802d038000d0000384003c100c010204000c921440c4907540d40810a04d1052000c5c8050002901c80301c52078600c0d059803d090b0241150460780803101842c50b807036031038556990101e400300300c007600480103070f008182c1844c2901d2a542d4510325000603e05020300400c42c5810144a1207030510445006003c464881d607491801001619080894000441c8081000b0820301d0340e600d1000c3c03051a05940311520500141c00640040601030401002c50081c1198004aa21468a580d000d148640000c40c0d135034101420007414415280c100c58450081000b8010141e43c2d07240c0307500d05448049800583c0c1c0e442d00e2074191802549444004c0c03032052424000500d011f01035104184c0943d0849042c08500c50081c3c6081c200c0c88212160b5010808500510004d03500c0350a00103004c05001000426180d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 105471933 1250 105470683 105470707
    0x1b0d050d0201140a0b03070e19020f0703090510090506130305060907050406060203040b031f1703030402030114010e07030507020f01060e0613090b150103090c0b18030705010c0f08 79
    0x30164400142c0c0d120182c0141c0c50401d600141c0d40049030200400c8540c54100010351291501d226500340d20301a040410340c50521581d000403541501401156108800d0300c240d146900000000c0d404900e0303220000426013007051042040d0203556a41d4002c0505102c1000001d0b00070004501800c06d031050040300103041004070901611b03020b40102900e500d00170820094803070a420040071900140010004240039078140d0346c010002c2402c0660205001d0101d24207141c0030340c4210850808020314900c0c000700032000b14060360081d8000c4c04004855818140a01000c4c4200c1d07070403000003000200f01c1440f030380c81590400d0240c8150b0315001443e228203820340300503401c0074552504200900ca4203140003a0b001c1d40307100300d0101c240034000e443e440c0c03001d00301ca0050820300080307007100c4d403072885038031a50000c400142d200e845100569126800180d094000c00074040c80c0419200700300c01c05140009051048030b1050b9507400c0025180d80c2c6180c03d1060008086884a400340182c600c445 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 105473183 1250 105471933 105471943
    0x8061005310c0507050f03090d2d15060501030204030804051207030c080d0e0f06040302010815060f03150a080606190e0f070219050c10050c010c0905030c060306031b0d05 75
    0x6251a61041c0d191110350800d6400c00000c40ca0064150388100300c40065178940303100130716046400240406041b201c2d0391402b400b40292040c00c0d42078081d0f40c10fa4408103e107141e00d00b54101d4040358100105922030006604038030950101130020304051100f0042c61030107104244600c52204261081aa669078075254420703003a03002042e01d50041304025010a0780002c07011604102100c00c0f40c01003800c81d020a200b48258040039040002c40d030006202480b10402036a0002006000c2c2c43d0f0340d0300b500d0001101e90300240d50907040d015000e800c054240c07502c020100c040c2c8110002405060310b41600f08070180c61104c881e84030f8004e91030800241c101c00a0000c42c400c10303942c44180300c1d40ca401c0c0300003802d103007881280e04d00140c1c9118a241c00324100045004203203009070368407035045e0300c0408142c0383d42c041d5000d080c0040d03003860000166907601052203c02c594003581154041000d002c2040118042152125010f61000202081060340540d040c01401d10240c54420311000d6611064200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 105474433 1250 105473183 105473201
    0x7080c070609080c04020f03060f060c0a05030406030b0909070605030a090606030804080111130614070b040c05010906050705100203060a080d081b0301050f0906061306090806100531 80
    0x30034038002d42040041c200f40418600781c603046408515280c052034609082d0301010703190ba400784d208136103050f80c5a204c10045030391082590088602d1010300740350643d030385c0e03000c0c0c064500080d080011480f01ca040c40ea0b18a4081c1030200c018140301810710b072003125550002400801c01c1a11035100c1d4010800c20b118120140d0700030004035036039504000806094a04414040301500020400e100740140007480d00340c140c844902d0650a80c08040c100142540600d40018004032160310070b104c01c020208600e4000c907072003078855a41c40d0359115001d6506004007030001c2d080e5000741e401c03c0c01c0d00200f43c0c010740d400300004103203541e020b80320f15110745484414030400c00031407603010078040000c00c45560303900e8111010f210145958144004110311a50512107103002d03209041c0810600c3c0d0300c40081d00c042c811090902e1a03690f42d01c1c400249460300c03d00c220341c0c26004031008241510003002001c0280c1d0f80c082c2c62900116100f81090f081c840c4400a03806001c120024802240c001c039006510781 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 105475683 1250 105474433 105474437
    0x212040803070506070f0504060c051005010b130611030a1110140f0a0c0516061d0d1e140705030c030f0301090c030603030e04020903030d0203010b070b09150a0207080c0706 76
    0x7100881e19141c0c4c94407501600c00424482e1550000d00c0c0385900c0700031181501d40070324002d4400052460b00c589406255854241000e0034400045020624000a02090441e40107642c0c11291303200d00a44038048885d610303030f1258008115511056000c0c10400b00644686012036000c580d11420301d0f0200c40e2001e1014280c1c4400c5414401001d010b02c4080e5041004200704102140c54898040c24034450580c1090298055060000500c002c030752100500044000e20b020400085619068440c0c0800b41d80c40301040c0a500c003400004d031036207400d00b0840c055071134060b520403071901c00241c940c208400842d420303c010002181603203002e0003e00004950510705984950400c107404045e5150b09030038404040c031b00341c41080444e911002010320540d09440c01a910b10441c000b09041d481030701048070a1500006c00090070107400310003804076900980400a940d1036100d007003902c8018225092400c45071640c0071485407a46540202281803090799458588103e40d80114240042d644c80400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 105476933 1250 105475683 105475687
    0x1e0c1203040c0e01060804061d0f0d12060f03080f0f0c0a1e050d0806030a02090906010509090a0b062b030e030f010605010c110a08152505030a0c0212040803 69
    0x200700622036100090100c01400000d80d604040c802001c0d4030008002030505500c541040d5094400350002d0846189c0c07500030f84000e038220320080b0707a903020380042c16400a90301c4041203440c0359070307880f4040c01d40f00c000c44601302c41880c50711480e60580040b841280b0207101048003500f002d1401e8010b14000040c80042d00d84601107040400050b4605e880604494403181e400710006400460b0501c00354000d030411942584844001c02e1a05045c000003e41041d00c00041c061100710010707506049450407101c2104581e00d84d9a503e40350300403072100800b0041d5000100b62945001c00729070b8140100c5810240440d03507581c01c2c000c4501801c800903070102d00c0c01c2030904101e00b428040c0c0075040d8402002400810718003800200f54100059014100603540c42c22544565070751044080103212800403070700207013440c0c2800151040192256203400b40000708904000c5201c403589090f1903801e40340c00303055075140f545130300c060000c2040303100449c014155510504003101d000380c0b02501c140d038000e603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 105478183 1250 105476933 105476941
    0x2618041811090c03060306041205041a0408010507030e030706092f030d1d09040501020c070612060602010b150309120307020d0e0906150708040b0304030c1101030506061e0c1203 78
    0x1440700026100d4103e0640820802c1800e4030005004c03900b00754443c9144448a031301c1030045855028607080380c04119081ca00c1101c1e40032008002d0420345030804001c1081d521255404d40448484514000040c0c000b80420f6011502c5c903481840805d008510b00111502c51280b11000d032420b054591751248141c168584443c05c0402007980000315a080042e4071504a40884000054008800307100344103000000c0d081200039015584100d144000b02e550301c42d01e800b8090294280003202499081c0381c048005901d610500131405c400300d010307049010101c0501d43c89034490707100804007012072103903948041208081350004d5209048990162261104002c0002c0038100d16640c603a216125520a201007566203140d200c181d040403c40440d40d0307140a02e044100d80c06560b002084090700801040141604003504000a92151000c9149071218000540c200e980903540107400040c00c0c41042000080001c10388201102c11982070b0401c101d8103915031401c2d41d106100228564044148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 105479433 1250 105478183 105478189
    0x80f0c1606021509070512010906020304050a0b0703060f120516060207050a090203091504030903051b0108160c170c0102030c130e0106080c07030c1e2618041811 71
    0xf0890016400440740d890406859244c1c0e20300107406024851000641c81300301200c1d00750320034045603610450a6450f440c0c5801c00c2074585908140070340303000029000080e10b5900c241300350000da94110070410001c03814010403695425802e0412203581c8214241c550a80080340c5546005103903660040501c1404d0809001c02802581d0000300220300620600c0704000d0049012805407100c000484c4541c1e9450070225001181c40d17101500c28012074044034005500320f60100b881030020b881d082e03c1c586440d0030014802c001d240c0206e00280d4031582980010f10701a4007130315034420784160300d8185100311509908aa100f6640300440c0313000000d505100500021640c001000b04803949099585001009021040d00030a810417100f0005001d00415001e10402580e494204204020311040141322080500880c4001d07a21103581401c2807201c08010216425109404081213040806058074100311010030710019034010788400150401641c1050030b0840d00e401011401e081c1c044640c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 105480683 1250 105479433 105479443
    0x4050a0b0403090b0310050f0609060403020904020103140109090b10030203150a020d062d03080f031306020403031805120d08090304051207090e010204060903020d0c18022701080103080f0c160602 86
    0xc80d02410052004400c0be940d50340503201180d8060312038100341d54072840100d000340300107200716070302840e00000401c00c0b100c580e00958410b4070510410303106444d143c100b6007880b41ca42c84002d5040d400440b04503003210304c5542d071641103081550003500385442150540b00780c41007034002c0c003501241c01002e15810b000f945d50f283c10713180e00031804039070340360858079145428440c41021000f400700000120384240f0740c03410381081c0d40703420880440d121354480ca4010700826698403000d841d40c01004001c600c42c60320404070040300d4003001c0103000c0e1220030b900c2602c40350001080b0f804180024800021644c0317420b04448000c1c1c844c04042d000d59400c2245800c2119624030b44014140e205120902416411a08407800c2e41c2e01154072004021031890044001000c0380c00009400c890720300d500106c000140c01501c080411000b0300000c0308201d042d50303070345d1509141c14980001c1c0040010000700f541c1d14002c101c3c451a10700c4461500803c401c072140303040c0383c00280302101d10301e000f02008213aa040c01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 105481933 1250 105480683 105480709
    0x90f051b0306010b0307050f07140712150e0d0e0307050907050703080c27060d0f0203091504050a0602090a0e01031a060909100b0d0c030f02040b060304050a0b0403090b031005 77
    0x4004d50031400c00a1005000d0f0090340c6c01010b0030320380003400c1c80520500130300d4801a40d200804540905031264409003885074000401c6581c1c1c4036441c40c103030300d010b00ca003d01910241c84000a003442000713120200c5055156100d03403a014080c2c9200803c0c0c6841760366986108040340c1c0c030b41d113130380c0c9005160044c0503550052000320400c3e81400f6050310040840415074207144100e0300600c003146d0340c2000800f28814841c2e4448150b10305160701405010503006544039004500940d41902520101d004100500719401000f5401031243e500010704141c0c003501e5403000c00341140140c15240c2112000f0b10001b07810a44400400316000c05403010158030b0658020802d90340310300c160502410b4103a039404d01404d0388840b03030340303070215922107031114900c84600c95002000e00c80304a64a08011425584214080c0e0050781005000e072040e041410843e4003075a8020024001c0040329151680c4508011f401182041403104c400617640040c5405180511070328000e145a070342c0303004200190009664 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 105483183 1250 105481933 105481949
    0xb0c07170c0601030201140d0c020c130b030709020d0b0d030e0f0d050d0f030b062109060105091501020a060c0e010818100b0609040606020703050106090915090f051b030601 76
    0x701a011a031008504141100d03820700340801100c0441c2c960f8100d03030080c0208848800e25044401d100d550b40010054030030001078592004c801407100076001503803442c5449581541c00304034108040741e44c3d5070040c407010607141000190340d0300d03039400200b000500c07800c1900000d01800d080b450380d140a804407010030b5011a20003400c104540e850a0300c44024941c2141800945402002d00c3c5010b0b401c0102c2040008116a90310344541151024a10303001031144810741030840082d15290b00001c03c681a9035004100c100b032030391502000010910160700daa411402000c070780744d000914038040c07440010007503120f880740d001d514000180340348401440e5500c00300d400e004c02c0c92f07045808141e50304088450003000c0b42052410b0041200f9100f02030810390050310701400010b900362f001c1820350a4030300c200300030300c0040d9a99290070140c80380140081c09101650070140100c60301a8003910000d8422001c0e0040f515054580c10304003050b22902d00c00160191020701400c0c0780a01107280900408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 105484433 1250 105483183 105483187
    0x71212050f190f140c0a0206010e0705040b0a0504081501051e01140d0905030c06041509030f0503090c13020a0e0d0c1a12010312030e01021813090b0c0717 68
    0x5030a41003192058021540082d82d520b51843d0f403001032a41060550600d000018095801c0400460b211a4019440200140a603074008100310700b00b084603030701682560f0381e030f282005c0c2054114031055001d44442c800748182000005031190081c00000040079480c06449069803600c0244041c58440d60303103440d503000000e001c10816a802c42150580318070394044940d1030300f00c07040e42d02e002003121040c050228480400c05005100c40050081c0c400c600c00e2401981000f440c139144d801303503036203050014003040381e40d5101403c20f0f01c141d01959104401400300c461079050600070418641c000004014203035000140b20b078100ba00200300c006011000e464007240061161140495050940580115041180714003c8444943e4007910072030803001c0001d5055507501c1c5890324101c1c000d0f22100c03000c071b0700708191420424418800d1740d44a0340d00b017100c00b0041404804008915510004400d1f60650300c807460380100f02e098135558441c00d1000c480d44d541e0103180c01c003030041e40910050107500e6601 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 105485683 1250 105484433 105484441
    0x209011209020310050c040e040b0411030601120b07030605060304121b0807020d0f0203030a020a03090e0603030a080a0e0a032c060d18120f1112180303071212050f 72
    0x200042c504413000d003200300082d541e103a217668200507100d9548502e4083c2403080600c0203000c4480d9409016511455030290144a10b20625450b604240b00e00320071100d100c051000400c6107200000d41c0100301c0d10300050b48030b0b1991700180e10780c1c0085d141a100d40c40b240c00c4000380e05030802c41e45c0c041c032207013101018000d0b051a41c64002c284100c501c0240190441c0500008000014031000c2c43d00754000c2c2544d0f1200184403009568480c080c0c415400101d40d04000156501c140494130b000707441c042d01940c604a031041098400100c05040e01c50b42540d100d11841615900340304105060303120340e840c0400e010800d492802c0c61407815203620101c040000c1d043d14142e46480498111400c3e100d400b040c00c010010203800515100038019002c0b4203091903080515030b00070b0b6510081182034581540c804406541250340b042008040c070011001040145c0703c0c5a00c8840ca03810300324000b4200c0f0f2070103c65644491340208141c1f40080420303402d5134291607020b081c0c0150b0b42c1c08007a01c50300c50901e00d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 105486933 1250 105485683 105485689
    0xc02030d05010810110c2a040606080a0606050a0e102706090905060a17030d06030c030506251d0a060207050909010902010203030103081c0e060a0f09050c150d0e01020901120902 78
    0x45020400500c1f004600c24140b40d424a142a05490b0741c80103104110b03c0355150030151070200125a890030413403400001198040c051070956a0000ca00c0c0e031040c211003903200620940300c403528218070502282c00e400c2c82c8640909442540140401440e00c017045142c01405000e035103241c0c0081400c1e80c10f090801c1240d880f20720344402140c86418408149812100303e081c1507209004000c0d400e2400c3c2000401881060944841103038455000c903940382d950816070405486403000e202602203c06d01c00103821500c07c0c0c10341c80c801d8600e9000443d42e0080c400000306007540740c1c2c2c8110090b0b04021030400c4549030007244a0380c80440000207000b0b1100e282c0c0000d469100500009103240c0d03000c1401c024180350f00c1c020a020000d080410003600d0030848a03d0303521141242c508442c2c9091500041c0340d400039004443c2030660040c002d105082c012000c00811500c1000c9500580d00144041080e071061805400202000c09000503950720002e4001003840802e104040425800e0210480050b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 105488183 1250 105486933 105486943
    0xa0e0103180f140d0e090601050304030e15040503030304060f110408100519020c010f0c1701090908070206070b3408071209080315090103050a060c02030d05010810110c 74
    0x6603102070001003a0046250400203482c928004050501c200d004041504e60448030b180c07400d01e01182c1d05c0344103035962401100c0c5440101d9005000861615030b0b07030b03100c0c1050420814401103052078541800e03150340100c1d1860300211001e56086454404002140700c191092240e00e1a17a580300615050410000550314500c00ca1105d1000303550380300203000305c2c01050052545201802c0203542d034055400e483d60103031140e080500740003494100d20b0240e00c1e000e41451600c00c003028042c48071030b80c0390442000007441104c40075107100400b0002c640040c0c0c0c0f008004c06245200302d03c2c40c50141826900148964480210041604125282d5800d03c044420703248180361039915000d41a5514803030b048503014580440c010f02d550801600208105042c0040c6100d1001e403071040340604150310800016900a00c400341403600003036145030104440e60001c40e081e00f4503004503440c080c0c4401c0020b0844100341c3c058101504100c8040b1903000300da002d00982ca454031031142e400c0c0008841095160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 105489433 1250 105488183 105488231
    0x60405010503032b06030c09020a0f0201050613020c07121a07020105071b110301110901080a02040311011d060a030e010506120601140a0b030a0506030d03090f0308090a0f05030a0e0103 81
    0x135550b465801d8110341a0042d80107550b020101ca03000340c1d40c588068029410030894100881d854030320030b01c4828814419180302d03010082100342808400c000c4203000350b0100c0c80701612070040a401065200c42e550301d90040501c51151001c0b0440703520b0b442842d070300025202d9000c5905007010311485c5980300410b09030580074444000480342d014a051100c601001102a40550800c480e04d00814100e202420f0003540c20f88590181ba502c07811381c0c8049114501000340b5581485862400a521888010700b48014200c0c0c002080000300002a08035004104034100198a45806e104090b034203020f51a000b900903541600051207010150751104014024002c40302c12884909045540e4444031030018590030328241c0d601d04000302088080d00d8111001030181c0300c4c0030140310a40344603208000d15950480ca240b5205007441d6030454a9880182c0000211302c0340503405400704244c10103410400d841600115a262070a01c0042d040340006035000341031500c0e0002910801050442600c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 105490683 1250 105489433 105489487
    0x302070b0a11091e01020d090317131a0301050a0914040311030d0204090b0306060108040c0501030b0d0501050a0519090201080606070201090e01030b071e0f120e120306040501050303 80
    0x10210080b0240c1150700404250740d03030101c181c4c07080c83e19950b80b0309180140d04e4400c0e03081d10740c41c1030080302c141c0d000c3c03c0d140f0005111840c03e0f00c41e40341c00c1a088025001d031015120341e0311032090b542c0700320150080813800400d20b50030002004018a2404481c250010f0500480a2010b4521034005043c10070000700f000d001c2c0452007400008030720040c4101d802000140c101107407120740300c100500080070880c4a5601a01c00d44001c540e00c0e44c050302c0078900c140d500c60394281525040c50011000740800c2c13030880d50404144041000010400c0c000c7ca4419044810002143d1820410004a90b0103001e01102c1891a041d10f150250f684605610340c02482501c40380d65805103880101c500c0d1340140d002464080110b40040200038000c00200d014001564411451503a40104008005074080025011500c840720748403500d4061540c0b00c2c00714102a4001460085104a5905224181254000e070f042c0000c208a000e01d414800d00740908401d070f00550820611405074019406052031143d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 105491933 1250 105490683 105490691
    0x60302030d0311040b070501090203010b030c09010603090203160303020d091403030f031e010b0315030105101e18060501093006090c0b070b16080112140a0503090a060302070b0a 78
    0x1441c500f080d0f0855004100106000b5620003080c2030880c001c0c06020030481c482d500b00443c0300101c3c9000100c5400c0d1220081c0b003812242d00e414000d0b00244901441241c050241504000c44d49180c0383c003c500540c042e8016245055801c0001411485990810785000b0b0f641140c00d0415100002501e030380620b101000c80d0b60741c41c2c50201c0c2050070a03440a0710031804110002040b180c3d240c002035409007410071445d04a8031b042c10b0402d0300317a44045030a00025044180308004c0508800400140140c82443d96200d242e203030890090355090810321034042940b102801c1241d5680100b01d1001041072402038032018030a10f10250002080741c3e2007000350040001e05100307200059200c42c401c00c0d40500c841005640c1c4180c07080300c580019601343d5511034001c0019018500144403c000c8003025641c907075040c0e0920000760301c3c40b42c103000b058610340d02e801d0011a048408002d03112100e4003500c02561a00b6042c400c00c01c000e00d00b50000c4007010b005005a0b800202c01c1c0c080c06400c1000c50202107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 105493183 1250 105491933 105491951
    0x3030114040902030d0e0a0b0c0a060f020c15011e0308121b16060e0a170a020109021206060907020d0c03050a050f0d15050a0605070b0a200c0c04060302030d03 70
    0x20060302c1014000b079854010090443c40c942c1d0400301c1c40c00581c2d002d1701c0d1031182e650343e01650360803030240e0504440e42d6000040c445002445542c014525038904400040c05c2004030741503a80b03081407402400303241000b04001408100010090103030031341d000102004c44141542e4886a050040038800c0741d82d40c0080001c50ba202c407507940000038103292f40c052a82c0f2044841c0c80107614800c01c0c4401e0700c10901d0b20380710142240c000315600103407542020740d00100c64522035074200164803142c12042103540e40c0c2e1120006070f1fa2000c001c04094896401440309003061010402c0650020701404150b41c4031201d1000f116403c914040c10840d01420a143c8403604c102041d11644031748000c0e07144244001955040e010380c3e607030011810301032301100c1020711784e1940240301610740540034100100750144803410024445402d078503440529801d0104804414104440214070201851480c804000c2000c64810000f04004908203004403001c0c084d0a03d5500847d44540c030603041841019180c038410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 105494433 1250 105493183 105493189
    0x9020d1202070b0c06010e0105060c0d0e060c0d05041409160503040204020f030f09010f06120b0604060b0c0609160501050412060e24010b070809210607030c110601060203030114 78
    0xc1c024000d440c10f4541d2182543c6896403945800d0044501c41c1e0034190022400d42001815100803400080c02428400b05103401500c03a07000c4400c805500c10010450b10406a0041c400e05406c281e1580b5456111801d00840a5140c941e001d00c0901600c02c09040050383d890507001001e10804c2414411b80ea61140c4c0045400b91094100c2c401100b4800030501c40403041d41c0d84101e124420010003080354002d980500000e9070158480c952140e200d00d100c070008204800d824607003045c07000303000240705591a643c1c1c0049810002a12400350890410000030200503c41505101c014800c100f4642e8200b4001078a00e000c1c90180381d148091301d40c403c0081000c0c0d07a00401c0e0022100048400c2c00c0b600c070350360440d400c1c0302003000420103806900010300b4404142c01e6603607041d40000c94a041001c01824800100185001d0800f041000c200d0420f068a05100c000d0107174243ea41e0102e40c400c26203030083d1428100181e04070040d40044010464260b021040d60305650484001d06e10b0240c0c80307000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 105495683 1250 105494433 105494443
    0x703031b0c121e0c030b0f19020f12091e03030709090b1c0c09060603020c0604030302070203070902030c04090506010c020f0f03070b0409020a030b12070b030a090f060f050a09020d1202 81
    0x3855050f000711010906005182580c40200d921512081e100c5070342d1f104030404903100c01d8603a500c040c60003a0482c82800403e030050410300880c490694201240ea03540c0040300c3c0020b5503e09000d42121407046c291203210200014080d04000045246003040c0e0310040c4004003611031034076040e540b00c6444115a98201e1110f02a0301c0701c40380f8010078807080c24880c4000c001ca12558203043e2901d8400600b4070300900942e00000e0091024150350f903516181030b00650300403d000c99240c01218004a501011440514081c800040e1001d41b40c03030410300d000d011244082c003050b05000d103006400005070b6441414404560003618480140410180402e180011942244c03150390000708010800c0d0002c0c0d07002c0c01c4141d180303980c1407006e08080b1003401558001070b00c40e010aa040f04506100751001e0200442e04a0380441c0005045149602da006800c04d0284044403d40c1e12404a50381c4008070380500b42c0c02c040d002c1010811b0480981c00a0840c4142403001840f913076503003401034401c81c002c4c0a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 105496933 1250 105495683 105495713
    0x406050411030607080f07090518040f05060f07020c010c02060d0b12030c03030619051c05070b1602190b0702090a090501020310030b0112080406032c0703031b0c12 72
    0x4a074030700e007410300002d001c20100b04d1b00c0740c0350010500005000107104407080c2085990160030100c0d034041d080c484080a8a0040003940c80c40c0e81c1815050005004100c60361140c2800c1e91849024104180001e04040c51088481d0400070700f20f19020160303454030115002e078541070718001040d04445003c40ca00c01000c2e45014280e0201050040c0100c8005c4000c0d8841c01c01100c0107031840d800c1aa4007044140340e070240030f800401481e1444d10760078010300c0035011940204121848030f55203507000c91095200201c15031b41100c00701d00402c11407c05d080200110324450040085442c00c1c1181440306009420703000e8442e0448001107580203c050780000340c8982c01030001e40d6680760880340314002e10590310080361414000341c00015800480701a2030a0740794410035107403400b858400c007107015100600c0080c0300203482042544020451040c8241038120b608003410005155040181980700481044800750405002c0d10b40000c800540080a4449049480c0362401d12800d041c006460040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 105498183 1250 105496933 105496939
    0x7110306070306050414160f050c010c050a120509100903090302030105010321090e0f04051f0f0e070510030e030d02040b280903020f060903030d14011d0406050411 72
    0x34490300c2a80b682020b015114141c0d0248607108600500341c10b402d100b2515200c02c41507540c03103150810710440305c4020b1a0098031302141003042c14001036085030100b01f40940400c0001a00803040740d0040700c200d100d001c84260812041c0380100406407200801140049510340d40c80e220410540a101c040c170203140c01034001c01040d03843e031400c0c003168900032001542c4400700d4410f48081034802c010b141c00340c4540715414a07403174513185842d540c242800703072044866003d001000c0c1d50081420a088000b102100004500c0e00841e5018904440780050100c400307400c00442030003252103134108403d140180303290000e83e4440d8410510f0441c0140e8400c501114000640003600303646130409000000c8000700c406001409008144407412180d101340c1c1e0110703030700740810009481d00d44d003150040a070182c0307620701d40030014000134215486450201000d60f07a5030b980000242d8806400342c090020a070040f03040c641c940d055501d0901c0002c00090902d0f45034000142000740d03407d0301900001d406 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 105499433 1250 105498183 105498193
    0xa0c060509041e0905120307050a08060f040906050604051b073005040e01050a05011e140d1401052205070207050a06050306010e0103230c131d060a0303080a02071103 73
    0x4500200c0501400e4009445070f114906c032040304e103240700f0700300da00031600d03501c1e0140390030108801940d41c100700a00c410784c0b06103079441c2110203890340c0c010320f550b55200b0000056a441d05400700011500094000000c1c4d0041d5261480100c065004980034283c02103081c51100306241c01711404044506610500d50070306a0f94007880a810201a0054401422051109030b80352000d000c040d00071072180c203001806144940c2c40d000d4000040c07140090651a02041e84e0211916030a0b160340644821a181c07691001c1a0b120001c917890214050078040303c084251089240801517102e24154040700203d40c2c46000c01d803418002c000f50b200826014041403881c941c1c034207014055820071140d09003c00c0c05002c00707140311345c0f0a06c55000708034444071280e1441c0303210301c0c580507031504000c091446404080181100b07a180d00c0d141c880003018200d403590910896010404982d2901800c03150060540800a000207500009040d500504d900c42c016140e480c0e80c2848905814002d800e66018010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 105500683 1250 105499433 105499481
    0x3050901090c080303010306050a0209060a1d0402041404200702090703061805090f2811040905030403050f010504050c040c021510060f0c02060f1b01022a0a0c06050904 74
    0x11001c2d504036230041004002035a60141510300b82d00c165100160312000410005080ca405001659a096a40d0000d682e4400c0400c1c04101260301a81010080c084003018030001450507009000010b202020354843c59820b942442e9001d010b041070017403140c10b003440001e031154401d62148000388603204819824003082a000d500600c0142c803040303100c0c040e00c4010900b100000a812125601051419561080040a062151495180488504800c680c1b4010950b6450059440b00c50082c400b4564803881c41c0b4009142c0a100b00307031b02c52a0f03410f02e400c10020031000b1444c8000600c00361000b1640308580d010072400c01c042046103000010350320080c0212981c550842009030b40309925aa42c07140440d4034180c4080001c810002e62120007000304000f4802d4003c007170101c0980068000344904144e1045a00703a807c00249410010f542c0c0702601e566140c2c030031140f01304c50303445c00184c40000181c2c1c40d501890000380c000d88080c130100140d041110f8071180d0001407843c0507501382c9191800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 105501933 1250 105500683 105500699
    0xa02070308091606050d0b0d0804050909120405040203040204270302060c070b0c090102031c0504120516030309170a0c0b061915020a080a0314090606010f03050901090c 74
    0x442080c0d0000d41c070440050042040050a00180d82c0c0300e0456500181c6005400c07502580303d81d01a601031512401100b41c0c3d901c0b142c4105251510450005440d682803000340610750400815800ba2a4050460525100f0b00c00003100d0a851058034051b980e40c1e281d002207805400c64503540340400c0507070918403481600d65149000724520039400c3d0785803034590300034200980c064500c2c0a4181050341020440508465004181d21136042c0141d90400810800310321007158000304c18070003903850700104020440c2d94041c645c120300d02424031500b00f514240c00681000c1d20b4050040038581d43c1e010741028440c1d1151140119940000c00680e9159800c3c0c00a000c1504104100d4006044201086951410311103441080b89c24450f41c242451a04044070925580000340b0410740c00390068000105040300c0003000055030340c1c1c601044035481103c10005400703004109034001d070080428000f01d83e80c40520042910260715022071248c503001546401030503240002880600c40c0d150000f0000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 105503183 1250 105501933 105501937
    0x140105071e021f05040209010504060b0a0c02040608060106081503030a05090f0307180e0f0118021005041a0903060612030a0f17090c15070f02013006090e1906021e030a02 75
    0x10f10a87c0c1102480c0da0f940180025239400340503500d41c2140a00c42148101c1c8900502006a4002400070030398aa07030741030080c148442078000000292810040000c0115800105900948158011480c00044030302c01011401084900382c0300d11880a200099036174108032400161410032000c000e111400c2200000410080708808018000d18040c2c5081003018440c590340080455902c0e108030940c1d60030000c1020000640707109104041c0710102d007a16154003407600203840401c076980c0d144902c204145c80e100e00140b40f40e204059880404007210307404410b861001a041c1841e80145c010301e0800e41c0c058000c5610500e0301d495040401802501c005007641c240c031000e0780c05401c4201080d000301c00030b100d20080074295003419018080154480c004411109e2610103901c075100c5400400541e1051406070300d01d049544400003413061000398480c10804c01a903100501e107595a48440c04c0c1410514030020f05555404076a2800c1500703851071032424184c40035001e990700d1801c2500a0700039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 105504433 1250 105503183 105503191
    0x3030910170c1305030109150c021f0b18100b0d020c340311060306041118010206060102070e150402040302180406110c031215150304140105071e021f05 67
    0x38100243d000134403414180314022029410803075000c10b10308540c40c004050540c0003401030441c4545444102c410036100d10b01060800001808252441c664042180e03501c0d1613000004100441420b020350341450004240c01c449000516545416604007000024080c0d907500c200c0c01d010302c195560120901840030038810000444a45400c8404c0450800c1051280001031400c01420500c800c03034036041c0003840d03002100a201144007a1100b52569181d0028140d00340c00201c01381c99505a9a010300005512072403e00c000e040c042c0c0307801c40311540c0d0301c1c0203001c90740519000c0d2989d250a4480d9012903010b19000341c030049071004000201e80d042e00c07044405071180c516100c540c00d030b03c202c0700b4105c8082110600045d81880c040485119048101504905081040c403904c0440c3c0e0b111607205c101c450204005882c0c132403a00e403c04040e4115020701c4681c060745000704000320260010f55115203a299140d05004028800005070701d0050355004411000260310042c107a0407009070065482 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 105505683 1250 105504433 105504457
    0x60702040f0e071701110408032704110a020601080303070903061a03010203090601140604140405060f15041d070804170c060a0b040b0a0506090409050118030807080106090503030910170c 82
    0x20008186d00580c1c0502845c010000d0903003003002880f000c070101d5030480991800000070311841c501d1200025045034001c1794031908083c03001c030300030a160307405002884c018448136020710300c0c520b41020000c1400d450313030000a00c03c4d42c0e1001260300d001600d1214180028010b402190703203040000103d03541d10400d00c10400ea44140d481c0514250608500f40c0d0111003052241d003800000100810000d0600200383c0c0b41c11000c44421a42260707548150402e0302143c10080c0c0b84c4d46d40c100007441c10a04010000c07030301030308800401e0000c8103070b000d541c4652003138200040d81c01035084031903603615a108420941c082440b41c001880980985a8440412000102d074204980b600c008240400c0076654440e5a600150030f000001903802d160700102c803114132a000020302c41b00815415000c000594006a0024036041c042010494115460b00c0c0588203605120f20030342d02d00400079a40703216048080e13001e00c0d204000c0f0000c0b18040d40388040c2d2443c48250303003070035407a04040303400c02030f0080501411 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 105506933 1250 105505683 105505691
    0x609061401080712030203071103101406010e0603090d03110705010c0801060e010305090d0e13020f070201090806010e01053a0606060e01021002071106040303030506030607030209060702040f0e071701 88
    0x20440d074011141c000340c4d6451b40280d4145407040c2c0342c0c202d041c00d0700100300340c0500921041100d0801d162068090b10134414925012504003c000100a48251884d4901509080050040462000640709004102c03494040b440000c84800c3c0070030b0b80a2104000c1c01903080030703040198980c100421034140d4840b640d03482d01c0304036070700d00442c02d941040e940c030900c58001300c00c990324079841110010241000541b074031030059001e100c4542287c0c0240d8095202c441e010072201c04569000c2e07400c4005120a80060125505000200040d0384061240602c03600559400207e0082c0d01c4458150207400c42850111100340c582c1150142c255416085820728541100403d8403401b442d0303a4100d66030181e000381400307040b4040590096000768010368255029503a8042550b40303c20040c80510b2082e81c0108850620000341450310b80041d00f03038000d00d4010300c8082507644807001500c0800b41c0481d80480c03098043e02074000200501f074a0040036000f0720f4000315051148810040100d000000200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 105508183 1250 105506933 105506939
    0x503091003111e0f07050102042d0b03100302040204080109021816051606060b1e03150f0f0405010602030c1005060108060603041403131404050402150706090614010807 74
    0x10201ca44000019400310818002c061203009a80b5140a800c083d03541010700d0101c0804007007000360844001100c81e690009404d021420300b83c26040f00e0100340036140d02c1000c602c6190b0500210843c0219003d511003c000513410402c0c035003140c40116006081195110349a01c5039502030b0100c01400e0b030181e0030025400c1c100c2800d4515491090125015940400d1040b803011030303182c0e00c200030701145c011049429030007003030181c8203803030080540d41401540c1312070654161040c8505004074851500c3d0500c10021101880f1100e500040d1044841501b06904c0c9400114001c00740315080740c00c5031400d000030036070940010040500c903d00c40102e414204e400b100d26403d0380c0c0d040307401900188079100451103904100b4007440d080791150b02580e6210000b807104903d503030455030b10515460f941c0407040003d0355000e4420b08100c2000d490034031292806401085441001c8034140700c8034280090100240120f650161890030340c4944207000003203000e00c2c2c0404500c0207000b00031950060345000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 105509433 1250 105508183 105508187
    0x160e0d201f030207030c1203050907240309021f03060f050a0807050108130f0b07080108010209150a0908120702042f09120616080624030901060e010305030910 70
    0x41c03610000c46401c108148401c0e22000c501940143c28100e05100311300402a000401c03861003140006803030754001410b0b21300f225130113281800c564040c2400b0261700d2480c14914942003860024a407040c200032030840142c0c030200300074045451a00c68a01a506014061039034960800e6088400d44141084040d48540800c12103410620170081107a00c50b020401c40d41d40900c13070321640041c00074094120440103803185103030103594507400c41d0b46c101079004000301c040e08508035038090003640c4000c600f82680c89001c00c0340c1400c900c0480d000107070041a840c0030701e84111240c0700500170050542d0741811034550521401d8210304400c9205505007401c200c9440380700c8820143c01c84460320700c003506501580b00582c580d400106a16004404001404600c01007000740901030081150315041c00c89491100600016010745041d100b202d165403111741c1c040302e04030980c540b850b0121400e5600c2e194a0040d40c01850950700c42030142c220700340000207000011020f02281ea1007500c800210340f03000181 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 105510683 1250 105509433 105509449
    0x912140c01050c060609070c0b040c03060f02030630100f1406010c06020f09060f0a020c030f030a080a060e1f0b16110f1c0c0f0b03160e0d20 62
    0x1080c091035101600017001c3e0711b00302ca0321640120807070402e88090191910380082141003140c4c00d6070a0310701004100304101807480340540c0321402807011401e40c180b0000089401081c0f5826130003001d0900070840b00900d41508500b6040000c3c0100d42d00700f4908950f41d80903141c8440752664480ca41004844000565100c940c0b103440140d5a60a0090066490000039006540c0b4018002d805021031003031a00c0c2d40009004982d603940c025a15441035110082c40e02d41001c0795207019400011400140c4807000058410311910350401e071442d079881041c20402445182e00000c0340c40000030601600280e4030100c40240540c44984030b68050f101c100c40c800130300c070b000300f540c01c5074111220b900046000c08140d000c0b40c90000300a08440c80702040000c036561016203507581c0ca0030007428201c00308400130715403071f00600207032450701409840c0c081c3d0340c0e46074000100a446d010222079010607420384a550200401031005000700000c00d10b5080180041d541d8801d2071604012100c0200000d14050351 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 105511933 1250 105510683 105510697
    0x10b030f01020408070618030807061a0d080a120e250815190b040f021306031109010305070903050d0807090b070c060e190308130509040b06040902010912140c0105 72
    0x1000b00070280c40c040003107c5a00146000740c61051011501100180484000306500350098001182420b0207a901e2410503c03100c010030b100340e4100c80f4801c0020151070503241400114100350040e141d50005c0751000d002070741c1e19400b1900503413100f942450b50786d04040706662501543c1c0300c04c3c2915080d1540d61307a0107078680c8208030700103200001d00e00340198203482e81440b05004086000d20411003ca011385060140c544000c81c0c02146851401c504054500c0060000b1b1401303110360480100f58101c203200c1c501002e4101b60b1a40c0000d4035160040711941e00455204007114041c3d06031440c010444141610107900040741e9000c009035181c00041920300031504919a00412807524a0079201ca0245a00f944c0e0850788054101e415181d600c1d000c44002c50143c0c402d03d940380c050341c6071411059016044588500f0b0050280800f2807006c0300450752020003644c0c005031b00d480500060342c0100603907100008141e10a0014001c1040f034050060701000c0d0481107171080c440c0c903401581c00d0700404d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 105513183 1250 105511933 105511949
    0x20607090602120906070b07030f0b010c03050d0509010207020310020d061202010203120403020705220b010503040c170a080a03091407061d0a050402070b01030b0c12010b0304150e010b030f010204 86
    0x14000f21042050b1100070300c96060018683d626196040c0d0b40d1020042048401c500400c0d43c60020080c800068001d012a455003441c108807140c1e01039030301030154042e505841200301e94400005110780c02c25070460b080940c0040c02c45403031317103034071084100030b50b0000d0001340e8011f0800d100001d81d040d00105102c90181c0c142c01850500584e50841081c6440041044d82148200b403c0024181c8581021025814114050300954440c04440000382c0c0d000d048014104031041081001054034003070705006555011902204500d40310301c84500e00000014060295036000480740d06c626010340c01924564400e01207043e691003600c1d200e9231100c01034801c0e0307008510506070000200c843c1079410034000000500f21a02e03c2e4a442c00310301260401d1200301c840700000c0d00148140118200c4c0c8560050100c945645096202145910040418071602c1040c1c5c402102140c20081070820203860030f403280c241003000320705a0390000d001c0e1410320780c107600900480c1044240114180200c0703041e03503554 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 105514433 1250 105513183 105513193
    0x9090b0a1103010f0e06180106050403021815060703090503070f14030607080c0d09050601031214030601020c011101021b0303101e12140105040302030a0305090a0b0402090a0b040e030a020607090602 87
    0x2c084103002101c5c1c0141215440b141c68000f605880012210003806009160f6440386c4403030451050003044242017090000e440e116004001806003440b0b40d002a0140646030103848440b00e14041d01d81401e07a82010794903000d081c1000c42e181d02038400720760032521007028844070812407509240d2200c50a03a02c10001030803110018404000d80401040e118a40000004256000b62601ea0410034280c000300c1d0120701c40d02c00c901950740c0c850001c8115507408103c2e0752440c200f840010b0355900900304ca203414041c084941e11480b150a505845642c080c1505a0112400c41e1000301d480e03a0044404030030f00c400d100380218490302114070883e01d8052039000d0307120240c1849280d000e03540c407002c0c0444034082550554074007288207000340307030040c1d200c0d0f00119110981c1003006400ea079002840c4501d84c2e400285070202003411081c130150400d405544000f42c40d1603041110020340134410015420a0400914020482e8000000c0035150111703400d440d00c0c1d4031060390440c2d48000500c503a41c016401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 105515683 1250 105514433 105514439
    0x14060a050f0a030b210703081c090b04030305060909030a0311040905090d0221030a0b030a0f08070b060919201c06050103020424050d090b18030a0906120609090b0a1103010f 76
    0x4043c010040301c0b540d24903a0f42582c117a44581014ad80c8440400c40e181c180c8441817100701134250050b5a0016800c6544403698a0402481d5a50380240113a2004054803141c45610f020201740845018141c0110180003d10301010081d58802c2d90031a0f041c0107118031141c031b5079a4829a140034184541650150345180c41303500340a405481c0040c44258075002e85130010b00003d14980c118070b8210710400038292101980e0400c06486140204824041c007603d00c1007000c01030032201d03258250007003200c00040000c14410709806c2140d200009040c0040c00042d0120b940245404001c1d01d0401c00c44203000290319240110140d0003030303108080300405400d500081800880003103401e0030205c0d1900c01d0400340f07c145180d080d03905231941a41c003c1414410b00401c0c00303010307003522180c030b110000861400c0500e441c020044e2a052040404021410444622400341a0003810091100344c0f8103120b050700c1814a01059802900c11080d075915101c01c15180c101604183d1b8100d80147c4820210b142c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 105516933 1250 105515683 105515693
    0x30406030902030c09011d010801050c03070302070c080d090e0604020f07030f0c06110406030b09270309100e01090f0303080c0904020d1d0f030414060a050f0a030b210703 75
    0x1c000d10201e030305015003800c840c403684078005d59900903c003c14404103049000500c1c8004841c040e0040c44143e410321b0200210301800c40112074014809250050f42c80e4020f040610f6000201c1d0058007590058644820f0a6a440001c0074103484242d20035591688401c0100001c0b0710990112404902045c050703400072030f020b1000d15102c5461403d1599240c2e460390b50308421280b042c1c0f02481c0d04000403c080c060982e1520a104130381d101918000c4450801c0e81c1440d20348040c105e1120010881c0d60030041c2c078000180140c035660900903100b074201440905000e00f1410a20302180e0010304034140000c2c0d003001920800003101d405456140e801d0701c034070160f41e146500c03102d5800d4000d0b03001c001c3d8001c001c0c50341c45540c802d0707040301c40c0701c00c84004080c0000b42880b04000c6e2039000c50f0f00510045c4480341c503400c098a0b07082e0040361816590710460700c3c1614180201840406200380c0851345124054241d004074000442c03c480c0c504200c21400c0c0e04819081c43d0308c000e4401c60f44200d00071300c0090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 105518183 1250 105516933 105516941
    0x61e06180e0103060207060b01051c020f090607050604020102010e030f0301062a0b0a0c090305060c0c0c0a030501051e01030b06010c060209060a2003030108030a12180809030f010203060303040603 86
    0x900c02004551586500305000d810800307034411210190700181b050709000782440758840d0101301b482d00e649044101c020098240720003495620310250b0006030301c0e24800203007003140d1440c0405080c00b80c40c1c0f007050038803545611040f40d061340507509081c1a00034584001c42200c503110ba401d00050f044d64240030302118140d0403c003010b01c96090740b02e40380000e0500c426060102038822040f6204500e400304503002074a0f00155a0380a120781804240f0005102144482d0b0241140b545503458000c03820600d407400a82c005855044612030740701200340a41900190721139040420750020310904050400c101c40400d100180c0100b00610204800c1d40c40751152035401405040c0250900c10040700250483d170255103000e000c19081074410504045000f5691441e40406016609561402811030303260b03c148400c0c901005080784030b070003011b240c55000001a8032004030030004d4100da071500341e140780c5c800b000f960f2107445807102180f402003050080b6840764001902460502e460310005401074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 105519433 1250 105518183 105518207
    0x1b0312030c140f07230c12190803040b0610050703082e05040608010e0a08030a0f0204030b01171b010f0504030803070806150a0c03080408070b04050102090301061e06 73
    0xe0001070780045a01002c007600c10405080c40d400e03074400c098078102404180c2c05803102c01c0b54213680c01c03501e58110046181d40c0c02c803805031008030341000a4070400342003c0614001040d9081d020300880140f02c4ca103005107104910030203d1046544400c41003141c400c890f01c4c1e103400014410030010740043d115060b2280c0198407800310390015807a41d40e400d10403074a81c03c215100480544001c20030740c40d090081500400d075141c003c100300c02d03120784d00710340b03400d40054040c0c0544400000309a052020758405542c00c05666400c5496a882c1d00d81752002034800c0c41004400303407029044020005001c9030000301201c1440e446156119480015140c2c0405444107034180308041c000000800c20b803e0046119607400d69a40c0f18a14000e02080103000340c0c0d162904004106006100d0f00701e800107081c04506800d030508540b5681e41e45403400c924860301340c00a10700600f01c030500c010000150061b0101a004130000d000194a490780a21001e0400f05d2030131800c60798000030400e09010310306140e86 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 105520683 1250 105519433 105519437
    0x1020c030d0914070506091309021e0102010b0d020d030f050403060f0b0405070806031b06120f04120518060304020a05180103060509011a040506030316030801230d0201140903070608041b0312030c 86
    0x48a042b900002c2940e00356140300803548111520020440d07a082c0708421001a045807070901903c842c1d00402e244e110350304d50050500c000803880c5441a40140c003614010b42c0d0207541441000005071520019000c01082c03980180e0514000c20364850141c801c091082e80050001c3c004101002001c000820100ca280313500544200300350082001c28010240c032440c051652023945003070501d0250382c1040c101c2184010404140800011070400b1a40b552002600322a89516515140009a81100c040e0301250342b080c0000b900c00c14100c90b40d208241203d0023240c0400907a03580c140b05a00b0b072185040001c0c004810f10000807681d00d401d0384100c0c0c006001a003180c4c18503002c40000100e100c20582d00743c0110ba911b40c01000342102e1411403804000c800401000480d5040c1b01080d031601031500000c1c107001103201c400031010b195400b035a010844c0201141c0a241c1d036402c004d40307903407020340c1c1c00d41d42580c44180800d01411b007a031020301160343c03003140e40500c490641000c0780208007030600c803c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 105521933 1250 105520683 105520691
    0x302031c0b0d0506090d05070803040b1b0d0e06010504200d0603050105070c051902010e061b01060b0901020c0301060806220203010f0b010e0a0e01150201020c030d09140705060913 79
    0x4440e200c034141004814443d07801007001d800c2c2003108514040c0b000d901d420070024104010000660070400342d0703800c00e612041128440d101d1035480b010200840e003500d00c500e50b012809010301d0180d134110800c01d1800806076075032640c8403020300042e1001c1c0407903421a00c00101d60843e6407840da9009010083c07072488002205a00c80d601c490945030f0949000c8006a0741c40785d010103000e002e0100c1d514a41e12400680d50280c0d07158006040c101c0020b40151043e0404120661107081c1654002040c034001d4008101c89502c501e14001180c01402c80103005205500041101b810f05114280641d00b40b48000c010b00d070740d01080d80c02100c0e11040b6220410b0800e56401c0e00580b024000c0210503940041c0100d400072015000519112441c50745601ca0000c1c40810880e41492000c00d80c10340714001e0100600a80000040e406881950308201c024400080c0c102000300072036100041482c410107140d0191401c1d061074565030344e15030007101d920410400000800346400a05804542c4200030003103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 105523183 1250 105521933 105521951
    0xc090d0203030d020406021005040c0e04030c050a0c06110615040513050f0606011b20180f181507180e13020a0f0e060d02010e0603070207031e0302031c 67
    0x103400e42d000f00c0403c1240b0754001c1000e100c941d03018480242441500c110030820340c5800d49800100840c107103e21108500700074041002c0c140304904280c5172680000450b5440c944a142c90800c1440500c650f50000345025141e0850301c07000705440c0d005242d441c1c8400400c2c00c000042000500024101e1494403000d50f0210002502c24444a8240090440589403034542039002402842e00310b402d030380c083d04001c882100000c083c41080301d40c84080002143c40202d285020418481c0c0348480308648010180030004090a00700c60644229628448114225042c4071511395984c4c880802584100040e800907130b0030340c480c00100104003082080200610758031038288842004c1624000c00e52a80c0424803819414100c0804005010500500e03111910701011512076200241030a442204400007540a581c460700d007800a240004080ca80c1c0c0c6d060800b00a5544e1101c0d100c01c07103503030703d00c208445030b50341d12800f056001e1a0590003862030180c20707000400d040c0101d4940380158a0303980c041c003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 105524433 1250 105523183 105523189
    0xc09150d050f0105010e01060306080a03080a0204090e1e0a12050a020102040b040801090c06020303091f0b0315180604020609040903091806091401030c12050708010c0f0f020c090c090d02 82
    0x5114400b03000380001406504005540000c000141c10a41c240f43c24143d01304001000040c4a120194040c5131100c2c01e500c42e02143c07c040c1c42154840d204040c1080800c03046018089480f080c02900124003000d1044924801c98a54403000400f070600804400c507c0201806140101558403961000511b440d88441e8510b10982054003e60b4841c2c1d901d000040c104115090604094400d900086086180c03035882565a00d508081c405201c440348c0e00d180b41c030f540d0035411800d10100001c1c2503035124081824820004003048901111000402c0c500715022500816100c0c0a680c025010078605443c02003030001401e40c03080100c0400900e80d80010340b0400c1c3c0c0c40c15007403800c442d142c08175401740380003c010b041c0c0d140305110307410780620b400040000809503000c1e10100c48419110800d10301440c01c042e81031030410382c4448415401c007050041c1e2241d0244030280051056211000201030b01103040f40c5d00d0200c1018603410101210201c2e5a001d9100090941071000405112098440b5804 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 105525683 1250 105524433 105524443
    0x90a020d050a1b030b07110d030903020c0315060108010905071d0f03012c1603170706050a0204051509100305150d080307200a0308100b0315090105030c09150d05 71
    0x849100e040390014020041c1103145d40d50403151034a001000d10403542c02c5281c85042003102001070680e2030941004050007840702014040c0d00800307460302d411140d002e0004441e800c0310024006500c5000100e2280307410310525006000b00e0355254071400072000000d140300707015002c1c01d60107440032902c0482c039030b4240100070704040c10150b12000c45400c8a0310b29a912400d48030040a504101601c403411003020001e90100ca4102c41602e2000380c03202920001c5109484020306014200403c010601c10203400800c200c4800369051121745d070b46960080c0150140145095100c81080e0100100c41d01c250825608181c000b221401140d0080c4002419200c0c2e840044403030b40f070040200500c16400076842c0106811450501c00c6900794980125190b104020004041c40280230218022004294035400641111855150b4038202156600e07070004802e0303581c1e88070340003a500203d00ca04000c02d0320100043c024100c00620707190340d044948100c0c10142d546400014040c0100041442000703 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 105526933 1250 105525683 105525713
    0xe01020307200d0212090118060206011409070f120608071202030d0f0207031b0f0305031803010605060702040f02160b091c0f05132303070e090a020d050a 68
    0x84158031204005814203110703a001d1074941c2c1640005030501e040c41d801281d0019000f540728140307952810000d0050f100385141c0e001c008001041d078440421601d4002401c503042c1d85000000800741904074040107408582182e07003034009404c05031a0ba80c424080c0640301d5100c1d484581c08224a41c803842842e1611114be400360003030104414902d41581024021010ba107015071a00780446155140041d60710041440700134111006101a02c51120f150a2001e02070110003402d0aa0f40781c1c0e03400c046580e600511220b000c0b180c1c00c60700002089c90144a0902150406086641403503a41d40030080103000d483c410740c0c0c1c66074007001901c540c02c20b00755100c0c248030700c50102d43c103441c01c00c04112485d19040b0310000e90851100e1522442040d0005501c4c001903540d0b1030910b81d240d80d24504203516a40c07075400f10020380324049412000c1e0a10000351b40c0f07180c4086d0304503040300e81e407510001040c1d082514011007540000171102c3c054140300415480d00d5020380221110f00a0396500d030300890410300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 105528183 1250 105526933 105526937
    0x6020c0106030b060604080705060703052b05070305060a050111070806041a0907030503180d020307150e1c08030601200106060f08151c0204050a0209040501050d0c05060702040e01020307 82
    0xc0e0041c000c0214058203e500214145d5081d030801e0700309400035950f0302190040900c908800320300307001050b2040c800c0790320034003c50103828080c0c04160a04038001d0759842c02c5113000c60800b8000380c0014401e204091003840010314289481d4a0100152000c1240108141c07440c000c02502090b903103001c00140340640d01c10460745160005c0c000c0031000c0e41c82e020381002d00603001000308101080000043d5520681c03d0001090304103030300700000758184100b0741c2c0250903000d000c40000f042c00c0b0544204070915182c0d107035005446d010008000324444881d00691001072400c201c1d102242070003001e10341c0268113040540e22141040002c59808480044100c516915210140032207540b25084034408010350602e13900a0500d0204c681418151401d0345000c2c01e5848072100031002401c600d540002c0c0c01600800080c01d021807000040d6020034044e40c02541080000641070408000076488035170005141c41420307040204110b0f00e907101c402d040c0da01c1071300c808a201e4003900a01c001e40c0100115 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 105529433 1250 105528183 105528191
    0xc150207060903080906090f030d020a110d02030a1401060810020a021506010512070e0409030503150a061403131406070e090603070512150f07110a0314090301060306020c01 76
    0x14010003450503100ea004002042072800080000840950544028400480d500b6481c3c82d20769000c034541010b8000301c1035042c40313500181100142c02240046e900d03030244600780203490240b0148101d04ca040540250180d00c2000000301060444580c600e449150100100d03006941e0f00d00d45282000c1c803600c100700240d0010702c0884040d010040403003d1014411242c2d11840c0040000e0007500501a80b500801003401c00100d8041c0704600000e00e0080040c02089101c01c1c03410010011b030000c0f540000f54503200748000446107031010500d01159165940c0c030418419501108590f0f800190502804000ca40c0507200080c4140000c42200c0c00000700506040c40e044038000c2441104001c06401840201c0900c00703a80c6000c5104416500b098841c0c0e81d00c0c001035000c071480c2210408242030b030001100144000c00c55640561070068007565180515419103001d4240c171011354220003004968251111101213002d80c003d0f28031154000c0c0000f0322541e4079203444081c2d0303001403101c032040d03503403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 105530683 1250 105529433 105529469
    0x60c050307020d020d09152313080303160507140303180c0f01050a0302090a18020c0706080708061c060c030b030f03041208030c04090e030405040b01230d090c 70
    0xb04100004112034280300415080031910740260800c1c880d0701030700c6005182005044503541c040c03010101034020341c0740c01708802e0044840603401038201c10080e403c2c5054640c400102c81c1c200000b42c074041e01c0f084514411210740042c0070f81e0344d503024402c100c1d07620f02e00304200e00300044140042d41c0302d0000c40310314012003061941d2103402c02d030340e011a880c4100700d1240c9480c11a42e2207025580403980d58200146c4d1400d0302000a240d010040c0c1c000011141d01050004c2c54002940182049019103401c940c852511000c00f40d9041c402101c100300010004d400040d0245804064800381c2408600c14034030503000c0340c4881054521138407800c1d010a403202c1e040d070000e003410410986820460f6010b141490304000700d0159030f41c014500500354034404000700d51119141ca00700d5008010009003088003520203403800d42c8a82080c45100d01c0b851a08031800a213500510301f0100d240d107240c0d1016410702002520001c01e41207107100c00740d820781d18442c2000160b82c0c0306855015015401052480c451 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 105531933 1250 105530683 105530687
    0x80a020a05011b02011d040213030209060303070312110408030c160b09010c150204051906020706091202010f0e0d0302070e070f021f020f030f060a080d021e0a060c050307 75
    0x24007940074a042000c260781080718032074004a51210180c1c2464002d00c0074050b03640c0c0d100290300b981401540301d0300c006064048402129440801c8910035140038008d07a94060404d80c8900400d04040c000c02c0b00c021010f41c024040b81e2003240500f4030884124141600c6100c524510742003146040c03650352044001c441c1c2e614140c80382c000100502c00c400e5240080400009260418000d4000c040114050b050a4600c03110380640c0d01400b005844a44c02c4864110b40a00d8418503100e040b0140c092801c01040140c4902040700645102141c01d03941c14400b5401103441100f400310322020405084042181c40c2c1e101d4141c201c0590181e402000142c3c01c2840004030210082c00d220180b22100c3c01a2003001e8001c200700d03a8012400840c1445003500904c2a0302911803080d18020783c0c0000410800c048610348021030084030f050703030403034001c2e07480307600c80c594a4806d0030880025a12485010002d060420440806054202c0075039540460a9540000341c444a000d1900800c0e07010082203c5d041e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 105533183 1250 105531933 105531949
    0x5010605120603030901021f060e07020703120206010506071203090602040b0d050a020a32040b0c0f0c03071e030c08010b010f032003040f0b090d0f0305010b1204140106080a02 77
    0xc01e0483c040c2d0315007906040080e42d130b02217056412103000d241c4000d5000000065101c600181a45000131901c1d00d07203030100079190b0304240002c85401c0e4072500c0c03070004e03030b4400a012416114050700b9145000c40c0f54451a800c900d0440d1034404068803102108005241070000d000180b2448107519240c10218108406503000101222642481403001048055100808070b500c2c030f00b58200c030121038410540d40c0300840a02c8682a08c00700000030300040c103d09001c020030f421200c0700160f40401304154125900c812a032200719600d03a200d44400d000241401c514500a61024000b402020743ea95450b070718080101ea100b0951039649000c3c3c2c41d0156000804400c00c42100d1a003040341c548100c0780380500c04210002c2c000124004030000c0e04000003610b0000b5078a030840803603c19450302504d007540d10b50b00a02103000203a907544111080c14007a000d030358140c0319002809820500b0104601141000081043d203141c1c0c008005850304003c2881100090310b1030300050900f030301250051003000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 105534433 1250 105533183 105533191
    0x504060501021501091e090b01030209010b03240415080106060206010501050316050d020906070506060a0909150209010306050604030825110114041703030405060f072007090501060512 81
    0x1540140c100c60185603c0b40201e01c0c1560302d120000246030341c01d08a9400b2800100e0502451146040680020302000f40c58050480e4402c6901c00c074680c2e260b10421245d400107035200300c1c1e2026101030510030080f0740040c035121140c01610004030300c075101c1400b07108859141d003c5450769640d95001d05c240b0f60f0600005003d00000c0c03d00c03038558200f552a00600140b200d40290810401185949019041e90100c544101c0000c21044c0c8030300090400da41c50b0f04069a905105400540000034200715900400714465045141c41018042110010001c1d51000b0070060416a60340404102c95840401420185000d010b0705a21407180e141c0074014900044444590039203030100d05400101d500d5001d000b00c1a084c03070200d0200c03500355000a10307406079410428500310b6615118410701e8001000e503200303d006500f11501c0d03440707002003440b1000081e285080081c520400042c0d200420031418581d0720601c0007210300165a81c881c00701111401c0c1c2102c000503c000401d45000111030b5082c80d08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 105535683 1250 105534433 105534437
    0x15090c0102070807060507080d020c030c0d0f020d030504080904090804090605030c0a05060a09080f01090302120c0604021504030b0f090f011103150409060e010c080702060106140f160303060504060501 88
    0xe01400c003d54a0f80d0789110384202010090001076101c20000780705c0a88001400040d001d54650b509074403a2074994220406a041d144560f0000c640424410a01c0418940142d00500302d003c21300718003100909002032080c0c0d41c000d820440d040d240d0710382c0c0c850881d0090054a01540340c6080000c420140e0f4041d900081c840c1d4043e2180568540e22502110300b11a021520199140444c00d01a80c00141541c064601c0d4000d07101e00c900c2418040d00008403062103503081c0c4407181c3c12403140c0405400340200014084e84120300090040c1880d801c0b14031120803051155051543c5c3c2c0d41c2d405102c0500f203e030382181d00d803e42c09110f840f0804101244c11507010300020702641c8040041c1600c01c0c0401403003401d240c0700d4012250300f240c135a0b5000c3d00c0c0701a040981400881c0751a4149c5019100300c1c1c05403c001011840041c10262002c01c006040e00e982d035561061514a03810600207541020007100c50a900c00c0012030384100d01c1e4014901c049109480c003061207031400701004200c0e04aa4401d47c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 105536933 1250 105535683 105535693
    0x3040203070e0a09120509190b0a03020f16050706121e0b0103060902370203030a020904020405100e04050106021504081605060124140909150315090c0102 68
    0x140e4000c1900300c160340c224440c014403551044000400340103c440040d002d40441c00184950940c8640107100103541500c0201c60b0542c004020301d071f6003001e4420f040f081003080c045801010709c25002400a4054041d60303a0501c00e100c101c2071200c0480420403162170b88071083c04c00100303820515610041400e00400c0042001031305002030212510742c03400c2c1625603517103a0300420340e000c0d61003140074040c04001191580c01c0c03500391001f545128495201c0035401941d00621040e90780020705000d50340740d07010714155122030009401a401c901e05941c0c0c000e03000c0c0000300d11908c0b4006040c0d81209155a02001400c0c40070a100c00c0b1441a0841d2007150401008544220041089190400d40c0102450742d105c4141d100c00c80ba40140d5440186a401594000582c8000f900c0c840284d1080d002c02c01403070b0703081c1c00b002038135101c4603003001c1e1200403000c4c0407040b080e29140320019071007441c0c030102215440107240003900741149402d10f58050000c64080c056015000c00903201c1e91039080c0000d03c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 105538183 1250 105536933 105536941
    0x150a120f231509030a03090203030415020f0c030c0310020d11030a020a08330a0b040f061803021005090301090c1e1406030610031b0f080702011a04150e10150503 71
    0xb03a00c91091580c05c0c001d05803111000f408540b400c108603402803040f03c00d129034000d408407000751980000c251600701071203046148001440c010a4909116100800418911907268045006034000784001e40300ca6666400c2500d03031040c0b03200114412181c400005995510000c80900450800b07032a440700d0810060002d0702c559041c1039469100b455980c1c45003110a00d94001503842650754008c5000100003040c000382800214903c2000d6807103940b01c2000700c0341c003d403001040b0802807201030352100242484e0405d00d0300a078020200410040c0000c140100e0940320804091084e5200864004580c0300780841410f1001e1104058261020b00b40c0001e40c20000240c52400050112480b603d020182d1b40d49160280d402042004244410601000541000542080010f41c1d1480c0032a00c1403000804045c810320800142640d00610501040c900000b400000c1c5540c90b911240342740b44910205d8a030000c403666610903d02400308001203420304080300b0030031130303560720000512800f4000c2c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 105539433 1250 105538183 105538201
    0xd0807120e090621010c030501060f020102130b0a020a050d0203040603060b0405210f0a050303010905150a0308090a090f0203250c030c0f0206190305150a120f2315 72
    0x10581000b0f046511481c403a0b881000300342c0001c5a146805400e40ca0a460118500e070107410031030491300740381c840e41004040d42000307034240d00c0707480f0180c07070310380720030901440980c107100302429030701045104840381515107680c2c06290100c48140c010150f0301c00300341041465850301913079010300503154006040a141101041b103521a0546251402c1034032a07845031045000c11480700d02c0d070034100c101c460580d520f08260b91664001e00819001d107007404001a04403200200407542c0306400b51643c240f20b0b04d1030301c46040356000704500c641c0c442c00c0c036000000e805409000346050090302210040c0c0d00c1c01c02e40285201050055041042c0365000c00300040390981002400c2103441e0035003050800d4070200c1c80d00200b20441c0303160081d4040c0c40411784041844c52520000c0c100d400c10344040103141c40d80c5100312200c0010055442e4840405002407020b440e402081916161003042080881841c07541ca00842c0c0b102c010504188403590b22055000380000c10007601075030070806042074242000542 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 105540683 1250 105539433 105539449
    0xb0f070e040213050901080a0b3408150105030609040b09160f050a091407080c160f0203060703181b0819050705420d0b0415050d1b03020d0807120e 65
    0x203d1203200cac1d68529280103c58000c000c00c522070350b502c1540900300350380c9c0b440684101b1080d942648410b10606040325954002c1c42124041e00004200150550b104d948400110100501c006121f00a4900c54036100142901103c0a00b060103116400c15007000184109840350358025060a41404914158688007032400d81c3c0140c06842c2c05103495840e40c81c18911841500c81751000181c511502000780070500c3c60540d6a40d100324240c03406d03a12900002c4090b80e242403400184654031348003140004101c4040c1e15440d11081c06600c45203966034070001c0c2030201e1038681603103070862401d2400170004284040c1010b84012501e508600c140c0c000c50480450280140038240000c1e03200c082c962442008902d21190318444403a6941e050240510010708910401c450089042240b00c540c420700d400036410607604083c18036144d4034030320340310145491690680302e0380e038040b158804805a141c407a1020712450091096079030b1001c0a203000b05244650b50460700c20040410341c9020304c0d503a1100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 105541933 1250 105540683 105540691
    0x90302180c1c020c0607030b040e01050c03010b0c07031a18150606090402270a1a0f0a11070801020304030e0d02030705010e0f060d06050301050105030a0b0f070e040213050901080a0b 80
    0x80b0b60529202042110390083c4542c41207002d19110340d004000030039034141c020240e02c140642d8180440b50f40005428241d503019100d010421000b0f00040c04420140d00150802a45030401c075841140d0381e0311849840940d507400174207400040800c002c1600c00d03202110003a10820001410302024255046807401805050070344500f0002410030340c00d68868054070741000000d940c0e20500e0401c40203200035011448065401082019030024200c400b10450079078206580b060320b0316250303003681e4400c41940040d0504080c80302c00148401607950070080e600c05000000001a0b40703041034140a0600b040e0300b44c44503c111000c010f40c0e00140c40109034001224003e003043c14045000c0e800040100b2802690a034100c40003140800b0395403081e40100c3c084032001da008125a076280c81c01d25884103014200681401a400082070400043d1010140d2050080c07504c9803c85079018006026a4000c0762080300349414060184424604452200e0040c100c040080c0701004455503441c8400e43c0c014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 105543183 1250 105541933 105541957
    0xf0c09060f3b0102010f060803041206090506040b07021501061e050904150e090a0209150f0d0f060c020d09030611040503030f0c01050a0501050f101e090302180c 71
    0x403038110308803101d50000001c2c2c1e542c00590410410026507800e090380348082d405401507007881c01d04420780d41c0c54495041503641030f070099441c150070425150203039200c030b0104035a003e03070b100e00c2900440c3d401c0c001799000328072921440202d400c0a4400074a05003c2c0424841c12031070711030040009642210038110724071200e41455100144d03040080da00b60003909040758105090031152007540381c42c1d0003a4010348120001c0c165690300c0d1580340c5682d40e00c0421000b5007000d2110003080101d48025892400b040d0010115410708a446012450041071140c1c01c03036403480808220002c00200c0d00501300c0329441840100030110042000900e0180c1e1840040c100355540e40c000c80384041b4400132500902005021240d07a00001d114501040e40f25408202c141c1d40703483c0c045152400c0d940980c50480318000c051070b03410909042008000c028140f071400074000030314070a070b541d1501c0101941c00162152600000c103843c60060103e0000b100c5038080031807a00c0c90070003907410300010540380301013a14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 105544433 1250 105543183 105543197
    0x60f030506032409101b080a0e06220c0303090e0f070212090d0f03090f1413021606050127050c0d0e03040306060906092f030c0906030103060f0c09060f 67
    0x44c090a14203100c80c80c200300c40c2000b44410390701003018040341e03811613a5a03034000c00d50b0310381608070122415400040115040000030500c1e407542c01104251b021140c10044580e4021962003d42280d556803080300403800b0700104125003401d540109601c940401d4100c0d000c1d241c88100251180c2c2c01071076501e00c004010800111940b640ea51260842e58845840c4041c00c010303060162a0f07440ea4403440394400641e000c041880b000b44040d0070343c03008003e0101c2e40440d00d03140f1550040e400c1140f100d00b010008046074004100c103030080d94002c040038003002110348484005c415032517808000f002150390500d001e009103907402008460b400c0411080c002000944180b0142c191312481d407000c1c020718100107020030010308590041040740d2505e01e0401c03441d05c0c2400220403420f00355855410101c074400d14108400a42d00c0215800b40c1c511003000d280001c240d00141240c1c2082c1c1040d224280d80d10050305000d040c502c00c3c08000714030340c01d01010740c0e454600c0c000e0642c0c6500c000e4408010700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 105545683 1250 105544433 105544441
    0x403030c2105190e03030907080a3201180201140906160303020714060609070806030307030e2b020411090303071101031512020906190501080c070507060f0305060324 73
    0x4143c09440580c0480e0107102140c2c1da1001c0350350740c1d00280c0307900074107000d0800000303a400f80004a0292085e0301105000d030340070009049050f08124283c01b00213900449404050940d403c0c403900383c035000c8190b517800d1241568000180a48030724407450a00c810308115031700f0340d0381c0d412040e510248000d007060403e201d62441d04801a020300d00000f0004180800501f8200c0400720310240b099500742c8034000301c0e0f9161b542c215411081130b00c0b600d030036400400400000c40d10600c0c2c3e159030300c07001909088a020003801050a1030b581e1032400e80d000e660b08401c0404501d414052901f9030111401140d00b000c994000080e12489602c43c020070484202c40301d8407650b4001e0b0000c1134400326141510f06016035480b8203c0c0181c0e0342141c200e01c283d0345140010358500d400d14041040310401132031401ca9501301001503400010203080b68004a03402c2c00f80f60f0010b4000c024100140c4484c0e990402d0007050385401400b6074801401043c8a5081040c549402501c80d06414203015421484200181c81d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 105546933 1250 105545683 105545701
    0xf1401060905091e160b0d0c03091e03020703080a03021c0b031c090e04110414040803280204140306150d02061c0501030b01140f030a032102120403030c2105 69
    0x2074041070740d01c141d44080c40007031884c46c1d10029242803022050244424503000108404481040c1d100400d9056140091280f1b681803030850401540300703004070340e249500d9031210703580c80d000a009040046c0d00040c0402c0003450700d05002441800c54401488110b01030030001351540c1d10748211004030000c4800b80c89000703100c2da02920060400b800e86001d503003000c0c02c02004203008540e03498081c03401c01c289907100100c2c0300c0006129a42103110f05086403501d02c108070360b00b01c036400c2045921080c181d40d00c10190310391004100a02821181030040f540310303000d02d814800018284044e13441c440340e0900437911840803410009038100d0f0500c0e0f0750703403803000c1c82004207c03c03001c0128014981400402001212000a41a00c845c0d40701403549200000410070310701490b0020325015004801c0c090006401042070103540c8102e0124100b10402c0c0d440680e00320b07006811407143c3ca400741001d11044c11380511803080c1c9610a850b103c02c0d81040c1040e041c044110400c1c0d0b01c0645555100003401f518 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 105548183 1250 105546933 105546943
    0xe07120f0512070302030d0e0d091a040b0f030103020907050f0711010917060109150803040b0f19020109030801050109060e090703150303020102031e07020a06180f1401060905091e 79
    0x76030b030946007910b070011400c000350380f03800422a001c0d10314a0304851400c801000540788080e00201d03500c0b090001e00306200c82c044401b000e49003898443c010f10010032901000c8014000000607c6001030301c03585540104185418080d00c04020b10000b0441000c00e4401c4004032803119400c040a00c16502e031850040346c2c0c00c2c0455220854001c410002c2000c44100070528904944680009000601d4201c3e4205111030213481010307400d0340100000c001545498000d0545001002052420140c0440d5140ca060640040030030060f50340f060154101038110303c01c580508000c0c40d02018680c00c1c080d0151500040140c420301c6a0742600000d43d105120350001c810800442c464455a1582d03450080d021750030030740b011449002d4580c0f003001c1364000040000c0c03140c0d220b0381c0140f8030591541c461100401c0740220880a00c507042d10b4038030109810408092a2501c503000c55095049143c1c02d072421a0700503089500010300703203000c2c030190940c00114141c0f2040c03a0625070301c0e0320b8a0440e0301c03441c00f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 105549433 1250 105548183 105548203
    0x412140a03020903280b0105010906050d0b27040c060305040b010e09070503010c090501020f0d0804121b1a0a0b03070501050a020f160305070603050606070f06020904060b030601030e07120f05 84
    0x2005040300052000342c41c1701020016184500507459040c0d07264030040d5102401401034000007141440f00c54203d4140d82c10040f800b4101400820800b020710403e015035007006c0d1041c46881c0320a5051100304a51959a1401840a0320f4100078034241a40d4114143c801071042c14889814500403603070340c1c501884480d009180c014002c21500c9241000a4429136640c0b2889001d0300400080c40b0f409c11001c140a01c20205d243d48043d884c0c0e50310364606c41007451080d22170b01080b040d01d003800b0001484103035070180a4040c814501034601c6000c0000e010003c02001c0118841c180a81640309880c0000d4940c141c4900342031042e15034400501c2249003682005415442d80705014258030f9220783c141c0460305884c0604d050300c2e51240c5a05d01941942d00503104a60444010040180031031144280c2c0a43c0902c00ca10241c500b1016600140686025400244142c0c00010a000382136815108200c081c20003a8003401d54545000c09190500401c800d0103032140b8290401c00040000134480b081607 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 105550683 1250 105549433 105549463
    0x30c04050a06030b0d0b0601030b12070f1e0306020313050d09152303061818060108120904090312050718120506010e070e09040b0a050c04050603070309020301150e0412140a03020903 80
    0x40d1040cbda00c0001e594000ca0300c154040e448007504041107000d924400e28080c07042015150300103601d140d071240001c0d80000d00542041c0180303143d610000e00300f40903540f918100e43d9503035005030342003d549038011001c0303484180500c4a000d0b0034100310303100a00d244d1080c0340d40c00ca80940300d030b4a410101e5400d4100300d0141840c0c040030760400141d01c400b8654007001019070f400300c6100f0380e00c5010342646c403464806411b4400c14140803000e500d240c181c01900840e4400d1078a101c40003802c80041080d18025950741d00800d034154044211900c13104003400050406541811406405c0d80366140c07901418080c210910109000044003a402124a00107400c0040d10300a00341c50682011440c4000950310207034054103040116950790038880a0f502980c1c401400607185490300c00382540282040c5400700d82554945666000c035640580005004143e04118805245418903024480c80c3c40403010b00c041c0b001c1c81c0069010030906000347c56003194103090043e40c40140b840020b2611001c1250501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 105551933 1250 105550683 105550699
    0x50c0c010f02010b0402040815180a14120304060506010e0402090a1428030302010b0105181c06060603021b010608061f03020d03030c02061005060a0f14030c04050a06030b0d0b0601030b 81
    0x34110b80000741140c0380c00301c11818109c0b107071240f041c0403405200c450381009850307200d4070380c0c500071a21045400302c0003c4c40d407040b1040010340040244d0550070880302070754103903034500402001d5600583c821000e030f501200c04510b8440640001903c2401b04d0164200290880c1901c15850302c500c11134000d25481964131240000e042c100111101c1c2160000f1401542808210090355000d0b00c04c0e15800414500444800750b0f4400034480c0e122010080410702000482c0080c0c00300c0c0305841204003402c03035960b0150303854600141c02040d11a00842c0348041c1da02d490020024010089985900704840161100c4440040c0011450003a07281e0400b950140301d600c001c404064041e4443d808900040d0291825580c2c1d20b00c46099081e1a882100d4000c2c1003008a07241c0107104081540c03048503141880034200081c00040651034000312022400701100050602c080d140c10703007120300207201038503041c4121840140480c616002c0020000c2c0104c48607404a10316a009403c40701781c811020b05080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 105553183 1250 105551933 105551939
    0x6010807030b010e03190c0909020604061202070b07091a0708030621010c020102070606050405060306041209080a0f050f0601150f090e070e211203070e09190c050c0c010f02010b040204 81
    0xc0000010200e080319041f40e02440081c1c5a611805090074150b00244224205480e010003074034081000e4803000701e8254204a0314001900e800ba42e20700a551583c1c82a21035820f180201c1001035400740c800940035030602c04040021007000450f584440141c070300b0300002070140b07910f100061145000070215400d114101aa03907505501420f07049000310001e12800d41c1d158180700c00c58a083e540c264142e0480710004d0041070508002d1902c071456450540c0350681e03035240e49414001d040100304c0700001420410310a0280400c0300e0303128062800b02500c1294904003645480c0009100d4000c2800048410211071034061000c40c8002c00e0551b580507440c0c50003400040511a61a495a1081c0c0341e0410b000f5851a0600f030f640749007103c10000f044480401040121150802080300c0200040302d0310883c2241c1341e828081d40100b998050100000c0202503400060b926070120141c03c0090034069081c4500c000a12070032018001e003032680c1c00d0107404108078050301c0040c001e55007081c0005000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 105554433 1250 105553183 105553213
    0x60b2d04180807061a01030608060a1d0a0b0a0b090105010c030f0917010209040f0c0f0e0f030304060203120708070c02240301080c0102010b10140a0504080d0c030e030606010807030b010e03 83
    0x282d030b07103440a1035100f0058035112006408a231458007c80c602a0701410000d510303e40c29a0098102d80140d9928182000300c00884520b0300041690450f401306090707041c007511400340d004180d6500300440d5040300560500e40000d0400c18115000750410071900e10020310580607020b03030300180c0003d4900d04094004607082d00d010794440a1010302071444e0650701d0002242600c076264149159a41d2041130004102048410601840489070310808400c140b014694040004000910540d00135503183d0b80c411b01c8901070058020121010b001100042141455004854000040d8100c82d482503903810f0143c0007400080c01c040440380d4100c0040082445000010b607662038010903402403058509030010700c07920755202281040411072002c20307841c1d4000075201030300341c01045241940c03d06569903901444c01d07100040440210300d00f40201010b040c0e0000954403c00d405134018006424804002450300d800200600201955042400c030940e229080e91244c0303903002030448580c2042c0c8102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 105555683 1250 105554433 105554441
    0x30a051c06150e01030c0f030c0203130e040b01151b0302031909091521050a05011a0f01030c0f050306030717030408010c08010f030602030606040b07060b2d0418080706 74
    0x3002c148441d000c00308542c0b090081d51640c24041d44d801c8000d11f071450041d006052800703c1501035020078001030b01e15000381d1820070b00801c180404041c0c3d0b401d06041098a624060700840b01f9124200c081b4204150424040d2214900c052401d1800541710304080741980074000c90783d0003004400065007000d0340c0c0480c40b8030540d54008410440440c48055a20541d910f51190091050994500101c9141603008100940d4060015264030384156035406007107503c9151080200d17481c0107101801410101131401a03040d080c00c040002a0010303078040e000301c14540b0040700300200000095140d4600303001c100c0042c0f09440721582681e0703549042c292030f50024000c0300b940d036180c92409403c2174824a0380504032010703040705c1c0e49a90f0071503c490000c0d60008000b00d070012020080081c501d43c2c42d6000b050114025840001c0380312039007040288000c00c1100041d208000e4090855150541d8244880c4448080f500001c0c043c100c94000040500c4280f00a40754000203c1c2100c00d20280d03401c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 105556933 1250 105555683 105555719
    0x706141801181a04050109080f0304030306060905031e010e0709020d1406060d0e01021e0910080c16020f09070c0506090601060f0e01020109120e130b03030a051c06 72
    0xc0240014030102c440001c0110620380060100314400029542e94165409500e4001340504000f00d11f002d41038454940303d43c8500c03043d42080e14000108000e060f4107100d204040c010516184904502d000c0010ba0340c5c501d41400c0102e81c3c000055901b0700c140c0254480c1400e00b008806480c50305903100f54000080d00413540820306182040e1050f05400e529000d01d5200b1000240050b04140d41c001e10701d0001c1c0703a40000e5003615942000b50720030502c00c49662400c006815000f041d0f4840c20030040c05500302140d40c0d44818455450300b40708801b00080c054807900c1c03100e0041d201e0810090300004d80c00c80c0481c02070a0b0051144801e0201ea141d00400c4003a04c24003400803202103445100d0242e076580001d22458000030221844003060714440c001c050502041407001042026494a44000300d0303c042c000703200481c0d07200a549446042004101a40503111803040248410300340109480b40b2038500b420040040000c2e101d40c0704085c141100c004000a031703030700b0001d081d2100154803070018900 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 105558183 1250 105556933 105556981
    0x70336020a0815010504090c3b04140f25030204090303020301030b0f070c020103020705150a020c162d0e04050303040209010803090a140a031718010f090605070614 72
    0x401c0d2410140039183ca000c8d480700c100c4041e40d19054420360000e07403500818041d003960700340c083c08040c207a40382c0140e012502402c091545c00c244c503201d0700076050b000400c4e5441d0041c5c9030704030a82101080f030300c104583c1100c80400030108084843c0d0210207641000303510a1400c8811001d240c1c1c158055410789100710b0142245490b84452200c02c0c2d0811280480040d86000e00100194841e8001d440003a210b8000c070ba418000000c0400a41841140c0d041c503610b81c00b0030020f880400402c0705524680080c002c40101c1c50908040707248003500c203840b0b000105040e03030004214218104170400280b041c405c401c10181020f240c034649a51007968180d108490000021032044001f1040300c49a50005004145051500b0031071a400b5403a101905c1c2d00508186001020420504841051440c044400e503550040b800945c40345034014a1054100a0203140380d444c0c0d40c4d00720300c00c0303c141c445c3c90a08030344690301440c028001c1d059202540c000c0c40c0000c000e02484c1400071846a650307481407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 105559433 1250 105558183 105558223
    0x606040e10060906050c1209040e010f09151503081e0a090806070807120902150a0c0501061401090e06031c020c0a05010318110d06051806070336020a08 67
    0x164008032194006c21360320f00c045410110400010307483c0c1c03500420801102900104400e005d8412240c2142d010701007440900b0703100c2614604100e210340606010320100305040248095800703a50000203040e02008044500001e03102c141d1a001640500030082c1417030403141d549802c03503001030440c8070b43e1045126520a0402003903070240218465071062020341e0742c0e490308802c2402c044014020419041e60050f1400030044540020003005010b0500c054482d110181a54540b081c01c55440d0ba001e01580c45441502c040c6c640c2c0e0250960040b00e00380d44c00c400160319008000303428903200303201e150144a0581d662200141d0080b82c84040f041c000c03284180e010383d841c030066013525991b4500f0341508107003110940002d81d550701c01034081e25001e4800590300720342d03940d036a0031540156a4032540c0901c840c0400085803040103050740c48185441c050052044100d500018143d041d0500001a00700760080300c0300e2a0803480542c00349800510210711aa41c42130303c25224444849065501405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 105560683 1250 105559433 105559439
    0x8040f09050c2a0d0c02030601080712120207180f0b10020c04020706060e0108011407031103010303260a0203091002090307030303020901110708010c030507080f010605030606040e100609 82
    0x2803103000d01c103658a041c040e02e0f183c00300c8404080440d001d00c6400154420605485003000108210449451252a902103090b55030040615122059200c00e920b81d0003010140700f40603010002c915003e40c000109c2d0702100b11400203904041c0310350030049540d13000d6078880b03801e5591600303c184c403002e0303401042054400d428240008544103128a1000d640405014012803d1650040c0b5200d4000c41c40000c119440718985a1700c01c000380e21140302a91251241d810902c103820754690031078424101041607030708600c1c0c2d08426000511010741809034500a040c42d10030002c035940000b0f1a401d04446041c906820070320002d40080d01c0c0c42039a40319001c84807192041c5442143c1100000600401c10185540c0d4214080c0d03100d010420304006244004060034201040b941c40a881042c0012401e40c60101c801811140c00030b207480704101000d8103000542c0c0045d200726056a08038a08a035481d542e000119080d803281c0c0c0c0c440c0320700b40c10b91020048981d00c5003440100b5a80c1640c0c81e042c000780e07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 105561933 1250 105560683 105560699
    0x150804110405040f022205010906030b010f060c0803130503030a0606090f0602100209030307050a0602071b0b070f020102010b270f04030503070c0c3506011404050a0b0d08040f 77
    0x2800726002130070500083e80c0400585080c0e00b4110b90f0006060480c600c1050380c00e101000d441c020ba0205007980d071078440520402140f0240d80340982500307010301d040e051415000414070301710220003600c4030f6400808168914001031100320519040421641e407030810031000c1e0000c0010348201000035640043c003040307480440c541e50003110300c42c2c0e004102c00c44400b0100c80007588107100071507041c40208105030000e113003400141141801000e0041e02c61170b0909107403c55040008034042800781c1048180720b15290101034588903500070359002c2c1c251409100603401807885031440c40c0d1007810500307110384041c0c00008680d1483c115102c03440c0f864071403a44001c6584016034005010030800d100084c29280715040101501d0300030b1990188440c1c0d18581403291110145038000c00350149124040060f0f070003030f84814460700340402040c0e2980b404152945244c0d000501c64401c0b40c584004c039201c036401d80c00091102000410000d43ea42c200d103045030a03540f02d481b85201d0682000d80010b204c40b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 105563183 1250 105561933 105561941
    0x8030f1e0d0207031d09060102100209040615021506010804080f032a180609030a0b04290105030f0a05060105040b010e04020d020a0206090a031b02120f0d020f0f070b0c03041508041104 81
    0x50410327002010800c041c1240f0300042e4103c2c1b4400303030b0496a03c1d080003071841003030741c40f180d0410030301d4020300702016000214403c40b5000030596810310aa880038400000e07a2981200c1000c00d03584102c83d12626103041c81d03502c0c0001100300280c0c00603c90000032031210804000d0803600001103900350010440014000380e8080c40440641c15045018840046102101d5456100d48903075501c050104e9038240e456052032541080c0414128090014802c038202040781c0e0300b0f010f1074000141400c0da91552507a96941d0305008180c0119180e00702e203085a401501807080e0240300400c19500c1e002e202602e480207420420750032006200e9900401c0011f03030081000c0081c9034055803140c0c1034160041c081407800c4100351049801074526260b5130030944090000031450405000503200260082000030b24140c00d45100019542119281c2c0032086000501c1004603000012029180c0b5415400541940207503030151201c200580048802554000310440c46a440fa2061100038891901403204035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 105564433 1250 105563183 105563191
    0x108040213150306020c0606040b0108041205160c080c030d050403050606240304061407030213090b0646020a1b0914010306050108030f1e0d0207031d09 67
    0x681e09294124800450790040d0014a1044a40c031818079502d58a8004a0f88180d451002540041081c46450700e020f005851084030240380c00c1003a82000d880f0056a01621000305060040000b8004811240018132035101c03500090a400c00310390307600d00d46e900c50021440c814428061038810304d00312801041034500341c903007100c000c14150351030409001882e5252040f1950b4458052001400c0b801c004005510032480f540d400305116807020440003c181c805801c02080c103006008046d100103c8030244422915008030206090841801103003243c8911601408020403110b15070f02c0b034081a580035410560003540103640700d00315034401c9004070340c03141400c40103800504142000c546104202035101200c03103c80b20400d650703025494203c0d0646220041010106801041800501d1161500402808001d0b40c54003004202501680c4522580f00792036410284c12050809050400e55150140b180800c654450042c10060312071442c9000d03110b000480480c40600500303040c4a82405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 105565683 1250 105564433 105564439
    0x6030213030303050402010c020901141201380a080f12040f03030f030e0304080f060a1406150c01110405041b020c0f03030f03041a01080105010b070f050115091a01080402 75
    0x40c0a007503950440182c070000e04140c0c10403508004003400769480c1926580200903104421074186021800d114054110031003003542a4981601c0920031070443e001400d191095000c41300c50b051014400e068071003030a00340f00d0303003052495802003019400000e0015079106220102c03140d9500d4041142d500344140d004030003024055820400010340115541c1c050981d4034103001c0b404600244035140b03182c102e584806156401a02010f40c1d0450a12046400800c8c000040c0310b890388144141d41051800780c00d0070300070a20700c0141500000801d0981c1c266640d040c0080c0a21030700c507403160880313030800e0148031f105034a4a0200705200091420034241007800d42c002d0a2603521450070040704000c00e11180d50107002c104034061040210400541c0304a110340a916800d00400400020303c010507040302c4480e0385010018000c02c1c003070800340c40300c1c158400390b0b4138201d0307102e86000c0e0701401074201800b180c000220310100310720f400c81d080b000c01510541c80601e1181d26020045810120903078020790 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 105566933 1250 105565683 105565717
    0x50411090f040f030305060102011803120b0402030f040b040f0f03020c01090e090705060a030e030409050a11031311060c0604053301140f100306090501094a030d0501060302 76
    0x30019009400c100c1c0d00040500000031692f41c501d000c0e004200b1000d00071000a59140c00b41c06480000e0310400402140c144c0f021415440d10800220403250301a0010b0055402500098108503040142034166640a407000e40001034030b1401942d034903030041c00c4c2408901d0b04003000c6069407400342c0c04c42c4900a10350090159924003018003040350b101c0f0440c0b900701034850407069500d80d820001040100081c190010351445d1a800306401c4072242c59025040807020800d12880191061014907540d4111808031003018202000542034810b00a030844680100710400c0b09120010641c510144000b1011040b514480c1d0094480c030003580d0420f03d020407506e001802980f8a07540c0c55154484007038008603041908100003090b4095800d4910002503d81d85c084c0040921f90190600408803100c09120040b54000741480360b1521148119002514400d06550b0090900201a801c4020010448808052a015a00c0f980400b6035501680e04100000984920910851300320400d0801500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 105568183 1250 105566933 105566963
    0x5010e041a0613020a120f020a1710030605090a060b0406080d08090a0506010f08011505092a04120308060306040203030405100908010c050403151103180709050411090f04 75
    0x5441075402400958100360080c0c84800090781d0ba01c020700e42e01c040b0780c480c3c0c8441d01265645ea0283e03000c0c041182130071401802010350305a0440c03003600e4a94640c5011a00740e517140c90038a90000900d91000c1d10090610051043c500030100c0d110040174000c60050091070000c0050100366203040c480c5100c00d5010310b0007008118407401c94560010400015202540701c5500e07410b280038401e800c032001c850344103841006889070902c125910325030f22012904080740b929000441d4088000d101400c00640790401074104811400300b00b5103079500031403980d2510340381c100b401d524041e0408100c000c600c10b080810f41b140b0703000483c1071003142d0090040d4139041c144130520460000002c0c01d0030501c4804100401c3c1c4040c00c2c0240e2281c035032a556401e4036603103142088080036241007002c11184d031800d0010001e1484c45c0702142da10081c1803030096121401500110703e085001d82c44000c056140c001480208034500184070881c410481c1c00507002d40310446821429070060b14010300c401a442002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 105569433 1250 105568183 105568223
    0x10050f0103020703030906062607031a040206090307082805030a111e03130902090a030201030e030705031204020f030706080708040c030b0702070e070e1c0f0c0b09030105010e04 78
    0x3001c0f4640b283c0790102c0c4403200396899000f560801c3d0840d02c01060340c83c1840403d60741128103422240e002000a014062031a2036600000072114020f40b01d545803180002e040d500e94104564031010080c040316422941c49070510344801e83e0075009100c1145402a210385d4941803101e8901c1f807a040320156190541a503411f40305102038859013100340c050000d1003907c607501a40703403410350410540910b5407105105000c00ba09613468004802681c0b050103282d0054075110f00c000d0076a0b9080c2030000e80e60000d00c1c0e21514501940390003d01c03a1000080080b80c2c50001880c09008500c00e60700c50000f00701c11820035440c0e40c00f6000d5271000500341000641800c0c4194500340d0068010400e0894494603501d03001700e11501200e22030b0160703100220800041d034807050620750242282ca8400d500e83c600f980050b000303101d00407140c8650043c03000f600702031001c501096a42183c1c00081d9599941e40d0315a4000a60000c0206511079441c20000140903049040d041d0b1155a000ca81074505015003562 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 105570683 1250 105569433 105569437
    0x305090904030905130218011d0d0312023702151b030f060918070512070b040303091404180210120c030204050301060b0c06160c150606030510050f010302 68
    0x2070301081010100090685c451002c3d65001d032007402c1d000350740ca52507884591080d15006489030b04000d81c0b0080c0300408001c000e04d00e00c11803400c481c11005240d03141022036040349004441c40215100007541c8520200031482d10003000041a811f140000d91140480b0040c8890b42100c005a089001075580d0a00b04007822a84500d100e030101c100449a02c5043c08182c0048803035000b024404010700c041403503c82c200c0ea502640c00e03030300032641070280440d040e103a000d80e100f842d0041c0307443d5660030081c94040c0404d201500d80c2d5440240c0345d40e580c2c10b00408001c030b54407408410940c41c00f4003c40b682000d0080d15040c1c11259842c4001849550a010042003245c07010001c01c00c0078903121030700300880d00550b40c1c409550356000da20780c4d0030081010700b1100194171604100c02e0801c1074940ca240040340399a400000f0400c0070301420b10f4000180e075000c404e068010016038810f00281c40141042d8082801c2d0783c0c896901308003c0d960110b400301d404510b401581e60003107206401a84562003500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 105571933 1250 105570683 105570691
    0x150806160e10030e010203040c05090a060602070b0a0c0b130210020d08010302060a050d0603140f0601051c0c080f0d1106090c190308030405070302011713060b0d08120a0b01050703050909 82
    0x340001d0780c3e111400c4e1903422a081a5011140c0340e40002080003146401145503420854584003003014902d0410041c3d540c10840c46242000880800e0460039240200e070004a2076411084651261501d4220281c00c030855150892090302040481c0540c644002502604002070f502d405486034215000c00c84c66401134030218080002c01c10011a10165a004a8004510603000007010090140b41c00d410f01c400e00060041a61190300100440c1e51882840c0510303244040c1c100c00c1410130341c2003912900c44150005c580c540301e00d1001000aa800164000c0030003090741d2140d410030113400300e10f40c640c0300545040540380e210702011000c9240545030400340310b2000d26022100d540d255649003a0b50400c80303003641c491300881020000c0d560040d1640c2001035031a00c82c03600c0c915109594014005100402130011569810040700030b813103080c4086082500b0000e100d0311460665100c10001004583c66041103007041550181540204240d90300c5070340c16100e01d41030003014014000c0c03100c03000b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 105573183 1250 105571933 105571937
    0x17040c050d14030d050601090b0a0c1103160b0702011205040506060915030109030309060f02070807060e01060e0a09030f02120708160804060503090c0d08030403080403030906150806160e10 83
    0x515002c0c00204104001e2102c016040c5000c0780d9441c18030000351010311180e10440340010704101a0722404d03488070400341881d40c4514103203044201080460315000001c101e5114442e5500d030081110644240a40780d50741c400da94910007152140070355000d40d403040c0c030001c240354000030105c1c0c82c030303c3c04640c060f80c000400c0c40110301c0320301c0000000c2e003902d80c400c10503070110380d03502a42170074030405d0702074441802400c1000354a007403010b07556011079228194000e08500c0d0341d881c0300b0301c80020a40140008000881103504c1130300f00a0321490060411540880220300000a100d05850010a490810345000c400d214204141c0c0e84814015a000b040090380c01d80301325030008002041040940b002c0c00e0b8a65a44e82c8038500780074020700c0c0400c4902d50501c06c0c208181d07640002521030080f01da000c0c1c1d0616040f0060f40395441c041d00a8000c03240010320442c200b8981301d000c40d032608549021500e2600c2160342503101c034410314907a50003d030119000503840c4028100d003410301000591080380d40e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 105574433 1250 105573183 105573203
    0x903010902090115080c0405010f0f0e06030c04081e0303130507050a03050a1502090307061214010806060a09090f02040b06040902030f0f07051801030c050c0a0503030717040c050d 79
    0x703a001840440782600004001888103c200906940c0f04101a034419070f200c02d0a8646410500060850070801c1a0f13241000b500188a4030ba00e881085050801d6a0241083ea26030078082980001ca40050013451000d2043c444450f084540e522461074a54540c88003451030740d15400c6003840e8800f02c0180c142d81c6807281c10000241503e0343d400c000000e5000b90041c0c49070000c0c0340340c0200d442d886105514006401072100c03d0141c2e5000c24804102c4407070781011021402048101e0016008034034a020341e280c2940000034000d14041390352032056a04403103520a0a490b68440c1d01120400313000076258462081440300142826404514014801030407a07042a580b4112030069900494404695107012018051100e201000164102035641811401e020706885841c0300c1d0108000490304141c2c441d070244400b0785c003607022904802001000c1e502421046e00384169a41d20640e4102c0000384580c5c3c408010601c210701140c09968454100c1100d40d14200030494265000203080d204503240c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 105575539 1106 105574433 105574451
    0x6150307030f0f1d0d0f050712020a0b090c0f09060105181f030207020f010e10081b07030e0907020105011d04051207081b0d0806010302090301 63
    0x1051400044010051012402800000c281000050701d86140d0081c0780d18030110383c4c5004000c8400b10f603c5000042d00444103002442c41e104002041446604001003030004100c68071461071040b110851600d40f2545131012064403d00425800620000c049081c40c8448541c0c140c4225051aa5845c00e000007900b06e100d00b8416034a400d01d031074030b200c0441d558141d06040700b54240d005581c4805403503501500035404901c0592083c0840306244100e58070030900034015001c0640704142d002d02c0014207403002070b400740640c1400d500b030310701a10080c044d110140403c035000342d40302c0141c0351005046c001d8411011300b05c0340859040c06d005001c4c41e044148586800d94000801c07200a03916402c0c41818803046c0301002d01440c00006000040c00f1404014100e0f039012600c580c00781a034610812030781c64921200240c00b2940c2000001c08940c041e501801c0c24081c041c2c000310324458 = true := by decide +kernel

theorem cover : BRFrame.Cov 105395683 105575539 := by
  have h0 := BRFrame.cov_init 105395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 105395683 ≤ n) (h2 : n < 105575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
