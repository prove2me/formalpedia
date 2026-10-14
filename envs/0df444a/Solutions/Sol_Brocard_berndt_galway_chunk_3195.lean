-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3195
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:56:50.587509+00:00
-- url     : https://prove2.me/submissions/126385c4-8886-48eb-8a07-2d547816ff75

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 574460431 ≤ n < 574640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 574461681 1250 574460431 574460477
    0x140609010602071503021909140609060706051302270a110304060525030b03010b01020a0f110103110d1b090b1b010605040e0f1510050f130615 63
    0x1140058100410401002809050a5503840c004d82005400d00302030361190b4a091501c8000840040c0c074a450810000038192000020100241c801307e18000920700816400d100d6400c0040190f5980c400080751079034241911001c49500504c0301c0019805020341c4400e441d030190040b41c0c2c80000c5800b1030001207040c45418501c0e0040c4504505503544c40d15810003c0000800400c00515901c18010b01c1c006c011580030804949601e000800240101c140f41c01c44031500109415513211417030ba140411290642c0710700803a0710103c0b01c441c0c4007030400104c0242c5040d0000d644000705c08103903071804d02e040d60042117510118200003001078581c3c1008072261513861180b582101d0b0b0800c000041514961100080c102641c400404e880b41e4450124007180c00d42c4101c100c0541110380100b401180c04d002502c1210902186100b40d410014a1549074160603c14144121050090b22050384c076080b004545058900004002960780c0710319442002e0030120703400001403a20204810b50b80610454 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 574462931 1250 574461681 574461689
    0x50c0f2d1c050f060607030207090c120e0606010912110a0303050702040509280609080309062505040527090610060201141f0308130e0601020f1f0b03030d14060901 72
    0xf03c2600e521080e06008030742d440b8250980c1107000304840031030000d2207406a90030103411a0380d030b803400300380b010119000c450800a000100c2d4010006204180e0f074040f41060a642c40314046040e4446589000708071035504440702c40d00400400d80003c00d168001c0d01034075006e03000391010701c48c9541305c4040e20b40700da8980d0204100049161340f800340d4200e1045c0c41204072403003150001880512a198001150000c44008865a0003142081401d0240400742c07205100500b2403943c0b04044018007510fa40954041c5034003800740d40e614490000880c03c02e4541100031200121103604109040c40d0f280e09086680e08131408503030400107030b407501c144141c010149080b181c00000742c131140d0304103e0440c480c000c0c480010360105c10200110740000018101d209107121002c401d5450440040c6004000518190541d0000c000c0442959404506003000783c1e8070500070784618400410305c1005004007141c081c3c00d40300100d4480b0b41209654442d007541e00204501c2001b55031461304203c005502401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 574464181 1250 574462931 574462951
    0x80606010c0b13060509030c01061a04060c03091e030606051c020603060d200f0a29040f0b040e010504180303020a050d290301050c0f2d1c05 62
    0x712100860303480408150030100807070f0650302000040c1c40c1c601c1924026074520f01507420000c0c039044901001d10509004055a500152100e00c180d05074101c1c5001d00d115182c144031410701e0203410184a412100090032821030702000c0394000841c81d40c269606400b040310002d02d0420041072901d40038800c41010084402c10b40403114256080c40000c2d04080e0650350480c116002c0480012035a00040c8030102d00100c000b05010b0303140c4108080c5031440c0510034050072510303006001e94503410005006480317880326442c0040225080c4041c80d072040354480080b071031340c100000c1038111a2030020001c4a4804880c1c0509988070b40410007128403030b10710803c8000d006079049001134040d4016181803003490a03c582025183c04480301961100312400510030076820200c141c42240b21740880290b40c069000304030914040c08184414400c1100c05840031002007500c50841003011401e03040c45840c94060002040c0111203250306400c650302c50650700408081030404d26101d40f048a200c0c4084034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 574465431 1250 574464181 574464197
    0xc0303090409050a0b1e0601210c020a02152109030909040303020909152106070c0f020a060e03060a0b0102030904021b1515010221090a0906090f0608060601 69
    0x3008002c0803604011240c50092120100c08102c0164240c0e1040b5007203994041040c88900b441419030400601a50620409880c070500368010b40b0481c3e010100710b444001200f406070281a1b2501c00600802036014050070214004c2046200c041d1003008404a00e000c02007109100f01031030b050044507103541a03031040c00520720f1440c0c201100c80e081800303801c0043c40c0c00740901c049021401e080310814800303e81015411000d04000c480180345503003510000c05590381c81c0d041c140d00d0340e4014201100700045000b11806001564940c400742c1503005098460300d40e030b10500a4035840c40c410a05200307008050000320b0780321580c0100e0042c000c05902451074007d5a80c00c1000a410403901240c000340c200d041410b085004200c0f4422801550b0701c03103042460b00003085c503d100c2c810043c070350464100d904600d07210000e079401c085e6200307407060340c8a44032410b100102c0c03150b40e16540301c961078508060300014820900d40c00340381710005040040c08107549640705139613101000d0b602180010007034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 574466681 1250 574465431 574465447
    0x100e24040f080717070f0213090b0a0e1203160201110f271c020301051b1c15060f18180e03040b07080d0f090b0f0705210a0e0c0303 58
    0x7000501d4007a00c28441340102d803c0c161580701c0c0503082681d045030300c507605e40c2181055203445416108505ea0b00d0340140549551a980c0780c0862101415844c2c6c283c0c1c541c130071458003240c103001d002e100464030361509441c0d20307020030b486203041804031040340036518000380702a404c100340044408500500300c0f000e1402e0b840d00d0850703100603214242202080c02440d20501c49940341040304601c0c1c00e4280c00c07030303643e403100f80105800c5810160210b010000c0865943c65118900380a5401105d840041c43c0d00c944004025000640724464100c8181c2c110250302094558000f020079402001c0d1b0b0361042d1603041c3d000c0c405c120341100342c0251020950070140c400c040c12459000106c1e203a60384410f4906080d0f4841d58054103800c59441141c200e1804a041c4500900300e20036900384d8039200000f403007425440e845441e00e0705000f500d1f0454004100000602403401842210007402e09142042e9241c04241007030320038240256030038802503090946c2a0144103000401000a01c4020042c1d860813201c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 574467931 1250 574466681 574466693
    0x3060a0b0c0a0f0204060b030f1510020c090603121201030507150c23030a0f1b0c2313090203060a0506011409150c030310080a0302030403020111100e24040f 69
    0x58078904176402619034401051700141e80700550b0194188820285c05810501d403c14811070301c2411482c00b40c6540402501201d9000405400d050003d803840c11880d16140086800d01c00f030074000301074000c000284010606d8100c14814100c0c0c0c016820b0f1845561203160004210760a200d091001a056a035500b01240c3c1540b0a100003000c400c01119107a01d41c1c0c02114195002002c0441c0814100d845c500b40030754009910107190441e64030011007001d000d68030955000a180244411403141d80040b2048603041c5210f10901c0100611084030500ca080c40d070b030b0180800b00c0c2b0481c0a40100004510141024040c41c0c5c003ca10584506410148070718000d00c06411015a040d4032500700c3d049170b0600841400103050462036100a980d0300d1400100c080760002c195070003442c4aa0000882d440442d9001c01540c0030b40e41e091801d001965280c1c22002d15102c50f01c05a0f4035054a00110401c0f4800e0010302d040389101da031022402d4244c0c005056070441801110058150201c2141c40d00000d04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 574469181 1250 574467931 574467953
    0xb03060f01050c100606171303050903030706110a2a0210031103100f080604111009030b091506040c08010314010e0604030f0207150516020301061a03060a0b0c0a 71
    0x401032410350305000140f44601d29010607241050b2550703540791820b1016591000d00303644511400042c1c0c1c0c0050414000000e83e02d0b11b0070f4005410440045150340d03071070381d00f442101d101a403c01d605101c501203074a840612035012001080204038500c84504181c210400400c03508e0203180d554003c00341c002e4091016800f1040006000c140c2d40d00706800c0c00c14840310180d4010034400440c00240c6003840761000380800e03142c001c9182035210408000c0011403040340282c801005450700084103076146000d50b408a00ca80009001c0c15150041040440c0c1c0000c2441e01d01c0c040001520441d110b0350107001c12502e406184c10001080000103001094100c00c148079855018000018066800914242800403d6408500140701602e241c0030240c0d0400c408009020340b84582041c4c03080d80e110240040c45400340c0c602c0000000380325001950380030361000d4007c1600042d200b68480303042c1d01c0081958404c0303404d40d01c1103580f1240407074180035002c1580c011000500041107a40f083c2c1c0c5a20311544 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 574470431 1250 574469181 574469209
    0x2130e101b180b041205070501020a083a0509010b04060f1a090d030206010e0c0a08010e1312030e0f0307050304270204030b0712050906010b072d12090b0306 69
    0x40c0b200002c0c1220401d8020001070864107000300c0d120300c2c0e519190303007071007181e40c0094110350090300c1060106078000e00300c405a402400b0b40000d240d01d107880c04e04540c0c10000904c81074480703d020b42456076840b5001580715400160017040100071590070030040b40c00f28024640d034030f44c101009101c950040f5a110b00004000c1400b01d0030240200001021006003c008800580105004000c115190074010790020b0030350450078280544007070f004000c03e00500c1080c50451689012035040144a40e00b2881260045840c44100001d40400303001b43c030141e2041080c0d0301c10040c06286113040071041e2055241d00c0720255141c1031a090240c0d010307602100300a145140c5d007203c00d0301d101080e84000c0000714810030101402c0d20b0308401c081c0000300c500860302404c3d402c2c5410000203100c089101410350f40204040d945070181c5080c850000314800d814111000f60009414011030900c158200c6120f02c6003a20f404190103600081ba80600d46114060f102c001c03e202280035807914000c0c00d40d0b51 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 574471681 1250 574470431 574470467
    0x80c0d050d1809060609050108070503011a0307120603030315050102070f05060306130507030b0906061603050f070c1e0b040803030112080904050a06090b040b06070605060a0302130e101b 82
    0x210f48400311607085543d2a07000d40c0c080780071400100142d581200005600c01c900b0b04160342558034048520301c14502c1509104003c0c8400400502d050f030059040590121044d0780400250784c136031402030003c11146100e40e500e4203181600141d203620008000c23085d607280340d5001442c2c0d498071041c80000d4001a119a901c00021644080595928401d0302e12465984e03402003802c82c810801d01180030707005889117004a20070080c900800b806403444841c12a4545080c41d612503882c02a00c00358040d903040101245272091002461080c0c1c00c0b8442c2c074000a140300460450741e241200720813407003203201b400f0180c0c05c180010852141e441105444541c0034402c407910f000e9006000608403901202c041160980c1c681041c40010b88ac1c5c45180e2b080141580d04202405001000401034024080000e0070345443d2400280303161903100c140d40003182d003d40424500080303a50403401078904222070480910980001400442c124000d50414480e030654150303003109884011600010300f00c01036012 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 574472931 1250 574471681 574471727
    0x10050702030714060106080c072f030316061103061012060f1212030c020703020f060408030f180a12021e030706020c0a1418040303091b080c0d050d 65
    0x20943c0b518841906070500300180809604200024203409000342c4046000602403002d980001c50180164280901800007004060f42d01801d10000040150200c1c0d054040400c0400c0b641d00841c00c80c94a43d84141420301002c00000340420040c00229841130340555582030010318a03018080c0f03804d03901003204000c90566201ca1819084101e198030001c5010110200d00c8140111b040e03081c0340c1c840e1f81e4901806825131842000717507121154000a44076001c0c040e001c6060380d03a000c0031100100024000d072a00e445100900700c900b60002e0050100303004180744c0f19001840c00d6244d250a445510041d080c3c1030140c0c0d002e1094a4915111032584c400008840c82440c2ea010002d140040c400b5500400e24045140e050201501c0c3c02e81c08070584051b2541001030a80d25120306043c01c4400030400d19140d600c41c1002c0f005402041009095581001c2e0040d8070300712200002c1d0140c4101000321511442d01c10140013260014503800b4045d5000680f140b40124840c40700c00c800c00b9490000740c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 574474181 1250 574472931 574472933
    0x16060902090f040b160f030e101404031b03020607080a020702040e030c100e0a1101260f0c18011b08041514070807170d18050f0a0203100507020307 65
    0x5040010b8400704a05145001088200243c402c681c5a00c190004001c0901889a510181c800ea010b81075503814144c50b621b03101304040040140c0012202441010320440c4100e02d104041d924003510140e000449850740040201c188400380324400358181e00a100d00e0759030860448132070202070440d550f1183c08107d0344016030359a00a9004050304400915900c00703002900320324111460300c0c1e24481703504200582803000004203210f26030b2900142c509a54180120040340e0141307901018100d0700c1c407100000b800d8102c001582d84c0c410081c100000c0070580b03445000e00c0840c01000b440d00e07490714140ba00c802095104200e078032066811340e81c44030003001d10359070380c4411a041074002140340ca00b040713080400305030b10840040b18628810b0340d8078944801610f0b4122180700b182000343c4200c0b20605801020340c8854126030b901040343c101000b805c140c0a400510303202c012101910940301c0c440300d281440502050540195034010300502c004168601c0c02000784c00010320725010f50005028100c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 574475431 1250 574474181 574474189
    0x71a1e0103260a030e0c0d0f020f0a030b070804030f05030c0a0c0507090c0c1a061003091e05030a1e050909060409050a0302100e0706050d1505150a0e1516060902 71
    0x81a050703200800d001700b9000c21a464041d003980030300e1081e035412030702501144020a00f8110246c0650359840400c881c0008550704101d15440200580c0d9008200148a036200f2006401544281d0300c0d24481482100e00310307028042507803622403041c8100300c081c2e400c41c090f10114105910880070790742c03a60f0f40d82440c8001c4804044800000c12a921610300c100042c403600c04951020080600c03655041c4000420500d206d0401c3c10814155600825424082d4030b020710781d403c0380c030208260306101540ca8060340f25004040000c02180c00c0d001590314082d006540c0100c8100b0310b6442c0740c1090b500b501040307014100a01210b0f085036540b20740d20f010610901c402075086002e900149000c5c000c00c20382004680c9900504145030700711003c18403806078050102c0e00140c00f1040003144501038070000725069001540040e13032100680d8802049004000041c11600d8025260712100152450901c051100c81010006076500108000c0911145010594407440d01032000001e8220080e800301d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 574476681 1250 574475431 574475437
    0x120a0902040e0a15050126101a120f0c1302040906030602030f0c03090a02010c050c09360304030219120515010b120109050912071a1e010326 62
    0x242e03581c1054084800380010010765484802c00c0c210300b003160b589030000784a48221690041d000c4074507800f003600000c030401c00014240c0e43c002e52003040003541c86100c1e001c5200d102403000380100a05030701d12404042c0820343c0780c00000018043c2009a02030001c01c4500400111242600756090001048696092007042e016611602c0b0040c0c1e41d05007a00740291a103001080345110480c100100f00ca5804040340c9460907560a00707000e40c42c60080d143c13090810241910064014981104021802c0c0341c074141494280382d800014036000c5030f00c076084800184d4603280070801c4d82c8200010401401e1010380f041d81e058008032124003440d100c0281c55000807880d10241c40c9913001c1c40a2001c0e107500740341c00500500403003041d18600798141003010360003a0148609141030342c1d41e030006107036640705220200000a14000c016501c121600d407600d91140e040d111310748038071100340001c0c0a841c1403800042000c44110340703490030303680b071340c1d555079918207031070440713140d40c00592404009550214001d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 574477931 1250 574476681 574476701
    0x70509190b03060f0a081902130c0c02010801140604030b0a1b09051c03080a110405030d030207061103250504050a080d0201140c0f0d110406180e010605120a090204 72
    0x80c0582d80d040450810805420a856041c407981d2003950400400c50b00040c207106600b00d042c024010014180005400501c940241c215030a041c0103480154607400b0504514a40c400d8035000300300d03600c030b015860480181b1008160001d20800c01400070410207003016500840140010503085031100d00984540040340d146004150300000500c154a81902c0340090340d40c080503442c01034419520000c104020140654860a640d44904203e80c0c1002046a0103048090201d032210100010010002d52103010700381c5600e8508000c903031400100380d0071a400b0388449001a1030001f04421901c0c4035604200080040c400100f20004068681e40c0a00d0020108078000d45010f1800300006420f40e0012003070b0b074008100c540c4c00c000040c454002510b03480a506221107484e154140015001040680200203001002003070000e00130791301410351020301d1041164a509142e40d0300309120010420f00814010a10501910ba81910681300c00c40d4002c1c003000010403032041342e0300820202e85103d86 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 574479181 1250 574477931 574477949
    0x20a0b070501110901080103060b030a231902010c032a06020a03050a1506180b1b0706081005090c070c0816050d08040909020a080d050304030e01021507050919 70
    0xc080003840420302c100d514840d062400c070362801c416000000c00c4240c0500000303100e01c1d070b40c2c1400c20207601c0c108858004150700c810b0412022140c0050380502d050308080c440c17014441d40050b000082200301c0f14918141e07041c1c407600300c07100170f42e0303029074108000b10900311403801c40c400000800310501a0b024403143c0160030040c0e07500303442e18008040d83c60041c810942d213400c1104a80400414100440c00c45280c1e03d0700740e81c01c402d00800030b50140c0d40766002a182e0382e4042044200c0010500003072909950810885e0708490f07541c4400d444542c001c407481d0f01110410401041203043c003400f2071b035200101ca1030441c5480083c1c0c1d56901c140c007150700300410aa01c2a10380c048032218422084004e07140444081c02903139001c1d91000000e105c1c030f02410002c0c0b500c131802e240841d00c4102d00c17403025102600c252400030302d010700010400d40084500b5000502501c14a00c0039500120f962400b40d0602c20800380a075031021030650780c81e44048212a04030800403480c000395070f03400c807948000d010080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 574480431 1250 574479181 574479187
    0x32106090b04050a0b03060105090717011701060602160b0703120507020c010306050102030903061f0803160c0b0c1b1216030b180715020c102001020c12070f020a0b 72
    0x4144012034400030182881a454085e40440c50303134000070981c4c1111421107106071965a4404115920020825a4000b180c00da8001064140e266008521100d2140b0001c1021982d00d400c03c070781c0c9006160103107c890445960a000e00300d0220001c200f940d010b0300f0000000941c0ea9102c804980044420348010b13044510b483d442d40da030500421009040c02d00c01142424503182c0029201c000c050708503a401240b98003000005a5051072083c01042840d06503a112401c201e10b00078000c50307098003141c0e0300c4e50685000c2541c2c0c0602098494010204c1d00504c8010008a0f45007104811207500a60000c0c0e800c074401e003084800c2020100201210001c1c1030007614500d04224800c001409900b9190184c0c3c0c8a65450107000440c01c0072070341e80c5004003804c2c0c0c4170860168241010b010304580c008022010404d21280c0094002c2d20307400407201070400101e40022034a00301e0150a0f4000a140c100200b078042a9503000b01802310180a4044250003c0c0c1c00c1c3d0000340b1041d43c640c4a00e0a0544c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 574481681 1250 574480431 574480451
    0x5070f0804091a0909030a110a0203120a08060603100524040f09050a0b0619050705010c03060509060d17071a0403080925260f06060a060203070f03210609 68
    0x5401000b440d00f60a9810f4050303802c10090180d01c034001c00354200304202c000f401c81400544100950140d040d009070641d914100310800c0120190b20240030380011410440201c0c2407030824004891142c01e68183d01d0360141d0170300b0100302000d0766102840c1681030049030107030b43c0000034500401c000e003602d0105549891030080ca040503548014603240d4100e1a04180307150a89a0302e0482c0d40580e103100d8800c510110740301059440d4020b102d00600395610b065a503c02040d09a444842618011102c1b522184e80703110401c0703042c10340000000c1c4501c0140700102096880031000c0c082040c40750720b500c1c0c1c1092112155445248040714140c000a11b1601807102512081c0700300310342e40003600500290407003060301c1d0304940c045031f22955003445a01d400050703200341c14025441d04a610342c2c040d1443c05044044950341d500003070714600d110b8401002c000900d04e0000040751016903100313103c45801091901c1c103803421030381507041c50b001c5005101d11041c1e0015500ca00d1010f04420300e400038601d014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 574482931 1250 574481681 574481711
    0xb01020f060c030a0b0114070309030c0b0a09090b010903051504060606050720010e0d110f0d15020703170403030203040c1d060f040209030109050c090a150605070f080409 75
    0xc4050406a107410440900800500001c101da500442e03011001c16080b1601004070b03201e003660703402002880004192002051741c081424821130380500c01e91840b440d1148428444e0f44201030301c1e00d02107000303501c0411a00125070405454086d05040c1600c8165603500ca050611070f190320b40c1884c0420b071408110800c02540320b004090103292800030b0074010b4a40c0c030011100e0340d644c003034540400c1030356610701681c1c4100111080c8910141c010b02140801d460440d4441e01004034a074401c28102c03940c02a90308001c114074a6164004102006074180001000b0003507000b0002907007003080041d41c6d00646841035003524001d0344280d40050307803071819042c042c0320341c40c0341d400c042001109901c0d010070306101c0300c000070740107201115000820407205001800074495a002e454065080011403000d000d0007003200103800d0416164811181c1d5203104d540200c40e41e40103003504503110f449050004604c00d10141400710312994641c620390180340c1381c0c001e0b5600507900c9000e80c151904d54802c20180c1d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 574484181 1250 574482931 574482943
    0x909030d091b08210309030a050c0c06040803130510051218031309060f060905060336060a09030c0b0a02040f0b0a0f0c0209070e0402040f0e180601060906031a130b0102 74
    0x48010065085003000c011b01a224410428404100030700404c04400141c0306004907020694010034280e0380f00d5407141901e480c1d4102070b00080075120080c50005442c20b03c10001c22001c3c200395142450028048000c0d82d40f408090103134858607045402480c161a01080103015041d1840d80280c00a86001d10980c15682e864020b9a1a01d4201104210290f0000560010740740202d560544940d2040a490181501c048600c40300c4560f20ba01c802c404c004040040c406001280152501d030741e10508414203039460106c0007030000f60044150404100421107054100c6c40800e00946402d6603a8540d06182819420110024030002154240150413240f046002486801c042c1d180c2080c1d40c000600006e4014600c900740401c580300e00210365140d43c104c170082d00e00112582602030300c40b491001c40200c1116030340030081405000c07502c9541e001920341d040328280c0da0361000302030500f00100c01401a1071014030b1007080a0582d07500540d12035070310400d09646044000380c000741030800245085 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 574485431 1250 574484181 574484233
    0xa2901050906040e0c061617190809032106270604090807061514040c0806040e0102040f1514070c03110105040806070e330a020712060b0306060909030d091b08 70
    0x400409c0304c00103883c2503007001c0c08658541c3c2008a01c40c2d86010010b419845103000e00d020300307402007030110841d0750344c100080c1c0162815110f50385582c00328000800c40f46013480400304c0c2000301c0c00000d481131815411500380540329405080c01c00039a82e440a080d07580c0b0324505000300480380b130140113402e645020030f00b00490031a000c0c0a41c80010102500c511009452140165203613115000702c09000d4040ba00100522003070b03071844030356a905c84440d07440b1907422100000c052a003007103041920001903449168000703400404003440c2d65521804581442840d42c14042d043c8000211001c00340800c91213a0441d84441e40074030080020010203211030ba22000c182014039400d449102c04950000302d0803d0000416565114071060583c41c0c0b81d44c5a21440410015032610420014141c100c03603480c0c0c0b402d404070740351520b800040180e000700441d6000c0103944207000c0d03041285d403982c0145103a80d010360b2040c8800b8200300c415a4100701070390800308266106241003e101c20b90540907000071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 574486681 1250 574485431 574485473
    0x100914060906191a040905070908030319090206070609030e03030a091208070c2304050412120e060c0c060124050f0c0a2901050906040e0c0616 63
    0x80e26204000514082010b052640680084203038a00034000c1c2d403420038007800c1080300c25070610165a40814a0307030b001d40904101c4500f4500851620340c096901c1c401511207407000386007159121020445550858000b5042e0f0680390030203c800341e2a0381008268080c040c039008180e0b900a804c0140c0a00950034603035010341c1c0108a40780c3c5039540f0108110643d101c4100030560350707101c1d0130a6401230040f400044d1502c0400200003414030580424036146050040d001c5c28282166000c1004030b96044070007034208149424402c10301e07807003680040201c040180001512080319601945000811140b00784000e030002090382100008001c40d0740107142c480381d41000c0850501c0c46a400a400354180010301c000841c658800c4d40555013038404449180040740e412251b01d0503c120b0808840c0c0581a244540c810f441417155209030035141641c4001e00320511a0700c500c4240001040035102144460244501c1010250b03214001080d03031448000440300c2074901428102420951100440c80f8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 574487931 1250 574486681 574486721
    0x90102093f060a0207060b040c020f060f01080606010503130c03080d060b0301050f22090804090c0201141815040f020f01080103051203060d0203030c01060609080f0a060b04060b031009 81
    0x4100c0c1d0020782c00341d1025251402589450091900030081d0a00e814825882420a00e1a4a12660001d03454030f007200d564084440e42c0d04d41606c0005d88000a004403074140d00600001001c95020b0401141c000842c3c4500480390042e5403120b98480a09400441f001c810014680507001041d01030540a40384190850303280d03500d0200000c0030301c480302c0180c82c0182881940140500e02d039140e1020691003141080c80301014600c0e05815980c0640a01c0d2140da00e40032030482c01ca40305106000d00945401c10007e05030300d44604e00021088501d150910314030888003440c9903070408400d414040c510540ca142d0703000400c1d10400c0b070341c074420040d194104200d003c01007002c13440018104448402c002c61250f40e0380c9406005c0740c0c10140721007002c1d400d480002403c00e889541503200348208c840c0c598a450107541c8491a264591008410581a81d801a03520708045070745070340200c0380114018000292103540d030280c0b4016800450391220312611081d420400030800d4016040d40c008081d00701c880d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 574489181 1250 574487931 574488049
    0xb0c0f0d0c2703293102010c030e03120a02030702030c09070c03050702030313030b150102011b080901060504151a0f0316022503030e030a021809010209 67
    0xb84090511000c1c0030504010000c81070480032607122101034841e84a118001d2800340d02d2102200e240428843d980043c174844980b981502c010f80034011607050b564003941c0c080540b8200c039281c10410002d40d050040c81b00c103800c05466071000381300d102069000381d070711004e160040605040035101c0c035038021581d401c100220603921542d500500b03903040c10120303102c0c4014000b00781346000700c2e00d1b650036244503504048180f05c58001030034410b090f400e000251070031000300120301341d60b0106042e00c3c4801c0620900d0fa10305000344039865001038200000a1502d035141d001130103071008680e4144802141800c18030540491541030180541c1c03003610a0b10f400502c3e101024a840010301622000d031000c076840d0901403081c840f11007100c850032200d0090780b40e2480c1100400700148000c178003099072200f400032a400c0106180040c0d41e0000c12000400c60766032005010141700030482003455600308108007040d55010643c0520380c6594420f0140801409084521201d4513108030082001081001d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 574490431 1250 574489181 574489247
    0x8070b190306050405010b0301210c060e0102030904090305090a060201050c0f0c150a1505090609040b090f060403090f0e151201020d09060b01030b0d0c030b0c0f0d0c 73
    0x100c8804221100c000c00490031801240200003980000b9401820680009615021030000c2d41c103039000b41c00340d4601e140d0301c540f01318002964004001c00300441010300300300d4a80106100600c4500c1030041d070b8505105480094221410000c04401003100410392007021306005c000c1202506060000f04041c1c2401c00440459008803900c8000710074000800c1400758009010342036100720702822038040d90a0000b80c04020b0304400c207112680090301c0344000359918054129500410000d009100180c446031a00c0841150061108601707100394040b1250345141000300d144214041d90381c0d450b0312414400c80b0707000c0102ca0303481020628007210500002c2d0400200c0c2c0824400103d50800307169801d070f083c003400390141e40904038090340751216800c00d110072500000903060090303804106840483c42084100c1011410103040703043c03c000c0c14400100940301a5400c10a000c000c0c030b0031302000d1083e2441c1e940c40340a000341d0741e80c1c490301e420f0f07401504110411548150f40410a44200e000e02c014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 574491681 1250 574490431 574490437
    0x32a0302130908131a040b120c07020d030f080a050f060907140a031a0a060c060207020604030609050d1706060a0324060203130506070b0c0711030f070f08070b 70
    0xa0320807061061100364100041c1c0c010781903036a00160341e980703660b840802030a0380c01c035038400c250343d4103135258241c03400300d0240c0211401d03505000001c90400d8400030401c155000c000741903034074000d0204401c40243e65681592031403248603680b5403405800e500e40007805647e01031f126040050402e024001c00500f0208e4003984450180c1d0741504907941e048007114582c02405041500c25400030325850f15070b41c1034000204803284880c000c1c0b104104103042c0140250b09100f0200081c0f0200071800c0090050340040c0304180c002040707541029101d03101c1104556050b8011203040d44610031130b00c1c09030782000c081a001c080e4004810b13070f40d20304540462400e11074420100e08040da00d0190307240308118216510b09030f0700b803684086100394840f00e002c1e640340d0060074101492801c0c01c0c40050f1510300682254462680807035180c000751a03403014002070f600650800c40c2e140420207120714264030f041050614034411030004050f81454070740b034540400324540003c0855004204103001c401c0e101412 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 574492931 1250 574491681 574491683
    0x2210d0902121621080d02070c1509170f210c1005040506100510050a03060b040e0106120525020a0f060f180b01062a1101140901211d0304032a03 64
    0x1f50352a8854942040347d103040d90040300c148490100c502c2010381d448074601003650b2650501640312980340222640e40d540320f014070fa5a40c2c0c00369440d0408180d280e20205800031040300d0f9035041c03006404074030b0308191907103052552090303a034401c01c400d00c00c040090301c0c0c0102a50300707143c1401e810320011881003142240e0b86d0050190026142d07500318817980c8414001c1402440362a2a551651003410611000303200d80e400103203d60010060502591241a008005d40030000b10103c203c0d44400300440e91107002a0198000d06010302d020820113941c0044092040c0c80c0003960074a00c0860f4400c48039483d055180d0b9509991068000503140507900d415543c55080940380c0d1501c0080403a8943c1c03015240400385400266110108000501400d2030382100347c840940490000002c40018081d802581c0c0c00030305030010031441204107002c224041da100755004500508a048488040701800b2040c03491980005020070030312403024982d04841c0e2400d241150030043c0d00111401250030303400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 574494181 1250 574492931 574492957
    0xc19230f01110d030b03070305060a1a010f050307030c03060e07022a0f09090a020d03050a030605060f19030f0c0c02040b01050313060c0203130e0702210d090212162108 74
    0x200da0015990304014800023164000200c80301ca01d014007045014001d411400001c007207080b01d618040358065044480c0101040e42c506041d0b9036440e0041f8054103240041405069807510040f518508622080344a5075194006003070781c070481c1a81d007215204043d90390152800b614500d030156503880d1000e143c000c00840d040b040c1912108210350a0800a1500a41c0801050020300030590810041c000340023450300c040109a544400b40b00003445900690f1000c44020031074604010505442041240c18902d80059003040345511074040303c05c500304000118107000c01800462909001303c0f80d115801b0710f4130a0460800714240d42c6d022022900081c005903c80781c600d40d00da403007041560070440030910701311511a40c80029804001d81501c035480140109000321040e139201601c601a00340042d80d0282c50002c900b104c0d08010f00b581202243c0c441e0000c1d02d80580040c1c1004140003902c07500290f50781c62441c0001e001d562150a090340d610320a40c0c40d51000128540314251000104692 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 574495431 1250 574494181 574494191
    0x150b060d020f0c031b0f010b09040803040309081e0105010b0a05041721091f02031803100f14090a1a0717010902040512010207050c19230f01110d03 65
    0xd040c2c0c4802d8000c3e485010010303c008585400d6841d10a80090b07105c0c0c038031200b52403480d040902c07030fa404e80e030080403281d400510500119000072071440086034480d001e45454074010761035403c1c1c1401d110141104400303112800030140c40540f002c2c401c0d90b00500400c10070924200c1407505c003601c039001d184120321801c50500080c2c0545d01042c000001007018404006407840c16151640c03105400c8940d540e806419650038a00183c4010881c1c07000580286c0c0045060000548006040c121040320a0760940a600c8000e201940b4a000d0f12941040d0000041409844080004403d041c0204104202d42c0800070030004600e100100c001c84e030784000844803ca41d1140c5080d109460100500014071841000014180310705502600507504c0c101e48094030403015042d864280d000f00c0700c0244c46500141d03000446481c02e9915031190501c0c031714410080a540c0d5206115801107500700f00546404075462450914140900b860041d8090030010b9510104021065544002500c00710030326680b8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 574496681 1250 574495431 574495447
    0xf02060412140c03043201090e0702010b030f060114010804030c0b130f030c330905010b1008071e0f0e1315030b13051009021318150b060d02 62
    0x84400c0b1020b181040e0f08880d42d480c0e4504100c103d9501d0310720039a4140748840b0352203043e0020001c070b40b00801c1d0142e682e0f0703000318108942d548418038041c09610556507292000d0000340c5007401058218580d01001d484c0a40c906503842c50602d100383c18407410800b08008100009800803500c825064021040d041150b0354403615030b041c59405000030303000401600c05d0a0400d0b9204604502041c4030b0f00c21492000303100c0b94003801a0724001d885420001c6042800199040c055002d07030501402031001240030384c0444003088003070106403103410004880030b04004480d50400e459100c80c0a44940c0c4407000f2110080040001d10080b00c06001c12a245c9180041355844485001d204207020b4010070401807021800b07a01c080591104807000040c0700300113030740400d5030300030100300c6500f21020703091903030746050788000600005000320307800301000e48488001c1d01140b09181e01680d1880035184075032000d0620b07104c508030202c0002c0c1240c4c01d240302e18125403100d50a0f5403070b40c00448405a111809 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 574497931 1250 574496681 574496717
    0x60a030504061d030a0921020415030f080703090b07020d0f0201020f0607091a0906030103020904170307030504050f060103120f0234090606050318031201090b010f02060412 76
    0x210b801c20040700390304034100b5824040003000500180b0051b88400b844595204151400c080340030300400c4000255480b000007506040e08039000b416080401104540c2d00ca541d4116407a00b014019102c017200841c40703004060b006880c40d0050840100e2003030610925030300190201d00651001440c1c000591958011a4000c002d002107416000d4142c030383c04d00d0180402000f8044612401184114401c001540b0034203182c1150710070072003e0545441e5a00715000d21401400140c070031200080c2d44200c00000c80b8584c00558000c464660f0302082c207040604140d031924003502c5040346150000401000080e04000c0540350690040c140708480244e0480184c1c00c150344a000000c1912305942e01040440c8020200e05103400581c0c1001c4003a900c035a60402164440d0150340c011030b4040020a0f412440000071034813400c0407100322860026a00a4000d0707980c42a03124010540d1184080d09080d070b00300d44c0d94024030702140300501c0107261645034001001040b0403600306000e4910622130000381 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 574499181 1250 574497931 574497941
    0x7060b180702160305070605220902030f150f01031a04060801050f010b0309210c0f0709061d01170c0306040f1b05031b0a081e0c04050105060a03050406 67
    0x14005280c02030440e5042884051000c04848210060203882042c081c0904954105000e480d004030081106604103081070394942e00080101d00e0300401e0f905040400900496807802804920002580701d0802400041103600041d015400c10f41000e0810805a1101c299041c0044824038020604803050807085011060114115802c036051003c0841c189005400c524001c0d824283c454110b6a65412503107068001035480c1580760b00803540b000030213500c1e180e2140d2105000000107150002040c0c2c0c003443c05801115149194001c800200114165445070100805928103121100c814800d000d80c808681401015040c4e901094a01421982080f211900e1039020301240e2007400e103401d090070030000e502c0045404098a200405404c03060404802c00c40701c0246c000c207075002401c07501604202c100c9081c1600204198400501001d0822100702c05c1c0264442d03149074003500e442c00c14146224913003040e0180741410010080707519603004540078041903150006641d116850080050030f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 574500431 1250 574499181 574499201
    0x40618150f1d061504141c06050906060102070f030204020d0f02030705040825170a06050c0c07090c170405010603061b0e040510121b090b01080a1a060706 68
    0xa00c0d00408105903485501c8241c0c0e02c940c08022551035900c2000300001031449164100070841c0510080000e01921000b425070000001c000c0302058842d486001142c20b09103900740c03061317a251410300030900003d01007030350080820300c0984003042c00d29100b8501c201691000078051540084c0c00c03900b01d0200ea00080c4a5141061300303554a04207110014625005401080440c0c01001601030011507079101c9003003c81c410b02c5520040e28605010300907013604072030500540e809171210100015001e445410b22a030800c141d01c40d102c54001031400d2504111f07410281c412840c4c060000300003500036192829220040190107203075948c83c03034a40d000d495950310040205081c0400b11028003080070682c00d4141c06540c0300079042514101300020350302c040e6448504118001010700651220500b40b210f001e01a840c08030074002506089002d40107154003602120b683e0305001800c540c3c1c09080e46401010030310043c40030018048044103550f00c414a41813154500186d01c0c01044200c1c2c200c04220 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 574501681 1250 574500431 574500449
    0x150f030a050706090609080c090c09040905210f0f03090a050a050106050108220204020a110609101d280b0a050103020a080a08030f090a080a03140604061815 69
    0x403030380d91030001d0b50781d29180074500c0850042c46001c44d8240c42a0700c80c2085890340401003100301c030400140200420007a0101d20308550400c1807a030707203444500400f0026840384000b011900201100c20780c0711b1684581806150f98100680b00c0b82c44000c0f41a03c4c040000744880c81e5994562003145490240001002440b60152803038001c1030003c10341c0400308468007078a405080380d40710b521000d91061100d60403199120440d19000c0541041d40c0503011400023400c2ca0403410004221031440c0c500201d4020310b2030350102d000595406114042c10a00d50713240d443c100c0c0e4a0200181d510344603040c4017091a00076a10100d0b41810700c0121380740460b0700d0381062081c15a424042c1c0c0c1c500c0034000900041e0b01071754654500003141540007031502d188a800098803401c5444080011400c6078002d4a000818410801403e0104404000401c0e1104268500203092801700c500d44a0000300180f4a611951038070008000352001e00c4070072a441c01e1129000114154542d0b10541502000d41040d107003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 574502931 1250 574501681 574501693
    0xf0b04141f15170f10020405010804061104050a0801091101030e0718060306020c0102070309140f04020705030403021810272301090f0e030f0405100c02040504060218010f08150f03 79
    0x301000700710111613001c00001e45012600c20400e0303400382d02c03031845990700140c40500002d01042c0994051100c80341805107880c0307001d60721800101c045803583c000d89020303595104510100f001e00711940030600750a0805000740a0540845600c0b000d02e4032071200511002c00e8400000b000a030b010030040c5500002c11915034071002c40302d5000f90000603048000c80d44010700450043c0080800348950341d00140b03c240001c00050500020750000f48089426101c14440800160340307032190ba00c2c208800d000f215101d03103042c03e6074089003481d642c00349001480418500c031b1210f01ca480a201003c552071008154401401c0c55a4500b00c0440308189403401e2442c0081075503480c0742c0142080c0d80d8010801d0200da984540c41d6a100c1c030440c90914104117040108026a09256100a10b0401241800481e010f02900813500340c0d1000c860443c4daa550015020728040e0320103000342101c490a2130414076503c0c4150000d0402c060160800c80d20102481418156035162051154503802c00340540364 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 574504181 1250 574502931 574502969
    0x8030106091412060c130513050403091a04030209060d0233040b22090203070c12050307080f1803070803072d1b0f0b04141f15 56
    0x203800941c020311405040c0010704210b0b82c40c3c08050391038090010805450680c4803542550800c1e400f44180b035007900d90064001a090b0341d10442d5900150b00305401240f20f281c80d140003016a4004e400c5800e40007803044808840700401d40c10f031415640e050f559070101d9110b640004d58484502c10000b0751242840b01000c2140300c11a0f04040c0c240c0e034180150314440c245140000c0e07140914041e038501e840c014849001e00110041c280603106418100411019803191991070a0b6070089500310701182450015104010701804104c08500c01460242d00714103024070000c12014014000e2408504850041442442d010000c1842d1030540d00440383d940c11030f441c00441e80d80044404801007000303101c80c0c6a0101111071118071107400114007162280c036a60082c0c074040041003010196026001407040083c080000b080e03009030264a071396000b840c09207048201104605a103ea042e0804030001001841800141c4518894000041040302a420b00045499203682c0424800c034006500303c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 574505431 1250 574504181 574504187
    0x10309060504050c040b032b050708040b040807091a121606080406050f0403020a0b090114131119120807050303070503090124090b0f120f010510150c030201020708030106 75
    0x50403031181982c01b4440c0e03104103c00c15445891212403803001b4071b059007201c402c186441046100015940c246203040c01d44603121141c4e19040342e040641d0002001078144048101001444010240c048041c0005010200340744007000d1120002801124550b140c0c0e03100e40e805000c1ca29413004038044041409079240e9005105c5441541c05071509460306d00414203100500e41128815500b41d002044072113000d44d21041c0266000b0701c0e80001c0c0d507131030340a41ca020400560340c40c000e042c0b6040415825505060085114038203204403441501d80203d21075044504c4100c00044070b0030b02d80ca1184205880c20702c0d8189100d103100080050000008205425802030033039802034000700000c2280c0f003655424082080002e0100d034030000182c020030020002c00e90400c1d0b8000300003420060a503038400c400b040158100c1c90283e000c07034120f28054841001d00f442429800000190000b282600c0c20b034850554184006080d020401c420042c80c0505000350100c3d129140d0102c0156525a5124001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 574506681 1250 574505431 574505443
    0x4200307180b040f050c16140a030512100f090e0102070605010e041401060602060a0507111c0e0109050a051203040b070b0f070c05060a050603160306020406080903040b070b040201030906050405 85
    0x544144e04d0001d84548469035481400d11030802c4815491821514550b03803036821642c584121541242000e000c00d05000501001c0074582c441d4440584030740a5005410f104c480040c485040c03189610410414000304d080da60301151200f145c0010701701da0100345240644914400500f41c5c50a0400003e05540c10310310f00b921441c0540b465041d841404144942aa0035601c02c2e0340050340810049106541c00341c2c004c641201c80c40c1031540c400041103210314100303031040c040c2020400c1c1c00d00c10003030110307002a559080f10809180c000b07403441c140380000e60007641500401d806540300da822022024000c004a40142049040d2107895102a117000200b051080b16404003400c50400031902c10390184003040d2003668024082c0c01560313921000b100080c040282143d034188541d0b03e000749504247d10400014501402d40507075102c0c02c1c094007900b41e0901500001466000b000b04105149101c0f05480448ce400301c3c882480391031364001207002e0950340c1e5015240030f14190030f02c41002000290 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 574507931 1250 574506681 574506701
    0x9170102070b091b19050f040e19021306051c03030608031620130515040903050c010b06040303020d05090109230301141021050a03080f0105090420030718 68
    0x50783d113032180c80d409009000c032982d01c02d02c910401d2000140214a00036002c4a18520090400101c00042490b03262515511580d444604401d00c5030f80350950038214881100342d000c00d00c0c148010351034a80400e00180080e008a2011900096800304040c483c1c3c0200c002042803404aa03101c111217603010482c003039410402c403070208c2c807503404c03000312601812203455414005060741d0080b038a5240600c082c04006240d4941c20785003403059032041da107520034089010300036500c1130749411140344070354211080d00103007a200c0e0703109010400010340d00048500d06c090344d5142046c3c50300c12440047e1416419a000741120744450380042c2255894011400715a04003180244901da40c030340e201c1210031606840d1040f074003610440c00d002e41905144081c0c0210408074168080410a4a13000c2c14802104400c0303002408120501400159040e1400e004d09000c944640c1942070650302d04018811201104049901c4100c050381259414004074000700f00c06001303134102081b078901c501c00400010030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 574509181 1250 574507931 574507963
    0x50a0314010c090b0403151116051b090c0706090f06051f03030905061309060b030f09030a050d0b030c030f1023010302061308010606120c0f09170102070b09 69
    0x400080322901c50f46494045130b5255010918081c11a00c96528105081207840034003500c664621803185c0c1c03680003c3c0300001d03128110400c40344d244d00c1e00501b0468440940204160002c612034119a20744244a0b040750700314402650340c0480c2d01d48000606a001e901509000102070140f0070b001003600028071496400307081c40080c0042c000da040309000309000203400a000e08405010b02d0a040c4000e18a40e204010b507020420340d240e010f10305461080d00007102c0c0d4000030081c8035071460a100d07007642040701c0304003031400c01c450312400030f01d140190042e0101c000d449501007a00340c1c40902c014107540784013900340c805500d015140e0641d80c48410444004c62850610342e0102c0a9040141c1c0c01210700c007d42e80c14050340b03181c01308201504045d151030b90100c5a03650014000d03c0903c15080240644c7d180ca29015090307902260071140d80701c6000741400040b0041036045940b011107902910001e60310302c50b55904a82001d80203024540340288405d80660071300c20b40540c006a030b43c2103010404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 574510431 1250 574509181 574509191
    0x10207060e0114040213110c030705240a050601050904140f0c0a09170c0a17070605040510110313090e060106020d050d0507170106052205060906070c050a031401 71
    0x18508a08031000190702d20a0320f408500401d00500c1d0500d50310702034400c2064086480307010246404075a038072002150096510010f5000c08210040c06001c5210501c400c2031010101c03e200c0c607201540008000c41100d5640742c0004481c0da020300143c6d07031400d1014004003c2d0742e01c0282030505155043d5298207241c2a002d001074410a220800c80d8002900e0381e44280a940c544250303103055030031001c60505607010702c0f40070039029114141d1110081040b20002014040b09803035582c280080743d003001c42000070802c014441602e502080c00880e180c9807401c10060b06030f05401d03d0541c0640d2520f03e500e100d00e600001042d10054104088480307407007095508590380c0b01c0c401da94859007103801c000032480600c06140c6148541d48920f600c120641130020842c1c55240b650a4200800d070000c1c80440d00100750b4103003219035013118025030f605c0452464215418407000401c030b0b00402114500c0303120001508410081c260a5140007004058440190503840c2e00c0c0808441c440c01e903000c2141e600e04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 574511681 1250 574510431 574510451
    0x501050405060102030702091015050d050703060302150d201b16031b15120e010c0504090902060705070f030b0a02070c1202060c06010603050601030614030d0e2101020706 75
    0x3600c140340c0103010580046182000640c20302409803001050b401c40703c1949140040c112480c10610203801d04541d0701e45940b03085110a0700100c0b1809010750040500d001000e00041c0c031070b07100091110740c100490b181ca600000c00c10101904103004648806111a03040c05400e00c1c52401030b00041f10305811240c1080d214280301503540780c00923410108402d82a0b0b040000c00d50b0100d119041c521401d10b0180700f2510744075a00e1800c481004000b001840ac030121000d44d003c00e03c285a0b1502200c3d00038409070f441042c00a002e805203000740703542030b90340b40c26080466980800301d03450107921500392400790380c0d1f418549281d41a10b20050300c0d0704001b0390001e011941c40303200303c0e2207141d8040000c149590400c9820030fa910070000d0201d070003400800060180d104100b04180c02002c8959000c0b6491408034001000c7d070f10103078080d090355850808612281c0d607021408100c880098501610b6100b00b0100186945c80301d801c2c481240000550b00000080e01074000b88007490098000b07100100c41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 574512931 1250 574511681 574511689
    0x1150905060619090312020d0f11070e070e030106030501091703010b0d050c0d0504050a110103020a080604111306020303070e0d02030a031409030115090608030901050403061e1103040501050105 85
    0x411107a495001800300215024a4100010038400711650300e0b0980c1455200d5079040000d0b451801654050fa2101036007a0384a0782c0010344c5031107420b0b149885c4064080b540311459888401c1c1c02580c50801100c0d001031040b610558540c202680d00800901ca41666410064028906030400340e490100c28280212080b000d10101ca04030303440001124600305400e407216004040180c5046000341c01000056020075181c061140600e0040c400303420115140d150090101401100300303410b0500600c0b212f0304090b04011070036030001040e58041a42d0b03029003070030040b03407040100e14083d01200c2903001c5601580000074601c1041c0c40c0d00c0e80d0300d03204403000810030201645070b0001e5042c3c4c002005000082e202c0d020032a903803c03083e129281400070b07003c0040c0c01d56503c400b00c03040001001c0070420194007980540c2c002056220099490001c3ca07500007040c0384924040501025210803040204049510010104e82c68183c42002101c908584400302130b442035a00341e48560921001040340c4c68 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 574514181 1250 574512931 574512941
    0xc060406020d1214041103072102011803050d0f0807020114040305210a0212060a0608043509041d0607180b1909121a09010b12011509 59
    0x291075001801c22140c1050b04840580a0000e044550b903214001011401041010b99000c0c912442c0314101e40c0c1c030b11340107040c90310703e503075010341002c1070303410315444031600c4a51580700050b40a03e481d84544805034070107403c08030180e0004040f48140000d6000342c40e40612030300c1001c241555845400c3e11010422030a0f00d0b91018416840f00d2088082000203000d103008098404000c612a2401d035401604050441c00c102c4610408030703000202045c2e000031100a107030b030040017114140009401d041c401818043c00900040c00c40b00f60303188914002406007442c040404c2c0851000ca401c03102d030740c4200840c2e008214118095030402001d50700a40f246e542c0b401a00680800030030356039075588000c440f4041006d489016280c2001c002207a01140c00b0000d00b512001280400f00c0e0300b007411001008200f1590254842c07455952916001a00020100c1c04156280000c40540d03203c6440007401024422029580500340001e58440390806401038188441e07403800c60a00c0d181d44004001c1550 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 574515431 1250 574514181 574514189
    0x2f070c0f06050d0c0c060e0303220b0106200604060b0f010c050d20014803020d06150c02010f050c03040306090c1d011a04120b041103070e04050c0604 66
    0x241051203500c00c01c042e40c1c0d024032038148862905082e820000c0e11800d046511f4182c2e070001c9600000308001d01419064481c079600b400150116080100c10f4558644104042c080c2d0750030030000120400708508010713428804007071950156400c9003010b01d003000080802d1558903020300100d0014100540c0210380c06030340160054003a18400a900724202c405503030030720201007070711102880b000100109210701082880d00000d000c2000041d4105030404e00c05c602d45c0060304e0345450351025440311a02c12401d02000082c11701588072a0b02c4000c110240540d50091110007481d0b0118002d0744d42d101945148080c000e03200c0c0172034200f040400300c07200e00c00c4240b40803081d4030402007003000400c03680c00407414134002d010854401c0e45130684080c80d0703400c080701c07841c00d00c15550052119414000c0784070079013004040d142d0319240ca08001940e0000301002c000d0b101c090b038080004d0a02422000407448040010161341585441c3c811460943d1001d803030070356203449204071135005c50504004a4041c2c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 574516681 1250 574515431 574515437
    0x2150408091012020f0909010f03020d03051315020c0405071b1b08030c0d0f08010f030206130801050a02070309090c050306060a110a0c03020405070806132f070c0f06 73
    0x4024081800300312900600c0100030045a5880a04460a00d10217010f6404403880e11940d078206110401943c0e013010f81102c00e43c0d0b400d440c000c10060fa11001e40200c2030f41d150401c00c0d03c1d40c0c1c41510f004600400d5501082c203509103c0d1100d4106940402c0c000c4062004403800c001c0c40d00e507044200c40a1200c0c1e00b01600c401001161000443c540320301c104c2c06106014803a603101504d90000a007180c06c80301d4820781951080c00c08807443c03500010704034900851340ca0080e12661401a8041100c101807002038042c190021b10020710714540741603000070f0095000244094105859038400951006800750300080c4800304c00301c0c1c904864015418486415a541e904544401d400c106072540011807060522082070704016560000303005000d030017402280c003035940728507500601040c0c2c1d0000b231101081040210802c403899960600f4109010615900082c01c5c0c20141b81d003420309211808018424246a402088018905d0008140340b41c4102c2c00540c00341e43e10603050121580c580100408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 574517931 1250 574516681 574516687
    0xf141e0a09091e0b01050111030a02150603010207212d0f020f0f031903410c07060b1f0507020a0302090a05070806030f0c060c0123040302150408 64
    0x760641504104846405450860f441440000164204480d528021a02c0701e9503040100103a60f0040341350190400b01d44051441c1c80d889100081d1a0b104a6001d0f8030b100c061a0089541c5860940c16240a503a0202c2030b07400000c02e20804465040070480e2150000c0d81c09800e1540a401251030310101e10750701c2028140b540d150942c2074543c25401d900900440c440c904542c41b51000400203c540a041d020255558140301c3c0c262040103200420007000b803604040f00c0300f06ca030051849961406424500550700010640f0001d0f42440004c00381c142503000c288240100120814000d0154501c103041c2041039504080a000410411503010011403000241c04001e081c007502c014610148000d0400424135140e0340000d8408105440e00c019680d5600200b000740c540055aa54002d002200209503240c0b40031240365582851000c0c060003894007040300c1c1c004c0b90094102c103040c0a031240704008140b80f032501910159070201c80c1500140f00f04802184484204c0009500454104030a02d02d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 574519181 1250 574517931 574517939
    0x20108060d0609020316140603133210150503031e1902010203240d0f0804080a15270b0727170309090f0c040f141e0a 52
    0x1008403402c1d9036082d15100c8440050b03409220418000d00102d0781c1107100d81c01e1040e003602960140c02d04a0088008006100928203145480d09015902400e211540440302c0c01100c1c1e026141451600325481c0040e50b04288100824044601400d90350700300b044040388079150f450008107100f140e030140c004000e1032540a0101c0c1109020350304c0745004520b84280f405000c104a42802c031020b0050358084180b203c008031115001480c54030b0110064000c001240000349000952013000b411411210f1044080040000a030780c001e2440d4000d89010300b4290500056075684444117200e00c0b8a4003800070f440c4c40d058201c004101804810f24580b040e45903540625105014051030b00b800481c80303020140100b950a0070803a00119503984050702c3c50308241002d140703221465034501c1e41052184102d140c42e12850140c0c0000c035151019842d440d4400c0c0c484031407041e508070f00c041d036000007004101c07485074100c01030003c2d2094440003804000812403403d410001d20116a001d40b01d010100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 574520431 1250 574519181 574519189
    0xc06080a0207050d030b01180608061c0506180d080c03070e010507020a06050903010f0b0d0b060a080a03020604030e0d0302121c0213080114100915033201060302010806 74
    0x65010418000051a007003480d12510318100c04c009240c400203403103030314035031580d644051181ca00070008200d4030300340f40c1080d8001c0d2030000c00501150003490380544042d030895101591100480d004002d42d035003410154030440e40c07021041300c1440540b140080c021800e5114000052003402810821403c6445010703040700d0038049031986504201e400d00940001d40d4580c40c64400802c0f40f03807120b96440c4900801e240c2503030740d011180c24284d480c1050803142a224206d90954117039014401070810f0342c51000040c0d1009681d08840c20a00c1400c803024205900004c425000303601a440303140c0120703690303c10845c1039041c541b0000c0040e0001000c1d01c8002e0000005009128590000e030700720b0603403802d502003c030303049500c085000700003d043c2000740c90020b1141c5079801500049503201c925121806000740d01300303840b9103020385559050114030703000102e041034059035110880304d1070718284040090882010081d4288010346001d610603070b148051041b5400c52343d0685411107660b807160200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 574521681 1250 574520431 574520447
    0x20f04090803150a0b0f07020d020312122401020c210f160b0f160c05040f0203060102010b0109060c08032205070614041a03060d020402180306090a0c06 67
    0x56401a858000035800103402038061071080b4980c0b00280e2550f54154204120507446601c030000804042150340c24480b0220704840745070344c040e030703000304007406500c0401c0c40c040b102440d1f181c40e4100807840e1609082c100f644c540c0a0b00b0111404905d4849d9a503159403400b800c0e25415003d80d00040c5900b4103800e04c00c113042200340c81b5180000e002440396900906203880803060a005400411102c00411001c0c03290002601510a10900301185058080041d00c5082d010700018611214080100f001c4028600040c2c407002d801484222800b02d402c1001c1d40083d03178070701e000d542060f20101903540710b0100e103c215030090b41d904041c070900c1d4569000590010f407c007002039250061291103c0240000c04000b64801d400a001c0300d8500311004199103440f00c406096a40108070410152031000b04544401c0311104000c0e940341c0380d500018031500090040203401078000710b031001c90a1040501c070b82c190041681035580e20343d1203002c01a200c881760308000300f0882c101c00301809090310070155 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 574522931 1250 574521681 574521709
    0x20031017030405181503060c0403031e05030c1c020d0204090b01030b1e0415061107090b0d0b0c120f0115051911030d0e030933030c04031a1e1302 64
    0x18070341c000c605c0040030904004040702c2d64110f041c0300043c10400c050f4410a1540d2110303003a491075a03401945071004103648000f50807001c0e10b040100e004c4090000c03607802c0c129000d5074144115520013010385420085e42261245c501c0171490840505403039400b80c051440020001000380c012409094280710001810020103a0880da90b85100100841d40a5103107000c1d108540707800f03040c00300c0111001c0c90041c0a802480e012401d000d4407403c40d4443c8440c1e030403d161710031280000d96030b8400241030580516550002c00140d81014082c009460308440360580b00200b0120806240b042001e84540c0729006411034080100b4241051080c8070b00a40400045c46030282c0c0c0c0707400300040c160400d03512600607507002600002501480380c584800c081e58022000f151520312909aa0403080f48444421441c600503c1c0000c000b03401c6030026000c80303000d0342d4000390621214a80d00d50b0155500e4003210405440d44c805021040c0d10040c0b0814540b02d940d000808401c8261f203a4203000c030111524203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 574524181 1250 574522931 574522951
    0x2040e030c0a0204151d0a150b032802070c0f0602150105040905010b0613140a03050a1b12030512130206030c0a03090f0b060f060309102003101703040518 68
    0x32001c01c0b2030003440e8003902001e144440d0071146c0c1c00d00043e4901210000b01c4452003000e004001040381c41c0d10441aa5401442c1100c0a50f0003400301210794081a40c4280b100c0e1024400a5148100080d5124800c00d50380c02130341500416864a5080c3d9071060346119042d603081c10348004100500e01900110f16640c80b500000c20030300d070313440041112908241942d032140c03643d1202c18800b43d0210f02c0e00c1402d01000b2903c034800507140d170725003c0d2100b03005c0d00040d040810540c044200c003844000054000d00584960b0440b000450500400c10341041919401c03040340c060100e102461595900090315400070b100521315110715200000aa02144400041c076480e005124081071000114440c854011003030b011192801e40101705416031100072141c85441c092060000c040b02c005402100e000f40070000144410b41c41c00041000580c200000b00f0091001013005960300088070408116980e00c0502245a142c8403101500c3c3d009900038590800300030b070100030300340c1d035101e1040f030b00590680 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 574525431 1250 574524181 574524221
    0xc02060603030412050c19090c0e061b0c060d0e010b0301020903070b070302010b09011724071407060207060b01020f0304120308070c0f200103020c07050105130810050402040e030c0a0204 82
    0x1b0041600d8046d10700c107104105a072543c04001c1a00305000f90304d500c82130381ca48080103545480018400f03018a200420800d40c0d200600140d000c002c1044c1c0c0f5210300f00800c4a40c03940c213600018030141070052118010b9509000c00c0948500341402599000720b4010041c00d40103040c10a02c5195801c141c1c1e00383c046640380c24000140d9203807001100c3c082e2901c0441d0703001c1e5049820515280c102a104240d9409100c40e10f042091009410860b802140c01d16090488a121402c0d060103070180b01009042d081c80010715008010aa41c05084480001e0302540e50090b070503582c0c0c80d12030203240701d040e0064104c104a1000030f031207001780e10b5000c4003c4c00e24901c40705880e201c0c410106a403400441f0f42c40414403140f40c0b810a00340340c80c2c1d60851b017482c1c107524055002311060349490301c0307102d51818031601040c040d01d494005680207015059960803a440c481503e80440007800c0203441c240e010780d19001c0b60350740201020044a01c48510803000309000c416982c01d0000a00a070030200ca040d140c81 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 574526681 1250 574525431 574525453
    0x6040b071703010801020702040c050711090a020d0e070302040c020d05031938040b130c2001091109010e240312070209010b03040506240a15030c0206060303041205 72
    0x1080607501030300c4c0003400161610b440d407061004607010f180b5100103002d400e20540001601614244580032825106810640c07901c03407100d4003074014481851301d103038208104000190400250301c0f0440f0b00031142484070042003002680c0700c450007080d180c00114204002030340500740e05a8441d03482031a290024070148041c41192001e50f030200e4a05200106811031420a4102c411090302c0120842d8200b0250300301e00001107082d8030003140400c42c00d89982c2c40d040440d0044e000c0c8400b44481081c80c000003652034030858000d20b65180d04440040742056080c80c0e87c141b03c00e126050b101c000001c0c41490302d80b10000c4014000700e020203550b05110b00454800e544050007074440034010559031980700c02aa00c10402c071791b18141c100c1c2c01940c40034130412001c1840041c11a41102c01340d08010340074020700050000600f03100b0f0b09580c0101c0e941d0000034502010400c81020444160b50406c020100064100d88852003520f80c00c1e0302d54401d10050000c13002044c84d0700c038820721800c1140c075010703070ba = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 574527931 1250 574526681 574526723
    0x80103120e0f1201020309160605180418080a0807140a0315090204080d1b020105030f071209030503010503010b010905090105011202220810050603070311030a0b04080310080c06040b07 81
    0x8481003100345d401000b8170101220401c038070030307808000000c210105420000c0080880c00b4105004500c0c0c02010200c42c075a44032a440302e013000320840c0743c0700e012110908000301e240c1d000c184440009005440000c000c18882d00c91441403d50007900707130307180900d1594210080c0c942d01c0791002204050110000e8084a1840100010907500e070103802c80702d441c5500940348000d061410f8010140070140100143e03440780841e40c5c000c00c2e8414892654031182e40890b560510950072800b220b18004041d0f045c10380002c080c45c120390040b0002e02c04842200011075014546105580d00001e504005020a42c094aa00d00c0b902c6d40f0b241006080c4201c41c1d07568400c0c0da183c2c3c104251a8111500c040c8585c42c0284841c12201c0389590741440030381008000b003a07555031079101c05481c030284400d60110720354007405500c49080c2c011305100325600302070410704030321350081c0c841d20200c0c1260700000402460126440114040c000c116a040034941548415030307501ca010111020110705100c0d06609403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 574529181 1250 574527931 574527949
    0x304060911030618070e090d05160c062f060402040e0a0f0b15010206010617060a053f0a110102150108070602060a0b0d03120b030a030809010c080103120e0f 69
    0x5045004000e511030500b0503c0c10070005e90401345180080c0d00070040317280000284603407030601034503000383c1d1080d028148821101e80040c2c024401c031848140000d03100d50004140b1421101c240c1091101941108029451952080c50447d2508500f0006000d071400c2d500103080340410701e05548180308541d803180f0b400314000c801160784c40b1852040c0892180c040c0f0301008910000e00060000d03504144024007030300e0100c080c1031910312030301c3c00144031500d502020700020b0001802c0b04d45402d00e90100d92030400100f0445814508440b000c14043c20420302c40361071515440d8004c3c0c0b2000b0314907250300303030514070154280d4154407595200c400b0318944261a54000c128107000347c070b00c81e420300c40002d040000c0a450800f4140c00d100c401c00b0f442d0f56204c81d103004075a00d400c04072101c0c05080c0030000901440351641e036260084e4580c05041c582c1002a481c443c03541c06c0c0003040103206180c802d0741e0b00383c070038000a003544000845400307500340201a890300c4075800802c41c60300b03440c10318006400381c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 574530431 1250 574529181 574529191
    0x14210906071b02010e0d031b050f10110315060f040b030610090f0506031e090a0615140f0420091306060c02010c0501020f0d020705010b09041e03030209030d091502060c03040609110306 81
    0x1a0040728282e081c08404d01512250303821024003440040c1641c00300140d140400b4ec0725a4001407089500036655a4903011510040c82c019441601c03903a80d0421201580c00407500d0f58040c110301075014803c0da104402031420394403280314000f450741c10481480041d410092080c1d01041c0055642e102404440814074841c01c1484003c0941d1001864041c1c10380710803000c0300f01700301604101482080e8504001800180701078070b1031041c80030170300c0029014042203c03810180407002c0c00e01c66014107500004141f8000c0c1980d185e19400c42d1301400404441c01b5104200c0013036584000306c00150b114030042074200340918005030400c4025618086035601489804417450b40c00160712080040a0091182d07866003102c0c038549503d8a0b4554540d00c0408900011080001e0801751040501a505070303142540c000d42100c910310070b0207001a1a4400901070440c0080a81a0903540c0c94400130f0910321559030f003c201c5046864568640014050b0404d04550a401102541400e40c0b800c10059100b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 574531681 1250 574530431 574530433
    0x315011e080f211201090b1c030906020c1503130807150f11070c030308131a01080727020708040801090f0605010506090114210906071b02010e0d031b05 67
    0x41c0040700110701d243d43d4841480500e1540c2070100c0500202c03807800181c1160380c0005d020035a1005000019402c29100300300011441c1074044203000e05a0080180d016201e56070200d030608071202d000c0140d01d0b42044008540b40742c0400004039040402c0c1d40070140f0300d114806072400c05c001c40d81c840c0c410f56406104086c07555a40c07030440d12402c4241c0907410040d003281c88d98034030303100c69a180c218000489020103014002128081840c0c80c0c03043c078440d2556a001f1080144044000b00010600d007020301c14854a8400c5180114a40d200407110601e500e00ca4061040035070840403003840a50000001540e00d030384d0522000800800c280601e0031200c0c45400d2a0220741890700c3c00e00c0840d401a000280a80005c0c000044142d810000001d8010951b100c03650300d4549880d07138010a610f156550f400d04540c01c40500c4009000094003500481c0e440d02c030714400030404900b1000c0c1e030404050190010b5401030245005050924003820940d0083c90012005550000f40c0d405140c0601000c40392 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 574532931 1250 574531681 574531693
    0x120c020907052502030613020f0415090e01020301061b0303270c0806060a031e021f0206071404170f07120606080304062c0d030c020f0315011e080f 65
    0x21407604402421841c0440d00b956543e010030383c020903620b140081100c00c0f0400300008800955072449070302ca100c1c030b80003132041c04003d00c1019903005a4003144140c50381d0724200320341d000c80320350103000b5a03050364003d564031010110100428401e141c000a000c3d07050640d03440300100000d000310b40400c00c00c1d00494040c13480382c242c1e00d043c07400d0301150760014903c0d411407806d00c501560b441080c002103d030445025600c20400900036130406110000095015003002202404103101d07240800c240481170302610a1076980c440141c540105401c0400380c0424100404e20407180e00d03658003803081800404449420003007031821490102c1a420000c4000c0c22404684101b140a0140801506a14010b141014a460405401401002c2c0103d1001c1054014072502506036481d42d0803038907000f0081000313004c550030043d200c120380e44426402501c0302c900c00300043c1000208484400b0391158021002c0e03180c00070214102084407110305416a1120b8005880082000680d04030962000030b001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 574534181 1250 574532931 574532947
    0x1219021308061003030e0d1e0f0209010b0322060209030d0e28090236090f0f040201031d0a06021207020a0f0831030510090206030103120c02090705 65
    0x85864801405102c0c5183c0b640da06000080e4405401c40007100245d80b050901d40c414a0600015480c02c45602c1240000464241c1070060320303010416091300039562140c60340d80701e0030941a244011101c80c12050200084d0700f4103440d000c2c0e200c0c0c20b06401000014245102280000c0c00c0c0702000043d003000940c4503400c12038901c0c00c4d1400742c18020003017000741a8100441c0555020074103500c21440c14680c085100703192000025503c07001d10030503040d030802009840742e01800c0b6030500104540201820703000a881c0364074949500e0b00600d80b100c4101400e58079a801100506490f40103010070000c0d200c030403100c50108001107003050b4410b9a0240e00c490002600c2c0c917103200700a01c0a81154400111800405e03078407000790503281d4001e294556218001c00c0d20000042a42c0c4103400302c8100000000035020a40c2410b000f40c078450006d55521a03083c3c00c141017035a2280390003a501080c20001080040d9443c1440b00344240d8500b00740c11154115000107030802401c4454501041000803241 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 574535431 1250 574534181 574534183
    0x1803070c090e03160206090a080f010f0f0c080a110d060603090506150a0911041a070b0105040b011d0a0b030f070206070c0c0311012f010f111219021308 67
    0xa40b01c580c00d0001141071010b4540d0b40804285900e8000e40100f100213072921264852042c00c0e00540403070022506101005030005000707000102b807612083c0c3c42c0c00f1240c140700304607000300e00503507080b6510304040d5207030080840000e041218070300401d200104509100014035000e240c00a01c0f180d1030009a002ea2400c0150608100520700c5110312451f40f00c41d0340d41d035100c030300c040c040e0ba81c032800000300e01d0111000429107101c1d070b03000760b03008000808401c50302c910040001c280c031500c9014450303d6a640d07201440281c1b019410340c07902141445400c4903400d0615441a001503800510440c0283d61b10741708017038140d0040d60b1b80b807d003400700030401c0546078041112603007200c0c1c0c521384820754041c1030b250b0307440040013800300030702d024030001c519140c070380c0b141450f0009414151440f600025501a80c0641c01c51000d00c0309055500f040100c00c0c801340b141c85141c0c050040f0b651910700c2d2008444184400b0500103151040c00351400180f000032a001c1e01c00303040f0f420b213600e5040c1031140c2810811 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 574536681 1250 574535431 574535441
    0x50c2e05060a0b0a0f050405030a08190e0a1a09040606031b14030c09041b030c230a05090d08070602040302011d010e01110c0303070506010501030510120b1803070c09 73
    0x89800769810322010000b0045940444101c1200c0345170501018118000072502031041d81e109650600ca03001c001070900c04020b0040c02d4944500d86250030002d61410203961080c0740c1a28123074031807a0901c040064030041c109500d1001c00d2003010b10302d883c4844000408a500720b410020000360b0303445000c07146551817503e5051507819400c010100200e24180109a0f1000419111b4114404a9049040d49482d0400240d410350b103040201f83c4481484000c0041c61203004510004090715003500181c140084052403011640854034a400044e8000307070303482d5010800d01d0350004400c20141c03000c02e03640009040000e129031400b6941c1c42c0b40d4000100b400d58694030f400500c0c001fa002c00ca46a80c0c00c2030415201560a0070b181b040303500420725242c104041ca49919405010000d40d1104000b00441c106050f66401d0320200050b403142526854a603142d03008841c034109000008001080c03000900641c459100340003030001c41d4900d5211030a641040d01c08550740c003000881884006618018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 574537931 1250 574536681 574536691
    0x608010e061b040b0a050d110c06071d010504123e0603190b010302160501050115020a0201020d05030901060f12020a0e06031e0109050102121e0412050c2e05 69
    0xc3c0c01d25042003821840703842076a4000d400d20200003480245031486410060401104442e03003920350800d80e00b00c54031042e0441c2c54200081c00d02950008110211034100c86001c0b06035503060515050a146296400842c03005035106a411040b181080355845400303850404444a40003041c014030325810b03410401e00c07030660b01c103032400d00400014148889425254826402012030001e02210050300207100d800d0f1089698940b0803c494248101504198121502000c184440c210900c038200e0700c47e1220724009005802050064001c14400c4018640081400f4000076200d03a03185000d80c000d98155100107149040c150b5100c0940c501020305400500e40408103c8991070058002900d841c404e81009030101007907802c1c14908a000d41c0070340ca0050f8400d000719646c0101c010640740c0440c1c210ba00418214100c8920b020341c09401940e240559031044103107602402640065806400032995440c840c464903846026008007100104100c0000c1030f0302c9940546006005000c1d600c0c0180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 574539181 1250 574537931 574537981
    0x1808060105010c060f0b06030a020c0705090708180715080109051003150911090f0613020a0f260403030e070b040f030201050a1101140f1509070e040608010e06 70
    0x200421850342c000700031040c1c07660b0100c00044d100045000b00d2000b4154024050b0b0840d0f00403007003100c3c4600750380c0100b40f410518800c5812207139668040000400084420b500016465008100e1486141107000c2c0c1f00905001918034194a0712240b0000103100c1203040700080d440c4004100c0c0621038031580b03405c12151441e40368200d041d40c0b0f03000e1620081692807810f0603038a1030380c0c000740f0904810303000341400010b24805882c1800e0416a9a2603c1600d41c0c034032500080c881803452070014401c0700c3c00c41d0549d440d001450f540e03852041e02c0f08003030030020303029802c1203a00305881e680f030001140b4410740c80fa8a00044440d08a407055240503211b030000d00c40c1d490100f20a02c0303580d4098013040222542460030035640c07006a903044038107451140702c0d0b452660074500d0607056480325042e500d00c1507401d074519580907a41e840421403134014111080340c1180b410340101d02142e01c00c2c140d188101101a2000c1042036a4046141c21103100d47d403c20260f40015051094071940d16096881b412a0a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 574540431 1250 574539181 574539193
    0x3070f061a0f12030c01020301180c0903200604030618030e011701090506010509030f030913112d21070c0b1911162112050c09030109031808 62
    0x10001c110100ba490030494414505400f002c00103440800c21a6600c1030303140d000355202e5039101079a400440001820404041c18083e10110862258050358200c135002220303009038004250611480c0b000a40566810150421010001c01c401380550400c00c0011a41c1460b912036900303000306000141c5001c01e0400c51040381d41c0b0401d42c05051340b6810365030348050000b0030382c940c0310050798184070b880030745038141c0070704c0203006004500400a0b1071031007400e0b25846080841d115a00e02100e92078103074592000014449108404000f00f1441c44c8540402d0300941e2030000582c0f11070041d0400100008d4a00d210b50203000350b15940c1c484175400216074100744001105940c0c81c151300400007000040100c0b00300030040300c0340095030000d88040c0c02a500e156030f42d204c03405c105d808440200300e00781c403885182c01071803442c10034200303017164885290340c1e410742c041d60404da50101409000c1c0c180c02d035042c07050013005002e617401c1c45520340c45c5100c0d80301e41c42d00c1d0300c9640d416100c4c138003150300002c0a81c0000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 574541681 1250 574540431 574540481
    0x18100206011211040e06190b04021c09050c060f130b0a0203030f13170d0e160911090301050c0406200c010f0201020d05160e0a0812090d0503070f06 65
    0x100d41d407082483d03003c08004980540007010030002c0c10010740201c070a119040921884102e0021170000511f0b10000500050f540b40b0144803d80c0f20380070005000c101c541e40c0c2c980c05179a10323070321901031681720710165540e28603075400003030040d0044000ea800000700000e03540c02c0903ca1102e54401050281c40180c141201c40704043e4a0b800001c0c40e812110203d800001d4515071401060540d2943c8040c61196002100d10703440c0301c1d50440030031040c1c5039240500da40031324040080c14803460f180c41c00ca03c07058039003050305100c050006400d9060345002c0902c02c00c44d4503502030081600c1010008070700d50700d40d850010000c02492880290f07400d41c1e000070340c520026841c08a04484e8001082c02c150b6141c1c13455400490080c0b0840400c4a40303071b40340800784854200000307000d003484021551020003a4110034100111201584103403861540007070801c010380c480010244c00c0360030b40281100c0b01044580ca4250640d8032103082192803140803c1200e040080318815403100d241e07200003807a65003a071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 574542931 1250 574541681 574541699
    0x30b01021f0c02030f07030c03080117100f020c0f010504030305060613030b0c0c19051c1e050c0a060c08160806011419021c020111190507081810020601 67
    0x60394620307080d180c1c056000220700800c00c40e0100b05540700c2140da90b01c2c903802d004144481014080300043d4940000081c1da91101d400c064202041d880138200c0004c11200e10b070014101d0040c89100590280a0704032400e1040c00614803441000d0004201d6140c540ba00504480780140450b1044200784450310f16a80c420f00701c181501e90052040d0041d032603034480318000303014129650803544601804100420740c0c8107001400984104d04030b03403961075020701104c80d00104046550002d030481484c4024820031104e01262074025051852070410740446403410b1001304542603c1e035945492400039541c1d844030b07405500403c1d060b045040d1484030040204034000242c071550401842516102003034034840100d55030741036140401100f22900c050042d40b0307407294002d1804103542c0c0c00786466289c1e0060185c045102c01e10342201d464220f200c2c5803a070900d022450110100403040c020f42001510000003044c1c00e44040da003903141600c400c0304001080325038400800c1150000c0c0010800c2d081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 574544181 1250 574542931 574542973
    0xc0301060305120703140409020a2a030e0f060316020c0102121207030b0910060e0405011d040f0602280215011406130e07020d1b12021f0c030b0102 65
    0x114180f00745540b50030302c1c01c0444030780d84c81c00301038006440c002800084200481d0f000b07008030b003c0d94403100c0785041040308401708140348030345040c9034801c0383e0b0118000030320400c013603142c3c1c8500500b044024809000070965542003216890303040300b1002c81154140360104605102e030b07a02480100481c09120305409181c1c0240d5099030550740c14280030500c2680a80c2254021085c040c1c4581d01900e480411070b61002030b640b14213400300703410003000603550078140545030680d0050031415540c4007400c10882c12143c4d0042007a101034003000401000500203000070403425640d80c040220340681440d1180883c4001e01c080d5003991b118010000c8195440d540090444d030040e241203041720040ea0204006124451808030080e019207004540b0710310520025008950715070880b00301c506602021f4803c910200c0b62500c50000340c02c581e10001d40182d1890000e05114419200d015003165400500044801c100c024150b85800d0341d10b45075036040c8901e00c0081000d100901d11b5244410310b0b8841c3c44 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 574545431 1250 574544181 574544203
    0x102061023011e0e0a0f030f080a110604030305010e0705070c05040b01090b0408062a1204111008061215060f2206090b0604060e01110c210c0301060305 67
    0x1070030740740c8481641e0b0181d48242d9034200801ea803052000808203000704041e403100394092180140510125040034400020001d8950021070001481129125800950004404172040010b002404c504054040c00f105005520a850108103541050402d0031709200c010508401c100e01800101d01042510b84071344100c82082d2400101e081050740121444100b0343c10110070408005070000c0c0d02000050751500c52080d903041d0880c3c0081d000c01602c09a220594040c51002040c4000b144124042c1c02003038215104203203c0421104c01c001040c052141005181c022a4143d4100a09810442020390f010040c0c00003606000c00644586444100c000e0004c0b030143c0401200d24070f0033307100d000e074168013041c4203036290181c5c0e80c1e801003090203019140980c182c083d081c0043d0300749505005055400751181790701c5402c101e8500c8401100c807041c0044044020f4812203803400107503100c0305400081e400c8941c0c1001d0281d81030505e042d240614a0803ca8000e0789084010004900e001c60a42d583c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 574546681 1250 574545431 574545479
    0xd0201020307060905071a040e010902090102072d091431061d0604060f020405010509040b0409021203130807030305041a120112030f080709122303040501020610 71
    0x111340c02d4209146481741c40d801200006003402452102d290b00e10024104540c40b500d00381c4990382c0c803442c98005038001c02107510701690140f0801c0c0554684454915441c04094108030010700d60541d246070030b1b0300d0603070080000581d10400c00d41003807038602d12607074858240354808809107541c20702580410906000c1a104403203200003a420000b003608286110001403140c0c8a03844640e910054540360151421034005140203146103010b00d560095030200c50701610782b81d003403a905d00d0500025004040d03c15621543e102800d10040c4d0300c3d881da40349610b10080085883c1e00141046c41003c0c1d0242c0c0000605601055003000000d500c00200c5054500044110900205900c9192268001e482110784164480c20011940150b8041036003d00b500030b980303010580b00c440700143c40198058526a000683e0610140185030441c903034181c115104602c00c690346c0008800c82c101c01322100e42d001d151600001000c01481d070f41005803640040130245825019440c00c2c80079026501840c1d000321007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 574547931 1250 574546681 574546691
    0x60e150103021011030d1401050a0f0b0909070e120102090103061a09010c1a09030304030906050c061f0503011409060f090c01200d030905010f0e0a1b0b0c0706020c0d020102030706 79
    0x203050024419120006e240e0102805003103414407002d4440328007401a64041c1081e0500040d426801c000001e01701c40300081c000d460440c62070280181c40030020092000e2110b004403420b0030380c0381c2c61383d04034503505200d000680303984011000400381e40c240c5d03118010745644c001002085c0c0c06420208c2d018084242014010742c0c2c100d10380040d40d10404004603c5003803003c400c0042d62440480210b03c2140b095603812445520b510f07098949015040c40b51803103a10250000b062a00705010000c451418101d00c14022a50344001038256103901141d200e05450303000074002c42c84400c0041641103040c03a6a901c8aa00e030002d9a00da80342c40125901707041050b11050a04980941c4150705200d4044501741c0360000220361000d000381c184202c3c1100c0c15880c08034205040c02e40c510a0142e2404040040c1020503115200d2a0322001ca40304400c00d00f4103150b80004e2500c002200034091120048090051940b80500103410718a00301e0545020715803180c06072006170381c00b20445903059840140080c1e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 574549181 1250 574547931 574547957
    0x608061906030222051003120f05040b0d020715090206030408071b060c0b0609010b04230a0303260114090901060b0313170a022a030703060e1501030210 67
    0xc05082540d00c00780d004107030403040c1c0031001c00300d0b0780d2440000d81c4200148400d48920317031845405c00052001500b000744950101c80b1041c818030102c81c1258070b0b490020b00701078807156480b025600100304d8004882c0c5c0050001c0401c043d04030150303030a014a110800c080440350300031446a00c40200024000e400000b404410000b51b4400500170988401c511a0110703180c07203001d4242440660191964120807002450078940000880d050f1040641c0c41803c5c9441c061090550800303c82807182e180d003101001071410745440280000a500030368a03410010318085100d02c03001841c20100883c0620280180328149020728030344840d1a0540303c2e40301c1680c072015680c4c01040950000c4e6440d4074000148440a1000343d26090307118024060803107804000441007425108032408080581c003c2490501e004032403000c007042c0075041008600031820031100290a02890786c10459100d07a59200300040c000c41000f0300544900c0e003500003c5294195000604903e0340c850016007008082c1c11911 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 574550431 1250 574549181 574549231
    0xe0108150f10270f0b2d0904080a1101020a1e03140c031b04030b06040509120d02040f080c0a03060e01020d06180c080411010c081624060806 62
    0xb900030715404440c04089082c41c0015188102a08244910b0780c0c107002e11801e41d40301030310550608101c02848003840310300721003001290318005150882960440781c00036a40b41c0761065090b1085c2d20aa1a0741d540345403031980a01000000c2c1c040e894141c2c130600c41d40300065040318041c030a0b21064840120340ca00207400440c00780075180740313000ca034564601c00d101826200383c01442c0240103c103000038540f000d941c00c04107940150320025016a401c44003017000f60800307a01154000d100340c410f43e5030404106003409100d502001e0703001078850303000504001c2c1c107040403d5a03004d004000c5c046c2c60210104c0c000605850940d000180c41c2540e12280c007090318100b5811965460180001403010340c1d5030780180d01070038404000c50500141016448010b447c4600d109034030899020160500c058071701c400454040300c00000131620343e602000f00d03618145003004407034034440c400d2078880800b9030360b114045031400700c04801912580c01c003582030080010105400c1c0c1d02c42c4900440924400040d8908 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 574551681 1250 574550431 574550461
    0x8010f2616212d05030412050c121c020c0a080c090601080403090b070512030c18100c03140403020402190813020d060b010e0a0f0e0108150f 62
    0x4010510500406010300200a00c01504070b40d682480d00703160a81c481045445800c40301d800816415200d501d05000c02d824890800e00310401c0a1020003400309079079010300d5588960060040391150108030000c1080401074a031504200365001b91a074407000d100940c3c2e584501159090720904481d042c8403041c070820401c409100b0040c40d02d01d07500c0e6140f41c11620340c002c014945014840d600002502d650003441024041c0e989035982082d11468601861216005418211858081c44910f0f200402170200a103000740441c031030b01b5907100c0707006803110000d04844202c039009880c407151040f031280e0040c0f6440800b94241c00d1502103004208035189041c0302e6500004e42c02840072480082151107090706001d428500d49078035116455401c025600340c007024100035442500001d41c540003407602c0d002442c00c0e46040c1010308124084800140c02010365400c00e0031134a4003a01d040220495000c200740c01130019401618015036a100415a4520005e00541e00c0c03000c8003000c645048e1040b022 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 574552931 1250 574551681 574551749
    0x91504081b0105100305060a05070c030c0501090c03062a0806061b0601080f070801060b0d230123010305040807060b13050403020132060907090302030709020309010c08010f 76
    0x801031071070301510b0543c04d1249070106036502d201d00c40c00100340c5211481554000c2245490318501351072150303030403218042000340840715952500c070404009803400000d00040c6103e1100450300424101c0c0c3c03540d0003007038403040c02e4006480c050014003203034002c0d4805030402410341d151a601c842d40c00806032850761807030f143e20303ca00c00d0300000070b401d00c40031984c503810660750800c0d40d2040d95030b90f04107030030303a43c5c0c500440f0840da00400c80480100384031740c80300961700348000400151286d00c0095107007441302684011600940382d00e50b01182940300c4240e4031851000d08007008242441d8403001700380d000e059401049a9a0381900e29015038603100c81d0540c00c0c05040c014801071420b840c0c020b018022506811401a004030500141c008004020752101300d69408100c0060b680c1508004001c000584030f01c00340022010701001680b414019540074240c00c1c5c101507500c0c240520824211003400b1094800c00c99150b005000300c0c480301e0485400c0716940c000400c0c801c44d208600c480d4036005401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 574554181 1250 574552931 574552933
    0xf040b0a050607060207050105072a030912110307210b10050d08040609050901061710080307030207050307120b010611010f140f0c031b0c01110f04030b091504081b 72
    0x1040f908004a9400901c1d1a620803c000d00458403603080542d903100d043e12109100c0403501032041b4040103582c10400805000740742c5442c0f00c13a990110780f803c0018002d000e4031030000075030100340c15041c00c010300c40050900400305040240041c41902c40c1030010407005010300c600d407020441840b01400c602c005044020440b402c42c078102e01c0d01212640c003500c1485d000c10700c01ca800080b5464003d110504035401902d8104169010300801e540000005207110411880180080346944040015181e4117210381c00030440641440105071801f041a808078066002d02c1a480c0006081c201ca2181190954101070500c995881116805801040c1d00d149035036141094807490410001d42c802e006039044c80c8019025210000024034512048032051440601f620000e03031074061a1001b8003121000e0400094100302c040c5203421150321004110440101c041003d2051000e080f2119401c00d40c00d00003400b480c3c0d010302d014980150700400241c800c030004602c8001d050b025480761812880000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 574555431 1250 574554181 574554187
    0xe0310050c0318071802132607240c05070b030f061c031e110708030307110c1f1106160e03010212040b0c0d0515100206060f040b0a0506 60
    0x3021141c898004482800200d14a14008592180c01080840a8074008400c0441c1c1c000b00a8418010794046400c0081708210400c0016245100140d110140b50000130300b60303410381d041c496032031901045410824810b10454200402015416083c44c400c100c14104035100c41c581d810400c0c14054150b001014542d000001c0055030b644100c0a40c3c41500c00720354041d04000690142c0030110840c1000a011a141002c0d00c0c000d043d9805542803031480ca45440b00b074000451083e1400c140c00d40e4084001e650010087c4545260000960490707841c01700010328920707072414001900301012040710100c80c180c01d0721000ca00b6110703503c07002c0d21903940801c64641e41402c8141118400d081e40c0c3c07050003e0074041400b00a85410300858081050846020300213844a48480107508400b41202801d0002000071000c00c0d81c25010365403160a420354008034440b25070003400545035501d401001190443d00801405641310804812884d4098030006120300c0040b000c07484c10001908105e50004001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 574556681 1250 574555431 574555441
    0x60301060f1206050c1606090b1617090a1403070501050903070c0303051303080703080a110903150703021b0d020c010906080a0b040e0a0b040c090b01080c090301063803060307060e031005 82
    0x52341040407000d2294038024166510342e04807600301c5800c650420000b030051030043c01d41078440d804041d0059a07140c04e94046900c2036403038240d179103045441106950004100c00003031110a104a6038801840c402031842d0603000c2d03841c040e1102d800d000050a005002c01c4c9900c07498000c2d540000611b50080c5d40658031580780c207000c4e0202c482260b20b5070209040484800c03000c40a0400c1d5842d00c1000780040010780100c030760f925841c000c0281104200740d400d00c58505c08527018040c0000c030841d2440602914400c07188002d0401c0c1c0341a034054184204e0110801103540c5c41440d840c1c2c0030a124400003800d9001800003000f500180f0420078480c85600d0540c2c3c1032000340244540628070980040024603581d10841042c0d480444103503010900d0b0700001422171030703a41d00500e001d030001000010002e0f11401d03e80070041034130345010302001001c252150108813000c2c00c46501d2440481c40b50840c5454030000750f1342c41250203030b0010403250558031146070300d0800400c00c0d03a01c0c45c1c2c4c2e0305115a21303007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 574557931 1250 574556681 574556693
    0x510110a1406091b06090603061903080703080708160c05070803040f050406090b01020c01120f02040b030618010f18021b03090315040f080c0a02100206060301060f1206050c16 77
    0xc0ea52401d45000c1c4912034031000b44c102c508011084001740c400740c20300004404010300d41d007000380520b4000d150300c0c10790302c03280d102c05c4054400707513114100042d220348050400801044000303180384188002c40052107400c4880081c2d400d5100d010b45048490400301d03207050741c10084607600400003813001181c0030800411032400f5005a4801355000c009465603203e00c04103480800304040e0141c3c11101804503554820070f40b018602c1c140c0e0001217040380444030b02d0700403648184e000d5958070300088241310b110303e8100d903200c0e080380504068810950400740000d0760002031b482511191410942800b920702d1090301501d4070080c2c05180d500d900d4080400180c1c8a034407007602e0034840c3c01961040104c0c20395400d0021f02450f0042011903120f1510760300c80c2015030008071950941c0c4511501c0f4001030781d9150194500042e40d6000e07069a003000341c14542503501b6a00700e44c4100039118401d002050082d44500703011074201038049440d44071010000d5182c8144a00351a503102081600380603c95 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 574559181 1250 574557931 574557943
    0x50d02010e0d021603230d050d0f05041a07140403060c110307050304061d1903020f030a0807080906160503040e160509041a04060e1f0510110a14 64
    0x30507501520303280041d821040740c030b56014986924507021002d1003400814114880c8600c0c40720440d1841c5109403100740744924007600e403901c0000281d03000600719034900c40382c05203c1103103d204800f4092420541e0f2071100b51106d00c600d5242452180c2c00241103d40310781e40069000d01c2c20032240e99035170784030305051001e00004a40400429014198405140800002c44000e50f070000060742c249420100201d440100d445061001416400c0300600350703986e50030304101d80411060402007214590b105000602544413001c600c00d40100038640042440e82013150501d580c080c4802c1c3c2d5861540b07002031181c0c02108610303410401c40e000c880017007001c000014020350329005140103196480c81c141c500190003c01e01840060300622084503541055008402641d0b1207841d40c0c107a20342800302140490b142ca61062902c1d4403c00180300c4a040c4051003804040002c18a40800d9802c1c500030640c10000b680c02c5d40308000049001805420051120a948940c030000102604001d4455650340e50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 574560431 1250 574559181 574559201
    0xd1b0f020103020d0e0f1c090e1b1804050604061518030614010e0f061e03071a0706060b0c070e090a060c0e13050402150706140103050a120311190507050d0201 70
    0x120803104d02e51700306452103c7c00c220f0b2000c940c0e0b548000c01d062400032640010050500c1044055a035142c007005603c4d100a010301d003c072502d41c040307420313041020001622000340000d8040d510749001846140400f07012060007050301c3c241050603491545c2069001d00e090703400038085906d01404a20103120780383c80c040c1201c100305034065080d2075414241d07003204000d03140300ba4090084070280d900381a10540031034587d440141a120b03000c4c0d59441400d030140d0240010070443d000026408208a02c610030500540100d00301c031410076054046140c1d9920f0340d0b004801e00c83c10702e02c0004038214010408001e034107501507002d008814070030030094055071000250b6446400b071800c16a89650a5100f01d52044e0b0f002007008400240758403011704241d000382429503c040e210200d252405010259480c001d512800042045007240d0501c1e84484645610041c00c2600784007940c0701d0822002c041e42d45510342c1c6904101951507c14042e00d05206030344008005008818400c011540c065210b40603036 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 574561681 1250 574560431 574560433
    0x90c02151503070509040f061a0a08010225051f090b0a020306090f1302120c032817071b29120601090506040b0403050d1b0f020103020d0e0f 62
    0x10344a0003010340307007810a414030036010b5009034020002c52a0442803140c00034025411640080400d072118000d41c1d04203100801004d000b10150740690030a00342480c01020024000c50070030554048600070300d400c01c41c4402804110ba00c0c400300780b0005103c5940150350035800d080804030384555641c00380540120645145a8800010345094414000c4038030900e0024441e119a950701c0c2e00902c44041c024086100e9441c120801c0300c0140c03a0800d04404c1621030000074950843d0410400d45080b060907000c0c0719450341ca00440d001108070010075000e03150310070b410b852000c02d80441c1030302500800038040c05c03120b503402c040b009610701d036134204085c0c0d44a00040e403d11101c05609481000b0515881103e980c8104040202d903443c0249054202c0b0052618100b01c0355540c0005075160070540100345680c000280c1003082150802042c40a90301c01c1c2841080c091030070500d03041e9616420006482c54044001034402c580c4a64111914506980f408010a40d0400c0c0c0450b60381e00c00208072001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 574562931 1250 574561681 574561723
    0x1b0a05090a0609180b04120e030106260a0b040809030114070c050d02120d0902120303010305100f0c090909030e04020c0d08090a230106050301050c0d0c140d0c0504090c02 75
    0x101c00e13031295030110039400038059400b94039561b5558112001000c010410011350500b490040d07503003800b400004000361400350444208200340b0f800d4100328102280800e603c4852924000b901c40c0c41da940c2d100b40c11410710398030b17030b603502000c030b03015080c554500392901000d8000c1003801504540c001c1e0415029500715001c400c4d9a0601780c1e543c5804502c03c0500590034020300c000c0113207540001e81303c030b803010703020b80c81140c8180700310361464000f80c100300d4175908401500842c2076428032a0301c1a16860060034400c0c028071603000390180005000d640c0802e03031501c41d070b502814010b1000020303101014008541e20315090514a0722041e0301c0300450000380e82c0c000440c0064a00182114405400c0050540c1445c44200c003c4504005a00501115500e4013000207241d1341c20300ca1144500000d03505159120707401c40b0b00301d046034254080c00052000072944151441801410f071800c21019520004500d07902ca00d09550750300540d031194580500707003481c00b10481e40c0440c2040085c41070300b0760451 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 574564181 1250 574562931 574562951
    0x10120b03030424231608030c2203020d06240f0f0e0c041202011e081603020307021f060e01030c030506010b0a020c04020f04031506080607111b0a05090a0609 69
    0x4104408180b40306080356142014046480d03a0070040001d10769185d54480036924559610b00a50002c0314100d07032107440811240c0038540c9080380a8200c1ba004030f0b000e022181181d0009080082c100005024141e031402c000030a4003658501c00b50b04150b4111300300c0303101d81d581006c0b250302105000d5019540c002c0301001401c6203610503058043c2a921405905003800e10740c50a45149140c401030341045440040d980044881c400c813142a2480e079518520989020061190010410b600e100209441082001f58655002c00c030300b81c0321a81f5002444031426814000d002406543c1c00079080f45da40040000100603100c03410004482c416802e42c6c5090380d80d110312841501030515500056040341040c80030714a4164010802003021603a0780d81415100d03168800310040039038048012581e1101c00340b0181404025440d40100f03076190004080c050235001300d494200018007009500303050000c550541d5507c0c940940a070001920904040c684202c00002a150034458403102903e1326403814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 574565431 1250 574564181 574564187
    0x41a10020d020a0f26070c06050403110409050f0d05121e041b0f1e14060d020c0102070b10030c05031207030516020a090609050606070210120b03030424 67
    0x110140031507009007100040c3c5484450300105140812662000c05054003080302c51a8003204c14141034083da05902c81000d49010804004960030800034848144002c0000131955015005180c2094030003081101083c031700603103400b521040c9141d150162000e01d8a06c164000050010b18410902004080e01d0f195034900d2160240040700703900064900019001c54182941b8100024070b6410854181d503482e000f00c83c0c807010a4000b10400c240340b00d01144900d9460340d004018240d50340b104e103144803050000031080c0c424203000803e2180c0116000d071811400307505a0b16419000649280c884c5401d00101d000c20f411800700312080342120b040807856040000344011111944a001864050103032001c3c1c5a642010350143e8904041c16248801030311040c50382c0e070040c10340791404610709007040c0c4e520007900c900400c07a40c0503400900c0702d00007607a103000c0c40384400f00b07590400348110031030460458041c112079000f00b5007610000400250031241c0b2607031041044c400d41600304204240640813 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 574566681 1250 574565431 574565443
    0x902180904030905062508030901050a1b1b061419090f030c020d21030b010e130506190b0306010908010b09180a050601080c190e0705031005041a1002 66
    0x90300083c4640c0c400d0229041000041c031112440504106040302c0c00c03584407568030130302001294402404014007813100c400b4021107820518541003442038822010b85032002400c4038802008110111540c50013842040703610320420760308030006000c00c0487c1a6113460062094075405400b80902c0358091040c0b5052003603040c0315501496001c25102c0c0c54404032001d94840f80b060f07a2100c0714541c0c50700000c40c1040c0444034200443c00c505003403800c0d460003408a440c01d100f8079061102c901003801950f42c800e20000016004850001825120200450311100030103000c450610801200840c0960001c0b010310b00c500da00b41c2e510303060745032110821801e80340b46040e280d4100400102007201d0f8424172641d0825005440d04840501c4200d40b110340c5401c5003a8040c0324181c00040350041e032030034a04011015407401d1164070305814641240043c1030240100007008104001c808103104102e40c420343d00081000030801c2c8022080c40c00180b03511030402103020b01c5807285401c076081e035500210745 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 574567931 1250 574566681 574566683
    0x31305072111120607080403090f261c09050324060909190821010305030403060e07090624030e0a021201110a0801030308090703080315190902180904 66
    0x440000d02106a4554408034501000181e1003c601e9082a2400c501000101d100d48003030f41c0c1e1000d040c10b2609000d400e403c140e41012041c42c1503018244000c045150210108480544015000070402002d85080201c1c100e2400601444e2501800f00e00e503002c550a0250341085082d160000342c0e04038547c03050000314400c0d01040203c440020100d107403004c00181d00500d400281d4180c5808600501041117124601300c4600d44045100c1d000918040420510320b501c00144090380e50450302d4042c1d032400369110050410341c0b42c8000081c1c0c20301c140034010080c04100801c0c0040e6881d003000c081d03004410f599603203003040186000c0c82074502c640a803c40303684020f8054400c240a40e000d0110342d20000321189025925507000e42e1400b45c00310010311100f4199a20104154150320700105002300103004500ca5511240342800410284012641c0107100380d440780c0000200c20b00410040c070302a014000c02e030304110a0003e500c54540e0001c158540c00706010b07005541c00001040105002518 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 574569181 1250 574567931 574567979
    0xe04110d0c0f150c020d0c0302090c131a030c070f02060a03020a02010b010305040816020d021305012c0112110909030d06090239060103050d03050f07020d0f0c0803130507 75
    0x1890134054140300000ba030f1440c0c0107136070850710a902ca0300490104042900c4e070711080300c00000d202c441d07031700b81c29515800b03401e280306000c60031140201046402c0c000500302e0180c24000050040821108400e010512a0301804054540c045c504c4040d000350031405108000d9400c00c801000d0541c070921070386100d542d00c02c60301c50031b007000d203803c140c0300100d0303181c01300e07004041c20341000017607905c0d5606c8051941c09454042003640c104000349074040e02406109494881203018445c08510f122040740c1034900707848204020110604103d2107241c0000c10341500039242d2801e010054101100920b449003501c0c2040c001c0c16514803201b002c078400d4070b20b08020104120f01c00d042039100d9006602d50307804c000d02070420606005a80504106003a44120303490703800040071020702078140c01480c0c0d000c00122031038141464510b402a4954250002250400001c081421142d900030f450040280350030a01d4503480c2c1c98050150760415440e0750f82590180301e500f00010b08034410f00640121410009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 574570431 1250 574569181 574569197
    0x6181b042a1e11100f020f04080a03020715050403020d080f0304050705030d090509010b131d0a1808071104150e10051009210602030705180a08070e04110d0c0f15 71
    0x300b040c801017201c1031038000d11940801000c40c020450b003000d03001810307940e0080c0402891500c1d0103898401ca44c0c0c00303c8580480d04ca4402a1540c100003502c00700c0341c054444140d0030081d460807641030700c103030140c08103040300c00f00030f001c1800f0700040c1d0b001c191b4409800f01e030502d0001001c140d559929510071941d204040c10014800c20402202409140c00c0e1542400300f4aa114114a10050403020100308995000303410804c0c150f00301c0c041d80f9451404440b2914031b00c1015113a044442c840d0304d60181c4125066902104a45c965030f20010400080c03005c400385d050707190030203000d1945083d52090b0007000b055002040c0b9140a05401d00c1c0c0064071340f24104224038202081028028002d900402c8520a000a0010a1844c0021413042549540780c607a503000c1031415003482c042e44040b190050400c0c21061100a400181d14000e032054400130ba0500c0e942d91a0800d890502c0310245da401c0070458540d0800c01c9a10701d214420703140c801c40c000b2902078407804c114081c2601083c41c1c4001031581 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 574571681 1250 574570431 574570453
    0x6060201020f0d1d0d170f040201050d1509110403021806030601051005130b0901121e0f0f09030c15230c071406181b042a1e11 56
    0x680e211038181070211285042032003035044190f09006010082801040d018402003c06e041d40e018125800140c10450001c00c1c00e041d0002002c40c000c00600d880020340e2020621100d501142c0d10380d00625401d4814810200e801031080700582007840201e00030400c0340301c101c00e010510032f5414403600c006030041440360301c3e1a040050805034040c080c0c00380401006203807000001260f5840c040c107000d048160392140b448000400241d2517a0440e00d05503d0040441003035010660b05d0115a14110404521891a046040010010780da800c801d55850800e01608043c0c02891184c00c190003060546e1aa502c4490300d5026a4660258100c04c1d070a1104000d0b00c004002c6011030f000000f8900c201e0078540c3c0350791403102c2a00755a00b5003400b60b10a00403c0180c4c3c18210540082108400c00350400821520488641c4109000c045200e90f49a40228bd40540118143c60100c030301c0c4c00e80207109104440307001e0b10174448255041e03210070307154174110b248601440c151000c80c000b820080ca004504 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 574572931 1250 574571681 574571707
    0x304060b09091c0815060f0c19020f010e13020309010f0603150501050909070312050702060a0309050d14120603010905031303020f0913030c0204020c070f09050906010e13020409020904140106060201020f 89
    0xd00c524082c0c07854140415044008e040108038044800080c0503018030806004018070700425048041c10010041c1002d203483e1141d05410102d9040c1100c0540c0300d448414210303024151864016141d01d15201c2c0002c00d120320856900c1040142260400042c0d03290814004000d404944003422030340038034400c00010348840d54a09a840451500b0b900b8518185d0018074554005c9c502c0c035000a444050b448207001081c403000302c04003081e0804042c1650f00034a02000b6000712441a0054140711000031501e840a402080125600a01b581d039520454003a40c02100e40070b0005a00440d500c03201e0702c00c507040180c1c500d40031340050f10400d000c4007941e80d4201c5403240c03020070880c1c20940a21904143c0c0c60704002107006840001611341c07503a420204090101c42c1d00420354005644818010840c130311a000d0b9940c0c0100e0103c04004543c034036800802d000d000c03c054001e4000741250104000d00c440700c00c110860301c05a500a00001c1e9542404034282c1c05985002c5803400000c02c001c85000e68 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 574574181 1250 574572931 574572937
    0x2010b011409040b040518011a030d0806061204051b011404050d020109090e0703051912050d0e0610180515011215121b0303080109020304060b09091c081506 69
    0x30b004201080c1a01a44081025a50180d6001d000c3d0b0802160010300c100084c0100482d1189122170034521182500c0003c3d900c04040f038041d030905c61102c0106007152101c0c03048400e80303540900c1100107420540b41084d62194042010f1301150507100c80d40403258840d007006561b09030841e0681e8242400c10701000b91084112030202c2c140034461720005030b40341c003e0049194030210800642291459810320a0603e1841d1002516a00166210500052901d07485280900316444d000781c5455070043c40c5401026084000007903882240700700440e40c0348030b21448091342d5a450702c074003a0920301001e20040e9441600d50010b402500d860000a40d4401d00e01d40b503541d6003012011038691080e41e00c400300c0340358503046016400080d928042c2480510540250011091000071440d10f185850050148506002e12000c4940000100741840300f540c0107c1c004010003480300c0c040e03081c80e000c1250340c0d013507024556045c001d65149a5403141d00880c0020310520f03052100c2c00c030444401007000490341c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 574575431 1250 574574181 574574197
    0x30307060e010e0a03020f0c1c060b030a060f0618150b0a050f1602010e0a031709010c060509100e01140402150408150109060b07080d0504140f010f0c02010b0114 71
    0x140d43c440076481802020480c024140d40290080c1c48402c0b60b46c90943d0030400c03a02c0046000790401a150442c07031415442d01d01d015074103d400000c1140b20f12002900302008003001609403404c040741c00740c80c400344e81d000d4800c0b20035011102e6003402543d809181a40c0042590452041284004200c48c1c1d440b08001c01c201c07001da2070000d1030820320f01d29031440341e000020040f2941034041440011960402c403030041401080307032020700951a660f01d416804c10f146600b4503206c40e01050103005a402070042c6d00c4150b500103001c2c422840c015244c335542c0c4103164000fa03007240c2040800c008013001845400a840b408000305004c694854083c00a9a050314000034130301c0ea000c22001404440510548502c5036170310200748501c3d450071000100350b074550f0700a1641c000301004054001503404088070600c0d10810341c04a299591420084200140100704080f64040c06043e041c1e20135040d40110b1101b500c031203040240e04028a012400c0b189283c4500d17010840d0811901218444840544100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 574576681 1250 574575431 574575433
    0x5040c0c1b0519140d0b220602040303050c2a120304030803010e0403030c050405061b0f01020a110f071518080a03031a0f0f130b09070216060e030307060e 68
    0x5998940200d600d03d06001c1c01d03140c00c0404880180f1603180710990342d0908103000c0f544401c0c01d140c0c0d074541540742c1201900b410452031603101001d1b010094070624484640e04a05c0454403140d0300d0401030010380c896181e8001601940c11035225411305940e510f203076000c0040d0100302213111013042c84043c400f00308007001c0c05d01c0305010000001c1c1b6510003e5010303059202401001c1d090900c0d0103402d603001c0c0401041400780a020600c100c1d221001038030035848034403000e800302c050380d98112414201e48040f0800300b0f50000400715245d5030080c9c03044042140300d10848070204540a5442c0c3ca94085010b040c901c4042c440ca4a8015071081801f284540b0300849491080c1d0354a4458503c0d11000c40422004a51548020440089071001490350284143c2e0401716141e49600003030341c5802120f400383e1084030304604010780b51111b07a2040202081c054445019400d02d68006551051880d51440c2c000144420105460b80301e44000c01c40303038101800035800e040c49940e0b4500501014000d140700e07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 574577931 1250 574576681 574576733
    0x1517070e0d140c1002010204210614040503040f050402120114060d1a18060f01030e120f07060510080606090a090803040c080709060f0e1308030a0506010905040c0c 72
    0x20954268208041159542c010005901e00200f40200540b00302005000c1d6403040c40200241d03010a0100b0b255011262000345c6607081c07030701d812030041007068000b80c401400c04040000304078000004105a640099048004903601e10410007a44608000e807032070115007000401c41c0c0c000010312440c1941d0028505828580307081c038020203e81010010340102c045e41541c50344642400d06100001103440300344807010749040008128a1086250941d0415503191002000302c41c09218141c0d0903245501e159640f0551550000440e401480e425240356140102054041c0f00c8030b004402240d031603a014142c036a480030104580c1b25002014158210344804080c400030b0352b400005c5105920450310b011085040000092400140b45c1000e0061407810718188903030a045031010040700c2490074900340c1e9030f0341c14040318041298208002c0c240000031081c824030240b940c2017148640302c00c0e641c1445031582e440801c001e4580d20074030900410380c040d010700d000c603496203d0100004151081e08031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 574579181 1250 574577931 574577933
    0x11109030c040b040b0618040c0f1718030d090606120b0f09070905040317010807050604260f030d05220b04060e160305010608160e18030409061517070e0d 68
    0x840b47e4071201a00c001700982c005038a00e030b0303d000d20407200315100c68581114071016812010384407a82c004264520600c50800003022012a2040010307051001010380341ca442d42545444050030340d42d00304890260030310402144440442d0800340d2520f800003240d4030503884001901c800743c9405041820940101034012420b1011400348500075480307544c0340740880002c00c550004d0560180c2140400c1d41112008200c0356454400f598152108070102e004041c80f01c1440c030800580115403034040b030040e40896407842c80040050a00788130003000511080d65400e800e1007809d01003038031300c003481c00d200ca5140020443d502845c580c000d1084000181c000310011002e890202c0c000d40404031307817501c040c00b402080001c2c040c00f03000b0a142c0d001800c1ca1255107803001480d41036409448240078a81c400603d0b0450108001c0d101410b000e810390350b94a8840600c1c0010344010302a01d21481d003c9003404172141c0c0304403003503400c0d445d00d01c01042c00d984400d0800c8615118948203103502040c40c01d00e00c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 574580431 1250 574579181 574579189
    0x30f0c0d060504090308060f03070605190903060e250608010603020a030e1e0106081b0f0102160b040303030b030f0a022205090102070309060f09141305070e03011109030c040b040b 79
    0x15003040c021b03212601549044001c00c2030000014241500039003202e4010002075030841d0540d0b03121101e0f444a000d21001200045030306402c9944040d01d91800c15903a4140d0103404900351899109641c2d03c40244041102420000c02c3e42c0e01c2030701d001460240040002c14800d602614030326016207004100300308150750791450700c42400c0e1800064084100c00c400d420070700f44259001003000b0300160401840710b400c403199209040030740c10b015103265401904aa0310a000a110900340085807107001901c99414504540080c0000c034046850800c0861031450700040240407000d1180052885004650030301c21454202c51065410f450a0201142c110302c06000c3d262240c2c180c20700060b162440c5080040007140f0300e510071400c1c044100d00c0201107031350080518059403007007180000d2001c6490081240d40024142901d5403a10707280034002059842a01006c8100d4110007d001080b0030300114091486065401c55159001944407101380c20710340c224009020004000091080000000c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 574581681 1250 574580431 574580441
    0x507020d060c3504061a12102d09081308150106030b01141608070809010e010809030715020d240f1203030b041b0201060614030f0c0d060504 62
    0xb00c00442c030210001c042012050000003d8102000800202c0c0038001118442c0440c0140019103410f440307102903203070111000e1102100d00c5020700850450301030300c000d075501e5060000151665904049039400c1c0340e0704034414255140c0d1a10182c4031080906102440140b07103a46007150810800d1000700380c00001d6259400c002c0404034080c0030000c610701500070b03031128141c0250060500d041c2001d80603991241c0c001401c11040c544d0f1a80d50011018203a91150100d40d0041007800700190580400482101800c8071100a0326041c0d20f1505203401921401002c80b40049164024482c41c404a20002c1000b01b403003444883c0186000c041039400800d8424140041b084852010170f00180d80405500d20030051517a609030762500c6051a810441c0e440c11003401500b05034480f07442c0740d034503625a400492100d20708030140030300440880300a80030b01003610590380400c110314409440c2c00510402c43c3c0c03180343c825a44010560316802e500d001604190b00141000f9900c800114460315240b0032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 574582931 1250 574581681 574581701
    0x30c100903050609190f0528050105151e01090518090d0503060f040902180a050601030e0303040206040905090f0601080309151801030c03090606030803040302120403120507020d06 79
    0x8494030503045051440c41c002000e0808252588000d43d601c1628070545d01681d45180d208284d5a121602d40c20301518001202c00c06061900d1000200d2011034405000742e481035219000a000943c0d0720345070960120b0120340403640050b01c00103c8a003031b0804050007681400c050501c0340700d1079110008100c8040c0e80c80e07441a1306000b10030134490440002c00c9611900c01d141e14103145107160010100c0c1050070040419801661185034080c11980c402002c00303411600d92050b000d5901c0c00000d4040600000c0e00c000740800e00c0c0c00c221102c01480841201e100d00d40107805246414603003101c0a00a00f0024140500e41c080d080d402c00c4014000d0000070b0003043c41100031501e44424000300000080801d0346800042c50421105680030160750042e0f1480c0401d080000780c982d2080300580103401c907030400034040c525101c0c000c0304100840e80030f10300542c003a5080f0360030400403804980941c496030202030032000c9021681c90801d4803680c010b1554610117880102c144449507500030a0300c100301c803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 574584181 1250 574582931 574582937
    0xe0a090503070b06120a0816110405040615060203090a120201090302060a02060a0b092707090c0221160b0c07330c2307080f0406110307030e0906030c10 67
    0x24403080e0324045215000b400d01c3e100190021b60007994511446200360004e1404034004500100c05001156160780d82d00f09001d0f109215501c1c05241c0390004080390520050076054140c00802c07858400029105005006070074500038a040030511401e0211214080781009030010010006803200301c0582000a082e400070101c60400c2140142a5905292054040da2400080054107402140c1802145524000346240700071610480c03402e168103600401056030604c4400f000c11580061500036112111184d1810004400641d47e05849400c5404407040181140707a000720b00031525480c1c00030550901245440c506a840c543d050000c030650b566403a803210b0018042c0c42c000022100c0d44120311a0412002d10400c2c4054000f50005003420f4201628001080303091500740704907040b10b50081c1c203c0751100c1d80e0419020880d405400707124000764808142d0181030b0b1000056070321030f940c1074480400c110721140c140301c80000e0061402c0c1d170601c590701d64005240c035403100032041c0c1c0c81c8541e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 574585431 1250 574584181 574584203
    0x1b080a050705060a090f0204091b1d0603061006140918090d020c130e07030b0c09010f02010c0f08131a092a0108072109060c03050405070e0a09050307 66
    0x1c01e0003800d0070300c010804c0c44030354240511040001d821541280301641c0c111000905a4114108140e0b1601c0c2d84a2400c0070600a07880803c02450008011150303111011155000c0e9407400103160f03c40e00260354580300e80c0ca46a00030b102541c002d4440018000a4423602c0e400c000034140000c4c16440181115849a07502d0403d011043c48240003001106071107000070070040d44102c001c590f084804061642420350b455000421f40d01060001c0d10040d45c00405070b03080d40c1030000b41c0744c0b405d6000c40c503c40d010881038144254040c0c0180540581c0c1885034980f281a04001041620401c0c0e00414204920110144071800100140071104101200810841041c03500d015070301c7c50000c084041d080039a03001c004601100090f002020314840c428a410611925907050554961008001c105070400d02e00032040c0c04800c581d80180f00040c00b50703105001c045501c45064080b141d007914040c2c9070360094031050003107070703075030180c498001c03004550004003454070391280b030f0668000c0701d02114114905 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 574586681 1250 574585431 574585433
    0x712110d121a01121d03030a02040504050601021f020306040209030318040609151701021201030f030e04090308070c0203030415120f060b0d050403030b0a03050c1005130302011b080a0507 82
    0x61003040100018140c26040210750704001903c0564810b445111503922203560121750170208840c03ca04000d00e4046984900b070224200c406500b01e8041d03103001c1c07480e200000b045503100050850310106000c40861721025109540406540010480d80d0847d808203d9000d05032020001000c0780c000044040820000790f904120a40301d41e0381c026a05035003080780c007500b030101c540034900031208101c400340c05c01100884c109003e030041100d40c6103a218108000018850141c00c80f804441c400e54800c4c903041522010001201d14400d0041e00144c0d0703107000614130b58012009c180b00c0a00080c2100d043c103686105200c504e43c10f0a040e1030006051018614038030401c3e0140c0c103820640c1c0300007888220f050803018401d60084403002a00192100045070070315001e64007119403114090941403001d9240d0800a5480c20940c040354019002ca29550110301c1c411400d030b400ea101c070300480343e141920b590011110170401a030480b80c581600ca10500010b40c0113001011090300940303942c0d464030a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 574587931 1250 574586681 574586717
    0x6070303020322032615010309020f09100f082803021c1805041a09100b13030510050f0105060a0201110a18080a0203060c0309010207060f1d070b0712110d 68
    0x3402210300001011030144446c84000c140741a80d1504203103800a1000218000180c1c11160031591941100b0b4003001c2c005000000c400780400d48007403025190382c2c207541d4070b4011394980e60101e125480803255402c8030703220180c41c9641400c0b10b001c2d204903140590381590203100e000c61108084c01041c101c10100d03c0440e528102d01000300f00032181042001040d0080f01d40000e1800f0410f4410307101100003801000c501621980542000c0b41c40d0740c0c84010101e044844107611b4001980c0c244100c0c281852030394014007555201f01151164041c080e480c040c180640ca800c054009015552202948135260001c0406000d0103049a5190191001c00d4401b0102c00301054000c18802e410600502002d6100007a04c5600003e554290036070f00d41d10034070700500a000d5068000c0c0b0180c20f20403006012515030700041c1844c15020754410911151000701643c17465203220310142c0350414000c020206861040d0030500340707054104034079005000f5842c2070a146a020044010032155040072030b100e00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 574589181 1250 574587931 574587977
    0x2030a030e060405060c0a020319080a050a020910050a052511030d0e090c04050d061e09030c0b06030106170f071a07060b04150e090609010501050607030302032203 72
    0x301e0710060800c1c0e043c192580ca480d600f0042040c19607150010300148064401c00444142503540001200e143c0c07000b5000901e1502c0a07902c00c403026080c0b101050102c2c446200701c07082e0120050803000043c080d200191240d41043d51440e00740007050003d5004070703940a9040e89181c001140800100c48640380421100c900300900038060b03400903080c1000c05812010707080e80d1110440e500141691804440f003458404d582015400c60580c0400d6010000250005080c1c20054507560506683c40d408581c00c4034181c10000d4000f9014001e8007001c100d01c04040798121101500200300152a0040744d107010344403c4901605030712102c80c81d401000309120790009000a000644051058900107a40c5402101c0024002d03c0c0d072098002d120307075134035401000842c1d0360000b680110b555408000f181c5080071101c014290180c0d0001407000c40061007228180d500060541d801c0c50b10640b41100250401491003004181c48160030203915200c2c004041c843d803080c0d41300e4422400d105082d600300700d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 574590431 1250 574589181 574589201
    0x609060f0513050903030103030311070804081011090d06110904050c18041506080a1e0207030e030d090b18060301090b01020d02010e0607122909010f03020604091a1002030a03 77
    0x2807030f0106000140f54080121390440360180345c04262071010000700310451044102c0184100710006001600c2c210209802c0c00d040718200c2e04124a1018101d8004688103043d1043e0b1b00004084002000501d20751000e941880700080060920261710045001c41b041030724880b140c0040490250074100391038810b40003000c0152400c0c40016010300b900c0100e861917014110621140c840080c00c0c50445074041c04010194482d45003000e6403802c071a9000b580010340940c000740048148088505001a0200684ca6140d8405820f94980b4400c200719402490450a0010540d81c2c441c5031607992201450203840c1600700082c00c1c050500c000780c0323850b040701115429641881d0300b02003407280200300d1a904c41668181150f28103002c0c03007243e005103600c107151006d21303039900e1884418009866001420107003c1e5070100890344c803140d20020600e2036100096110784100014080c190058014164180ca810081c032035545c1c2c0f400000f10120320000c00c01d00103030320200d10813043c5036040c044d4080f41 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 574591681 1250 574590431 574590469
    0x60504021e06030103020618030d0e0f04060b041707030602130e0a1802100c0c140a0b04081f090605070804050714060d1a12030d1409031602040609060f05 68
    0x2228140100d0043e0005210103440355101103241050089a91280078041400500703444031030b80000d4000e03019104040c2298000c0c44400700e0301c445818648100e00c15100b0140c4094109032418402071a2104404150070060240500000004043e4009000b00340000da4506081c5070400d1113130940c03107000500c00e2010758180b803500900c000744152a540300a8060303032034444050307500c0020f41c1c0c2d400340020018040d00000f0070000d4410459800007070f05000481d2102e05540d43c074440102c00740180e0142140c1c40d0050500d00380c051400007038080c07005013401d9012440c003999458a0007180c0b4111080741c0440c4908042004000c0240a460007500ca17140340c5208007000c84001c64241e0091406100700240e540d0711200d0719901004508840200c01044684512610b800941e1a070f0450024542120705210200b901e603a00e00c01558401c11401c4c0046041142c206946202103420f42c03026600b090361801c0c04030b0050018001c01c0c0c0600b0404c000300d0b040c10b2403c000d00c00b10441c91403c541c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 574592931 1250 574591681 574591729
    0x32d20040b0d0f030302041503020c062a0309010f060b0d0b060307051b0708030f2d0a0503101502010603020111030a0c02060d02041d01210c090e0a0602040306050402 73
    0x1280d42c0e4010300a141600100c4500d82d02005207010390080c82250010f400003540da800400c00964035400901d00c0c40d140006581079511915417111300301800c220150b08180c206a15020703207207170503406154001006c20010640084510031681100c2c6607801036603030301030b000803915401303100c9010f03070550301c0e4040da4030781c0c0307186020400180a0700800e0b58180c900c40c82070440007403c2504000030b0340030b001c840c001c0d6640d503010041608080da0000317410907100b042420070900560b04443d4111208091655613626004400208562580c002080c120b001d40110801150202c1c1d03004500e140344041e40c00011703000e811070001404140d18180035142c1948100090046071f030b07100d00840401e0340e041c1c500b04e4a90700f034044604041c4c050780d044032450300c00d0025a04406180c1170b41d000d048417550700d041c46c2d040b4003019180035004048440a009803080b00303c01c20002c440f41e404140d11071032030300545090307421a583d03c4069030311a038026034140d5212014401175150020700040c2c0e80c82049580d00c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 574594181 1250 574592931 574592951
    0x1080610030506130501110c0a17040e150409060c021e0c0a1205070902070c0e0105120d050c15090a050f03040609032006071506050d03050301032d2004 67
    0x5030340c4a0081140702516950a026810040c0940001f0b1803038002140498441e50304005055907140e40001c00d50b4603049002c401c03809005580102d038140c60050304030280c5640d445480e141891080c902c2d00f90065034402042010030b0940c401c02c5261803455001d8040c0e0ba0340240303115003c02201508801c1c60300700000380400703580d45803520401ca4108030717100040b500146c1080750400d4181c0d48807040d514000100c12040101003102d060075034802659049069880300c05000c0340d068030148030480c50b40403040300d03034540d0301543c080d085001d0001c046400c0010141b4220300c040303006a40050352030744084c1c00c43c010000e0502400c0b0850500800840c03c2c070786059001428400c80d8030010301034040204080191440c1d041c080c0764000c070080e00071565084a480c0c4442c48103029901c040d10540341003400309943c80d04034004811140c05a0782c2d2070841c2d00790307111700da441000d03244041080c3c4026240f40702c40c0300d181c403001003402d40602d00d1103070701e41500300c1d80d000400002820030303104501c0c000810b5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 574595431 1250 574594181 574594183
    0x30807020c01170117120316020d080105030606210106180c0f080703020a171f060203043b07180503030f04150e06040807030302070909020a0e040812040b010806100305 74
    0xe41117505030200c101c9401e00d81c0d1040c0b0b00b40180f81107480d09401c0004100726140b20f000c1c40980719640a0307421074501060810003103d11039401c1c02080e50540010000c100c1518103040d030b1002803140c0240340300c0e00e50101c1c031440b421110154080510005038182015540e0b2441c8141898020305081007403c0b40c2c0e070390f071000b00b4100300184400240750380401c00415851040241440d08809061030403a40d0421601e4100c14800381d00c54050704160960707010a8040c804801e650850312a075030b062036401907030f2010004000210440c1c0c0302e04c10110004418000c0c6400c0b050707001e503000c0c1c0c503034400c0d1304580f000c0324081e202a50001402a40108603c02c82d1060701c41c100d034111208018140500b210300e0804641c0c2000d01d0003502c1e885580460045401c007004950b210440e44650210355000d03595903c104161180140c0103944192000310400081c2201c2500d180e0191040c603140c0d00c0e1820705017030821704000666003031f90304407008801032140c904108411a008683d41d600345e8040341c6569140303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 574596681 1250 574595431 574595477
    0xb120d0e09221a010b0c010524100201150308031b0a020d3c17060a05040b031009061b0c051c050c06010305010f1506021203150d030807020c01 63
    0x102003204510030005060103000040c80c80f200c04403c1c101c49540d41e56440c3c401c6603170800c1d080704089500c1d0901188202c130320110348174920348041205858042c241804c008100f80840001000d55481744c1c1c12501030004502401c0246100e40d003003c1d03c0b41400140075050065100e100104400200000060560000764010203080d95240240c4080b210b0b059018480000c20304991010003003c0d488954560060010b2a5541d0075035900d0300c0741c0c442021000040201175030740c3d5401880074482841203040c02c7d08200c0082c10054225846801c0c1c015400044610049090b50203e070749400150050720791003045248449185040d400c030700165150903444002803200c51150021048242c0c100a01400599000103001c0040e10095030b56401c01d41e02a240e140b0100c8481c9103002c0c00d500391400314054440c01d6805503401048815011540010503500141203902034544044807070101c8c0da6001e1001030b207144603a8500e07280d428201d4010780b60000c104c2c031850601141c8220b44441441d0f442c42 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 574597931 1250 574596681 574596721
    0x70f0503120d270b0f100b0d1a0306011e06050f2703160f060903031719090305210903070f060e071d0705210a0b120d0e09 54
    0x180818001409040f078190b071011103401508608a440a003c040f641c410700c9403000d20400c2180750f507403141000740520140121680072100b801000760540040d440a0810400203483d00701d85480e03240080d00d402c1003680220807500128824920782d01c51804888010324260510604103089083c540b0810700401c200080340c131001c0529000126500b000e800c1d00305001030207940040e0600800031200c02a10301503a41003404049000400c64030614001d8203d0350160f8601c517000e8400700c1c894000b2000039100c1d81d4409510100079000090390300c6254100c3d44681ca5460f950081d081000800c54403541100030085003501c04c211401c0740100c11070340c0031980410344612600f428030340788005142e0000d482a0ba0300c210040429569018129040200203900140000307545040c41100c0c144502c8030048122403441d10020300c034180c00115190004003071038011502e122410040b642c07030801480315134240e91052450950071034102461040c0d802007a44c42450b540b51421420311040540e001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 574599181 1250 574597931 574597957
    0x1140c0c070504110405090606040e1906030b0a09030e09041e02010215040809031504050a02040e0f0109110103060603152709061d19110109030b09070f050312 70
    0x4040940c61014084000034000c01401003101c05030701d450b00c880c544c0140c001c0a00a2003d08080340780b42c5001c0d400e450031500489503012888d915884180e408001d0310b83c1c00920030b61152004800900440c1c14240300c1d0f418040000b81055440c20010006c8201102c998025200032041c400032900b11042e02500d811071403004101c45943c0c0c40100d241c68050500040040c03213032818402004680b40040140360340841c115078a0882c54210491261800e41c0d00508551240301844010b050642260318005464026150201e62250a06003500c10120084540070305c1048000c845607050f114590250001d8581006410080300901241c5070050083c441d204c01c50083c080300788111ba000131861585540720910580205141c0400a40103003140030144650421180114060002d45160341d150080e003034020b45003842e219801c0704000101d800341003107640c20000c8003194041c5190f1340601000030041c155185000824250440385411083c400e4001904103c086c0c04050155180c3c240320318 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 574600431 1250 574599181 574599187
    0xb0706020a0f1b29100f06020d1d060d0f060303021c09031407210302121908070311070506011d1b13090c05030f010f0b040e0c0c19050d0201140c 64
    0xa85410000ba191a0080318130313040704200c941d03891550b040e8121900c24100201003510340e181030b0f07198004804030000040082c0440e05c20002c2812918003c600b01904a03403410010a15031310681c0c003401082a00552500020001c069041101352000800303134400750064040d201005001c842140700240083d42c0c00c590346c0d4502581400100d0052491001f510f5580803440c000c840031a03d140810342c051b01544075000c0c001d1308440100c0328815008207c00259140c0d0210030b641098015102404060f80c403160900d2015000e0700030144580681d008020f91b6140480d640090020100c0302c4041c4038030b2100340700000e0400030b544020302000802c295115200c4900130710004400b4be104141c02c50900302c04140042c0c0060066000c0c2a100716564816030f2a80442ca185000510840c0c21001d8100400c20464405e42041074201c0034a00f009c03840e101e042e060742440e0516521400509103000350841c801c0060401c8005100706e0140020311440e00860008141400c0c01001c804002d9000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 574601681 1250 574600431 574600463
    0xf0504050d0f141b0a050a0c0b030103020121060b03180f0c01080610110312010e070c080a0302070c170601061b0c272a03050402060717040b0706020a0f1b 68
    0x44100040d0101021100c090f045804c0840d610700c0300000549000c00d80c0c2202042809d2080d0449060f2601130b120780c4a2500d11804014a40a1400c841b011007a039440c004505510444000c5010710303a41a1140c006807030b0802c00320b0a05410608500b45035000300ca400711981d80181c100d40e0320a104880100f4008804001514010001000052a07000008061040000c003500e141e0503900092115450f540d1046400d0750651445800646a44000d0240d51208d6203e50000c1100520640c3c64036002540c804032402c14402003182404a600300d60018010594442841a840d03451a21141d40d844065151945146018099800e11000301d602c010313138400241d0600000e0080a8000f0041070002c205079041c81c54110b480c036040c03a644001c00e01c280354031a01403107020780d070001c0c00145854460381d13500e07080b034140c9403011381e0941d001e1000240c442c41c03100c05080d4460061001580d00c0c88200d030010100303059a0006014040300424504a1007040a51280da1550041082d404c031916 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 574602931 1250 574601681 574601707
    0x6031306090c0312210b0d150e160e0a23040302011a19050d1b0608040b0a060e06120f0717010c03020906160606090f0504050d0f14 58
    0x901a015042504064411080100c0c0001e04000c8900940c1c2e0484210b40306001100c07020612119280e1490f040c0c2480c480310b0b00280c0c41200d0b4030302c0060124500382c84035aa003900300040081c18450003951914514207500e000c1c0a02e002024030f800e040302400d07050082ca440c401201400c1d02c00101d9031101c1843c414a0b548040c01c0c00c6013412503160b0094601072800030b01070088609040c130b24a100c1c034080100c41c2031008448a04030012590303078566500f0881030001103103a800c01036580c010030844810f226000d051004021f0481503442998501e02810982066000641048000c51500748204003036002002c81d10b400c03880413504660780010251640703251011141c5000114019120006010081c10030410301001416000f8450b1620740c020550032070064a40060b00404204109500c0720080241032844601c41e03040098116100c090303a1084810345168a1090380c1e031201403000703004e01004410684020352500240d64500700b100204408501070344030b681640003191040c0503030b035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 574604181 1250 574602931 574602961
    0x3040614090d0f02031b0d06150314060108010e0c0f09070c021f1107080a020111010f0c1214150d05030c010c080403110a0201050732031b0106140603 66
    0xa0001d1401e1480880d0781404504408858003ca220344680801e4200a03d40d46e001403481d860014201c4030082c0e5130f502c550003e461100029080b40c4881040400014180d070f03440940d108812009010541c140084070742100c01103200742101c0d034000c1110344613584c0c80490810314038009562000503600c8031201a01d000c0d41800000b580090076103403201c080300010300d044400103c103540c1c183e00c0040b10001c190300e074095401407141a4001c1c0c00d25030007650149030f292114000241c00003500301304841c07043c401c0381d1080b4426000541010341e8009280c4a5008403102e006917020300e44101d0038050381c01c800c07400303400e00340600034061400b58009100013402550b8115810758002d102c0230144c104000c20001048030103c02207004200a00780c42c080010f12201500e9060715520301e4405203032a10081d87c020441140394866032441178240691080300b181e214100827030015525a024a6003c801d484d252055111050303140171020800b2040300306441c0290341040d1000c544d2a20703000740201e8a50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 574605431 1250 574604181 574604197
    0x40b03070303050a0306060903021f0c05060901060f080f0723120d030e060108060a0504060905011509050a0c05030c0d140f010306061203050a121d0a1202070803040614 74
    0x30203110400000c0c19041002000b80c00c00b20f41d4104540307030b1136007400d0700c940c0650b000194000100b90402e840c0d4081545d22541500950b040c40b80c1c0b490304a03501d031841c0c01c000700c9240e201d9075184c803c100720090303079043d50304041d0000c000500141301503042035640e40c20302d5100b64001c04926851000c22007034119910315030300078090220030700c3e100420070b0036654601081c1548002807800400344840310003c160300c1d0582d003408004e014240c0314030150401411014009a4a9940d210b034030900040c000d02c00c0103c0765900484111802d4905480c82c4206c41008100d01c0480e03090101018900d40d0002c21258000031600d00c1c0340e110040010303524000d00c008405104504100303401c1c0080941d80b68200780c100e0388101024440241c03500380c0300031b040f0700d14100100403840900c85040104c0c0a0214071700f01a07049000080c0da44884101d00303030901c114030004800e51704200300c1c0506000348001d4400c003d08850005040c401c0ca4030b0181c80e624842c5115541c1002002a070807a010010407044440032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 574606681 1250 574605431 574605433
    0x21031b04051203030118020c031e04051305090f01020307020a0b0a1506090315060315021e031e01121a18060a0b100306030b010b070c050312090a0b030f01060e040b03 73
    0x388842e000e4a9070702c0e031003800f500e0302c84903040c070900382e0a12603030080b1940c0c0e612510107903041c030024101f40c0b032001220440070303040303441d0078440854140c8565802e5041400028408903060400c4003095003484400c06900010f64010420028201c2d00041c1544a440d406000c0101c0c0781c1d1a80e070381c0d800501d01e0800d40c6003d0030000c90006005c0f607002e070031007040c4c07405010084111414501e003081192414440101900e072550341003040012164003a124900302100240c0c1005241c4a0350340050740b04071104a604820b01c20a00c001c464002009405000c043c030301c402d1120703c25200c0c10101702c00d504081c207021a0301d60014143c0352014403c44000608581241c0d21414121010310151255a041500503c92140480304c0c00f84240510012a50001411001642011030040345a80044021b41c3c080604801c00035198408100c03940c49031442c2400c20b40c40300800401c00001c500e0306c0d440b410016405100780844400a10002c6045800900b4409580750410001c00c01070310001100940c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 574607931 1250 574606681 574606699
    0xc010c0807020d12141312060b040c021f0612080a0c1a2401080403030c020312040f06150303020c0609040b030f07061808100902030102090910060221031b0405 70
    0x40225100000b02c6a8110782ca605c0b144040004150800e409040d00c0614200c1342c0b8881080841c040101c000001d500a60f400704503070b084080402c0c10340300c400f2030410041e0b001007400c001c0c09210030240082d0b0b0350728a03000d0000c58a8904c110100301400311000d8000c1000040302000b0745d0065034005000750380013151140c07500a48076007503050305044501c210140c10118071050300580c0259983c01b10041612000382e242c540d9103089004240300d504503030a6100c204085440843c01d010325070320442c418509800c01c0314a43c9000740c19103520b94294210300409600510010f9008a000d8040a80540307000e0340300c20103000060050419185040c1d010f000301d4144850b6000b001c100041651000d8455400c50444c040b091150705134241f04400040d000000320240c2c61620381c0024141d113000500140c20540301c040050410340e03090b0f0300182da8501e000000c2203030381d40501c1080141d14030f005010304c070001c201d03000510922000345140020040001d508076140464001d5401410b00a4080c0803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 574609181 1250 574607931 574607933
    0x50711150a0f061d0702240a0f060503100f09080c0a020102160501020c010324080307111c08070624050a08120415020705100f0807110c010c0807020d 66
    0x1050356060324500a00c03800c08035189840c0080c0c1c010042111040000302440d4007480094108864016200c2d43c218080e400c21802c2040b0301e05141200c540441d0303032204450030a020458100c0d035140e01c40005150814004120580c0c0120300c0c01442a101d201c081145000b038402e0b44000d190340c00c4001d01180c030104101000070000a105070072a4406c0c0c00310b0341111a018640003000e42c075441042c0c010391010618450651280d007040301c401404050a601400c00a02802030701d510f55000944c0c154008184042400002d203403c219103042a1080c81210f007201d56040000305940601610b16000020f00c04100015503003d1006545031016038981e0f03495155981e40030034200d00c10107100706201c05010a200b03501140c040100a2002c4401c0e2405142c480d02003448001c0b901c0000c2540509000040c5503140c2c0c00c46400c0440c1c50741c1e03a00000300c0030914080c01c1d800010700300108104a107405061400cc0000d07412410402c00d00300142460703810725002c8000c2c4242e5400035008150382103888 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 574610431 1250 574609181 574609213
    0xa020111030709210209130206040335040f0302100c060518010b01030e0312060d0f080307110d0c02060c12130503060612031213200f060a12050711 65
    0x40c007075840041c0c040c10311468100c056a0300c13000119001c0e602c01952800b18140c0310038212603010092016000905050782c030b480c2c5d00e43c2e5644000089203d44200703240c0c614401006c0d0740041c8610404d10701c5504241c1405660007411364503020085c014441c07002e10111241c010310a10603140d9100341d00740110300d0642ca444040030044800c100b220b40c2042c1c03c1096941c000d01854041403502002141420718081d40042650700260400783c2040e500314105022650b409005850705002c1d02d022540c0317040c0103c00070400071342c2030840cbc00c80c2e0700100024401a640714120104c0150120740d050b40300c03d404824203003071030090007140d5164440000c0c1803400b41d004001c1c1d1700072207d0850590f682961140107110400d00c05000e0000b8a400811000d800f414024940d45c3e005041440201004482a501e9042c44020100001861060000f2818152400e001507041c4e481d01541c41c0d030f0404000c0d80c03001d0b2410b5110b00002601c0c94031140050040742c0304008404030b800780d080480d64a410000f903a4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 574611681 1250 574610431 574610447
    0x80d020d1a010e090a05150909030711010306080c0909010204090e240f010b0d0902060a080a05010512070314010b0d120806010309020a15120c0f0e091b0a0201110307 73
    0x103801c0c4603403038801203402580101c100c04841c0c1c030b01400140240da200104e4400405004101404401304496828515140c041c922441120307160002c613951101070030004101d0700d03620000c0f410142401818020701c040410046403c8000b6201814152544200140640602c0d00200282c629211902110000018410300c000118408a41a40c40581d404035043c03041200e2061029003040010049407804000401d1f0340d80a20340000b4031100300e98001082544180c145000282801060040708001481003900504045940c0184072801c1c4e0800b90f101c880034840503041c18200300d880010303076100703410100000038000c0c101c20402e02513180407955612240f07070400000c0c1500c4006000c55000344140d41500b0b4006151050440c50450302002c42c03403265603440c041001c0007030307584000c5405029000082030951502c1d007050020b5070f001081c0c0003526802e039218650900501114250041e124a031203080c420716103550381841ca006a0243c040403214100303078180002000b800503441156 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 574612931 1250 574611681 574611701
    0x9050405100e1e10050d030c060605040204090605030f0a03081501020111030c0712090b07020f0f1207050f0126130b1509060607020108150a03020d0503180306040b01050d080d020d 79
    0x5814541e4071000740035058001d50380a01c61b005590030004501181c040c001e1348240910036000810b07a95125030200742641c001e03605c00c81e903403a114502408640703014040c09810f00013980040001c0242c90300c0040c40b01001400500d0040c084d045100d007079901c00c0d007102c07004000311000c1070703a00e0400b03a0750341103640c3c40070300d0a40345010030031800d0703954900c140c07120740840b0b040704255400c00080da020007480851999039035601040b404968685512564100103620700030202910405182100388030034810024110750401c0840d5078030718a248c1048070010300b60305c07003140000d419998450340003140f20b0060300c0c054a030002c1d21041041003852160380d880c140324240c900d441280c80380402c0c4000b9010340d80e002804500c0c1a00056115000f202c1c080788100307001004001840d569402241007841d80d55029a0303950070001e4003003207143d14008007414103c003e80082c00d00e480e2949403404a0001802620300c130b000200310340000c0c0201d14040d20382d801007081d070856982c1420f0582c40024549041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 574614181 1250 574612931 574612981
    0x301020301151b0506010308250c051905130c05041a0702011b2307090e01050411060301030803070305150418030905030d050d051e0f0f01050306040309050405100e 72
    0x4a20341c2c070020007040c0d580760307104d0020815642196100811a040101c02c41c1d4160381815401000e0085109074910b0382d0b014411b08070029003404140042c405185001c610b001c10340c03a00400440d20b40851015000420281c006401c04178030800b21403d10590307000004e0104882c40340b10b2003804000c000c0240354402d884502c0344400d00001601010142c0902a11410107808951240d00b11003440741002c485050a903070380c01c0e844094030812070311b808000a029a40d21002c0000300001d03201f1031044211708072600d504540c0755076103084045c840100b0300803c040d2100042401c010b0341e080f0390700302d5860080c824454040080305038820040058415000201c003084005814100407a060045410359920325280034424083e0001070480903021200441210601140000c805014140594441c415110b51f80c204002581400081038003c00d00c650804400c0c040003030780080f201401c0302c1050710041340366a42c0120320003a4500c40d6100c0b07803841c000c0c0030402030141e03d280d0902002c002820 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 574615431 1250 574614181 574614197
    0xb030c03150d0215390f030405060442030b09060f040c020328080907080304061d030d02010f0e030909010524180a0b1e1305030102030115 61
    0x80704001c0e1880c440030b800b942100802d180e440381c00c00e80703d000349000104070355210300c48075204140d00e03494003070f848aa210303e981603000b242c9400c01c18003002d5a621040001582440d013003200140c072078400c5103d40312501d83c815002200b030b001600d07000503940c804015034071308000000001d181400d21102004001a1030300402008524103a40480c0c010000900b40d00d61004a4000b0301004095140701181035201c1070108502864960b0725800b6110012800901c0700c51046070064400807010307003480e4985e00903c0040c0a20386001050380c007207031410310b01b189070400b40780103400e12069000e030fa00b034043c0030760040c829507260150060405c40d240138030200100500104450748074000c80e102d403a480104c29004200c1d900c0e00510082a0070001c0d200c1400642808070b406400ba07100d43c030800301d07101501854014070700c0c004500400a0080d6025946002005207070001e15980d10406140726450100703560203500c601303580c240003400d4090000c5503a56101c1043e42120320201c10500c000407412 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 574616681 1250 574615431 574615471
    0x609070917013606020c01020f031e060907020604031404120c0503100207050c060a031107060c021204080c04050414011113050a03030503011719080712020606010c0f020a0b030c03 79
    0x80200f90300c141101c034000300b80e0101e8641c1c500010354401820101d496400784458013035000c48400650045107549244040fa01c4481640d8105040c001d25551103a00414200300000d5000700b00280d025130f0510f0094420f15012001c15201e010700d80001c100c0100b07510f64a003c10001d805081d09a40045084807001072290500030140d00c40c01c800104140c003c1d04040f02c003400e08802070040c240d0142000716807111340100300d602907040070401351000340d1070317003001040107406100c0c1450700c1010740011481c050400e42600d6807004205a034034001c543e076000050038060045003c80e07080e0300c0700f4024404881c0c490300e0390301c881d0050001c440d40f202e09100700040703e24240711032108481d0b154450714150381c81d0800c502d541101000c4901914001d00a15041d503924900840030254450078006483e500203003494030510a0400c5081c0941d400300051011740c6e0303000031a5510203948401e4004114500c1d1021559501640d801040840404410300c11000e0690001d184185002600c080806c402 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 574617931 1250 574616681 574616741
    0x30f050c060f040509090102120c031014011d010e04050c04050901080316150f2d05040c140d060c030b011815050309210904060602070e060907091701 66
    0x140b24030500480c28100020011810300b80b298642c002160400142003010440c20300e00c20207802c95010345000340003c100000355454259160107001040d1481080c1c08100c0c001800c203203003986061401501d450086c041c04e81c03199000c40e9107404060414020b1b4204001040010b400501a03140704101d50070004c102203400000340e80c06502c0007800b08240d0100c5860303075580d0480c8a16180042038445480c0c10340000c01d4021883c1d10b9862901c40428008203000c1d05010700903003c16040e00d07600b0001030001166100070402e00f50b41c80c0030080000100394600280c00c04420110042c0f91a0421164508107034040e8811030100f442038950514040840c600250a01e13098000c00c040410b600d001840c0881c481d00140da800607007081115244c49c0c0d07141c0c003481c500554070140100d0b01d40019101e441f40c1018041c0b0401032166000030000503043c010007012540000b410240540c07840e5000404e070030302c2412420001c0c4000214160344e4907180744428060130041d00424804851107880c8001441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 574619181 1250 574617931 574617937
    0x60c0a05012c0a020d110a0909110108011e05060a271d04080a2102070f030e0d11060903011503051c0e010507031d0a090e01050903070201050a03050601090b04030f050c06 75
    0x84c1c000e101440b40701c0c0c0c65840c0491030806106141d08156584404646852588100071049015101183e204c0f5100000101109416005000340c2d0801d00624000d0048042c000780c25903104803041522200c0c1c3c050200d072a00d2100d1161a0146141102c0080760001ca4031180160b40c2001d50a51b40c1407407201e0030030b034142010781d8001e0020008100c4030741000d02c20102c0400001c2e40c140c40e10368451204082200f070783c110002c20b846200411500700100764000d0400850002c0c140c8000071400001d1f12031050002c3e840d402d4030302440c0300046624184e6030a5000300314801104424100c0c560300d904100342d03200d515445804c40d0034150319601c9c41003401510584000b0205949042c40c290710f03641e045800cac220407001c1c09906100032104807180d60720501b041000d0a5027010018409108003040c1d03081d148040c18042e41c9030010042e000160f40d200c812150290f446003808101c03a01c900e80125a0116503034081070b070818010401108004640000e503d090f8003a00440790740c85104c50030818a84 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 574620431 1250 574619181 574619183
    0x1060b070b010608070504030b07021c0e0609040b040e0102131a120c0d14011806140117091606110c0a3803101a0414060c0a05012c0a 59
    0xc000700004000351849a2001a03000c0900c1c0f410506165403a42c41d6a80c130181a031396100503030040c8428400340c3c00c005074410170703991041ca0034083c002c0d00c10000c01e850340f080d1181203006a0300d4401596027a12680c0000ca40d000d1840300856981e641d00c882e0310045042401a404102000c603040c01840409000b48c68600e000c55848418540340c01d001485c0079400a014440c605499900701001c0344190314203580201b00000d451004082d41811031000c8a0742034014480002d55000e030240c5a982c03004901c1c450682c3c1015440c960b40b01c40c403801d860040380500c2c44400174803210b408150740b60302151a54180c81c08030211240800040100b09081c3d02a014902d003071f124000c0c4100c5001d1000310300e000c1800786200c4a10319641103a51030541c59108480c5001000009101000302c0710444025a100c0c1e10035668240c02c2508000b01e850042c007880c140c1601c20000804c80c0d46a0b01c07001e0150901480e40100200202d042d07404010166031813613080f402d080d0800d80c0c0c00307842604000c45c41e40d40c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 574621681 1250 574620431 574620443
    0x90d0c150206012c04020d0203160f09060b090918061003020111030a08060913020d0c030b0c03070c02101b03080f220b130b01080703060c0e0310050402030c190801060b07 75
    0x1e28100f00e180d104c03044c801401642c1c0102e514034800050384040c0150348007026039002005100c0d0030074001c0c25402400b82d12503029140381c00740c100030031203611080da0b5111800710344140203a02e40ca00789002c0d07040050f019040c9409082e05029917903000f40c1200003240d01c02c0e00d07124036059441314055182c2c056501d802000c181108005081444c00d808803907400340801c500717642c845100342c020407141441d40004485550780070700c05009201d50316140603404020048180c2ca14900514000d000d240303002c00090240951681441c14103000d000803090b51170a4100c2424a4920b038140284035482c1583c945103441c00413001b250b0540181a116113101b48000c0c41c0200224142d6544906840020111007089241460f01c0c4005281092034500034521007000745111804c1d42060700889288145078810300640030400d42e110346010483c4000c513405120b000840303580707031300229040520030803403607601c1456145520803c81c802c601c001d09840a00d0000c01096440c3e41d00328289200e00c0340c0140c89 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 574622931 1250 574621681 574621739
    0x2070b180405180a0f1109091c0c08030a0b0f060c07030323040e07030c02060f0103030f03060b220f030209060910081009061b14090d0c15020601 64
    0x340c1080c0d008250410703100500950080348118919040011032402180e0b008244140c0b001842108010002140012a07240c041418600c3c003069a0380300015005210180d0300c041712054a001b222141e20650304620701c5541ea00d00380307a04400600340034501031b10541581c01c0c00c07559401c041042d2240748401c10001c00350f55066031416606002600ea04c240d52803000e600042d4110303c5c0401074001003a8001c00c0e00c100b800c21503030180507039102101d4141158030403406c010520924615150440f170f09810010008113140b24200d000d00003a410041001c400000e1880c0541030072000c100c1040e80c02160141d107141c9035034074023072440c042e8400a5801107241021501c5841c220b01c14507000b000380b0000c2c0c00c031a50364808280c10080010710542000740e0369000c003401d022003406144075200003121600c104c004504000391906100380803e4505e001c000c5040c4180c1d8407402d00307103260203801c10743d4401e400c0d560303800701010091404401d20060050000000d032a064200e01400c59030500d07942011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 574624181 1250 574622931 574622977
    0x809071406160c0e0c0f0301090e03070c0b040f140d0201211509060b120c090f1306060f110a120917100b1002030301030b0606040302060d050702070b 66
    0x1030020110258268014401c00256115241c0001001c410034410030341c2d1501c1a01c0c0c8020081141e5000f07082108041e030070000701e04005004021a410340c2c804a0000400345c007800640c501d036010360b682c000d0004691960114402c41c0c8040070b042244c10711030481c0e40441d2600d19900204c0c600c8910183c000395400021801503024400c409840303020441403001a0440c101c28800b9a00303152814510160016000d10484015014050141400c4050140b9110b2058240700d401302c00100f8074102044045180649641c0d49640216030080c000c0190944020044e1190f0040400f4865070010070100c0300000e1846002c1c0c5d4800d203000c205d94000d403e0010940c0c80d04408043c06040010421000200100d2110990ba00103031400c0d02d00b00003000201c00a0403031108a840d000e42843c07284411401410700c1c0d030340c00030440b419694801840c025688400010818500403030300025440a400b041124042d4500c0d40500c1c4078802a6084509140e98cc28400d043c1c6c3c81280e8100c8000d51901d9902c0c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 574625431 1250 574624181 574624199
    0x171b0d050406090b0a020a35010f0305012003060d061104033c0f0c0b0d0b0a08071809150c020a05010513030503041209180b03010b0604120b04140a06050103050d080907 74
    0x81700e074003624408c2e80f6000b0740c8032010540c5001d8000c0f15903016001003d10070710000344a031114151006121425081c0030103c41802400010959446910410780000c1000400d400c902114080200d5560710b8680380c0c680f07458506a815201a81d15000c0484081100e501c100c40d130940007440300c140180c4c094281c0f507000110141400954206101c00d400280c6600c0100c000d20300400445030001e07010140404001c0708504aa006a40359840b441d42400311000000708010605000368002444402616090104200c0c000114095600c0d0003121480785401180600e1201c1c40b41c402002580d513003d20405d0f0b00c454089019001581c2840003500150b94080345420400c4c030b034100042002e50382d40c4004821100c0700303184201c0740d49a070002c502904003405144104181120311a090a0901c106400c9140401c40090001c803010740c045014402c0c942e00c0e00a00700705034400c0d01c900003201e080400c003404003848100c8003842000910f0824134071400110340203541b100c005e4080ba034a01080384c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 574626681 1250 574625431 574625477
    0x20a0e030706090e04262a03090d051006030c05120609060411010e0d080a0908070302100f0c06230106030e0606101110051006171b0d050406090b0a020a 67
    0x48424100c60301981b401d00351244005903031800c0d8012000e54403010191484805001c00c441c200c03000b070345010f801c05800303170200a440f290942034503959403a003003d040ca10f1601c01c480a14121040c5440c0020050210500e01d1400307a0b04240e0f051982c8660442440b03a82e4903007100c0c138825903000b0710003150002e0028403000040c00d0307051600401640d21480011418616458201c800c10800034841d4411900301329884d0090040360068131545203180c021882030002d51100a0402900941030401e541c02501152400f64104034108080c0c1020010200c00301030f03a601100c81e4061072000014824400e00039940781c03042d020f02070946600d40310107200880a409102c8020b210f182c4101081020080000708242030180e01c0c04103607401d02c540c914074070707441e2900b01c1c408101091200684404200d4010f541090842414a83c0090512540108c0c0e0044600c8034035a80c0c2098184403d02400360800c0b84d01c240640040c000d5900d80fa0fa019089106503c00b041c04580100d500d440480070314521 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 574627931 1250 574626681 574626683
    0x40305030307051c0513050606030a020d1713030303020c10111914071b14030706050a02010906020c06090d09050a0e060d0c030b160306030c15020a05070603020a0e030706090e04 78
    0x4600004c140d61159070702950b104944668001514503850000d0290410003290018410381c0a01010710040c0c001c0b60103016550b0b0080d2155605a0200d0318010b043c8045890174202c1841c92441c0c07a0b1213190080103540040b8044405108465220308410f44a10590040c60f158030031984c64140340320840640d421501900e03800380200d0407038102040004034020440380303201c2c510084054541107541c99400c107054200b0b1142038540240960b2585001803001c041e138035113051140d1a121006412805051001d07002402240040751540081d0800120140110703070100c00e03150384a0b442a030403110603149204055114644c40e8080041c2c5030040e2240d50840c80250400c3c120818130784854888c21031070703402200c8540d03c1c1010403003a0b010780803410340c50301400d2406000507480c41e00e40c945021024010f000032100000d42c0141514004c001d4440c8030390384001560724203039036070401130001e4101032228000b03d40040c8000c24103141c0459180140c8a15440301680c0da800c05210000503540200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 574629181 1250 574627931 574627957
    0x3032004170f010507090e1008060c130b0d0905010b0910140118141c050a020f01050d0e010c03060503070f0e1e010305060a0b060702010905220212070e030304030503030705 76
    0x4103540c40354800e0040314821755040d29880d1040380b42440315100824010106000f50401802c1070011000110300140c2050010204544403552100300c54210300d540d500140d100301000a074221448000d42010802030300501c000c00030301e19003506001041c0402c50300c44240c400300303101c24881c4289030805003040c1d403810b1400e190071407030b08181d60382a40300f107410440416001541280e0585070406040000c01d45501c03440f6400b110303d540e10341d601c0c0b51103940284507113107400c01d58a1907407059007900c030307181c1c0f48503418070880c002e4440d654001c101c89400500041d05007100803c0e40d040c005000707011189807004001d4100e02d00701004644440280c64047c551040185904540c240034051602035405000600001c0c24421113600031501c854460601605d820f00468000d80e0708600074004890b410ba4a00790151080300c0048641e00030340702d2001003544007089031321904600250185c460000c0d0786404018401030002c05a07280a640f01c0100141e00030400907020361301c24030103007800134003402d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 574630431 1250 574629181 574629193
    0xf09070302240c0f060702030a0c0f02010c05060a050a11040303091721030601260f0603100603060b0f09012102010207090c0206040309090209030c01030b130903020304030303200417 80
    0x1100d010502ea1210f030711040d4581c0080340e4100d548200f0b015880e00044103000440c80c0a50860001e000351000d0840649a241034141840c25640240e0140d0b041641c80b40075554285041e040c00801440d090704c19611603071500310390950340c22054013290305807509a02e03100d101e94036040d141c01401c21058201805401070b100e564240d6250003c4000316403403403c40c2c0c10340300e10780705000410082d030000c80201e600790149103012801070041e00d8180c101d00c1580d180364195683c000406e141a82010700c0618a41c0340c000004184030701d5038011410018101c50076462050300804000c040a02030080340280020701d40041c1c1c415186a04403194a841801511010360ba40e2911104485403a115200560400b03000c1004150344030340d64030042c10b401e080850624400307201083e030f00c10a00120781d05069071a030100005981d40c0c0346490071416110401c0c00303108128640251290490310080307010900780704580d41c984150045015401d000898942d080502e020030310004801041090680e42c05a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 574631681 1250 574630431 574630489
    0x130b0307030c060e0604153c020c06030c1213060203010311030f0109080306040b1306170d0e09070509040e010c03060f0b07020306010e220b0601080f09070302 70
    0x344511001140600c4050b12150b290007800b401c1480080019489244100800d1040d41c44054030052800480d180c181001520110f2070548201c411841c0c12046424113181038034541d1070002018403071400da00740c1c4c0058240005128542c0420b85181f11603020502484020140392100c40d41d0029104011008100054446c101260306c04c0e0403d132034641c02000840050f040400c40e40300d440700000000c1000030307115140c030101c90001134002c0d4411620703505242c80c0ca6403121800100c01d52050401c0100941d43c0c911803500b038484c0a0400740f940100714150034228003985040328148005802224550f403887d034121055813160494580c8603554000c062240e80c1d003449040d000301529103000411a040c506d01c0603060359603500c0346ca04068204104001601d010509074112900707400960200d03110100d049648010380b0b40020040c008180d502000d001e0704c2c0c50344338001d58003070b00c030640c1d02d4660740c0603050b004100300d494442c95803120304100018204400203000112003044c0c0000d1500c60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 574632931 1250 574631681 574631683
    0x40611011107170412050a0c080313060302160212010e070f3b1303090801020a14071410050604060f06020a02362e03060b040b09043c02130b03 63
    0x8010302a1b6441d0b10000b24141003040c405a02ca020342400d031700031410201c9a032000511040140610070400d81c001c03a80c251181c58200d140c4100c5035008003003e12041030111070900801d600000d81c1c50511a104001914045080000e425201b01000b8081103401500b0003030f15420704c03000415210740210048031103250030352030341a0041d0b0b040d50984541104500340101244004c6e0000c0750241d10420220030081e40040d540c05985211510468a0b110b89041086004d002aa90b00b161401800c0a6150010181d400360340309000440d403c0086070b44500038000705035281c1c0200409a40001d13025000b5240125015810b20812106500b05c1c080072000a5400c0311102086040c0502d40018040803018542000c0040229030302081e0749945821011100b40351148009041c3e1590b42c081c503400c03921181c100360b106034400360440d484d07400e083c90f000300030303045a08030001425001015030f009040220804000e6402d03190000c0e4200009408010071641c141c0b0503807118a9130782c207104c206518 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 574634181 1250 574632931 574632959
    0x2070306020922021207020c030c010e0f0301140703050115080a150503010606051c05040c0e040f17090f0a06051e070c090c1209020109150201200406110111071704 72
    0x1a02d0f101c056140c1d15800d042560000005e404c605c259009200401015100001c141c0402c00b02443d02d9841210b8a00c081080030b04401c8000d030700f55013802d40049000076428074803400350041d55420401e680e41c600306001d9510480409000185c200408580b02c1e18850b0401c004058803000100c22455940700041c4c05c40f0540d40c040e4001c90ba002c00c0c00ca40017801c1d66014100c251a00e98140440d16196441205001083c000d140c012651800810240039800e4240703040590700c0040d05901c107030400d030700712500d41142ca904c52044c0100d01d020901410304160720070844200742c0b145400c002032060038103640d021400241c0c07054441441844003040b111030700d440041c010707030100080d2003c40c040001c0090307010301d210800ca1804c0200c03010060b41c0c018100001c03948502da208800001d00042240549012a041100403064000039504541c0c0a0004c0c0101d420a4a90450301c004c0c9103200b500780c41e9040d46404004100f40802c80129100640c8001002c2c11850b09134501074484904001c260 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 574635431 1250 574634181 574634239
    0x30711010f050a0609180314070507030302060115170f091908030a0b0307081005151908010507090602030f091f050c1501080604120e060f030405010605060901020703060209 76
    0xd5114014071410f42d03501e01c5800c02405100c8024410404000c51101ca4061500001400c00030506002040c0d006a2403d84040c15840380c00c1d5a089079407420000c1d62210203010304071380030f4048444150014014441c0290b8030b10741c40315807001d030740c3c900859503881c017001088400316010b4240340d06804d2018001c0300c58030303e105855007512800c3c176168420444011305201b0313000342d000f042d00703100341c80c40004d00c0048a000c440b40410035507566100b8149141d040c0c08440d8220529108882c981e20b45000207a050751000d0700200460b030781b48071049503680384510401000da001040f2260088103541d005008030000030700a18075145d06010662010081c084000000031030105401130141c0091101306925050000801020750401e0900e0362106800b0f40010702c4003500110446010b4054001211600e20082c5681e07140d841069281425500c112000c54065190420104952600310103030381c0c403803406070300900c01e007800d550301d4000940c8401c254980c480d500700c1c031184401920403003440c004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 574636681 1250 574635431 574635461
    0x9030102040e1603111c1103040b07020f03130308070c15021f1104090b0a0513140f07020c150f0d0204061b020f1509030109030e03120306030d0503071101 68
    0x285404450b2140141900460f1410103003403041e500d4820000109450040344440f01c1d02014045103103a4500800c2804604500342c60084100010302a00001d118414440754094031400001c10200d03603200e01c218903545032030410450b0240003242c2090041c0c1401485a841500f9168442144d02c1c500d01c0050164001039102100071940c9180c0850007100140783c411301440441106948030100707004900420049594070310740050749076240880e8800400018008109110700e03950190090000c25110340142070125002c240704040f0b008610b03100384400c3e0301628145403040c04101c41031811110300c01e074842c0c05000500419400034028111100084001070f0786500d490005072007840c1003501c4100300d80000341d40102688544042d0308451500301d880300110829240c4208241c0100c0325081c0e099882c0c042800704164104591144803203040341100c00350600305e00102100d22045070b400780c140d08401115001c080c02000a1501304650341090292190040030b850b007102c500c0d000c04104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 574637931 1250 574636681 574636709
    0xb1b01050f16050406090b0307020c0a0b0d1413110d1707120503073203011e1203050a030515030a1a090a020d02100e0904060b0915100309080903010204 67
    0x400000c2c4864142102c0d09810800d003428078000c00035007200384038842c2c075081120000009a04610070301c03074a0071030385000b003149807000e450700d0000450b50071004858a0462510b03102c0084100c0d050105407040c1180d50124045400564401d00203c00012003550080e4290994200144808401940d94500340440303580303814260800341d0f00882000e900e002401003c00c02d0000c40381c1e00076070b2240b0825500d00035a03941c071081d840308040c2a1100903441c000c2000480040b82007540315002601410456915002003030300c4000d410301e405c000d400e0003008143d0800081c28264001d8001981c00050800100f144401c0c507000320307040c801d22610031500031000d0340380c5012031001280002c1d0054084002041061025400f00d625001d0721131000e40f142c640c1401d0010711500c01e00740f07155400303009031242c5003509091409401030140e50081da032182804100060030700c0d00060845155820080044c01141d40024080d002060701d04e006031000c200030804502641c800b40010001440c030407240d004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 574639181 1250 574637931 574637941
    0xf041d030c06070201271115040906050f031507030504020301180b09010c080705041a0d0c1d030c06040b0c0715020f0c06071a13120e18010f0b1b01050f 67
    0x800c43d810751001d02c000703540f0050510615a0650b06201c081076200c031074a144401f480000070b003c06010442c649500000203008100c1ca40301c2e81007002110020b45001ca90310300c40130105526440b4521081020f9841d10000404691082d08801c0e082800540001100003012645d100340402c00340090729103503080414812043c0b000d00c030703c5d54030307c0e07951030704903498181040002c2091013503109001c07a000107036000c1c0f1098420325003242c04410700460100440c481c109405405030b040f0b101e5a240416200740d250045040100e00340c40e0382c80740103103c0c42c40d040c201202c050f5550072030b194248040c49055070114540c604c401038040140c5d46038000b0002c0340340c5051010f1030100000c040c1401044188a060000781d07030f5071180c0c1098407c40354144829517521400501b071501c080805822604004001c60300360350085080014810261103d11004260250319074602b2800c0c0b0610007802d022003001c02446e1032080c0506103803c1000c40112056001344051400c1d141d040e030380e07120484a5401402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 574640287 1106 574639181 574639183
    0xc100306080706020a0c0b0a0f1101020705060411030d0207030b04080702030f06040318053003070f110307211b0e070f02060705090f041d030c060702 66
    0x5030060780c1e614030095079281031040035103002e2584c06d00030a640c0369030400c8428030011520340a006000700d0300125441091000b84440c195402c0c0304075800642c0500146001d2401805800c490542d070000700350621295107040019540702d0102000014107130701b1916405900070149680b540c1c0c0c50300100e820321310320b0010309456000e141b04200c101500621038800c9820041880e6101e20746510520101030600c0024540f50003401d49407141c07418204807851030f0440160b007681e05045a039650808002d020003000c8803003688a41d00310519080030080140100402901c1e021800550550700d954040d400d070000d411401c140c0c0e03640582e004d03500110001444030590012030f5103403242c001003620040e80078003801400342c140801e10303143c803480039101e000300c00901c0c80b070040220720100002420420038146e07000305513512201e00c03480c0920243c10060b1001020342824645a0002 = true := by decide +kernel

theorem cover : BRFrame.Cov 574460431 574640287 := by
  have h0 := BRFrame.cov_init 574460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 574460431 ≤ n) (h2 : n < 574640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
