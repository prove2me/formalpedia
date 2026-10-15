-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4770
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:40:34.809323+00:00
-- url     : https://prove2.me/submissions/3a1d3209-3d5c-41ba-be26-0bd4229445e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 857733812 ≤ n < 857913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 857735062 1250 857733812 857733883
    0x190b03060708100905040302010c0e010201020c07051c0b0a20130506030a0f0e0d11030c0c0f1c0f0308070c020306040213020d15080c040203060603010905070903020d0501050702 78
    0x1640d03040001c4a03440b80c0074148029012a48103130003150a1004101c100f40d810340041c000452240c036800ea0801d140c0005900341c0c01601840c18980d44159020000b524102d04910f800580a40142c29004116111043e81040c211a194843d5843c0e9503080d08020400c214041d9254040001c50b0500e90842c5644003c29510300c600c500c0f0b86000f001040e5807101c1507100040300c0d0015101049036010318030440c0c1d140c0d48590101c0000ca00c0ca0b001d40b0f8031054001c0200d030292000e540c0640000c441d5841005040c4030760302c0c0082e0300107031060341c0d05919082c0d05a500507110300071b60500e40c90040c58580100080f400511090400040c40048801030300d002a04503001681120510341c01c0f0f00d05a1403400034007a454a807000181094842e000802c000e407021001d035820b0b0b9060f102d41000380b000303000170f03813100782c90194000a003000100a141810f03072045800526625059004584da900000d1108004840507269650358400b03004c00e8a0b010031003842079241440703411a100150008044004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 857736312 1250 857735062 857735071
    0x60105150f0703030f0603061b14040b03090f0a0309171c03090f0c17060c0c0304210b0103082203020f130603020a0611070b0702060f0901030212010905190b0306 71
    0x2250102d9548101030081d0042c80070b4002c924001c001c025501d040000123006001c808141114a8040510517079101d1010b0709103104000f050946040d00d062010308156000411034006400340001c01c020002040c0500c0a11500030f1f034030318100d1418100c0300c00024140092003c000d510010350301d00490700030031101201e802c050a0002d240042c17414a4034401c00c036110000c06805401c076000c10148200300410600c0d00d094022a180341d5909001d6590034800c02800e94211303807080c801080400e41031121280482400309243d503100c0010742e079012070f003071086e0400c8a41c41e90204090700f0070b5105009498170075100342404000c01f031850b0040713181c104134220880e0182120000ea1554589180c00000055901528044046170b881500401a4800740792000c0030b8000c1e00c20000e0802c0c040300684007210b80080c81c951900c00480324002d4198410382d42c05060603024042c080211454403680b50003041d10900c04141c500e00201d1500b0300030251062806401e00e0f00000e1000c41c3c03800208242e20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 857737562 1250 857736312 857736337
    0x90e0a0207050c041d0f06150f030604120203130902090117071d03030c0a1a01080607090506250c091808090405040c05030604030207030303140112110f030304090e06010515 76
    0x5041488600008542c0b60030881c0080c4a8660304101c0b440c0e0018055100c2e0041c8c0c8801100802c1c41d01c1048844641840070580c0343d03214102082c040ba0600607030002940850040320b1a00b00c9280b40720140e9003441d800b01002c9a030201c4c640d0b001e540c0010440180341120085081145084640030b003401d21050790180840c0107210800649403010400c8070700c43e8490380c04a0701c0107031240c9031105800017080b21900c500540d031000014030307000000707890340212030a446036408141800c0c1442015004005a00070a03082d01c24802010008903a8000311346016440c442001e504110b80e842c15113141403002c3c00d072144990741c0d100101c0c0380d450581e001c83c41c04a0340800c1984403810180f1122030183c0103140d041c0104020b1108241d0000341c8070086034407940b400d11130703548501180c54806a09110b032041902c028a9540002440740c440c52030040401086506141103510209185030000d420060b40d081d0340b1505103807180c604115003401090200c40c3c1164080406d92241c07024082d1131b030034110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 857738812 1250 857737562 857737571
    0x6130201030216110411070503070b092a1807022104030c2301210c02010e030310030c0801050601140c0c041a10080f13021807090e0a0207050c04 64
    0x4580c40303a0110b84082c44020300020600341c407400d213845905100c202c2144614a4510f030040391101c0c0c03034203495103075030000051800c0000076280c085c42d03450b0060000c0c03083d01a0015908182006907110212501a5403801105a41a0060002c50f0740c44001d00c00c5c9040f0042c08001030198006507041c0005a07146940c4800403c0c812502c0345801a900000c00e8403c0415000c80c0303c035100c2d081d000311081c607001040350b10f40c1c1036401980c480001480c14100c54000321814280d40e000b640064980c04064400002c5c40340980f22221705641003034503940c8a55100328000c00510048480d4540a840050000c101324245000068092241552048031140000c128003451410901001c0802400a0810312004600c0105c021450a890440c00e00c0351f40401d100708140d070b101c0d048140c8140c1194030510b0042d00d6841e404028442020740c1283d1000410a00402d02228040954041d54180c1c540681715410300c0100610008020801180140b041c0004800301ea00010701c19082e09090b180001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 857740062 1250 857738812 857738851
    0x30b0612011407020102030601021204050603150d060c020c03010b01090b040621060311120a0308010306051314010b0a06020f0307063305030d0c08180d0b180d080906 73
    0x601400b0b90103554241c003803000c0c041200f190780640080d40328070700907801d441c1c50010400070362407a4010b40c01019008081400001c10001d260500380095030401000c0181d448450760303c510a481e28404484c006804c02c816100c00c0341130901480040090900308044140e003809640c0046014501c2180c0401c039042d40d070307200101c2d0300b107440c40d4291200040600040e40c482c1000c04007201080800e60084103000c40c541a01c80d4042544000d03140c0c1582d0f1000c00c1e03407840e03c8050103000c01910152840c0c1c000040b200001785070031803098565000c9000802c804c40301400308010b1108035440f81040d0b4002c0e00540d4800c0001100b00e03030701d096029200281d05092101010300081c0e0390102502400c0380c003e005280b00b9180110482111001c0f01222261000c0c01c00c1103170b124a8100e0000c0c044bd005110850703010f00064500c08081c4400703014800c0100c01c0751560000c600d420384603d03003000078070007900c01103007018000c0c041118000e041c030079002e00b0904c0d402d5640b0f030002072031314181d0b08411aa41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 857741312 1250 857740062 857740099
    0x12090b071e060221041b06081305030910091d09030a11070b0318120c0d14071a010e070f0507030e010c061518060f0b0f0d1a0316030b06 60
    0x140c000c82e5042040440e0191461002c0072039803825103083c3c0b910002c01e0400c4075018141c1c100c0c6826113019541f031044a403590fa80d602c52700e460000c0200e4040c003050006031043e4803002d000c107040603a180ea03683d011624041000c0c0088900401d500300b4012460100580000700100300c6030350404614100c84820b454070f0855040c0800da4004d82043c020000900c40c0640902c040e0b03030405035404045d10807080d07542c0315684843c480d40102c039913190400384e00d41905500403501806034040400400e490321861307917a4a2110400d00e50482c280c140528010b0040003c480d240707a034410103504200e81208260b0030054128018010000c0c20010b0603000c0a1059100e1040e800c0071070760012040c000c000c0b141c506c00b40c5403080e41c096840a103900c0340a0b1020100c2c68000c0900711240d020361118180c0c242021000396500c01c0c100074041c1d0500f00488180c0b2080352040d89a40e0791500f0b021200c8241402c00c050810692030500510300101190600208078080c40c025000007046131400034100030742c6042e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 857742562 1250 857741312 857741317
    0xc0109210c0312060305070905150a0303120222090204060206010f050a03080c011e0203090d170103082b020a2c01050a17040f0506090f0606040c0e030a12090b071e0602 74
    0x2425070247c144d0002e12902c5a0304581d0080001c803514000078008601807010786209840081c0010b6001c0740c1c0c40110006503401003441d6140b8045134103924000a00782c4514041650000c85503650001d01006a03550611100c0d005d8501e0301204035902d0311b804002041c08146001c007800f07480c0002584042c01d5403d5202d40f0340c0b40700c030a080c0900c41c06800301400003504111110030f2640500407000e9401441410544400e14542042460903400c1d070302c1e501410f41010a005024541080b442030244291100b0343c41c041013107440159581100030001809114a14181030900f5001903800c9281f40000c00e0b5030300b54070001c1c85e2654607450349910854840e07800a11104801414030f0610040c0403000c8d205c0712140d405501141d188e41c545d5040c0c03590b07514184003160000d42090000c0f0741a4a400e4011a28030700c2c3c503280c409240501080001e0400d881e41100319a01c517400d00700152030302d401c940414000c0402c42100d908029154483c000742c4519014400e6512203a405100200940d0794103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 857743812 1250 857742562 857742569
    0x512031003032d090306050c04060c0b0601020a021c06060b0414040c030b0a080c0909030f25120203180a050f04021303060e061807031a06010201060b0c0109210c031206 74
    0xa8040403c4240f07000644081c2541c042030381d900e410b1000188000d02a0401c8138101c03000c0e0365444501d040f0340c1d01c85941d1184003801140c114000c2e4508131016035641d494442001c41e00703000c9074202034800c1c40c11101b11191588258642c1c10148403c0181900303001848016460903100841c4c4141c88140840061000340e030401d901513124035006c0b409060016610b40600c0060351003500380d4652442c0b0075641d0042e245032002c4403070100481d010392200d49000500301d02d54030314590000110340d03a6248900c140417500900607803020903031010982800182e500c1c039060507602c5800f40382c1083c0c0498000d20724141a0b03805150001341051240c0c200e840d45400940d0080300030480c002520164646460054502d4400b45420342e0310320700b580d80041103800450350722010010039815080800542c02c18010810341c1555a40d0130001121041d04004009240c40040001021802403034a407540950f007050840d0312a42c00c03242031041c41c1d0421408004a078060821010640c58090404050702c00c0b43c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 857745062 1250 857743812 857743877
    0x1020408010b0a1e050d0302070b16120806030d1b1704050109061d0d050a0605100f0b13060332061201090f060f020702030105010b07051203100303 65
    0x200014060350640c02960340070310456408003c150746114510003902c0c0700c800c200071241c15603002c2000e850407041701d07403042e44031f401510180da41c0c45041030840d4101c2c14610072160055582d100421260301c1302645c42000e58146418a400d100300420b80e40d594a0301d110060240d8005a41400c00c03201c02c010900d9035014251030701c1202600141c0450703401611445001c05e80718180401c44071b0007440c114011741d090754802c42106282d2004c00c401c040d1b101c80300343d03024010f0201d90004200c11b4002d9074454084a444c00d1071a0303180c820040307035020392540b19009070502400384031040070b44480172a00725021450049018903c0200700c0700894840756008401501b0040fa45650401c001101403140c42c0c1110000d004075040c021041c00e940011700010000040812690009070040d8001e09200c0205400141000703540d0780407900310341007a0020030f019070020601a04000e01000518805156420b88904500340303020043c079601103a0000a042c0121508066000e0349000040e403500000e48 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 857746312 1250 857745062 857745067
    0x20a0912060e070f0b1206010e040e0105090c040c05032a0c071e141009150e03010b0301090c1505210709051210020c10090b090d0306060c0b15030102 66
    0x40c54003030000c002c90026050b95006540002031083c0040000c0030454841e120f0492511b019089080482c0c0402450340341400f400c1c40d5000601e0301c8620500501c1c541400001881c1d0500300c0e0b5451a005500c0440d5100364213006420f0200f60348030302601d4022040100c040141101a5000e8031941000d10303a82c0c21821020842003803640b0006180c1c0c3c11185c00701a00304112009405148020045001c0e421001d0440340310b42d4030360f0a01040303070910034600d8a8118200703a11504442e00502c0c24000000000e0320201c1918203034502846811004c0804800800900c001662808036451841c814200d41e50100041ea4a00c5070003031080720281c1019640c103d00301d880a54010417088003d4507568001078442c00c010803541004a400c00e0708404440c01010001c61170a01c42020307502c180e9050303280b40540c2c8001c4c11321074014011054624800c024203080752804100f0a4541003450b0201c900701420082d040020039000707012004e07050f420001000c1030365200f001c1e04041c50b5441c005a50550b100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 857747562 1250 857746312 857746349
    0x9050d062a09080a02152a010b210a0f0311011407121e020d060515030624040302060c0312010f230303250f03120c02150a020a09 57
    0x40c41c0c410444207180e19200001900c51031402d0b80c490300401c00941115000b030001001e004260054040410f0b0140d1000c8a08007a201c0302c05100c40051101c4096915004084103a2031302c03c04042c905001c140c40c83e0101c50794030f94900e64135501200d0240c51810065521428544a01c20180201d48114000d11041c0e18007044030131101c00c101c0307030140011100740300b0311088421801a140060031072200306425091941e501402580901c440b5400345036a4400003c0680710ac94aa80c1c000003608000341d01c2c0d1030640d060064916840e10b018a00c40540d03482c1100440d54101640e0549805503021a200d130183c030f40582c03a5124440282c4610744e00743c0300005245075105221003e5400d501c2c0d601001e49903440d100d940c480c17001c41102c6e03415001400610980c000100c0c1c48104842003070000855081c80352a89404a43d043c070040e400038004401c1c840c500c009034068003081c2401c40c4000d11180c05a419207000d008005800c2c015841d4000925581c22482100d00034068548a0903030b1150119 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 857748812 1250 857747562 857747621
    0x415181503060b0304030c1218090203010501030507050703090315270303241703120a0510050d15050603010b060a0302070b06090603063709020117060109050d06 71
    0x10003120200000e060400105040ca000381c1602c0c042c5515482e075201c00c08030b0b55a00c8410704140100b220030410408140000c80b1041c80c00d603801031030120b0300142e4a504040005041d20001400f12051100803c85100005e50160b030701001c61f600040d07440a601c0c10b2000d50805410441d1480d12114011b80c8a43c1185c40c0742e120310390805100b52410090211900159650010114031040c003d4a00e80385c204980c60a251007074071120b5400c010b4a242092903c0c12140d10b40003500d2a181d000c0d526000c028003410703203680f00c0000d4141160503100c1880ca568a03000340e0440c103005c113103040e52128007003480c0b61025040308810744401001d458590500d614010f00035000b040b4203864941820000ca441400c10801c0e11740206d0018010344101d5a896071011003e1100c401c249440320310f0148410025950800c101c01d40c4c800b503440204e04807040780001480d50700c40c014551098480b9405010302c0da0b030426104000c40b007040d00e400080445034285940104201c1d2504800d1050383d0104012801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 857750062 1250 857748812 857748839
    0x3120a081501090807090f0f0c1107060819020c0703350c0a080703121407080a060e22050a210306030812060d0c0f1a030903041518 58
    0x503481003107819841c1850004540b15041c07842031056a802501081c4500089500f00050805c404400414403d02c10840c032822140c07510052000170b40f1001d54481d14403c02e000b440020200e1f494100c1507401c040d401050695500141d0402499001860030320701d40c01030009a00440d044540004619049a610200c864401c598a0000c0380c000b003840801400f40340070303640500414401000340100580d5000000c4d17011030b505500f444025a504a03840720300340164205504000e818500314241404050100b0074007900740001a81001c17000c0c040c2d801c4035100140d0208018402c8040c030181d4101c0b09180b0054040090070384d00400e909242072000440c0d00182d44031418481551a1451400450854006002c0201066020440d8440c0d81c10458034403130300300c0002007101c04c2010349580c80384d0540c1c00580c450100e03180c0c200420451a03080c481000100754403803416070702c0c600d015814941c0360b10071402440e955184603080301130070038481d12512410964210080924135255890300500c030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 857751312 1250 857750062 857750071
    0xc0901080c130e0a060908040b0a121b0c0201080a1d0a030f0206040b04020d02060c030703030b0a0801060b040902030c1312050606100507023a050c120a030e03120a08 73
    0x340d026a4800303102c004140300b0072000d0025100a4020300c1030036a42c01c00617000000055030145010f11000c0b5021008000509500e00c258a0785241c910b003107586442601c4440319030300020168156040c840381d4001d043e09800550920300b0007070f40d6443e00805030083c0441076191590307440d0081001c1d205440001c160921900a449400485c012403901300d07a44c04c0119001041c1c0d08148003c02d005081030514203034090b10090825041030941c0c515285980c001c45070580c0081d0b11107951401034140702640c800503140c040c0080c81018103144003102c040c8500d10844811940c000300280d8643e8500d0107075810160644010385d8100d50700e286440321a0350b2082c082d5200d00850300802d00606d004000100c3c541280d444460420145400f00500015086a44d4901620340a41841c40110080071b42d10710303880c03880e030620310140c071800c04903d00810006168056500703414546406000000c011110550610b01048070f02c604801103402c203646003407000f0b401d2402103101d0200c0d50300b0a130f046128 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 857752562 1250 857751312 857751319
    0x905180103080a140405120a0b09010b1c0212070b070b01091407050a0e090711070b04062705060f04060206070306211703010b040e0f091504050c0901080c 68
    0xa01050098154440a100080c003554003000703221040c034060904001d641c02a40c10a0341031030f680d000415502c0b1075045590009030852030b89082000b008000b83e680104004008100201040020980400c07403281007071a0418524401401c40d65502414403425003c0d40c16242c8140d503c90f50102c0035048061b044071a106148008a0014128801c51056180c0751640c015507450384c1d10150b405038005500c03001044800156091262546030300280118000d40d594142411503060303940c1440450307003083d40d050f02c04100420038194080c4d2130180d56804481e0146580e82c03495403101c1000ca807030380b18580104001c40c600486c0e070310444c050320464843c0d0b000c0c1e030351a035202001103088549502903041c8214007120f110180c0c201d000306000d03503244038418042800c0011044021260426400701281c41c10004041c803030318000d013602c603411002c42c0307a0000d0f441c10080310050700d5200009555001c040003000003018070104010244030b5131000b40c0141c4807561100d500c25100c0d003221004a00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 857753812 1250 857752562 857752579
    0x10c0203071e0b070e0d0b01080c0f01231312060c080901140c03100b0d023a0506060d152102061801020708030a210203060609090a02190905 62
    0x703521044600d02c46000e500c030801071081c0d55001c401340c030208508041c09820130413180088000aa81c590414060001ca070014110301c0b22010801c03880e28001d40102d4104003c1d843c0016042c00782c42d0300c2210b0381d10b85c615040d0300c68200310840707032441d0011382c440d8450340c2501d17041006100e010ba001000f0403107251b88803005640d80c541020b0903540809498800c5c5a01100055001401c1e800a1504040c45030032204903d60364020514280c4c0254000f102d045070300060030404941e01021051104149040e03c0901e0b603014842c03408501007104941c51001d03102d0740080c130300d991008121805419402c20810410440812000016016024036034001107021415205403044034148848141c0c02440146007409416101200034040c451340c40c154812480049410b01050002e0403c0144617940c85540c1c20528041e004480589139410075018410014440ca82d00c40c2411943e10303080030b0b03400d0401a1548140d000003442248a944103603035446250501440e03024010104827042220f4114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 857755062 1250 857753812 857753843
    0x6031303170115080c19080603010501081203070e0d020409060203100e01080c130e062508010f030201111f061409070905221b110106080627010c020307 67
    0x9035001c070a0003070250112000196500040c81031000641c004501507002e81001c2006170924950780c0300c04400004242400c0c01c00c011405c1c00d11a15004182840061035038a4074200c401006100142c015010010110300c5040c1c191151001040c1541d406041000042d142c2d003440da00a402c00d032603c0c40c600c13481140002d1211050300500341602c2e0408003400e80d008081042008a00d54019540d03007194940301c0041c00b00e0070500ca554400c4c02091241c01411800f16003050056210f0b0035040240242c080c0103008000c03540c84084142d039420f00f403200101059660840c500405000441c421400190105500200c1c0d6000102140d10300c40c0d00c2e0041c20401000c0008401c0c0031518080007a41310f601c100100c1c03602c41072191118101c01c84840200d0b0508003000180c6004000d6089060b120200c005440c96100e840b104807649a00003c0003090309002c10301d9101c0c0070251070130740c00c44d40b07400028118450a01003580042040d1000304109400e000d0041d40b20b402501060b070740d4850880802 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 857756312 1250 857755062 857755097
    0x2003030f0402011d1509040b18061c080301090908121611070e04170f0d1b0e131a0a081b010c0804060804030509031501031202070f0b070305070206031303 68
    0x20b810030f48000f024969a00e48200c00c1c00080d4001000440d4019114810f11701107440703c9e26900440c1d1700c401e48908803450424184031044d94460ad04480f40000d040d07a40f0080f070201c10503241035981800c8041000300380e07424202064000c03801051010001003040c080f2480642c0c8074051403941c9a21041240c00021102d580c480c40a032041101404101d400200050070214100426000512000b414007a01424007030141c0c028400884903166030320030710300c0540c0743d91401d40c070050a06e15000011090711401700348070181c600080500b041e03c44001d14a66104010501c0503c44042c11044a82b80e4131258140d85410b0340700440354400d803410b041d25265104055000c1b120f50450f5540380f030280f0f0804125118000104150100401445048a81c0d03905102c0e80c030142c4030103004600c0030750650602424518a412200c002e540c0189002c01800240c2d035403101c119500185080d48030f194604007901d00340b0580c10025030103a4004104003460352001c2e907520805000c0d60720f1044880160310745 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 857757562 1250 857756312 857756357
    0xd09060f02010c120c050412030908060c03091009051f0204230a1a0f040b0711041e091104050c0c060105010e06040b09010309080a0320030403080105012003030f040201 74
    0x1a182130000f0000034915042a84103801d1494803500e05640d40d0007602402d82400000c4001550300a0304100b007000c03c002c00c98000310110540c901d507042c01e00450356140745c0400c807a40720355105c0d1103c8043c403409010303515420085002442c4081d00421910b00254054010003241e03801010607075500c5250080e00013a0018040d110b140301ea030420800203012100c441c401c440d185804c000c030308410b00c45040504002c05203108044e485080078a00000b120190202c11030040d49070942c0004031601400501801d2100c0c0c007000215204241030409072b100413403040399009404d0400780244010701600038012220040140c49080c1d0300c4e940111403961007130b000260300410601050040300300342d100901001005040c00038801c201e9545003110790b0404000500425a52070313610070004980c071b4010080919080c001c0d4554601550060421401030103001c0c108085c080601648403100d0344071460061200046a86a152800201c004030104881c101e0001d101009001a02c032140d218 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 857758812 1250 857757562 857757581
    0xf01060e04080d0b040609091a061f0c0f0b010302090f0618190615030605010c120305091005040c03111206070f26060a0b0307050415050c0d09060f0201 67
    0x2403000d055120764a9401c0c0c2c075008a40c640040558414601c2c5482c4d4440c400c0b44010081940045101e100900780240c2988440c861030154940c08420807c46035240c00c04621200300d40c1e10901d0b213400041c003045451202d680402809086070518003014000f8944925048920031103030543d141c0d803003501801405030117442d01d5401510b000b02d10001c80c0e80060b007030780e1720012082ca00d802440f0101440070075034401c1c0c0c0c0120135507001f20b180c0c0c29805238140603042c0a4002820300028200705d5584090750070030789840a6040551b201d000c90404441404241c2c000f00141d18180324074180f50030540c5550390944005c540004d084203030b07000c080c00c0010555111400c09005000150b40f801419904824081000d03c1048015904500310085080440101d10b2212903201101d180880a0081c2c1e090f194100040184044c020404001d602408440a40e0244c81c0244440e4200705002d65440c05034010101c0c0030300078406203000c0664081c0d100011108141d42e460a0000840e40c141e0885403040d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 857760062 1250 857758812 857758829
    0x1060b130f0b07030507020d02030604061a040207020d110609130c1205040231060810060b0f0d02180904120e0604150c020607080c030c16050609013c020f0106 70
    0x4803c0020a0092014201090002d043c0d90f0300b00b91543d0009040034021a800c88129650711025981c042c07441580c40ac400c901503600314a00451a00043c020580c00030000700316281321964036099489241c250394884c880030307121030005007900f0034900c00303401200c111000107a0460070b4110341809a000e26030085030081c0c801c4521040980c0b040d108030041c0d0308226510660388000b2001030115100381c00c002c00102c0058106115030360404003d4408660000703034402401d0203007031070810841046515140c080710300140e0700c2c0c15244400703052498640c28540c0c400c50070b07410441806000342d00148101165030322600403c0ca2103080040900070780c0200da40c5200000b0340d0488250160048400040c0018070703183c01c1126030340d00d610441d841245a44440e81001c90480d401c20020085101e01a2500c04484021401e000100b41c2c00d0241c1c4c1c00306030401041080310301c82c1d06040e043c64440b111645041828404d400415610182e1450585074010720903080c0741d9030500c1041c410035003641c4200307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 857761312 1250 857760062 857760067
    0xf010c09090902030f12070317040308010608070e100504090f0e2a0604090603021f080610030f0e011508070305030d0203370f0e071a070501060b130f0b 67
    0x1c400d4900804101200300c0c1c043c42052091090403070704028107141c3c248400c034129650807591800402d000c1d048004040e03580b40300790a020009130080b801d241945c195182c1900300b40c1d2135a00032288030b009000d100f50072101c101048034510b0b80c0000100252040c42c1400e102442c00d00210100729141740c0d0a0403103580120f240642071640301101184914180744070302c1c480f04811400984180d01030b81c400c9544965134101001141402c040f8090b441480a001140108a195018021044c010000303031046000c2082c10005d54065880b21144400d121020400c203c100d082f0310340248100d07410b036031007103154410000f1198000200241a20f90082c09503003021800010b10300a0b410140c1000013800c10450740c4194a80b10200e5150100c22045801c500743e010004d8010446d24541e1500140c182000ca403100c8030000081d200c000c4a040f0000c5e84000707580c40e00d1030300c0e42e03014203007004000307500713103800007920020a10140c1100401004000c04103a9101942c06280e141ca12942411b890709 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 857762562 1250 857761312 857761319
    0x815061303140304090606111f060315050106020f031201060309030507080705070812130b0307030612060606030c080f0f070311160606090504020d0803091507110f0706020a0204110903030703110f010c09 89
    0x59080c09c92403040244000c9403258603a5240c4071910341c8803109115080d07882c0010410703540c0c10000280c000d90384102030b5280030203141c80f0509101050003014181078440e400c410805204d0320840b640950400c1d02a40c40c0c00c81440e0030b0392511014800c42c42903100d9414002191030b4171101301d030380910150700190603040c902901010550070040c4a101810743d10380700058100000c0004011032446008001201803c00d0005800c81e4511104a400c02400c4010440c81d0080b041100d03030800c11343c4140245560390050100c02a02d0340350580000c0b2030020a4038154003082c10500444030303208140501c0b449464042c104222003086a000c0e5100c41c0c0000641d002c624200000d542147c94801503460007071640081420403002502c0c4400010f039000c20008541d0f01c103000b202d01d510b415102801c2550310700308000350f95030440c1101034803484d500c991031781215413440101d07920741c9005015030b503c40002d81001382000c041e44036002da460080403010001404184030308004400c003900d910218906 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 857763812 1250 857762562 857762593
    0x120408070911220816050a060806040e011a09131a04060e0601060507230705060d0212070c0b01060807020d031107020d110a06081506130314030409060611 68
    0x1031242003012180400c01c4843d0f4403500b074809100704000800c400c40242c54000603501c5d004804030701c050b440071203030070030b00c02d42c0d07038108000c0115102c62524212986464000900425900c80543c0c030f20740c40d04140c3c0c11031508104090450803011610480e985d80c4002c5038240c1c08401c1000104005205c0001c01800380201d1201d070342150280100040040c0d80505440c034051080e00304201051020a070041041040980085030503100302d410030302e0000c48a0b6280c1d44601d01c0c000d8a22036840458122200d50b00c90307055a403070000c0310b011205a0f051011001d088a00b0410041d40e0110740000003060140c0600308081c003901040c1d0090401c40d6003000c003100148224804804440020030500c40580e035500c18030b030140d034099540304140008034400c200800714103a10600038007601c081086860091000c080907001410b071111541d403ca0b80305210400106174000500000607140c079000d684070000064400d40d2200401007040944450b001d0f1011140100210310a91200c5a68140c081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 857765062 1250 857763812 857763821
    0x3060a091a0403031d010b0907050f0d0609020a0f1d060304080c063606040b0405010b0a140102211b070906170d032c03070803040b091204080709 64
    0xd0081c019154075080320303034501d24050000d86096001030348a4030448803200703811036414044a4124020400503d03201e0105a80004c02041c3c00d003842808130701e8182d4030a411040741c0046518803000c11401e0344813208600250086100040000c121054103a443ea008032501c1c101105081103144102d59000c0070003c803584018000c840d011001c5c0180240c809040207264054026459400441906a44e50b03a15074031b00c2095400b030860703000300f1078413201030301040e4590865007000e41c0124541c1d0300d041090142100044e80c0380c01c080e09e460700141056210345181240c282c01d80c240c41501401101414902c5903094800d100c84004000c110301c3e03021061880c40151610074140e030b14980d40c0f080d85504440b06540f090146003001a5140b903000d400380034901c44c0301010b060030054005050010580c6140410202da20510b40041080740482c040040d242201c0c1d20485a980c0d80c501481c22940d003040a446c0c0c1032280c442c00408030060801001520190781c8914003c100040c600f050300030191 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 857766312 1250 857765062 857765081
    0xf05041502090339011404050d020d12051e0315010309050c031f050a050c0301031209030b072c011407020d02060a051b0c010e0402030628060306050f03060a 69
    0x40c411452a801a04c005110711070000c102500f14105143c08403900111280301880014100310b02e000714808108880c60541d000e43d101030302c11807500c3c4c2281c030200e030042a1a80000c4e1800514406090400c0c2c1d0041c010314038152104078503041c0d0260361101c2d00f69400186d488601885d082080702403035500c250701a0000900803c02c8405e10001c410101f42002240040e041c40d503000038201c40414141c2c2c0c020250411241c1004021903c1c006500200500040c0401044038416000d040c1540f44582c100401a540007000050b80d420074440c068a14442d00300850000107078045544201036500c0303100c4c042c848040c3c6600350342c0c0c0d800c1550400309520000040b130f4031074066005000561141800b0b440403644a45075250b488081d0052540c02078856020701606622554044010b0f983c841203400d0714603010764025890b61115030000320328502c0741e4041322180c22100021954811094446422200542c400304545504d07502800b075a850798014094140c2c2c006404180c51241a6019038800c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 857767562 1250 857766312 857766319
    0x706030902010801060c151401151b0b0c040e0c0301051503060306070e040e0f061509070c152a03150317030a0e0f03070501150510030f0b031009060f0504150209 71
    0xc0141002910212340c010400341080998460060060100d48110740100c400365042038003038150303603c440f20040241110000d09041309440424210507907030742642c000d00810307920203070107150080320244950400d2103058824001da84400d6408004582182c0c05520068058451507449000c20394650341400c141a421076603ca600031000d4205010003401c035042c2c9d00107041c032400c3c50207285c09a0f8110002c050303c1000c1034000d11500e0f81e080604841110340c402910b100700c4202100c100b0082031340b904010f855540100640b88200d0348100701008841d401e031010800c3c0d20740700700d180707110485034000188448099866003034a1050034020b9039201564807008120084003405060904007250700c40f042d19030010980c40100030080c00349540a070110081a03224929140c0001c01d81c074101000b58041c50fa8501103001085101e4100c8880d164016086904a420b0084002c0060107403890a40e0040d00e0502c0b48000c001f9603014450149800079112002c5210007203d01000b9801141c1ca103a2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 857768812 1250 857767562 857767583
    0x31009030f0f02030c030f0d050c030609151309150f020a0c06020c01060f03081329070f0b0106111528200301080c010309050d031805011505030706030902010801060c 73
    0x14401410002480001f81c403d0304140c407641c040700314806071030002e058808140014010400d03a40c442c0018558400c0c0000c000c0f060b5442050b011812190b688440c000229050030340740024022060400402400581002c010030038050760742504030700502d00d8040009001d0709002c00400e0395900a4800443d010000180150707039421600504400780c0e2088138210400f0449800d0700014262400c0240503080c40000d1030001c000d62041003c0700048000150362001c12000184850380d81e070020301d41c1c0d120701040c00c0c82d61034410280c42c404800c03003101a244035584140c0b25450000f0083da014801140b200340c60090f8003055620002c64410107d100151b039480076054041c0c1d061000f0421003154141d490360395042142c01420001186200b074145400d044c0258000b40d000565850030032254900041c0314500d40c841d2040400340e001014001d503081000c0c0ea039081c3c40014030b100844800328200c1d40d00d150350710740035025100100c40183c0070031414001040880c2c01450380e41c80d8184035915801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 857770062 1250 857768812 857768827
    0x609061605040e16090f080307020409052d0c01031a01200a110103050a0527030c010221100f1509031a070323010329010e06031009030f0f0203 63
    0x41e02880072140b00013805103800e00e60810640010b070107000390841c0c1c01450f00b01800c01c0300003030742c0b44105c0c0e0000b405165140281424400d081c816900c0e1303d40e20503412204914000c000c42422001107030b250115001c0c42424fd001580a8840d8440ca54840382140540364070400054500180612491480112240c0f100c96124400d1000030036a40c81070b90580d080d40c803c20001011203100600306012a460b01c4148004802c0e9000c95440c26001e81040c00c80807034001e00028118000c1c10301c881c40c59800403441c4580500d00b41c0c00e072001e09941c04030340540c55881c4480c2100c0c00b020b520075801507512200c014881c0401c2d40700052a10b00e65410440ca0300c41c0e0ba0313660200c281248500360205c004090041c4540c8503450301601e41086110621050080c0c803009000c12034503410f11000300480c1224584000f6080480402000f580115201d142c3c02d694603100d03401c48810441d00e0a06c08e0040005030805a0401e1081810558166a40241c0c038280d203141616080920420a020341c0710520211 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 857771312 1250 857770062 857770079
    0x3070302030a1205040e040c080d0813110303041e180506010507032307140607081005060c0c041107060b010c0c091a030714030c030a02060a0c14031b060702060906160504 75
    0x6400344d84901d08e007585891131300d131240b8240002c0c047c0100030002c0803414010b12480c0360085a0318a500b00048182d0340c4541f030006803940c4500d500a50314004400503819101d406041690100c520b94104000c10380100c1c01000c044601c11121310307002c91000d2010001003407280d5042450056650f00700203070743c2c104482102d815006600e0403501d4038000400211640b2044c440250003080e241007030721031401e00d8a051014000a0701503c1c1c050000402c1e026070800b401c100001c5c450502810402030f04524000288955000c040d0030340d14541090500542548504a4139890b1034000316520310796400d055114024003400d05d5440001d05410311b0590280d0303801d02084c0010491071100e241d050b084003040c141841c2621200d1440303500070600700000740c1c48140440750943d00d07618000c0d004080d40c1c074200810030700c400c072200c100b44004641510350608450160748064860001c5914070799600c3d608a0381c0342c6048070b80d101260020004100b100301c030040741c16408000c50501500b407035118041d9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 857772562 1250 857771312 857771339
    0x8040f020a0905040203160b0a0c06020906040f081b15030612010f27080a03020307050403060606080f0a15090513140717030703021f0b04020309011a03070302030a120504 75
    0x210b40c040e5141c0074081140b908100d4100d02031b40c01051058600c0c603100c40b080207130140441280511100e2906d000400c03d07a41c1c111110120001d09154545888082548a0116130302405545104046140f0410700041000251030341008108100c901088006001203420190481e50040403201d03004281440a01481c2600b1081c584002400e04110000d9900148107650490b030114900204002080000c0c04403041d442650a001d42e0701e4860000c202e0752031180b6400178000c10300c4c10318042103da07448002c160265500c646030350065203514100d8000c9607251020044d881c90280010032040d5019002198410312490407000150030a8070b80a083e55045401c43d521034201078801c0c03100f41d41a10606e1000004030300214145800c540c0c1c0039507500354410304244400302d81c0624a070086044c5c1c0120488440180055480781041100513000c3d10a410a08014101d0300c11858824103000417402c0c2102c0d0010000d10300d0b440f142e260312003605006828141086407c02010407407500c3d0102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 857773812 1250 857772562 857772569
    0x7031704030c0204060b0702010507020405040519050a0c0e06010c1212110c0105010602030307230f0d0c090b27061306020706030b031504080a17010807080118021008040f020a 77
    0x2c0d040e40e0002c0d9881004116002a041350101031014002e030000760342d100065171120b641c19500003a60341c43d1360501505d4502041c0060703016901c0080b100b01040408201280418854070003011883d4955400050304502111400d0000c2e00d08031502d004074681644201e0184c0700340c18803811450343c811040c0b0070b881d0703c03801408030f0000c0003c880140d8142440f40c1401000795102840c1181080c0d00020301c82003520f07640c1100c200014000d1042d01c0300c2d81b400c5a450503c80924241c0d5807000c03005000c080c0005882d80d001045079401c0001c0c465a4420442c0d01d00c0c0c03452003001e608240301c00d1594030707014403105516410401c14000c1c4080c40c0d400800204c0a092580c00503d0041e15100b401803e540c0d9060b051802a0807450b80e041a260700000b01039023181c0d20000081d203d03410818202d44c0c3c9503481c0b20205115001800009240401040c80000c1d1155075009200c0d001110f0078508009030708000082d0000b03101d0f00000c00d04c51007490701641040c13284103180701c211699000140030303c00e20b40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 857775062 1250 857773812 857773817
    0x906130905070905010e03010938040605070f0f0203030133030501030c1202030d03051504050f0106021608030405060310080106261b0f0406050a0e0405071a09060703170403 76
    0x10080c01340e076800000d6544d0440003140248040c0405030307114001c2060034400d031080083c41200c51031081c4021001218441d080d0040302c0202d203054184000500410b07030386040459210499202131502c07071030780c0100f40c20032034004616591030310b0020034140454808d004030500c0003410030b2014425443d01849040c0d00b5540c00304442d410340c10025018030280d4003115106824081042c01a01c0c007141603246480d4900380054143c0c1d07004e1005c0c200d0203943c0e104c0303540545010200042415003c000d07505131082a800c0352580300c4054034075590820300e03004000c0e96500a000c00c0101c1d14240b40103603030044002c00d19842890380d4507449825201c0c2742e0440001d000d0500c541036a0540b8849400620b84140002004404480115150118641e100342401803880300d60342c05032030301e603500300070003c00010308841c492a544d00180201c101080d00c044416000b128000a00340740c1124072046030004035820b40d0b00e000b00c14000c006403a48001c008500380801c20405c1880c0084034404148214000d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 857776312 1250 857775062 857775077
    0x306050103051c02150c0d0f0c030522061d0a050705010824150c030c0c0f030705011b1b1e150504030b090c03070b0d20090613090507 59
    0x518259050481c0b4400f02e005031000030702c0e407548107940001d4450300c01c80c07a180c003000c0704d80f40c10030b0142d80703482151440f84140742818a1203449000c95400114441c1c80b0740c1d42044152a076840e4010100d100c000260410340301c040c4e524000c996250700c44040006801280c4190012041c03440c0d0a060358030800340c2c1d254110002c10411940c2080c6c00b240e0000031700242101c00200e850110002e81d001000340781c003a003150801d40c050b0000220440c2c4414104c8000c8030344030800e090340103071b030380d501c0c0101c66015400b0b2030040140780c240060b984040c0e401c144c440d0740c01c20342600016078202e0300988042c3c075074920007200c403c8204160020000036004182040c41e03100340c200e6040d0401207081d4411603074901c0704070440401c140e100007502c041c0c0e17a0000301d41446454079090645480301e20801c40b60300d4080c442000985108210086c445c0e03219440c4188040c0d10007030701301d8940c11500400d44402c120100801c1d003e0b1325000004020100008a440000b261200d03102e80031903a08807015804100003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 857777562 1250 857776312 857776319
    0x6100b040b030c07060e4b0705041b030b0405130f1109040606030210170c07080702040c081e01120201140c0d02240c09010e0d0b040f02040e0c09150a050a03060501 72
    0x800280e2414001e25540017201225030304c1210015588180602c12030900003516040c0c40b1f0400c0c84402c00902c4024014070405482c60001d18040d07214960700340c0880c1c81d10b140441241854014144203010340d0810f144c0d1310305140ca41080180190004507000c448104c00f0080954840303c401d4001d901407100000c2d100d003148140f220404501c00184c0c2840070342c003008106920040e0440e0741c00300000c20b03603645540540c504082070f8082d020740250302900f4a0510303000c650703120603664400c0c41845182c89181598002d04c1007056020700483e02016070402800c809540035400c030880c00f111076154035181802d4145035500301080b0181442c01038015074580307121030000070b900404100c040140b48105060003040000b441c8280b10050303041c00340a83d0014001e42d215481c6a100541208540d000c40c5441d04d00f0f16001c1c1e00c0417008134032030b9103421802c8800703a40004090b050080041c0007020b258450540040b4032051200a00364041d41c52000400c058440000d0103005500c24080171031103506 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 857778812 1250 857777562 857777593
    0x702011103030f06010e030a080d020c0601120c0311012109030e0f0919090506010801022206050a110f1b03010c020c010c0b0a0f1107020306100b040b030c07060e 71
    0x90044552103a68002e20512281c0b4000040140e0800402d003030218a0481140209081960200000d041060085801c248a002d990002e0401410300c0003a50701581c1c9031440c110608554680281c950400b42134180001400c140c0d03c000446e10505006044028034a9903034007803150302e00300918598890815000305a045464031020381800ca840104d1f00b0710000108140c4013004110f0540c27400c4a0900546105242c4c2c071009110b03801006481940d03840380c0a070ba010b507001111500e1454283c04010500d1901080540f09554495540e42c3c60040c41100c1120a1071280a130343c10980103841198082030010001e000f00300b0884911108514260800c042c07c645044000b102590000701041364540e0307004012405e2140e2000501065031540e1242e10010140c0381c401007034040ca44869030000181c000702030031600c0d00c01c034100d4445a45418452850f094280f007411f000107000d00060043c2c1e07200101a65011000d4255079003072180f40d032140c1c0c003a07540b00002100303140c2080e00c50800742e45 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 857780062 1250 857778812 857778827
    0x801050103020316260906040c05040908030105010806030c040c0f08010906150809010f1a040c02160501050705190803010302090a140a0b041e0c02010612050d052d070201 75
    0x902420300b1070541c60000d0140c1c11402e141c0300d6510400c103010381c0454000007104005c0c1c00c000b03e4072039221002d1810b10f00450752490141c03404d0301c400050800000d158901405409880d0b40d100c42d425003144d282500640300510050856a454040d205512526840d14850002e504001e070780d8074007034003210358030203483c0000c10f8008000d001d0510405201102c0d50907100302400620740b400d422541d5030b0381c5016004142c185001120035041585001c030703002c102d00300304445040844081018460b26041645d590b203403140b0300d041122201000300000e602403c00b62000c140a041503442101000030346030448124680c013151401c0c004001402542454804580d000140c0e81041007141003e900324080101700500c1c010009840c1d5030160541c7e03d40b60881c94554403170315424801d000e0700e00180000380100c00c803000010740c43d2031380006100801040300300160340c0040160280b81c01040c400c079447da000c0f42c1c524440c48103001c81a94011030281040240006180d991510380083d48001481035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 857781312 1250 857780062 857780069
    0xf08030714070b011a0c030307080105011106040302120318120409110a02101d01020d09060b010c1106211003030906030b1f03062d0506070507180f06060c02010801 72
    0x1000c2840302d0b00002c0e44540031075054940c411144c104494140e540d5074a01d2107400c0342d2001601021092140c4280c1207031400f416034100f40c079080707200d0410100c01a0f4450040790083e0059001d8040900c10182c003100a58000c508480100507080c1c00c0c8115034a0440c446081c658020307400182040140f410344681e54804901000c21440d25001000c0299162886c582922003580d40e500340710340c50f10781ca0b41408581c11030140259210001b2890800084c00550020381d0200c0c2003003221040340d8841d0418420082d40f0048030003001040d481804129000400d0541c51100f4503d44d21002a014841461040d600b1045500c2d00d2400c61900901361100c50384100141130802084043e5a503802c41401b41c1403560304107464496a03500001c402401040d403100400426003040c0c880e00511302c4410483d550108a60074400d40c0e42d84050100c0b610a841000d080350b00302c2141805003600101103411b0000c06640085181100c2a184a08032941a071092001c10540c440d00011541c02c4524507004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 857782562 1250 857781312 857781347
    0x40b0a0303020f07080723010e120d03050903030c0409151d01090e030405280e0109150f060e0d050c132301050f060703032c0715050415020a0f080307 66
    0x151a1003029005074500d40c7c861503500145080080301648141001fa4072888001c04c900702014460103403989038000000b59a00082c140400280301c0c45000045900a50b46c1c0d24119140a19007002000100054803404020442d55500000d40301103022120186c2041d600964100394504402001114455070035101c440d0014402001140d68882d070301100d41904d8404422070840ca4003c0036a40b80c1d07550000d0309441c0c407034400456504205e500110308218110780707440b002a01e41440e42101860303840b0f281c0015a840040c80a28209520070b040f202d07104030101c40c400c048403000104041001d004900349aa0388003803600d01405403802c00d00310090040301105095040101042c1a121244802809450001240000c05209600c0030080c10400807581500c001c40c074a0348920f61443e050050b0140c841d20f0030100c1d00030640507080316945440d0711201d1a09151040c3d54048038039024440301507018032580301000c40c5151714264005031150f401a5500d06e409180a84014001940c5018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 857783812 1250 857782562 857782573
    0xf0103050a0807051e0d0e0102010b0303031503151518060108040b07210603050d052812020307020a0b0106260a09170405040b0429040b0a0303020f0708 67
    0x21400c041107049105401a02d0329a448241382045441d01100da00c5c2a2624205084690b180503400300304040c190b0000d031b84900e5950b1541004a09964003141000e505070020808104500f4076180c1c542110796014041da01e00190715144d1050004007124641000b4040c5a203e0303013503242c200c0340000240e01a101c1800c3c581886800200090700040c0000c28548042c808103980900880400c078500022603000aca103071001c0102072015012600c0121007070320822825a0000d03001d103068a00704801010380d4030903035484049144044a040c5500b00521016050300c2d40d1f154242d000440c419480d0350006e100305005454002c034000c005a2240301040f0203003548020b64043c482d0110001d03031031301500d0449a26106140c00c000d0245200040c0294540c03980800450031000c064000c4900c21181049440c1b00300081c0006c0d2001c00d4105445207446692000240d001070b01001905d21014100080790110703100415410103d68000f5005a0300c13090030821000e80411000c0040e100400c0a0304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 857785062 1250 857783812 857783819
    0x606080a020c0f030a23430515010b04050105161a0a0e12181e09070207060f0c0f0308070215130606090c0206220b181603021c030509041409060f01 65
    0x803071210280300741c0d00f83c7c82e000c295403031000e02d10402c000120001380c9060f1031015140c905145d0300c004488440954180c50030000881000020030b540407030354180c5a40c0c0c600000ca0f58922021020450110f8030301d40c1c0c60749103244a102061401d803196001c82400540075421607a003901c0d05060700c00c1c040d06124200b11205850f4500b00b803590140c00305447c2c3c03200802c400d0003091008041c1011468200000704200a5130a50004840040b90b00503124410860301c0d41000700d64940c0210780281c004003a03405e000700081e11034a0550f030b0040b0341d88191811010340b40d00008604800ba00d14504c1002d007403480109010300f0344030b07140c014079030400100f000c0d00101070040d464620040c4000312109030044881880c443c2c034904680e00b503501170341c54000d07442c000265001e4001e580c14680000d1103209885000364400e240f012003038a80003018402500112440d2005600c850501101002001c0c00301407030700d480e54042c0410104c030f24a60b502152400c0c4c02c403589458001461406460260300041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 857786312 1250 857785062 857785087
    0x2100c030f0e062406040308210f0103260d060b0a030e010605090103020d021c03020610120c180e071203171506090f060d0501180606080a020c0f030a23 67
    0x4c00d400304101200d116000007075400101c0ca03010303980c8003515101000038120508156940c4086684840c0b030380400310b03601c03100c4412500c0b100074003000704bc00000b5a020050f603403c03482c0c0c200104d5102c101c0700c1d00d00602000d503e001d84415911045442d00c2c049007039801c864250013540c1168810400801c0091300c1c0200003107041206210180c02a400020741c00c06641b500da05a020305441c14080d004154110316000790303160000c55158075584125140400d4501135a01d40c0c0c08801e030402500f80c109824080c800251140420718030ad510360b6604103c0d04000307020b000c54401010758007142c481c58003003800c024200e8552030381300c0b001e2030f04e07038404101d01ca105620b6007443c00c40080c3c48658640c11507102180e284120301d103c907070340b084002c40c1d0b01214001030b4003c24181c1d450554080080c02c1c80c066404113070317501402403e000c00e5100300010424070f82c0ea805480042e41c1d880403550001109040c0a0430750340700c003044c01d0000381c14104042500702c981d040106181d642c044038a1524440c10100c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 857787562 1250 857786312 857786341
    0x8030906090a031b0806070e0f1203070f0f02040b0f0d032d050403050d0302041508040201021e0a0c211403090907110c030321060a0e15040518120a02100c030f0e06 72
    0x990302c20301d40381c0c5105982c0241041a84c2e44554003400653752492070f82410025102104000c07840350382401489485418400d204032030640016190b43c0000c640e40e039080d10011210300756100c42442c5d07204002606140c01c605032007030303c1c8039844030340e034403821800d100c0e05002c007288a00701414010042080007800e2008440b030300154924140340c0035180c41c80100d081080707520000d92038000020070880c03050408500740c44600e1196036003001c15aa1906a00076428100100800e6010442143c8000c2a041040c840500d541c940c01e4901c0c118103030700007c0741e6030403da80d6500061401e04000e003900790104440c542e20700040f0011070618014030103140305401d07101411207401c40c6a20215100e51114000d400183c11040301104c807528180c4a040c61001c9507103c3c0354815400c0c04080345c0d00c0451a0f4a60107000080b10140041040002154402d9401031004004505c10007120310300c2d81440344070324036104041d82d8001c50401441000f035420f8a0754228010303010b81046c400c0c0010444620714 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 857788812 1250 857787562 857787589
    0x15040c3204030f0501020903060c0a030c140301150e0405041b06020f10020a0e03010906020a140903031902030d09033b011209020402030c0307110708030906090a031b0806070e 77
    0x203070343c203e100607480d15074060302415490715018030038001409015412031024040302617041d036080140c20380d4100201c0f40f182158420001c00a01000140244030b11141d6500c3c2030742d41c5080031814144031002080c21110215425a00050b02101c141000340c01003140c80c0042c08070784000e01c4040c03090040070b40c40700e03171103120001f0842d07000030f01407031070350040c2007202048200800070040030440b03041c4100694407036000c040c000b0b1000b002d006203000c0e0b00401e6410061015004504100d01007550311010341031003060009620040c41031582c4c44103507014459140303120359580794002d04a085d4601610030800720b0282d200080141030b03014400c807034012441d0440246000c40107640312140000081c144208040c0d003041c000400c121280651400441c014802643c541601d01c003286040c0c1d0301c542e118010103809810030080101c180c60f04a014110111000b80202c10095895440c601504843d01c882a1040d507040d20401c40f0302c6050180c2580141141407214041c0c00c008000b4040074075040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 857790062 1250 857788812 857788823
    0x60906082406040b0d050a0c0b1c0b0d08180a0b03040312050709080d0e1009060815060418050910020412021203070b10030c06030b0907050315040c320403 68
    0x10001410b507519500501e840c01c101529040240329241407043c0c44034100d440c00d0303c107031206010008a9881d1038040740e040c44e807078582a107440c0f41d282c045500500391801801e81c0c441e8200343c41201142507031000346100d1207540043c81d4540158020b02000480c2035001035080c0c40144204004072384c010501c401e5001c04e10300002910340d1402002d5800c403c440d08900c0292241e02c0d5030402907900074004010003035040b1500d803400f00645004441c0100d09000d22800520710001040c143c45075104810054200208801c1c2800d4541c40c49105828902d40c03090022038459041c4002813409002030501c00070080d000794a01400d06400035001081040020301071015400da05041c0c0d40203106850003980e01c840f15403442d08004020b040c030f119440c00103407528819000001034050185c416000d02c4400601003082ca41c0e00e003e415942ea0b000105500944850150401e00d20380c1c03030313118010300000e0301d880f03010442d12007150486115000c003403645503000620740509522008941907a08690740b02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 857791312 1250 857790062 857790133
    0x1030204020a140a03150f05031c02210301090b01170c0a1202070c0e01082d031308160e04050318030313030c17030315010e0303130906090608 63
    0x6910441c0e0f2524400e0302503c0040011030010201540342e04440c2040d8411031a280403039844108840c1c0a110ba84209507040c0d100a01c607441c45003444584910180960043e180c1c00c010f4034141e034124840f11004200c00c068004010301ca8805544904400a8003e103040c043e001c040035041c0c04200340c00307070400e080790030f02188000c16180701c0e80c150300604017144429500e4084034645207a400c02c280c015040044100c0c0700200b400c040010300307071390100c01c583c0440c020700c10018080c09002152082c0311315540404c0050545800e850250200101203400041044452980d000748004030103070401000780b02c0c01d9040c0004143d0010035900c14444005544509544180c00689503224011640660b200381d5100001404000c40b480700c01c031008030a2078880404170010b04ca0300c03444100c41c102013040f0000c0408a403540301d00440e101c4031074060708032480c1801e8840004181e45281d030144030801c0d1240b0040c8480030050061000030050762004141c2507510341d09074200302090340300300b20b00c10440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 857792562 1250 857791312 857791327
    0x30406020607090e070207030b0c160501062c0f061302120a0c09060e0906120f0c040c05030103031d01140d050415140117011401030f05010e0c060a120f060f03140a08030103020402 79
    0x80d041120507180c40406039165042f442d1800c607000c2e104a100d50006281d10030703c20140b4010780c256407071070580030f803901c00340300d40c4d0f040d581e90607082010300455080341040343d80c2a1125141d20090000460b54002903a0900d41203032075505a402c0c8081c4801004110f4100300052a04148007910340441215041d1b1030b9503c00002c2105050180e2072812688038004a2004130782c00441ca02901582c185c4083c00b059024034025a0244070070710001b00090a614910038039001c0301d0000c8001c2010524203844440451410310500ba0044001c00211a0b941c0742031004100c1c000ca00c4080c0030084076000d00c003d12402c0c144520201c01446106916550701d070303001400d00c40a60041c036403104103100d990902d5071131b0704108500418002d0112032941c40c20b91650070b20303000005c0301c04029100610142c94050400307001c0301d6241c6180b026011541d21418440c03800b81c2c00d4090300014008801d00c0c14001499800d00f0801c80c140180f415106030019001000803e0046040301d0540e6015500960380d01c05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 857793812 1250 857792562 857792581
    0x9030d0f0504181b0908010506090f060d031e021e01060308040e041b06030c1b0b060f240307080c03090a140316031d220e0f030406020607090e070207030b 68
    0x40b0071920122004d00c0030103109a00c0d00101150141c0700050020003042e0351345401e0181000007582c0c1c0c03001a1300244005082807400546079406240310b0b18000401040d8000000482220709010b040540c01c2900520301d101c6c00d03140c1502b0078001c034a00900c280c2d480e68035442ca0300d00c20340c00360303040c403101280000f4140819190b1000000004100454210b60ba404004005080d2101c0c2d90000590700140c1c3c5c03e10b1080f043c5180703c01034200b00c05144a48629003002104030300070703455a80200c400184403051003c000c40708808841001826580da1400d244000c111000003030120409040034804d10400c1000001c00410150b0301081c0220b030082144000351450099002003401d488550180808041e800b65042007a600c00980c0889003003502d904011100c68081c0f40150440809500c141e101c4400713801403c10340818109a8078000e100852540c10365115401007009030303000001780100e20390701c4041a002407180b01c0070356002d4104030100035101d4505110181510307d0480c00f290406a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 857795062 1250 857793812 857793821
    0x703110c1606030509011406040216020604081e03251a07031d03040506070204050c090604091406010905032d030d09050105221e1709030d0f050418 65
    0x84a400311555010039a4000e500304441d030050300002814640400c01c01c003814020301401c10076282e0314140c6c46d038801041c031001b5003050b009444400035002d800d00258450100401c050b20001c0040c00c1300c00a03640307103807a00040c0003030f1b8213007181d00c2008103002400c00b180c0c800d06200410022200222032504207158a501030800d608040f0030500180402c09405a21617030180700c4904001c1c5200d0741d0986155102e0140f40304481e04440c003040800010b1a099000650020404500c1ca0a224525004c80d01942081c0c201c03050703550340e60040e100e00d2400001401d1707000f0802d01e0807200710b90604000c241c1b602001b0b91940c03068808084021124821200410388801b050000c4a071031700e17a91001a0007074206254140c1d400d52805c1b01041d40b28041c01280da0071029040c4100c942d50b482c41da540044021046400c16800e003040c0d15420000c1c0752504c0040c03401c0f804444d081d46a0004100301810204110100e0052040811100302602e4000e000d45048a215132140d00074001c440300d0031030140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 857796312 1250 857795062 857795077
    0xe0303180d2a05030f070603181a04060506060703171503120a1409030304061110050406020910090e160314010e04031701031112030702091501030b0f0603070311 71
    0x11108a1200700741c0000750790303402c8025030780140c69402a42c1d08141522005042070411319500181010702c0340b98003e4100042c298107070141000e0040540d190300d01000c410759184003180078410300b4041400340c103019481c1c209108491a80c07412031641c1e8094a841803000061040d422081c0020b010809050f1008071810030250641d44581905485852154407400c512008a03401900000c6001e11050540701c62034400381c003c51900e070a002c0c0036140c102c001001e5094500c220864000b821803d805964000c512940000d600c4944a03410400d411486031805403c10044100401c010b1a00c0b0103070759080a209030158040707558130344044002c5c07e1800e020360741c20400800001403407152072035858810340c003a84da1840b45140280030141c1c018028030000d040503905d442d0710601864181c0f142268a1a40c4040301c0c5001c182d540411060f0404494031410200c11403400121540c150181c0e2900e004100e481c6039000c4403150020b81e00d800040c15050030035580301c1e451000c44013803400b2100d62 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 857797562 1250 857796312 857796323
    0x105040c170c0c0f030c0c15040f080c1c0c0306180c0e060418030503040318210203120703140c030408060c07030e090603030d2703031b0e0303180d 65
    0xa902e80105024140d50082c0703418540b80c0304030083d29031600000700940f01c1c0512640003a00002c40300d8410008044030860015030010020400000c01280d14182200281941d001412224044404200c206803284c848018544000d1041c030f0005022200c0e04c006580c1d00c0b007030000b0600d41e00e02102000705071301d0b01e008000850306000032415031242c08140f440b03010300300c9061050440c0d54222036614283d884004010840a04c04100060300540710007600308820450b0484071a0340794504a4000056402c0c00c80410500c0b584034190308041c0000071200306410390040c605070859400a004160320200b41ea0709001c0400c0340300080b1420300440d00240f140008960a034103101c021424640c0c130049044001c40c0e2070211114441c02c258001d103200c2c160040280d41410002c501101c041c000c40310800264138401801c11010054501000c9011406603800040790f04c04e20b44100c44a1032000d40e640d0030300c03400c00c8042c400350350008103c800721142e11031070340002c20b19030700420310300c14802da8020074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 857798812 1250 857797562 857797607
    0xa050903041508191b0c030e0d0f060e030903100b0f0402030f011e0513090c030506130c0e040206090d061512021807081501020a0f12080106050c060105040c 69
    0x80c203d41c0402014010601c0c40b140e07410b10741d40380c2800c0d011a04211032080000c010400c0c08180207000300301d02c10300e42c1c0c042c0c104140480712140000f6011154100119502103800000b0380911000344146806000d90308025071620003190b00290b40e40541c1d0030300c03181040d00c0360000e01d03064459000d0100c0c00300c0040e20035074690070f28601288030224240035003e50a61410710300040c1001c085280380868101800c21018416004102d00140030544425600007403070a9000000070307020042c26109019075841c1030055070a6140603115800940d0200c021014010107010269451904440c0040e004640c08400300c02c091403d1405400c03081c1d18100a400c100c07400054003c01c203e94940303030740c0c4220b582c1001d00c05c2c0401c40d102c10a5060b61600d0016076510001048801d86075400341c00c01005004581d2040e8640e550000e808006400844d0120090300300c040d040d90f007240d41d59001d001c140c00c100d801d16201d10042540e4605c14440c1d588129102d00e00e4054007070080200316a080059501d100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 857800062 1250 857798812 857798849
    0x70c1a1c090206040603050a09050703111e030c0405280902150304030923060309100509030301030506071d06160201020601051909020a0e060301060c03090603060e0a05090304 77
    0x10a6004010345440100000c000450010000d12440c800710b6801016541090f0400c0e40c03c90050070001c20700c8510030340da0062003011030400c02a40300158416421040080c0c208000c0c001c0b041c03140d6012902c07950310030204144680d00030841b01c61002080d1400692a9a07030410000c001c10000790140030409d40c0c900d980d141d00e5182c0c0056400c01d000f540c62089880707600840c01451700c01200c001d4005480c4100612040c64031103981d50040600c1c40085400c10400c138001515035200380c0786074159030b006c00d01e41c40103a4100d004030f580c00f4140300007440c159072450b1074040c2c0f1000c0060414080018499034405900311000c0303c1c2402080207030905844040d07182c100c0e02c080c0c60305581030780948601000008c03685002421500c8000118140303076242c0307280c000a48040e4000c54044018007400400320401d0b9290000514005c040b2075a03408210000750a0280c04c1f0b27003058101030308040c00c003c0c0510040c0d00156000d508910b03030400010722560368000040c00c1d800b03907030004846c4071581141130 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 857801312 1250 857800062 857800109
    0x4420512101a0d02011d03010204090e070e160302130e13061505100c0501020f0c030d0b030105040b06091003050709141f21150911040b0a0506070c 65
    0x401c4901c5500030100014100301030041040d15401015030380c400030801e00d02005500c100c410071200d8003c4908032154000c0d0320002400e80c0c2087d01f181100a640e1201003280000c1040b51354001c140c4560380d00b0803401d25a1092071070f040c130b03411a5130a1540000710740c0c0b1100c58446904005040708001e15440f820b0074400140f00c07803a40d09040d610203042554403c6044c1d6200550401c6031401001060704900c1000d080e03c0e2020410b40c1510207545c20700c41d20601c0c00001000b0501d02c4680720140d030f55904200c541ca8101d03032002031500e009038075210400c4000791002d0f15150b0040c03000c83d0034080031398a1101c0c07008880490707003004005000c0d1000020760b4500c0d54000c5218a03110640c1d00800b0761303846092116142c0e11200003145411140010055460790307507000c41c1c89003c01c21500c0600ba001e510740c1c22403800d81d10f454500150f95072040c2c009106540c10340e01200f8a040320180410404400001c0f41c562090044612821000a2010401000506032001480c0078222440300c014401d804 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 857802562 1250 857801312 857801323
    0x6090903090e0c07050706110c100e1e0d14120403080d02030411030a06020d0605030a0209010620011407090b03060d021012050a05010609061403190204030f1104420512 74
    0xb00307000d03c0327170303c90a69452504000084a80e51140c0d94032500781d58035810044520b04072103250084c0c8599080e81042034071400311348500b06000b81c0c00150002c1203140c40034985042c50380003600c2c4940a002c24400164040202c3d0045c800e401d0001d61a52500d0424441c08a0020001c0341d141c428222070500700322058002d403c4900c11140d041000c50b650700141a00c40307170b03c02c0001b54080403040041c0082400b40d00d50141e054800132004004e2180075840a00311240d80390100c00b0031490034100811191711500010103400f410046c2d03401d6040001c00309100d141c0940000784076107150b0b040d658105201d650144400a04401c041c0401e090840d580e100415081c06094000307032603417402003a440d0140444d4050081d400d00400d2335683c80705884100748a042201a605540800c80003001c1024194503c000c14054000c049054403210200012940d520340b6540e0faa1164460388001b002440c61040541607050b038440a00c0c880184542c204103800b07810a07035000126008046260400040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 857803812 1250 857802562 857802587
    0x30c050d0923150f04061404051c030603030e150d020d021312030903140a02060c102007020108040c0801050907080115120f051002160606090903090e0c07050706 71
    0x9207090703248608440b291110907011842d40501c0c035040120740201401d40504d64050f009170310014080601c01800010007406607800e403560341c8402c840300c0f940680e031100c2c2e0002c000b95080411005245550181580840700f64940c031139020401c0c107001c62905502242c3c600c0304000411541c804c070301c0e0341d810004d41080c040d03000004c443c2c0c24040340c0480d181d03200000c100d406171980b0034101e20351f5496482545100040d03107450f00450b076840c0d006071100d1b00070745002c414050142541420403001d140403103000c420f00c00c0c540750440417048601c6c01c050048a03540c0703030203182091050b6194140b0510891b059801400b0350740c40c04040140c0d04401060110550321044002e008450a0600802c0e8075201401041078281c45032070004d00003240d085900422510940a0300c40e01441c81081504a0300440c8004130110a80c0c07000400304034042c41000054100c0c11010002d4241d5500c000700101010b005451664802078042444d00c180d1a040c2c0702c07141e601c00c04441c141d0b0380b40c0c03200030080c3c6d09020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 857805062 1250 857803812 857803853
    0x23061008070503010c271203090603050618070509040204080d030603050601091505060a17010303030b01091205060c0717030109020a030f0903120c0509030f03120c160201030c050d09 80
    0x100701240518043c00b41004e0007915560313211851010001c0c8000703020180f2518003160211100006d1080d0481030b580c03449502949600d1040341c80c01c40b01800f41c2d04028201c1d0f00c1103d03100715a10211030502d075160303004181c601d04a03840d8107014011400911807074019003420310801d00c204906540c160801c0c81968410300035560036982e5912044192202c20609105410140c0014000c40c05d0240c0509038000035031412058a072071100c0b501c074198400fa00140c0019071200340c51031941d604442000010020324400c1545030b030307007500c07029114080a040c2804103480043c020050002c0d80c1e925803009000d47c0c4c803a5541c2d59494180030001c0d40040c00e454080307403c104050f0440103c40c0308070210039416407900800321440c1000c0341c0003070000b83c2800c0d090000500a400c10707902d00300818052002214000c40c1ea9000d035460b11090420000e00040f90020200903611000011060b601c23800c0d942070a02103828000000b00b9144d0340602c02c841c4000700c1ca41210201807003039001c5841005071060 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 857806312 1250 857805062 857805073
    0xf0b1201060201090f2904151530021207080c030c011b05030702120d090501090501020c13200405090a09032703060203090a060b01030b0105040e04170c0d09080a0f23061008 76
    0x1a20041c2000928800e18070740c02c031071510640002c0302b499000d46c419414080c0018142c0e55a078000fa03032075140c0100e180c00e503a121b05424491000c00300059003d40c00101c00034010304948000003400c00440c0c00e000c000b840300311240c0404015041055580c441d0780140446030210f142101d2945c2d031140302400b44c00050402c0800034055018456500a460f011fa02400400c010b41052051040240d5044000c0c1c40e0341c0e81c40340e5440d0385414007a02c0488440d180c00c0e40e5a0b45804100130001c00003a252505081c6880c1d1010002504402034107910524104a4480210140300880e510100c560024040300d00000411040303240100d1680c4149104003010040c0d828100c00450890700c2c5418030501250b001c100c00d020341c2d094054a240d2252040c1404421100a44020a11a08880c9085030143e001800e4502707119041200301002d4641000180f44101141d210a02c40100f03001c4040d203a54851070003040001c0100c910032000f481c0d080112002800c1c003811145c013100c5584240091801038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 857807562 1250 857806312 857806331
    0x60c1c02161a0703270f18060e0f0405010b06070b0103230706030b030109140a03120c080424060b031017070b130f0b1201060201090f290415 62
    0x81988420b104801203101500389201070790140d483d0032030b1450060740040070381c1040d40352031024990400505480790400c0d40007450885849031280090f0002450503040280600001d99400b10059211010307100381c079007a0300c41c0e0400034010442d0400013504040d00080900501400a11440c1224800c0d10347c100c843da0a12075141e0050700c520b1112174030ba0494201000003520035008600c100b100200001036510740da42d02c00d5852501110251a00d802603050725042c1508007400c0c083e00c1c1f000310410711000300c0c100e000034004140284001d10f00c0c009800d251190689a090084824106800401c48142c035100a40b0f40c0341c0003201c170226940c0d5454800301d0012002074518008000d508020000642031004602d42500240c1e00907a140e40c1041000505001c0800410020840d2104199480310b500d50040c80c080e005030084000c1da8109200d0000241d031040210b104280c10104100001141002802070b128540e9484030050807858184000c1c000003084070041e10040003400c22004c0003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 857808812 1250 857807562 857807579
    0x62704150b0d02040c050d02030a0f0516051c0207021002010603060f0c0c0209040611040e0703060b0a020d080c04410907030f020d090f0311010b0f060c1c0216 70
    0x16181c0d9903900708041000c040c006003010342145511002904010b411f002c02c41030064101d0b042100c2c403009203520760031001294201807040da900522480c04031a810040080701900b18031600310201007001e0442028800e04040790b05a801d200ea000b421740a00040c8100000c0c083c011600003501c05d246000017081410720f2511a80700c0c841c81030f4941105030103258081113021031008209840050300d03105440d0f1324416083c0100050010360907580110708001c03500504442e25600300c0e001c0b0030b00030000c5548240d00040c603200c4000f07030b91a00c40c503142e8496130400c0441c0036982c00740e9100c212010380c054041c80029003400c0740c440c00e03d2004920800d20942690800e00c1c3c060040d0b04007401d0004101038620070703000b80301012180c0308007502d000552a4000e040701d001d82c0007501c1c15684520361000701a8440503403040292904c000b80a4406000c0c002020b0b25203ea541c14800c0c81c0000e40c4404458081c0290103074480b03180074101100c1c1e09084040e444040342c00f00345015242000d07000c1503511 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 857810062 1250 857808812 857808821
    0xf0903080f0f100308070f0c0e07020f010c120b0f0301020309010c140a050a0507030c0c12050d090608130302120d0204150206071b020f090c0d0e0106080a0b06270415 73
    0x501d580c003d009403840c645500402c2d0f40040820b480116410079054080b800750300f0074500400c50307000c1d60320051030702d07000081c1031aa04008100084e410088064010355010403411400f405035000003c601c002c11000404d03421218107400d40650012003040900e51042d071040b0850503250715549404414000a000310380704000059010440030b1040b42041c0b4451030207410003d201c2d08152242c025541c5406038015880e40c07001c0b070210070303601d491010040c051010221455403410140b401d141007a03000742c00b8000060500341c1071941c441c4828240341c4200600041248503c04c21030744c0d000c00028400c040d61041c0503506100b4140202c041003540b00140880c401d8045544a4050407103050b51240443c001c150180c0c0d00143d00d00c40c1100725540d402c0c8107400f500d6030b211130507903e46a00c80c08405450302260b811403070f039140c007808000008009c1070f07240f05c1c660311501c030205666a0900084032602000050f1100d658003512111aa1540c0d051443c0140c4c01061084d100c1300780750100c202610f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 857811312 1250 857810062 857810071
    0xa0306051f0c0f1a011701020316050901020307061803020c010903080d0207060f020c0f070602070621110c0304030b240f01030b03031206100801030b0f0a0f0903080f0f 74
    0x91030000c0320300c0840c0700e00203845080f4400c0d003080c4501c1c0b0032911402c2c40d003d2030075161100f1040150040183c1c5201c0e2025004201c01100250308528020304541035900f0b00040b544240b040016a804440e03109000f01d400459000b002007107940d140b003007103440742000e001049015111b1403400128540c001c0c2030b0a4100d82e401011180f40c10320000014000c1c0d00b00f41c400712105502e4444503000000d950015180d104510350040403100030400c449480c088941e402401550085d110610606030311030325002003821035030300707091640d00740c001c0031402801401001d0343c0030074021540c00c80d031800100050048030b020340309841103521000d00d03080701c60640d17a4a9040003c03a0028034005801d0500c0701e40c400301014100041c0007209040880c0c03c0d03520030804200e0300d08954040100e40d02e803c800c0d031b444004052921408a40c155642d5020154001d01110364002d50440003500b0750417603400c84004190b0007a8180011041440c02030300208080da04031800b282d485000820086116070401d104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 857812562 1250 857811312 857811349
    0x3090b070c0c1e170312011a0d02070f02120a0b0702030405060d09030306050306070e091311010c05190c0e0601030b0a09020708090405010803070c0e060f0f060c010f020a030605 78
    0x1c00e03d81034a900905002040501030b52224540c000ba5035140745442c01e44c068246805199618440341e40c1942c40c8005800c507454509401c11200302d8000e00c6420307210440102c0100681d90b01950030441d11141c2d00070700c000d52003500c40e0800c100f0f0341c50201310750318103c2c82620900c61548800d04140c2e00d1740564000d040e0091070500002c02064601d8200e0300301c59010b4180090259103d1002c60f0400000300c9007040417440e22100205d803810014842035000f80c030191010403400d450358650f030001c000c1a00300f81c1004111b4588c201800000d200b140c81c5586500070040a411040c45e0000e140682403050004074400390001071580c4d4041c1c0900320310150002c2c607028040d03090100b20402500310140c04e0303420700800d02030031450340c0f214480c850207001c00400441d107440c1c0a2030120880c034640c1d00a0050403030310805008140d101d86003400103503501114801c2c1d5550a0700c0c0480c0e01ba0142c08600381103507080c41814641003000f58020301c18000365a405018458440c1c0c03e1080583c0006005640c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 857813812 1250 857812562 857812583
    0x140d030212040b250809120306100e03280b070e0a030605100b2805120105150c0618070b041208090109031a061c02090406090302030d0c03090b070c 65
    0x2000b800c034156014002c80c03104400390380340c0000d55004d008207882d070070302246a413401d00c5500c035410084450100004010f45103507142c07090102d001e010881040006000c1c2c1b000400030f1540e014401e03503916080c0d4802e888082242e0309d010a800c40072100702038506240d0000800c0c04c4510806e001401c20201400004644d803a60352007030010103005149112200c10b0840205071000d0b05070041c40c500c0924040c4071040b00156400c010b0004107060742c0f00074032408210030019243c0900441d41100e504407030780c503c424041d18082d00305104040440740f05002c5d00003000b098003031044150300880103c1044889042e107400300d2145500c194018010048044418034000039450000ad00359000103141220b0019038a540d00f20445629401c907045240180040102318100b00d030304100b0080c920b84500200c02d0300340e004210105800361014080d25100c3d919401494000c004403111201c22032000c03c01080340d02c1d0b0050040c004500103c943ca24400040741600b440b80c26811a0720350000004130 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 857815062 1250 857813812 857813821
    0x41409010e06131b0203030103140705010c062004061d03120906091801060908010c03051b03060d0813061b030503070f0c0b0103080307111b040f060305030304140d030212 75
    0x1030302c00700030355080503d40c1c8580c591500e011607a0910720920165800540e100d5040d46012100007150106001c425442801c0810450703030320030344d0440305607000840015545000025001903015901149460201c0003800013000da41c008890310041240341c407040341950410b410182c5540043c00300442444080c0540e1324607251140082a10307200041c07140c2d4a032680c2c2e8034a4040c1500036405200410441c0104206011080c011030444001c2450f0801082c5409000201c0400c20b00007148845040400040c40a884a02c1c81400c1560031003942611222401c401c003621011714011000041d10001601542e141d42440d030202040d81900c80074190780d9010344c2100c1020fa411880d008200b464003507680031030495003d26018500422001d640e03443c01e4900603188415040465056a012a80450b11702c41e001041440c404c1d0215000324070b407248500c40c07001410b82508003410901000041c4820810b050304051201048603069480300104004150100c3c0142482010b940c5620b60005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 857816312 1250 857815062 857815069
    0x3061009030b01051306030203010e010e190308071d03120c070e040b1f0e090715050a0815120708070302090c0f070f031106040b0f0105031b060307050f0c03041409010e06 75
    0x48840017002c42c0015041c1c0c1ea94001909403880045080582d9640742c403082480c0c4800e128001481c80305055000c5282419500101101002400352040203a4500d0031154040309440c001c21030400201203035400c4041c024885907e5001c2100b00515224188000a0004c0d070076070441c1c401d980202c007054040da0b460031040c460065034400e50030012490100401c0940458034118094200c0b00700800d051400d150f1070311603102c03401d400d2406210041c01780514407944003403400c0e4460b6403000500c030001141d2011030140c0e100d1003103004660142042c0441da01c0400100a070031070b8002c4a6441841c0c03103111480d050780c8203514216100e85070401c807900c0402d441d050525201c2d4803a103442200c001469507045c2c1469401e0303400322060640c107018800c6001e035604107607002d040120050001400c0e04281110851090001e07031340520b001000040985001d642034a85290704c04101d29610080340d100700d600e9600600a2264050182d4003c10940c1411035800341a24924889080140c5a00d0f040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 857817562 1250 857816312 857816329
    0x10203030a020c0102220509071130041716050d1407050d0b04060c181e080a050d020f030a0e060d060f06020d021903020a08070804090203010b03061009030b0105 71
    0x443c0b2813507408104204c11808001c41521082c0c4184201c2e40020341007804000351501c001d0144030802040011000c1ca54402080708220785025085c4042051040da030840000b41011540502d8081d0114001618060700c01d0003c3c2c0c240030342d8054589a908000384030781c00070b1150007090b40200041d640c2900042c3e914480c046002480022105025a510000b446080750401c0480e0090b40d035100f848104503260084651789043c0d0300302001451090303424a41148460310440c10503034040060400b114220600700006030050b802940c5410100d070500c982ea45e02c200c03400b50300510841207032250302c0c5030200c240c41180c1c4441e505d403070030b4024920030004260040e000c0e107500d5907520325002480200c1880001d00030b14070ba030060440000b1b400400ba040c90402d4841f0704102c1da8102606000a901060400c410340d80702000d41d8841c100c50500d9540350041350040c0039190301c00000410556140d0003d0742c841d200859011817040f80004048921080d20f1000130280ea40d413600500403847e10b443c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 857818812 1250 857817562 857817577
    0x90d05030904050a0b041424210303100803040501050a08090316060609150f06030e03070c0602010527100b2202070204060b0a090612060e1501120b010203030a02 71
    0xc4a0908000c07100260450300261105036140c0d44d20001e0b1062410580070710302d401490000301e0300551030403001d40400c00d0250541201030104800c43e00c15140e6404003079072168000840560240308120741201d680340d00503240c03600d032a401031100085d015400404c840561344180c3d5441e0400d00b40c0170059421040c05042d41c0500e01051188c082c680510000140742d040c0604000300e141c40ca0440383c10b0459900c0c407150300c8201e50604040c0461444603002c202103034180d2400044000070707005003604500030482c0042880c40300140004040f5170541100c1e0080410211501c4054801600c25500304042c2c002d804a0350071101c0d900c0e41072100d59005500b41c503005844900209605a802c0c8610082c6040c02000503034040350403800e40c1054400c01d400340003d04400380c64810187d4000c0c240c03900c1c910a42003003140b048105c03c50310805400950041460400750709e03403400d007215810f240781d04c41400c0c00d002603420b10440001c445140581c0d40d1144040e005103155446090062000e5445044e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 857820062 1250 857818812 857818823
    0xe0103050604060305100524010c020d1119030b15030c011805040207050106140f180403050f041814070f08100305060108100c03150608060409020a090c08011703090d 73
    0x503c000701013802408a545001c0100b00000f50b180780c4921403480440e520f0b1452100c4400850310303140c192360003443e000c41603601112043e00c0481c60f45480c022010b14050310982080e1002c0d20100802c45e000203280907070344a960042c00c56580c4840e03d4045072800c114480e8140e0000700d0020780355014400c1c0f600d5848079400b483c01c82585a8010034280d0740450000c6569030343d290810418246001550382e28000111070030421880030800091460001c40d4480c442075070700c4008202014012811030310a0b8100104090300c03036607107460f511a1101c0c510310b52080c030790404102d00006002080824800e11050301c46030101903552030115030002005040d100480b001c1107020000c0f890405c600d070700800c4050020a0300e05260302d0701c0c800381d03180316428200b454102030b500e0b40920946c01a15040c0c850f64038000f46503603070701000903001c0d01501c0f0b00070750450503103c004100a41c003a0003100724001513484603245640d0300c00000c4841b603000e815084182c0c0080c08000e0142c83d10342c900614050081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 857821312 1250 857820062 857820071
    0x120201051605180d120203210103031e030605100905090601111c050f04091e020403030801050d02040f24080a0b011e0807080307061a03060a0f14010308040503011b0e0103050604 78
    0x1071707507404001240445440d0160b800401c43e40341e100c1d16003048190742a000107444820b5451940d0280869600340c080e400f00340b80b8034110385402c1d0710035403201000b010010803c1c240c0840300580a019040c1c0f601446019481f10300c00610a540141c66101d211040080101100710404040e250441440e00400042000c20010503004032038100c05032018000d00140040ca461048450080b65030b4540d03e0840054014842000420742081c1c1c9541182d50641c0d03988070a0f80c0c00d100082c01083d10f41c0e03d200600e8a000080500700541691039a00426403500f540f41312a280d5000c196511943d04004041e018480d005004495424103c1c2406002d20781501e0903003500c49009034103058454201d1b40c1da950010810506104450161400c15100c811483d1442c801d6140401c0d2910b40080250408948038040407007407040543c4500d00000010705040c1c081d5840e0300d000a1260b20912034175110390b003840c9410145c110200c1d000b02807030b42540c171980d07260105100198060000200740f168069030781c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 857822562 1250 857821312 857821339
    0x806040b0919050906133002071502070e0a0c0e03030408060901150302010807080402031002040803030907060912141f0219030b0310050910020712020105160518 71
    0x401c041d0a000e000d41c640c040901c1c1100b481d8981c2101c1d401050301405070321410610404d40b56440000d000103811800300840c3c40343da01c4025480080b080f21070a1054440c030040340010b640820700380251601903c2050100c444600101d03034410650280c4034842c4900004039400d91000d40c0045060350090905055401103040000d0658200c1d03801801c141d0865410410100020f1240d400e50f8446d0700c40718031510342941c000811100b40106003800303100e0044003042c2503603401c0102c20407035900c40c0001c3d0355803030b03c2e030b07034555140d400960701034007588581c44012449a0281d00714030240e800310080002855100c3d11034810b03003a507450960185001c1ca41415540d0b11100d80880a007142904000d13a44044904564002c40e101c03969000070986031000940c0301da900817400e01d11001030013001050a0303c600c410076060000010031514118400200581080000c520f07414142c949074000300146c6d511829004800403140000e000000c00400089071044046410f40d603001101501240f0f02210 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 857823812 1250 857822562 857822569
    0x130902040e04030905041413111e2403270321060315060409050304150207150512160c020307060504090b04060b250b0712060b190806040b 61
    0x6034211070800203412080105158200800e0701c0200019035082101d901c03800020506404c024160740c101c455003017008010702c07422002c0c50384414401410020042c68500c80384040c8079038861241c4c09050120001d50740310354001c000242e404401031110f0720790340c1c5180c10303441021038000840800303001c0301d210102842030800c05001d581c0c8070f0340301442c4011320300b901c0300c0d00c0f01000421b441e1113684080708984031030720070001040d0080340a450100300240f981c60110f04500454019001e441501201d01c00301d20b9001801c2c81c00c071081118008028000c803041140c081c030540c0d07651644140640c020a040900703d21401d001140700340340c02400107030f85500003424021954004000a000400d003400a812640318404130300d20201e40c2080744c5071030301d045c600703150184c407401120b0214000c0c544e031040c0c1c0040009103c01603101103003491a140541029080301c4408401040b076030b14000d00400d03015010300840d03041344502c0e070644d01c0101d498041100e030303101e004041c0c071740240d2030f24030404182c0c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 857825062 1250 857823812 857823817
    0x602030a060e010503010903090329040c030201110a0506191b110c01030c0c060b0409020d080c1e030909040303150909110a0506030a0f090f0b04141f02130902 70
    0x4810902085091501c0c502c00d82c0058103800c250f00c40d9160a690800080e00712440303030200c0f0380c001c0304000400c162032015021303569980b082110418400080104005002c0b02c17400545c2c0c401d1b2604d510101091162030399034280c00d200180342e60f212101090506941034000469450300a8000c035a070b8066003044a1034610500b103020108000e541103030501e46084c41002d040303000c02c0c603041010050080e80140100c200340c0f0050700b0b00f40c2ea03001202c00ba1301c07103070040116250058140441041c0380d1a052055a101c64a64502d40c01072a2400d4102102d0354054001c0d41004001035040c44600d00401652030f00280046049c591b6416002c42c200401c880e68400614132004005071206960030241c100003000c815580c896010f02c0b0050001e0381d200c8003a0b80c4c00101120000030070b0340391900190300034078184801078681c05c569010001040903420030b103445541b141c0c0910942080606070070742e46490b0002e00c4403410b811103800d0300381041705074041d160780b850b07000448049030fa99014140c22039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 857826312 1250 857825062 857825071
    0x16050604090b06090d11090c0c100504050a170706110f0f090a0807120303062108071e080301140f0f0103090f08070f05060c0307020705040c21020307030b010302090306150d060203 79
    0x1c01b8002850054035001445551020a000a6603d460b041c2003950380c84480c18180d00c0581c5a65401040c00c0c40300400034602c40d0b9520221070014103071150344105654102c0082143c0305410170f041002c246184400380d83c1c00052541c41503050000d100c0c56600e0a4100301c000c0c27500640740f01c3c00005c80b80e904022180c0100080c019503282001a030400800340e5020703030885000b0a00c0c000089640618078071200e041035801014060311100a881c000490190b0914051102d182e40c1c0300040500070400c1c01581210405103440342c12200031802c0c0b0400000038126554002250b4881c800b4950081d00035000243c406c54082a0031000355450030741e00d81200c0019582402e25140721020010200250b54000040c2c07012181945443c400082da681c0745800344a00641d01c03502041c00c6640202401125014100c91008100740300c3e4017000c0094008071141c600107820b0442c41403955000b27100f252011500a4003400c1c0c82e5884d040e0000070500044c480c10381100003000380e500422880d10183d40074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 857827562 1250 857826312 857826323
    0x6091806070f0f05032511030a091706280b06030a02180d11060f09040234031e05041e0509010f0815101e0816050604090b06090d 57
    0x1410a10b07900103100507203c012200500070100f051016043d400c00d10395a0780c06150343c1005108181004c11a5100ca064414105e00e21000c02e201d000540c01580380c80035035400d41600101103c04001c0c05540b20004d40d030501ca01240c0b803804488080800080c0d09110700400310218a07080c100f00032440d00e40c002c039003402c040b41c0d000c10400c0007100c1441400c850780b241121800d80314210303610b0340c100d070801a2110307510501c1c0025940724007441020540380d0300301c4010001c545444080024010b0300d04041d82015091003000e241e0140b00318804448002690544d0f111042c900164040801c00d006041c1c45c01d0034000300740400907400072010000c01441950b030b250880c0007403801c4184200600186c1150b060340094007000d20810b1400a400c1e0b51040d090100c00002c1c9d180c0707108103c50310381c0340c0e0008400d030f0001da041d400c400306030003148000321001e68044814480c001c010081d4500d40c039010b801e90000d0100010040102190408046024001c0c281d914021003440060079500c00400101c98 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 857828812 1250 857827562 857827577
    0x320030f072c04020310020711090106050a030e01021914070602030c251203090f0c080102040f090207022107092a0305220f0c060201022205090609180607 68
    0x2081c2c03007060080810303000c0c2c000b0861a0070326900107501c0b84280d00d005c0680d02c0e8045620418011284841c42d45040c015011680658581c8001030003507124074014000300341407100c28074001c44140b00315445220310070a103490100c00040d00701d914034840021215480d00500804001c207203070b1710065000d481d10074126651016400d90f81c03410810103003600f00098129240c0d640100e0120460009620700070b140000d41ca100526000b00003000502c4058220904544082420401540148142d8490a01b50700341260341c1c0e00030390168450902d000390041600d907407000c442c802c0320700d143d03400740c40060950701c415803140141c40480c1c04008111002c65456000260b0f21340fa4120351500042c030074501070109190a00840200c01e860380e4024240c1d14580617014140051182404442c90f0b100b20110f43c0c0075501c2c04000c1c041d4100a0b02c40b601e20242c107080a10714010701c2c403ca01114030141c507120302c5540300e10400c804074100500082e42845c01d2f14001c810180140481442820b242c0c44810 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 857830062 1250 857828812 857828849
    0x11070b0a0207290406050906120424110405041e050406020717030601090b090307080f07050a1e0e0a09060c020d091e090504020d1e110a0320030f07 65
    0x1404040c0c0e5280c8400240f00300b4600b001c01000402c1101c0644040d03050441c0c0d1042104042501d1307104007445080702440fa03405110404c010014040320320042c606006056121107180c2100f00c5261000d401c00005042200300600c6c145504544140d4043d0707104000e85001c982440b400f03030f51045604035001a17000401c4030070000c0401241d8141c0c046076a2036070540c40c0c03400028050891a019118a42c2c0002c150200a641c00700108c0d03000c0d00f041c00642c0c2c620106500301a40e20304480c01003920030542c075072000c2040450b810b040b015000c1003451300307207c0c28900380a04141c2c0030060301360101c8545030031955000c9a01e502540310004855802440040071245008100b1003c0c0e404c120881d01c640380d400d202d60780320340c03501d0003d41c0c40100700013030f403500c0700d00c0001e2142003454001404103c07440c0f0241d110303210046941c01d50714054050204071074410020449030200e1408020075070102c0510b024210bda4020061900c1d5401404403040001c07000d400c941741c036125501c16400308ac510b10800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 857831312 1250 857830062 857830079
    0x1101030c030b0607021509030d0e2e0f0c2111210c010204091e06050603131e020402030921040807061b02090f01030501050906150111070b0a0207 64
    0x50450600c945402c00009028500041035803213251800380c8181007010745141c90484070f500322000c4880c01800c403021520440c0d40035017000c80d4004001d10a8800c00101000d5803c110500b042a0030b01c01200f005c018980b00c02030395001d2016055008004084100390009a5a0240340100d0380c01c4055902c032544d140c4a004080100d100d6501e81035421210201038290840d442024949043c0004652942403080321140240130390390110780d00a06068003120100d0030b090a17400c3c4c50214902c24401148c5a40912034103110075120ba521080d40d040f40103000ca6554100005503404110700001c614420350005001c0c0d030400e48000c2e0803900000420080701c50400c044000c11290103c110742424905841c16443c0c40e400d100d00800c0c0840c1a40f00790000384540544c1c920705030300a0407541281410644000054400d0004403550f6180c0b038040741e40740000040b09442144005c800b01140c0c3c03803034401161460700d0380709420568401c80c18041481c0480c140a0701c60250154000c1800c02d00d0a07400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 857832562 1250 857831312 857831321
    0xa030905010e0a080a26010f150503071b02042405010906020a0c17190609030f0e0d030e0d0c08010b030705060304080a0c0f120207063902030f060103110103 69
    0xb19a4540c04411200d000524401c255851500b40d8140f88400400c1104031074002c0803881006208110395200116803090700310640c0080d01c0c0c8181c0e10084815542c807040d656480150392100129100440c1e07411405161401c07001c0e200e1018102080f894510080030007c0c6403550002e1103612401e141c144070030750344080360500818041c80240241071407500c84070078110290140c0581d1040303025450a02100420131250f09103600c4144101c0c0f0041c40c00c0260040850b05404c80c00642c08107280e0381864490324800100000080414681078001c0d5021740340030201d8041c007908284030a0110f004250215114401015034030004204001b1403070401d0b08020303160300414401c5a060080c000800c0d01101a20102d18003410100a002c81301d080500420511a1004049070800103040d49009e5001c00c0080494481d0f848581000402110200c2e02c807140c0c2d240189100409087e1480d65000c405d1b070926400d0000c1c041d02e200d000c46e14a05401e02100340c10583c0c01803440a403007509560725204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 857833812 1250 857832562 857832581
    0x30d0201060b0d050402031f0606020106060905010f030c02190506041a0f0103300f02010b030106051003050a020c06040804061b120e01020f0105010f170604082a030a03090501 77
    0x1c104031420901490b4490150552600d01559504001011500d04000d00404822001525854807103100701032009003a283c040c03003005500740713440056024016030500c3c0903a003058503102150b5a008200300c00401e8030405480442c4908031815561021103034030603c40310b02500141000c0e2611f41820070100000100c80c8500c40d01c5101004110a502c81070b45054aa1004c0c40310200100508924040d6000385183e4180301b040002085565400410880102d1501e4009001ca040a18201801c8aa5900c61303550405407000d500d8070341500c00e41c000c0707602c5814040700500b0045e045400303a2500a048a0803101500c2c0000c0900010f90403220003143e04090000c140c1107602955545682140d80302541010300942e15990280f5a000344050f40c0b0551440008010319a903400707400200201c2d62062644c88169410301444171440851243e11690b00107811a280c850710300311502c030001003441034ac0c0c0c4580c980030814105107070910003000180301543c1e0100300b80e142400e00c02c1c2110554503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 857835062 1250 857833812 857833817
    0x100501080f0a092a290912010b060307050307020613080d200f040f0f0b1e0705010c0806130908180109080307050c0414060d020f030c03190b100602031c0204050d0c0302030d 76
    0x2090000102c0300000c07201d1958003611100071000c954147d65000d004912085503020b0b2000c0304024460b64000003440c401d01d059400c0784c0e51358941243c02c1c04030855400b40540490000c20032402d150f00d0031340200307100c4803650002010f000c4048a001341d141d0001d0792507082003c03002504001c003a00090000c03000c0e0403901d2040041034a03010b01d16205100b6041c000d500c010707500a80c5100c0d0315000c0d042d501c8442d0441c00034004081e10b60801807001c602110254841c000c6000e00c2c00f034071001e0340b0810300e40300d9002c0741e10b40c640440700c210313a0208601201102e0400070f1011010400074014009000e49500c200000c0c040324803010304004c00c0c0ca446da0200b00c0c0464003102040184d54514610703082064054811071440030203003010904010705040c0c22a010f200e07003e02811442002c01c190045540681c00c080b81c070303460b80c81103800b2000c1c040c820000140d00510030805144288a0000b90548040e03000500c1d0a5441d004603280b514546401c0da90351615480400c10342c1000c2c0684610703000b030351 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 857836312 1250 857835062 857835119
    0x501050a15060906230c0703150903090e0402030304080f01020307031b0f0e131a03060a090201020a1704210201021c021b1504030b100501080f0a092a 66
    0x7000380750f1926442910f040204100b06500c0c0c0248007450340621030303110441c2a594280f11a00c2543c2c8084522007124000501a19800000d20f00c1c030035201010741c1555007202091510340c0080031851f018100f40d906000410001800040402145110584000015880e4500910040d04443c5221004044d4016148001c01000e0703020250030442102c0c1c0c203000410183c2c01c008104d00f041d0703d001210300c0a1401b405080300a40308543c041d5407400c00c4080700c10943d513040030202030302c00c401c40c000e0159100415900000b000f40c0d00039080390b1260696203007400c0e07454000090072445032014515440300760003010107650303050008480540e52a0207402e9800a01c4c0c400a44e121090b00180344c6030f80c080f5480c42c0e03080e40c0c0e001e01c100c290a65040a591625100d08000c4c0030400c06844512407031514110010365540208252441586003c0384001180d8a80d11414060602408c2c04c43d220b82010303144019051101b043c8540c25980e03403445030030007401c1c80004081c0c0c4ad0016000154041c0c1c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 857837562 1250 857836312 857836319
    0x1c180b0306010507061823010b0a050607150e01020a2706090b0703050f03070e1f09140102160b030711010b0a090c120c0c060506120a081b0a0501050a15 67
    0x200f011a0384007a440000003555000c2a0001c1485580c0c40100508103564100345420743c15602c40d175064480301e010300030008500c5a404115000c119441215003101d400c1c4039460109500b40282c0b00c01441018000c2000c54050952030308a071301483caa500455181e200c0790320b1104460003000c01d21845a00700229903800c1044c041c1003600e0030b1003540c91700000040c015040510580a456402202c0c000150300c07400c0c0914045c11600080074150300902413420191401d45052011805001e100c0e10f07071035052070500c1150080703020070301011410342c4221001e100c041d602c02d042e100010650040d15075184e003410310008024a800000400c5203a0405021032296074581041030120740c1140b00001e0219070102040c0e030200002d118003624035142c098141030b4a0f810140002500e88200c03030800440e602d540821a46603091b404100040d0300041c0d013000050b0b0420010005043c804842d801583c1190407544d01d02800c0500850303d5035101d10a01403006824000c000220b82480e1110000a04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 857838812 1250 857837562 857837567
    0x70b0f040c1d060f0f0a140103150303140702010c0f030e03010c1d13060b03070903060c141204060e0f160e0c1920010b011205010f090207051c180b030601 68
    0x78042e544113032030720303200c0b800d0641d80e0a0403e03a428001030402080b081c2d40d81c12a001090030210f925010074105000e8809828121a102c400e036075054944a400c0314001c25002026003284038100e052001601c0e408011929030581880d007071344241d503071445428a500625003540d5810007504140850342000d00e14070300f43d626003502d0400302580d03071038111906906100c0151030a50b11070458000d0003c24800240d0380001c100094078016802404210300707c0000300c800741026003072100840018460001c8061521002c190403502030300001ca0580e925826187c200010100c4d60586030344036102c8603041d602c40d060070400504a50216014901e00041107004520844003420048402a200c4504031801380c3d0a80548a01d81c1025806a03000782c107a80c2d0003010901803075804100402650130f000a030501a0078103803500c440d407845105107071001150180d00701480483e003601903542075011004c0c400340751407920904c580d20313183d2403101002540724008090304294043c98042040117082d98 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 857840062 1250 857838812 857838869
    0x30605061903050c0706090b0f130c1806050a0602150c13030209090f0a031215061d030a1502030103020a080f0c011215060f021b030d030504020105070b0f040c 70
    0x484900740801c030f42e50b030302c0c1da890b445114440d40141490700e020041c000340240c40c04a0b6108000e4011032900589444111070401d00c1c2c01c0700c0041a1032000c490900803490342841c0309150b100c281c00c020441d15100c100041c8032504036003110006134030180f610554040328940e9a80c00c000a000303070a10301076a522480002c2c060602001c3e0086e60018089807032682d04008054190300014280c481444e26440c0041281c01c011280e103900e2418a240c00040c07942d515508001c0f10441e882d80b80002ca481c65442d40c40040c0303080b005170305001d031640351340c0800c990407101040255040300043e41e0f581503204000d142d0b03516800c402020307400300078841d002c1000059092040442420101b441c408560b4500025011840b10181c0822000e00006001904406010ba810a0720b03001e50b0038030904c0a040c01c003001c00c1c4d085103580c55441a444104041d002c0e9000640003801817515500d09110394130f800540c1c690640b03c0e544495820740404c0240b10302c070806040901001a075043c0c13100c00c81c089004041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 857841312 1250 857840062 857840107
    0x110111091009210206130801021801020102030f0103120521091207050a0602090604030203011a0109052e0203090306040c1508060d0b10082b050703090e070e04020c0d03060506 77
    0x10f5400e00d2002950f03a080160b03540c5201903410110406d4803003a08078081d40108036a1050b5091081c1070310310ba9030060007524803400ea40411540c0c5a8a151104c90b815041da10802c020b000c410406141c01c05014a20380d4001810444240e44508049082618040c901403100003402018851700002030404070740d0700e2420fa04200050780741c01044001840074496980000d40c1580307442c0e00003c101142501e060b502e24000d803a240c0c0419590380074811202c0045140403142c28101190060f40f1240c0600000c1c2071030b280c41102c2c240ba2095020078508501610140c030711600794003040000c00d90b0091009105080c500e80003200c0d00b0f0070004140f40c4014400014030301030020000131845c07080f0803e84802030009500b00c442d0003d159105010300100b02801c00413012182c41e04010550240c012a8011941a034400d03a05034545a242c151340c40c4007604060400a6584210b01c281e5a6030024005a188810103050040400703200501103a50542c005402017005101c03541031000701444c0346484 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 857842562 1250 857841312 857841359
    0x1805220f1b21060f05011211090702070501110102070b09151e0408070204110a030905010605090717040c0e0106030608010b0111070b1303020904050309030d08090d030903110111091009 81
    0x20b00c103240b404401801d801c04000038554a000d0000031020280c0c458040b01e64002c4032418000120780061081d08601140c841000da40000420411135108407025820148146c0005042850b180c6d03a14101400c182c6038603015610490700540b1400180d0240c940080c582180f400c0c0d004011241645030840051000d081c54401007843c034159102c580240240414110390190707642c9030400c01400410030301a06480a41c64008042400c3c00c04405007030242566440c3c0c0c010200302d40729418030400004004581c0d03d105040005102a0041146400b0703003180d48010a002e410583c0e001e00710b40315441303801d04000701c40407a1010a00b010420302c0075103103514500b942d10b503060714050080305001d40c0025005a180d004100a0200c04030103041113400031000d641441c040e1407000c888500054821026680169a0350b1b074919009178410070545100342885a162a68840550f08441158403003281200c80007a83d41414904404020105041c500701070300582d0030050441d07882c80c15601500740 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 857843812 1250 857842562 857842619
    0x30b060316150f11010c030501300206070f0b040317151807111c0f080408250213090210020a0b0c0306240c0d091805220f1b 55
    0x203244d20036072800c103810000d20020700c005048500002c004060911640108440b207003551410b5041c0c0e4110510007808910000003100907540030440180d004500841d450701481c0e031180d00264118003264403650003602c603d20014200c542503000c080c2d000300111654501c1d00003444155444800107000110910035121541c2c1d50540151106c3d50720011108243c40b4081440580d0400e0408205102d080c0b980c584200030322154090303c900506440003072414200340b019038046044d8ae284000c030400c2305074441004070850b4020070f8410ba8401c1700080700f0f40d294030036081581010015401400c1003480100f83c0075116403903041842401a0121212070320000124540f9600c4034a503540e038003201031012030051030002540015510001d0806a14010799444c010300d103005541072002c07070307551783c05100b01c240c1c0e00c40001c8010032000707002643c00385840500202c260041000380c41414407131a10600c10019509140204242408080c1e102c07180c41c400500003428000042c48600b40c240c000c0742e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 857845062 1250 857843812 857843837
    0x50c091e0301023c0306030304140105070218041106250c1e060f020a020a050126190f05090a030810030b28092604030606030b06031615 60
    0xa0292013a41d280d9070380340c1d083e000d035100001032106101e004213140741c010000c0c41d030000996a4041c003080310540d030700d070b00140020400503100c04055003a0910500d03005192017003607800503a45500200425084444c043c04000800440800b84085e2a900312011403d0100c140311901404035002822402d40800c0112002004251407106001e03059034041d030b03960b0b034418202804100c0f0751881890002440304416000444c00490a00741e00364000d050141c1d030038200001500d280104d00e18521101300320700c220720004080104110b0203170038009107818103c0201c0c020714081d01e440c50f0000300658a0441800202070b00080c44105c40d40c0d060806600350358880501c00d03803985a640c0003900c210400c4042000d200f0300940348403901c8850200d86183c001110425404580303031f5440c014400c291480f03540300382034188a80c0907400400c1080039880d050320b0b81d4907403082c0c0d46964802c6514101c08818820a450207024031405007100c1c00c40440da40303203410381504424005080450500c245c100c0c074007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 857846312 1250 857845062 857845069
    0xf0f1a031b031f09031b020f151b0102041a280912061d150f15130f0b011403130305070b10030512040e010e07050c070305030409050c091e 61
    0xc54040e00f00c10f080c80308188044031070034090036100303008800082520810620b100b000c0150071046540250500008200c1c21061244070032900c446c0161320b40d81400444041c2803038500c556503d9001c0000036895624007119030624403030b400300c0c1c003442180500481105100202007010215401ea08542c0006404075058a40031410f81000040039200403401080c0241c40e000115200780d10004c1d0501c0b5003295480e1901e031f540c5107000442212101000c030f2120ba1a8014141e0483c0300100c500703002004400c000b13a402206036951180813038441038160302421680c4104a40180d081c2040360b80c9030501d2000d00600d1000030204410400420b600c0c0003414898002d0358460350380003160b20700d0341c10b10035082c59110009100803590342c440c0d025450405243c0500355400ca442841d40c81d00180d0074102100d100b0783c4001d005804016050054904003441005040700031f50040c0c0145075928109090340e4241c2d00010f069051f000401c000000240c0c0700c41506d1042059100308d017442180c0c2a0000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 857847562 1250 857846312 857846323
    0x801061b110402190c02030d0504180506040b190f05030c010c0b073b0f060a030902031c090e0703110316090f080c130c0e12010f0f0f1a031b03 63
    0x8135803a0b0190070340d072040c4d203402a81309443d281c02181190001e000340318040300e541c4140e02602c0100504503441d031310310384440c0e00b005401c40f00041c4003092041001d00441ca0102e8842c125880c03401100c0d000b0017840001107400c0010300801e4014000107240000007070301342c0e074490710020503c0d030300b64001500c082d2043c049502d40c448409100b05a030300340d2008038484000c0b410903803803070603030805240d007002e150031051200d10300d901800e182e00304002c920080e001022502da060341c0600541c801864170ba00000040010050b5a0300d0301c200c620f08005900c90340b008002c2451082c1443d288100d10b502440b041644d038490058400320588090081e07003102c441196900034510080480004104500041400a03401c442551040c1900902ca22508203a4a4504030715010940010300c140301400c02d0f0640305901d0064000105407894103007800000c580c00000c0c8050299540c0c0d80c10311000c801c50140c1c1401c141000b01102c040d241c58030000307841d00c207006051601c0d403d081c000401543c80a010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 857848812 1250 857847562 857847577
    0x3040b07111201091707050c04050903070b010e040201121d100501210b0a05040f0f0f0b09150f0604200a09080d05040909020f030a11010801061b110402 67
    0x221a2561041e182000e4001082400148105000d035840b280119051091503150740d0040e0807001017000108100c60b903544010700c19241c40c003800c83e0308a480e41751805104d001c1c01d1440021a03503180541407407035170303150182c01125483d4046814040584ea11050403905840601c1002603010009150070050b20f14103240f800c0b550140c40e043c031003161802e5002074121050b1505881340f5074610741810b40340f802010801401d2580503401300d08040303144c3d805a54030910804030b01702201d00780c0d01e41142007600900b007111440c1040400c00d04004a0b03418407500800c21074000c0200f202c9100b44c1c0c1c408003100605101c008441440004d10503542e071703048050448202c03807c0d1a0307000b20304880f0240d59484944618042948070f080050b034140d0000f00743c80d500d83c0e259035460416003000210300261444c0b01090360b2040c0061b004503a0360fa4107020031002e140c42100440e200c40200c2c400074021900c141d00110501250045030242c03003101400f07102c6050b6001219084048800300003070001d004141 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 857850062 1250 857848812 857848829
    0x9071403100510080f060f150a1403010b0a09051206060121091104180201080403030b2d03060a0c020705190b220902180d14100f06090615110304 64
    0x2602042c00541101300f550103410400b4640f0503603074800060141d1030000f40c4182e40c011245150040542c40701c0000b8120184441c80c2c660751030f081c03c04a101c1300e9042a00004a4104c00007845003119410074090001818140c2d10100100039050b20310380c070f0b214001c3c1128180550149680840240000e489800b081107260401180c021401e0004816a0075016640210314049204030b402005400741000310307034165591004e03070b95240e0701180540340c02c0344141d811403000022010982d003e20a0240b0640c0205056501d0b204441d08051400d0780140003103011a03d46048800301c1640800c4c0d0a0681e0f50075154210000d0f018441c4e64010815a84480024030021400741104034042d1341c48000031050894000480d900e87c10200b04a02c0780e43c00d800e8081250b00d8540c40a030409402c0d00050394000c40801c10001082c00b105410821510140c3c191940e803001d1150290700107100303d90181c0880b220070803005007081e12100310310754822940070501031107076034452500c40f04200301c40203001c03141d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 857851312 1250 857850062 857850079
    0x11010c15060512150408160c030807030201150302100f0e04181a09190f0b150a091808030c04090e031e161106040503150103060b090714031005 63
    0x2800c00041071280540d40c410b9500780f14480d01114005011402a02e4481e10054241c80d01ea0310742040741d020818003555090801188000b09041106c614000c500403404540d40b010240360090844000460a02d4543c4102e01f0900c00b50301d031103584000204840c100345487c0302d15040250340c00d0301e403241c4459001b81081c11010300d01d0100800818107902c201d46103014180884100c9001c154110380441e06d81c2c0c00301014103501255144220540ca02905000c1522503160321144001da1045800d440c2a9442c0d6941c401d09040c801c5842c002801070000c10401c4580c04407110f0400020307800c1c09050b240010000c078900c2481d541c211002030401031810001a2030a4801540340c0c5c01c00d4012040195005000300c4001b81900c3c216002c290b5202d0000c0c5400c80180c0d1100010105405d46a800040c180b00218440d14100014214031400b003a44030050f43c518034196040d25079508105009804a10504c011540c2000c0404200d00700110602c2c4c480d0389030701445c0950b07805540031940c4481c50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 857852562 1250 857851312 857851343
    0x50906041e1703030604050c21070f0f0203190e03160e07050c060720070902030901060803040b03010306090501020909070e190f030807060f0e030c0f070506040311010c 74
    0x2203000e00c4950740394014a45806503542c1040c214144502c02e0056803a0700200700081252800750300890307108544001a0741481050700c02c00c40c402152081c140f200200020510844940040c404000c002a624003581d10072a183c1000b5224001c0f80344103115010001501e410180c016400403a03241409411100c01c1180103540d400f0318001031040e901900000702c046001c031880b84003190100c06c4581c0082400e40c494010481c5ca21441ca07c6101813441c518100300051402442400010304085a002d80c4034104800d6036400c5076125409003845600400c420440407441310180c0e411283c1000c8000345000a90074405d019229000e44168403113544000c00c401d140c0c120360150f120840a0300e0450f0394403099241c204020015028110031250045001c000003074110000f4038125100f4180801c01c0310070840410250343c04140f500805030004a50490140410404850b10303c00031380050040ca850305010031194406d1b4000640000c121455000c0c05134040c000e840d142c26401203003006111078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 857853812 1250 857852562 857852579
    0x9031403092d0a150c0504120212100e0a020f04060807062a0b0f090a03050d0e030d230a05010e061309051f0c02010204050616050a05030a020303070801050316090c05090604 76
    0xc0ba007004c44594580b80b815400c59200740305a506441c1c2481d10010a2070007502006150000750032030307140d644604048000300760361b01d002d012030710b00001004210504151041000c80c02414808600451900200f00400c0f00e0000e0048101c4505041001002d6450202110650050030301c5480310101354845204102c85030a0b003500c14505c00703d440ba02e645850807803e41f0b0361090701024000900c144810140d424680d44814a00420042141c1c50b08844201d12003c1c3c40e4202c4d9210711401101d0b0601c00d0700301220080b140e000c41084401c00c060340c1005000401c0c4000640201d000703854000440b02641e0803a44507491503500101100c3c0141c4800740700c0c0082d1440d440841802508080340d41107402d0050081e03078180d0b2002041c0c5418581c40300036107034400000300001c4c0c81903c41c40c01401d01040c0c051001300100311b600c1c1c2c007569907894110800b51610300d041e88041c0c00303a03114107040075410410804400c00e40e041c9050100b11000b041d40f04460034001c070104503521a400203400240001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 857855062 1250 857853812 857853833
    0x5010f0e0a091814100b032b11190605071112070309091503020109061d09041112160f0302030c011413060201060314030a08220609030309031403092d0a 67
    0x1045c04006000040c4210145030301e408101208682c00c4007620480f1038000c0e050301900c1c1108440b0b1502c40c54103c0500c0311245403c5104816030450341c1e583e000003081c00700b54020194064241e0502411400172038440136940c451740070410303024840202e1500d0405224014a00041100c40000c0c030500340c400c2104140400580300c100d0125450f20000203035030b4001c04100b01e2041c005140b50684801c1e0000f4061380d00e10041c0101ca180c4004201c580b100d654600301c0401140074080108500d200c00801c0701070444240e0080c80c3d240301e00f0b03070342040160fa0015810985002c2032030501405044802c01c0d0480c0d0050140c0280e03107a14401010030f40a078158444011203004e88098020166180031440c1c0300e228100c42100045c10000000f040301c5041518036543c41102c000001d9400c41c0398840f101240d4800b002200040d440300740000a050388038001c0c1041c220164000c1e0300c0c5040c01c00c85a5034030f942c0d490801d42245070b071124090281000000241441004805032031007050796280c180f0004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 857856312 1250 857855062 857855083
    0x1202090408070f020d030f080117071a09120307060e070b030126010501120201180608071803050a2a080318030a021903030908070b04031e020d06020405010f0e0a091814 74
    0x80e123080c0c0005103070b00043c0b6070b002038003c02000ad0b00c0e56500704010190300b401082010300d2075500c1007240300a140c42e0000d0700154010503101464407524180341210565141820780b1840383c0c070510041c0911b100400403241180d0705203002400b07414440a0744c0b4600d00d014900340405500c0c000001078a801d074144c00c1d2034900d01c04d0383d030b0620309031120384140c101c0140c501a00b0001007007600040c41007405001030411810f00500c49a1042c0d0b0390f60b603081e00e0801d40031011102501c01c9001e083d08100c1d980d00c1c07a03103c1c0c0c448124542d44181812400f50b03907802880c1075028540d22041e0385401c55101482042e00c0603802911083e20448024a04e40100140b44800c8000505903000050300c1a40456550191403051021501e05451038860405000301854a2001803450340240700060345c8180099425030b1140d580943c80303501c0c01001529038000c4900c11024170102003090340499035003a480c40c040e203010740c20000b900401540c02c1c207655848034034014150307840881a18032030a00015a04c020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 857857562 1250 857856312 857856317
    0x1b030204080d03050f010b03090312070203040501030b040c1205060a031a06100f0c0303020d11070c0608010503010b0a03060e120d0b1507051c02031c05101202090408070f020d030f 79
    0x1d03002e90200450881d4422908014024284001400921140401035030068140400c8904084c02c0f4040c42d80103010982d4454056130001404000558041c05141880841100c0404c86418000c03001361120442c1e07c00402d08030760f968001a43d41d40c2d407144181c059034105901c2e41c04030120043c0d11528140a442d810321a2900944090006104d40c1501100d090360b44d45800b441e0302641d5055000c0e4020030340358814151203650725152150140090007409025200390100c03d4601000982000c0060304400d020340d0400c038507011a61521a130040c12203600450020311545082580b604041108200c0c00140c000055003840d03058070341d044040d41001c1214103191801c0b2011119165100b0400d00418640044d01118903c0c0210022080c000a050050320301e81404045400a01c803030000c02c195180c0c1d5031740140020501d0550020018050000a042c0c0301c5011703800044a8030b01c010070040a00d0300005101d4100019184044c29156025054608940701803a01a0842c0300101c1c14200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 857858812 1250 857857562 857857573
    0x90b0f18030a080a0c031209080a14031b0f040503030304031713390f060806090402060f0703020106051c0501050f0609061005070803010801061a12010b09041b03020408 74
    0x615141c003180c15062a54024280c500d07145010700b00341d40d080f0f04541e090301403000c11345400c1080815402034001d19449505025980c01c40f0100203008200100046000700ba402d204000c103d880541d4252001940da404c055103600100c81400c0300c921564000a4040c0000300900c010103400003111075855824025003800c0b81d44062420803004a0840e02600c1080400710300c040b24519081000009441c41042c0e10107503100c0f040c80c1302010364035130003101c3c0301003044810000250b220541e250031100844209071641415000a840be00170500083c0c0307484e000081d45410107000350b010400804002c3c00c0b0500c0204100e00310038042c45100c07400d4a042d401c10f0002140d003120f03101e0486c45100024624081c030348640f818807900c05101c05441003030000c02c05c40c400205140c08051030003000c01d6000810340070700b031010a010300326285001101420081c00711071035181d02c1408103070544600501da2510b0f1000c0c400041c01410410344a8200c114011400e8510254980c008205854900b0100e40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 857860062 1250 857858812 857858857
    0xc0f030703050114010f090c0e0d061503030e100e0a091e0504030e0a0b07020a091e052502061e0c0f0c0606010f0507050c040207030314070c032606010f090b0f 70
    0x3412307542c1c684507402c000f80380045665071514001040c04186c901510300003505406408a0283c610f0b050303001900400c601c00c0c01c0703010318504081d8154600360b0616003940a07400c4017011600798002400b03220100f58480051001c0b25003e00c0050441925208c0c00380f0042c100b608001d0b0003400c032000720f240500a40c2d540801e959840c4401c840ca126030142618451924004241000740000750003004840030700b0380b204450020034041c00e40591081400c001840a00c0c851130040d440c10404c682c070a5401030800c120060ae1416904004150b06090301841d03540c8036014144a841a00c1c2040390301440412080c44c01000001c040e44035800c03e80b105c8206094418043c0e40034010f1810040065200201d40c10150600742c0140034180c2c8039013008034121140180d40b022000040725524001181d006210b41415032110044030012044944512078905810f144d20701424001c2c08c10f4140b00c60900400d04081c82006590010f205104147d901c5002d400e0b0366007002d070b10618100745529012142131 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 857861312 1250 857860062 857860079
    0x150c0f030e090a111c0609090308090709050f040b101a0c1203010b071103030d061205010f09080702210d050901110d08041e021909050a0605030c0f030703050114010f 73
    0x1610304001050480c103103445400445c442200d0000d14410785070b126400010448000d0194580a902c261a5000c0030300c0c14030141e0f40391242607030011416609000a110741c0d59a21880d1982282e00082070b480155240005c3c8102c018580d40142c030381715100040001c20401000250000341158800c2d0741400c481d1032080c0300303980020b00808181c12030800c904000500b80841d01e48481101509807400c01442c0c0c4e00768402c0790b0740c90340803e510183c1e801110f03003002028800c02c2100e550340201081280301f0751712400780034000c103040240107036880c07422910b00c044d1110024005ca803848044902200d2a03c0340104917810803200e090114203842c80d0705031101c5002c07032aa28242c1c0c440e645c0001aa131152a941c0440c0800c08c00411280700c0300a40360003503180c02c820301050258034102d11398914541440a003c45a00411803410f0b1031030881e05203c10b43d404200c010025600302c9a942900c1c0b8004002424070043d644000d1447d03203000300098a2422590f999412181160401d404040c0d81e403018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 857862562 1250 857861312 857861321
    0xc030f080103051c1101020703020a05070e010f03020f18040302010606031104051503130c030c15080402130e010b06030a0c0f0f09090f06090c030b041b0207150c0f030e090a 76
    0x2049508000980003c2d050a103810313108003e00c41c5410004503000c28403550890b408030600341d0050300148000d5003446400c00014000344a10514420b02d989044011000c130b4096000007881200c8446046280d540c6003000306280620185c6403050382d061501d0080d000f04814800c40000c00e081100c000d0005403c00251030460710007511400b0300d034080303140c0c100d00d9900041815001b020705000c000c0204030b94299201c040c2d807080c81b150b680320b42060303014540c10b800d40302a84200080c040c00c00005032942d04080e11025110384000c2a04a140c0a2140c058504055143d17000740c004010001500920b80041e0303420002601c60840415503080d04560282035001024007152034030100b0800035032642d01512860180080001e6030648461806090303485181026002a8a1320380210940c03800e446403190641004544801034181c1ca00c002e5100d0300c0c180300c2e4138404403141205030b06042c002c400001006a12110b6001007401501d4090056410014124050400c41c2c000503000c0549204 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 857863812 1250 857862562 857862569
    0x10050f13030e040507020106032312090f090402150c100b0102011514012102180a05150d0b1503040506090601210201020f1605040e0d080615040e070c030f0801 70
    0x80d074004948000040c8005440054002c0085641c5c503230001021590910500b0074001140b03083d040510208000c1d6440c0c1945449100c0310b0500810600c032842e540c600315014a00b4040ea1b4003011f540d218000642548038002c2c404100e0580010000940c01c004505401040744c09030040080c00c80c2c5a004a0899040c0b0100d01610410004240b00040824100030030079041403521003010b0400040c40004d10b5100f191004d80c03140c002c034844814141a80d01c03000c044209803188600e1519110002d84c0d64070103080e800d030050100140301910302541d86c0103426040342c09001e03c010710300c00641510b01544111350554079401280c0100389580008180181255105402c070040502e101c40c078200c43c2244210100c0c10b5114140d4200c09119040c07100d000c008015850183e03140f0325103000e0000b40c440c3e10400080c03680090a626090f5500704402c10340004d0151000f0001d0545002250500d108507003002d0710a010300020040072591100c4029040d0307100390f0f03484412510840060310307081c0b030a00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 857865062 1250 857863812 857863817
    0x120e01020d2403150e010c0c0203300f07050f0c21060604020a050c0105010e070e011403010e04081e0301210b01030b130b090a02010224010909030504030510050f1303 73
    0x9081011413a2000c4008444d864400c00049400000d9130040c05c441800040001141850000c1025468107002481d000c041002000b2685103041104240e0450032001d0403042031070104128500c103071b111083c1c0305126030010445882c0041c51440e03da0340c40001444500c901501c8246071400d14510702c2c000c4074850641c00402c0c20f5152101004080d410851003281042014820144081424007030305009080c000d83c8441d0030304160344000c0980c42c0b294000c3c1d06001c2c42009201e0503071100c50403207045850f610b501c2c4240ea2910300d400711544c810303c2242c00d2070800603038085040b442861700441c100d4203216410250480c4030314160740300d03003195600600404070384401040030a901c100059402a40c0b00c811400103001c507664646661425615400c0503401802c1d86811541c042104004604c8900c15182010906603155440b03084140203071540c890f01d580901e0704050065003643e01031680035041c1c0f500800d0304d4541c40020708045a00400824100c804a842000b1700c074800b1020340c1d01035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 857866312 1250 857865062 857865131
    0x7140a030c0e0613090e0114130c08060f010e100e06011419020a11040204050a210b0702010c02011a010215060a08030301171614090403120e01020d 65
    0x5a054004102005511091050100c0c281246541c0c0d030008180364031682407004540350400400c00120b84045940380043e030b14042c3c3d480300303030b12a00c10095880440d405240d0030750041c5161000540b506984405040e00c5403405105500ca1645011416075150300c07811003c2c1d60301c41d0343c020407003000c0380308485a503410203002c1010780d445a040c1820904040030f40c01e28000307050f404c81d40c600030303950240401600801241000c000c0740c074451000f002000c0704c05606140c1040d0024881d070f1a184a501060040705c10f0742411140212881c40110340c100071291101d19042c134020303021f8410941810015442c205070a1040c0605d00811900e000c8103a0007810105001601c070000f1110141c0b8103039101d4117607800050074660400046000e401c0b000b02007030f0044c41f04401c4074034020480c180010440c100354028003031000600300c03940e0062404c9807a480c503900e490038140d03200481700c2001005c0d1828210500700307140d4150000c002d0f8801c0710700104001945d40941c010340304003482c0c070b520b480180d9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 857867562 1250 857866312 857866327
    0x6160e031501061b08041701050c0f12090a060606030518060708010b0a032a121a0402030402190803091207080616180e01030b06010c030804021201110706140714 71
    0x9001341801c16518030941c64074801a600da0155a03042036202040f049841d4100101400c0300307010705034000300c404154034202030f041419002c0d98058a003614002150361000600c03050001c2281c03188040e0800307820040b09840740303c024082d1030700b1102040010b103034a103030f8000c01a00013241c500c01e00d081e9460092607424544202520340c0402004810961981e100c0610b01c2012502418050700c08100b28028560250018148421184103d440301d49041d0400c2c0080400d4020f01c1c070300c0f0030102c4e40180d0b256200d00c002400c103441400d52100e0201082c0010031004c1c400002801200c800316843d510401d603941c0c4840d594113007800b500c0d2240d0002c0c0041100b0158840d4a618000c080e41442c080d031120304005030b40342e070050344c0c400800114010010001e000352031041c0b07904000c080c0307400c0d0320154264402030f00001d80a000240a44006028440080d02c03e48c4603a0100c8045100c10750f90ba1450308044000d000c0300703505030082d103040401090105024400000e001c0ca0303480059800e0408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 857868812 1250 857867562 857867567
    0x6040e270d020a0b06030f01021b070b040e010b09060d0f06060206091b1c080a03090c12050a03080c0d06090e0d0c150509010f06081005012c0a0e06160e03150106 71
    0xe020940c0505c47d0702c0620300125000e001400701419549080d030001d064a0b440303c0e1903d100c43e0310458000d04104414005074a490243da41503440000720b96a4078202c030f0011450901c40e038503039002c2207403030700000c680741c641241c00000850b41542d01b1a1500c1c0c0312040c1e42c540745d0400080c04940f2a002c10038003140c0d42401078000c2c180101c0d0802240c000c1c01e1a40340c15000b54400300060380045e40d20000e000400a01017940700150080402802400c1c1d02651465a100811203019041c8000140082d0181d05404210781d070a800312001480031300d96442c1c050000e44030a40362002a0b00610f0b0500e0314140c81034000c0c10740c00e03800c00e2085d110308014081c188020300018113502c045540b615512001100f8a003d09030081c1004002400e80b10a4246a44101c5106802c03c00c008401c880d9142150750340b003264910689a205080455500c44091043c000e11030218140f40d14040c1c24100481e034000201481d00d0841c29881c0e00d028525580101600c5040310444013850079102c00040c80180e2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 857870062 1250 857868812 857868833
    0xd020d0e030a0b0c120108060f10060f20012408010209030a12120911101106010b0c01060306090f0209010803090d0f030e130c0215060d06050606040e270d020a 70
    0xc132135456a0b46003000c0c100342552000004d030402030300e81d44084203020044400c000a141c0c4800780c48104480c160500e240144203103001144001004030074080755801c8004100e1190400d48494020488001005102e034910b08000d001e01c003028911803800500f446040c02162400c4200501504000e10f00c0d40d603d903007001d100e01c4d00d58108866501d509043c4200d9108078201c0e071380105084c3c0c9207002094104000c1184901092041020101c0d140f41c1c0d81c440000c0712815244908071040d200c0048440c0c660051116a1003d45543d0420059406100e2101d0380ea0090358000e49158001da0f17244d0503029500d06c034031190b154000d48000a0100411036188250825a00ca803070700c070405128080002d110404071407602000590b603030030708606507070b01044003505d148500c224a20031454050001015508071980290040d030312840095072540d540c104032030150121410700e5034103003041224075000b206604044904550f15100d04198445c002441040d102030b507500601a961036a070b1400b9968 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 857871312 1250 857870062 857870071
    0x20703020306041e060906060509090a02030d11011e0516050403080708090d0b090c011d06070803150a0b090411070f120912050a060c080c040b0c0712050d020d0e030a0b 74
    0x400f403e000711300010746140981c52006000e0380c400f1542c1400d1400700140306901070400301660f071001e81101d005880c00310b000700d22110307907091040141c0c4130609031a0240c4103011043c8120845040d1800b8462960360015025060035003105d14600c20b208000c0c0c0d000c4c4103a0101034150340052046000050304100180305040d00a0001100d0404a60f5103400c9030700140c41481e450f03084500ca40c020740d40e010b4001c01a18660002d014400e0341c0340008102e00e403150000207802c51000000007625a640070b0400740300b0b101c0141c0301450040e52611804c50680003081068410b900742200f0910b544c0102080e10203103a00b0003211078090340c0c195243c980d02114081c50006101c0590341c00142c4c600f0a100d107a10007801800500502c000918028040b240520006414013100700c0a000080704a60144c07011748821000440d070b19805100340924100095101c02c600c21031340c60701d4074104000815010b0182c05503408a8086150010080d250017462546da96010b9000e041210046885200f02e150403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 857872562 1250 857871312 857871353
    0x6030c030c07060b060f0315030303060f090618070c0b24010e120304090f06050402040303080c03070306030f08070605060a030305090607021909020c150f040201080c09040903030b01020d02070302030604 89
    0x44680400405d540384c00c0a903000d41030f038401008010160038040402061050210302a510303500d0500005049804228903150141032400001846922406054900812082c0b0040740c01d1402480042c84070b0380348001140e440b0180d0000c19480d1030103c001c90781c600000c20327890484aa050004407909412800ca007031b40a4207a810300c0980b105c0c10b200034000351417880e10200300001c2400ba41c1040d601c050741301c940254030400040000c02e5020500f10341000311b2009072540c07622020b00440150841d0b0700041d10a5540c260320b40c08106424004040091003008103009540c0d501c0304001001049201c05808610200003200743ca1034018000e0660900c0100b40f0401000c210200407030f040000c0d046602015070024002c42020404c0180c0907125068514920461401054001c210311002d40001d040c020b200c0701088002410b10284d61450341c01810800407030740380d814001c015002400f8a64094081c00c1083c240300c0e4070100d072900c00c8e260081c0007000300e62101d540301c3e04c41d42c4203850a03410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 857873812 1250 857872562 857872571
    0xa0201020d110c07140904080c0f1203071e12020a050f0301080349020c15150a03022409060d0218011106040f050c0d05061506030c030c0706 62
    0x6001081c440d02d900881c0034040e5544541c21460944c2c82d041c11504141034059050b00340144503a91190155030180e4042e03003003500c506808803020710f4548550000c25050043c1d4201d502210b8070314024600c0b4540580d1030203020400350b4414071000341c03213941000004000a986e0a4109015001080580780c107180262814000451160168200383c20400031504001804039242c20a80e800f10304030300c004c43c202c0e05004544400c03007074000c43c070407100c100c40c1e45040e400c051304101c5a030603110340b03212071401d80340c10f141d04056512258000701c0e040d404498120200d2441803c1080007007094990103000d4010110b603043d4001081e07000044085018101046a10601c0d11a60302908952f841c05c940983c60300460134241c10714803a4000003e0401c40c50208000e070342d4100242580d04150400f4012441c512a41002030505030000c00203504002114840c03c100440003a0580c03003540400c0d030403440c001002c002c001d0944030991303c4480104052020558080c051001803240a01c500ea0024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 857875062 1250 857873812 857873827
    0x1e031605030415090e01060e04140a0e0f06070f05090301091208010e0703020f1b0106090501261209010f1b03080601031a090115030b152208070501050a020102 70
    0x10a1444401022149038001180c1000b48282e0521240e0908446050102a040c01c1c9420f6600282c014411441003154004404100351038a901c22049254121104201ca1401c00b040401400182c604001c0e18800d28100c911480c0000c02e02500030342040e0361380b07541d851002c0030498682d009020442d606548e01c013040c10004400400c0c4059615091b1140c0c50347d585059445064088028054010700d80108500900c05510904a4030419440d01d0180642004407102d03d004140035000b00261600d044008117200429034401c1000e0700e0f900070410020301c0032000050711522541ca1402d551002404142a150302032071501c001c1546030714051008407010303210f130700221003609000e07800301d890355052102c4d03540d241c05480c0081801c200968020000500031400d00e16052044e03010031529464100d080c180300f030b0040580d024000388000c050744038a922508503540050f60b00c01901c80c1012045814600c0c02c00d14000b00c4940002400ca5545131a0040d03480b584002100700c2103560801c002d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 857876312 1250 857875062 857875087
    0x30f0e0a050c01020708060601050406050a030b040f021801051c02280e0909031303061a03101a0a030c030b0402060c1902010212040e061e15090414091e03 68
    0x359519000e070000701511020100007900308141c940000c0401d030041c004101036a60000b0459003203503850300d81b0300e54540400108500420748a401d00d94490300385400c211101c45982c015055012014000c050100c10000054640d4801c801c51042d443c14694080004840960701500f5224402e201c400000f0010840701500700003008030100102d4083e610341c490500b8120212a845241100118505070a0801d4040c44030002d2100401103500c603c60315650041c40c00303240042c2c41028080314420065010001d018285140000030702c0e8103011440040c610340690b02c9001c0341c1e0070140c00d03a109429503c3e01c1c4c4084500800517078120000300a4110201c00400c02e00e0781000c010036407039a04440c0c91000a0515692052501d040d440600050101035a044803254000804032100303032000074516540f80c8c1500554081c9a84280300c0c0c4c0c0581c01d0550b036900144079500c4115800c02003c003c442100840010948483c0102e0b40f24140801201e50701203952001c01008a084900f0030300b50080340c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 857877562 1250 857876312 857876323
    0x18090d020106050904080d14130615050102030d0903030608032703060112111c0b0610050306280f0b0d0510231f020703051002041a070c0807061d040516030f0e 70
    0x1075070003009202c51089c0c03d028051260715030301c1840151840006282a000075501d004081035400076569034591007040602a80c000c0c8001e041203400e890301d0385c41a03202c94220104400c171354010030b94030000315400f918020400c0750603104000540d010308502c548599040000b9011125000305a0707120001e0201840a44960303164800c0c10103400601c0c200d000e00004209040e4a401800000d10511141b5507844a4130400c032104044d0600d2000034042861041039140c1d071112a0030260750304041080b204040090000301030342e1400b4889600c41c600d6003228441c5500ca9003070301682e00d840c0b909040c60104054050040010259099210020354000112821300000da001da84121420000c00005000d03071076811040d03203011401c085c5080741e400080340010308803038010f0301c0000794002042042c40e41c10002d0302403401210b20341a1554001341005407500020030b445118011060b0403450140101c511880580b4140394182030b04e605c090b0007034019510a44011611800314a0524000300300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 857878812 1250 857877562 857877571
    0x3050a0908060a1b0320070606030f08030f0907060f080705070c0e060310090210050c0307050708011a04051e1923010e01080d0503060d0218090d020106050904080d14 73
    0x41c00201d00704d1100700d9240f100c4084041c542410300703000e4a5085880101002036003122007103902c507681c01c500d1502c1c00041c1120b400080013102e10203110303000d0140301405540b10303610b210b12040140e103a49555a544d07809911469000500c0d007860502c1c2e183c8644a003640082e140d00b029800d10545541d5008001700640000faa045aa0820001180350800c643d25207100c01d04802c001c03544090f000b00c1d080300c0c014818041888400070343c0d01e812901c208102c0c1c3d299038002c0c1c00d69203400d440f01d5080c4d000e488a075561804000844c40c00c6445072500d8802e2034041e8241c2003c2c902d170741d10b0150100e8440500104024150080c8000c40100c1e1a840d008581da8203e110b00c0341740e03804040d0895108400da06820070810710740d203c8018412210300069180c00040c10f820b000d5160fa44070381c00680b40c0740f003441c80250400c03803806650950780112400c1301d00038103400d015101070b900d01210883c00c844007442110743c040500c102040200700113100403c60b220480a0104610215410b84031b41c0c1603041c0d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 857880062 1250 857878812 857878831
    0xa0608040b0a361b06090b070507031406040309050f090f0726010812070c140a12140f060709030201080a020c010c091d100303081302030f0d0905031903050a090806 72
    0x45400081110a542001000d40e103030004025040c05c0038070040c10643c1500500903144800900034042c04002c00c052001540e101d101100e0014090440940322441035400303c020039014403002c80c0c1860840c107244022600680142455030b1209008001168082c00210512951103581c61480440e080b9a0080151034100a00c040d4540344d1f81030301d01340f44800c20209000050181000142c030919403d801c8414803600c040901d1901c000090709206254030410030042210750705000c01a0801c4144009107400d010388146e0014001c00548840c401c60f0000b00140c20880c05000541c00383ea1881e40003034540100604100d4000c0c051401c4034100e0703495001213540321000f08103d440517003280103c1c80407c295031a02c2e04048200b018003a040703000050601209078001480d20090040300309070b903600107040350b011203004203110751502c2d07601d550f0000185841d400441d444c200003940e0320072080f1a8200f40c6d0784a000b44c800702c4140e00048644001c0003080400080d90324802c0004601038201c26 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 857881312 1250 857880062 857880161
    0x30809091801180b06120303160e0301091202010c0804020307050d1401022209020418020307050c2d0109020d0f020a0f0612060e090703120320090a0608040b0a 70
    0x1401d14205807007005000b644074030b40c0720400d10b4151b4008002e070303034220044004168040074909400d941d1220411105070305507203050610742c02d000041404070b060a5041d00200000d075640403080b40c0c03880086030041e405500c40c03082082103080036000003170404d008154080c03020b0541c5412500f607038400e1810086422104811401c10318003115502c00401840d4011450300307140c1400c40c401240d046082c151803950210000302c406004a084480c0100c440007941d542030b03908884039001054060ba940880e08108480f03030900241445020a0160002e0041c0f10807826070750303580340070641ca9004980140a814002071400e040c808c00101801c542c2e160349400c82814000d080c115031075944580d02c0c0045680c01d00200c02408078404066036042906556103509011040d80602144e070305c3c071a0f00700c50414080e100c62046da009811060402c82c0c5c500c4a017030f0384c0c9600312941001950083e05d81032440d80442c04054403580040d1040c10380c010300c4001d074841040c0f0a074500403003001d04048440c40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 857882562 1250 857881312 857881361
    0x9060f05061c050714011115010905060a0b18040902130504051c0c1101050f0d0221090d030e010f0903030911091509100e090708010507030501030809091801 69
    0x148540342d1254410024a0b0b1910780d0b56124a039443c0b0700c502c10450700e9550a4034103160b9910403128a0704944003842210507400c2581601c49079400d09104114556281001007606858500c0951040720711600c03d1900701600c2141071211416011304441c6e102c0e50b00c1c6e60407001a01c0d20b06403090340e028105800616841d281c2040f5040c07403c004205120308494800e0b440b43c0d141c0004103c0071a40d00665802c01c012004001a2060320a0030010517a2440114000c9041c44258000b400030410b00b6490405224115010006038001a0b941c84da10f900310000ca8400b151181e482002d1102032400003055035003a000041c0e0444900403030507000a903d072840344050118500482442060507140e182c524640503017151400111b00b505240b00c0d120400c046004480700d0040100500f0308001c1000803410f20030038140c0d580e411486000d0f41d5500780000924003034080d203d1a0f0403a0780110301c4a19081102d800c00c001031000402910394540e24421044d4040824071a60300608000350540f04d81c00003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 857883812 1250 857882562 857882569
    0x30c011404020604150e0603101a210408040f120605060d080301060309030509030133060c02042301290405030c0904030212210f070c03080a09060f0506 67
    0x3940300301800c4400003006001c01611558201c0b000c48074803c00301104054504c0b011103014042d240a40c2d44030340044244030051014002c0c82c412a1041500000e600400f13001850300d038068204518143e20f00b5460b1b9002404150101907842807103840c24502d4241c440d110200481000c0d002490b035516608011001c1005074841c40b50442e004443d00d002106403131b41d40119a2005004400c201a25284041c0801d40103d0941341d507100002c00070311041008404245082c1070400c42910b02c5851404031002d8140c05241000039a2050350f101c02101d42c41f40c0078803001e00000000e400d140350719140e601c103087c40745d002c100d400b0381841402c64140365094110580c6d5258060721010102c01c04000800465400040c0c42c410800180c03800340d400c2d50303641420382c1405501070003410560030008034a12a00c0920800848040e0758a52481d0a0f0300c2d4440c0c9081080710450708100880c1500b0720300c402090061b0905580030704150b6001c41c511107542e07900c800b03584143d11441c070400c0d2600d0900c1800d15 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 857885062 1250 857883812 857883821
    0x70618080a0c1401170406020702011b17030c07050312010306240528030305030708070c021c0c092a030207030915140309030304050c010e060a0e0301020903010e030c01 74
    0x94000080011030995100d80300500040d124150800300c0f00b81e2031402c3c82c0d0080c002903007030021403980354050f480c1c17500b44003029600841d0220300246c5000c854000c403100550140504c00e0300800380490b0700c000c0e41000d0540d0350003d841c032107400106012400000d00c00700300801c60307540d605445040c0b5524516020b021340d0040740e001058800d0680100345007001da4078250040b070b481100c100180364058141d81c007071600c0c0b000b408900040f950201009042d0424000c5005500b00d644004160b940c403903048503a5444d000000394030000d4542d0b55a41480208024100b00d0300030040600311640d22001ca402b203802d503980d281c81c40200d01c80716801c02812060700342c0c01441c190400303500d0b00006030b500030190240c2c0d008820310840706449841315244109251a9299011504c142c7e80e4102444059aa9007080302c00715000e02c203180200d030144d40319200b02003030f568020308864103001d1030324000d403041221550001d0701507500317000c52612a682400703052103d038580005145e458074045030302c40c01d40d0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 857886312 1250 857885062 857885069
    0x10e0408490507050904020f040305072603070c060f0e04150905100f0302150d090303052401021f14040b100e1302010c03051b0319081e090f070618 65
    0x1c5140004220b240c42c0c116040710020203003100c0040c1d803940c12500054150107070f90009002407048201c04545680794150964002c80c904100d10041440c00c05490780ea0712980c08001c4c800f03600d5810411019014000b11240c038542410903545103401103012a0032290010200c3c0c00c4140320007010030031440c0d648125504440c07943d50082500b07003088260161001144130080c0610844903440c4c404015400039200c8040805a0600c2514041c0c00c0045c060401620f12030048504155050b400100a81601d0105c03801038003d081c1007143c00c401115090142d64035000d001e51184c805114050b80d540160344654172400000e109070902003004180f415042d003052040a9007030b824005801d103ca014800501d80c2480c0002c050182803078200c505000314481c040785884882010241481c01001400a082036980c0004226009190454800c0c10942d04440c02c01581d5116008154501180d130394449000d204032090f05081241031858050694000000900c41c0400d82800d00c61540010008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 857887562 1250 857886312 857886457
    0x101403010b0a050f060f0a0e0f040509071404020f0705030d0509060f160e0303160203010b01021902042a0e04050115021b01030f020409091a010e0408 66
    0x4030120002c15003603003070360045500c030780c2c1a140d007541e040ea81c031021a200260600407150b241c43c80183c01a0000e40c0c0e0240031882620030751005c0c1400c1c01d041c86018444d56142c80200a068035200307841c0e1a080d034028440780c0050b0200400040070620000505441d40b250004540e114400a04107086800240076000e145d00490240a01c070304281440c907800c101c1503030249100300441b5005813051003000b05901d070107010101c0d81914040c42110b05106680c000c1e00213001c50a41070300126200c4d80e000035150742d0000800307424800360074a039008010003105010001a9106000740d10001e1001c001030020000b04c5c0b05444109030700703144c0103450040001070642d411402100c003003c0d4840c1010388404520311a000608a020f81c032a80140b180d008050600715039540d200c94508010b4455208165030300c40034105000f0b961790612403e641280c0c2c180000080076100d550f511011030b0b020b0304000c1910380c0098131030004011012032940303650501c4a5000c500107046070311500001c0c600608002d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 857888812 1250 857887562 857887571
    0x110d1707032f070308090f1e04050a0209011d13050f1515030c070c1a130b070c0501050d110f0901020f0a120e21010b240405010507020d020910140301 66
    0x44500c0003e0701d40940b64001a03154988007240081240c0c04540701d0803681c01450071251a082c05a4401007440d9031609840601080d903036440340c0c400344d21070b81c0704c40d50019001907201c0c0507085920314008040217004000310544668055110180c48080d0760030860043c800c421b02504900c0c0c090101456202914803260700d0030011103140e21800018507000081400140120400000c3c1040c40d02a06000d606e0000716480c12175801c010340c020885194100007800e0020824001c1c900c16169601c0d841091a62884d0400004441d55003010403c40c4059446e00e0780c00304184c0700c1e1001740c151308030310311121600c6030884c1000914100c40318000031807541040c0700000200304540617a40400e0b007141050030038a00301c0808a105150800300c0076a10704081d5002142000c0c0c1900722000c800300c2106c0000c8201261191210740a83d500c0340d205010004010030000c0754016005859001d00045c038040c4a0300080c0c0200c1c2043c0c3c811143c00c0c1091040103400e00542000722410001d82c40c00382c00800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 857890062 1250 857888812 857888897
    0x20010c26070e010e18190b150406051b010c0c15023406090c05040507081003242301320d0c0305010c080a09110d170703 53
    0x189007140c0c007050b040c10400e502c00c4800740c603160750912030f0120200360000400e030302d401a031200c807151341000d080c5036850408102c02c46a14285401a80c10300f5410105407505107042010784040d40001c1d6010b1505268542c90b024800d0203110780c000341d2103603448450500035140b610b14a4262030041a440300c41c4144035100070822051940003400401090040d4190003030621804c8401000e28020b0080341060041020454602c4000c02180c0c8181d805008a480701d90054848074021a15420385461042003000802c0004c070050b0500c0e00840d90f20141c3d220b000f6143c1c4180d94441c403003104000444d00801c207620341d0035070b0700b140180b1041c1c4c1603a114a56680d007200c4028500301440c00c445841400c041c400e0ba440e58000030503aa40030200031541d650313916006001e030a050006a010941701400180c03200d900d070080c845819032200945800303540c140100480070741135010907541c0403401c2d00c0070840480104000c207149030181e20382c138034090611150341200982000c015030360444e6805005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 857891312 1250 857890062 857890067
    0x120f05090f01020f071e1a0d09030318081206010212040b070812160206060f060d05040302070302091e09031305010507030507080a03020c010e1c20010c2607 69
    0x1596600c00c122540c400407070724000101d14110f02c0c86a06003550062a80019202503074505003254036891580c1030035120b0f40ca80ca11032902e8041008404000703001c020611507001558489107000303209080000c0c0c02d034800b104941c041e0b451850111089200015240107003601842040e5016009200903d8001e544040443c03840c00356206114841401040040c1009020000d0700c604104c1003d5403d038a141410140090b031402540f52005170141101046190a141c0d52507255020013400603890107a15803000c1c030003048001c0082d0110701031400040700581e01c1d02c02280c01407005000040400c03100c40c00300201000042d01405003648104621070f0860302c41c80d15035040381c3c400d0910540354006403c00380c90034030401400030304003400012800d40168165001d440c0190010000700994143c80c06c070159a810745600070384948042c0204107c030710384a02c081d4940741d006170307415110345a03c1c500001e003940c03600e00d1001d000c1800315252640014000c0b915641d82d9117815025242401c01c1c0602 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 857892562 1250 857891312 857891317
    0x3060903170114011d040903030b130c050f0a030f091401060f08060f07020f01060806040c091e0b010c050613030f0207061403070306030803150a0801020903060a020705011413120f05 80
    0x20ba5050004c002e4051034440007000807550b08172000f9105200c0c130b1041d40b40060082070420100d510500c0a050000d80d046814032541c1c0000340f582d00e409240c107040100621b0a074100c600c4801c01c058a81e49485102c01c940d029404c44c9610951000c2c0b071140c0707042c180c2d0342074a1590b0070003502c030080704d10108458030000489540001d001c0301c480c03030300f0f4136003203001c81c1005c1288816408642c24803c00040c01080001c500e40316500940d042911030f62508140c1060302c8000c1e000c000c4024662900f142c06c3d40b480e5010205103001414058030000156403014104042114058102e0406219100030b06d6089201c020030645103202504109007065000752000840c910840400369011000416140c06644040c010315008100319441e490113181640a0199545095001d503801c071400003032840e014001d0740d8101000a0140c54191f841d900108004d401c80941942c0c00d6480300b5948204000c0300d01c8050241002500e0102243c045040100540110040c42810030a180c0d140e02201d03130b4004103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 857893812 1250 857892562 857892599
    0x1203010306091721062e0e0904260a02101a1804061b230708040b0c10151a071b1a0702151c1a040e030406090b0f0f0301030609031701 59
    0x40d030402e981b04840003183d07010502840d0b503801c0055102800240514401e184025456603402601010748020800c6040e004081c00b01000d40e02c0030890f03007203104103900162010303400b491034820342c840005c0014060602d40c042e442075031184401448203004040c0116507040800d0584001200c800c07180080500c1e074101100d80401d222400003c01181d140342c02c80d02116048480e242d00c85455403d5200c047d030007035203144024400e01800b6585402940a0503103505010420a951245014040b48043e942e846407000f0b20801000b141e0009091038613806184505031008101542c14680503842008d1540e40c6500810030034045240181e8400a0003441031f0049842030340c032140c9400c2d0146001580c0004804028145039151244481c1c0c01e80c0401c100104603414052119007403000c41d02c80c803640c0100310000d00044810b001d1135074000c4c020a641079402e0116850400101d25040480e0800c3e08100d0703580c1c1e1103054400906a11040f02c460268001c3c404003859458800c015083c08035504 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 857895062 1250 857893812 857893879
    0x90504020f060c030c0a060606030b01020a05030d020c01060503010e0f06180604021003140f090c120705060c0a05010908090a0806070f03181b03021002120301030609172106 76
    0x400c0d01040f0740c1031051380e0711000d4810032100c0b201860701d80303000a081d107030084a002034507007100201e0303540c1700050701c10b070140e08000914135003441f214031100a58401c20b01070141e9034a138040058180ca0920907910820a01805410094134440f519424aa40600144100094215110025140403840e5904143e04661150302c10014040c2036003d00342885114003e0324195040024020342c3c641c84920030185042924111080030f400c0100c0a420140146044e038002101804103040c40702c0108580d000c04002c0311500000c80d078034039080d9440d0210495020001190811a90421100302e00141000740090011842d080398000e061842d0101160f0415881c0c070070043c0e0105000b420114502d80001161040b20105401406023007038a103c200d02039501059412109440400c0001524403d180e401e40f03140d180d03031201002f42049400540f817810000d0108085203583c02d000b05a5001005c408034040612401d0044543c0701c01440d084c003442401880003001030300310209882017203005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 857896312 1250 857895062 857895067
    0x8010519090c030908030f190c020a02090405030408030d0204080606040e0d0e060903010f1e05010509041407150c1230060305060132090a0e0114160306090504020f06 73
    0x1150110058508070702c0140810b04001b041c07005400c1c00707940341c51143c084006c2e007000c250118545001140c1c1035402000040e000400d01070014a80181e0164116008004480c10141c891440c241980d20407a5003c101c030740d0000c2c04110f480d40c00d10010340d0000c1d040750704014602d07450b020181c5440100381001c040100d17004c0900890760703c1c0c605a030074180300940200000046840220000d26043d0200000c1c202000c80302a20b5203102e0203061b051b0380f0003525107001915241d45416480ca1800401120b9010b03041011803402549922001c04c5078560703984800b140700505003200110043d10301c135010403c4a161302c0d04483d880d081402501c429001800381000a014a1840100a55000140b00340200800020091142c9869925402851951103540244c06d44402401510908a82d0f0407185040009104182e980d0101c070040c649100007184903510b031503804489010850f50789a01480d100d18002e1142c0e4944145009421217810401441c1015000189140c0c08020800d11400c6c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 857897562 1250 857896312 857896331
    0x90c0a0e01031b030917130308030403020f2a0a140f01050c24090106120303050405030c071502150f0c070206040906030b190203070c081e04150801051909 68
    0x7a40c40180a10f0551014188600c04403d004026000181058501d0102c0c80780c4054001c00c010f0072200314482c401000d0708a00c0c0346a81d400441c0d04010410f500750300550706080039a081c1800301d1407110350445044407031061a15060038071800c101000e94002d00450f50103000c03420303880b080c29914034030403114120b692860070012a060300c9581a820300f28040c00d47c1008038012040038648005940c40410355055450400c02400c8030100d100b1032600042074040b160100c2d0103984000d03001401401030b07901e800c514180d020310305952680442d1204081500c8202c0702e581c140a0105003000192054801c1d0422084030403032420060113550304184001100310440d56250308a4006241d5841e05211040d92030800514450b0100d980f0f001884036900f00c940c0140b81482101c0c0700c0c543c3d43d00d517142ca48010340c80c1c90700560040c28110f081001ca00000088580390800030384001d0a207510101240d84051100074003004060384803e024030b07000c00010305d40c54180c5109a0660300c2d100d80000f001c0d00e1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 857898812 1250 857897562 857897567
    0xe041502181903061d0120070f1509050a020906061e0c01060312051c0608101104120f02100903020a030303021305040507050a08090706140d1413050c090c0a0e01 71
    0x15158402890b2500d007449240c01140e4031703001e4a203c80da840c0300030400408110b0219884030b4888407002e1203680708114040010340b1980500e07041c00d0007109048200041c0a0200003161160360060310194800c510280c11444c100b4040c690080c1c05542140c1001c603c005e40c081080c0541d038000049100c0425071520500d0254401001950400c00105442411035006440e5034451b100e010107000240b40c225102419500034001240d503500000c2c545284a000748000034104403480321025030307040100042400d00503174403101e10340c020f040308582d40201d4410044001c002a00c4181845071170322041015903561001c61040301d8041c01d0261359442c540501c0502c600c00c9401c5594030518040500c015a40d01002800c2d003101c0d240c44104054444515243c0c0d58403461041d0400502c214180b032202c081200043d0110b41100c6c0c00c0481e00d03450340d41c00140102d00403201661500c0d0003110920601a0400000080c02003d85a11485042010200c0328521030010070200707100100303000709407591 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 857900062 1250 857898812 857898859
    0x30403020f030c09130b160915020a05071d09060106050901081305070b071a061e0604050402030c1e07020603040b062716020c0a030f0f0c0e04150218 66
    0x10b0780244003000790303c0c5c030090f00c000504907003a00352103040c1034400250344403400c0303c41d642040200d615041c03101c2d03141c0b034440c100010288071113104500440642c580041c0003080560003415420712104010380b1040b05441424500921110041e40282c00401002e40c00108a4040e200b0a1810103900d6803455003901c521810460010800e1151740b200059000e061000307441031a20804140d088100c891039551048041581d02340d03840ba0b2a801c0d8034541c070f2400c40c2c40c12100c040240045091035640c0e80010200e8004a481643c07003040040c03416074609058508070089101c4034010342c288112074000c65034a00005000410307240340800821880c1d56416512071110460f0314854030f207541015220740c8264030966081004010013a0380400040c0049110072054030040c20104840f841e54480300e407902c03811031003070b00c0101c100e42034078011405d01c11a03a0064510008601502e051078684181d200341d40056101d0000e00c140146698100400740b1a20b080a04a65041d803010000c0600840070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 857901312 1250 857900062 857900083
    0x60b040905040822150518090711120a020d0516060f1e0f06080c0d0b1e0106050c070e04030509040903020102210a0c050a09061b1406160e03030403020f03 68
    0x20708814003080c0c042d0700102e504101340d1710424140140d600c80e00740e05071918040d00e207200301c000b24084d40030340c090309180c00b410782d11a00321324240a600444c2c402d01810445503070040718003d040060028103168041080d9583c2c00c3c80b61400500d030521022041001245841d07004024984a815540c400c0c885500301c14225142344110001703104220703203d10300400020201c2e084090500c00e00103004071010581e1003403030704c01030600d94050f06039a988035503005000780014100240050b401d604502c004c10440e02800c42038403002d9403910307040315982c40c1040a60100502c00460030400c00000d9000090341c100c85403daa011400140c61b240590282c01010304540c1204200d00302c000c80162810340450065903002c4041140007103143d4119074905c00c462802d408070780c400f030080000911402d001c4040b0a01c100c48c0d08208443d41da07a0b48440d482c120224001580300d58188034440340c2c11441404650b0503401c003100c4900c4c244010940380d000794400070f032048520048000158a060120345c050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 857902562 1250 857901312 857901337
    0x61713150e01050a060b04081f06030c06170a0c0c110307093902060601050c01060e011d06120c0d06020d1104030312111602031e010e10060b0409050408 67
    0x95101180030036000304400c952601c0d483d17041030320010300c0d1020079084400742c9582001410050703410080c3c0890750036030100188103407a51b0784d0001000c0b401808030b19029003c5130f076503241c1100402520842c010000f0349201881403a008042c401d040e04855455410b5900524242002d108580000c1c10422254000700b2458146400451341101204a00c42031100f407004140d0310382000a01d444201041401136030140c0d0002001c2000c0c1c0d80a440035042201201c00041081521002c040303c1a01d801e0f130010481c501c0d0964440203508003481c030980d0000e02520030043c140d8075840e03619503440700321702c59501421052409800b07008494046514680d2240010300c00110344548010440e070003484290001400d40421248400361b0b401224202030100c407029007008140e0840034141e484a003800c99140c811100780310428800c900c41e800c070140881d40005a10b1202c43c3c10542807980c1000d59121380c1d80307048070601500360306034155800d0710507003000019507654a10b8010410b21405160541c8c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 857903812 1250 857902562 857902571
    0x9031c08010e0402061c0507030c0201140109050c0f07050c010e01020a030e060d1113050324010e06041b09150c020a0b1602060d0b1e0303390a020a06171315 69
    0x12691247d0403040c000e101d5582c0410007400c0310f51080382210013600c0d05c403070128504801088402d00c02e801954010500c0340c10390740b42c80390019a490542d80090b4040f00c4513008400f8201056030400f91640c0041c4080c005008107a940d95001002c1958004844d4800c200100d25080c1c0f284455001050359280e07000307083e07a20900c2c5200b803040321410703206003482031180c0c0030030300c03010310903451484038100003c09131034903c1c0d00f0718140340c07180000205410340045c1d55491146040c9101d080640d010000c41d1902522241800000a214410100808180011031092000603100d08010900b12a41e8940545d00d800c0e401141600e0301e030307078000040c0d8098404034051a64491a600c1800d8928003103c1048510b15003940711060440b480b03040542c980c1050082e080c0ca1060600344510012600b0883c88100400410121041000541d2b01940f51f016608103011401c1030503008001d0001e50400102d5580d4103500410001c0005015200304005080802e00300804a1480000001407034014803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 857905062 1250 857903812 857903857
    0xa150b04090c05042a0507021c060f061410110f06010b0307030b04090804120204060504020301080a0c120b160507020901090e1009020906100c0501020f09031c08010e040206 76
    0x121032200703000d0503202d2840c00c10100101010728450095540d085175103107000c0d102c81a0160307030a0308068000d0760003403480c2100002c4a0a0031072100980e51007207600040868a45e41c03110212815904004c00c940d00c4400e448180f56211400c0c000c44d00c240d45444d8180b2030500c0c1480341480e178000200e1081c1d22402c0e0021601c1d1508101a520501c06503804104a82c103001c00c110a0b9034400c00040d151000802050041464019040f0340a5001520109280d59290b0214080364000d92102045401003460041000382e1000090024001442040d088800c1921082d200240c0504502000d0703204203841c0d00014002d0301503910154005054283d150380d41c41c1030f04040c00660f00c80f8210b50085280480e4161180c0c811303c5103054020b00000c2c50359072040705101d4202c003e00020800d210035090034100050303003400100140f0802c1859076403558188010f03d4540306052820492a00c290070950044561045009044484084645002e61102d00100d1100c3c880e00282c040b03c0112400080e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 857906312 1250 857905062 857905073
    0x2070b070f02031504021c082a060114030115031106030709120503040312050c100b06090d0609020423070e130e010c180803030f06011103120123030a150b0409 70
    0x40d03114a000355120720494100740008003000c7c01180004040c043d0a010b4038104480b07060b4100f2804140c40d48105c00e039503281081e10b14100c001d900c651404a4030705200140c904080c002e01d8455090303504100c0c606815603035420071a00300c0b580c0c4e43c0c0c01074502000190745e140c490704d800c4005101140100039901150305002e5200d80c000c2c003007a82c14488145440340d030303180320344c00700c500711007506001c3c0c12095000c1010b140580805150294401c0d01401315024540e60b201c04008418411440014456031a00c1800203035500900300c0002d0160052584500c0c07101c0c21003856010721189003003000044150001740c1004005108400c42500d030030315040b071a100541c4240e80310a600e45424098500200b1400110341c842c1c00b900381590400d00c003180c13413044903003203446c0c101a050428107109058a8030b0b203407854005401c9892064441001005071004908131031070100e4030024886075040050300030a42e518032040b4000c0a489000c1c19a0307170610301950111001c0e640080c400d1101c01c0803801c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 857907562 1250 857906312 857906353
    0xf021008011517040b1f0b04031401020708121e09010228020304090e070305030f1201091103010e0711010203090304081504032a0c0b042402070b070f0203 68
    0x700c41501c107030b074402d840c10940100500307411500c15843c10803c540e116544c4016411019081d52a42d0f082c29803e0b000400000c0f10311005005580340480d1654135504114400d00840c003005001c0703910401241c2d011a140404440c028050590308001d10f45403514540e54100d0940c0454200c880c1c46018007101c170104fd001401d8034441018004002c1c08880c83d01801a0700322114400513a0082200300415a1150072440c0b12074030b9201552000d580e644c4403141194050402042d09150014026110380a10701c17400340074040740c40c2c0402060404c1804217415200c1800354100309541c5600080da00c0788907913070011003165030340002e41d1039003001d15a1940da9040f9015514140c010031240740d031040304110541c0e2003960035507a0900c50742c0107103600a60345c1c60811120111070b410501c032b82d00801c1080340358100a01a03000140d54880c0f6054400400c20000c4002c1e030b01d800d2340d1040468032694000703480f40c00e07070b50260300d082c0d5a0465890702c2c82d119400701ea0000c0d01401008071100d840005aa04c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 857908812 1250 857907562 857907569
    0x1b120406091a22050703060e07061e1409040b120705040b04020c0705040b0d080a0f080f150906180406020d0b031c080a0b030a0b0402190608060d0f02100801 69
    0x2c0d1442910b0203100302d000c0c0c0d14211a0301c0c00e07402015031600c885490001216503042c2c0030b10242c0304450707102c1c2c4400c010383e8010766030103002d54400d0004100c8940d025010401c8044c14182006022444440c0100506035243c1d06080c4144003103154080c60341d4580c05190b40200c000c010b00c1c820046c3c44503943e1910b031a0310456200d245030000343d903607a0409008032101c403d1010301034041141801304006c000d00e03c90714401e405c00110000c500000e28488c0040c410041c10b6221504039240e041c20040c005040144500c8803000700b403051005440d4094082c0c60202c80888840003590344400114100c00801c02110403a00e0000b0140828405168001e14012244107070502c002800e2030149941c482d919010880b091101d13504400f0719030300c00c0720341d160007650199002c20700c4100034002929204c4600300a451031018001231008614000d00e4848074100781c003013000c0100e0324201c80034080c2400100524091b22400121038100003482d25101d48055005103410706613041d00070001d049140c01d01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 857910062 1250 857908812 857908823
    0xa0c33050a0e090a0e0d03020703020c060d090b1806070e030a0605060121021e34120e0910051e0604030c082815020c0f030c0d08011d1b12040609 64
    0x60607181b03c2ea1207030080f114126010340003003000104100510529912040e20749240c00d580e0050400064686504c13203004108640d0b0300b64aa07442c16040a06090000e0244428404011081c0680352404548030400c1a00400005480e944441c01601c980290000306001c50201030805180444a039020302000710040703030700c607400100e24110307002c0622075511030000c8090801400020020b401807854800a405486150300800942c0c070b9210400c0d9040b10500403030b2543c00d180d801c6081c106105a84075003420229012545010049185284180075241c0294080400300f0324a460315011a80150b80c0150014001c555400a2549840b80d021000080c00c00280b0f0701c00341d031038500c050080710715003040e081455402a40d0246000317501c040000407490240070411006044240050008803000d0350181c00380e02c8501d0b000524905058105191881683c168130541c00182c3c500c40341e01c07030313800c0742e8081d020101d0314180c004502a2210300c408440010040008000c0517800207000c003846030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 857911312 1250 857910062 857910073
    0xd0507050c0303070b1801020f0d0902040b0415050105160c0305071509030c0e0a0f05070525080304030513210209071704021509030a0c33050a0e090a0e 67
    0x5104068403880383d00806080c8030f074000c0c00302d6804c040000d00e003c0c40c6a0f11b2030005203080d0580e402030308650040d0010314001551003481c1c0f0b040d41011301414040550450302041010018110040b14004501031541080703000f213105443c04510340c941240e015042075117100a15564603080f0303928134041c014045600e07501101c81c841a0301030203400741500d502c8107019035600e080a080c40c554507001456901c0c0c158035504050f14402d941d2050502800b00c560380c01e55034009131605007803184111503840400704588102d500c04540e07440241e80c0c1003a4140750041d0b44d4241e801c07181c0c08000d09908500045417000066a0103030f445034043d8500700b482500d050002d0f55490b0010f4815110314240d01c007460040d07100007001443c08070f415210b880340403040503041840d010003080c03400000240890b940402104148146501482018030510358010240842c880c20039503e10406c0c1c11318811000d00801007280c1c1d613000c1c011103107c0f29040010b0032540140c40e1800c2500f0150071105d4408400c2d0282 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 857912562 1250 857911312 857911333
    0x51e16080a0c0b0304050c04110405100909050c0f090f0409140a050105070f0c0f022704060b0402070203030f0708040e07030b0a05040605010906200601080d09060c0c030f060e0d050705 81
    0xf01060341e21458100e0090182c45048a0a00000e816898403100724414100804501d99607500d240c1003100d0283d40da807072401404d000d903400c12243e01501130180b1080c14042e003880d036401c21046035090381e42520240501010600403801804030701c400142400968076018144d124001422210280640002e000300c1c1c0b40c00c24252041c200070040c140010782c9000b1040045081480042000c07440904a242542d802098009003039440e000f59403c102429030a010a0100c0c600400b80d2141c4100c40451824010344c0c000713036030391003903040c8c0d503e0b550008600441400360714815500144200d42b40080b43d4606004010010030a51510900c00d08616001254070309151003803409442c0b06851301000281080c1003941c10a01c2c042c409034060f0980da40c0c2d0008403c051042600030f0030500010030100e02c6692000e40164001d400c5801040b85101075240864401415901100d4000c3c4d40c1805802d0941060300240020b900700990503c1742400355440d05901c00c00a111440c050000e07034a410b0b10707 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 857913669 1107 857912562 857912579
    0x30c0b090717010522050106030f0803040219081f0e0706050307090b031510020f120c1203040f0303020903160f090612051e16080a0c 59
    0x48600c0030050307010b0361104040e24034007030300c0203201524140703200c80f0024000311112407900725601d900d1000e0010130340c000c2c005190814822009220b081c14402074a50065904a0046c89050040038142c50141d0309102559440000b80141890008494003da04101c03054501c41d40c0e25009200c111000b040001c009040302e444440e1603113008000544140b8003039108a459003c00c0042015404081c20300c0c442c8824211070038034008880680807860440b1a9020120364418912000582c1d00600050010440307040c003100c54104020f0103140890005440c014498840e0032000301c0068020340203401c80b2600a0704a030204a80350414148030712490303000302c54004041d20240143d18160040d00042c00c1d8445503164000580e5403055601c500e010301c86003001c0c2925440072400d0800740141e88412a1294500701060303200d0702516115000c914080300c804540001c00030780d441 = true := by decide +kernel

theorem cover : BRFrame.Cov 857733812 857913669 := by
  have h0 := BRFrame.cov_init 857733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 857733812 ≤ n) (h2 : n < 857913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
