-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1382
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:41:37.713992+00:00
-- url     : https://prove2.me/submissions/f53f2924-d6b1-44a4-a22b-36b1d3cbe3bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 248381294 ≤ n < 248561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 248382544 1250 248381294 248381297
    0x28050421121e02011103010b0a1707020309100e010e060a050d0e0601050a050102120a2a050a0506090705011205182407050a1b0201021c08091902090103110102070321 73
    0x30b030101e201d44140150074501c1d680405003403843e40b07010004101039000d401c400302440039002c4408500350070381c400305120f18019000b42d951303414484100101498800c01201c00e2003c040c1420f0f2503a40e001d1814104248255543d6641b214881416101c81c02650004074625060040d000360040003c0740c1e01303040750411340c0c010001a03140c800580c0c40ba51181480040404117010303948400b841010301140416142c00f201400c0305202c110300c80e040c801c1d0042a1410b0303108002200402608000782680f04282c4009440d2003070805000a00b11103080810102050302c46010440222034240301030b500c5034164045401200030504803124403c215100c0418903108680000e0747c0794041d1045850030f109a5035061107442120441e61030030460803c0aa0442c4100448040c802c0f5a410398001e40e20065200c954083c900158850314003061182c0600c4691010409040140c03203501d007242c150307680000d40043c0c0030707418130040340760099651024081e01065900c5187c038540c1a0746206055059 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 248383794 1250 248382544 248382587
    0x3020a0806041205030403030b12062e0504020c031207080403080a0204050105030703150f230409050c2403010b0406170103050304050d020d020406030501022805042112 74
    0x100c90245841d007000300d030040d0141c40302620003500240b2580082d98040d200c0c3c00d000900354985000b0a0504450a4043d0313004d50003281404030100090301031400e0000d003012070560b0320b4140060350044201d04d20519000e19000f14900140301c2041c020b0f20f001d020203260525940c58203a90040181c44c007510141c01248041c404030700f49030840d000322b03008c0c0c407c180c46403403444d10b60000403030043c9151044c950851910300d902144000b040d40c883d1008126105c05401075000f5040000680c5041d824220301c140d20340301108001950118150f003040c102155480b48010002c148110301c070341043c80e2140c0c49440003001040041540c40076106035a03031170b500c0c404555419869481042000c0c04007600d664000e00040050f4039000300107007210352016201286503200d83d0f02040c140d86d00d60300b080328aa50080b4104000400400551900c0301122102a405030000070000d8014840c500400e500680701780a910741c01d031101c0300311018580d400030810844011340c00d030042030030980409080c800f154 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 248385044 1250 248383794 248383799
    0x30d0519020304020d03111507080a0c181205100c050a033b0f070f080c0102030304030804260a030506120d050d0e0106050a03050102091503090d0305040201030f0c030603020a 77
    0xca1003503d1082d40d02501d4800e80c00125142940c7c811510321f20101d140c070900d002c45902800303ca46050081c1c0306500c0c0c980341c1d401c06080d114180c500310001d90080044440002c1502003e510050301120510700185034080040d00300242400c2c4e090490144050074102003200599000000301a800c0b42542e00304030540d66403503060250810b92480e651785d00e80015412011041402c035808041c5610800c0b9050018a20205030410803035902c41c0c415250100c0d03042101c00c0060061040040007440a1071551402d40e402400a100151000d8546012401c000950841b5140013403608600c1001081d00c9407003015008025000445038140a00d05401c1010322012001401080b0b41035281c40ea5030414640f4180ccc44000d0090200b400301c19900c2d160006415140e10300190050350180b0b0000d603542c02c4100c107000903524100e16a85500408000b000312051010504000200091401003a1a165400101c1c082c00c4d01c1415945014030b0500d0b015a0a90141d0010b82100d1090b1130380400030360b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 248386294 1250 248385044 248385091
    0x1514190b12160507140316080c010516080c0a02070906090219030203010503250e07080403021501030c090e01060e01080d03060509090c090907090207081803070f060e0a0305030d05 79
    0x107845010b001c1c08583c080c0030850028403c041c900c144804c400c802c40b410070140c040d0800c202c8014000580b80e040c1c00043d0b410801600703004440d4450100b00c1024508a01a000100f9002c001005401d14a8020865049041c801d2102000038140c9250510090b601d0b07840f150000d621405504030444032075260681304d00c0c00381c001e8a04848005004c5c103d04840061440001606103030700d041010a43d145c04281c00705250601806243c56036940c14061a1030700d03000c0c0c41c2102c1060b10b60182038170f03c1d004100180c074003200d10b0183c841c01003010034032881405695000d0702140d0801900c005007440082502030000030300031186102960f0901c04140d5500074030104010554400303d403900640545500c40c10044005500454100201d5182c140c4d1591028202e0b080308a00711740c182000144d12140046070001400d040760218060065240b84c99940159100c00d4800c100c14410582400c1a071903540e102c041c4015600300050700d5407402c06040700750040c039048900e400c410324034048103480320 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 248387544 1250 248386294 248386321
    0x50c060f06040e0c031e0c030a05010e0615091303050d060603020a0f03020f03040206030408070b190b10120f02090409050109020103151401050f0c030a1806031514190b12 75
    0x210003030080e2102034006c5c00c4060113401c407021402590b10071802864011f840400000719100d029000000c1c03025100c041c29404c11130040d00940440d003050030080002ea0360008415040984202000c2803d06186403e4409001d0b003440064010f1500100140c0c0f50381540060102c202c1030780d580d5a800e1138980054089008010781482681ca01307100140050502c2c03401182c00c035002c1c3c2c40035070030300c140d983c2d410400b0344045401561072004501d40e00001940c43c001e4241c440346c2100d41c43c4028030240401456034001151808485485141d844060240d5604485c0400c00107001846160720344e040440c00707010030202c100d0009260008081045004034031150640d0003004580b07600b200407400450f9030350804a01140c41c100c0800c00100402020400bd04034526180c480320380314080c5040c004907030b6510303620080072b06003005c0280c0d510312a8541e03603400380d6030300c3c02c4124150b6506001040004c2007485154000003040300700464415103080142440b0410f0340031041c584c3c0e0f500c64540510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 248388794 1250 248387544 248387563
    0x1804111002120301140409080a030213060302090310050601030e03070812010b090a03060908120115020c120703032f07090605061204030813020306101d071e050c060f06040e 76
    0xb4204140014004001c080d072280f000d04200034808940580541c82d0440399900480b10710010941c001281d05907209400403000003801c15040841c200760b888000700352038082d20f2039147c003c20382da07400054403603011b80d201c542c5201c003480c1102d894035000d00d00b52201d5400304e00c00781178500800d000020464a071070221103003410040c208c011301c1e910350360394071000e1311181908850241060103c807524810aa03e8a8000c3c590307140c084c207458107043d8002c1d09110100400d140103204d081c521540c2d5400c00100041140d42c18500001d0000741900e0001785800091842c00000e001d47c44100103529000581c00700f520a40c1c40708100d440d99400400000b0f20881017800c0303d4501c007800040c0401c0c05005243e41c05504c00c5d00d40105240c0f154002801e0000445044601820f032004c144984d112071120915000400e4018080f03a061448024040100d4100042c0003103070b040500819007442882900ea600b000ca074201d03207490401d01400c1e074a84030f04403900350183d4a0565607840300140011a0600e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 248390044 1250 248388794 248388823
    0x13140c0f0d0302031909050616210905060901030b0405040501050f09060412050c10110a0e0910120312020408060711011a041a060f09010905090906070e1804111002 72
    0x90a00707640c0505140f19034007071074a030600540d01c86c00645902e0b52001003c000103000140c00c8805402d140002d520010071b861014410340718a85c10740407941007080034040c0c0b8021110381c0c0c0c0742da0f203580040b0b021b045a009155046401c1038288020480150050707400307080901614143e0b0342d1034000c800c2d91060202c2d0060004440308400c4c42080303008400a080d4000c101040c0c4c0e9101c00c1ca0841e00f030550b064800a5020000002840c141c6160302102c0c500c44040203c45c0e585003030801c0010664100f07054003500d0040300a0022078002c15001d29419003813044400707819900c440d03a0f2220f4a40303c803401c88000700480e008030744840100344180f2501400390b01c400e20320901c0250302001d200c001d082080308844000400b5022100325912100074008201304011204e680b1350301e04000500320207290b44054007030150101072000d1b006000c1005640140b840c90050769151103000040c900840e8050b1b011181441c0070140400e0010501000b442080e050b18140b02004468000700c1c1d0300d8407480c14010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 248391294 1250 248390044 248390047
    0xa06020607051812060708040c06020c1302091c05010605270a0902060904060e010f0605040608040f210201050f0c090f091306020412030f020109021813140c0f0d030203 74
    0x10340b0104200f01ca0010030024101c00b010301c4805500e18036007071040d40e145001c42d41d05403c00003000154903421000d02102d1001d01504076051012803140c481580819806940101c0c0e100515200d92031120022541e0100d8520001800d0501031300a11391409414015046a00b01c0142701c00425140c2000d03d00b4809254141d613074400c0ca4000824468000b280d00c000c0421444015594602860300944130004962106515000711912030300d4890388640c0905c401403004121003504030305126405504001c1c0602c0c86181c0e4540581e00100c214027603014018450080c414181d815481244905030100440b007040e202c0e01c0801f4100d005000720594840054241c484882c10890041600402c0a0303983d0700d407064140e17442c007059800030303080442807410031004c20741416403158058800100700c0c00200f1458002d90041045202008520b40450b41032101250508021021812001e900805003240e010b0035100c0e816100d025060481344204450f14402c0e1492030304030100d01340350364941c0095 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 248392544 1250 248391294 248391307
    0x141f050703140a05090a02031002040f05240a0203070c06050307080f0114010309050102090d050a0506130804050d0f050d030c11060c040e0c12190c0e09010b09040e010612020a0602060705 82
    0x3c05000d0080510442e402500c124130b006032020080200c100407031036000b580f61401d002c80321507507500640c0414440d030302440a102101403c800542c0c010b125000c011a170741e00c9a50b001740c0c07440c4541100141040c4490600043d42c981c4003018500440385640c42061684941d562143c410030300b03004129010010342580202c0d58025030005078070a01c290000f6003000244c0300041c0c880c3c80084400d84154004078200010040e050010945c00328805501036440d20198482c07075068052400707480c2c010b00b00401d0190500003e4014040800d43c00011111000e1685c48010080c10034030740c4060100796031b00160240d01c10007003000d900c25003c04401504040c074094040140d644003500407e02c0000410001443d50307460318140d4403680040244401c8a40102903510480f40c04010103010041c01c01d18140142e60740701a2181124252005180c4903055000090b00400c454000d0021540c80c4c04400180b8080c0c1d40c40d10800203000700e0391050902da40380340503601c41d54100c81e0440082d0080105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 248393794 1250 248392544 248392561
    0xe0402030603012405100f2f0d020f120f03061c02060403120f09080a0f0311030a0e040b090f0408070609140a060c090503031204141f05070314 63
    0xe164819070080010482c07860310b1403101810942c4840350740076000d00c841c1c14085030500c806121170042031450010029900314070001e14054495440d21007282c3c482d44a81403000307604080c103008074901c03001d07642c414801120280d0b0381c1e0700310502c42e1904c2c000ca00d88010000085029100c035841444ca144d4510354405003005001c041c00380380c0e40108100a0040405601c511003d8405548980c12440c0e403c104c80c0405020321051201a20070410403c03403d010f1444045000032406030f00c032032054220b15540c0b1b0700344c0e0a505004080c4400f4400480c0407440550f0020450741c00c0c0c0025502001190f281d1320501010010480b0411580855400810700140d040c0000f02405070160b400018180c056a40303048114040f004c14903030745e81c000b0f04140c060004c0e512500312403840354185007141a00d028046a22401886107180764511440300050500601c5d0b0400c80b566048602034aa40340f40010000c24a005144244259a442c007400114107600134491942d034865421801c0b105581e800c0103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 248395044 1250 248393794 248393797
    0xa030305100801020f0c0c040203130f03210c18030c26070609030605060306060a05010509060717040602060f010b09060a0c0204050703020915161b0e091605040c0e0402 74
    0x70050381d1600012000a036041c00784081d210410a08031a65610b036804a030f500d142240d0000764511551040040c0a1041800b84000c0c1c142c07a8016000b003010f220340d08080c1c80a0380043c0b200303082c28507200c681c40701039405a03004441a00242d240c200400b00c3d19060b052844800d804000c0c150310390040c083c80550310410080c070300401d5941e0280d06c0c0c0c20b0200101800c10441740c0c05200030410903c0700303104210140c0119944240260300803d480d02e4548001032400c4194850513040c440009042a070750f80320907040303d0441e90401c81b400c026011a4a0022266200d0b2080718014010540850110b0b542440c40f54125107180561b5810144000c041101d01c2c3d00c03004881d000d0140030b4214000607240c1d4050144510619200161100d035444103004251041d040060b022110401c070300280004020b20b40e202c40340c2c20414440c001e1219103000d50600c40e40c2c0d00300b40107886058003000350034a400035200f42030403c4450000390080c4e80d48140001d4610203000040851b81d0304080d803800341030503070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 248396294 1250 248395044 248395051
    0x30d05090304080304060207090e03180103150801050c07030e100c11012d0909060e01030b040602090603090c030c0117240a03031e05030c0d0b0406030b070c0c06110a030305 76
    0x401e6a2500340e03180d10f890300d9540658865030240e0098102000428a581b050340b44005800014601d804002c0b851821120041001e081c1819600c1d441001240441d41028001c6d0440070000c00403070400d01a90112600902411000140c980040c010a824510f401400c810b0054564081005013036440c1106c1c1a004840c213410410823212000000e01d41405000c0710101001c143e0588180031f1600038002001500002c1c2e01c0360070107100300103002142d40111b0450ba0055240c120f9501c031440c00b5000391281c0c048456104030080300f40140040301051581c4850301c124201c446d000c440200540305401441d104205031010b0100007030301501494008003c0107002030030036510020b200001003515015400640000b1040d08000f07000400d0265004100c41146c10441c1c154036256002c0c02f02c0d8403c0c10300a40301151505001122510381f17400603406160700107081c20151400d4000145010410707141070b1034080c1d00a100081490240c0c4911000a1013032010300717080c14003920305402400340030303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 248397544 1250 248396294 248396311
    0x5100b160f0819140415030203060a0806010308031812031303020705190302040f06050f0d0819080f070903020306060f0a030804030b07020601170c13021e0a110609030d05 75
    0x10104074000841c40d5008003c014005440c2014640281d140200000f11004030712134003030002c1000380143c2d61084070b14506400d06260141e900c1d698a804a448450142c5c0254080e00c642400403040245a4016600c03d02c0c00f040d5403010f031015040c002c0e0340c0f4580c0300c0030280c80390000c102099a03041d4001d200744209001e40115141165510042003000107a8007180ca00c24610220a04c110310300343c02030003210424000c0034040303e0306040002d0440c1500003403d034800d41513403200d1810440c0d6003060302d103a19800100d982914941c0344024007a038000302c0717401c202c03800900000360041d0700444840702500d0b0054010403840d651403051048803149041c015600c0400c840000000079003200040c8055841041c0f000303054189160f001e4544181a0840381d000701c00b8543c10000700d200000c1014110504403009c0203010340b9450389800900c138403807a150318148004c0f0802c81024218004000e8086c20f5640d1145040c0d107502400c1d1959003e807840b01c60383c0c004201d06010b030695a007005400c46e202 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 248398794 1250 248397544 248397563
    0xb040b0c0f191e0c090605040c0e1503040507030b010b030105040b03010216021201020c07090e0607082203050f0a020a05060a090807080310080f01050103060506010807050a182705100b16 82
    0xb1340f10400e2101c0340e0341c48840001d403511000d00c110b041601900c040c81440d401c100c4090781994000841c4008144000b681d100004400101400000c100807401140c1000011006503120601d41606031b109016241c0a14200303d0f404903203080c1403007110060600d1640941d43c0d07140540c02c004e03d15500310354020a0359024008010321200900c40d000003020794920014403100d51901329402c00100030301c0c003000c3c0320a20082010b011307540c900ca004107403101d0010300c86c0e288040c43c0c10ba03001e00520365615401803000c2091002c19400107041c00889002d0001c4130b0850b0340e2403001c03106a41c21200020700c0041c052040b200000c40000140d900075084a070743d0101d170380d143c1c1811460482c01d24203e141903915080100b0510106225240d0095820700e0140007a2810501c00340c042d10840c0b01d08408c100880140d008114035000b1040b0242000d88003401d4044040c0c1c1c01e2482e0407100506800c80f0500c2c0401041600c00350601c2c4004492280820310b0600b4401100954071020011003a2602c203007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 248400044 1250 248398794 248398853
    0x17091902130e0303010f0905160f0504031a041703010501020a030c0206071a1009020a0e1e0a060203130906210303060e0a050108060901051005190b040b0c0f19 70
    0x506014402c40074402800940e00c941c03501500421185882c0d0010000300c0c58103091004002c090041528250041d0801d10014400384000f02c07074074072907540301804440b1a024452400c20b914004a402a030103080141c40710703080c26510428a10080c8141400360303004c13051240019008140c81c081807400140540c0c03c00c0504d4440c1e100b001d01065219140c0c10003d0100f00c180300d494003074140503154000e0f04500380030404034080c1030119540c41e8544240140540c1041005201108030305801003d002c0c0ea070302c1980c3c1c5002035600d41004580d508210302c607000101d01519540704020131a4026401095151908452003129220540c015820141c8a03180865400d50fa01c6129000e806001000101503142c076407400e09000c4094a0f240c00c990510b418059112400381e0710000b0b48004488039203500440c590714209100781d0754002c070348500313004c035001030380300e5184025100d89040b403426600d94501c45424143c8424200c6105114542001d9103400440c0d94161240820385510f03c081d401c0c0c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 248401294 1250 248400044 248400079
    0x4062007050f12100603051204060c020906030a1502030a2f03070504090c021509010903080103020f0103091b050f060304050706050f0c100c1206030203060c0a14070605060117091902 80
    0x4c1003d40d140d00b407500c5150800801c0010051008880b42445140c1d0805042410050141c03005207000ba10911000300850026139060010f80c035000d03404031184e26a40050000d42c40690401c0740e400011500d00842c01e6600483e04450802d09030030f90f2540d03500b2900d0701445920707580010744200c0c1000780500002c10304201074440c4800f03c844076001002110490071040480c403900070721260b1682d0501078031000090b00041c595054130340c1155103005181000e00101d0060429200107003c017484802441005a58a1003075410340701d0984140c07101c04812401c0c0070491005071030092165010386000c114051089024140442000380e402d440c1c1151318100d1440e1158580080020355910039507541d441ea000a440c40400c52900c40921000e4555000262140001054142441310011b1025242440750911010602c00501201d80310305250803d84020241110480d000c0f070f13002000c0c500d11220640400780b08070981c100402c110582007000a14594072644102d80181000e0b85807003424 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 248402544 1250 248401294 248401303
    0x12020c0a0624030312053111130f0605010201050601050a0c0203160603021c050705040605090316030c0306050705130920030a0e010f0903170709051504062007050f12 73
    0xf1402503032003440624881c54250220755024100c0e003800c8003d4604d56815400f1402c071202460382500405604002c503041010202080b00240c662000e4101c80f000012592540200ba80300100c9000700a1691104016401c0300e00c10742c0c03400c0c040307101804004005441062034042d4a8806070558406056043e4002012415500940080798003c0343c0c00d040c500b80f0400031412007068400902c114206008050000e1156001e180108040002c01c91a0303924108500741021185500b2803a1a680e20f0a1288140641d408100d904600740f001043c111032250013502d80c09022550700754001d40c074040546000701541d68511031280040c403405400040c0081c0903511814145101184e6030420448041c21130745042601001640b601c481c40012030341c0300200c001c01c0c0c100134401d101c040d00d03001c809596880e41030380a1640b08854a155440b95400074000d40200d80c40c070781300d092a080c462a51343c40fa440104910100541c0010010012407030119054196450044c00c104c0202c0748428085090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 248403794 1250 248402544 248402549
    0x90b190e10050609071701051513090209030f010c05090d03020c040903050a02070b0708070303020c0a0c0915060305060d030e0f120d09051206060904111f12020c0a0624 74
    0x1d07039a54200081c0f030501042c190b03401a120310b07080414035215555040105018000d84d4090702101003414031000c4007104559644152011002c0042e40d030b004800003a60041101d54040c0c051000f48603c541e6050240008000031521a94280343c84032040c07060300d5484250aa0031441650007840407500d41e449807001d000d00030b0b50ba1603038400a00e0406850013905512001c00c83d0010400d10005c907a07510143c4103802ea042c81c0169488141c04215442e0000c00301002d010500c07002000141d0040301d501115412200c8020702c0b01140da0761100781c0c01c582046400c250046411110a00085e02c10b43d02e40460036001800800d12300f05c0240400d4071441c4101a0110590003484801015500f110110004080032104078641c40f24005000c0d440e210094031550041c00c8980105007007144000300e1158070a0050301c800ca5011380d1803802d0314030303040785d0071000089080076401c001b0f111442d000312018581c44000525540700280d64217001001d000d0a0900c6003c0c4034042c560300903c500001c03200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 248405044 1250 248403794 248403823
    0x50a05071e0f11060a0512040311060f09060c0304030518130204090f0506060901020a1b030b0408090f19030f02060d020406021b090601090b090a08030408010204090609090b190e 78
    0x89403510f20340420312601c1c110840b44144014008844016400030490b41c2c1d0f0480180000303111344031854250382055130051500c2040c0619000c111803001c01c5442d017072081140c00d04445107070315600750489103031000f0358000c1c000a4080000d940031107542d000240b400305025010341900441c41801d40308170b800c20f0300806401c0791514041006551207020709900b0083c102c0b41c1514151019001030360310040420010178403049004590122000c01d40a0002035810114038415803900380751203c1254064040345100c0c0c118412884090b04009520003030720261017880c1200107003107480c0c45800800101003260310400070004400542c156002400050280340c008101d04508401412410008100f4081c0288545010001c06a0b4482800c400711a14003141c0c0e6035414141c004554410300c035800c140250300c400500060900310540c001d004035142504200062901c5002c802c050b600f0110015001541103008903800b10341e05880c0d549005c1c00c510002646843c941491814181514038821 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 248406294 1250 248405044 248405063
    0x5060f07021215040b0a06030f080a0809210903030c0f0105090d0e0a0b03060d021021020301240215010303020601210c090c020a0215130b0307050a05071e 68
    0x40440c01c28404104200c4400000f0741003488120340c094586000040000d402d0b00c1002012076035114203039200e0700c041e60b0050301608031044a400c105403a0350050b02003000240c1c0102c00649500307804200507a01da40d001c5401004044000303001e02c01a00884122607060000308010240b02c5801c00a1621b01c40210300040346911b40800b80c18100309100c0040002d200ca480c039941c9995813984407090940729404031554480c2c8035030001c565002c9001c400250040b0110900c03580d0036802183c45041813008070380d87c1c1550040c000c01c48007030707000038801d0300c40016641c00010410b00242100c1070b100441c3d84100e4044110b02c44814210601c00e034425000350700038038014410118080c0e041c1480c9141c10181000c82220303036841042030342c401c3c864513248581e0f600e2030a4076a0310a0140d001415002458140540344030795014640341d005407041c920401700b070000083c864074000b00343e030312546403070b1149814102c81e44001d85131070340b107003034111035212914410201401c03000c580742c1100c50062481c0d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 248407544 1250 248406294 248406307
    0x4080d0813050c060a09051e03071211100c0b040b221e110406180c030606021906020f0c0319030203090304090207060e060f0f060915100905060f 64
    0x60604103001d422080a801424080000b09030002002d050802d4140c554940da04c14441046403205465001594405100d405e080d03d240728420090380814400c40075a2021592181c503091a09403400004155000c1040300c2030b10b618000c07882110340e040700e05000501e0f503901d981d065698201220200c8600c0000c00c107000046100403200d8882147c00000c040c1c0408068480b0400c020080258841600b00384900d0303070400840d8080030b0840200603005101035910b400d800b07000400705c4644140349524250005c07444911030302809003114900e4016040390001c0d60b21002d0039045140058501c50703000c1148903020703020319004014810844002d59100d410b501c0c000e0041d044071002810401d030040c010320640810110407034040b15020440140e955003e841c1030030240401d2550940079000300800c0080c071300311025401d4403804608a5807000b0743e036884100441e603401a80c00c4c2e00e11006038074000c0500d04000b07a40c40990141c40c02d200300d40b9580d410000307403030f6409442c04030000d00012509 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 248408794 1250 248407544 248407547
    0x12919020a1406061e040609020d020c150f160e0306040f14060405190c0b070c030b0115051c0e0105090c010914091302011106101a090d03080601030b0604080d 70
    0x1121803030b2900c0d030041c00c5942801c3c800610f48411411010303100712800d6000031000d42e1507910800060202d02c0065469007101e81d441c200a40007107011031040c0c00341104604041c0c0d03403042c0c0d052051500180c0f071031194032810204135504190410754401d0081401c21403119036400c004030781c407451003048581090b00303140c40c02024001034514054403e0b130007007040c0300c0040c201103603000401c10600d03800c1003910074504118400006640c018620201d00062001c1032015040c007003015a4020b0300b0100599903105099031a04116241c1034001078000e10110075540c8000c001e000c7c1a0361000300202d00441045030240c211601035035446842d0384081d005035444d580001e07000c4000c214410500400701d4070030340418000c070001010007840500d1086c000d011603000f5007485943c1507410041751303010301d03107100401c108403164000d1034440c0c554000c141000d148002c00310764000d02e014205e17021030703100356409450054004e451281031540303c65030030311642c0310341003e800240261801049a5078400c0030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 248410044 1250 248408794 248408813
    0x608010504060e010e0601170a0f08030114060c0a03030b040605030115030512040e1902040308030a0501081903120f02041a07060b0a15051c0c0f080f012919020a 71
    0xa120b032031039045c68604401400041480380c11174041c1a0428007500c0d1388003486003010710300440100740968100e60300044c031929602641c180c90507401d9050010b2400400c101260040c08a504220360055038040000303407180e00700e0445031902a00118200c1d84a500203400c0d81c19500d060006070607108020014020f080207070440d0700b000851820b10b42030a02131102c54010f4020820340c50359040032800c1900580e1541214015508801150f40341d0a05548000c0604400c1c81000c29620510035030045203010640c401103042d40c16154413203d9a240c1c101d405c040c0450398292840c13607a00b400005103c81001844c1c81080c50441c402079035418091504400300d030180c000060088120040921100d1641d048405100600d820007546410f4024284e80301400b003007076902c03c10740c00c00c42402e12542d00178201000c0031055469150b442e550f510f0b04110960781c01d00c20b82d042c040c201e918200c40034118407100c1e030084040100540c60481c10501a040e181c0802c2c4044006920007041403043c0200d441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 248411294 1250 248410044 248410061
    0x3060709050a030609210f02071505040e060d050d0f1e0c0f08070c1212030e0613030201020f04240504080a032709020316020105091b0a09060801050406 67
    0x1000c480382410031021500c0d0120360300005192036603c10900d02407211036240e0748480301010711603024032081c43d04024400b00e04c0416840240c4103c84000ca40442440201906502030f607a0b00c60810b4070344030b5041c10048015044c0d0b90031030305207040742d0080b6000317101e4040c180e0704644035010b41d0046844014400706c8442c00ca001003011194900d10342070750155003150f20641000011032031000e00e0a11501e40c0c80342c440018066204004000345440002000c0384100b0f0181c0d200f4a2448680a001d0341514914a1b00c91481d4002400113080e002155055482050203480010b003000f120030301305040c41e40140c00c480e007070000c58141540d0190504480c61840d200e01c3ca0f150b428146022055035071181001001030a001028005a10700c40410240c4848640782e810851641030703503072000f40001d50080d200c160343e00144003e0b28207401d0050044500810401c80101404a10300e014001001031001444d41d100c212082c1c00160602c141c000c000250140400000b62170402e441c0c1882218280e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 248412544 1250 248411294 248411297
    0x28050702120405030607030c1e03271a09070b12062409060912011404030e03010e0c040908040b04030c051009030b18031e07051605090a15050d030806030607 69
    0x80000f8050341d00e002c40c0301030b0000400d05000c1101c540195095036001c003010b203076002c1107050042c0c100380c641d4960032050005042c81c40301c540000c2500450841044066400b40400000e41c114010194845948039803103000c042c2540c014035243c108400d1554480f640c082640070000043c042c2c04d2030010f071307002c140107541e0001f00141c08261058002c0c5000301d0024904c10100482c61032416202c9242d0705c001c50780785500130820085c2c6a4403416881209580607800101d040503010f1a5040c144200b00051451000601d62052040c08100140441c02411101980f061100080d0400d070f010151014501c248120340784a420a024032402550b0b41341e102c1c0030001440d00800203e40c584d1026604401035610700e400d405580c5e20700c2d61440c480c18405035018814501c2140003003601002426040b80700b003069440d44e40c8198403156040c0c03900d00a00d54170510782d00204440100d03640c059420030401c050f0a0303000c00c1d0303940c0000d11225101c0f82e003600400c54007000c0080700d113014808903500402a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 248413794 1250 248412544 248412547
    0xf050f1f0b0901021006060c0b060a060504030b06040f09051e06150103021e040909151b080a111b0d0c122102030c07050d05070213052805070212 64
    0x204000309102100e900c181044000005090041c0782d100b400302406800c00081c06224290791810300a207801445442644e0650703100010500c3c5161030244003044451035918141000c1c150703110138104590240c0101d6005036a19a2095505054001d080c8018061409014142088200c099002c4411050b040300741e0008001c0051131a0846a007155003042031174010780720302c40c0302401501000318002c0c9040a000100340080e0044940d005406100c1c42620745041240319100b0980a40f4900c1e804e0710014400e540350150910f00c074840490340a5900c00c404101c0600000c00f2500a074031006401c40800b0305007141c80d000d02000c01018101618600e04606840050b40701c803034410101504000400c0103640c80701e07845002000c00c80c0c5285100c48401c6542e8280107581d2201c81d4803202084446004900030303040101e0044069604082d005400780f60200b00c000c41c2800105001085806a0751103440f620b1500340708804008001214640005401e00308034001a10b03100ca0301441d40d216050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 248415044 1250 248413794 248413831
    0x120606020f150f070806041508030408070902070c03062c010f0e0f062a03010b0a03060b070804050907050c0d0206010311101e0c0f0804050118140f04020d0f050f 71
    0x80500303e0503804540d900d0901403a45858001501038000e0304c1107542c0c20110a0070100c0d603140c000c002402216070100454480c182d403070a18505038065140098241e4082c9a805c00c0403541c0c40c2c019010b50071851820800e40078071110040740d182403440d103142c0c00782e64070320003d03180c48030522403040381000c0c0d01c0051040000302d01140d0b07130312640101460010b101200c1d034880c00e406a06195a00c2d0400310312003607241e6841c0c4100180c1600b103003003214002424044001121140841180e02c4550884c451518080c2050b044c040300c141e01405200c100901007266800c952021301051007440240d6014001d5540745046c00840d48030403220701c0d03201c2c0180c1c80c0c0100003240c0210403000ca0380d082e038154500b4980c1c2000d00350f40121300100045c00041074a28000c3c00c0102183c010030035a4000d1329200c078218003064400020500764001d0b20803406103c110000240f4001d0500c080245c0024005482c000301c680c10703001a0752071060550005038492003488007a0ba94114241e900045002080c00000d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 248416294 1250 248415044 248415061
    0x70507050d06050f0a0b2116030f0c15080403050703020312040609060e1c1d03030a080f0108010507050d09020a180c020c0411030106110a0b04030503070809010b0a05040b01120606020f15 82
    0x341407070b5040f0549147c000400c02c2001e111060304000c290900080159403802e156182e140510f038200c1e98404001804601c60b4184c200940750480b141e66841117613a10340e81c0a1b01c00e030380719807415800c0d0711041c080520800460310342144524841c0c00007140c296014900304e0144d0314181e0078990075800c42c1002e881c0c00401c10401904546040c503004e0881e98070a911030103000d000d88181c035010f0100085540110b90814440c034043c100812401c60980c0e42c411142c0d0072030f8002d40b03240e800a0340401c00d44440701e00030307040720580c03e0004113081140f1780d68201705012801410b1001d002e80392245103d40300c254050081503034026090703d003440000c91042c40480c0030b01c814010341c0244000348402c81403c520030080d445070705038044155035080c01c0505015120b034000301c03580000285803100040503400d040c050342e240f90300043c1101ea042410807003044054880c0001c13860402400c80724003038074005540140001014103402420802e61404c0007282003101c503446040304003400109200501 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 248417544 1250 248416294 248416309
    0x503010b0d1203110c0f16080a08030601140904061e091401120c090504050c0f01050903102412063c09120207060806180606070507050d06050f0a0b 65
    0x8240526000440303054064003180217009140320314010784901d0039000d00c0084001910b0201e00d03e6031000c11004c17940d4050481e5580d0502d6001002d1074010300209180b540202c058030403143d02d4448850a00e4941d0b408181140d00ca58411800c020824007900d0001498140c0007001d0641071005000340e03000500700b09000d1106203d403080709003019110b1410b103c00128400013a00c0380500038030460134107042c007030341e9108a070844600c0f4a902000864282d0f015004490790000c025000e800103640444200d8001e0014019070500300184412228043c19044c2a840180000b280310130700e80105401d150045800e04907900c1d003929160b22404500d200b550ba00104102c41d90301000e101302804070f40400241c5603007078000300142084801e034422142c010484c107055500030340d03900c403403651524200007605921982c01c4400c5204134010441c40c1c1007070402449200d0107501101c401503034403404901809104202540c100e9074030303c01d01c4a04450015003e401034409401844650000d00004100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 248418794 1250 248417544 248417573
    0x803071106070c091415030607120e07170105012c06010903021807030c0806060a081e09061005010c0b1501090302040f0b0301183f090503010b0d 64
    0x80000c6a10589107a888000311490300340d120b640c2000e9203986180d040090117444d030184040303102600014100d03414042c1c0f07183c0c8945005004105d40c1d25030050a072a0100907501e6a80469199009e04041d44010400382d0020908610240505246d440c051407c540c07068100b07036161100c40d2840d03a1011204a91301140301031205c0271108544902005990101950b84008d4002c05442025495070300d0f20021340f0b02c07a2415132001e0100d05080c0c0300403110f00d4412201c06a00800034052961410301c40d4104680c000300500041c4c0340d8100d0800c803080070b010708a556042a500190400c41d00c83c01010310280188800c0c20303c0d080804465032200310184c80203140d0921a1012031140d82140c0c41503007014001c640241c0100403039588100c0150207000d4180c5468041e42c04c055004880548400804c040550065030001c82c807411070300e002c0895264500c0402d032066002000b18420b492500140c1c40030700007a21424803551802013031500351346008501522a24240241002141240300c10140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 248420044 1250 248418794 248418803
    0x5031f0e0d020606100314041103010506010e1507020109050d05010903110a0b070302030723090f061c050403051c0b0f01081608060d05121206090405150423070504050907080307 78
    0x202c20005c04100c0041c10203020140300300611800788010321541d80c43c0c52082410a400920459884030015901000c40304003041e049001030f60818014070020010b0b104042c414940700c400ba40c0c2c2c1d03d0016403d01e810305000c1d21a659034003007450030107400140c409980c0301181c010b0010849030b911044d440d090010465003c2c1500000018800d504c51066859895086100c210015078500503500180d002180114061310318100040b03150329001c0141c0c0c0c07491210880b003010011f841c040039030203081c0160048050003818840226084020100c02e5455407143c0c5000501120301020001071404180440341446030700c2d000c0c81903412500f161035413040c4c110b040076041d640f03c0034043f030a07041e80d00c800a003150084580381c0c501242440c0060a40f80c8401c6403000c002d0b202da03000c00200d428141d400400300d40c8a040242c00e0b048011041c0d0383d015004e050400c0420000324800350394001d0100c00103009400c004014400f91929205091300300340b1400007002c2c03150400e1f07015a56441211400751 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 248421294 1250 248420044 248420059
    0x1005010815040f110a02071401050903101a090c07030f08150f120102040b0c01060501050a02031c09080f0a27180e030f070311010b060d1505031f0e0d020606 69
    0x3a4021015089561076000e030344081340d501e03504002d00079103645013401400c1410303080c0761032010309611440036105026002006000c59000d000c54180c014043d200c00c8010040321140c04050310ba0741d4202d154800c170a40c50500c1d569509a15005106c056043c00120a122150f801e0010711000d0741c8090180325402c2c0d9103d030521143c1c0c400641e0f0030480402d0b908181d0700009020900003c1400513219209031900244278650701c80d0300544640c040e80f01c0c0040143d0061020788007200444651041c9908004000a02041c481d290324410741e10190441c002040c00040c032100d500d5114000640c10700200441c41d141500170103113100d54012520032030703c4c84108400428128100c2c1d42c40385160380960343c1140e40c1d403580e2005083c207603000900141e0104030000703d03407900f002040c01070402c1214000d00d0140750000c1d0b6005c0c1d10041c1030340e01d807840521507802c20206541d28100844500c10052242c40c60b00807504500e00000d46003031000d56003031600221411f00b1707a00c1d000200c0c0380d00300d1412141d52 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 248422544 1250 248421294 248421311
    0x10b03060d0f02190602060603120f03180d050301050f09040b0a0b03010b0604080a0b0f07080c0c030c010606020709060b0f181912150c0903060c05091305100501081504 74
    0xc214115002c80c02135488072203102107501c4569840320a00480e4000c1e001c0da0313074682d514402c16840c0c03603180e00c2961608104121451450070218029644040b06a981280c40c2030380860f02c0c3d1500201d41c0180001c100700100502c00d034a09815829a600000c881c0d5402c47d1030130350740e000e006540141191501607210450807003a0398080d00221800000580307003946560303880b06041e41d524001041a00e00d21555004039074154010b06190340b140c29243c50740c901d2a103c5103800b4a51746c0c071013a22252180400e211141c0d102400f03000c1c40c80105a164000c2455604040c42ca8044408a500042c80041d08000002030b02a502c1c041e50400300001030074a40c0b0340c2c030f440c1c04240c04050846401d0060f42d5200d01c08902038601520000305a030244013107800d050742e00354800003141c1c207120403240400d902e502c2c104002210358008000240c02c52801d681041051004900d24170716158814805940340c20401c0910801800580e0080c40c00740f07000d40d00750902d42c0e07070004d03400460300c0310500954554010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 248423794 1250 248422544 248422553
    0x503100509130b01061701060c2a06020f0705031009142a1804020904020102031329070305070f0507030210050702010206010801062610050106020703060b0405010b03060d 75
    0x120000c00014240c08030a142c01030003021941c0304030108032480040d040004c5100b41c130414280304903804040c42001241d00b41a4140e0740380303200c00003c4035480e0a00e001c003a18401d10b080740340d000320051005200c00c9400c20502a0074a40c501c00020701c564800c0c0e900300240e0380d0016012041c4900300f04002141501d5081c410240c5070200554a41c51061030f40c102d420000030030309480d1f0780786100d4555050a0f031500c03c00100d020001c0f124282c103603145011901616182034501c0e006441401124507007075190042540300000340d48100d1444c20141000f180d900c2e81da09217040b030782c000c125855280660396a0043c0c50f901441f00090010400c0c5440c3c03500f044410444c0350040c0d600142503184003030152400038840c0c0d00181e401c900500414000083c2000140640c00a590311013101d07802d800206506444a00800a030010300c512074440c0c154046d0709240b01d49406401c4982c0503040701400c43c14050306603000990028003072450035004001540c107060036a0b8002604076500000309005041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 248425044 1250 248423794 248423821
    0x60e06250f0309030c050105030103330c09080c0a24050904090c061b03020601120204060312110d080108060a09050a02040510050f0f030a03110f0313330503 69
    0x20820164100c1c01e038241504114a6000c072481001a000625161001101d11307010a21004004069a412090942075481510708401410254a0300209240801b043c2500c01c101381240c04a02c1d17004051000136410f0101500e0b40c8425680c0301501231900c0641c2042c0205036503140404c0443d40702d0428802c0c0704d04121b50806c10014410f004d4080182000b803c14031140c840c0750049801250010141c12960240b5800c040c0c0580103000c40d80c1ca8a14a420341403d9902d0407a40150303903580c00301c0012224a01d081d00310509075941c01510000d1840a071920081e11852028800c04000400100c040010310b186d10100940340840c083c112440c3c05807804854a400940c894185001c00ca2400c5500039164200d910440c1da0310b00100c1600706000c0010b0003142643c1e01500040350b1827001c00e001d0030250080380041011107200289190b00182190082c101d071195480c9000407c10117603201c02d42045803071044c48520103803940d800604078100e1002060b103000344000400000c2d100203c40c1e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 248426294 1250 248425044 248425117
    0x20a080106080c131806020904110403050303090d020312010b0d0221061e03030405040203060f090a050f060f21030c0d0522120803100513090309060e06 67
    0x50003444066250035803140c0707036040302803494051000c0845003061301e0304900483d0044051442104141006512400c0c080c2d4882960349030403070f07201c2a2020a40d60080000c1c4001d41c09100a140c480c02c2c100c4c050f07030419000e03080d0102194000c0c8500015640c200901c1811030300341c59611540c0d860340c0164440a405021031301e00d901c0b564010404042011440c40d2442040b01300c0d50095010000180b80c9000000480c0c40e9800d68020701040c0240d0505078011504100d009012400d0303240c0e814000340303104e60200c8000300000d132500300744600886c20459640d00300c9800c4509006111280010640d440c0140d880714960f6400010140d941203402d000b1211030020070b000361150140b02e031202401583c843c08400c2040600080224804010816030005a5040c50740d90b0088020310f03225172000742c00203019405015400000007480e0b98941209080c11440c107280442c43d8025810060031054030f41e4000828400c070803107032507255a00d03c1d003140c005c4951030181440850b03513208040c0102c041e91 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 248427544 1250 248426294 248426309
    0x60b0a1202030d032c0a050601060c061107170a1101110c120a0e01050d0204091d19030e0d14030301030b1b09010f030f022101050a060503130b04020a 66
    0x2004003248010140400010160003541150100c0d458580120b04071004098518056a29501100310050503035001c0b943c0038060138111400c10800da221241807000a07800340e40403840c0b544c080d03030030880c03103000d902c906c10404010303141001050385804152130004417501d000f1903000580401040d02486505015400800c001c1003004030085520340c1ca50301690000c001031003000307423030303500b0151620840d182500560b0319860300d000c1d56801520181c00c029220f0701e50b01d0b02031001003880000d620a0703810f070145201c0c200030014521094981880e0141010310080024010102c01094100d10301070150b18060b1250003041c860b9080008020305a09285205400700000010074803840c414203d01801041d0820a095800504100424401ca24050340840c41200050fa00c640c020360140a880d45810b001601d080100419290308030342801c1d0580c02e070501d00006002604203040600d01810103800c000d459030528404140c4199170403040109209918400101103481c0c24000c807006140c1c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 248428794 1250 248427544 248427559
    0x40302060913050c0a023306060d020d020409110703020706110a0506040b150307030b04030305150303030901091106070309051302041809050d050906030a0c030e1504021503040803070507060b 84
    0x54001301394240e212030103600051080300038212103150401c06456805906900c080c00602c4210b0001d031840c20002c05040d07200d281400200f4104540380002c0c0013105103190010390b0755040c90382490444007040f499100500d41406241c00003a00001c0d603105841990070201c0b0f0714421404513518290521000034003071300a0034280030803c0a0912440d001d001041481e000e040c521000b49540c4011622002d4403d40c0d450300482c011900982c41903800001c124080c08403000000c011a1447c1c0c001c0d1529840c1d42e665102c071fa01031010010704402940c0003107030311918214090320010701c4141d4034010f4a2140480c2e01c2318249103142c81e411180140546d81803080c80c0d00e1000c444e600103117076001c2d09581c14041c0e000c2035101d0078421b00031140503400c02406142541c460082c144024142e00100001740b55989020203450f59042001108180e0105801c4c00145445c7c81400500190903200c1c0c2c01442e000d10900000403803c406407540600c192400f552260301d00c0c2000405008551002500800e6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 248430044 1250 248428794 248428801
    0x60f03110a0b03090604030e0612040f120201050603031b070302040903080a1505090f0702070b04150915090302010503100306060e04051506030c120c0310060519060504030206091305 80
    0x12880500a00e2040c00c44401d030300560380b504020128401102d0113501c50700000c00060000307009001e403203c030b10005052581071064014890340c1d40e50045c0c4003955240081c104600800081111104410641303100910282c03d103000807a0387d03030240540c02800003004c503a1151204c0320400c04c0d10f00554000b002400b00c1030300d07414098103010081c2c5641c1815410300c12605411041484a0401c4074400760810825684002c12900c1002000c2c0c003034030071806110400592280890060300290540c244107600c058540c0c1d03000790100a06600c00e0300c4205140368104a0282c201601d0703400c494080c244070340c0d01e59900904090550700c4d500002d003118a014008100e081e01c009203980305601c194200c855070303075803103040000f220021640c590307150780300d82c240044a0a0000d080306100141d4000c6851541d45500040d00f00080c0e0840c965110380c6e01c010400c8580741902c41c00510004800410030300d01e04104005005100c0c43c003010b1301400000508460540b160440102071040c4208200007509 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 248431294 1250 248430044 248430053
    0x311130e100c020d0e0a210b04060c1205010b040306020c03041710450215130e0c0403061104171b06120112020102120a08060a15080a0f060f03 63
    0x7090403007400051082869210b0b03514098490222041c400420106c01549046a065401d68154080c0d000c880d8080c4100800100c46202d1a401280b003481c0c0424030001c007000041c038407000009006601070504c8010441040104100c2e01130726008900547d468916421030383c5544556030114212525030821010752840114100c1003030710310060244000661244004486c4510010070b02d1400d50000c6140010b01d408820300c49640d00c42100e19800c5031144c2c0010718480d80110b41d1444409000840811300e0781f00b0726191000d464855071082c410b05000c52420b01500481c0001070a555540756042a088113070380c242e800505042078403055454550b0b002036142c4822035114003015034400300040b2640751000594100e10b001d100071070b080e6840e148441444804440d0140c0c1580510740700d0070800c0c04030307100410f09008186c41d04003641c1400c10902c040d94203603520100442401d07004110044c0d03805030100c0d030440c0ca002808640d04400030226001000141e101c1d00e1880482c220000c05c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 248432544 1250 248431294 248431301
    0x30b01080706032a02010b03030f030402030f010203040302030d1a0d05010c0314071407080d020f0a020705060f16030e0307090c03150509070c03090509010b030406050601090311130e10 81
    0xd0359038109840106903522002d5007a5954020629403200d60040040040154a00c0c0881221407034800032501d40802c10200e415503220242c5c00400341c400001b0402542820892450000d5801e4001c51940c076054400945900074001c003000699190900800c4150401d800ca081894000344452240c000d149080c500030000c10358680c000c01d05100f280841c03900d03d250490710501c5546c0341c2c0380c0585005020301c0140d900020023203e0104090002000901592029040912127510f0640d9201c92050010780380c45841d50049224440800c24044001d0303040d800e440c1c02c81c6449194000760407031450140d03049810101c090b601445803a100040e100301d590048400d00009488c100705494099150a4008010340219a040b058450100340b4003441500c0d1071540c1c9001c2d14042c44d04684900028032448801e82c000c0c02800004004e200070702c903461280a40042003420881c82240c41d559030345c40f149211540b403a20a0300c14501c40c100e1114070b40c114242c00036802d420346032801a21030030702008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 248433794 1250 248432544 248432549
    0x3030a080a0e01050402130f150305010605090c1e0a1b080a030c050702090f1315051006030e0a11150c0a0c150e0d08071406011419030b040f0507030b01 67
    0x1c9034146245512820818480c1d103000c3c80c1c01038130000300e05014070700b83c20143c0304d050080d600b01780e0f6500300110204a000a1240a5441440086a428a01410060740792030181285440304010000c03208000c000e0a94400300c0f000400d41c441e1611aa408140d4160040b10a0b04d560008564240b0041000700c1d00102020202034404001c201c103150740486090140801c000d40028240000c03a000320036801c48194850034603c102c08000c94140e842001c0017101c180c1100c001c43e15201406038401a0501c0c1e0030103010586010810b48202030b00c1c040c0d480075081c50240001000044150141c2c03200c6d48090382c1505106c402a07030700c000c0c042c1c1d500e5440300644130035900000902c6010401c41180c2410202240c80c036610741c2c0000800100300000d03031081e04001c80715410200602000140d812002551a00e080c1d0041c0015615000300c500b01031184e10b40b4079109070540d061a41c560114010b03014192500088580c480c0d554074540802d582c2805e1300c02a2181c400c002c0e0000801007000b501c9810b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 248435044 1250 248433794 248433811
    0x3180f06190801030b010603180f0203011b090e01060509030a0311161814060a030314090a03060e1b06070b041b0e191808130906060c02010314011d0a02070203030a08 73
    0x3980d0fa47d640d011000c0303401030420044252408210180450080e000703840a1030700060001600c8414400326008441401101601050f984c5000300442100320740e03002c2c0104400e041161034000541c00080c0c94051301680201800307465000c22001420403c5000040c9450a42d82e4503841e442d00740c40c00380e039034210750005e8055052011101c2d030002c2d0400c1c01401064080c0007100454210398080e40c4869900226085c240303800d010547c2c2540d640040341004600800e0005140c0c4103607480c503130410f4610759540c030007000b10120043c09901c4800c1100c146540010b070004071a00c4a2402003c83c04e09554110112014400080f43d0844070b407003514068500b4840c102124021810303c101030315451072001d0100016a01032501240b4040018011b0030f0b8503c0c2e040520907119042c8104955003500200c00054000081d10115601032049107110641c2e1f150300c0d42d0b991b25102140400c0c4000b20602044400a0070108801d4009601a5120564000d0070759031a10581000284012021240007a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 248436294 1250 248435044 248435063
    0x9010b1507060614060f070809030604120305090703053004080f061b03040b040624170303090303010504020a0c0b04050606040b060a1e05040e0c120903180f0619080103 74
    0x19030a031290b04c0c0b100d03551390050031844c14440340000c81e078200c5e00600d9054452003800c00c01c518150790140b01481c8194419516078440c1008800d00078115200101900c80c168000341046c0082000020500c000d0004001115440610701c02d509440b503c540c0300c428440c880218010034130341808180854001058000c50f0b2490b40c4268419081101102c1d18440601080010a0100d0009c0c91000e503c54080c41c00402c91a590005941090958500e5a00d6200e003100042c00802c4110b220b0501307e44c080ca000310f003541860811030303480b0312061065901c1241e00145548103503010341c000340d07240c0e0341044000f1540d10301030428503200c00044408610840c60032a1f04d41d00c41c41d0402c16507909201541c0d030402c0d00d4206801129941c00080312200c140042400300244002000008038899607203100b00b00d44401010300f8401c500340b00585000101d4200307000405002c458000e46900c00c100480344640040c08410203c1e445128101a418543e42010315403954160403080380e6040340c0c820540350 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 248437544 1250 248436294 248436299
    0x2090111160e09071404090f1e03031808090906030c120d030f0e19032a0b0a0603020d0b0c04030c06110c10140f0c010207030f02070e040f020909010b15070606 70
    0x3280c039502c2c14043c45000c0c0303541703040c005e585040c558090320001d4800d03030f000000075040703441e42604103515030801c0c620101290305800400d41d01d0300405030604003141172081c80b4541d80d43c0e1044280521400359000b9a203960000e02c55903010461010340080c0648403110406005407130a03100c82c4510108030201e401c003009070302030b490305102d40e01c0000c202031701a01c801804004489412041e982d03064080207a51040d42d6056104041c000ca070501e613078210040a00b5142c80e0074039110b08018120210300c0d00d0040c3c00c2000d40c40e08460605565441054941c042e6035480b0884040d0080340c1000e071407524501e401240340c40e040ba801010000007a007c41d8280d180c14810040e0741c090b00450100043c030740303112601411001d2801303060b0001d802c0c0c40c032a040214031020b650898004050a070000781510800843c150b070103110440103040b003924038018034681500c814440410281e0000e0203045500d001881d50325083d03100c0400644001c203c1810a070b001c42c000d0b401c0303400c03112041c0c0d03041c3c4c5002c900 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 248438794 1250 248437544 248437561
    0x8070c1e05090a0c02011b020a110402040e0105011202071a07111c050c01110315090a0b030303070f180303020706091e14030a0b0423030306011202090111160e 70
    0x4080860744014540007495072007000f80300c0944015000c8105541d02c0355011030170450503004060100b260b90b80213040e05a420700300520088019030310240200d01c1048140301504a5940d4141525800e0800c880d0f000e2901020000a00c180f22016002e40390b6044074418408200b04c0c00e6014004540d6000c46881d03545501c076031506841142d0051801490000000031805030700504001202e520000540203801400c403040d40e1b00031100540c4c20a5201d4084905103012038440c0d41001e82000c0410040c81c5c0040030a54a11015001c24140a1708804003ca903d20500e00d41d0703855a907503070b04801920703500c0c50065580c65090103608007041c08244045010096500015040d039400481c101402d4038054058a91003c00c0b03010030b401d4080d031030f40b03200071501f8080340500070b9200e000b095001140c420b0b1305085005d01c44180841a400030001e010050b030340681181c0040e054000300585c1c13402803500588183c1c9003010b2030125030080e400b2811013128030a41d84400ca80c1c080d010301c0040e90310b0f07011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 248440044 1250 248438794 248438849
    0x5010b040f1d060411040f0f150f0504180603060c031b2f07031406041e020334030b090c030606010503010b0307090515190905061c020708070c 63
    0x221202c00481540003c076180b4180d0411500c1041c15440107117820f84030440c12034003000725000b40c0c4107204941c40c2009102c98005619402c1d40c805d00e001801299480fa005049102d83c2c458411054020604031005e884558812401950310003401c208066074460080d0140c8196030000b1720340010842d902507454001c443c0c2c07144060010311308009100150b030340e02c203210b48190100c000501c50548048002594504002c120000e41c8008180520342461301001c40c0e0003034100c1c2c4806144440c41c000c0182c4001408011000030b800315111070090803030903942419020000a800380744c4000002040c4601350038894000c005040a580c0d0a003030107418541e64400c107942d02400a1020801007250031042d0703024541001080c42c007580c407143d1391400074034001b00140f0700c1138901400162401070342504203102c145a94450030b1140031240b500c03000802e070b4002e0708941c150402030486420b00580c05070381140e60351540300c0c07142901c4181c241007202d0316039450301624041e046c0108180403d02410030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 248441294 1250 248440044 248440079
    0x90b06090606040504051b0403210f08010510030906051005010806060f0a11030717090907030c1b020609100512070201090506040609061407120c1e0e060d05010b040f 73
    0x1005245058680011710004100041440303104441041c0c2c1d0010603814070000780021400340a960040103045103c10030b07090b0940700104180010000c071550700300d030020909811505d040f02c2202e50604169000d40c080d2a50310002049189440d040019540d850901141aa4420799480a240d80c03020103110142c480c1c0c240e000c1c5000400d00201a01d030344207144400c0000041c0090ba41003010b5a80d45403200403901d4101c2001c1d00000c6251100c2d4104508855072108144c40d0a02c0034081107032000d850107aa00c424000341c12703003031041d10701503440d035900b107903625180600119445210100000c1c030b250408100c3c440c1c00f82c10318000c9400701d44140100a03c4039004000b80c1250344496864034000c2c0a410002c40b00c003500c615082100d4550b00352114400c92668032400880420a4404021218044080e20030f21203400010171030746580c9003030300c600c0d00d01a0a005d0750b8010a1000210386004515952203142d00300800450f008a0b400003804c2142e02d030f80400e00040703480c2e0725104004200007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 248442544 1250 248441294 248441299
    0x80304260c0d0f0f0809010f0302030f060f0a1d01090b01090608070e040b040c030e060a0e0a080304080c030403050c03010f1823032805070804150e060706090b060906 73
    0x3180341c8194600703240c2d207607400d40c490801090800b00540e100b000b0082010002c2c0c46402c000b1604240e1540c10070b801461010351071030114130318608450141100f0001900c02e0b4094403280c1c00303610144e200c2e071020101500500050040348c0f42c0b00b08001c65040f409008100220341880d25140c455401a03410200b620340e82e440399a403698503c00211100c400c403031901e69000340c031041001c080740c686100360700302002c00740e4000c00c0c05090b001c1010b00d008000307004880303854030348852443c848501044503d03205e50311085c0e41c0e42e80e4995060101c0c01d40210f446240f0907020000e400400c03c04009841454180e0a0b0028028030000c04441d9003116141509000202000b540d00c500041255031f142e02104a890100d0301031381045815a459a0088401200401c0b00f42c4039030201200210007402d00ba007414505545040c0d00343e687d09005020318170031300071191494090000750b1801281044902c09000d4180b5480f00e8141c100100904a0260140d030420030100100303216080c2400031500c2503101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 248443794 1250 248442544 248442553
    0x1602150c030703090812040c0f080a030c050a0605090708070902120705070201022d010f110a08150d200301060b1c021309020702030f0606031005040807050708030426 73
    0x1004000802070340018402e6041694600304400000e04c0d0001801c1c082c1ea4200500010b480c0500c0c0141d00d900c0303650403549840300c05043c1044144000035510840070b51500e050b1a500c11a407804074986a6038000003824103060104103d03c541c0001283d0381140c0d042d100b10350130265680030300300403440307024400d492143d2600e0000c3c003101e01a1009203943e03481881290b88840b20f032400500e0000101820541e158001d4940405a007004d003c2d801c0d1040a01d01c0c1080542d03408122181241b160300d0901041c07100b0300380003840803211909585030341c10000d0400c08494465283c0b22040300005414440c6601e09815080420b013414414081503030f02d01c958003490040030f80c5000b080181c5422094401e035400304600d5408401c05030000c4010205203001503200c0c0c546104260405222a000d5980340d4090b4041000c00d030380024488000d201c1c000400500c0342c07a1400d011655100314400034115201e11040002c80ba040000100304441c0781132488903407100080715032100310228441030070a41d4007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 248445044 1250 248443794 248443801
    0x305150d030c05060705040807090608030403060e030f0703050702010801080a1502030901110d4502011e1107060c0305122e060806060903030d0e1e0105160215 70
    0x605014000360240a401c1c102c820084940e00e152410f5821100c40000813401302c0d080150950030800e40c8054500d0b00002d20100f81090800b135624083c0e4417000c0c0c091b580740d242c84160030000b07104540b401c20780900d200c3d5898505060160441d40490401c038006604017000050303038000404c1c2110740d90750040b40c0d05000350504a50074043e400c043c0c290401950303911450f1030040115002000340b40341d40720740031600064a0a0060207000005090030b09410840480d00b0b0000b2103402c440d40511400d080c5103c08281c50004803030101038598441451403001c41c1e0031b0000e1f41c106a182d212000640c045540f81c9440303003411610311096001c003c0206d13900340f048401c204002c10056034401070b844180d402c800001c0281e002d036100b0301c50b094091244205801d00600c0e600c182d0303507580314078181c508610700f40004011907624441c40181007a0995181003400100c04180456441c445204605100311000c1040c660300800068840d03d8184161421071340f09140003140341488009060b411321025507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 248446294 1250 248445044 248445049
    0x6061e090a05090102210a0501080f1f0612060f0c0f020a02060d091a090c010305060a03020108100902132606010509070504050901030818220216050a21030515 70
    0x12014083d22041e54080c016005c00714440508021030404400c084410380c2801002c00c411a8030680095005403c8030100b11058000029000592001c84a500051348541c04601d4020540d40e0044070b6002c01d025205024050b0b1038009034109445840c08008a20746880c0503225003902140403c05600101103010244c6401c0002d4140c0a25100c1c001c01d1442c02581c820101c1c826480c405501d01200d0720038405c072184200034101e04540203013001c1159040190000b44c1402080c4002410015440c0000e040c11240d03000351070040100c03174015034840c1c10040c07155848001c0c500036001c001c400341503024a21404851030210111505015004503401c00e000d200f0b01030720051248040c00010440004c0503200da03d0201c4c0214042c860310360303c0f00c1c1050503502c511b001c0c0c81d007150b220718840144a120b4881d0807052082501c0c500200607a604180c090b405058502c4610203001400b400300d1140602c20303050003120410610003448550021404400d0b001ca54066071884145007074500001c0f00750 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 248447544 1250 248446294 248446301
    0x20a05010e030705060706050403020717030d020f120103080c0d18031b1203050403120e090a0e010e031321110108040311030a020a0308010512150c13060206061e090a 73
    0x207850260a45141507122000f0441d20360004504840c070603030750001c0005169051241101800d40310720550403c40e0341c02125030f5240101c4940d09a000d80c00110340041030070f413000306d0300200300700c03c5500010b41e56810602125003141810314100e00031400c0040189108074844050f0101a18200390700c141981c40720140c241040001800f5100c4d50780d000b05217003800800101e040c41c072960391641d6490640c5444c100e00c02510894030103210355000f05580c0d81d5102650640d000140d1000068070030840c0d01d409000d0086903070300c110703140000075418800d65032000d0000c0988001d00c15012070312140340c3c003115460501000143c504007a641502c2c4079503100740c002a0308540a4901090085c003048a0103003160b000c2c510b2000075a12510740c0d00c2c20590003040c918010b240480b840c41268000095035034403000c46031610901c20740e108000802c030700b01c1c09041d5480a03085100540850b601da0070081d40e245029941d0078400c3e0203d1004c0f2080f0085401856802103003d003070850700b43c80e2404020042c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 248448794 1250 248447544 248447567
    0x1614060318191b091a0d02040b10030e1c0c0b06031f050609160207060c050a0b010803040e060a050a0b07150c02010b010e06030702060403051b191509020a0501 70
    0xa0050b015207007205103203501c0c1e80e2800c0f030180f0421220540d5110800003410101d82c0000051170824044419117000602070714550b10064031282090029480050010b100001a17654491140720b8107070003040e8558006405203084604494034002410b104101a0030307030718811000141d80403884000203200b00e03042030300550045c0c11280d0b0b02131503e4490420782042440d026541e0b0382c800c108111484c1188a103600005a1886080300304d0048800a40b01d0109004039400d104150900ca0104070741001a40d03401c54000507094629619070780c00c2500d980c89840394400c0031007003402051a6240440482c0210f41e4018000c2000c03d29001070711500740c01094040d170b00c00560840207114580140124200301c6429400001c0000c11700340098109250b002c40b42d406074809208003c609034000441d1a0082d800d81010b644890000c0101c003c0447e260141080601800352900195240c49810882083c4190203100811009058540440b00d0526020798004808a010000d650040b0080180c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 248450044 1250 248448794 248448841
    0xa0f030e0618030c0a0b0318030d020a05070c06020616080901240614030105030c040e0a08210708090c010e120a0804030c050a0e1f05090916140603 65
    0x80400300c8000580660403200d0b0190740b04904504480300d5280034441c0d24481c1c04112841c074a028103000e0040c100c2d00004195680c084010621b1001c0f0f450100b0030f6640810105070195620200440d005040e03403c00e41007240c00419980001c00d46600200708a40316411901140c0414000558100c800050203445400176560b0350700f00307240030242a00c642c01c0f00d00852101050a6203040d000510410300d02c4c0b144d490520090006100f1a50003081030142c085003124040b40203000520340c50300340105014010321600b0005204201110451110080340411050390002990313440000d03903081804450b0f450305070b00114540641d940c0142c1404615080c054404c0f08507c0484196900d0510200030a0b07802c03180101d400c03c2002044085000504016265805460b2034145505181c807005005843d01001c2c0c4004800340240a0310300360024200208640540d007802c2003c11786840301c0900c0400e280c070180c6800300d00c4c0e41e59104074110408014000600c3d545c0e03014070284200d104401c0d00103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 248451294 1250 248450044 248450057
    0x30515100e07020a0b0a1e09080f071b09180627200a030f03080c0d05010311090c0301081509030f1207120504020a03030503090109170a0806040e0a0f03 67
    0x1020100c0c211450b100d5503460b00101443c00d25410501c0c12914000c042d240424103004004030700600748240194082604180820484200e140c03050b40d6010742c2072101039148021441a09101d00c880c1d030710b8180380850140d0f14800d91181001025510030502d0f00c14045071019100c000076005034042d100c182c2c1c112051136416983c600c42104c0403614074509880d1750807000c0310b1400101000041c013000050031500c0d46106031840d517607a9801d800d144409401e100030040001e00352045039040300c0081144400c10406980c407490034040381030007445c10790b000741c6000c800180f141660f0403c803810386104000410a481c50440e0303001d107d00700184100102d020074008034440300700d04000303843d910008080306002032401c50ba008207541c1d54095a804d14504000510016071211160101542c2e010710300240d481c4d4540650350301400d00d480c00107007000503a2907034000b0400030380040e0184d02c4196596032582e4440c1390810080d200010524403058000c090048001a05000200c2c0f05a11904104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 248452544 1250 248451294 248451299
    0x18070903050d0315050a0602060403081015030e011d1209030f100e0f16060c14060903130b03040203071202010c0f0b1b120103080f040b0706061e03051510 68
    0x701d08040d00401c850021076191070600f0b10081035a415400a0704003550f000340c0c3c03d0f1078590700955905002d800035082c405454041485102c642d89840054020840280700040c49084010020720b544032450509520780703c0d0525045555005481102c00004010403d01c0d204000200055000f0300c00c8651500c42d820303a40f082d40384240003034802070541d24000128040c1e1007009905041600c0c40c002840e0300603090002d140132108141c002616094039207032001000302e00c1c000302100d0f010707400010a0320520701003001a002c00001001d800bc80b400d154084981d9550498205c1c2c0000d850080d4180c0100c40c05000d030b00c98114208088900501d4031208540e01d9440d12481c08107100002e0350b0300c840752401c000604401c400002c8007800c40c940c003617281041c070725100501ca48060200401030540003402c0304120000405072006000c40c0075149981300c0481c60709100418580c461004113024464640000c00c0441d4070303480480f50400082e00744814980607042e170042c1700401c4a0044900c02002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 248453794 1250 248452544 248452553
    0x30201120f050f04120c0804030b061201090b0a0b030309060421020604060c170a020a0b062101020306040c0e0102031b10020a0201052401051231031d18070903 70
    0x2e0900407045400010201e0909080904881d20350140395410f020340e075202400001c00c484212070840c1d0300582007403070507180c58000900c1002022088103d5600b0721b0902d90610101020300b0b0b00420404800304403c05189041c56264041d0f0350600340d1001042c00300b0403160a00e540380e4103400440034080d00d040c06d403c2e8005070180d08180c008000042407101c01c40c0030000c013031102543c2509505101d0342020700c1000025038403881781c040200f640043c140810040d484122005c0000266030306004c19420700d035a0000d000f50801c80d0310314416420010800007003406800059034481040e4080c0d40740001d0003901f10103280740915a01400d2103800c0c030001c45a00148003410101031607900108583c03c0040c0d050120303030524440c1080011036110300c40a00c0e0f0b0804200e800042c032031a87c1c0c0000d5900c8640e4084004194000003041082d0351030114103184010349070b00700d4503100c0d17111801401000c10b00903460415580800e900000468040d907040d04540003503d604c41020f203800d14a07107032603654 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 248455044 1250 248453794 248453801
    0x203010e1b04140103060911040e1f02070803070c150207060f1a0105190203040e0f090709180311030d0606050918090d05070c0b07031205010816030201120f 69
    0x500c040d03003100d40c0d81d181c030000c0084040c0301c407a0215024428605500340350104a20184002001c086d606c0a6200070415406004026024002d20030060007103c03a0102c0c1d25101300b9400741c1e0782603561558480f010801c170f100340d40107075070058440e40c00c5907909040de6558100e00202521003000291022080407040d00080046600c6100041255025008244191600400b41381e0040342502641c4441341d0703200c2c00780c0701120b61440d4441c55001d03e9950a07810361040350004004040440100030307450b82e00d444100d0241080a0464040d580ea03210300004079135205000e603140141d4a0314020209110f01181d040380130299086d2481c112422002d40111215540100c002c078101041000591900f603081000d0f18281c95584805d0746000602c203900d4000c000c0c46502800f4003c22540240941c8192240140601500c0d1341e40e80c42d19424040c0902103560007616059081200101700924003003094440e0400d2105492107090035a40117540c0c804200021402c005c0e6079078030f801c8101c400c3c1e00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 248456294 1250 248455044 248455061
    0x1020703080a050d050a1404030e1903050a02210a1203020436020c100203100e0a0e10110d0e0111070804030c060203090915030c1f0206090d0504060e0607020301 71
    0x71a403503a1044604e0100701a6003008107003808a40c50108821910359000c1307503e17035000340c2c9864038100c00d041030b80024a43c1da60043d034480001c4510100441002000071318000e81030300880391080ca15158030406980112031020400300d6407c28001c82c2e0004034458001400079010b400c01505180c1c80c5c42c811030344018500444080343c50100070710390000917400c80481140c0c418200543c40e04108080b0700e50fa03080020174008070190300000003074203a00c0140402c005440c038401d1100c40c2e410201500c8000d018600e009940e036004405503582201d40508c9003a0000c1c082000080c21711a519901d0707401807c03076108642c0c00c0e54031842030300000300d405070007480d48620032500d1719101c5046040c60700061001da00004107541c410060120266941060f4640c01608a03034441d802440307013000f09003008500c1c80443e80041210040d4000001140d9282c3da00041ca1740c200c0d1000c0e65103481c02580c804c28184580080b0f6410002030020354494130420724210002340c0300750f2074621170354040390031141c082c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 248457544 1250 248456294 248456297
    0x8042c0406051821030604090c0b070b0114130915110717040501020304051201090b07050c1501140607050f0f06040c060503011a07050c0a0806010906060314040204050601020703080a 80
    0x640403c51281081403034000e0f0350205100920301461400c5020fa1907080380112100704035408400616269500e810802d075055000d4401d80b0480e17959103080030103801100b4200c40c40342000001046114490fa040c1803c1140100040c000d010040681c8005000404007616070700031803c161074207440603024480c080e00071190400d0799010181004810000341500c924080343c0d00f000108816130307002040d14103580044501e114030406101d003e03801030a0058000349a05010b50410210780c0e0400094500d11400006607580750703d8001849402e05400d00940542d411560a8034a282c10210003900443d48a5812a0035100c000b1b0500c0d8540001250410015481002040100031a80120800410650030041c0c215410450b00640b009030106004418540105504007840000c01c5828154200a8041c4504984429600e51100c0090042100143c20729900080c59072207403007402007400107080085190744541d42044003414002c0c004a0451041030300100128a00100900d0340382e210707 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 248458794 1250 248457544 248457551
    0x30c020609031b031504110f21031305010804052104081009060e060907090906060b0c0703060513030e0402161e1e03080f0a02040b070c0e010e010308042c0406 70
    0x42208040c0f400405400d186144d289500c03c0c80001604402810340e4146c080391000304c40403084021032034083d0301c605403500702849c2c0a50420a81070120091050001445c20581c4140c2c4660054a514a0a69008040364410342020410049611040104442c0384510618150381c41748010f2a08900c00100001550340300d50003000c0007200c1c2700e0050301f00102c401900b040c0c41c0c502540c6440704030074400c2d480301c113840b00d0200c010001304e43c4c04038028121119105442d050320b8101d1a903650868007048400702c3c0b5010100d030b0400c0045607910545603040e0b46010901d810300d42030101941280054100c07400d50303401b4440009040032061480f1194a1480000c601d500382800c0320080f006c1c082c4407581c0c80c00c0a202c000402c5c4c0c04412641d00c009841441c1c10a0744800e44500001c5c401c1e5840707241e1502000c500b102c00c2024516409007110314569900140741d80360102041c0c2c80800303200c0200070340740c00c10041055980203001d1080c03044410340f500c0700c0c071100c918441d032550004840440d0840c0d074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 248460044 1250 248458794 248458843
    0x8030c03042d03030f0203041a070b091f18060606050c010c0e060a0813021f0914061213152901121d01020d05071409030703030c02060903 61
    0x2000d420058074040c120101402c000c088803120405040c01d0001500300130403006480b054a00070400c8400903d9115240c500c070980d40c1c00644569000307080e088840c480c404d030128a0025002540015a204504d4103172844040c4141c854010030419501441207005841c0c2140850140d10074031000300031986030950b882c0c0781c2014040c00c65005c020400144034070000601461380350310066030055913a90500e41c0c420740f81e109151124008640d00298001003c1c00d250040c20590041c43c0614425900c0300d030300c480d4031020071300c02048810800075009601402480303154901c80c0d8480e608607004120182d0f8940158442014141c80f5507083c010030b54507400918020003841c0c4840c1c40e0491240144440d400f51640001c18941c42c14807050405c64641c01c11162101800c00500140ca04503c0210740e101a10421140941000c480210110385041102e034200c0c4814400c95036942c1008010740500c500b195001d507008644e40310182d030020701c2808004601e807800c2017101030030f140140c801c00003000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 248461294 1250 248460044 248460059
    0x2121c0507020715110304050114090306010b0903150c0f070c0b0a052107080c0306041103040507151103030c0d0b04020a110d030209030c1314010905040b06010306030b0703110408030c0304 83
    0x141034400503420040714803841c03045e000c2c0110545058aa0900c0d002071a0303110081031080170b0150b44d880c0d940c1401030400000e50344c40c08900034070081303d064041e01c082c0d400450342002d41e00c50440b4132550050040011f0403408803140000c0441c144126100304429031140d0210b1503a400c40280940800d0002a603101810b108030a070382248182414041c0d05841d203413100500009014100400002010000c2007042c4c1c1e4a405c40c03000c00482025203a01c0c0c0c9043d09115030b03030b04d10600c290a81403805034540d1084510586040b400321050308003d5107507840307107190421207600003808800a6075807207400b4081075666000070482d160f01941c6070f03441c15559a80160510705441d2040f81030500c10814280c481c0c4020a116031210400c41e14504658180c03070804001d007401060326601e9900c118000320345104154480c5000d01c0c01000b40b40010b9943c40011740445807a8040980b02c2c0720101e00240e9028447e82010401820580e14542010b03690407000d851030b00400c40088458102141c10700c43c20703 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 248462544 1250 248461294 248461319
    0x120108030a090b030105030a030f020f151e0f160207150c211209020d02090405030315010804030503060d05100c0215060f0d080a170a0b03060901090302121c05070207 73
    0xf000034074100c0b0b00c1d5503d0400081c3d0703984a0341c0300041c1803044000a4a044034001e04c001400a0008415030f1401340d204100d0381d50580c0201e4a2403404541c0b0024001d1484454a40a03c900c40c0a2419100c0d03803104610446c0c1d00300703100104002c500c11400003154407603041c4845c55555859480c1e2a20030b240900d40541e01e0a140e01100c0300d10909950b001b20201e602001c480310310300c4124000520301d251800441c01681c030460000e03400504e50004c1c4030810800100031403151904104ca0b0040c1c07032510004558030742c1e0594000e4001542030010444500c0c1200c403046103140b1840c102c0700925014403002040e40c0d0b1300032005015802407000800c01c4041e8121040d072140c0c0489100444d00c0e801c0c030001d0006028810302800f030301004a8190b4009014820416500c0040c140355280c03864001c0e223203006001c4001145010b03018090104458840500414800d02d50507000303405a89805600308456802210700b0395181d0784152810b1027031912074882c40e030040796694082c00010341081c00b000500c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 248463794 1250 248462544 248462549
    0x30712031409191406130506090703030903060c02011d06060f0a05100e0123072d031d090a1406010513050f220902010306080a0809120102120108030a09 67
    0x110074850421284120204110660b90406410110b0182e100d0803c0400e0306080e100b005194420341c014042030140703030151140355920170011940240c0c1d4428050382c98005521000300459001030041c00041c03140d8001d0114446588000948400903410301c445003402c09141e01e040780c00c41c034140b000c1030400708146012040306980002c8210b20705808039882d031560004020170030464000c83c2c62240c0c422090a01c060400700c0c8485504d01d90820020655442130004403035807000c081c00c1011030207890401400001207034039040b1100c1183d460585e07100540269160101c0a440d00c00c035003541c9c0345130410b4062000f014000076115801116441d00703601c06001141841820702c030300320324840074481e20029504280c412444844c1c2c44400700d203200081c111050010341c681503030301e000e5011503481801c0300e5000341c3e01800b146a40d24000b0380c903880d1203070300641500f20070081c078080c9041c503590f1a2819600e0100051400c0340450403035006203403c2c0c00030510745d0030010b000304140341c3c0310084401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 248465044 1250 248463794 248463821
    0xb060c0a2f030a02040207141213060309030e0d020103180506190e06151504090c140406021b0a08151e06090112050f070b0d18021c0c050303071203 65
    0x100c401504000036600c1c0f440c101c009104070f070001040f0041005000c100c031442c0002c1411155030107200c07078201126401c03000d000d00344006000c900088030743c42030003016592030b015140e010320f0300d40d00c02c2840b001c0640f850050381410b48400305010b2000050100883e014060b00140c842410810746450f080c0016400c10311080c0d0400756030024484020880e51b40041021102403a80000c501c042900351107110640f80b1021000f0030b0026480d44150440c0084c1081607542c959072402152078800b550140303024070001030784000ba403170306820203080ae5580c203004020f1400d007110ba030b107400b840d140c2041030310520340701070680c800d101c141c042d0600600206e05032680d40007c240f5140d40441c1c8074110511840c0d404041000c1940103100b0144000300403505018295030003162030b1070142510380c0c0300d035629603403003864000c0803180c1d5162010103128240e80202019101c100c3d559000402002500c0700b556640200d020005180e50104000d010003031007546607130310000a5000160888128802502 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 248466294 1250 248465044 248465123
    0x506030c07020108092e0b0603070504170715050904020f07060b01090f0e1308090d030305150307180e032203021f120f06030606030b04050d02030a02100b060c0a 71
    0x26082c40e50240e00042e11801d1032121b0042800340c101000141c41c07103000e0f0680150000050241032a4484000d01c10303a104000800700b141e9086e18055039a2032a845104084608103080c035400600c510300801000000500140c10a10451940070b180d5002c2d0808483e0650740d08640001541c211a1002c01481600e42400220345800e003140c5000100400b030749408004c07040c040d0108200c0f1400e45030042c0c070150205031b520201f81344c0500240001d440b80640074911009034249440d00060b0f04040d03650941200c007007000742150704000340c19000001c0e03609002c18001010250b450104018001c031196010090382455801030011025001c1c0400c8510250042c803030071841e4120f605440701c04894000012a2045100000000c0440d50001009207082020020501c1441c1c011031780114050800c2e036a0aa0310104141c0c2c0d81c0c07003044281e0380980c0117401d505144091a60005082e410080d158524148090b207025080503c6e40704c2c04c90700700415582e46c400c041d103602c1c001040c0e00c20030340170807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 248467544 1250 248466294 248466313
    0x20105070516120528030506060a0e0f010e030d121107020d0b060f030109030306050328110406090e011e02030c040905060d0f03020a030e0108040309050108100506030c0702010809 79
    0x890b41a41015000781000400514480a03203200c0c130111a40d0900190100046540c0b60081030540c1007010b00d0100040d082c20041201031900004444046409445a15040d0859014008059420f4100c0c6060120490301d140c2c45032010f2150034100300403995080c3c004041041c20300100c9000c1003411412107010f100020060300c521b080e031050a5040100411181c1d1000001902c07400c040d05455010350920103103400301500354116605541040f801c9d03503420a80640341d90302c09680c2c0324000480095140580d00400c40716001c7c00007018000e030020a102f41c59680c410180c1b004009280304d56035607020407512200d4919000705451603030610030740c51418100c24082041c080c6006064002c0d644102003905551a0340500c1450303503000207540c04000349410040d417502805101503000c00c1c0f5001558200d50f21a00055200f950305450f0f006c03a140c10080112401c64000304407100e5440041c0e80400d6a07501c802c0a9440382181e00034003941c0380844e00c001015001c000d00003204035402103182d07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 248468794 1250 248467544 248467567
    0x308070b09121e030a060b040f06080112050307080c0a0c2c07090506090d120906110604170a02191b08060f010308210709051206070f081302030601150201050705 71
    0x103905500c070fa001049900c0b9290001c068004085030750040e00c2e02d01c0c00080000300036070b0b250b00c100200c0e49070b80c44218050707a0f11407002040c51400017008140360010440440000e080401034816030410700101c4400c042d042d640d0450007846608012012800110400c1202002c40c00d1080c5042c6d41c01c01c0152242040f15025203014114000c2d14422030000c18114010740303d120281d42c20580205102042a03650741000c2e0041e145406078100080c000d1040a0101000046d00f41c040c5130b004000701c5030307403040504000c561f4100900c0380045016244040c0d00500c01417070a01080c0d4000c0341442c994092046001c089100b0303030350026071141c00c040c2c00c0105440101c101e550450b1f4000300c00f50f5031850201070703c00485c2c660340d2090000000c3e9000340705940d54000e66000c213403041030320000144010051002d58801e812281400091180c1c025107042902c58800183c0180d46032059a4141c04a54002804d03c03100340c01c901002c0701c4a9100103070141c0c0c24012243c006849003001071510048101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 248470044 1250 248468794 248468827
    0x30b010f0e0d02041a0108010f08070506030a0605060a03060e070207061403070c12030c03140f130503040801020403030c06140403051605030405041d1006121103070308070b0912 78
    0xc0c0401408032511640d4055100c0601103481c00750b00401c00c000d08036204e0035402c3c0317042117020081c0c0007e0040c400401d403903070303071454240965096800a0078018680f0003042016800284009252500e5600001d0592902e00c06001c1c03004a646000c2000b80c01c2c05504900110010160b00440d0302042e07040248640203160441032102e0040342d507640703030354400703050b81c0c0780d02000001040380e207540c1140010345c1c0d410761001750095200d9a051026400011141d29003020039a1101340703103001d00c2c0101d64504030280520000b148200c0c01d6074202a99100d0702402c9030825442500880c10415151040003224071900301440d040300329806c407508051305d0003030140c090b0300202204070991071007617814000b00300140ca00900d4014810300c184079040d00c2c482582030081ca0348480903c25504805003c840c0ca0041405070780d0688410741405201e526000c0f0060300c0c038907950303815000d00e800100110ba007250042c4030720781c01190024034504040c4941072420721904004240d62406000a200c4e1113580301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 248471294 1250 248470044 248470067
    0x705041a0304171801200703050f0d0206011401030c02070b0c0109021c0b04390e090d12110702040f021209010605030312150a090c030b030c031903090320040b01030b01 74
    0x81e103410f4110000c61031112190b06d810302c0d075605109458000080202c0000d80004000c0d4403c00d40c1d10034004140d00f680c0d540820702a203104080b06440142c082d5200798414480d001380f80c411500c7c05940c0b601e00d00900e50000d40c5404081c2d4549210100754100200941c100b160032075648500c40256071101e0000e00170141008002c0b09401a90403091045141b000c0c140c55555081c201c51181504ea40714954003081c4900c42e502010710f0001074090340c005c101c011080c0350300d0b240c2c22150034802300500020000c0782c210b03008a02042c8210340150702d5034814003004e048003a0005070f0711308054420300c2c2c40840042080402e40e04042c0d0521458402106980d80c030300754102c10301c60b41e07140c1d2480300c4c8001d200790810942001151704006000c1000ea0401600c110709501d040060400004c00e0648540d1182c00e041d40603840800980c0411020000c4912024043d00d00703845259120350f0f410403080c2c4101109504200042ca403a10703e131400b481121005a42400c0402c00c424800c000030f002c10f203014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 248472544 1250 248471294 248471297
    0x309060403111f050301090e01020711090a060308041e0509070f180e0405100506040c0c02060705030f07030906030c0e09062101020d0f0c09060203070b0705041a0304171801 76
    0x71a0040ca283c403070261600400901d401480780078000020700504903002482594040b0382011950f218071103041c402c03208000d0700300741011203003640c80c1305000300c00c000130700b004034501da0707950000000c14401c07005000a804010007608001103440b412580d1800039411171803107a02848240580180c100a54503922061401c02010b400c0784901c440c024000b090740802c41c00354120040108212000c21030603101c1d0841c0c039041229459120038001116689000341d40851079500c900805807401b103000d85811841070302100c0c5411041c06c0c02655507044660103c01107100444c0502289816028034865001c09246c5120140e04200000c0d0300014080d25150085000c58050703801008007000034100d00940030000e55441c011307010002e0041c158800310100e024034005101c09001d10810608003260700590045042c903c0360345610510355000ba0000003403010411001880d01c200f21a80e06900c201064419105d20385414400c0d0b17008006000030004100c01c001e044581e00e0300c5080d02c540b0072000e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 248473794 1250 248472544 248472563
    0x105040f171204060c150c0203070204050603030408070e0f0f130201030221130605010f030f12110a0308190b0a121106070c0303020709180303090305130806090f0309060403 76
    0x1803004103414040124a10402002c00107000300304280c018203013051642c852240c00c83d001d01c0c0c1000b030030300b180c1d520003c2e8001078000704200005403615401403a08880300070141e07840c1a6907100880e01e05100b507800003e109c0181c004004d45041000f410903401134500400341a2480e1100780500e030f07120243c900a040c55408039400400102c3c51030a1144440341c00140e1400742022401c005840c0e40801d01221440c0c241000070691608080e0440f0869a2002030300850358516601d11004c0010310b503e402c20045a4002e80c1c40141003084441143c0f4042d441e0402a410a60344d285868a440803c2c0100c03e8244042d201c107549403001c030202141c190b0740c3c0003101c02e02d0f0307403809041d1400e0181c95158000000702c0c00c6410700c0b1640800c08201d900ca80c00301d6081c503584000305d40c19100c03008030030100084880d80000c0444d0207a005111007a102e89441880c00001400302c0c00d000f6000d07001150241d011004001100c0c13020028001407400c030f00e000b9414140c403000010700364880c5002c000d203103d16 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 248475044 1250 248473794 248473829
    0xa0203060a020307090329010b1308010e030a03021e040b070605010905070c030f0210020c0313080604080405240309060406111201180b030f010203090c090f0f040201022d06060105040f 81
    0x12500402d030307c0d2216100b46000c00d580d20403403a0b04540001c4040742e0700e070304000000984540305215101042c00301d44003035820800300a04c25002500b001800d507840c000d0340102c0030740f804110760040002d090701039442a191106820004102c40c0160060001c0d2071500050190300c070740140e41e12440300d62520f003420451305101c01c00c07810100804480d15486001007a0f124400d107010007d8014203052403800001e0300d41d038000081e541c0005503809001044204820f1106007000750300c242044e154422540ca0b01681034041c030318154012a9030500c160451802c0c0410010140a4401c5500c00721040c1d90400f42c00203600c15000030706110b4049170070114044000901800d810034004004020107598010805030442d5001c1d520403114219507020782d048079081c0d842d000e81000e0054082501d9000d542d0796603649610400006070081c0d0544c42211102207034150150845d00d600e1240300a0544420750504800e46024005001c82d8107104090100b07000c48080f654006003101d148003160f490651 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 248476294 1250 248475044 248475083
    0x304030e0d11041109040f05070801090b0f09010303050c01050a020414060903070f0b070b01050118050103020a090512010902031203070507030804030c050a080301060f02280311070303020a0203060a0203070903 92
    0x802c5480c40c15001030601e4010203401d40000060071600009840a0060740003c0c0150021504210b5248c00072a00300300040c4440c1134640d11096400e031020300301644204042c0009100081300b684120b000401c0041d440d042030b84203006960304014448010340c102802e05040d0300d110700c010603916003d26008200440c180d50b0800003e002000100e5004079020b84511240c1c40740e6108100070b45002d612240005069441900320724030103c03000c80030750b21103030800f40110080d500c18140c2c90200005407030040340350354401d502240040164000041c81440380e1040c103081a880652a280c0d081c03041c0300f000a02c54112085480441e41464511003646e9030f031400340c586514100006e8103034890030100b0010004404011170685500e03445101c8140c084400481e43d40384200c040690403000010824569034540d8034049e001c40c46800c02e00024008030503030614241c0c140d8019001a0300c0702c07580c0c20031b50905000141c0c10402524080d0714615042c0c0003d03140b1042c2e840018032070710f42c440c0d075400303a503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 248477544 1250 248476294 248476313
    0x1e0f0601180f15150f020d020d050c0309120d1103031012150504030507110306100603020315031501030b010506040e06010813050610080609010911150712020d030506060304030e0d 79
    0x140003505442e0303c60b8580c0c42004080d4022000740002c03600c034064007075040b400007903c1034400c0e2081c1c0c010101c00b619a07404a820760000c44100150388014441d90711142d8071100c800c1c00042c030540081a440444031002440e501d1003ca114075103400403c14400d085080b4441d0f00d0a860400307804003100300d100d14005010312205104c0300041490107062104040d4041c0041180030302880d1101c141c0809001015100d0000707640d030314004405c0950420055010382c0203542c0c001c146503010300b10141035001081c20501c881042141101c014001401040341c9007032068090034055440c04d06050400210400c556005003609040c8840100020004580c20307410650143d030003025542c850810146088a031030517805645014040c02000503800a4144205a001354100342000004019401804515012500c2d28201e441040040201140004040c50b04c4290a50300900c40c9580b0384800a086030400390100d4401c1008009000109030302956144d01e070141100e8035070305414a807900080a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 248478794 1250 248477544 248477561
    0x3030c1b0d0c060b06031302090403030b1c06180804090207050304030f080912121e07020604152d0521090708010b060403030c030c050f1e0f0601180f 66
    0x5200303101ca20306407582e005490102003845a5024040c4803c0f40b0704000381400211030a081a036034101c40800945007601015401038020304000440d20b5500001ca5864100f290007801a01460304111040103040d21403084801c0c400268581c1a96041d59248014810f52050780f884907004250341c01031010a204480003954000f03403182d500c80003844c0a8080c0e40203012224414154041d8070700c8182c00100780308038802205800c0c47d2410440c2030401400d0b0b8400d4251048200c030610a26005868040060002e481d200d40c80c00c1d803440c580301004181d81010b04a0003403118030400c003600303020324014018041c030f06070f03040646d05c03141c14847c568241180706000080d04001c03042407003c404170220780d2109681c003201c001d04c8100f44031801e002c12031141d4400100001c80d0010000003180c407421080344601c0c410b400b40c5042d990b250961502e0083c000310441c1c2540d01c07011075040070100c100b00140528003004041c205640c034140b02d0015506080b01b6090745592500e40c0d06115000b1035002161 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 248480044 1250 248478794 248478847
    0x7080304090e0c0301060b031b0d090303090b0c07021008060d060903081b07050606090c301609060f0e0d060b090606030103150c0909140613060803030c 67
    0x850329551800a00078240501e0380307001a0041d80c5001c0c0640c14180039074000d03503206030001443c5403142d80c1070541d20a4100d1102680940601441070518541e015140300107020381d50103c2e02c102d484c10243e00188003e001c401500800300a1034006807180f800c1c10200104a061a902c0350345c80d0350105909803c248001802c0500e0b0803000d608041d00302046034054800107000d03c9808a40089050242c0324002c0302420700d03131000000034094580701e149981c2c0a070001e54ac082c10410f890070351401401109130003402e000848401c0d13500c41c4000b90002d40d844000c126003400508044030b40038003100200e005400400c014000c084113820b000c4c1d96081c5940388050042000c6154604250300201001c8031014401c1031440f011400c0d030300c1c042e415a81641c1d0000c0d40908a080049040001010b051100b1420b005404000241481c001d02c01c030114803002803007411043c5008010042070018004001250f44d141807428440c49d540042070741c1d807155480e50b105a0b144604000c1c050712a0003800c1011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 248481294 1250 248480044 248480047
    0x2090a050403080105010e0a0504020702060f07080403060c05091c020a05060a08010e06101202030421050a08072604060e03460507021305010902090a0e0c041502070803 74
    0x140040d88000e2240d802036840001690704d6200449490700e0554204d50721219461043c001868203038001c2c0452032004028528014201207614465088408159492140402d040040c0a41402070784400c20242c1b17801c0e4a008040c0000a403148414100d0f0484400c00c07186a00c1107490303c1c4a65005484014151500c03441c01c42c400801141c82402000b00c0c01c50306401040d8642017440c0a0b680c407814980303400e1070030301d20043c24400030742000f007081d906010030f04604880c03115000a0131140b200c1c250b0b00c603980c4402e41a00a088000c000c0e04120400065680c0302010300545411941586201c6140a800351a14203010028010340703e0010b040340400124400c20082e08115507140400880807004048182d4086640c1140170050212000035981d0307100c12258400e40003405103610040200c500040c1854214040350745c00d030855011554006001083c5141c140849401030520001d0701c1d0452501040c0c003003440c0228031510b42071032034803019020024001d000c00e4000e801e5203400c07207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 248482544 1250 248481294 248481301
    0xc0801092d020904060803030c1909051c0203010c08010f090c0e03031201031e05030d05040f0b010806071206080c100207080613020405010806091b01030f141b0c0a0615030209 77
    0x10003c0d4091900180700f503161040000300543e0200c2074074803030b20b4042481828180d04140c940c2c6024030101d0f403a8200102018042080d9543c0c00030b808088807282d40103056107070b052050508441181d26190203001c50540108030300d24112501c4000c3d1031440c5d101091001e01030900b929000303044021aa850301000c640c1c03000c4c500040403454100ca005403104002003180803074404204030003000280c40740c0c0080003c8001c0b012250452500684106207004880c05c09848134140c041080e04901c946c1c0c0c001c1800d0050a41d44588080010300030100200100f603e0030440541e00d0740c0400c00f050040e104001000b0380c0c54028040c840007440200141c40451a021a500b14580c1c025001244158a80700001c50407001c00103503540314800715002440801e40c00070040c031728154180e00c11410540c0303038404580389101c503000340d60f10580383c0d03681c0e030307101d400c0400d0303000c0403128040e9015200203070510240d0b5248200141ca45004c941261000404010b100443c49032240550806034203e60b138041407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 248483794 1250 248482544 248482631
    0xa0510020c0a140114030705032701020a02010606022a21060a020306100926030d290d020105040308090312030c072105041806050907020a0b0a0c080109 67
    0x4100d20f41c0b0036a10000507020f4081c0b0501a80819030700817001480c11f100142c4071482282804481d04c0c0501050700d00411601c11650990740041c3c00c20340180d464100411016804201e41d00002d5a100b030100060140f00d0100d41e200c8101481461180c1c130a494110a0000e5100600c48200781038001c0d60314a00e4840d0130440a984141c502c28001d4042d0300001c21001d1144e0007000a0307564030456200300c8510208021400c8050381d000c0d03882400108540c3d030180e2841c0c41858863f540172903100b40001c0308840d0029203145104c4185010301c04070070403100141c1c2d0050444d820749901035000c5441e050510003103481c04109070454996013000206029042c2032600152040510865400070081c0c03800c03c0d00c0d94008441c16079040401c00600c424060b608241c1407030250084124030005855070b5807000201002c00588121026030070803101c00c03062283c034a04039607000107501b20500001c1060100140714160510030b2136105565502c81c0480d00ea151b0001e19083c01d61848002c030a203c29040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 248485044 1250 248483794 248483819
    0x90303180427110406050a03140f010c030606020c04020c060105090901090818040b040608030301090903030e0a0b0106080106020309030d030c0e0a0e06040e0f0d08100e0103050115050303090a0510020c0a 89
    0x65900b10043d885004140c80c1034040e16043d598041d0690542ca0b20355661440b40c80030840601d202405031548005e1140000d00c20310080b43c606583c0480e14524050340030741400307400281c090150b0700401008503407081c00541e1a04503007041c2c5881c8015519003203081c0c01000180301c01048103000040d421005803802c842160000b0080b82c04100311000242004115001c034132a4050030340041c0010061011594003480740180641404101d64242000070b074200425054125009111840140303c0c040c3d002c801c280c050040c42c0002c5140c484900c0009940d0080110038000301625901c0340035003c1d20801003a0036589000d01080810340e1580d15424201d0b20807542c0b07500891034000d41002016000035002082801711000d0034240c0910001203132803000040900b021030300f1011000460594520905008501078000080d0201503034100303050290250b030190707200f1751044c04800380541e90b5020f224111942110b55510700030700188182c0c00c0c5004080340d550300101041000801c51040e05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 248486294 1250 248485044 248485121
    0x40e07080a2301031205070602040807080d0c030206060d060f0f0c0e0a0308071118010b1c050103030f0f030f0c0903020909060112060b04020412081e0903031804 71
    0x50302030024200b0040342d62000300c0c2d50740d20b0181d4180c80100410202c2c0225000d0011a040703850101d2074280d03151100802e90741300340d00c908441d0740080d900300940703001400402c01174070b00344c070341605113603001c0d14000d5441c01d0280c1494443c03a8020134450400c1581c1d8488216120001802d00100117661030b01c2d402000082000000300743c1ca1500e50f4154a4403200d15020780c1c0c1e0001200e801c0c03803401c0d115845080098040241c02a42c1c1188000c180524118094000c3c201501060340e9016403d051005904450005021060038a401440000c0e0041e05504000340103151820b102c00451904502400c00c15444811840c074006680310b400da0301c41c0312441a64001c2d5842c0790039032103415006a5a0000740314003034040816403c4140000c049400031990b98a0042001d0300701500c1c0d00800d040105203600403a172805001408401e01e941e10192a5818400f01c1d440354241111200480c2c1c4912811107201c48240000e200c144c542e41c0e40d90b0112885007603c00c2020341070000b4030640ca182c013400740c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 248487544 1250 248486294 248486311
    0x170a0c02120408191406040b011707030b0f0603160b0a021507080103080703090e010e01030218060906062206030e07080309030714011b2d0b01060f05040e0708 70
    0x111405090240607004a600710b41030b80d8001c2031441948003030040f01e18601c600c21075203285112010901184200641d501030b600640a0100c55407401c181c000441d810303205441c1240d0030040381000422140d485041d07105103408014001070341d40900003828400c0b0b01000c40f00300a025000420800e0218003e0b10515003e07800b122803200168414103107a035270454081d800605400f00500c00103135050080c00a143c428104429540d8982c04c000c5e901c804242c000340003400808004101b5840d1403020030440784502441520107040c0100800e820090081a144c080c034000a000c5241451001601903541c0d0100300444155132a400c004002c0c0004c1c1d0000c48141c8507100300803030a00c40100c12240c440c0300c010020580740d46410b54a40c1d8164070380700c4031411b200c11005517640000303405c045641302c0c520a0b42e002c012490280301c00c00300e2284004038860b590f400c0c80410400079040c030543e01d05541990078115501c5d61b00e400d04840500c1143c011200e28103080b002d01132032541010b0203900480d41e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 248488794 1250 248487544 248487553
    0x2041103010918020a12020a03050102040e0403120902010206041709130b010306081504030819020a090602010516140313380f18010b0d08030109060b030c07030f170a0c02 75
    0x3c900701d075004202d020070103944110090410041d001101a030705039054800307070011040564a403111402ca8002c1d60001f240d105400c4104810142e114070b040c00221246581000450b94540000f581c5031401800203000d84801c5240210b120340c9502903074801100203040070116800c602425004d44011800140440d081c05800b040b0408049941081c80249050445403a912604d0884801601400c0410030030810150300c41601c42d94001444000360340c0e00c44d0010b0038500380d402400c558000305045c1241182c1c0301244106903200ca030000040e0405030074540c40c0d0b16035075001c94200d504030702c00400508840071207050030403066035034103291280040c80e000714031804000320b89034a60407100a00c41e0500c03840003a00156100c086800a00d100c0d4000040602035480412010103030b484098a2040000c40104a40b24545c0949000fa02c04080041e04600f082c0a54426500409100405000c800749031000c800d841400c484020740d2410009030b06e1410302c46140801000f0540d0782500600a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 248490044 1250 248488794 248488811
    0x111121b150a020a05040504050103030804170c12070c0905071e050f070b0703110a02010e0127020904081e0d0b090c03160219030801051215150d020411030109 70
    0x3011900865031501c03a2148400c9503035a00d0008000d501c981c11080030b0041c00e00000c40c2c95141c42c81014082d5111b07441d2070919050500b4129140c1c007107200d1303400c0d09070810011040500400704a900c2c16803c8040ea07581c0358582803a00401700384141c0c11400d01d4038504001c0102706940703c17000d01c030001e681942c10107007461708003403c0b42d451150803803440e542d01c420490803001620301e416080d44484180780001d07100da40040141c105030300c10a92400182e448050400040d5007c0c8140c0c0d0400048102000760304800801d051002c03420420068404c2001130300180a00c0086011a8000c01492041761400c080c00180001980c011010b4601014542071066066051402019004132145c2040da0700359a07030f40034020103d6074907002a804501071040380d0103200c4018080078100f075100e6101c5203030359070415080c07203c0c11246548100740741d0b100c1844c10140d01004245281c12904030702d47c1041880e240301c082582401030160082d08545456020031080340c1401c061030586142500c10b100701c02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 248491294 1250 248490044 248490097
    0x110312071806090e06060c0f010e0d0e0d0204020f0c0a0501090b060d03200a020d0507060f020a210e0d030905042f07050109210e01050c0d0806011112 66
    0x109005080202e50142e0082c400e8030754401c005030b030102c1c000303181524207180d40903482d023000e540d0354080b4aa6912240032201035101030020142005242c42d01c203442020781c0000881c80f6103c0480079000b940e000801592800300c0c0740484400c0c3c5190310807280890100c1c0f61076402800b88420640d044008200407800601d444000c40e203205400d580e519940311010600b4040401c010014603919220b0318007030b400140c44075610030300880e001d00041d1803c607140860103000640d4444501c011034000d000e00c240080c40d40d50075aa50003038645010030306c6050014003a50200040d546031644036424802c14020036034000c04810503a001a1020301800e00d02d64040b105921242c20742e0f4200c3c0c80107200c80e5120102801c0540070040c010f030004a0b80e2541c5807507000d511a80c03184040310b0003c813260304211494024084400d107600a281c024a0300030b000d007007d41c0f10511464800204440030b800718445a01c24035002150306417075030036580b0564030843c0d1500313103510108004482d02c110144042ea81c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 248492544 1250 248491294 248491337
    0x905010b040b1902010e01060e0609070f0210020c0c18072d0806030c0d051501080a02130b010e0306150a0b120f0408040b03010306140a0903020d0e0111031207 70
    0x141e031100140760520395900700d404010f803600003060b811507503502d246840c0701a09026650040c0b00d00300d0302511500303101090000d4800001e081909104150456401c200e900080074070005d03031840d00c010307254401044854142101e1100b03555024400254504065003900002801201d094071012480704070240d03888050f0040d00303120056204c02030701e01c0074514011003189034032401c01405e4a040808240015030f4204480c1010b41703813079000c5404008100c0c0b21070081405000d940004002c090150790008120980041d5140172003919074681c174119034000d4601004a0500034195070b02440c1102007091220680404c1502c10076110320005120041e100842d01482c45a075000130060b0395205141d038011300090304c02c541c044401c020004120508e60040d6000e9407190301e011a490a00c000700040015000d0804094640b03040390b60400250005108200ba0b019400c20007c034020a0340141c5910580441c00085404000b8080c60824220b12a051081d00c0503159034403802d103080c05e0034000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 248493794 1250 248492544 248492549
    0x705090a020901031d2d010e010e07090513240c020f1501030206030106030507050408010e030a0f052106030c090112051606050d0203040c03080d050118020a0504180e15010905010b04 80
    0xe90060480c080001d0005143c4288912054a29510321704903411b60320308507940903009079081e0b5520404c1020340c50341400342000a0420f500d080c01070f42010b85084a4407002c00100405c8403940c0030380a41c00e10f00c0c4d5000a95481c05029080000c1040c880000c0c0d2071700c440020300003081c0120b50361440c550710b0f8101400e0580e9000f600c107a003542c2c00c09a0540080102622980610500b0301000038070070000d000785000d00c1140d034091502c030240d55a0240806400d400070754180441800404610a41c150071011820101c400c840c20945a640100b07041c144001001740d001100d000011984104400246180ca4402c2040360652459244110a054460301031400040c404002c060741d056821f401541e0000d000c0c40b400c0204a03601e42c2c0f106c006a1080215444403902e6000407c00c038940344541003250503603e03400350302d04a05100010010f1043c1c1c0590914000b07036654102d0400c40652141c00118189401c85102d20440d90101180400034803440c0d2060381454004107030703480c6c5242034404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 248495044 1250 248493794 248493851
    0xb061002030a1407061104030c031a0c1206061b0309030705180112081201030303050f09010605011b060e0d0c05160f030206090d150204081603020d140705090a02090103 74
    0x6494150803100c0d190350f0301610003030312003e459046006e814803050004200951103050803400c1c5503c1c40c50151515000c4203850706030300144404004d20045c404040f52111804508150041e5885100145450080c0c04201d214403000054000d103224000000b400000401c808891585585070304104103119980d5143c0321100740000100059864154000c0c0c420b4440c2c41d400303003010340c1c003024903410b14000d900030741c0001d4540c02071000040340c8152040d0054440c1e802449058100b1002074000d0000205c2640708109140038802030049661103101c52246600079100414041e001c01004429420415100f40c00f61998103543c4015041c0c505017200c282d034010951031440c540801180b40c01521529400c0380d1044415030008048070700d201c50041e000c09005031140d0408004a1a0001a03140383d40400f4034440144050fa403003006007420183c0c00080c100241a896100030f0800700039074031060700710600320300b032141000c02c0d50058002c2042c207a0b41000010410342c00725040d440840c00ca02d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 248496294 1250 248495044 248495057
    0x1a0607110d05010609051509060a0302031c02070b070605040c1205060103080f0c0d180b39030703090302120a0c06050901090e0405161502190c0302030a0b061002030a 73
    0xd019003001a00c1c540392500900000400e940c0e40c040d488283c40f01228404801201c064501140d03103400322003130fa00f0003c1500c0000c585421035000c666101040d170400c0c0201e01c201d000343c0b5141c0d842040320002820b1441600c1f61034030100e1600c10050305042d20210382c1d410040c0004242040c050031000030454119005000c16441d548500c0e006034480414a16942d004218500009000300300c0d100000c40c5558481100c5450000c43e10541301c0541c028086101c0c080000c0b1a00940d40210100b4100c002002007480c049130030905d52002c040b1421300785c2c03c1e0001080003010b00d6000a00e80301180e00994107075192491a04540752105070742c44006007183c0d8514018801c0520070405809540713410304080b4110350726039540249107402102c00700c03100d601840c2c2914040c90040310300070003440b2107030622805003c1c2000294845034101144031800c80b11a07903140c1400b001001c03500c02190040c040c3c55503122642080c0c0c074044011240680214a01c0001c01c2d03503107100004403000501e483d0340300d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 248497544 1250 248496294 248496323
    0xe0a030c031809020c060a0b030c0f040c05120705040f050d03020a15020d0e0a0213061d0702010f0507020309010207061103040b03040606030506010b0309010b03060c07020925031a0607 81
    0x6641125024400a00184903902e0115400304144000e1140003070403002445103150881c09641540d03d171081700e90094001c400108040e446161034004c40020841c0d0115401213080021502c0b0b005800541480301940014002c1d441d421034010825141e0056141c0c0d0415102c0061101d00e40c14120010f0042c1c0c4103486c00030214600c040240107489001d00c003d4a00024861040140c40110300e4900c02c940100c924034085151004060307500000c40b00c003d01c00203280c80c403c030601c10b00c5007524501d558400c8002406140c403e5100c4120301140f09000c100a041c00e680c000e5813a002101403c3c05440703200c0011034402e0082c80701040c18400f00c0d00642c5441d04140c00015150405003040303a1143d203600c40840020020311809002e40b256002940d22468545925420740300d10362102c03030007900403006112030520341d0001c544404d0303019610780d0f07115251802c104040c6c540510184042800c07084a404049a0580015800c103001c40006200c009840c001c010040c811441d000b841c0c0d4103004a04c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 248498794 1250 248497544 248497547
    0x2060c03160516140709201c0b030a0b04021311040515090907020a0b010e01050312090607050d090807090501050603060d03052203021201021206211e010e0a030c03 72
    0x104040c40544a0420350248159100044104090580c41032074005d00002d1090800e2446207a00140803006148a03400ba0411680070502c07400380d0030b40081d01c0c4c0103c00f0001403025008181c030010301500b266101c003124100303101583e8040c3c03400c9103d041166050500082103009000d003e100e00103603245010710b4401000302045815801003078854092001101954940c00003130f12504150300a00a000b0300c5180c1009030a805030009420a441e8130011700468500065004440103802c12959a441c18800007a096000c1e1000080003841955a01c4100c10791141d080c0d0211542d800440306019106c0c0420000d66200b4095903412150500c00141a0b29041400b03a1045000e828481d14042c1c42020300c0480c41000e00303540c08111142d0000b0811400d00791000414490036034001c40c241000d10340c07401040000a01810b101d032240150520003841403d0088210442050072907800c100301018060340300081741141500f82d464a00710a444800124542c2950355040d5280d0a021b01e02e641d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 248500044 1250 248498794 248498797
    0x12030f0412030b09010e10030209090c03010b0a084602131404020f0402040e010e060109060504030201120b03071d0a050a0c0207090906061203050904150b091302250302060c031605 79
    0x7c0e690320740540300720010160b110144101c0c00b41211401400016803c2420305094951200c0114020308803010104442e0f0340119030341060b600c1404a25030345000035000c05001c2012400702e07400d4240c04002d28103840c41445c0c03140f410a48241c1300c1510461084c6074004c00c032080c40d0843c1c1c52480e0032000082c01440c280c1c0180d2009a0001c10040c02c26444500c040d82ca81c0c0242c00c03a83d42000c104040c04003e6030402c1220005006030b01d000d034a800d045a0000744800344503000b40c419aa1610483daa5664051111001130000301c10414031000000ea8402807080c4240c841c401050704d84000302c0c00107400c0d4024000c0c1800c854000b0500c281c0b6241058000f01002901540c005079518000b18001c0c5c000950064100d010340c0d107441c2c50ba0007080030031084075401701c0343d90300c1814014010440302200b4030581d40341e2035046400c850307040102064100070741300b030f00d282041c0781c640c0c1e450544541e03c007076074181043c0b0702950803211a40c0d1140d40e40c5000740700940d00448800d400205048580d0310640 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 248501294 1250 248500044 248500051
    0x150103050c0d05131a011e1503090204090212010617010606021f1808040e1f06030e01020408120c070e0103051207050c0a0e0106020114130201080912030f0412030b09010e 75
    0x2e02c07403141c500c1d1341d1034221080d81045840303000d0301540e0004103c3c480f03201000310100d8002039121300c00030f86089240b01140c0321a04d00b0100303241d101e025140c290750f900d034000b06409801070614000001d60100142c001d00c4580122858004070480c07000610740d0501c40d40301650000e0300142b505122a545c050f008441e55100030140c02d80322a0700300f101d42d40c199005e08903548103001d403540b41c0741030902c84422004000d00d000d0501c85000502912200014640f01c1152000d00f40010a22107460040d0301a109075044038100b80300e91403207124003280c0d000c01842012400800e07228002e0303c0f03006011511000707200c0901740b680000300c09910406001d00800e420b510031000c441400a00102060020800c1d510107040c10403008010491306070203003d10b8085501803220420113181c01806410602c0020001a04009903000040c2d40e00c0c0042142501d80d12404c01599100d2601d203040c07031055001150700304c4081c003100002168036802400707030100d50300c4001d204a403160b0810010781c103c2d0074002d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 248502544 1250 248501294 248501311
    0x230070e1207090207030f031416051b100e12030408180915011107030213090c1205030705070e0f0613020f0c03041a0703050708030c091206150103050c0d05 69
    0x402560507500c104101c10001054615009600c51505082c0a0329031000600c516040c0350501c4d48080840c0390722805203a1101c103031350284081c01d400d07036000c03112400340f13152440c0d910210850200c40408000b0710554503080301e60040c41100d00e9480050307150840c3c240580c62014090000c01c0018003000042d00d0720280900e8018114441000003880d000e00540700201d0f44c0c2c0580c1a0850156482080540c1b02c1d84024010801c1614544c0403510703401035008014a150780d1002200100100b0b130168030000c1881001411003440941004c40c0c69510840f41200c2ca03104020000560b41912451103118400c1c6042d54580390381c0720001d1000740c0216a0450001070303401c103d120f5204032040c000c0d1181254260042d0b854904050301c04441c408400d400d480302042c107001c1800001d5028044454a035070240c0ca030781d20398803908035202250280f103012136484004461090040100020240d10642e92003042d081c07064031032001034044480658480103500c00800c6413041c00f94541d00303d2900003106 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 248503794 1250 248502544 248502559
    0x3120c06130201141909050f03070909080d050103030207080106142d0325050409080f0a020a0506160e0a0f27051305060717040b0408090d05010230070e 67
    0xc2c40002c0c40c00b640071842c180d80d008910511700d42103c0d03000400b075024203c01d5a60400c205595000a6903441035032040103000e070b03141e00120b01000b00d00310943d8441e02a20106008558491a02a4842c205d9004e40030981d86401d2000900c034000841e80710b070039240038100c200b41000308c04009600f50089422503241c2051200c0002c85503e040004600d48500c103214080c5544040c0b42c0c0d555241d409900542c841c2d8206014030000c6010724040310b035601d0301c0014040d940d840100c0181e0418004860160540c020403040100c8000b4881800804208a64440240d200b04500b0010000682d01039039a000d80c08410030311190200848130540c1c04000d4450b0320303e10808500620a56504076131501e4803041c04607410040000070020941c00a100d41400083e1000341d1048400f101d03001400076102d01c100340d001c20b050008800c216041a4000380406658804030f0a145010350300c40c1c0c01e0585110225400f18400c0b0344510340001c40c4441d1059600c456444000040b2440e0712840502c56210f4503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 248505044 1250 248503794 248503817
    0x8070f30020409330b16140105160503010828060c03140619091116050721081206040f0e010c0807020d090b0c010b210d05030408030a05090c040f060503120c06130201 73
    0x70b00720304c7c5c0c608400e0840008505072420500b040641148066520184031382800188035415021076000c1240e0b0245210981003103c407020030050b80f0180070b001c0e02d00707894483e1156001d039141c0c0140740c1c64100c440014015403103e01c00d11031005e070100800032950400c02010302903000c068004007898150072800350308000174211045011055108106c6031584416020410507540211b941582c825104e540d82d906043c507240d00601e8428034140a00c42c400850008645070380d41da002c0500c00144583c02c008071400012028000d01d10380054070089400c2c140080e1800340b000500060f4522030755500a8907515000d00440036410441c46801c040d503c0c0c054030400354032030f484543e100342028802d41d1020390864041a0804c04010a4070080000410400001c25444c02c116600001c018800140d0380d85c50309400e070706254aa00815034001d0510700c25101422041c0c2025050f500120140c0f1103018581c0b00301095841907031032688a40d004800024082ea50401396640c0050040c18a10042c11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 248506294 1250 248505044 248505053
    0x60c2010090f0602010b0d060209060d02041403010501090c020d080603120a1709030703050405010e041103010b0711271b070b0708070f30020409330b16 67
    0x1a282490600001c1038500e0401c12600300c00c290000901c0980001c01c841410395010a11032490039201628a0703400160504880e00c0307020407641d180c280b2183c11926244c81d00d160080603d4a4180d40c0d100f98240400814403542c14410320304071014a40080a005c00c001c0410344500c14000c04250b458011140c499280d060300c2002081e980c036503555040c0341c003541c140c140d025102c000350005440d6032084c05910b0020b9040301c00c50b02610024201003551800850006000e0110058072280d01076011000050140703c00b00134283c000d11442000000305188070a0020310003040580056159510f06c1b602c2c601303030340b0204103504540448058904054081e4041c00103901003c0304807480c24032002000b0b040740d404401c0716044105440c089006180c070440c010b081369100721109802241ca03415036441d0000c10342c48102c108950440664850b0764603595000104010040c500780f0103181050b6010080349010003035001c042460b441c5001c1800c04c0c680c01b4440d00403410b0500502403a00c0c1000105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 248507544 1250 248506294 248506309
    0x41a150112060e07021c08070f120b030a050d030606021b0d151e0c0203030f010b1c090f05150f1b0705010203090c0109051e10020a080301150305010f060c20 69
    0x1300d00680040c004914440c0704000c00c483c8810340c02d401c003c41501403085031a032140e02c403045861186054555011a961010010b006010040e45e051140188541c104040880d11090301c1c4500d13142000a9651807000380c6e180e0880c01c000d41101c0609001411941c60010405200a80900c0200e0440f4642402c2c0000310b5401c8400c04900c41d0216070702121041c000d01a0704103880311440a10b0540c2042c0c50140d1170f401d010300a40142c160b001c6038150004402808051514802d183c003031001c5e00d110b041c801f81c020302c11003040d5501c0c068440040c20b190030700000c1d94003607001e02281a0381540c03030742900b400059441140c108484401c002c4400403450034006103000d502c0782406884411800b00001d8064036403948800c6c012000c1014200725101b15440c140358400c8160741e40c0f03030b42c1c01100208078209540d03058010006800800042280c10032040c125448003c1918100700a90300c2e12446812006035100c3d80001901031000d05000460959049101c12040c603c0305040040000021703442d0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 248508794 1250 248507544 248507551
    0x150a140307080105090a11070b2a071104200903070f030809010305090d020a020d08040506270301020405060304060b120304060309051b030d050a09090507030203041a150112060e 78
    0x3545440140445d25092001c960004080344040082d40c61038045840e090040d040050103c1e480302000543c0e40218a443d40405980c50341ea010341000f91101400319034120b0702c2c0944001401c91a130901d50300309807042c01d81c180858228012820150754040489500c40b001c1c85800d8082e40400103840940407007031b80e000d1449a0f2006858155030000182100d000418480075036010340c0a4410294003c20401403164058600e0360300710000d82001a080e100e150302503900700f0000a8000d450515807101010503900030040c120f040480031080500b44d000d0742c0181a8400700c200040760000b040390740100072010b8050900114012500b060301c0c19600280c0c0002c1c0440c2d2216031110070800f0500c901d0001d1040310250080c98015000403a60314000110b9907424004005000085a402a5041c00c0208841207050046240042005020703400513181152605155000c00f04141c15001c1c181d131085441d110001e0b0400015001104c802c1c0000071201c240f6940d40a002c6038011901140b10720 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 248510044 1250 248508794 248508797
    0x5040503070b0406030b0102010b06190c02060d0504021507170a0c06150801115202010f0f0215130203150f0906010602070b030703060e040311010c0905150a140307 72
    0x8480e0b10f080b80c080c00f036442c0707254104e0449e4500050010b0603650841070f05c0802c07841500c41c030010441c903031060360000600d100c06540f0030404260380a1010107504502e119900c01c6d10308186950104083c030126025050b0010028100b03a41e500b162840d142003c3c021005a41c80c052612103600d40380c540c1280e4078640e110061425410060001c1e8a0900a00501158603609589003003046c0403444800204540c020008003600000340141d29400343c2c080780c011820140c240a071401241044665075205c000490209501080c05006540544243c0c01703040c65a0f00944051a9a01b43d10b00c451003000b484045240c501d1183c0d040903850400c058140300742c5001419416090a00c044d10070b10344000c040080544c046401030100301d5002c642c1e241140e40b15101c850700c07920f41043c10307400380c840ca81102d0080d407008400c00c014150301030354600c1030f1880540208580540503a08032103042d254051241c01c030142105c4d561080d070070900148940006072400c0c00340009001d50781002136000b5110b500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 248511294 1250 248510044 248510047
    0x20315090907241707020705120105060406090207081218030406020c09220609020a0506030703020d0b010306140d0f050601081606020a1104020304260a0929070305040503070b 77
    0x2980c0f01c00c0700c424142d4002e5800700b000400761980010168164041e540c400d140003180404e02080c000c01c4004090117004050b90070840e603041c00a8000c03c400c40720284603508089002800466a00c00c07100c445421919241c601810704142c41c20307105014140d0003004400c0036a0100c000c0c406e0010f0320141c8001c0d4058034002c1c04c1c1c10100007080c60081c014007800c407481c050290030300c001c3e1040007520590003507011510742420b000180f0180d03102d900068011000108014032940d147d801410303030780c8001e6400c2090290b003000441c100c41c00f5001d400522804014000713680d14110200966181c8030744888002091103590381c500f001002e034441c035402c1e0710201012240b110202485000303401d05100900f11080070ba240e103158410040d803030138000ca900002290602003580425844110100d01c8003403070070400c10398441140d000b10f00310800030f202007001248801c01c03c0e28a03040e52200905190320380111414901d041e60151504400b440b40c100000035160710b0a21100b0001c05c0031f090b169 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 248512544 1250 248511294 248511299
    0xc15090e0c03010e010314030c071d0a060f050103020913150302011e0503070804080904110a1101050411010e031c09030201080c090901060e0406081516020601080a06020315090907 79
    0x90403000026203503100c112000c2c0018881404242900350440e50080000c404800b840b0104908600c0f0300b04d90aa0280505100031a10362816003a424130004071110404a641e070f0b0012240840b030746400345c0005003503140c004211319842500508445480240111035070b00b120b002d298202c0321559686081107180314002c205642c3c03c0401d410f080c03041c50140c48400701181200802d1751100412000600044201003020300200e5001e407907001c00054020044103c50f002d51901c41d4005915003000500d071003807214024034043c015035028035032240c01c1c680043c2e0031000545036006500501d5405203d510a000a00c44503440c268075070000645030b040c2c4079400e6000041817408000c000f110821010001e400c282c0d1034035038146046821901c3c1840d00f0500c07450015025081a52000b082c074480e41701c4051740280c1b007400c441c6c0540303040083c62510000400069854084c2441414095009072407601e01050f002e40065a100c0d91a8640b4035904910100007440b40d80c05545000103548409000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 248513794 1250 248512544 248512559
    0x60e010906050f03060919030509060c06010f080f10110c100615090e040f02030709110c070f050307061b0218071d030705040905150403050705060a02071e0c1509 71
    0x150100c0310044d80a404107240c14851256613005040303100510350a541484014503106030300ba611007c0c0c0c011300039035440121990190390381400b07005403024003503510000103129000103000140240d408000e03040b82956010f200000340500103000307402a4017041055000c40040c0a24142007500b65800500d0500745185401c24011000701c8205000141c002408090b95050885a00c03c0d8841c1644a112100d071000c241460f0b0103601400741c483c01c1c026980d00038070303080c800b5001144000f8203d0700c05941e240b012580031046d500c81d06405410191081c040103214445c880d90001c4c0b610910520840c060380031030407020190140110011001051102d52940108581d680c510248654080500c00900203602c405483c46141c0c0f2444e0b40380900c4003080424007280411520813030106582e458a404e028109a2010707204492a0203010006803080c0c40c03600c00e0f2400706401409882400e02c492640c0d01c2c0c0c49080b40e4064030821030400700003071040007015069801910032383d02c0c148524584442c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 248515044 1250 248513794 248513809
    0xc0102210d1103040c120c030210020a050d09030b0f070e0105030a061211190308091e09010e0f010902030f0615091e0a08060103150c0c080406080103030806030f0d0f0201060e01090605 81
    0xa16110042c06c0024808520804c1120081e6a011a400700c56000d600406030328059000304001d1890084a280f413100a40001412045078054401070000750f552040080c800348088031001c001c40c04028401c46a0b5115401540d4014000300d4002030b4a03450b40c240015110741c010040b81c00088401d616203440c103000440c6c0200204a0b240d0040705070940d0b5172499640942d052040c006e81d089603014184a09603244000c003990041c00210300755844d050000c4101c2011101035618003448000000ca50400c2d01c2100d04c51100300c1c00b10f5903280c465004220228035403600d541e6a5204c2032000c58526503600010354404011442d40304a580e84250034480642160b0b800720445410a070010004200903512403503864511200015151600300000e880309134004c50301909010b07020802281042d0440d1445058900940f200c019a90395801015a07a01c10030356054420b0f0800360741d511000f03000707800030f07040313032001c0d00001c1041a01d446905c6400c031400d038060842e441c1c030f8420030030041c1030604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 248516294 1250 248515044 248515049
    0xf0706020d0c03090c05060f04050a030f050105101211010c120c03090f051509030f0a061a040e030a080c0c0a0305091206010506030c090a09050a0504060e0c0102210d1103040c 77
    0x30180004c080940b59400c0107152803107054000c0c01d0002e1031040741e02c40309040754054000108600082600c074200b107010603d0143c001c0740c0d01d61070400031a051146610500d4202c808000c082609041d25596065017401603240340780c140800a0304d900c0c0051011a030300c003140e00c8166140f151031141130a0040c07141e00c280c0d00c41100b07801801d80c1441039484002d01100260b0b100c44007540d0302c1031243c020070701d010580d110810260103402000b0040001e41d07044004607072552070200040c40081820002154007a00c101c1d482907008001008081d40030302034032a4030540c0c8021090811420f541900d0424900380c008074005100012405514034003c2021143d418018004104a60410b0042643c5100150900000c480b000c0f0710668a59a2844001c0240c01d0200091045041425105002c0c01003035400321030280c00c000810707500020000e5019100c410590051000001034407031500c108245504510380c0c40c0b0200001c00754081a07004200c000410024a5956841c1c10705041c40d0741449034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 248517544 1250 248516294 248516297
    0x1240e090108062a0a03050907050301090c03030809070b07030f030e0f070e010816030201110c0d0609021002060c031303020708160e0703051308030705120f070e060c060a0905030f0706020d0c 84
    0x200c1c036102076101000940382c14617001d0400042c00c1e120049007620b05040341c4d02440d415824081210f04018610354003004681c42500c501c0310640302e00c0841501d401d0300f806004900070042c00340b03c0c08603206081140e482d13100c0307003030000b00c000302d81c0700842c02cac19888078070300200d94400482000100d0001101900400c1644080c0805d58089054443c00c0f400d1448041d0400c83c41107271210110800780044401031000030300c800880c229500d4003c0180007411010f901c02e5000c0c2c1041c030070751341c000326a59100c2d43e008000c607890b42d55880240045500040e2082c0d0462140c0000455004010005444424036a1092004113440d000c140c10016038000c1c641000c00d810801481950003040714000a0950700c80c004d40c0d1641e440190469030343c06145e003031002e560442010f200a16640070803c0780100055a514003502c182030051140300c0c800c42c000c088142d4404030005035028019446018202e10a90560340f03008d003002c1b180c03041500580802c1d5072031640056944540c3e800ca200380454a4a01d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 248518794 1250 248517544 248517601
    0x603020306010303050f0d02180a06030c0e041802030109060207060b241b03210a09200a180b0910030327050a03050a15020301240e09010806 62
    0x15540800d4a400061100500307000010070071207011442c11b0191031101101d60011074a0f4600d401e02c0440d00310203481000c0c040d8840b0f580208200d4400c4c051810342c401d00e621800035442e00c0509000003040400d003180c0380760303a14644840050340d0038000d032a4680d002d01d10250b142c042504010040f1014001040d204800100a60903002201c0d0340007801030b41c0d02c0b0314154880104800d58008016074000c00c0049010009825418008034200c8040450602004403501d41e208040300c0c04a0b136141c2000780581c0e45081e944420000b40c0e4402c901ca4078030141101c40c5607a580d12141004c94401e6080e4517841d5195207688515040a040042d441403e40c84a401c01070302d1501e01a001c0240c00500c05c40303804544400389403007150703090761400404019042c000441d40d00c2c10300035154101e40c001150f0303d1000d000662003400160080c0e030705a42801c481440c1e01021401442c0c20701c10b495000728180201407818910940c2c0c3d03401850700030311100c0060601d6240280313003140000d440110305138034081d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 248520044 1250 248518794 248518799
    0x1611100f0b04050915040218040308041a1b0919060c0b06090708040b0a11040b0a031a06040e04050703020a03062a020606010c050703020907110d020109080a0c06020712020616020106 80
    0xc0026440c00c2540e01710b00304205900c40f8000700d08a03d0401d9514500f080b1040140402c265104001500c214010800c180031034284100070001540c041d03c0c400111901124107a8000c000900100f0380918010101c00c01811034448a0030280d845501000200b011003a070f050034801c8007582e007075105400700c0700b000b09407500d5000500089006000900003048003000a140402540e01c54442c40e1030740d807400e0361200e50326051080d40c1e07441264080002824001075600103410a407240308040e00080509040c241802c2201800400041c400d0321a84940003001000d6100c4140150195003d25070124034207850121150120402103241c4202070400c0550040f019070201c0c603150442001d01c1c0101c050340050615601e00303540745e0800f941c040040d42c1030180340e41d0455107500307030384603001d054420b44043c8a0040c1d0807200880c0c40a0705182d420030601c1503062081011403021442a0801030030803805480d1800c2c02c1c502081014003503070049040c001c900b041e2149000b072750442c51000340240390 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 248521294 1250 248520044 248520061
    0x106150c06090209090610050f0d03140d0203011e05180402040c12050c0a020712031d040906021206031603020f0d210f0f080106081611100f0b0405 65
    0x8008202010032012031444810030500360007011115400600740743c1a803e241003030907205c040070344622241c0000900b00003111b082c481081d4514a40041203d040a0b400380c070300343c1d004030405507800a202c80401840b0317841d583d1031001d98007070032151801200c0300301101440740002085800243c824041e0b410040802c500c6010940e50065041d200484e040680da40309039980d0020000d06e140e00d90500081001c00c642100c080c0c1080d070003550031103c55950302d00b201e51504203026030260000325440702c909400720011000c44c214401c00340c40001e00b45a00d0b124030080340c004015014200c13142200744802468100500014a0203101c0c00d5020703207207035a0008100030040581103010b035000038400409e2101160131901c154440107901f45140f03408107001014100c00e4004a40403c400d100d08450151003954014140c40d003070384581d50380c0d0f03e8614a030b00c447c8000741041d4040054081000c1400c070400e025410003540e481e100850302d400300c100010107a403807071303003040d4011841d0400700710340d04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 248522544 1250 248521294 248521319
    0x2030a1706130e1011090405012c071701030506070809120703030929090601120b0f060f1509040e0d091203110a11030f07032d120906110106 62
    0x4414400b80001c2d403100320a501e50070a40c812080440341807420385010403034412540200380025007290100045c1ea00c4010111520b103500b4442030f0f85040404803120034280008043ea04007807241006850101102d408402c443c2c4244c2007215a07402c590144829550401d06550f00032a000c00030b880064003c038015003050059400c003804040d100d00b5028107221420340803203181d9404400509110381000182d10f2201c4003075490208078400c0900008540d024150f00044560740f0980c44040f1f40c50325440d8001c0d030200601000d40c042840072036400c06940303908002c55105800107686c1e44800d54002000704603060402c1020050b00881403002d41103038400c40e01c605039031040301d100b804080715040480e80c2c410040c070041d001d03100b8505501e091041c03d080001d00c850b02181113a800e46414100103495459074413004000c1d8100701c0c034201075803e0100c3e07041e485020410703400c41d000c0c4450311418440c42e0000529004039036080c40c14412a1340c070681856014220000a1049a01c1d103140344e02034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 248523794 1250 248522544 248522569
    0x21092411030a02180604090c12050609060d030318060c0906090b040902030c0c070b090406060c0c0e06120a060902090934120c2105060105040b190602030a1706 70
    0x855500042144030f426084c00c02600070b00c1c1c0030f0300c4c2d9500c540c0c8800040d801015112610004a04030090714901c581050040d144196005410758a01f61206010320113031341011201102810707101d9008000f40300080504902c0d250295002045003500b01d24050110ac0301a0005420800410760601424140c04101c0e02140e0501a005907070b6600d00c00c010780d880c0a80c3c0c1c1240c4072030007251000035009400f1405001090801c64040100c00c0d5604010703104403a0011004080070101c020400c0b80e003081000480d8402c1014042c81c0305000301d81c43d49030415880745403c40d0016a103014030000d60070810301050780141c80f60000c3c20a0030780b45031144094901c41c0403900042c4030344182102302d1076401380400002c060218a05000d400989804143d0070b505000c0c2451000030030a1020440701c411240340019600702c000391000380d003440c05000190290800c0e01d5042440c04164400030382c400407003c0001c0a01d44e01940d102c9882140081c0710103900d40050a00c040d803801800f000d50b0311200c08402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 248525044 1250 248523794 248523811
    0x201050910180b1c0b1c060f1d100c1d0a030b01080d030e0c01143001140105040e0f06040603080a0e01020f01140103032109241103 58
    0x701e254203940700b2601c220007140a04551604240c00080e9142c94001070809038100c08940e40194a00c07410140031184111051a4000000c41103081c41c550441d594820690041700080348022500200b80d007030341c02c80c15440c01c070058101c9040c403442000384200d800d01d11381010144101404c078100182201450358254440340c00014803080c0c41c0d82c40500301c00086902400c40b020035a034a540c01a19041c02143c0800400c2c1020030300f84014030042410b0300780301c4050319440018000d1121140407508500e2042e525095140c0f445868a2483d40d907401d0b1129007141000c03401d40c1003103081c46131410b0310b0b40401e05000041c00144014004802d9581c1c5c082a04000d00d581a9600c0001401415070365001a001850000f007041c14181d2000030000c180c5403e030211071900d159a10410308a80b40600707a00d2401b0007460051000030310800a09a00e0012060b40d00002c1100754814011118820412130f6401c1c440300100d0f036088060846000f0020208104000f01d03d0442c3c10b01c400c82c40010704010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 248526294 1250 248525044 248525059
    0xf04030c0813080a080c010c0927020403020a0f031518031b12020c10021b01080601110d030515042306040212191104060207060c0f050102070b0f06010c02010509 71
    0x1080720b0100c0c0e101d0001401800b003142d1000c4000c0c102081954400d000a004550901044410710f0b1301487c140021200c0402c10030100014840844161403080841103e2064003040004096076400d078441c0d01500a840d1245080ca18502c2c01c403c00401008181d0380c00350800250040300b50540f04600e08164042c10320b031004041c055030b04001c003082c4490081c00022114100440e07207030b0015084c5000d9070f05a842282d20316001034141c0c1d64500c89078000c5594540401103640d9944034212564100b03d041c10300c84071501c20a00840d00303104442d50310800180da03070740400041c02d89401c5803100d04d800640e02004a6070340612144409140e400340340f201c00d00294003080f41911207034112074a45c080601071300e0240c10b000050030f801085066004a02c0c5040010180b0b860910008450403030f455a0002c1c00194070380a1305841d201c1101d8070a8429521050280000c548213000902c013251141c842a82540f408002c4216001c0003d0070050400481104110050344c20000302c0d0a082ca0451700c0f034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 248527544 1250 248526294 248526307
    0x15041203050606070813030c09021312020d0b04060c080606180108100f0303031b020304060f0c0510020408010b0111030c1002090607051c020f010c051204050f070f030303050f04030c08 81
    0x10355075204d041d8000f460840300184018500680b46131038010380b485800103400c00380c1d407550080d0a90294000c0101607a40ba14420803400c68651420540303a88089c00029503c069616140c1445404807000e4400b5500d41d2030910b0306540c8105042e0380080708490f4a400c1c05496002e85420300c4035101d202d4184400a00805c1c1c00c28001c4c02d600000305603800440000c141c4a180c000d0160074184500003030120039a0480800d10300200c02e44081d5889aa43c41d2a100c04034801161219a800801d0f81d55008107026100f18080c1400103201815400001080740580800014181400d9040300012a0404d001102c412031020801000c0c1e0104120050b0f20340d90b1900001c0e04904c50014001c01071b1080740c2401c19083e081807a00c00f00241d02d50291940074454103400340c00d03281c03942a40c10014108010040079171109c001c003150000c0c080c40c1101d05001020004130b00c0d104943e048030000d491408420810181e05004441e4031030800525541981804c2c0e502030801c510303c1074020f085113004602c0303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 248528794 1250 248527544 248527549
    0x4060f03060305010e0a060f060302030c060f0c010504120e092701060512070f0803070b070302031e0103080418061a0a11150f060409030e01111e0f150412030506 71
    0xc00285803c04001c01c20010400791866403803100c09421203c140c1003140601c0000c00900c2000200e030740241c00b034181141c0138820003201c0d50050107806450002070118503010f410908c2107503c641d118900c100000420240c3c0540240a003480f0b441c41480703808100605801c6903040c105440d5490466814040d1004001a0242c04560003c5d41c01641540c5940070100000480034100c031070220703002d0740d2179444601064492040c508003030114400c202c08165078030300ca41c0c0150340c8400e400c030607802001c1440345180b05507030080c0d00c240d03420b140114040c48035404040d0311038043c1c0342000040160901d0f2900e85800004800d648400c2e040c03012032600365084c000c17403424002c915110203036845e0111300c1d8048070b40c61205981d001190030308140007e0103400c080c41101042a0184c44030200000382c0001103c0007621107100003042d0090305405420862291400c041a10505000e000c94051032901d1a02d4190103489502010380c01200f40070114113281c0d80140388030700307515002c035040c7d031090301 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 248530044 1250 248528794 248528801
    0xd0c03170f1201050f010c0f080322050c03010c09030b0f091e010e0705040204031121030412110102060c030109020c070b04081c09050f040b030a0b0718081204060f03 73
    0x14022003411000820b020030309400d141650503203000315000c0340701c0d088107801101c0e1188a048000c00c1c07a003002c2e00c2500451003c0011b50381c00700030303900c50842d6400c036464071408842c01c0001c00c40c0c090340181c0184a03d49001c2c019400ca00703099141c142020303469500d03a045070300340140200c8100ca280c880858225101448020011168a000312580c0d0500081290013085c507041c000c1054018081c0200c0c00e0f240c03500885003200d401168020800000740204104000e842440c00c43c84c0d8084400315448010a0001d000205000400d40b540700d5058203001c4442e9201041c000d04541000c4104284101c0010699055454160700180c1310a524031485203042c0c4d03290062102d000001c6000600304100040071400300c010f12100d0045070680e030805440c8030300940101d070b6200a58401c0c1e038100d410103501460b0401d50041c01c8500482c010f86401d10711000a0300c0201c009200001941445541180c450004095010042051082010800d841030040d030245c4402c0090320408001c17004c0c801e80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 248531294 1250 248530044 248530057
    0x604050d050a0807201509060c010b1e090901060536010e010302100e0102030904020702040609050709031b03020d020f190603020d0c0e13020a05070b090303060f0d0c0317 75
    0x107a151342d94804900b003604a044d0b031001c00c00c15a080c414044502420500c0d081d10340e091814000c40c0c01e04051004001c2d094204c103642060665175400c3d10500b99070307450b04a240c45104074038150200b8540800740020110018004400d40c0e0410008010644801045844035a80c034480c01003603c8580182011202030b60070508000c8444200106110240200c0c0c1c5040328402c8484e48264880514191002a21040b107940560814421440181003580003404520710050000030342e1030f115441d0004441e401c2e00d42000040d0120300900400003e044072030b0240c10790030503010381d80c1d28643c005103800d500e45000900640b0b030090b040d0040c0d2141c400b440c0007108002c250401c156100c13400240290440e011542181d428000003c1e1054040d00100003c1e040141060000b855a0211032000c0c2d440001e00d04d080140410551011442c94001c032070242682c48043c640e2400c060040004c046c0092150f14854101c600c101c1300040c02078a10f500440b50b000c00c0903040304914903182c005600698 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 248532544 1250 248531294 248531303
    0x807030c0f0c0e070206040b180703080d020904141506070212030711030c0a030213240b0c1006050d020d11060f0d050c03060604060e0402070c06020607080a05060604050d050a 77
    0x10400c07004000c6603401c144141d811064000c4080c4d0f0342c40d03104980d1920305440141c08644e40b04049600c4505140c00d80800d1089072044681550b43ca5907400c0c107a5000c04080288a503012880018a10346401016800b181d4906410180d080a041c40342c64881001d507110b100e803000280c11800c640750242030800c40e450400c03e99403100c5050800c01c09504200b82054030a010300e858043c07451424400d1803069030780183c241106200005640c000400c0300c0041907144000f40652103000001c0d08001074080c00118103510384400c40400100d1030318808081d811100707420300c5024001d235150307080401c8401c0d4049a0000f0500300604114216042e07034907007030383c200340000b607043c510030b00311001480c1658642200b005250707190f4503511141e01080c1c812070380c0710004100400c41c0354400c0e5507401c14228000c00061602c1c46903070700c1e801d1a1741658001005604038604000c08550003144032070f1701040f00c0700700f40042e10300100003541d00d00c542c1c040da5202d0042101e203002032100c10040c805486610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 248533794 1250 248532544 248532563
    0x1506130c0f0e0405011d04050c100207030510181b05090a0911060c1e071d010e070f050418060b0309061008370204051503070506090a030807030c 64
    0x109800244181d501100d11004107080c464100d4a9042611900f0304071003d00410f82c0782c4030010350141002c05005881510300c0d00c1203021030003ca6403011040000f801242d0014040c040ca0341c07030030b00d08058a0322444890189410034800400c04481000f40b50a030703010081035160000c800300d141101e482504000d4100001c00200032043e0550391107420054040e1000d00e8442580008220040c400c5441c440c0709500b004180c021803c42c580703600494003401c0800e0728606038407504103000060383d112140c01b095103210700400a55000c081c40135003000d00361400380c1c110343c40c500010340a40f14500c603210000108291104c1c50320b500b035116a001d401c402c40b28980d241001c03090303681c0e00c0f081500d0201d01450801e400103840703c2c00044c1c1201c007034a000c4451291040030010100c5070001c00741d60800348002e004c44800180e0301d80c81402d11402c8001d40901464a00005240c070709501504040e008240070011400240d46142160381100d50215001756991050318003100e009450400c0103003030086 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 248535044 1250 248533794 248533811
    0x203030715020d0f050c0a0e030304081207030801050904240b03010207060207060c0807120c1739031b130311040b04060315090201021c0206060306060a08150613 71
    0x80603002048000c181c8001403010013808402d5104450040c0d40c403050002d003c201d000741050281c0b220b559a150700805480c01c1640e0b81d40b40605090000b001c01440780c00c00100300c010113801c6901107000d0301e02130f1459502403800d03944040c0c0c012000a942c6c10807624811288014005a0b0030580c6074540160095480d90030a14084000c1e400c940c004135001410100d200f034003e4825203010340300b854aa07541b280d42295461040008121105440d002c00c8901c1c00642141031080c1811130044200030031a11014150301213034000f1100114000681191a411082c4142c0b0408281d030340010410701c0e5040705050188544059106403904044c411004117000410300c81d1200c0382000e02d03c0152002c0c0808140380003017004880790b500004020028000548056203c16031001401c680b0600440d120320b00480743c0c2484541032110941c0043c0d104004012803810140900c1e03410800c142d60500c0682d007001c2045454980804016101d2200d0f8000540181d8801c01e107140400444a005c028091 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 248536294 1250 248535044 248535083
    0xa0906180302030d11030f130203010209060403031107080c010c290412110628200c0c030102090a0e070504050d08030f07020c0303090f0a030605010e1803090a05010c02030307 77
    0x8220b510707940c003051320701800615200151780889202d078071410b400b60f07256074501114802d440800607041c1d07015907090041c3c50054941e00c006202035030007a00c2d020344040c4040711181ca03150461300001c01d2600f000403c0c51460342c02040550352558010010700c3c0545a0105a944101101d0f2204040c403500c00180b1040c400440740c098000f040c640e40380218803024080b115036038030b4103943e008801000550380c01c030390801c01a0400c1d90780ca056840807401c2000f43c003600d00d9100d26440030090f50a0009140250040b041180f40007060042d4000d40c18594444001500401540b146a50301d00c00b80001403080b61040044802503c3c000f4103081d1303456001d040040c0580c00c125a81c00c9003007031803c08102c26a00000e071508041c100200110f1500b0301000c103001c0002d01c00700003241c0180340440007000003405405440e000c0e200703500800380300d0710344808480e803000c50b446801405600100003200590316100c02d00b03402d0390000e092100d0812680d1000c2461032250a0002e000e00341c40d89034000004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 248537544 1250 248536294 248536297
    0x30c0e010e0f060414090106020601062309040c12140c0d020a050c03070303051005030319180f0e150109080709051504020307030c02060105060c0c100201110301030b011d0601080a090618030203 85
    0xd170b10a0b1170522080c5c1e00c601040e80d56800c01c1c054a40070401c641c3c444072880d00c03500c4040094025503480d15003020b426901081c1507518841c2d02401094490f40c00201e01c03151482143c1c500c035903140c0c2d0008a4104002e0402c9944944841b030511030760001010450180100216081a1010007c880e0b6601076800e0080081c81d041e1100c89204418180016091400005a5540e0300445001d001c1a0700b21680c00e4a481d4202910307800c203a001e02c8000140700c0e10801204000f0040188060424039005245002c02c185200d075950500203440c40c14800058000355100945815450000741c039102c00009500000e0110740148e80a4000020000082c4d4140c018840801d001d400701d400300e0b621101000075500603484411242d9001c41d00d000382501e00513074103000c40e105500000075050520540d81d10203038001d030815504110b040c0010040c81c0c1a08035905200d0404008010356410000b00082c00c05001410070782015898069800601100c3e520144040f4000c0c10888400411031070042e449 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 248538794 1250 248537544 248537579
    0x204030b010b0307020c0d0c18021306091d0403122903030f070221060720120a0e0f0303030a060602010e0c0f13150f0312030c0e010e0f0604 62
    0x10344191000185550b9034030280c0e4002e0307419030081c0001d07140c1e180c02e101074440300b4001aa07040c00740d402c1c00119201a680d9000e0350940c070000150380c580c00e440910b18001c40e240d1218040180c40031082102c0e8841544140d101120080c10604a480300e04044a0b03204501c401000c1c032920b04a81d082100c5110306041030314618109989502402e04410551a0f00602b403a1454144c4100002c100501e8002d40080095914039240e940c4032145d903241511306401150711602042034140320642602400c1e610b60300e81031222000b4040c040a95110b001e071130060003400014802c1d04141200903550f140c4100880c180e010342241e880e49050b03100600508010701c500005035103400011210f502c0041000c0101c1030010b000500c02d42d10304030038030503036242c046103500109079200d0381084a4183d850b6686c00420088103004000c07402c50500d03007110310214001d10107151a01400030001500400d01000d400024200518144200701c0461070400160381400c3c2e00550008010807800e0291400380407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 248540044 1250 248538794 248538803
    0x90605030d0201050606030112050a050d0507021903030519050d0903030506130902060304020f0112020a1808030c060a021b01150f0b0f120a06030210020604021f05071b0506030a020403 81
    0x107007004081c0c0a9003294415103005800c40010001800030402d0592038200d550f1080085503c010f45580b90540bc183d040c801c5d10001590014160040d0304e4102d081c01980030204043e0307681c1d14556900030340244542d00000f404010340c107180d2216107000c3c1e000c0e14441c0302d00900900c40c1d050b55280c020b004001c2100c200f03115251b00469091000440c0c2b081b0441d4641c051f004510f1500c803038003040702410b40c101250f41001a03110340c98004420314009009c1103201500e803803030310a043d5084a00c0d1090b090704161510780c0248800070300410001101600020030840c0141c0d21400384d100704480c0200061120025801c10040745c0c02d1850540500044a00c4d140d03000600c80d403124048803151041d2034054600e40d00c02d111035400d20144520844c1c001d400d1010000e0301c0e5a80380c1c046110300c00e140041e8005604144200802e506200510603480c1c0d81d010541c40030b0388805030f000344c51802035202c068030324041c0104c5290748421021104014290003411030741c4030702e80f49154001a501c18001101c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 248541294 1250 248540044 248540053
    0x10030b07051314060f0403150506010c1509030e06040e061e0607060f0f09050d1812030e0d061b030c031109040218300a02010206070f031509060503 65
    0x22031103480780c01594140b00300054082442441c29115078020315503074a980d580650100403030201c010f100001000151b00c01d86501c3c0748007030110604021100003d00d02e40c1407061000b0710000041c0700c015030183c280c070b503440001001d0500341001c5400300c042c603204580100c130020b408a07038001084582441504226030300705504400e102c1c10041c902c020707680b1540000d02030142e140011000e13001841c2d02100c3c0301c00050501307985c4c00d00c24180e800107007003030300c40350442212410a56840b95035041c103213032100d50b0340d0600c0341360840d04104200c05031400f0701080018100340c2c1240d56103111841e56150010760034000020780f4030181c0419409040201c0c00700c0d10385031540b8000c0c0e01901603c1c030780c0308141c4c090a042040007000c0c07002a40c0031001000c1100071032407000c1100d5983d00d5050071443d0074100e014030200075401c02056036070714103403490000d82d000890b4140184e900060141e4054054541544036585802080d030151400822011500c4802000451007800c030b0b602900031118200c080700e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 248542544 1250 248541294 248541301
    0x130605060f030319050c07030b0403030c18060c060b03030408060108150c04060e060702150a03060e06091501021903120507320408030d05040501061a07030f031410030b 74
    0x101101c00c1c0300100e0340540003841400420804d0001c1e40600c480c02d0b040c00f501e002c1c0c0706283c40e81080c0e95034200f1906549408248000d065151060b00301e00382507414010030000c0500c04058442150348501001c000d103012050742000b0143d0041002076401a040f20b8580d5190006162901c60034054a1502d100f10883c41c0366203004800054018120107101500d0f241c00d080d01114a05007480000c0d400c00d404000f040016201d02d140001c076030401086090312080c00400040603100e003507100e034208440b840e0130b000066aa03550314070b40142074103d416520440c0380c0c00503070030b12449610003214046507c0041042c1508182800d0008984441c00c1013156110710045d00d049052805854110004510361150034810400982c20603031380035000340c1019600c164445c6154489817000380c41a03200d00902040003070074002c01002e4032403520102401002001c3d00344040c000c02201404200541480c1440103000c3e0740401000f0f0b075107080303511882c80e025000c0340140c50380344000c0790503031a8003002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 248543794 1250 248542544 248542549
    0x30103060203040611070804060e121005010501120908030f10050d0f050114040f1b0f080f0d0e012115030b3921240603010315020309010b0913060506 66
    0x1b102c0002c4da01502d01420315042440494400d4814800182c001c040b200e840c0d81549010456040d01c4001c107100803d503581810001080c0340a05404015210700302401c5100050380701c020340e94040d4001600948a03a1b0714103c01c000b000702684120b81200c0090004001d0051440c000c02009000d100207003c40c0003c0b10405512440483c1e025040000d160789040000d03480c01c0d000080f14410851840315075446030007d07074100d0050b512000d03ca901440d81c080030b9100c24440f050807149141407120a4500040011304011040c07000707546100d809031030b8040103a109a0003601000c08030114550404d0301c2e0b2601701030454085e202c1c01c4000503001c529149401c020b15011001c0d000c000e9034200e680d2800e81c560511900015400b00121002c0427441d511a100d22410350700c51002400f240040800c15000b40d05e5205141d501107000700d104000600203e4038407400782078403140d07a4078016601d40d141404031340100030003800c43d6840305d6408103000764100408107080c0014024101080345445081c00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 248545044 1250 248543794 248543797
    0x6050105010e100c1b060e0a0b03010609260307121d01091404020c0d0224060a050d030c0f03080114010306031104020a090312080414011503080c03040506030103060203040611 77
    0x50150302841003c04100350b03500c10401c403a800e9108000108403480188030700c1c400c42407a45c2090001890b8003038406138910b031800e8a48010034004401030b1644d410194001c00d9002d950059416818615502140038840c1140d000d00c0500c0b10300130759485030980d1424600303403400386039500b00194541c9142c402e01056186418018101611a90040e51070722525603006611402d0881c0e00c81e034240304040a600060052a00440e003ea014000185094900b06c1c1d0000f92400e41a413031444050810500f52610381c0c3e00b5082d14011a10201003801900e0215030450b0034240080c6034040c0403020804054119000c14142c0f00301520044400003c84011004c44210744400340c55015403804040c441e0500c1ea009002c2d0301c4051030012007441d240d850f240c10b40b400d900e640300c0014000e038040209202006e144201340301d480900901040150801e4036100c40c2c001d010141a07080c0000ea1004400010404c9030000c2c4000380c4019260340c1d4a00b0007a009403c2203c055078901c0c1000ba030042c029002d00c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 248546294 1250 248545044 248545067
    0x50114030c011e090302060f03270619061e03061808031f03080a0f020106090c020606090702030d0905070e0703150b0f0d021c0b032a030a020d050a0605010501 70
    0x1d5612903030001c0f51100b03001882007001818107000d505072011000d0303100e02008281c1010501034071541c1c2d05001002c000c1f266851380346c1700d20b4403100811808210b8000700d1241d4112001140c40c0d40c0d03080062074118000c00542c0d1014540c00e03d40c0480c46d000e603213104c20050449000e41e2040100c1240c00c800c3c035031007174104d15006100f10010000103a006400005490801c81c0c986800c28034181c0700da850100540c803081300f0001141c011480d0380c0b00b903542409604042d010f030341000c3c00b003041030881c0a940e420010b0003030761055a000002820382d0f4400c00c15507a1181c2401000c2c0300d14102410540d80b0b841c41e0b40203080300604405d0004038454020b00810101642c001c80718240c181c0b401d127102070950003440499020840c10411940c0000050010b4040f00740740d2a01d80b07020300380080f9200700310754104040e10f009070001d0146609100344140302d0010014205124100003800034002070030604114402580151428031500c18030800107091502940724103410002d50741c0740c1005545036110300c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 248547544 1250 248546294 248546297
    0xe06040b0702160e040f020402030103050a290402040f0f18020a09140c070606032009070905010503070e0102010905030703021e01060b1602030c0904060209030c12060a0506011701030501050114030c01 88
    0x80344100030705031107903074120740c4a8000d03413006c0c80000c1103038006426640300703a1041c1c61542c000340901c5c0a000d40e007803111001000010720213242149100b01104050303070081000e449150b440c0307400400508941c0000c4203180b0304c802c003004001c2c11644c0910784030741240d00690041c03400300408595807841d403040b005500f92141d00c541d03c969880c240d12145600c8900b044a16949a1740000001503e110300c182660b00f0001c10030200941c220140000b0020042000c0f041040e00d180811050f40c0142c103ca4108402c1c0ca4207003840824030005034054607060000401510001809006241c0d002c1307000527650111604100d50f502c1d507000b46900303a0b9502d026581c1105400c1083c41d000300c0c4214040d042252019003a10071302c030301c140300052500074202e0b0150b400c81c6e0001011226803405102084000c10201d4580c070541c07018a1441d0b075250401440390348003c0e5584046882030307020300c640d81000c0112700700784452503859150080c0602001e1085800410214a450780103107804151601a030406 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 248548794 1250 248547544 248547583
    0xe010302120702100b04060e0f060a080d02010f0f090f1403070503030c0c0f0f070510090503160602071203080402060f0c031804060f0b07060c11010f02091c0b0403030902130e06040b0702 82
    0x2201c06104274440080e010690280c00c4840c0023405e400107110300800501c483d00001454180c80c4541019035100c4c00d180c150040c030708010900018000322032100700360307004411a0607048080c0d1300c1500d03503c9407620107482c80c800441000034000d034040c02003c22032282d90643d00c0b890711900c0801c1d0303584034010701e5804681003d14140101d0900b003003c482c00b8802e070b281400000c0d9603000403a0800b0f490101e4180303561070201d01400001d404201503401004185c1b005000044035480080c0340fa01c2c05440284a03540004840910039550f5055031080f510784803d895441c0002403d0280c144105036209024a043c803000060100014101c01c0c111003002c00740ca440d0007007690340c20000b05241502c540521081c503000340740450f000d104d0400b408014090050765911640100404460f080c130420074900003580100c2d0014491802e081d03009941800c01049610107480001d1440c140319201b101c0380740c90102001d00c80c520018a2034000c50181c105552541c0f10008103e03200c902005005560004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 248550044 1250 248548794 248548801
    0xa0b0306100e070903120f0f020d02120c01020f040f15030c0807050c0115090207170f04051507080313060b04050403020615130c0503070f0912030e010302120702100b04060e 76
    0x1d2180c0d45a5201d403e41c54904121a00e03540c40d80300301210a038019002a041e100c3c2c3c0c00fa2103402030354541c0d400c50705000501824440e03405c000e5603820a1400b01c01c0e0028040744400e034080094050710b5406c61a00c1c00c668845031204120b2850300413074428031058100913940513141074041c0c0301e0154001342a079a81c15491f505c80784c00340ca0650011202840c2c1d5960b0741d4080c411143c6ca6200000680140000940c0c0c070015410048440c210a01c48050050b808116041d0310501040c112001c45809036800720a05c0d038041c041a1203400b1301d10024243ca032000080001c3c20070b05030076042020b886480c040080201c400180012100704407030082c05030740140041500c181240798000f9820703400807d010240070303203014620262007541c43c8100224001000307104000e42c01594000203906c10b8a081c1c12000c1c54141d485036045e078404005400c1c40340c92110204282d2194040f14080c40950002d01d810f0304001000030741c0c404c0001070882d0907601e0959008101c0c5028001c0c0d200f1102c00e5141540d0310f49 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 248551294 1250 248550044 248550059
    0x90203040305072004050c030627060103091506031b14011220070b040b0105180411041b0e09100810051510030c080c03040302191b08060a0b030610 65
    0x700f504c40b44241c0c0e10000400c501e43c4d0b500c03030040038810551400e034641c403414158140400052800c6603d64003641c2d00121005400f810b04406a0001091034041100406405e00050704038004600c1e48c0000d0030039070302105015101c0c181c0800c071401180d250300030a69a404032070320088003a160a000480360181c0d1a03000b2000e07085001d80401700e280203400d4000502142c40c403603104010495031a0303542020401801103145401d4010102514007000000b40b051072800b402c50000c100070004509285841e54075221036128200150300c0d02e55004114014000c09490074804001d41c510030507980380052400d282000d804400c9803075580041c00d90303d400c04501000360134010520072030b4103501249801c0c00d9070b401c24880340e80d5603a070302d00103020f89043e01d0040c16105c00502c45422b8060400a00002a50000f00d07482084801e091141220f035aa10304a51900c02000c182c4e90443c1c02501e01095081c408078a00d4003400e00c2500411490808809141e201e590841d030350041100c424000300b1411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 248552544 1250 248551294 248551313
    0x908030d09060612030903050601091814011b020105090601060e0102070b03040f0b0c0c011103040c0306050411030607030b041803020c010f12091a0a0b0a060c030909060b03060a09020304030507 85
    0xd8400e9070007085482d10384c08805030b507a15688041d00000c6110408006000b410b0069602600c400d000500c0988000001520b146a11020080200600030b846850b813440c20350005007100420b1403010008614140000d020f420240c68000c4540550800011202c3c06081c00f60080780042e0080e003d20344c94504600301641001308190340c050007200101c8005441c50644500c113110140ca01c584030341d84042007600f1903000310061092080200280008100030490403400c41e680460003141581c1c0341d10b01113003080d04444105405210344400d100d8001e8240d0800500c01009035004c00c0301a003100381d03540180000c4100607026030024104141c055101e00d4000c0303072001c81c5003000b8160a2071000c0320800c40341b0002094600d050314180d000c080c1000703402020b03005048010309001800c10080000d40060701032040705e0510018031108005c250160500c8401043d9160341080411307030b50000601c103540300700e9507030303100b00c9019101146081e890300c00d6a0081d034060362860300b400f0a5031b4541a02 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 248553794 1250 248552544 248552561
    0x303080c0d150312091a090913050105040b0604241a040b070f0b0604050415020a020a060501150f0c0c1206092103060b0a020318041b021c0908030d 65
    0x22602d4044012040b598005400e009600c00c8564801c07811a86400070075514840d0410a111910a821114449040020346200c610110380303405050710b5400120280d001115401070482d404e000c108030521643c0344109200700c5058900340821f000550941c841100d88480242d800214a44e081c4000075643d5280051040700300703009803605494015462158010303400071680000041400310402001200154002d0002c0c0e8041c88242042d13a16102c0c1140c0c400c003034400eaa42e010030a4980e032031003004000c0b451600041c0030007103940c594101d40c46c603030381d100c130000041441c4043c0080d84c0f52156903010310b4190096031100056040410240004007003c401380e60302522614164045245040c1403158001001c0085507092240d030b00140503182e0981c01400800030511211004903000300071284480c5103020381c040017a2511000034010113204901c1c1c0c40c65810900c5280f00385030000f80d24240303074000500f41541d0680101084443c0303280f40c09643c6507030300288600c0199248907040480b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 248555044 1250 248553794 248553817
    0x103110609090a09030e0d08070512041d10050d05071409060306040308060d02041a0f010e06090f040207060212041b051005030901090510090c12020603070513050411090102010f05010303080c 84
    0x80d0000420010704c100f0084d840a130350402000270740d0004c200c4200202c54881c3c8400e0b940d03500741441c00a031485160072040420590f14203160001d030140b2208d02200c03001c1d200c000c0c0302c080c240001c0e00345142e80e0701c154050040103281441d00e2200619120540610604d4002d0090400d83d460395811a000e010190940e500201621a5400143c1c2c0324020801c0c1080030941c1c0040265201c01005241d01c000f100d018180421908414041d4443d41d08840d5031050941b95500301101181c0031600170312500f000608618404540201074040a1048901803030060302c0410300b050300c80460480c2524140704059009565440d20702e166800391000d590700288103000003c03090030035281c0e40e08240c0c800070281da51b9555400c2d00820003000715030260140401d0080c009a000855002c0f034042d00c8040c000400740310000c242500d004580b43c0b56400680801f510921264201521652203504101c403828055424209958180b140d144201c0341201d070035980315420340e01c90034403070a2681d1200e0704400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 248556294 1250 248555044 248555057
    0x312090d0804090f0f0c0903020a0b0a090b071214040f03030305040807020d03020705130203150103022503031a1207060e060c0105010f060809062401030f140103110609090a0903 78
    0xc40708807504c00c4442d0028118004201942c0000149080740c800c0e002e210306004145000f400543c652018180554518500d156a2800340001c29100000e26a00240314000009030810810805000d02120034030a502c2d81242501d10712011003041c0518010103510038040007040000c60f100340c00640e0800d0046151514116041c4c0200705e0259006030241c0250b44058010481c0b070400b801c0007846004108030443c02d60030011403841c0c00030064521181015000700d03250101111444050070008030f000140b650303d002c14600580038018a0741c800030003500498040ea66424031034102c0f50a0170091380580511401c0c41020f580045040c1e6116410003414004099000401d10400e80641004031a02664a280c003900400b078810040000e605900a0301c140174003500700203909445501c01d2000760070b99030794002c0128020100c203241640703120304203c60742582d0000e00c03c2c40781c1603034001c540318850908441b080c4102d510405401941004a0b10001650301488e603001c4103c45209182c00c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 248557544 1250 248556294 248556299
    0x80a0b04050a0b0312070206040e1506070302010b0907050406170a06080d020105090f030408060c0304052121060f130e06040b10061403010521070609060206060312090d0804 76
    0x9080701c40840e0560380550350380e83c0c00542071900700a43c429509810000d00c2c0b0b49140b42c0d02141c070302e00a621404074540e1006002c2081e0f00c00b5603041ca180b0010103808180c030b41100b401c00034080c09403d2002809042c012000c20840f601c1901201c050b5030154540c01e0b601c0400701c0302c01c4510b007002045401050794580010485007402d00c452195650950b00200d40e6040000415042031051100401d440d4401c0100f080361f8100030400b917a206100640300c6440c1c0e40c50f410000d0900000306034040c42c480c4582e81155900c07000c10080c280d101910410131006095400000305c0f03071a0180c42c51036209074000c85d80c0d5040e181180c6d0f8202400e0f8404000300728445500302c0503250140039181168070119040c20859243d142d42148402810b00d803a000c0d50700c0c41b0164a0011074401030040038020445c0c0715450381800c0d5801710b09140b100c894400c8441c03d0780c0d1004020300750b92850082d08014015000030a0f014500050121403003403a041007945820848000c12544006641c000ca40700e10b41030000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 248558794 1250 248557544 248557549
    0x140c0c03010c0306141e010815030d031a090907170c0301050a060e1e0601050708070f0c06110c060a260f0f0708090c01120612080d060f080a03080a0b 66
    0x1402035826060f00d01260142c2407070000030b16948800e0110b1301400401e1006410b1400da200d0305c245240c000e080c00a06511242e4503032440103910a1600d815100301d100400100b41d05510101000001401209140d28028200b150790328068a1100c171551111105229414184480c0b0961004407012294404d039180082030a550742103070880c2c90681c0e81d48040100380d0407410314540c0b140d01c2d07000710860b0414004585030300c18006070000d0304200d0049645030421230f8030421504110f40003418403401020b546402404080180076070030000c0c030400710344408138000058241c03e0800080c911030800c81c2d4142d0031103840001c0c0108103040d440351a0a02c1003060416203042c020b800060104155180640702c0c0700760044050189010040b1b0401044419000030810701d0564034240303003484008244400303840140c001ca80011462040d800448410809000c0052444009104045c8003030b9a89001d4017454040c14800e10070307160010000d0500082c892140582e0020303d141d40050081c40c040003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 248560044 1250 248558794 248558801
    0x905070f030b030f01050a0203070906050c150403090506130303260402060a1404090e15090a06091b06020105090105160f030905070b0315010305060303090a450b0a0303140c0c0301 79
    0x10003280c01f681c00414804420b5002540d00d02400c05800e1440c9000002c0e10000d5480c0c9051f501849e0800b400d00c01310301010311074402640102401040c03c0e8482150031001e803602901440200d010071400c40c95410142c0a14a0704d04070651001d103002c5003a907580d024090740b0ba019841a800304104007400044c05502900074201138683e011000480c0001d40c441c1618000040b02284d051300003407400c1103c103481c0083e0600b071b001e6100d0000f080c4520a8900310384171090075a50407840048510010500750750541c4180c0c812031810000f4032081e22883c0c0c4144941491015000005080e243d08413401d074000e80001032440d218000322080301c1e950f502419503d81041c3c4507004103264000f0300c1c841c80c0d80e25004042e040f407002c0b00030350325014512001421109aa2107039091026198000101c0f8120032003000e076100c0c0c2d801e00001200d40103907a0b04950100743d002101030041c0f400c0032002d0305003000e800360b1095a81c19241c0e0421100200f20074003468208100c1c240452298a0b02030345a40c80a01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 248561151 1107 248560044 248560051
    0x501030b0a02130302120d090b070f0311070807060c02030f01060b0319090219180515040930020c0d150905100212010f0905070f030b030f0105 63
    0x2d100305503d003181e50720182d80a2030148400b4561980402c3c02540540d2a94420709400e4683e513040402d4001c180c005410415500c0e411400680142a94105991002c00301d840c00b03030b5a40d8a01d031800116400c180b0001307028030702140841c141006125481170f00b1000a0000340d0038a51b02400b5800028540741c0700402c864805000c001e150341c08030515035005000031180c1c0d03138150301c5000e01c4501d901c13131000030360100c00c8800441d010500c5858040c0e264100c9603040211035104001c0079103443c080c1900e80f22103000d9440f4401a440556081c0704410401454880d00c4803032001e42410410020f0741d018050f8200501c00281440b4880055050a04000540c8010500340907190041402c2c503001400d100154211100700424010b43c1264a100301c514149a03c48801c40142d40d0203807140c10100d8a00308181c0c0d207aa01a800580d0001c101030120ba90a00180300c2090030354005a = true := by decide +kernel

theorem cover : BRFrame.Cov 248381294 248561151 := by
  have h0 := BRFrame.cov_init 248381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 248381294 ≤ n) (h2 : n < 248561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
