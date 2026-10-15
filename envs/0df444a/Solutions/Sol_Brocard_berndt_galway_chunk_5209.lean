-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5209
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:06:17.563819+00:00
-- url     : https://prove2.me/submissions/87ceb481-7a54-40f8-944b-346592a094bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 936690647 ≤ n < 936870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 936691897 1250 936690647 936690661
    0xa12020d020d0606090608060d0c0e09070810020a0e1225030c1d1806072a1101080a0209090a0c1b06020903010c110304062d0804170909 60
    0x350468049100e84540800020240007a544602005000d40d41c40703c2041504100c002090114000c1c40f6901400181c4881404106840c805004031006104904c101d030745c0310421242000e120b0f50000700f07684150740c4140c00c2d0712100e4000c0c10140d692a038541d00041855400c014a5184e0b00c0100e10f0250410020000800304946c0d90b801000790240000c190390b6680e0740c8640006d28541d1107824081288240504400c0409400c075070440b40d045c0381592580b242480b80c035260b5a000d0f00250500206400d08070080d225151050300c204000c500d1541d01c00d030b031401c0c104420055040102d0001e41c4640009102c54444c0c03081d1070900d04058034003111036498410903001420f01d1410f090502004015640039a42c0000080044900c07034280540c03903403200024103080d03a1018059406000c1011800c1044103000000e0b03c00700c44130303843d007242d0403403549085078540c03407402a01585082c00080c801d030700c10350000344203030241d0302c100341040020304080051145400b915100b964814a010081146 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 936693147 1250 936691897 936691901
    0x36080307050703020a0b0a020414060316051c1d0f0f0a03050a0e04020313052415012007030302150402010203090d05030d14090f010216030f091701051009020a12 71
    0x20f4460300440350302190b01d0b11540342c00001292291421500003d0030701c2a00401c040d1a0401c0c00159802800c5040c0842c54500000c406000300f070400c04081a142900c0809003403080741140e05a404212101007406105481100350b001e9882c02c0c802c0e003080c150b07882c4001890595002626001e8015056103642c00c45160340309040c1c0d40c042000c220f0700100306540382e100070350288510032581d03070002249103072140c1441c4032940c071400ca140a8050b585081000040010b07403100940840360300e02c0c031481c001030320180c0c60078402500b094101c80c0e80707890403140000d80c4400d5034003076000c0f103c183c1c110721484c2d90342c2c1c1808c945c020b005800078000d00c0c075a42045140c8000c2c0d18071070420b5034105107140200c50102d8030420034003044140300c4d8080c04030a42c814402403103400780290003545007801d907210b6a62080f070305450040800c020000b5240c5c006100d0964400074108407488a90041c0d94000030328040d1000303541d51440500024400944010305100720f540d4898240c0b50391032065207604880d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 936694397 1250 936693147 936693157
    0x61d070b0901121404030905010f0e01120e0109032111091e1903020a09060b040312020a0b0408090103050f330a0b0c100e03030103060216063608030705 67
    0x4103002241014001c00d82e1240144e031040e0441e080040f5042c0303028100107000c00c0044d400303a410300100406601040da8084841520f12900b802d04027038190400720641d000308110420107006d5460000c8200826074040180c1e00d0030319000e207450261a07a003a11180454035000c1009480001c20400310300749040c018039000c2224501c401a20180c90142c0100c2c0c1c842d181c01c21907010400c12020240110700c0c0403403841c00504080882000024108180c102c4548182c1c0000740c5040c2008620403500f078801c000c610703882c030743c401000c1c1d41d03d080c1860301030901d0b081244a9401b0030b082c180000c20640c0c00403c0e442c496900b0391120031201710403003e0344880c103180c40000100e1419881e10400d9940360409000014090800b070f1594031610031899504251581d40c1040005003050054015144000160ba05581d040003006a44a800c0411585080e03c2908010142406c10003000300650041ca0586688034070780701d05001402d400c00c030304103580a00ca600103040040c10f00101d59014810000341c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 936695647 1250 936694397 936694399
    0x2a090405070302070c0305060106090b030f06060f040f0b0316020a120806030a0219170307050c040b0105090d05070608010503150109090f0203030301080d03060918031d04020d0504061d070b09 84
    0x1807510728203031980300d005c0e4425081a60b02d44e02c80801000116400f1100000074190b182c41d941c00d5042c40080c2e85130015003d0300301c42c031038203002c5000e080300c000341c074129801052304071400030003541e864117004c0b4290803c5480203040303040c0300ba89280150000c030f450920b40d640300c2e0f45c694181085040a94901d2805001d0329014420b0365410f07001a1200d40400c20640c0c2c1d407400c5000710354500000f6030810a000f550b1015260030500540000610018241c507281d002190045400e104017001240c03140504400154031aa000001105201d4080f56070030507690159920300e41680c8910a2581d81e01054040ba01d1042200004200c003408540c041c58602d480b42d250000e002c042900040d1958100f0f070490718554202c442c07100142c0e9018802c0c50b009000c0b405060191903401c82e00340d01002c41101d005404d01c4180545440c108010b41103521070311100600071501d5188401a800007030a084a04803141480c0010388000382403103860b440351840040c00104025170814242c5449600061005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 936696897 1250 936695647 936695651
    0x3020c1212070501150f08030f03090c04020a03230705070809030703050303161d01140c01060f06030b01020c040501050906060d18060c020d08150d0507080102030f2a0904050703 78
    0x11064204a034001026210f000e00e00219036064040310840000d80d40d03600210500140140c10050490007200b035806811019080c0c2e52aa95200142c0d41070182c0356003074940c007900c0040c0e02101c0d03d40591110140c81540c00c5868080c0c8100324800c0030492003030b10602c3c0400c0c000d02400001404100080590450140580304a59500c3d80c85601e10781040e10b10b1414070041d14231144d60113600541c00340340c803a10304504003001c440c0840080e160203c4602400d055050018410500040035000b0800500000c3c0c0c100d41001d50b10403009006100c000f58240c014020300d486a465481e0501501d4186c500c01000380d030941d150081000600d501c8060503000303240d21340390305110300680c10a2019200d0f000308401329408060703440007414000603481070030034084810240580e404650342c00d424070301820b175400701b821800b42c20490300d06440d0b540302d81019800001041207100c0c11042c1e00c0c0c01081008078003070009007902055180300410241800c0c10184c02d200e007020f00d02c1c0c15004a9040100345c100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 936698147 1250 936696897 936696913
    0x160c03050106060e0306090303010506070b04022808122503140705030a14030f040b0705160c0e0601141608070204181b2d17010e0111040303020c12 65
    0x14142960615845140800d29100303403012617080a00080382d1225039600694510742c1880002215400b0b000d03070280040d24203000060071034949001210110440300c14601b00c01444a51401400419002d01207860003000000c00c4000f040005840d500040040c030310480034042c0e00d010700421031a203c15004c015482117002c81100000340149041409000038503655a41a84d01414629038409240712a0b0303010420014a8600d001c0c2e06500039030f0104a541d003584410f002115075008424003e222040c035002340504000c3d072110713044229642e5210721718083d80c1d031400558401080c000c2c4038254940070400d0501d100c400042602485104100003810718103da00440c04455002041b0099a0825811340c0d043c0808403810b0583c141c1c2d1000c032202d00b581405000c010308041c2d82460580b172801e640e8104240c281da40504000340212004c1c51102a4020410320b0280407044031600d03240d4681601d0f0b140d01c2100d81d048500361398143c0c004040301d4003a21b050142c5400d020103d480e060080070a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 936699397 1250 936698147 936698153
    0x40501060f12061103011d04110402120f060603040f03050a02010621060609050c0406030f09050d021501081b0d05010e190201090506040602060705161a04060f11160c03 74
    0x301100030305803034502400300c2e0809152450440e40784031220940001c00f40010410140d0700030700d45c0d02c1d21030705c4a59141c21342c8903450185504449148001e034018004a0340c84901110300c8504c500c18000d202d9514407035100e51003440140c1c030042da8060f0251452031940b00120307000d1401004085814400014103d59440e01d500c001c51801c0d562280342001c0140d05001c0c003215006420103094007050421071070908011320002c900c00c034443c0d4410b2586581c10104030603950f43c07180d8200c54009094825081e504a402901c0d0101035420303202c1a00144001b1584440004000042c020b400f0030341c61041c13486030200103d40d0b07445442110550348501d00d106810f0800e0040808030322002000340c0e45426180300150205400c0d400050092130306220411007940c0c00185940c20180ba428980d9480d0040510400c02002040024145009003090440407181d10700003a0b01c1540249410030283c028410030310159400d444880408a400307201144030a02003542d035035417841c0700b20600d9040303507501d40d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 936700647 1250 936699397 936699419
    0x2030d111612030305151f0203040915030309060f0516050a020d050102040515090a0905070c060912170f0601050901020703050105010b0901200307200d050c010e220504050106 77
    0x141050803070201400c0340742c1c1095014080c054000e80b29004200f02c11400101088507a00e160003c14041c4411441d804503060003032040750054501100184940c0f910b0003030a08680c0743c640720441c0060413140000410901c1030f90380c1009103206a60305450900d0030401d0401e2800182d40a54003401541e00032001a42c40030310103c407440c0b040c8000758940c3c3c982002c100045900400541d0038060400075200e043d5030700d12208041d203200000c0003880d6200d140c3c0880310910f100794000d04061500c0814000c0c402d20190050b088030305a940c01c0b440107001c4da40c420006001380c500302c010000c0b4130b011520302d41c0618042c120012040c41103030380941d6281c8400e802d440081c0c0c440100002e0003c0c00300d400b540d00680034885041027000492502c0000f10f9034903524481c3d20006840b503a54074400d01e50107440080c8102d1090703c0205900361351881420501d44031015049441e0104448000780300d032500300300c4c259602c0800c501d00740c001d4556182c90060081c000080044905550b0390a011404c1d02030340d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 936701897 1250 936700647 936700649
    0x2a0a0f0320030a03021c1107031211070605090a12020f01120e0d4a060706050106082a0a0e04020910080f010b1e0c0c03060c07050c040902030d1116 65
    0x3a4020b01b060341d0440a56841c05c5008541d4408200c0142d200381c0e22140700281c06022654401c0c042d022030008490202c0380d072094540b4049a03400f400400003203095002018121481c41190043d080d80c0d40c41940d02002024080025001140184954015809203581080d51240400003046002c0b03401400d5041c80e030212a450b020842d40e400d242090540183e0340000010010440e002d1040c0e0340c4802080c0c81c0c00f150821340d114490b12281481500c584060f640b840c1d45c0319030700b0311080d61265400750064808840c0c0d8001c0341c244c00503101115100005403040704040d0640c5600d08148440c040b1034000c5501c2c0707040c0d0459003c120300f0f02e06803560b040d881840c1b0b00c0307a0b0b103e440350f06143e0480c05464a041c1e114000001d018459801d22541236459408603e03800d500301c80d511500310b401d00d07040810310b054a55260285000b00a400384104009040c0303280310b241a290a6200c0c1400c100444a1900003c1d405038842001e450030301d40108641c0440901d55400c0310400d4107029580d1141d0303215 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 936703147 1250 936701897 936701903
    0x300c08030403050106080d09230603190c030c050901180b04080105010e0705040501090b0702121005150a0f12081c020d0c03180b1005032a0a0f0320030a 67
    0x400a410010f1107000c1c07003818041c040c0c4001400c3c0310040908018030b21003142c05602d0460901da01000d41c141c544c0741105104000240c80707aa12458050361213081d0b241091605000c80c0d0400029070901c6101e80b0400020b20101e46601e4142a0000700459a60f03401404400a4441016010440c160280c006e030009100450000c0b5040d03041c41c0c1c1503810044041d00c2c140500c501484140156a0810003075025030752920305060b01d404c0180005003030f1100e24261450540a0082c54a90740041a0061380c8100008004001c0c01030390801844441000d034410325025603040141402600040c5203014443c900a00005080034180d90385005082c00540d9003905250b400140142008a1400742d06880c1c821810100400280f94011402200e010080242a07604500c0000c1000d0890a01340e400780c81c000c1c0480b0030000300808600303569006010070214000110200102d24074111540d00f0179509046c0070748810034950b5940040007020103e0004400c461030402c0620350710100310745198140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 936704397 1250 936703147 936703153
    0xc02120d020c090c04060309020607020d0b06011e05180a0b0309010203100e0606181201090c1a0f04030f0501020409022802010614061821070609300c08 67
    0x420342a01918000c81000010b00840d444410402203100c0002600e00301c40450030046144180752001602c540700d1664029440443c002240c0107021080042610403403081c2c80b01c054051610041c50390841041c1201400500b04001c604008072150846403a1100050441d000c600e880b4070441c03005410840d55001569404020420180c940943c4c0d040103080811000c031071400c2480c00301d030062154288280c1c940c1140d003603100c2c0b00d8803802d02c8034180b6040b0100810541c10b0030b152160b40d51142d80700b40c1910702c1854502049048070881110a4004060060b40c6058076582d981144450041000c2d01e0755542070100240c4018a40014641540260382e04561182d403182030b02e41d101c1307081c5440400c680c502031040c40b100c0c000d41d401107980d000848046072221a901100310191004000d00c60704545070300d080d40104000c0300c1d1007907030354070240c01035502c2c01da01c03503004844e145010700c548145540e400c6035000091482191901c181030004284007084c080c5a03c8001c4c40c42595803051003654 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 936705647 1250 936704397 936704413
    0xc0d0302031903110d200a0201092904020d26040312090515070203010b10020f0601120c030f050102091e031203040c0312210b2806050a0c0212 63
    0x4003400d40c1c00c1030b26150381010003600440821504807800f07592100d0002c0b0750b8130f981911b00c40d180e548084c003140380c16070040c90359072251490090113018207480444002406403106000714000d400f2903056651100300303230075240c0d070340342c08200c40d12500315020354000c02d404220700c0540c080841000c21062280c1d61060b540c07445d40c80d000f003841d00c0e80c00c80c0004010441e5010300c042e6440c0c04441c1c01c40303404880180d498100c1800002c0c014074020000c0360b4046428605040125004200d404001e09914180c504030780c1d803442c4204080b00c0b0b26100031f042e020071510134000140d505c41c642d6100303070150b80010b0514000c00041044d021300e000c2c00141000400300c24140c1032808001c24855a0700030080301d0700350b0606a46040d02c0c1c0c0643d00000f84003026025a03840e4080c07081c08041e05c4045c10710303204c200000140920400038040314035014000c45074404008094616010403103076a201c400c20140200c1c1c80c006c0121426003010982104000b00756001401503640d6200d511215010034000d08200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 936706897 1250 936705647 936705667
    0x170729040b06010c03080c0d020f07120306150e04050c0909090c04060f0513020f210402190b030a0c0e13020408060f01050a03061a0d0501090201080a110a110c0d030203 74
    0x46074004014504000c80c3c0c4100720f000a070b1220680c2d400c80f00303a41805495012608402010380101840100d001c98003142400900003079021403940800e080c0c604001c402e03182c68005200b00518500e002c0420f040440b00502801c285d40210750001803001690704007400907000543c114000d86812001c3c0d44000c40c031030103514140c42080d000304424400b075000d4a150001044655122410348200b0660120300890700040b500b00300e4680483c1d20802980a1020303403941b842c960000e8505038080c507040b8850009034481d00054200392502e070500703071f07045031b030382c01142c4000d021920a04400c0114419110320f45488140c0311030294070512402580f00c5060413141d528201c40240300781950140103004000f6911034202c070030309494000e100803400740b0000080b00b0010b422020f407103400c80d4401903218148103040d0310280a0034401d0307031000b9903600c41c04140810f0302e41c0da01c4a0035604504101240400f4010b079116a0710440d40e42c140d8013040f40080c006070304400711b480300354090b800000f030102030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 936708147 1250 936706897 936706913
    0xd05091c120f0c031a0616030e0d120207080d03050f0c1e04150e271012030306081606080117010e060c03060a0b0a080406240303020c03071217072904 66
    0x10b05c8015030b170140c00c048400c0c0d0340c910110071a513805020300c4204d0106036020340300c1d150016072060b00180000000341d210742c4000d41d5260310b48540c009070b000d15900000c50368030902540d409412403822039540307900d07007040d481c401e030748500c01c1d81c940740e0a10b441e186d0702102603002501c020480e0804102c0540c4100c00c000c0c02411030b00403e030744502d43c0c90701c44c4d0000f2903510024511f050b04442c01392402d0741c0c0b460841c05000ca426000824000703004c0c00c98204040d03040d007110060b00c018500781d038501d00045800040f030890724025580420080750061141800d4500107054145c4035a00220f1207222141c2640e040102c181c50340200b020001003000413500f441c81c0982c7c010301d00103030704902d80007412100030142400900002d0469860b8078110380654116200e004e02c0c903180b0701c41d000c030303056030b80c680a99100aa0300704036000b40210743c0300040e6040075104122130b0700e8200b070900c0c1018940f4110118180d001480c12a05401c10980d0321034103e4900c0e2503581d11001c45088010181803601380010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 936709397 1250 936708147 936708191
    0x5030a061703040608040c080105011202010f03200901031e0b0f060f1207091d010806010b210c120411011d1806060c0d050d05091c120f0c03 62
    0x401074031404502901030400011601200c00314070f0032111580b5245001504206203900c001c1c05907003420008218161200003049070240300b6219035000341c0c90039000750180d450460003c0e550469104580c3d440032481001407035000c03030502d00040c001c2d1031003a46043c0c403071810641c01001503803807020742580d013000381c2c0400c0800c0f8122401c80c00e151103001e01d52403509c030f00000c0d140002000000300d620725010b40f000b0300c040e024001c41c01c1515000c005602e01412002d22aa00d03051181800001da84c2004004840802e01428101d030034885995c0303402c60503600040d1882512190400c600020031000702c1680b80200e1040a01c502000c20f036100040c540352404801c65000c1640b41c0f40d070315403583c2e170280c0e0081c00c07454400381d841c1036a00c1e0300c00a900c0303008402544840c0e000c0c107000740080c2c030307480b100500d405141c1080410494460301c0301c0315501c0b4645400d002c0008522910060018003076a2a10003049051102045aa03440c07544241036402d4041c084010030388580c0d00b1a500b5014280c41e00e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 936710647 1250 936709397 936709409
    0x60e0706050903011a03192f0a0f05010504093b0f0601050612040f0b100503060108030301030f0339060b01030506060414010e04050106021609090803241005030a06 72
    0x17650503003400194807031114203080c40d0051240721020f01000101c0c00b00c0060300205684003148950742c0f8a40989504401000341c2c410140324001081030041c0c3c0d0640400c0d0782d01a918a030a09041050b808020680800100300700d1030700509402810742581c44d410143c103401381d504210006140c0c03c0070301c3c0a004074004601038128800502c0291920304c10340788507040070074400c03000351120b04124001c423410038800740c81660b90710200300369054104558000c0b0740702902229007030703179031002d4681d1039000a000041000c0d8804110328003191242c02d106459100c24281100380600c0b541c00400c0c040e404004050030841c590300d46009010b40c5200e1100b50480c00c3c01c0c00d0290b844d10100050981c80381d8018007c40640004c208946a4072503110040000e40141c010032240d42c480b20083c4d03035450400035108843e100340d40003041301b210341e0003842d1403558842c05590940d19501c1c0c2c0104041c1d602d8101c403016603011441c4080e26170301d12103001d62219464588980d642032409a0000365841d903000a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 936711897 1250 936710647 936710681
    0xf060c0a092414160b18030f031618030b0f0f0403120e1002030a0b0306060d0309060f12021b06090a03051e0f030a0f181e060e070605090301 62
    0x61416408418500042d90b07146031500210464410b6800240540300300f081e801c00507044013808116a0356940c2e401140140100d900460700001c50550301c5c85100500520440d052021480380b61820041c24501171090914100150080902e00c030200c140e544181d80d44000c41080c40014203d1055850b0040c00000c09a5040d00e0240c0780038000e03188062286e11382c260790710350b120038082c010b03c00c0c200ea0b504801c0d420b43d9681025903a013805030010f4046e0701e110f40149404103d841c40c061061220700e43c1e058851801d0945041c90a4800b6180180b8690900c11a003c0c10500d9141300e10042c001c0040400202201940003403080345401c200401011455001d85000d10100390400c0036a40c4150490540c4c02c20790b0024070f035491080c0242500184403000c080248500e044403a000003034144c4015100b00442c41c02d034142c40e003190600d510082c244410b00c0c401c4191180001e803078900c0e10390003040c010400b48480a00140340002551100c0f00195010a80b039000b40340a0007544800908a003030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 936713147 1250 936711897 936711929
    0xc010b030d02032212030c150213081501030b0112030210020c0a0501060503030c1b03010603080c0a03170f0f0402030f030d1a1005191202030a1d060709090c020f060c0a09 75
    0x2e050840c9060741006411f100702411104108111140800c6600ea210001991501c2c00d030640c503c40c0803103600848026000340300030308040d00030300f84050b8100d81e00001884a540d1901354400c0700003034002000d40460069106080c100001030005002d03a1714050f000300b00400c424208907003150440c1d04041e11035081004500920003002603844a600c4030b50b014121402c0c2094002401422950320003407080b100401c580e101c00c1004030f000c0321118025111044148058940c45022450440b544881c090303c8502160140b6070000035194800e101404236503d410301c03075003040e2854103d4100703a4982500d50454801c01d4001502c07070100704900f521520806040100301800d9401031140249078209491410f1a0030b9104900c2010700a000308070841d602c2c2003c0304407501402c400250000400800b005241c03200f40005182845800190754501c02a410944140701810000c5414021886175411300c00c080507080c48101e01238007038944103d949500c56400a490365110364403402e500c1c846414 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 936714397 1250 936713147 936713159
    0x305010c090605030c090409050627061b03040312050411030d0806030303010504090f0f060c030b19050103050a0212010b03060f09090d0c060603051f180213020c010b030d020322 78
    0x684e070700044030400190700c6c1c00031030b4003003001404c0d150b802402d184501c1c0244070071100c40125080c548468070700030203044511000060741c0c80000303540c0034400911610031210f1001c00c0d0f1003e0b6401903c1780c17508411030940841200c00390348060342c007611603400f00c0300000344d0303890f042003640c40403051801c145200d86001c2c40042d0b03e900051141d03500685e12400002d040098140180101607070050110751000d0050400340010004c10f81e0050100380303000507510242c540002e1060038040707a8a007641001c2e05220045001e401c01412b0022166001e1008641c07280c010f142d8640a00b080c10b0b01c6c01e4980c80e00da01002022035001c0c003110b0191048030207000f5070000220759118100303010700f1f05018027030280c40d228000700303455031015105000311403051552038440c001d108841000c5803001d0011070740341d500700402d403d000c490080d8494100c1d100c1003d48000703a00900700d1111007200006440c503040001c00c1c14a1120080c09005810004e0229401c0c10645180700c00c1e0003c40300d030b000246007040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 936715647 1250 936714397 936714407
    0x2280e0f0109050a12030c0f0309083c01020d0606030e070b040803030f04082724160215070309030309080a0b0109052509030209090c010801030f05010f150305010c0906 74
    0x401400c004c50b043e01c4103941414050200c0c7c5202036803010056851051904008184d02e4003070003048400d0044c4845403034030003500880c01080722180c817050290030303003150385402e81100c21240c0140d10355000d1040003900300180c403600d070041255480c00719142c0c000e01051400c00e1855080007815040c14002031150300f00010a13a540b01e0206024414a40c07240c0c00c03e10102d0203041c0d8400341c3e02041e00c05083c040c10800907030342d03500b0ba415101344c8094145c4550021541a00b8035090911031000d20014064041c42d00388070580c00e00250001080e0107404042510582c40b2040a40108056260400401d54031081e514010800322015000f004120703510000c00010600c10303c0007494590000c00e4a41090710710840c84411034a034100c3d101d00c3c1590010304464010b20049e03203c0c010400004603040000b10b00c1060015050b550b220361a0b00750340d41c1f100c0c07510780c0900c103032123030365035109850341c00c406070f105065032241960075031000c0c1d03491071420390b0948052107032280401413404010002c45400c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 936716897 1250 936715647 936715649
    0x31401090302120f09041e0c020c01021b0a030609140d0c0807030507060f05010303260f16050f0307021e160b0c0a0f0807030f0c0f0602280e0f0109050a 67
    0x3007040f0701c1d40c580480c1c4100241c2c0c01580b800340d81c89032030444440d030070000d06803107420702c103051200912001001d5141661180b00d081030b800e0168010020b034241c41030300102294510a002000c1d4000180c0740d4551404484655900711480c00030340400c00903d6004002200507200f01d46020303c418690384d51003031440c0c007441d1001002c1c0400490440100121500000202e20402900b0812503031349040050084030030500702420a00c103002c000300a00341c481d1b00305200d480b00d1b0b003a840c82a12a15043e14540012420040400c0300c14400c00c0e0380038101d10000c41c0900c58030340c002c2c811046903055142c20b4000d24041c140f4a40e0006640c0a51342c403a06039100111481d20348010703211041c000034a800e10400240003800540140194010401d5040203058031501031340d213417020141a49000d442001d1071003030180c540c07200c1303030329240000380c0d5500101074840f003844500c18141041800d591410f0320400403000818500c40c1c06c01c00c542840c50140b20890b9003480c0c03081c511464403012070201916 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 936718147 1250 936716897 936716923
    0x80a0c060806010e06071b09090f02120c0603011d01060503090d0e040b03070308031f060801030f030e0904030519021b061b0d080906090a0b16210204031401090302 72
    0x1c00000030391180e024004450000c50301030034450356140d1a29201e600310034000d4180040c0310315840c0205e92003e0500c00d00099590100c500180b0800a07002c215600ca22031042c440c1d1031184580025440d00e54201440c0206050414500f2100305071440e410062016080b08040110038420040e02641c00656400b000d491410302040070090a40440c01a1805544080d054840d80f1000020488040020b52080900342054158000780c0421120340030300394402e80340051030a20041c00032031540d803a1008120300c6030811828400c540700c00b00b0700c003281c1150264041480404c0c542c02d150f05241100c104568107201405005072126001d5002d1400d51998901070350021411402c08018002000e00106880f011a144100c0511000344588021200b210550103910041503006100051036040b0b076600c0341450030700c1c3e9079003242b0034103c0321140720a01c204400700101c42e02251800f00030407641c051040b40560f465003036090034190421500d668055580c03408002d1008030b540417a548440003a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 936719397 1250 936718147 936718157
    0x1207031415040e070b040612180b0c0a05090d0b09100624050d0e0105011d0f01030602220b34030302032802090a050d111003020d1a030601080a0c06 65
    0xc15460450703d040503c5e0003240d00d041c0001008524283c10401150342e40c01040024064503612003135800c0219009103008142054000104641c0a201c9014005c4040b083c0b42450400c880100000c1c0c0403151407030252118088001403100c0700c02d081c0070311600e0b200c030380c001445214900081200600d050b015140d4400074a1704040a4172440740080311400341403030005100c100e40d0a2602c41c02800203205014523b8030f1180304081103116a41900d22451201048030304036840c584480c4003a40c03142c140f136411000803022859442440b83c0d8648040c0581070b029580b0b40c85803c00c851810b0080c202c559441070b041403c0c0c007089002c6c00045140bc0e503490f150158070394866024138080d84403041c10714a0208901d801c52200045503a010301413488044510000075641c0b0b005200f01d042e032556003d0210071940c04645140e080a00001c1524070303941ca001440c00c114000607604840c2210b2102d0f4503440d006003210228035041100502410105015268202e03459030b400c0e40300e0a0900c21702c401e0003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 936720647 1250 936719397 936719411
    0x90f06020d0e0109061a0915060921011a031218040e0f060702070609050913020111030d1a0103061d0912041511031804020c030708120703141504 64
    0x801ca07070060030a46071250000c0c40a0b45040c9081d6002e8403503008480030b0407120088683c0c0390300d0168035242c01414007500c54120707005818140689940700117400c9400030680e0302401c8542c0e00e04401d08011028040000400804c0a600d4107940032032440103e1083e80800030f0300760a00a03800403903000581c1c2401d040705c6010300c0c40214010300388035001d00b6400d0041d10340d090300900c801308400b403051826034280c1d030040762201c1040d10640242d006e01a00f02d00d402001840a50b0800c580d0b40360140141404104d82101440305480c0d0303407200d800c82c824981c4a000a41201d0641c001c2c045819509080520540c1c2c10a4522649000805203c0013031403010808901c405031309022540900e0404400f140c0d6a60310781d1040e070030502007014100000340c030055088260107004800e840f403030591300e0400316a0f852060200400b9411011010215010402110001a056400400200c0700c140c1c80802a40b80405010341151700480705081e03041c40c14010000b940b450a000300b84008422540041d80c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 936721897 1250 936720647 936720667
    0x70902160f0507080d03050124120e010207060b0d11090a020909070e01080a06050306060d0606170d23120c0712020606150408370f060f090f0602 64
    0x10590501030003000c4404101010b020012841038103076410202264540d0340e07284070440c01c84d84c0910030314140e03c101c2961101041c4244440e850030366a103140464210031081000d4080b15040ba2110040340c0d800500300302004000d00900288290441c5c0c40b4540c0b142c42d448a0400030303440010030b0312680220002440810290381580c006030000b400b80b8482d0310380b44101801110410005501040f241d8000641402d0240a06010780d90042e000c1c10454844805121039600d4111040780e20503218a804240800c0c804140d04c0c8100000004100030b03a440d00026104d00780403d0000200d001e1607003080e00c1e041c01003003214680f980600b034480b429031f1803141c2c00c0168007a84000501401d11103c00f00034044d030020301c5a020b900125005001d004100703a040e51140309500c10744080e5082103250000480b0003c00030510400a01d030340c089112801d203004c06450306c035240b04030b48100c0c94050070020b1104e98411880840b050440030818080e454458020b01003200030014160340c0c00280e04111 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 936723147 1250 936721897 936721927
    0x31e0d0302030f0129040905010e010e0921121905370b3714040203040c12060203010f090624051314030105221106070206190e01090503070902 63
    0x740546a05403651603940380c51740f2101900c000c3c8182220842010000704002507330301c1c1494000e0070f07100000d00e8802103910a415a040c1070708005100601c0030b120364400c030041300304a284250701c1c810880b038100901003600b004880c07010344090398508160740550920902c00c0d0500092040380c0809000000c0b56000182c060411800c4240e04503005203a61120065602617281a241c200b081110b0781d6003030202041d15905092244400d002c0d007640102e003803410283d000b150001c2c01051208805a2a03001041450302440c0c41115056400001004240d90032240c11028020742c0f0800c3c043c007850720341c05050551030f00c046416400c819400004150b4080e004494441c0c0165125a6000e03688107101c0d4402103006070740d28002e50800000074000400000b40803c030790f0490101c2d100902890b11010010401c403d4010b820800411a103805070769000c0180042c07506507000980d1441c5a1700004000b100080701c2a1b06000c002c02050003155008602034069942e82140141c884d0803194044070703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 936724397 1250 936723147 936723209
    0x270302190609060606180626090a0f1b0608060a0501030f061511100203040b040b0703061d09160f150309080403030e1005090a060c11031e0d0302030f01 67
    0x3c415450140c0010320315400c00050b0000601010901caa060340d2941d060300e0313441d194407441c0d0014141c1603580510034202458543c104c500c406c2290141c01590ba1100900c00c04804180c9424005a0711024410500400c041c00307032000d49041c0c2240e081c0140442d020010300d000d1141415180c0486e840c044071680e10500003031040d80c9910b401070a003aa8003900c8600c856a00724428066011003441481081c02141d00850b404522881107540310748401103514405030095040580700d0400140c02c0d24980c0781d070305008401301ea0004060900d501114644404c2c2003545000040c03410042200c0ca9850000b0310454441c0354015005944052085009203284040205403141c045008014950300c80c3d40b503900c0174070603a02c490a001041c4000d407030394000c1c00c01d4168480c40c1d0550a1201d180b045001e04681885000e00905079064103001034100800c850840a9000222000b02030814003004400301400c014141186541044204400d03100c605026076100265901107045030035003081e088035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 936725647 1250 936724397 936724403
    0x2061206032a010f0e060706180b1e0a0515041817070b01051c081e03250512060f031e01020d061502100b060c0f01270302190609 57
    0x503680118002d000c002069030340c401400100401403c0f11064080e41c10159080e0000300450300f4001c4d90ba44007000b902215224032090342e42c0040e41d500082003a00250b008811203504041450440d614030341001c540241483c280e0744c1441c00b031021895401c8101800700d1000c0c1d80206201c0b042c2441d0070400d08200d10010030162078501412071002c4810058000e0500c02e87c006407690340e0324810001407082c80201007100c0d1034412103400004100400400142c0030811401404e008151103541c030702d406c11a0700e0004d11240390285601d11414034024039171700c815410f00d00e08004030212009000c0e080201810300600041d00c10319801c0d17070308004462071028035500d4066036103c0550054040d420842c00c0f460300c14280314020609d03554603144a41d42d007502e54000c0407110b4500d60315802601c800500250400020459000c2203203052110a4030014210004140e24144d0350183c45889a0480140119a41d2504600c0040d0380032514182c1d5010001d09030258888130300b0900d00800002c01c0c02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 936726897 1250 936725647 936725683
    0x111b060315030f1b0f010c1703071407060c031b0c060e032a0c010905130c0e1302090a0e010f060507080c0d0c02100f05030a11070b0c09120a0206120603 67
    0x8414032002d11045541c0e0704d00d0554840c19400001e60056800403c055801008588640b0300030f4402601c8801542d400821842e0462810301c0003180d0120b90303030210310203a071480e031280700032104c190301800307440ca1540100309084980d94000f08010824480c17810000c042a0300c2d014900440700301001074840c01110941104010807081090700204000341c0314a08090150030301d044503e41c0107480c403400300c07038025007001a00c00c0314201c407000030142c41c4003600c2408115418401316450b4203a840c08210103540b030060344c0d001c24808210304c48001e43d0104114002e50f90060213080d485e1001042190304d2030a100c0e444410718030b030101c032601425040441c90720401d070190050a901c0303031340c4003011350007911610904c00400c0130440300c0040760f40844c008035030100045221140c00703622814020841c0c607030740c605124582e070305c041c0c04450544a4100401c4003081d540000c0c034000600080c00341083d8010590400d242e404550140035004900d59076210140c0020b126480901c503c04000c8807602c59 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 936728147 1250 936726897 936726913
    0x1060509062b060f0602071401030509010e062e050f060304020a2304060605070b012105150a0507091805100e190e0c0a03081e030106111b060315030f 66
    0x4a64010301c8548a80601311507016800640c0394000f003444401c2d5a003140507242d030a405680150b0281c031001e80140e07004d6588000f441c41d0300c0420f001d1079010303068280c07002e85c80b13000701410140103010901c211402d018445800700916600c10200c41964030041c0d88180d266a103e000141403103820340e1080e90461822402e16125000b01a190054880c0469040200c192078241c1150345028015005000d00210001402000034084014240740c8a03221740c814001c41d00e03035606041210985200c0031171903011003803100940b504d014895000045281000d0320364501808910106004e6014201156a50011030140c4041c8544580035064440390103510b801c00408015000a02030103c9420307915000c00240e180f640813480040061b03005001c28401da04540f11180d0310383c8050360741c0c0c0c00c444080c85c280c1600d40c0840c0145000f0320043c1c88560301002083c105504141e104881049000c0c100700c2c480c01580e907040c0c160307a00820800703410f82d290000b507400300386040441e528241a0344201d090b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 936729397 1250 936728147 936728227
    0x90e03090d290f0424020a02030301091a030a08030a0912020d09090615050d1b110d03020403030f05090a0902130501110a0305030106080403090f030b0f0f0106050906 73
    0x30404900540e5030b0076094480103041d21041d69a41942c03000c411645082c0807030302250745d4180800b0000b030841c8804076059005288072080380d01c48184500503030000f20041111040601c20903c424a070841415511103100c8006612210702180061950b10040701055464007503174015911107a01c000318011440140001175610708010280700b002600c201d0010910203441d0164070219074090510350440c81550b28152101e4014500d0644281c1c0d40c3c202c50a1880840902c140c80250745440e0341001c90750756070120b030a015840c0c3d00d14041c140100001c00002c0c0d408804241820901e00c0e100b5140c0c00400c2c0000c240c080581d200340e4410f4000301d9401000481e55200c04202e0b90240c83d41c0b82c0d107040a82c0300ca522186072030030140110300309200402816000d0b001d207c4d4400d12a00d0801b0040d0344441c040c40480d00103410035170b20761107140200300c61071746105102900400c10981e84100d542c54404020110300c40c0d8043c65000c0d010205402098035081c0380403a04041214441e0202d2894040d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 936730647 1250 936729397 936729413
    0x6040308070b090d02070603090f150e0601060f091a13090203061002011e0b150a0c0b09030c07050f061e09031603080304020103090f05010218091f090e03090d 70
    0x8056076500c2d510804100e80560020f02d80c0c500c0400707034018210052401106230b008220346401078404005190808000441b002c9403004062200c400018000c450b10100300d243c01d005820030f00500c403459008519054100035120102c8040c0c00d036260a00606030b000090074014001d06a10181416502080210540e0082c43c03288000303407108025410f002038121b0036030700e00c09143c1415106110a05490200503080b00541c82809016518502401030110354240d0024802c5000107000703200783c43c200304410305100d0304072040e5402141040500000181c40da038040c8541803081403407030b884801030344840040c4c543c081201481051200406009401701350300282c0014400d0080007815200f8000240c0c0c507005076038110030164216600d40d07005400421150500351a54ac1080a00354006003090000380038540d00c0e80d440c0c0c213030b10320240c0c02d003d15403d015151004202820b048804054502c903400400c940c140030020510a00c0181294110f02c601d5040c103030803501410240b000c1c48001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 936731897 1250 936730647 936730657
    0x110d060c111915050604090c03050d02070608061f020c06120f010603050919030909020708090f0a2102120708030301081c08010302120111030a0603060f0e06040305071106040308 78
    0x10200740c0d042c914007001000445548100024083c0207202107280c0c825000303500540d403165018000054a48158441c8040607810307510887d29584041044d1100036418000c48000301043d08122040b41001d02c009895140c0c0c0c05a03c0203444121a00c21912501c2000318094064011304641c0d030311180345d80091001c0383c0c12503491726504030700400040c40c14400d204645c414401c1001500c40214002480118049006010303001c001c0502d80115045480d440280941da21540c0d14603654000c0c07100740020800c44500d0b007882005496401c11081d003521503048000c0000a03403a0700d41203418270009075a19801a8002d10b18840c0c1e00000c18800d000100a5042c0c3d0300c21003c40d05a0b0010b4044031107442c44840f5000002114440100b00508103c07a000c81c08074074500003c5074403141101c480304c00b90001c031416030403903032105020000d0082d28070481012090305202440790449a211180d42c41601800040400c40d0000f081420f0103d400c06d910b5030440d00425480c0d03165545e04001c1003503084 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 936733147 1250 936731897 936731927
    0x20402190e1509011d04050c0306010f09060503010b0d0609090303020c0f070f14131505010e0409080703080c1b0610120b0a020307020f16150f0507110d060c 69
    0x1030146030358610b00d02070b5600c1c800050300050461400b00707998011550f880105111041111640e510800a0341c3c07603000710361090980c12000c81c1c0f41d151540005040c003040205980c10301c1904101444407a920508903810342c2c6003102d50b141e0b0f60944002c40320041c10943d100600851505807034604041c4e040e001050f590161104403800310500c0f1180b00d49440480c410302c03800c1c1154103004c204092000303a4420032036a008040c114100e0070701c968101610000d290321041c0b24001c0c4010300c0107681114002d581c2180c01d45003042000d4095580b054941310f8040040c1c14080820002031041c05004100e500301c030b4640742008400040c00049a0352035206458501014000d401e01007850030150300c036160f0290b000041c0c6034160307c420f06008025400500404c00718080d4802000d12014100104820040e0801184480c0c500d0000300c2158604120404800c000c030408080d803156601109640071550040d0310a18079102030400249030004182001b00707920b09082401c480380340c024420802070f480d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 936734397 1250 936733147 936733157
    0xf07050306010f14150c06070c0c090606090e09030c071202010e0f0f090a06050d1406010e01121202012018060301062c09010e0405010b060f0f0904060302040219 71
    0x10302c841152458440e14024915984003c0305054000c1ca043c80024817050f0700704540c07501d0b201c203051841c2e081400071103e40c4042160140c0c01d00800080713801600080222810400850b030800400605010740c6200d28101d101070321021924000c02407048500b070641c2c000c100c07055190340e1603145618441d00d10040c1d0203e09640110601e500307128069012442c0c009042784000424201040030818000d41100c160725641d00c0c011074107407503c8a4180d001400f90364000c541c910010406807034180140c00c0781c1d040104180041050345a07209007101e000364000fa0180c6403a110701e200f01d0041038185801d080d0f000e00040c51104d00c0c100d0b41d0051891100200d4204450a540300510910b40305c00e00c00d00c0c000454107410407403001c010160540203204d10308550145942c1d05d4000035500942a0003540700c0181040501c010413009200c2e007080e06001391103c5042230502000c4540c680a0400450180d81000941d8003a0755165404003014640c014400c40d02c407404101224240160600070302c001c40ccd = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 936735647 1250 936734397 936734399
    0x71e121203230c0d060503030a03140a0e0c27010f060e010201050f070302071b080d020f0601120f050f0a210c08071b0b0f03070305011d04030e120f0705030601 70
    0x1c40031002c8084032034000a00c007241e80d00d4440b0300c1d0b01c1651150005007102c2e951a200412030740d6084c0010402e500090b6008111036003c540d0b04c2090f10380181829207030900d03002e1030103181c1401107500d2640302401c4501c18a00350b07401c0354081040c91a0074005001401840c0081258542c0c03c0c2e5000c00d030389483d6a103c2107280542c005a089810030740303500d540256503070009003199202e6001440c0c42c5220b0315402a00000082c10641e451180f030b0000c8410b034100b401d5a490080d1304108000c8100c0482008051135454040c41d800051030b41c08000e006132403c008003e0602500300803003c40340034080304985c0c10502504112940d841911106035015a10071a940200e0344500c80d400c030001d41101c0d900346050403035915443c0c008070f4807544140307440d07641400055244040c0b02904c842c081700045107581e0720341441c00608403801608441100c1c5950704095a6213801c0960143d030103981030400d244c0b5080520001003002d004071050064510804811001d441d1001c501401150b1042d8222020303a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 936736897 1250 936735647 936735671
    0x5030d0815030a050307050c1c031706011e02061b09012a0215040e18060426040303090f0e06060d09060f092105030603071e121203 58
    0x140004610040091a810045a1514404005808151802801c071032544240390b0300e060460304981401d035029081090080700c503041c005601e1035400f070320540004101d01d0300c4c0d401800800c03115a841501e01408000620143d000380c0001c820680b9241080c06101c06840d0022750714801110040c0301c0170b03118940280c3e0740106800355600d0b807005840300c0a01034008031401080700c1c00e00c0080c03182e0b0502d460a1a016880b043e88000750b00806085240c3d071181009143c204080001d0501e40100562002c0e0210450004c50348a4110f40d03c2000404824280300e14a6440c071103c4813001c1e00b0002c0010300004164001c042c0c042150b404a00c621030b015502d1000701c105000417201d09411110400a89241c0b030555840791055600c1200f0000340e075211141c03441d0481c0e442c0201250307910200440c4403203c80d400901055804000d00c1d11510b1072415501082d10340000b4441c0100d960a1100103c81c4040f440e00b00701c02600351401c292540d1407441c1060200c800c180200c910110b441c1060075460 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 936738147 1250 936736897 936736903
    0x6021e07120306060c03080910151401081b0714060901020904061a07030c06020f03100303080a20070501060b0711090114100e130e06100e01031101050a02030712180503 74
    0x12105180c4a0030040400b1b80c5080d50301c600024403a030054000c0c543e40c078003004520700c00c0040030400c2043c40442d260900358a82403205054806906010551082200c80b14525501c8900c1101403150385480e0201e03132400002a50001c03440000e103006010401c0b403030710015405041001d03003c80e4203001090791009040b4450fa804041843c01000411915000c80d0040c0b00b499003951052500501d07104141c1140001d98200b5a040500021fa00c9800c00034140d00c244101d0700400349440070050504503140052180840301986c040440d40840c100c400c0c08001c0d442040204081c220b260343e640b00b40d160005600140f5200b8902c03c0c0b1003240041126029949840102900601b02c1c46c1c105030205d03000c0d01c041d0501440c1da54080c00201100c1840425030141405d2954044014407003418100400c4400682035000b07103e03010864401040400c0041c50b46103251102070030940d03690650503400320706620515401410007003c411401d100a50b114220106111214030300b05440c50b207034410191 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 936739397 1250 936738147 936738149
    0xb0a021c0f15090608060406090c03050106060f0f0509090403180504090809030601080a1e06060b0a030608010608010b0f061317030903013b0f0a0b010e0a0c0807050706021e07120306 80
    0x9506d90101c400240018440c0d84018a0507010794184801b41d07580e50b9481c2e0950b2000d03000030b400070b40f12803d4203101783e800c107041d802c00c6142801d040d41002c1c3d41402140c50810001c00c060100315900c84005c0240b030002240c0c8020380b0380034006001203a01e40c100f691031a4030200507140a48202c0c1d00020303030440301040766440755900c1100e5640b400006001510060380400381a42d201b542c0319800a240700b081d1004080781c0c6ca2586010520078640b4032118211051a80f0440560341401e42088250b9140c0a01c0d0001ca107044034001d4640700300404210f5410101d030860390f2198540342503503100050000140c0191442280244000103034038202da00b80110503410440c1d03128216009109100e030f410704102c501080002100e444200fa0940c2c1d07498014445810b0345c01d60351000060107400410110182d00051015080c00450440c50b4020521a0010100070400c2000f007040020071005804441d00d90000038010101100d142c26030a00030380c800c080c11110040c0c020504190f0034043e0107204 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 936740647 1250 936739397 936739409
    0xe011a06130603110f0a02151501051b0f0d0903052806050403020c03160501110d08010e22150c0c02060301270203070f080a090b0a021c0f150906 64
    0x550001c2c60801c0030b030301420303640420300140c100503c110303c1550110f001409640030746034000d01c03661102c5011003d0b6400054029407088038070000c25071459800800700c0b144000c4440c401c800d1810900d00c042d06200b44038252040c0390145080a0403200d07405155002031b41d001e0002e4442910460782c11400401031840c0c0c0403608001741d01b5000c04500c1d15800305034843d000340191548845c0c00000241005951b50860140c1d4560400071b001d1941d000d05d28110000e01c01c0000c00f400c1908000150800d40144600b600414820000686142c0104210001c00d8000d000f200f0041a052503c4810300079200d8215441d0b43c54801000704030380c421000c88040a4018103941c2c596400c0c0215126492020b01010031600901040c8448080440c80114416149540c1700f038119419048018032442c405082e1001040c20801520007083d0000b11698000c440c4a00040e0b0301d00d00d03c88040586000803a990140c0c0c0d142200200b518001034220400c047e0040c49141031140d16100f44808843c1d45002c1c030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 936741897 1250 936740647 936740677
    0x12140c010c03110c03060a06080c030c0d02090402010c0f0302060a0b04150605181207060201450b090c0406080a1a0a0b0a0b09010807050705150c0408010e011a06 71
    0x8407000c00d0154841c100c8000324030007543d288022076004689003040c295007180c400c44d0795441c1007104410a00c65000422000c40261000c800324900140000800f40d070040d118540c06008038085a000d0400008071582c484401e110b90742c41401e01944030201180c4c0f011030f060820501ca102494039120304501c160403120318411440c1440400c942c9038001030403400319142c3d42da800e0303036103039544c62040c2c21000302c09401800a2810448005d0075039101e03250120040c155040400e01c600c044501811103000c1004103000075a07080315810301c07413101409010f400342c10100280100f0090200343c010111409407400d02415a960003402d43d96000e0312000340c52a0300c110011200e001d4408001074210328100000b0400c401e0000004401c01019446014190000201c1616a5812180496005c507042c1080750401c0e856840780c079110300310001c01d0190100c01c0b00004482002100641d005040740354020042a4008808a4020881420b021550306140354003100203250031011101040039806030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 936743147 1250 936741897 936741917
    0xc060a050a020c07120b100e2719060b180a2315030d020303070228051e12070c030f021503010f061206060509060a091d0703050f010e22050712140c01 66
    0x61907401c8016143c8140e00264a20f1085550b427010041d0480c2e2402014103890045414600b88003100c1e011070f401030042d00002c401e0500c061080c911903611005852020481412a0003a250700810207440c2481c000d84003401c0c803604040c3c008845040d0207080e011a11714510341c5d1016a41c5e400100e070304c080140c1c0810a251540c0c101442240303080300800684582c800c60550741c0e54100303c103030300f8601c003807001005940342c54110812400740e0416401c85858034280598540034420007050002802c041d80d240410011904e1304010b40c0d090001c00311000340c480d61070300704d0300c42030904030300c1190002228000d0030702000f500ba205e80703c11600552145458040d80c2c00a00000d42c2011101c2c0d020301442c603000190043c0e8034a8601c0c00800c81000510107031500d880044d007120405010108040000d07030041c4100d000c00c102c0150086020004000e15281d500b60f2450b400004201c0140309028850000404d01c01a032000011740713200f01102522024004171480d0385c1c214010000340002c0d03400344 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 936744397 1250 936743147 936743161
    0xd02120a030906140c1e1606091b0f08010b060f120402030f1605040609090302071a071e0501050c030709050d150c02070602070b0c060a050a020c07120b100e 69
    0x1001c468050f10681000c03403240e0b014440128400000c4803404004400004ea0300100c00d41700c0000c801700700306444042c2c1807420303801d40321090070b00071500202070310781d201d406405009018490039031070000741c05803070000c1e0307101c0c030381c610f2060807034400c00ca42c941c00c01141134594540002550314800d114859141840c240c030300610f05620001c0c20a80c1c05005a00000d00120000d00c10741e2010b05c3c074038528006d25440c06c000d010444807581c1c40140c0c2149044041400280d01151440803035600e1044014013240d640100703032143c0b0031084014000042603210780c400c2e14104a50922842c0108020013050382e40f11801c550512080f60444005030f5401c0c0e0074005481c040c0681d00e140d0703020b4180c21303840300e01c2540000c0c04c507080d0050107409a40a000c04000150341040214042d10343d0388800c9050035260703103060343e440f100035040712100307511a00003450715202e644c1070b80c1210a8070b9040358145561803182c50f100c503c2014040c0c03156000540000e05011012800a0031126180701c3c1c0ca0b00c43d99055 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 936745647 1250 936744397 936744401
    0x70306050a1e090206120a0b0108060f010203190e37030203100c140d0506030606220b04090f1a010b030714130f141e01020a0213090503040609080d02120a03 69
    0x43c2003240d02402c248005444000b980505610603003406100003030284052001402002006203e144030f0b2600550403c2240da010042d0303141c00510382d56601030310480c0c540070b1700e64808200c14540c01c0441c83c030780156242110202000e40d01042566402c0c55400381041a40f000c10501001e074050703002c442c400b04100c09c1c5510564600d58a45800002d4200030011303907400340d01c1000c000c0016a100ca09200171454140803041c2c01c8501100c0040303035000d5020709850a509441c2915940980d100f80304001d81d02c031600030346a1103074844492010704000d4508080c030b4140b4041c1d50144441d091002081107140041242c4c0110b803d0b0722100040341c1d1300241d40c2e403298003228040d8030a040310301c1d000a841100e0114031000c0c00e020306000c08161544414403c050100602c1c0b001a0308604406004c45d9802143d80380c1215010b0f0b8520203a0040720707803d10003074480031400800707038403000400042d102d5004001106a135040130030f03070701c000c900c00c0012a9103040c03402501d8100107041100d8280b41b400780d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 936746897 1250 936745647 936745661
    0xb040b1c020d050103233004030203011d0d1106040f030507060905010506150405100507020a080f0a02040f0b01140315041b09060216060309170c070306050a1e 70
    0x1090300949490b0202000078141d44003a40101c8501005040c07014020f00304407031040b00c01e406180201044081504010000d551030040d440c038941025540102c80c69007001118061500a402405a00e030b00d22101c480d159000c1070b020506000d801c40b00c0f400d081c03181c00c1c01c562039040d840080600d80c40b19141c2780d44c00c035a404002c905010040102c1e40000d81c041c00f4018445010340000241460500240198001c410044c0540b400c02000180440c0e511000709880049040c0b0f42581c9030200c3d4400309228031000d0b0003010071442448000c44507501c0020380c441c9000e109450a124251000440100781c0e000d01c0f03601c502060080129002c054080000785510080840d070b000f003409041da0100301106d024000c2c40d50000c4003c0c903091042c981022404004000c0f0f44001c0020982c10b41040083c05124041c1004140d1522003440c140000c04142c1d80300c8001541c60b07103598460b811011503403103900b030cc0b04603001d41c2082c001070040341d440c0c0f2804504040d008460320390301c4860498000102a6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 936748147 1250 936746897 936746947
    0x807030c091206060302010f0306050a180b030f0c1c1203090303020d1a041b0c0602070203010603200301050703020c070501030228050c010509120a050705072d0b040b 73
    0x2603181d00040b0349080141c1c20a0890280d20001540e908500004140004542c0300c5401c1c14140309081007035840700f250170012540042211004200f40d803a9020240411407081c90389846140c4000d04201c501041125480c0300446007815800111980d8001c80512140003030f21400c181140a00001c0c0203030415103003030b0312a00e00186403006080600040360f04201c541c004820052200240c81d0406110320702941986060f40c81c416030103d90010618004807500030801600403030a83c045440035004ad0010316404034160b0b1182900041944010314840803442c840d60900c0049800315009200300ea903205048005403000c0b80c00c040056000c1c1d4442d05091041c94000c180f41203d0450560f81d51410b0b070100d41d91959240d50310f10800e8252034001c1d2121f0301c00d8004100d1180c079011307403108541040009003006500c803c0c8600301581021095840803d24814042d88402d074200c4001010440034110008065000d0300c450b90341d240c0d4080d600407641d0031001040f142c00c425070141080d13508184 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 936749397 1250 936748147 936748157
    0x61012021f0917160b090d0312090507090203070e090130080d0e070608010e010302150c0a080306190f050411130311091501140a020f0303040f0507060507030807030c 73
    0x20351003c0c5907040303982c1d0a0005201d500102c031802d80c45210303031551030002c01c1801c512906090001c00011412508410010b0038000c5a00117100300031816000362103c0c039000070564050651b00c00307900c0b019603c04c4501030001401d01c40c0e085a42d2400086450588010702134500d03000098140703400c203120404895440450000d4072100015030400e000309824004034002040301d0100310300c06864140144c00440500c00302000500410713003400f044904403501180d03404000c0800c1040300405110322283c04482e07000c0d1611900a00441c80001e6006100030ba560300c890800c081000c20081d542c0b80100701c2503c500c08030070816132815030000c24603006415045440c0581107031018803064541d52048561034004060302400e03244c8189110f50210301c076a481641a204200001c202c0d15081c0650511044085421800d09100b0481c000460601c0002c03a0307a01c5c181402d00007030118002d807007201c3c0b0340305101000c10703024450000d451030385030705464180940c2c039002e4050b005040c0070038105003044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 936750647 1250 936749397 936749399
    0x609090a0b220507050a27021e0304060b090a1103010b031509040b0a060e280612030e0a15050703111912030507080112020906060714061012021f09 65
    0x4420b03a007007445182c0700c0c00c000c00c40e007441d010074499060559445a0b280382e07c0403501350701c0d0709500c400200c041c07005004016941c0810150b1420428052003002c1c0f103622000c8100010403034554040d0342c1504007147c80100340c0d074500c400340d400da40e8502407582e2a000240010810504030201640d00300d40c178001208814042000450102c00045805546000f10300b4140301e220301c00c92003618081d10400411201d580340c802c000c075400c41504182c4d28000e2803801c20380d9810801b01c1d030008001d810031145107110a050307420018070080e040780d8500c2c0300300b03018980011400240702c03070181c5140c03807601c5903401c0c80450344060311010f590000160003400341104000c0300610103030302c52889034482da410742d041144040004048807401007000c4207012602c001409400c80f03107907000031090741c1142d8418055035401c1c0402c1d0b003400390000051100d5010043d112000f0408941a4414010034010740036040ea510442458400190f0340603422000d9814520090325000701c006c41d00d14883e043c045107407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 936751897 1250 936750647 936750691
    0x31e080304120e04180201050a11010204060c050c1c080c030921010e16170309040203161706091819030807020708030324270109050609090a0b 63
    0x40c0e008a4007255007003107040e9210040b0342c1010108000843c1510100081c0b032040c0c12119a2104c61180641406004142e000080d07101d0701e81180c006141c10001c0d51143e039240d0f806810f2601d1008226994019014111035909041090314607400e42d00e484a01441510b4031781040a5200440968042c0000c1010a000d034540c0703041009111201000202d030000d01c01115421102d8500c400c4902ea007101600d828019007021030402a511140b140e0180200059280b40c614843c80300c6054100e8008003c200c0761403000564800c10071241d480e802591560940c1503240d400c8204c079884d0b484011f00c004125405060554541c1d1740558000701d46510300d5041046140008012046001801110801ca51580d0600c1000014681d00300158150709000c0c401c072212501012000d40407611194035607006544114501c141c00b40e00c5010022803038400a400f45555800740203a11004e810000070610703d00340709203514800c031201c4020300070148241d40c4061707012030b003d00340014821900b0341c40010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 936753147 1250 936751897 936751913
    0x5030f06540a030206060907091a0406091a03160504030206180a0807080a120201140f01080c01050403050d230c060a0b010203120f0402010909020705010c020c040e07031e 75
    0x8100165100080301c9000c0d00e51000304001003400104068105007080400a03030000b446130f0b0854001c464600f8565aaa20225502e0b2042d921003114443d00d241440b10896982000b403080d1203466542d00c3c2880d031580f1319206268510645001c1032401000000d00e00303e8444840c85144101c1d14045241a0341c07034001400310b03046000210494100c8460f0386105e850a445654010701040000e0481c1074904142c0540b25510110f0140c810212410340c0e400f41032003175201c80c034000c401209503442402c02407a0306400030b1003401180da03035108050841500350b000790305440850303921000034888440391402c11038010a05003c1c00c10704040301101e041580707200708098905800d03400010315003840c0101c0c0c030109403100701c00c665065401c100240e4501c15580e0788203030781c8101c081111001540b6280b00403910416281c1c40540300390b1000c074400c02044010340000d444c2101076030840f00703400141c80410040b10350420300d14010340d004030000c0000550a110216561401c1380c16450360030600e442c3d49030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 936754397 1250 936753147 936753241
    0x3090b0c0c0312162003040b031003061b0806040b0f04022206020a030813021c05070803030a06090c2c0f10020313061706010507050118120905030f06 66
    0x4480161010404280d6074084040341d0503140c4040c004100302c5e00076019070303140c0c0318a0007603040d44d410010000e41c107092a018813a00440d48020304000a91400c0d402c600706100d4804d03804009500040402d400b40b41500400c50000700c024101030640c076000d03041100941c860000503003400401011400b50355648001040249120b0f005071144000c5487c0081280c83d005005076080c0a02221110141e02c84c0780c41955010706524010b2110001410310502d000001e07401120540302c0042048042106030700610102c400d410343c24400d241c42c00400b587c040c0c0001003010300c411002c49183d22880ca81030901012010b01400f41e0f19441c0d900ca0100d1000d85025100b400540d00c00610309c0c004103140700b5180014041c61a0010b003426800140321034207100a480181081400305a02043c0002035010400c1e0b5489113006034010310581c54102d40420a64030b101011070451000002d40e4100420040510103080b40640002da690000703c6000b0103551035a1102c0c100d2070301d250700038840c0e0f07141004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 936755647 1250 936754397 936754411
    0xd1506080715030203091011130315060e04050c0603060a050306180d0804050307060c051b0d110a0c050d0302030f0703111b06030f04080d020f07050d03090b0c0c0312 73
    0xd00504210507030441480ba001c40004252041040200c074810200314030549500800303012592803090014000c86000d0b01c0c402c42c0c80c0307041c03e00002003080742e400356400527001e00110a1250f40d03950258501d140300100c1c0c1c0a4801d800a880c94407130b6151190045a200400418040c0d41302d40f1203011a151550403a490940480c40350710104c0b40f00030401400c8083c590915100c031151034a0340d92240c580c0908900100784540720385243c00301c68040d078140c550395101004041d02c840102c0040d03a65414800075401c0c04038135000c141c102024004554101465000304407586150b1a000611038040c00003102070382180410b0044182c0320641800600a0901a985100d88401c10300311060500c00d04e000c4421146d0421140d812858641d0b409070303030740300d401c00c01d9114441c0d5507400c040d047d038459401200055480052001c1e0b0344080117015000c2c842c052411110300d0300b8403005c01d034100c40e4164409003542c0c00c00b100049820f000340000704400404001600d08110002d00003400c0c84c5402d41e05c2c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 936756897 1250 936755647 936755653
    0x408030f04050315070c320a05060a0c020a150605060a0507120e010e09180d120b100c030305060a09060b0d1d0c1512010906031a0f011e0803030903040303090e0907050d150608 77
    0x120b00740702e02082402d8010344bc42c03400708803411000d20081d42d102040d28004289510518429200038200e5002500418015004980d2500900c10060055101c000f00b10360428000b4007950503203200b04a200603100060b1180481001c04500b04281c01400900c2a0055807509810000c102c0003440b0070505151141c603100407403a007844070101a540c00d00c1ca8580502c0800c001070009560203145100c4858060400080d642c075103501207041214603402c103083c042d050000000300010404024070202c3c0c90204100030f0340a802c414014203140b4a034003070300b05510076124040c1602c0d0440f14443d80c0300600001516006403011b80c2c95184400740c1c41465019034520b010410f00600080302d000240c42c0f01a40281407400705080c4100304010f001e03002d0300868010b50340c02d28101c601808406400c5050841e512880d004604e555039134018001180014076501e800510016030301100c40c0034a2044015005050600040c0320039500b1400e415103a0b0f2108600c403520354041c600c44c03d0003502c6c4010103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 936758147 1250 936756897 936756913
    0x1d0604050a0303081e0f0a09050c0a1502150c040509060d1e0b06010507030807030c0210020301141212030103030c111c02031b0d0b07050408030f04050315070c32 71
    0x13460031140c182410142440c0341d00e0803c1803480410500541c0000347d40c600050010320f6090540c580f61000b0725081d08505607a0000c42c62072440101399408108560885119403c3c010008000000070340b8201160b540c240000c4c007441c0382210409a1100d805820741c402d41e080c0b80c4a079203030488507803510607040d054a0b120700300344040c1c240d26a60080003030031b000b4606461580c0c01001554010042410181d660029035011482400b0090682e50006000d54032542c480c1440c3c55000c0348140202c2c0318040201002440000c042419040851500c290030b046030f00c2d5031002d460345541013200f00c0315901442d003421140c0e55140280e00d201c1c03000080700f0540381c2191062615281119000c030001c8141d074250b4050a5890720f0754584401e50140c0c092a4688070740358160b810f0300803038018014030b02001c1000000030b140f5802410031a03008404170380181035040a001e01401d0182e40c50400191038480180200b420044060010400c00119540d620f079142e411108030080e8084c1c8a4a0b07070050b4070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 936759397 1250 936758147 936758161
    0x31e0601051e0906041e02090315130b0705070c080610091808071505010e07090506180103020702011e090314070e06150c0a11040f0c1d0604050a030308 67
    0x88540d0140006803055018109407546042a40328003101203441403030038030300003501500c66410a90103441d100c1214015140d071a030f95a0b02a4002040440c0280b003403d8464152500a07003860780910740c407c801d540044407a4a4407101001c0007400c00050180070098040064040107100740200140e0026180790700b482e940341d0400301001c2c1d03c140641070400c08001c020f0303460b0741c10401a550b40314040c41d0b0703508141e25000b40882607a940b41d060061030040000307441c02200c0705481c401c02e5540d0320480e015841e40100b001c90b00400303d01204009040a2602055000781d00406031140141000a081c06040781c142070321070f907001807103000108045010820804880405400010140003415450b400d1005038847e034407009203240e120b84034400540c0054a8114200d8403000d6005007640e00c20282c2d41404d42d012501001c1040c0124500400f0000301c103100d200d828190001995143c5035188070848c0c0092802d1002c00a550140301004002003030b03030318503207080c0080d0f100e0f841d941e0040c03030008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 936760647 1250 936759397 936759403
    0x3071b0c23031b03070b0c010504150c0206040b040f050f01060609060905030d030c1e2006090c090601020708030d06030c0b041202040906111c230a1109031e 69
    0xd001000d0512448072001658000c99041c500082540e5906202e60b20707074000920306030459004c134520b000002014101c041044d040075110b240102002c5080c6500a6020b1080303410010403140180c1001010500180c0b4400d409500180104180f000300301050303c40c0c5003012861a000c5000740e54800c41000000d4102c40704030003d10440c184520420302d4240800d442d688540900ca08040e40c03142c80c3d030445800741704a403030610020928056034480849018080a400500e0340803000b00e010f682c00e05400c000212103209520020190440c02c40035014490240c43c007608660641c0240310011882c19010000762503099203d080210300e0b07a10f542040a00c900c0950000440e0120400091003481c030744080502a040d81a600000d4520315428180c0003082c6c003807000224100005a03012800d016034105101003000c0045c10070564114084010201d48605500405030303a000303001401009c415403101341e441800446045c0b802060b0000a42000381044000c401810004002c3c04900810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 936761897 1250 936760647 936760679
    0x20040f1b0e0d03080103060f02040f030c03050111071e051c0305010e0a0501030506010614070206030727050f060903160e0106020d030b09060d03020c45070503071b0c 73
    0x1520410342400711920004c203445414000a0041a00d60001496000e0b6a0b412a030080c1412080350903001d880e407a10324a100d00394030081d5659820034071640102103208007152441c95200e141c280e104466049514040030815500b501c0d24040c4160603c03480c2000341c041c40c41c50b41540d03400500340d03040c110840001c100c003810281107540f400d001440011800655181550568181290305254410b2060490310a80c00000d402c6000801801a103d07044448400166400c0802d106500720000e118012450b0740d100b00b6074000c5500d007000c0c9050034540010111450040c0541d09503030100e441148450300c9a50224191042d9280108842c0790f05000b4076039904410f1409000c29014040050807d03071020b40018480e49410f4401c1c0c04150081151550190000d4000b54128019040c1a1000558440d00c080012015107a115030050b1720350f606002c01203a10000055600c1d003150407103030342d04010a8a014020078200131000c48030f104802882151190496843c0d4600301200900500c4003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 936763147 1250 936761897 936761899
    0xf1206091707031713030804080712050a02100b0609010e010e040617100509060f1e071e0201020c060a02130801060e06040c0e0f040e0c04061403071220040f1b0e 71
    0x1c80c00500491103105c01c0c40c080c26540510f4030107190349441c10b0910540c407906100924400048010458481d08103010300030b01016902900c40da05035969648082d40e404410701680400b0421003280d40f980201524142a9010316214031101c030300d50003180450302c05800214900707151031003820344094100980340750714030711740300510860800301142c0799140d401500031400e62800200003821200c0d03a10303c0d440950030f41907601603182040328002d01454880b08504190a0092407202103a034014000c64640b143c040d00101a5540c3c0d1100c104025080364011903000d20010314006030b244000d01030003001d0841140d01103081d0814004200860300d0185220341400703540400300446036200502c440d8500c0b4103840c08648214045162400c100d4480080d6500510703055020492089026142d281d0b52415421908000e845a002c1c43c5403d2080f03400400358404a20385900d1511402603118154a000e0808929602e1054000043d110640e000f042e82c1d0002d0a199100554030a04610180303134 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 936764397 1250 936763147 936763187
    0x606060403080301060c06020d051e1e0c130503070602030a0306050909030702041d0f03031906080d0c0302100c11120a020a11030f0a080d060f0f120609170703 70
    0x72441d42c9006550005102e40800c0c0030340c040344001800714075011600090b01000040002d848c0c03a202d912141d4010b0407950881c80740180004040078140001c200c0c002c0421030318000d05680c0c00900f203130541d2160701212200d031264500096280c40400900c800f4110540243da26600300d048000c003241c080d5070120b0311480180c414400c000401104403a0900d405030340104064212a428129016200c141007809104001303a404c4003100100155010f1310103451041070a450101810064404900441103d500314000040d9200e0007113180ca80164403c3c01601c8007086608285030440b031481c0c1c090000305110800c0c210554900b0f0283d54154400000e0213410305d07000141c025507035208144020900085000391045030350703081082005034940c41084903440082c9103010344140d0400c0800498050406101141c10040300c108401a1407001040803403085c43c0c00e10510000343c414400f0b136085030b80d03070046a003c603080c1050500c0382108041895614140d9140041500f0446032100740100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 936765647 1250 936764397 936764399
    0x3190506010c121d0a06021b0d02011e020f070f0503010b0405010312050f070c08010b01021e0a0f06020d060303020705030f151b040806101d09071802040308120906060604 75
    0x4000e00e0303003e000d0345107925240c00e0003d0301d030b02c038000d00b0904e4244e810741c4012034000010700194005070745000c901d0b0380c3c1e49881000c0c1101041c0b020602d0070304402408502039900c0600510b821148807400300b42d9230700c11211001903100e04542800140e070070006040450340800e00550034240250f020003102982c0170045589580c42c0d25506000061b804c4003041400164044502006001d0312403003504001d10070103142d501c1c050785008044d000c0b40b07d4050b00071884141c10060a50300d20000e02c030164800381040b05500e0b91203411824550100f00ca02070760a0000008041940c403604001c1c610940051420302c5c100401c01d45003d003410300b0b5080c1c6900c041311035200c80700801821a088840c5910b1044110510102c000303560089800c42d06203481103408104008102000080442e50300301104882c01e4925040020603d8003210078148a62011400700300000d150500324070021019480182001c1d1240e80c6c0140c2c6600040d82000c100c0e0448050014090342406041c0d00550210b1b402c80c038007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 936766897 1250 936765647 936765653
    0xb0603061b0c01021c050403031b020c040903090806040f0203210d090822090c0323060a05030d20160b03060a030218040b0a0203090709050606040b03190506010c 71
    0x103404007210700012080e012505007000312094066038116481000302030700e02c0c8800e44043c0001c1c5801c41d81500000c1c14a505a444000c0e95520707600581455806401c440280c4d0b801c0c4006041807150032010841c50b00ea0000d05081c0a0104074000e51280d848540000c4c2e4600406144c05d44440403040c45110704a08411585110012a0341810300b074000801c2d1030605042880250141ca48810071205c0d080580901507001d142c1c80341c0664450b000200700601c8403a000b00d0888064080ba03200c094055240d010100c0b540b4010b40e0380c4100c0042c40d0b0540c80703844001080c1401803000d0104045000401c003800e41802040c40c03c0c14400c01c07080200f400d04001039a02003603507010f03c500d00b803002000002c40e01c43c1d1143d00c0007402a40d0090300c000e0008080c841110300b2200100c500f540c0c0124001c001c603050303200d20f00840e0301030000d140c0200410f0741440321304c400400c8050540d84e4040070404c0009184e03142c4c0406148110741c00b007034042446a60300420410359000400040c10032005035605800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 936768147 1250 936766897 936766921
    0x30c1b012001020705060c0d0f02040e0106030906090212150f0702030a051b030f1801020115090c03060513020408190b07030f0b04060b030106021902090703050405031c06030b060306 80
    0x5003990501200c901c840d04290080c811442d02800902034101003013401060760000307140d4201290401c0019051000540c4100e020358066800000d142400401c00d80d8807030b4004140980c0550070002c1c00d68903650005d5080800401640c000c0d07001080c984844d41821030b0803543c024075451924881303103044500203487c0d101d40a40001400b001090141140b054a2202e602c1c41c9018400c40c0d990b180c48000c140c1268204544500d1500c900541000d8107500c10b000349180700703850304200d6841d0350500004201400c0342d280d08604140d903481000940b0341c3d41346002e513090024180c0040e620313820020024100404011b1002400f400c149070600000c5009242503400001c0d45030000740082310705801c1c80501601c00d00154841d0610802184000044008504960080c2c007104e0326520040e207900040c400030440030b58880e0b40c00700000d0b041801ba0300f04c0c03a881340c801d5042d1703460060024210b0202200d00c0f1410b82c80d460340c0709414001c000c040c011042d04008110300611491521104c1140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 936769397 1250 936768147 936768167
    0x50103061e090e0312090304050a0b1204080a03090618110306041101030b01090b1209060703061202190509010b04090b0111100e0319020f0d0e09070e01050d0e030c1b01 74
    0x4641e5643d00700c0103484000a10a480000c01000e1041680d800e00302c454a50766000f0f400303003a1158a0000c00021080c81e44001c940802d8070400c0350b059181d0b280d40321114036400c400750307020615849013001c80000e00307a4490a0140000c40701000c035802c00313905140c002d110603408503a0103588004140008284a1500d600b02c4403c04d10f07022078450f505000407603040d0036651000c00c0134100030882d001d40c210ba428450384030348019422100039948441c0300303c068500d18424120750b00c4130b04925101500381009480c018000d40b012941429a840c00412049182640b20003415103012505000b010014080c8245281c424604904021410308519441d401c0210781601c06540e07503001404480b10134010b4031007803001d84500c090407030702d8000065115104440002440d002d50390300310303040070b00030b8501c0e8881e0a40604440502d640c0c01c0780c19208002240391a0b41800020700540060000c0e0307001e07242c040f8210202640e10341e40f42404151500d10302010b46ca104441c4102a40180e0760f1000c0808 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 936770647 1250 936769397 936769409
    0x1303032720150d09080414040c02060c1b12030c0705010606090315090606090c02010b15070b0106080903190e0906012a110a0306200a050307030504050f0610050103061e 74
    0x903640d20340f10707410708014021080e00401400001c0ba00090451005c0c01c140f4040d4010394081c4013807203045404a8440380f04859400010205001301c1d0070820a0b480b4100c07407040184c0c121210120f051100c0070301d5810803183e19003250400100007007000340a0280e44002c01ea107040039212142599980e040000b088850030b130091b80e03a030681c68144050754115000414854800304004110044024041d01210402c94000c9000300a9610b005800380d08540e07400e03402c100c902e0016401e00e2030499040f207003d0103140c41403109011036040e070a0902e07034030341044c08641c40e5800c040399010203101540e00000c042c9410306c41281c1c911000d40381407c84062491103403d01c1e010100d0300c3c80c5884080d50414100342608401c01d40b0010040145a40c0282f90003a161200140f48252a414100711481004900c100140d4240049600716010303030005500070b1b10038402d640180da290b186c0b00340f50960484081c2c8001e04440e40c00c000b196014170451020744954502070044080400b80105014054800c107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 936771897 1250 936770647 936770689
    0x80703030e180a05090c0a0e060409021923010810030b0702011e0f0612030c120e1806010e030c090c0901090b0d0203070e060c061303032720 62
    0x84200e82c0e640d00d040301c8014031650003901c550410410400c003c2c4411110505217106065901d00d0358038000980d4001c90f550700c0340014581c3d0700e100c207210140000c01c2c030803a00000c0040e584884140c0114100000e0a0707482240c083c2400d0b00c03142d0300c40740700079644014140000d403004c2c0005072000d02241e00541c1d4102038004150307140c9c480e0403801010a50b9030503450b88402001e5100e11a015040b1000400c40800b0900420380c555403180703408014600000c011501c15140700340001c03403c2d132160142401e1410700c01d0b100100b640c04125030100300c1c003843d004a2070b400201b02d10380d03810031803c80a502040d070041a080c64104040b5130442c1016107440c0f180100030400100a80c4160091405031001c10001034807440d0659905003e0f40050341c201c800321b41040e031442824144030095600300d4a1040080c02941c864443c2a05000e42c0c56000380c080680f02c030f0320050b00022000c40c8502004603034880040c07904543c1418641a5031010401daa88103004442c98034598035540608500034000c454 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 936773147 1250 936771897 936771917
    0xb2b03021204060c02031c051e0d0504050102070c0806090714150f040311060f18040b030d09030213050c19090e331309051608030301051908070303 65
    0x1003a850403041c03a080a4a4820006010a04540c80f842945016109800325189060341c403285680c1d62862074101000100d042c0401d4501150303890454480505441c0c10f203150652074003a030f1081e80c00840b0180d0b1580c4d000203c2c50108004000c6500003040700001030311480c1882c0364816182c1705948204a40c0303a000e42017103c86035454981d0120100608252103642c1d2a103500d04e01e0740391700244400e0711040c101e40105e512500341b15045400e404c6040102500d0225603440d41c5600784060700c0455005541d03003201c0e100301e4504110282c88a081525141c40e0a45184100a2541010b0300020b400e5410f0009015204a14030141d405010b00c1808600c3d403c00c2411040307407a42429405144240c0441d014450341c04464040c400051017440d185c000284454001c80103d0364582a200e48c00102c20760007000c176061141e0102200030301c070b03038159410710712030840e00c040c41d2442d90810081a08008010081450007004002524440401c0000060300d007204040d158101488058244089181 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 936774397 1250 936773147 936773153
    0x150b0609130e0303010e04050d0c080a141e032211010f050c030a0f0e1822050a0515130506071209080d06031b120816080313060b2b 58
    0x310b070700c0d08000d01c00c80341c40e9a5506081601140c0685090350140500e804e464200781c41207109125040c2c0201c20340386450741c500c0c01143d405c03141c9000031401d032406008400c07881c40003d06036210302e100c1414503506da0503c0c944c00b1204009405071412000040d04070200010743c0c89a01342000e003424203004a9034045c6a4003943daa00c40c0c032411110320b010000c1d207528113582201c90261070714031903561055851119014448520181c5000180586801001031810100e0b40a1003940c0c03c0c80007181420304609950b594940070781000100c0f02900024040a40301e2044160550301011091040c4845080c0341c488a840d01c40c00b41005003001044100d011246070341e500000e0702c040d4820b464603951804400360388024011400102c42c0c010314005101c400c045140c005500344c40d4891070342000d010030b542d51105190300840d82a282da600e00c0120741c003c50a00310240d4402c0305180a203815544c0320b1310f0f003901145c100961061068004d0f5580442c1e42a0904002d003c2071907901081606c80040c5c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 936775647 1250 936774397 936774401
    0x915030405071508090606010c0312110f070305090306151014091819110d05090a050f030d0e0a0b15041b210507020c190b0307030504150b060913 64
    0x50054410303c07480e024079000071503100c011180310f21001d8060340c005841350401101c00051584e4080d001440c4052811402d503090b51080d41c40002d10340c1140d1916200d403462545641085005801066010035034412508040c04015408140c03003805a17a80084100001d00b4407908680400402008a68000440c03840200f11400c1002c020582103c11240e10b480c000e03950001c45007808600010880544102d0080c0901030806072214603046c1001d40c0f001e410802814018181400d903c40c0070002c101254003400b400781001248409035030b50b040f14509a400b51140c0d041100354517031081c074a04010481b903000d0a0707007100014110701e001220900010b005418841e201c0d840d483d8420707920491068220b90080c045004c5030083c540701c107006030300000489204503405805604000e002070714610340190303503500c084551102d000900707491700c000e0490360300b0881300480400d40c0c541c240304c00c0c80101c035405442c0e00202d41c0184040c2c0e0340320010030801e01448060030700919140c91028203c14032a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 936776897 1250 936775647 936775649
    0x10b0a0c0503090d0c0602010b0306070f0c02032d060912120c1911190b010608071e03150b03060d14010e030d02310b07030e0d050c04050a02091503040507 68
    0x100030807402e007031030b01700900200c51500c940300243d841c0c40f8100490b1704002c0380035403140804d034440d81000000d044042d01c02d1580c0340801c0342d25000b003800c00b41d28103211000090a100d00000c0d011079084071100b440e4944000940f11403581e03408407205d100c2c068a008106c0e01d1441182120000c541c50311004031800d030044000a40c050110700c42c00d208060750104140500080a50440e04a00f0300e0744281b40107040d0029015281c00c001d0001030201d207000b04d28440d0000c80a20348a000b005002529521034014640d0040000761980c2d2030040b1200c082c031946010b0030519190b41d1860405000050046072004001030140001180501d0319000a5010000106003c07003130729503a00c48183c07440000d40c403415594910402000500301b4914410034841c10089908030b41c40003c90400d61201c0641e00004000c40c1001464141c0c0012605d030030030410402d03449800100b00d001c449200b04000d0380d00c01082c10081078814080c803002942c9000004d411703104da810420340d03a81c886061a03800c160765 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 936778147 1250 936776897 936776899
    0x80301091503060e280c09020a050702120c0312030c0315041e020918010806070e0402252f0423040c080601050301020f0f03060414010602100f05010b0a0c050309 71
    0xa02540080310300b4020a400030801c5c0c02040c0c014010760202c52101d84131850010242106001303040030b1041c500550b00819060419003403032402c140007640003440d00d918080342c1c42c409030001d0300394806d281000c024071000441c09010b5142180f030328014224003404000c1010104602c91240c0050f541c070f855021114000c07484002000d07a103005402e0001035070054000c18001c001c00b500e4411520880102d450603180b04602411030754484480807243c0b421400c98013503202c5d42c20004034860030800000c03c2c0c003141d20745a0180702800c403400c0c04401c110302284204020944454041124000004103d661150403900000d1446240341680c800189121000d01d09100c11710a000030310a2101240b030880d4031711340c2201c006030b03225801e05080c0c2c000c2d04904002c0910038040b00302111a040c01840c0d22100203400040d010404c0ca0b01c22030403441c04c3c0e02c08805608110b489030540308981c000da07000440780c10340a200a5240c08001d0805201c0ea00705501086049120907003004014422501d020b60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 936779397 1250 936778147 936778151
    0x16020d05010e07170a020d0f0c0e0709061805010f1404080639040308070204140f090705010804050a0318151716090b0a0e030a120e030a08030109150306 67
    0x4001c8007015a903c403a400b03110100d44019210b40702c1c0c10000190f62101950140c0001c94805256a034a0303903c01003118201c0701801852000b06400301c694280074801d40a030b03920120910300c1d22002500d030202e05c0384420704914940a0a00c0280d1300211043c61041c2103103020b8034020101c00380707203c0034091034000e041140114000d00030700c2c0740002d000c8841001c08124001a2aa140e4258054080c4e08002c10b40229014041040410a40320180071f88900280c070206500c4855500030460040031505203106600d03400074410180c0c41001154090328081c00d10480380c3c01c0c151500e41d518030748031400600300652a50514a01100c004424000f040368115605016143d01000391004528604c0c1410f0035003c040020305601361041c80741c013817100c0e40d210542c03094104034100c0c2e451307800342c107684052242d01d2480040548041040b0400c1a024509814901b02c0590000f4254045459494030bc0e50004824401003500b94046a04403000ba0900280000d010f9100c1030200c0c1c019132010b03244034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 936780647 1250 936779397 936779411
    0x11d0616051b09060619030c030e150109050604020c070b161704060305070504060e040e0715090f051212031302100c06270803060d06110a090b0a0516020d0501 70
    0xc0d42a620418140c1d42152140d10581d1001300380701d05400740307600880c0840142d05030038a00358026803003003a03190042d240c00702e043c4a840200343d1800b1500c5041401f00388414004114041d014460381d0f4000c0c60445096240c50410840e0b5940c0300c7c0c0034000c1e100103030301c005242e507545119130380d610240d140c1c4950407000045e41e1042c540384540040c422000800d08050008180c1880760048074140c502948a41003508420400d12004008080c2c52541c40c1c400c2d090040791300c15a6440503d00391416540d403800e900c6c105051210044003550045018400c42d030080310490f600030400504512800400507125520125021a05421800c01940200c1d8455921801603408204404c889010b076205120106090241e804a0b00000444000301d000c1c1c003041d54000b9504100a50b0000001001005517141d1074a03298115038500b03180c0300d94848001900c0d44403d8020b20004000c000030340901e0304181c441030340600765106054500c0d140b0710941310800215a240425441e0b070a820200070008a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 936781897 1250 936780647 936780673
    0x1a0a051b0109121106010e2701020409150e010303020c150708071101030c020607270b0d060e0718090e010e01050a02030a0605090c071101090b0a080a0506011d061605 73
    0x500070740480f03000001c01c40b224440b082800058a54100d0343e0f0518074841035642c3c014111464a1003a44282c20b1100803410140710140c2400035001130181890300061141c2c118240b8003040318144c1c402604500c0080041000c00d030003180b0040135070000d44441701c40070b00010507140944164074009042c142c002c5218020322038000c01001d06a0b40a03203081100303103103a00742666540b60840b080c00025240d0180c1e145951030b1683c0090004510240b070000480e141e101e04100b9401c40e07203c42d600e4a03695503080144045103188944c1195041c18017548543d40c054880180849500440954580f41c0f4449008401f09500041d800d8510500800160612aa81c030700654401d5681c01d814508211001c9640c0c9021803956014910483c01c4c10715051195450b9440d407142148514184020030318001091804000201200c1c0710a41d0750405618040b1740c03141c04c135000906802c1c104007043c8031115840c000700c03c0c9900088000c45a1a48030080318003082d007505201d0303c004215015680782100302e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 936783147 1250 936781897 936781913
    0x2102060c1518030c070306020c07050405040803061801080712020a0504020a03050421021b01180b0a02060f04050a0b0c0f0c01051b2805040f030503131a0a051b0109 72
    0x4100a4042e4044022000d00b00d0b96a809940701080c0250007000b410000540c00307500500410007031000b0744a03040e5868000404844040310250b90005c0002f080101500d0882d01c151603148007800070010170350620351a0b41e03807420180508000c042c100401c0d1b1041d959880125801410000c1055580d40d900440040251900b604c7c100d0300d0081c0380c072124003002c1e01c14091035043d001940c004e024030704200060300314520551003c20705001090410000e0311034042801c0006c0d140304e0b20710a03500c440001000307160001c001e068039482034644081c00005030010540390380076900541642c5032511340c1e109803207a41c403580742210a03400c1c00040c0e000d00480d06401003882100c1e21003402c00c60182c84500044584074160443d00c15008015841824481040081143c1c03001b13841c00500b406c0e00d80c0c2a4052500d0140c00c2603555510200300d007890f00f41c5200d800006001420010340b0494500154035580e401001518018800c0229650b01c0b10010b9900245020069500900c400490b9041c4440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 936784397 1250 936783147 936783151
    0x60e040f0c120c090503030f0d020903030403081801081e0709170f010614090622090f050c150a11010e07060c03080f04021f030e100b0a0f2102060c15 66
    0xba00c0c100044020864010030704041219000750140d0318008400d06a001c0a03880b5001e046841e5a0034030070740c651621700b003000e4800781d445947c0050381c40da01136809403038030b98403070301402c2c104542131040008400703202c100b50888400068144045131100502a40e04400c16000000c68140000e240300300c008000410703c1e1944d1591008015460721743e10311401c51500c0950380b6400106600105109050440c41c20580341d96102c0b05c402c3d034440c8072001c0b50948502c10b5041d01d175040403108280601406000510604c3d400303d40780342d01602c51074107244c0180241a10700c0305000030140c3d41140802e00790040e800581850050b0390f02c040d10b441c8003070a40d80c00c00e070050b030002c0c80703000004500403005c00105018030f4006024808c81458090240e002d045840485030803d922041010000401001100180400102c01040e0341c1e081a052006401c0070740d011400d02c0403a0703002003188882009070a40600c400d500d118454070703140d0010031001c1c4100b000d120002d10407160080c1c0088484c0746018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 936785647 1250 936784397 936784427
    0xd0b090403120606050306031c0c05011107020f040c0e101107030b1005010513050423090f012007110f0a03050705040c0c03081311060a080a14070207060e040f0c 71
    0x80b003c0d4590404454a000440d0280c3d0141e04c850300d049a1103d612244000000c0940b030141c0c004c101a81e20709007903480c000c078a590344100c00310b507220440c40c00c42015441c0140a0b9803c0140880058004003160b1540c896540100c501d8507900314050b120f002c00d441c47c004810102c0d900c00307659150800c030801c0c00301c0f03c040050070145400b10761984640d040f50b0701100100041008203040208100007014800360100c07869a842e101e88281c4680c801409100d00c6ca450081c0000c0c6072101046400c0d5604240e44021001c004000c4400000842c0242c6051907080360864803e5544140070070032547c510340c0300560202e000700c4000f04002d0002840400ea4006580038070400d0180c601c2650440c0c044c050090101e001c102c00502e00c00502007541408a0041c001d000074074640d100842e0059105070903041c0000c0225081140f00d020380e0050202e10405a00031074803034076041000a442e0070f1a4003910b81007041c290b25010075aa615003043c030784401c0c550403c004a04844070050801c0000300703400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 936786897 1250 936785647 936785651
    0x9040327030b240a0611010b040e100e0d05042c04080c0f030a09091a040204150801121110120c0c021314060f01050c010c0801230d020103020d0b09040312 68
    0x21507500c100e8000c004041e920242034244e095040c4001980d50b013034a0b4600042e590b60b1000c10391456602d90048074403056840c0302800301060f45c200e02d40d0039502c0d2003110441c0d650207170604440d55540801181d046801c1d05068684000c44131804180d40300050b000300850111100030b100900c13031000010b0848480e80000c0340c42c18002c0301c0f04d840d01c0b40078595140000c119810801c00131f80c0915000360070307036a800488100d0030003958000201280c0064000c02601081c0160503c00243c100c000513015180c640d00040c4800c94583c0e801d130481e024600102c0c040c1d4083d088421819000c0c1c170750460808026442400610200c240060400e610124107920901c00039555424420310392145e201d0150030f00c42e106507559038500030700400b0780021000da81045020408007990400a205038104c13640395030749110741949018510507042843c940301d10f0000e500e005079072000d43c0d1090441601d2680c2030034051f0302c89a194640d0b10040881d4a0706070f810030617030010001090707442001c19128034200802 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 936788147 1250 936786897 936786931
    0xa0305090706020a02010203160f050d030e150c0a030b01090e0c0d140603100e0312010305071412070311060f07060e010513020a050d0c0b040905041a0609040327030b 73
    0x200d139503400303425001e07003da0003c000390022122540040000c090260f042e170b2581c40d500744d6559182414020300c00300003da46000f40700c07000100340240e1800c0c02c9203040d50540c0b410325074905c0d1500e104824540d0141681d4889829069014040220042406072410602c074905005c14034840d5000c0f0744824038440ca80a00840e4102a400c80c00c0e006500190060081400c040544c1008192525280400784824484111401801001d581c043e40c4904090f0880c0c52800f2051440b1001500c0c400707103c2c22440410780194600081c8000440341c10142c0c4106440c0701d01d001c18800d10640081c01110800090b101e010701a25411990100d03101c1c0000700201c0d6552009102c00d01034800c0000e622180071442001740745002c41c0103030010b501407071031306602c1c5a98003401044c552003648101c1c030031601c4108010074422035003d50b0b071051400901d551030038580000003501c007010040c03004042c0980780b00382e420381250340c1105c548030749240d186c1d1000c16500d908100100758003c5038080c503818080301c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 936789397 1250 936788147 936788159
    0x31c0e0d0504050f06041d0901180c09200a08250309020a0527060411220902071a070c0c06090f090902100f0c060501120212160611010608030a03050907 67
    0x2201d0031248030034500c0008000d010540c5518030f174003500c910000d40d00e580c00007441c284819100082c1500c0bd1480c18045894411607805652403021060071000c1352640780c4d0400114082191401001440c0c101c101b540c4000140d809011780118410018400091218901c3e405600159920303000700c8240548940d038104101c07445101611038001c1c0f000e0034100e4045c02a10700a141d4000d4001400030825020302c60602d040d03900440200c5910014007000c201d00340c4100c1e810309004c0c042d010000e62605a03e034456000e030114085076075042e51800400500c060b407040b49102d2034a0f5005108a110343e944c1c1d0401407100b0401e0140600900e0805000034414101e0f2103400c0d001030b03016001d2800c43e401c00c103050360005000b8540c1824024404000340010700701c0d1142c0c034041e12400100d14051800b500520481d491040301c1324a035940203440c140c6220340341103d9441242da052030016100c408005205014000700d5114540c20310010074100c0710260183c1245201c4c03040d20b07046134840c694400d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 936790647 1250 936789397 936789409
    0x6032811041502012d0b0d0f0c030c0b071208070e04063b01060e120106120b0a05060901170307140a02010e010507030f0806062512020d02031c0e0d0504050f 69
    0x21000728112200710603000244017003a04002c0c0e0403a00186003d0158000f0784a0207000303012010200e83c0850001c0c0c1c24010004200c4910001c3c0c0f900302c0703101c0e04141003a070310740c511200240010400c0c401c020b0000340149104c1c90100d00922400703003040c40000d9440b070981c042514803504070540c41d01c01c028401205104150003030900241e00d01000e80c1646407039001e980700030081c0c0d034454005136643c06d2400525801d0003494001c204a108507500e0145034242565802806050740b0400cdd8100000d019a6a0302d201019054a20311900740260400002e44186036202c0c0340c4000309507010904004843d104041074400c01c650003078031209012348c1103000442e2107204800000780854024207440c1c280300e2041b28010392001d00900b48a141039904415504581013002404000c81054000c5500304280d002c01ca03258108140000d0003092008140a500d034002c010110882e810059524801440c0301e070402d0908070002070590780343c030303080032401025503115005e07150007091135152117480b0341002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 936791897 1250 936790647 936790691
    0x43803060d110d0507060e121c020724090902090d02040c02012301030c05180a0e070909200906011202161b1d130f141009020a050603281104150201 65
    0x1503405481000e900c9409c400341107902802c2c407030462240040c0415855031048011030903c21100302c1c60200f01d01528000c050720210b400045015005008602d5507490f48103142c42c81d5581240c010600c1740400c1d200b2801400403c101c0f180303d120510402e000042015101c0b8103990040d80001c2c6116240c0082c0840701c0f00c0c0d100007042090007400040d00e441c0f0160302401c2e01c28901c0d41620b01e070998840002c820740ea82c0c1e01e01a10307014980f1244500c1d41962020510200d182a00c40042600d001c0b40044e00038400650b802c46480c1d00064012040705549501c00d54095110032101a055000a00800c01e56243c4c0942400c003144400004815001000c501d07214100651035604922015503d1030f10b06108190101c0e81980032011303030586600d06100c603881c10107001da0000741f09801030040042048181c0c5c41280181002c2041c0304110341c0360342c01d2640807000380114185990115807100014403180001019080d00410085044102c82110901c000c0d0302c0d43c0240410310200088a185040f1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 936793147 1250 936791897 936791929
    0x90d172e0641090310021210031101030b0a0905010303110f16120f05070b09030106060507081e07080703120c0e0a150311043803060d110d0507060e 65
    0x8448900d6602103140160b03080c05403004240b080c01d250550002c649401d0311070a142c5013450700881c2000f20000c42d1038420b5845600c41543d40c245500d5529101d04100c103e0449604040d00d07581403285a4440d160144010180d4180402244d0394900300100520300404c0001414059088170f0000305100143c5102c10b10303220f100135004c1501c2e1a00c1e01d00f40c07944180c011102d82c030b1143d10400c00300b042402100c00600403910215a600811400c05084941c140c00c0f60003441014818000420806810b0305c0300148001c4412001c682501c0e03404819000310301c4010840040003400c0c0c000c240c2e2044c0c0140e03910554460501040c0c800b03501c140c5401e500d00b00b0458004019003030030002d1004070b5101c1e0324041c0071820000303004d143c54050b42580790b0040d00903075410341d2106900c001800012441d51701d29070500600514640140c01e068000344005005140300c0c0c0e00e001c0b104414008500c80380a40c4000c0105040314400032890016140c035061b10403c0003140f5003998a4074942010340398038410202d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 936794397 1250 936793147 936793217
    0x3180c0905060f060721051c0b06070c0b0901090506070f031d100c020909160b0702060d060306140a0509030d0905010b0a030c0905090d172e06 63
    0x41480c80c0d0000a0a0040450758080c05003500340515484800090001d44e00425200f41401d041c80302d0030b00c02040e18928041080020850b2589008072444c0c0120750242c000305c017099007400c1c0000244503000d084800382440090340710000d41d003012240140781a6600781c13500040c440c0c0d207004000311401040308c00340100340428511000248121550385038104408090041d009011012811150038490341e00e000c1441d05c040002945803554041e68020165801419001e0100341e080c030041300c1d5881034075294007000c02c4d400115a601030035140e01d10a1200c041000d01d81da41041e50150008a01540c0c011020001086102261b8003465201e01d1000c0001d600e4503245a42d9500100607120040c2d649550b5004141440c0c1da40150641c002c50103217000f0100c09041c030840c881180d402505d65640e640c04040145000d41d00020300581590745964220019580e0981104c8681524030003445c2001c0183c1d000361203003502243c00c005840c40d664a203020001103c580e03512011a203403003c40800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 936795647 1250 936794397 936794399
    0x110403120c02040f1a01030b040506010903080d0204031b090b0a0302030607120e0604080304020a060216090222031506140901120804150201050a0b24180310020304020103180c 77
    0x140900340c41c526291000e00000f88121600c0108422507004020030021000d42d204844400c1d03a2500030058074000484080100d81400b44c0040c1140d01d1621000742400070115100e81100c1e40350341a0f074011608003810f03403200c00c2001c205094504c00c50140c410b800303103000c582d13113101c0c100140400c00343c2c0c1e40038004010a441d0a00160ba00742c00700f28008505540f24903c500002c20140800ba0290788a100900d0700ca00701031041080c40c1005410000c115440000c48010640c0f00a020008441d5858001a5a074425000102500c10001100110b0f8003c00714000b00300204445000355010301d10200f00402a110f84c440e1030a28042000c1d42c0d13010106030010300009440c040b800000511034084246450340d01d100c2802c0002114040c0401b5175940c40c00c0044083c01401341c00d140440444c4c01d40b001c02c1805400008a064081840d404202c000c038404a010754a5603943c07440703000060072a012440f202000c48081c2d801103404a0009003080da42c082c801c88501d581d070381c1d20365000b08200125 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 936796897 1250 936795647 936795683
    0x30f0302030603010603060609051015480209010b0414040e07080a060b1c240b062208031606091a0c09041b2c03010c0f03110403 57
    0x3940016000d9603155680c0c41001000914a01c00c5000078a11541c001c5958501b082e02c0c0705e00c0e00303070941c00074182c4050710b0000c2601c01d50000568180f40165488841c00240c030042e500691000d007a41e8a81006282551000c50303038000c802d0051a0b0b01c2152080103d03030720307810303251006d000f54401d040410b4a48441510345148c1a00310f1102c120380182240d201550f2041c0d11460211000c2c01655003075501c1444641b1400d001204800502c8048031030200d02c0710b60b07600e011071102c00c10316a10614000c07656042c080820740e00001228003004140a8442c04030840300c600c031160f04041044042c0d0815000070b19040040103882c0c14540700c02c0060502d8602c2d4a41e10050000114111428103110b00209921410140c0b8640601c90070207050303131205420422b100807511901a41540d84000905426100b40c2c8040d080381c5140500e00000c1d000c0303c95141c03030405403001c954015415401c00710041a41e60740030906030024002030740e0900000020447e000c50920035800064a00b0040c901c884140c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 936798147 1250 936796897 936796901
    0xc0f0319020301020c060c03100f05010c150e100c080f010e070c151107031205190e030706090506160827030c0a06060810050c042903070c140a030f03 66
    0x10358005400503103000c95403801d4901340002100e20314203080000c0b090220008580c90194090645916119031050822002900c080404c1d0801461401c95244012034021660045a0840020001c075040584c41904440140285004000004440b2400550081c20015076541200d101048001080c1c03241981116125110081035562401e4420010603101003407080051480c54240815180d07442445c004000102401c0758a52450502040c040e0200702202c04510208034074000050440e429030f0440e00b94018200b02a1000b031801c2900300c01e000c00480c0280c404d11004038483c0398980e0f410001d96040c542074500a45aa49001000500c0e0305188405103d10708103808a90404041c062020318001502c0c2044540035200d0004110303140e170030001c1400000d03541c24180060728000d001c85503075010354031036400784d980c0d00d00d104800703200281c030107c101074414400f080c0e43c3d1a0224001c0c01041508070221010115001460b003c10703800f080d143c0700c9070341c540e4620800460700381003100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 936799397 1250 936798147 936798193
    0xf02040f0918050703110109090e0d0f020a050a0f110a0b160f0209090d020601050402180d030921030801050f03030703032403031205070504050a0e07050702060711030c0f03 76
    0x10505000b09007a03008a082008488000d51042038048440102800014083d010640c001070003c0d003481c0342c50032240310104d1100d441252601d0b02c202c840041c540308034640654030703001411500400300c201081c00303a900b14040310301c2e0043e004407015488060900030340d00706c0341c450019075980a0000601c6641ca044085c4040c0b0b02504210480009580005002c15025549003089a1014100200e07480e0148003080c010f00044504504100940c4001c03a403108100c0607183c884e0700750b0b5000c0f808040c003401a0f54007800c041c0b41070b00781406800c0040e10312034200318010380219101500004191811030081614280050095130621f00540d900303401400005c80c0140144040ea4200c10303481a140c8a035800850183d03441d03614101c842203101c000c440d0003600f804104541000280226241c0c0c89840048458462031309241d40c0e01c0d00070442e954011844000e41c0200001601c40c02c0c44401a041d06602ca800c0301034801d8076a01c142080301d800e80340e10728103030903400803060799442074081c4403046 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 936800647 1250 936799397 936799421
    0x90203330910050703021209010b0f04050903042616060c0b0403020a1e0b220b1902040303030c0314010e13060e060f070f03060608010b070201030216080d0f02040f09 73
    0x50303840e54240c102d041a51070480b03096001a82c0030411910700041c0c000495045a452802002015030680100c2d01c805020602c0354006d80d1910081413a482341081258010488514031102c205450f102550050b8108001000107114000308451640354441604084445544810480c0e414039511111200e00040054056001e000380c41d034041095040c007800c0710038500050185140851070464a080030280890340c0c2a061008002c03243c030a035100d2401d00d290480d102c8540d5940d0081c170500040e841140040166002280c000105a01034200d05a041c205403007d02071800d1042945031046401d10850800525001c041003886900d960701c03c80060281c1404220a807000100c45d103020b8003a60307240c030110802010031008941c0147c021000841600d001d00042d0300e4407000a08c500410b01031001240300c00500403046a000341d048542c00c2c43c0c003074540c0c030a071203141c180103520703801c10450b07840c000d401c28400d003402c1da00d18070864099403103008418904908028202c0010007004001c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 936801897 1250 936800647 936800653
    0x903030f0103030c410c030c01030504020d080a030f0f020924130b030106140a0804030f262e0e04030509180403120501030b0411010216090902033309 66
    0x140c0484110100104069400010010548a0464818040305d8111009119008051103440d1590003143e4514900e800340f8000c03601d502d45000140c40507040c180000c00941002414002c0d0325050b07084080c0e0107a5040081112851000481c0283d02c60b5518159205030340740146074a0030481180040c00c80c0080c92154200b041241c5401c0201e022504001c00c1010003000400480b0b0780300c5954840d42030044d03003050410501150107001d1400c0900300500380301d407002d101010f2038800c6550f1a502c5100f00e43e000c04460745501c00d03114009060300d24800c0483c0b0000d425115140c440a00010f41523090482c0402c4c1d0306d405c140c03101c0504090700880800c10104030700c0c500c568030b80403c04040700c000902c00400e03060500c0c014040d00d9200500301c4140b803d000c01000400c41d8001c64076481500400302901d660880385c0101e060000055503861800c00c01c41020032039001c19405444042d10a07011a8a4044024424505843c0b03080b03440c8411848203040407615400241d025802040c03450171 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 936803147 1250 936801897 936801923
    0xf080609040c092a032018100e030f1c030f0b06130e0f150d060e0d0903150e0601061803172a100b010e0915090903030f0103030c 57
    0x103d05858242942c0c0b21a6030302c2503050f02c40848a8080860906580d00781040f40990310300c500c12880d501600607a60044011400c0d0303603100004000c40340202e00040103034208c51030f0314002801c0b190340c07803800c00e0182c42840c400c05020240000c20645500301210040401a00342c081200a00454407014411545608220130143c981d9400f4050109817000e140c0d2000381004910801080b000301903c28515a403020300940107414030696051000650744118104054140000981444a0110424440c05214104581d400081241a60f21070040340401d620481d400740140d4100c864819066000000108041402120082a0351210b15141c0000c00d80e684c40301e40d161501c20260303078411000083ca0045c103503010400d0101c01c1e5a02030440000c520403144880d41ea00721420360f04d24541e92650400496070150b01d130300b4000c003801813440c006441d0640d5440c7c0c01581c0b01404074041c4000101180307415001109882c801c002034110302e116681780d6141107592100030f650a8440041442c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 936804397 1250 936803147 936803159
    0x9030c0d0b010602060c09010914031603081b0a020a05090619091505010f0f0e040e030c0304031b0e071b0803070801051c0b012918100f080609040c 65
    0x2090344000d0080c00801015807400f81c019040c070384000e1134092840c60400801c03029a07000000202030700c96000c0032115003402800071918010001a4100500500010020400118000401c0011a44504200728411001c4480d564403c224002075101249041c01d102508091405c50381c441d07802011141c42d0040709030107a40d03030041340c0c2005041d140c41c1d55415046620512000008000a1070070031521440500300400a14010401c001044a4011114a1907645801c00380c0b13400d030f0301806d03a0ba0325004004040d03560380c000e02c0119403090805402201e121030844112044600c0800300b200c1907950314100311600034450720080c48805c000200d56000c10200d9005d1840b03401076884d04041d41d41060204400803022042555101412524406c00100800c00c040e04640030040400c104064481c2000c0c1c074100a180084884200030030103072444c841138000e4858060054440300054240020101d60207208403030a0b10105000c0e40c04204181040c8045583c0980a10f81c1c54402c0ca84443c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 936805647 1250 936804397 936804409
    0x70209060d021003091709212503060624050705150106082a09010c0606170d0e0f1809010f2d0c09060f0207050604170d020703031409030c 61
    0xc6000000f03076034510950030440194805c6038588520740c2481c0c10403440d07d0010703d603141815103402c2c0001c0c00f08014090b40d0410080c0c803103115a141b1900404200c4044007407008c4445200c1600d05e14148440010580b555410b61480741108201c0d03030058008000c02940c80341d010305001c49540c071030404003007401408144a1400380150303070341c0c910103420001c04040640c0c0880d040110400f10742281070080440c1e00342111514042801d052103030000c903041201c01400340f07074041103d5225400031502c55903004030b002494015191107038409a42c11005005000310910341300c0750000c6010341c01c0e40e80300b01c0d5018501d522005100020900c00d56800a038415100c00003000d005001e21006070342000d45040c141b03a40a4a1300800c02c00c20f6100c018001054240c07203108401c144081e1003070359100c0c10303c01e201e03110141c0fa004c0e05443c0d0722a9a0100c0c5602210140071840b10750007150700141501e403001c501d45048035011b0380d03008848100c0455a401307685c440654283d141c40303a4140603050341c44003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 936806897 1250 936805647 936805669
    0xe040f08070b090f06192c010501081b03100f1d0c030f030702031c12020412150b10030b0303070507090c0e0a1212090902160213020f070209060d02 65
    0x20000d0190343c1c142505414900101c035000c40352590020802c2114000e020207402d01c6c0c42070048004540d2110524200c200702c99071a2030b2602d218103070403403030401040540040e4122040c26040321005000c80c05405009140c0160b842d5060300141c007180c06035001354100c10783d05080140002034400c3e54100c201d8004c400320310341c0150307500060380c0340480f80781c240003e55841d60786d1800b03036207084c16681c002515551840c102e420641e00c258035800d081803081416100c07150000204656680d140d521401201030340d113200721115601070b4090722261080e4084c6410142016002c1500ea01c2c401c14240e01030519200119014030007488003c0c0440d204001a1009284031113000801c1e51410788004c03c41c0303101e10591401103500c0c03a01008240785001400003071640018452007260301440f4120f4900302c1c2d079401009041c0c00130031078a04000e080e18403901880d20031100142990740c1c0b1050a02030f03018400d2840310262042c8045c5025003010000340360310403c024001c00c501c070007a80c00030f0056901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 936808147 1250 936806897 936806903
    0x1504091116150501052b0f02030a03020a150249050f0a200a0c0b0403110601090501060203090f030a061e1a09130f080301290c03040e040f0807 63
    0x202c45080118a82d68440c0780d015050a51344540412a80400c828803007111940c5504030b02071080041042c0244080074034170981e0300405a40d0706000f00d0a0003980e50128000a0f11140d0361a0301d486820f407818421150150303420111070349160080c00c480003c03482c2e2044440d40c40140d0103c0040c0758a00c41c2c21982442101040018440c1403440c44408410001000861054544030210071800d00c0c000c08001c02c11a13000740150340300169901201c1181d014100240255060403e000805400185105c2c81800701d03411100c6981e6110030f081e045d5082171203a5409600300300840030305400d059400040c8000302030304503400c0001642e6001c08455406014122102c0240e0309083d050400d40201850000710442604c0f2001c403c0d000141c0009002d009107039031090144c411010402e01a0a241c9000d41088100740c9035a980d00500215040803800111800c0342e6035203241d00c0c12052403e480090180000450400341030a260340c401001c00b0713000740d508184541c50302c0c0000300024014501144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 936809397 1250 936808147 936808163
    0x120c03120406080c0c0a020d031407080a02010e0106150e0a1e0f120308130224030702010c180b03041506080307110105030717060f0613080c1504091116 67
    0x4a4400002c3c455000035141510b100c2c41040310701080000099000c0e55075404845c0340409600e146402c1d142c5140814010b440c0b207a0102c1c0030400d106100010302a00c1e20150028460855901d40c2d9070300701c80384ca0154019803000c1041c000300340392282842440d10f000c0a040e40c601070b40c607405084c004426110045041ca04014030900c00c5803075050740c0c0702c010310442c0c800f64210700181e98041c0c07010714003c0820074003c50080a01d415540c5940c0b10035116200074507810304e414018612511746a2045030500090360801c402580d41d60b104415018803400150030503024036050a101135010390014105a800c2c1c400c007201e0719405440ca200300001030030740710000c651f20096441e00d08004d1892140709814072105000f002011904080c40305468049541c10002c02da075030100203032107a006225042e81100000c500c04584603520020f02050394800f008441c1d031144010200644084050050541c2000c10b0204020640c0741c0d0300181c0c01010501500f40c00c02c4140d07040100c40908581064450003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 936810647 1250 936809397 936809399
    0x30f0603070e0906070f090e07121d0c0907090f0f09110408060712020c01060b180402030c0d09060b060316080906010501020a140c040513030e030102090f120c031204 73
    0x315042004100074418070b55607003074503d89a024591200d000908a0052140c080c0340500d215200303141a50103480c00700d0360a50b0714103002c0402002030000030300c500d01452400380e82c0380c019000303c00171610843d01017004180a04a038402d200700d0000107800388050207801100440e001041c010030b0000742c80740c1010049c0152034140450103607242d0807910402e00300100001d0000c1e02000c40c44980c081c685e418040d0821a00f0700700e03d8000e225280407c91203500c1c0813004546901d8120040088000700003400c8680c4003103104200480c4400c0c0c4e60501e41e4142003150741c8200a5079085582072070b00130480050007600c0400842c00ca0f0740101c50f04080144a80085070823180c20001040d004800100208415814040082d548444035100641302d203e60441e1400050030810105030522006081400282000f00c0c403400c040d0304008040300490b170302400800741810144240e40c002440184081481043d000501000e80e40901d41481c00e0700414050401c1502e04008012210000004140d0380e5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 936811897 1250 936810647 936810649
    0x90f010b04020301120b0414011a04141608090f2b02070305100f0605060f09100203070f020909101119180e060d0501090305040906140904170c03030f06 67
    0x1141159000d522580c0305000500a424240301d0f812002a03102504c502030f40c91700e08203c0f51001c10101e4010166081a0001c550841d844640f40000300096600b80f005d4566800e42d021510320460310001c40c80782c03000003480c070240305200040d0030689210559004042c8140c0071030800021317a2907403044c1d58084440c21141d20f03240d100b84081316058070190030410304544d42d6540b11070301d0800106090742c650150404440081c1e01c004010413006210307656491034444205020f42040e801140305110801c48000c0b0280044203c071069a80504590060700040e400c0041c451405003d4003240e03c00c0258040032010144502d070501c1c9440400310f40c603901007503101e030807000c103210440e41040030408500c007410300e801860000f0b41d10b181c0400c42c1660794020104000740c401880282456007000040010b01d42c11000a100f940c429500c2400400c1c1c030349001c01d4000d0b40b40c41150790030510050009000c030715400800104c1074882c0c0d42251404041e00a10752468009960042e445e034401c00c240a51 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 936813147 1250 936811897 936811901
    0x903080a021b0402090a05090603010b04150f170307080d0b210d0906050f0702011103031e0c09010c26180906010c050d08090c04020301090c030507050903210c06090f01 74
    0x2650300102c2d411341c5002c48090208810000b28410785000d90b00c410b002c264107075800c1d000b0030301392440a4010405031030200b004915400d42446942c402002010000c1490307109162500003040780400150300c3d00d0041c0c1e80b90035490b80840d00d01e05049507a00d00003009992850b08400d8150300342100145681d544c2038405003880da403c140c2806020300c00e079003000030725004425030f000162541190384d260050b41c001601c044015002000c00c501000080040580c200c1840c030a501e9007801c0d10182d00c0c0d4460006074802d10400c00f00c87d0200d0020707600280020346042c0795110303100b030b989407130103030f0400590302c10007a5040b0b1300880c0401d0083c88850380140c00c160800c5603200d075091034865400350090b00e0301604d50625030030802c00c1001c0e13800003498040082112940380100684115a6580d58404260040844680400020303042c032000c1841e580c855000d44034100380040c040c0542542e800d10f0200ca89040b80b032901c0140300b003070240b40e031610003d125003407094003518050306040403510100c600b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 936814397 1250 936813147 936813193
    0x17040f0b15041a01020c010c0f0b010305030a08070f0e1002390604050d0210090b0723070521010f0c0e010807141e070203010905011a010206010e06100903080a02 71
    0x44075543c8040e00e10751a80c0d0000381c1010200017820710880c5441c43d400c0802002e04ca810024004841c0d40b0f000200300f1000000403c081940c9a5402c5020f0312005001c0312145844040403001a10480511a29240030b080b52032002d42280100e9000e19181c500c654203040302c052914031715001e940f886d80e0304408006880900103004580c04c81c646818000002c0c4500d036100c50180c01007802035003504507103000c5c14145000d40110414507407200030b00e1a207180a144210001744d501c50400c201c1643c2400009000800d40313200078440e10070a05045000300e2079580c9a01c81c1c0c1819926103070800d925151522510900703114580d80c40d4030895030304002428480c409848001002408186070300e00842205c1036030103044503241845400d40e4600c2e0300b00c9182c041ca0001a505520b0508501c0411905521800f41d250344030680700807540041d0010381e202c0700240b0601c5441c440d090009078052610803440402c0000504007409210307101e460392122500f007031181d01c4c05623001d03103181103040b440031217018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 936815647 1250 936814397 936814421
    0x503030714161103030c010203100302180402090c0901090b0f0c01060e01030302070e0606220e0a1e0b1c080a031805030a140d0e01020403120c0317040f0b1504 70
    0x9450402400e401034007124000c200903040004000f2109a0755030140221940840340c00020340d12401c1901440084082e1407204a101f0580103400403e011011248103101d42d4004141d0800c0d59a0700c1540c124517407002e2207042c1000110701c00840c0c0448c404010b854413442d02c500349600d41150350200b60840750319402545842955a00400009078000303020b2095401c5040d240003d0b0300c4450200f0304500510200718001003c54038600d20900520058500f150424032a050558031085515000c85003d20b01c100009801558403c0100846421011704c2280240403503184072040c02d12205d0b4141841411108a8000600c003000785031b040c0152140560817206e0302d03200c052156142d680e02c3c440c4038081402d2048600d001c88000440070166203000e00041018010603e4250300c250003503016000c21986184003400a04000c1e201e03a014230321659145d01d80c1000700d0341c2003100d4804c0c0c200c01842225080002e51500e00010103011005000e003280d08085000114a0020002a0b5032908402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 936816897 1250 936815647 936815687
    0x90a120606170d30090605010504060609051207030b0705130b03160f18060f02060c0c060f0a0b1801170a0803060d060e030a05030601090f080a0201030509100905030307 74
    0x9111020750102c0d250440c16941e0030400d0324404040051303c40030001800e1004041444021030600401582020050a12038441040f11707070380305d00400088440034040c000000c0c603030240600950404040b13540142403808100c51102d81c0e80e54407035002c507108480c18000100081a01306502c150345042c0c0000c0c00d10151182d04600e444204030607039000c1754403c0390400451103002d64909000c2d04030f4911090211400d010800e840d51400f0300005010000240148100b100094004a45505480c005000070014250b6602d03004480184414050f2042d000c0541d11203482200d40d0710120846950344602c032110070190300d800c10040700310070700d808240c1d0b07960046005a0001200107040700c0e13012030f08443d0740850301c0c003a0504100400d401008224503120004000007002d0b001b901562040c3c0d801d80e0381040054840f1000c1d14a050103200303881e80380d406040584015130080e0043ca0f407003120101159100e29042482030305a50002c00180c4040e0000010710020350780c8101444d908c4908100e034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 936818147 1250 936816897 936816929
    0x111b031e0408061302132a0503150f10111006080c100f0906081503030c1c14030a09020d240b0102011406150403050d11160821090a120606 61
    0x81100640f1900705c20032016692200940449100305800510041814000e4131b105003d840c090000d0340103980840c41c2080940c007201e00c1d070bc3d00d0620f445842e42c01414400e55650b02a805030345010050006c1c500038010f103181340202c201e252045000514060000b0b04080c000300003403000d0722240c0b400090070041190b0205138000d801903001022140145005142581e5104507a1140800314425944c540400180200c5120001802e04034000000034951008043e0f940142ca41c0115041d090310040014400200062242d5202c8a40940050049021702c0300998440100c44001341028201001c10308a244126525101d1510031002c20b00003080781e81045552000c1403400104081e1083c800d0740305024074500e404040d2001194000b049030042c603100342020380310384042287c06800388940160f10100c116250080f030125855400907101c0c4490070140c10b2004d10100d440d80c2442c210030045041035841d1810074000529910b02043e100d4011403805606803900c607400b0181004403e01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 936819397 1250 936818147 936818149
    0x16030905040f0527030d0f0501080606060304033906020304061a2103071209060e0d030e011815020a03080a020f030f0a0b0d080706050703111b031e0408061302 70
    0x84a0381002540c0e139814050192074228990301c200d81c001244d16003004080d503000d1900780c0040c0d05840304c0328191000ca556880511000307000840e00580041c100d1541c0781034800d24072803030110f10840307003c091510880c2c110024400311410b200032100c20350700104100502a1901c6000c0c115801c0003090303280b10680c84005100c114802c0c15030041a101c650b122082c40c0e0041088581e5144e11480c200c0b4055030b0841c0c040c00d041c41a01c40c8401142401840c0c202c0c03031426450403030f0031680c992641441003803903000451f03d0104041c100d03040d050704000d01046240110801d4001088680c0c028509014686802800c922000c0c210212a90042c0f02e0603c1d50036484040d60740c054060161040f4135a1910300c094090013001a089800580c000032102c18000d0002c002c00003940501001d1108c1d842d0100b0480803140300c105040c403480c109000c14100c003c080c403441ca9000900384100d03401d0800c0d0b1480840f16a04141040d800d01000040400503020103101144e8408000040b400c0700c04042d030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 936820647 1250 936819397 936819421
    0x210903050f090607021201090210020d1d010507022110020408030702040b0d06090c2102030c0108070504030b10090605030f0a030302031015110118030c1716030905040f05 75
    0xd10000350303040c08500042c80ea11081c041d078079480e400400c2e8a4503805002e80d010300038030308080d0907030143c1c1055807065482400000c6100f0038003100c1da03c6006224110300003903902d4148140c2d960412808111800250781c5210003001c110003a0301044051a2108240e1031401a0004c04082814010f01003040070600220940b4110340c2c040c1d9012036036280140000d16030000f04030000f000b05207804e04004c14041c0310000d03542034520382c0c95003500211841d1000d0200c5030308114002d5056101290401d5294030030041b40b83c0005850134503d00306a1640c1d6004081d42080ba41c5008800c4240d000b0403483c412070042000503c4113a0240062801034805540c81d8200c0000186c02e05030008046100e0b44609252807000b4110010618180c2c01c2028004041c1207503902681c01c29820144c00003440030400b040c440446034141c449410907441c9503150380070800b01030001602814280108585411401c565410080c0700e40e4441d103400c1d080500704400c45000b640c080404038a03110400186d20004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 936821897 1250 936820647 936820657
    0xc020d0e1005031801020403080d060e060a140d0203190f0506011203020601090509160b0d0e010b010f110f0a1401050a06230424031a310b0721090305 66
    0x204c9a04000540580c11a0191146910044c282e01d000a840070b0640100c1d40300038140c0d4050303d00248942c807024100000011075008620b410768030400486401d1810612030300c3d4040c030103001d9030860010301e02c00f8903d003140400c05441201901c500e803010464180503840c0540f050509901d0141d1a80c5c43c0299075500500410009540d91070100c0c41c83da07010016140c3c5001c007809015001600d90802c540c1907040b8041c4868501c3c01e00051407040310040c010958007500603560300d080340c0c54694049440020f2250920000e000320148190070700700500505084900500320800781e0f6860301d022b42d0031a0340c02000c0d40c07d500d1402c0024000102d0381c0d100114802080d05040030700045c0784c400100105804400031070390200c18000290580d010b0100c2c14110b0b03004510003031460b00d9400344c410078188200c5411280c400d5540000c1c001d0a040d0f0f103100d05060140c1903864078190326641c4e41c010600140d070894049140b91080342d00d150030f5920301c8003000d00280b03010701556015540c040d01d00d00070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 936823147 1250 936821897 936821911
    0x40e0d0c03230903010b150f07110d0f14030c0d050705010e1606020c0d0804050d0c08030a030203192003070e030703060c140403031710090c020d0e100503 68
    0xd0290004249442505001c640580700b0900c0010903810304141d525540c0702d041c1c0140a5400c20011080a241c403003001003105042c10341103403824014501e60107081d40321759821039000d24114600342a41d20b59680041140384600c3c1d100a9011150500d140700755008402d48030581c0c01000807105100000c2140e0240701d10f6401c00c1a12421945089405007403100d1600d2003a1044079140c9e10b84e61400b075810022103000f40c00361070b40340000300140004020b90020251440b541040108103e0401010b4540d4082c05402c101ca54241c544540d24110307840760340301c000001d4000c0140701c031f80041c108001300718298425081005035201c01c0c00c1c10050340d906001803075030752004c00004c0350306002d000d1000d0344000007010b40f803055441e4a0040c00074410903c040c0c00040b01c001d4086402c15030303076040781d040c1ca415441d032510034021f0340641810040c0040c290b1007120709950000440081c02c4c0101c0c3c8070103810350045c2000542c7c15400030040e0b1032810106c3e00c50b02120601d440065002002c407904500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 936824397 1250 936823147 936823157
    0x3100b07120f0c0b070e09070323040203070b0c1b09070804060b010509122b2a0f0311010b04060b07020103021e220f0612090c17070e0105040e0d 64
    0x22030307000035501603c00c107001501c050416010890030340d83c0f04441c411080700c100c44103685034807400c8044003102d80c808501656000c0710f42c8181d110716961840751754401e05c000c04903030740070f500d074250254540c01200e607110b2103a0048104030320403040340400c0006900140e034050140c0c50280e00082040c08040d101419940c1e48855011150b4403c0f400c1b103944000c040c107074154401006080342e5580c0214080103248000c904010403c4500f09244240300ca0499502d00c20b00010002a01c4001c00e44416401e0f02c11514003403c800090400020359a6540607440b84c4600888420100b13095074403203a00140304074070744401401801040d00c180c6441c1c035021318005858503034810400444001001420104e2040071032088584183c00040c0600320b212040b00c60301e40e903520390b60243c40010900030b150200d21004032000a80329a5408130500d1401140a0803c0325a282050046070307140b4082543d03950441390050106d04441d080d8070f80100401d46003000314182c08085591120860103031001048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 936825647 1250 936824397 936824417
    0x1516050a0c0f23030405150702030c011103072001110f060c0c0a0b0103080712030902090c0703030f0501150216050d290a020a0e0d26160803100b0712 66
    0x114040e40c0b80500d011010f090b0840c1d0b481619a654a4126108940c400c400d003501108500450b9401d640081e54050000c0c0602e0700b001c1c0042d80c3c4442075904010301403205100178000304016070349000503e008000c000000e000340900040c651100410001c0140d03000080d00340c0d0516000402c01d030301c0700311504020344412500c607210307013842203a40c03005d440464610300110500c0707041c0b070080001d144595a518144c00c2c42c00015010740340d0039003020f58012500fa002070150070983d4000c01b10700740304e8900014100c03814100c140c100d400030b030072601c680d007000081038480300d03010013603d02c00414500d49082e07581d14020001e1072221078500000c00c000300390562654800786410840e254503801a5214083c1c1c03900c4580c1800a401c01c1340070703d000604118101c000303030401004030024a038100200103149c168003a008040c5c01c51441e01400e5120040144040b500000241a1090fa02c521100ca9480c2000b40044d010045550051301c2c0c00381003007207200000340c0c40e890503880310f02c11820800030f00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 936826897 1250 936825647 936825653
    0x1302310b01020c120c0a1d16030b1801180e0a060c030b0306130209151c29180d050d050402041e0203090f190303050c0c1516050a0c0f 59
    0x140f905102d802c100c1c214004540d01102042e00c215405090342e6140307043e960b03142c00031341d421081d007403095481054101054024210207406084095a800d0210f01814004046100421b403a081305082a0301000140700000c00b03990600b00800c0c03000400e0180c00b00508040d5124034218400408940d501e02984058070b000360002494500001d0031f0301c0e0640741030319024051396088030040388070390041c10024941c141c52840e4010b1404010f000321a2100344850120b801c03a0340c000040d41d4110007246001050064005040c4168415400030b0b4070034144000001c1c1d480c0103041c10310360345030080c00c14140034541c04000d070380c10888086c0000c1425200c7e80007040043c00070703030200ca208106503100d0304151502500118000e444450444415803c02d51510703848040c00704141e5120400740c0048000b007482a082250080c403190320303a40c40c1001c00d0490b03620b05421900c0c02c521612480e000c0080b4800300040c5080004000e0810b54a03000c14140014402144014010420541803880c40d081c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 936828147 1250 936826897 936826903
    0x2010b0103023109060b191409041a060c0307050708010b091f09151d0402090a0917130e1506033105060a0c09030c060507020102151302310b0102 64
    0x70882000100200e91b15410242d000d94085414150820703c04c043c201006880b41035880c1414098402c914140742841003040050a10781d003038850b10b6151511000b00d15500d010040c20b044801d0b000450380c0e80035600e82076003000266030200005914110302c400564a0703030b4003a140d01030f0140c2c4d00740c0c0c5405106605850b049456411203070b207140c6443e12286811041944400542c0c8005204094101400003410344414003220002d4018a4820210b03075200011f1304402e1101d40705011200305132a40c0b10080560b6040085904d075038410400003080406040064a42c102c00709a10820b540010100440c110b0301c80a030240700b41d00c002d01e44000450a400b0b01c4410109840c00030581140c01c03e0901503990320781540c010b04500c0ca450b48442c20a4081d401080032298001e15510b00c5600e8010151800e810810060f1305500581c100c01c4204442ca1041030302c502000803880b03000e10310768014422072403104c1d43c0f6080e20240d0304031902610000440084000e000100e40440c21142d8580100c1c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 936829397 1250 936828147 936828149
    0x71106070f08040612050907051e060f09040c110307030509040617010504051606020c040b01020111041205010f09050a0f110a03050303160306050607030f0903020607050d02010b01030231 82
    0x8070070000d2004020402c09080001d00441d42240d451042c4044501244011100c081e2000003050f0f110700020002801c3c449400c0e2205a01008440b50044070300d40801c0c5107a10a481009442e4000140301507185002d00c0f8500e200761045c03611048204810508556910034194040e050000c0030034401590760707541e0031800142c1010030841540300e0303070208998042c160590301100e02d401404c40d40b1800d15000c00c4240e040701c2007580200f820711601c6007030100501d00c0100c21811952038802c81940e65000c100104001c04040c80940c009d0310303003402c00c0c80c01c5403210420386003035500b842c00c15008180d0020380b807007611b0b4001c00b070021004400e19240982d5040116415080f40044400206015004c03024600c62189262400c41962014000314200c40c4580074081e40303e04144018404640326411354500d8544908025000c65242d40000f000c1da0803001046503641d110300010342a46a081c0240035113100282400d60912014440031062840a00e40c8400c00b02013000d1001c43c48418040074034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 936830647 1250 936829397 936829403
    0xa050c07051201020705010608010b01020d0309080f130f06020d1e120516091a040b03070e03120307020d09140d020d02090f010f080d050405060315120d1205010b07110607 75
    0x48903080322011583c00303034102c164159565440d08000098200d01802200e170700550581c0a07000045020030103030014180c844007900ca8080911658091030410002000701ca0301140340303000d0f050302d081e900f140320110f42e402031811900088900260303030750011200108a801030f40340180c0400040c60484480c603004591507111420300083c0f0080403156840ba040b90030241ea1620882511000c44000111014201445403003003000104110f01d400f0000d0368106000385001c10144402a0010f86080d000c03840d9400441400030500050310340402a011501d0840d04201004900e0052001e8201c03001924950140c0e0074000c0c1401155103d000e00b800b00d903802802d8070268105105c5442d407910003405412040c961840d0007092440001503205204d0140d559050b10385810041030001c250400380c159400c0c460800c81010095650080e84507000b0403940050404c0e441d0b005c00140821b11003c0bc80c10042c2c039040050082000d940704481103503822600010712800c0b10030200342d0903c90400c0107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 936831897 1250 936830647 936830659
    0x11040f060611010c030204120f020a0315270c0b39010b010c0b041b0308120a050601090503060604091109130b06060c061803040b0c10200a050c0705 65
    0x800d50700d030880c5241400000600007001640c8040740d080d0224882c0340240301c8c2000c1401903100000d190101180360081c8050316038001c3c195030b5660843c1030b0409071650301089031128241c2103205400c0c04458402100d00c01007000b0318000d6280d4041070300303050240e6030f000c04000600042080c4e0442228403905034000c2e43d01000e41d420381c1010990040152822047d50820b8003501c1150300c00c4c4070010300280c0041d403c00d0b0750b03143e560360000407040c0582210319500803164000041810107010317002801c6000e0481c80720703283c0303030152404030307800144504c0c1408000c19080c0816100010150342c01130b81a034000a2440d083e041c0f0007441d000c1e0304141e941c4441501b0821a6111900c010004914800c2c10b44e4110382d1541e0003048014000d0440240069100b074000560302c0f0740c40c2e8550b0495030641d03020f89103440e8440503030040c503038803a12090600740d03c035041208100c0d00602c00c81c40300459080c02c800c8031400340ca40fa130150340300c1c14803000100500440c00041d0100305010060040500600c1d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 936833147 1250 936831897 936831899
    0x806191505070c0602030301030c15020c041806051602150a020403060c090e0a060308090105210930040b030709080105040614060d050304180204050d03020708070f0503060411040f06 80
    0x1041d81c2d0001c08212101c0300b0200c8000740036400042075a050fa40d0144500d41c0080c00e21203118217060300301401c0c3c01144a5031407483c0c0a52614414844d20360889100e40c4100b010720f040c0403081d10005418a45d002c001070724001c9203203902282e520502d000580c104803060303c0301d4041030040e0141c1e4001038a140c0c86c0c07401040d2516001310b5101f04a64002e141c0480541c2c402129804603200d520000c0c01500080058880540c4204000d00d911180804805413402502030952035848040f102c08046a000704030301d0401c100242c1e28820745108034000d240807012003440140c0507000d18800d001300c01d1401b00210f4502802024200061300154000700070b1807a150070709d60b003c3c080c04112040900028008140720b410980c0040401c03d400400451074146001c180c5c05000c1140b0040300011642803002160580c0d50400010701d6500030380c003c0c040c50b1304240c016403c000d11544040920000028100300c0c5071404920941d000703420100e0855100741560104021300803200900602500e4920 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 936834397 1250 936833147 936833189
    0x130b070f091e0e070903050c04020d02071b091a0303161a0906070e060a09060e060913060302030d05180f060d05100f05030304030f020909010e0709050703051006080619 74
    0x1101c0c0b00315118141500070944540c80161100b05171400054015008a0356824050800c0e070010301d42d04104600c0145040040e8480f01d41500c01407054003400070804008000401d1240031b09a1081070881c10b22940c40b1b0400d001995901c24460700308400c0d0869001d55090000240301c41040a00f220f10192140c54402c4101c0d480303400c12036040001c07401d12b80062100b030402e0404e6070640d051a4884850650a240003070700c40d4100581003650007a0300704000d04198840b080c1d0729240f000742503008103902c0d08500c101802c00c2404d0810604004080c07090500d8190841e4060710b0b2001d082d035145c0300c2c500c02180030424034803420303800f62080340c144004d006c10480e0f221410300445084003280d01d512925007082580724800c40c88043d100300740b00107070f0308094070f041140e0315042405200006841040881800d080500b42c1e441038000c0c030b50320030070000e019815024030b6030b220006001d821541e9003000c070003412910340500070302e00498884c50280c0140003c00d11841c088c159048101d000e01a01c60 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 936835647 1250 936834397 936834449
    0x70602040501170730020f1c02120f1f060815011806030f090506040f0308150d03110c0312040501030f05060d0f0510060b040e130b070f09 61
    0x4030510380003468280851281c1800c2c4600e40e400381400c1e98805c00d2250070704081c5a080b4030780b2043c45403010012031003101041e480348002c2c103407282911400c07511012010002c00101d00301e040040c04040c0104107a9441760b0300005103a9011590030032504a81d10790305484400030a001e2601c1110000c00c001c0412030700d4000c03541c07510482000d061240c1e800445401114200b100c100080790000d818407013030001c0380c041d1700800b540070741e00307440081c0c1c0110b1622490720b082400d0380c0655600c2030f81901c1500341035101d001164001c1051555010346825000815038244040d40041c08004e02142d29282410303050001d1919094000c08545040035049a410340e113a101d80b1070b490220b0303c2c10100c0d12141040f405040d1040000818030105144a521031076202000008212154000c5070b04602a5000500c242009809506005500c660a0ac04c000d81004000392030840707003107503401240c0001103144600d10f40c40b80c860715100804030311440301920000307856044031a880705811070782c240e403140300c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 936836897 1250 936835647 936835649
    0x6012601140f0a1803050d0b030a12080603071508010b03190f0204090e0a020d02091314011a0f030c2202070f030e1002150c04090509010e07090c05030a0c1407060204 73
    0x1e0b4004116821480c107802071061300070314004011078030510a8810105c0f0356884808411806010707110328101c00c3e03031100b1130a41400c15901c00310301100107002d01400c2c1000000058a03200e0350f4240e40542180d0701030a0b040c070500c21141c0c403030400000543d02c00c40d2a00c1e0750107580b40100090056031501100c18020350024014001003520f4111701c0250340c0b10010340c207e071058018141e110b05065940a03c41c00c464010146154080d0140c0004005400942c600324800252000050141001200031103480420034a085c0705003110007105903c2c0c0c0e03022403031200c0718030f04444e18000c0d0080c1d4644000007000d000000c0802c039101044130024404030202140800740b10750b840f04aa01810010042d0156140b0516030050344001c4085000c14414840c1940150300302c0100e90401d82d8601d48981030b1202220060391760b0351100b0600c2005042080000302400070404184040016450000c000e804000d140c1403245880744c00b40b02038280202074020940031041d0106030f41d4030705030800c2d502035801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 936838147 1250 936836897 936836911
    0x61404030e0411160305070209071805010816030903090515041403060705070b040c050901060e010914010c02010e0414012304061d0a06080316031106012601140f 71
    0x100584020706281510660607610074802c0c80c00d00303040d4080210104405000021014004100482c40241eaa2405801d1207032540c0d40d00d01c542200030000c05141c002d03141e4001814412400c00b40181044014060030b5116840d20f00058400c0041c18201da00d0000f5a11080d040880701c407142040c95819030003442942d1000072480d40d214003070014540e0341c020484218000960600c2120006660038462542103030159810710000c50303c444c005042450207030300400c00329401c07040d000c4580d42c000080300010074400f0101d0740401c418a001800c035402e0f800c002410810300142c0e030032023903550364054065410003103006043c0e90f03100c2044d580c0482c24640440301c1c44488007034a44682c6040d01480081d03079900780602c280340140b00d000f81200c140c00f420b000d07002601c8800104440b6070401c0609445208020842c41d00f07001820003404a00c0740c002c810310700e50800401400f098005510414040c5940d41380380404a00c10241d20340103100581d55a000307070580300c05000343c28281d1100c1ea0301900d6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 936839397 1250 936838147 936838157
    0x21f1206060905040b06070302070308031801020d02030a05131e020301060b0406031e0c0903080304141f0e0705060f1b0303010305070306110a080a020906041d01032a180906140403 79
    0xe054000c06c20030307001c0c512009005038454002440081c259101030354120002000c07003140d0aa080d44810301360b8000040780c1140550100811410003054001c20360000d2182c1e03400c00b1454255215000c5061845002a4090302c0350b4481c44d00b10345096101070300400c500c0000613210707511080028003070085045840c240d450803050074055600c1c1841490101015500c455200c2403440e6501600d0340c2001300195a860302412036011079047c203018424544040059100d00444100e00e0350342110821880805203a00014060105888642c200c410908200040d075448490403000703d104114180701d0044d50b4003011000108102d0001108400d5030700c40c0c842844107a410340c0000c07006010720703540c40300020f0b48400441c03003240c4150700502c04402d015141924198540304c44a250007101d07290400c449046a00401c00d10640d01007070050158001d50412080190f480001c0241c260b43c050744081c0c42c0405881c144500f034550102000590100050025404c1f100c07051b1070f05c000450702130b03004c50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 936840647 1250 936839397 936839411
    0xf06080705031b0108060112051009061a070611040305071d07030c0e010e060c1e0c0a03081c0603170a1d01090b0904060e0906160c021f120606090504 66
    0x2c0b6012454500080300c2d890041802d010307940046a2030003001d00007505100e80d40f08680703d19aa03602071144110030700302002010a20f08004482111100d070301000c541104c000700d0414200c0580100c40b501c0350055400f007a800c000701b000c0300ba0b9103d0303030f0300c0105070344a910000180c0382407003207056110008011030200c0d00c2d518031200f0f405451381c04040d0030004403152403000ba15030013814100340c050b201a050508008000c50b2051800300300381c01c801c02c1e10b1510000c0380148101000f50b0070b0f04240540e00002000c0c42d681c0c610040f40a11210b103410850052507020090309503503c084001c40c3c000b200908903030345201d00c144050380400308000000f41c0f00c00100280342e01116501c00805010b03540e641080740b41070050b1000340c01c098909548961180c0707002980c0e50000b803a00c4c1c01610729401911050070101e500c03400d4482146c1114091001d181c0d400c1c80941c0d04c103011480103022074582c0310000100c0c20411030761441854070001415180c504041a2143d101c01c0304415100c069408100c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 936841897 1250 936840647 936840649
    0x1021e2d01330608040206070c18021815031306020903060a1a040e031603021504030504060f1704150b030d020c0102070509060a062111092b02090c0d0f06080705 71
    0x800100c3c0103580200d841e0a010800600f041d90003842d84500460300050116100c0032002d4005041804008840342c02180345031106100303440d202c044003412112030204d0405021040103c2c040207003200c28403080c140548061250640484400d80e1008040d00e0301c80c03601c281100c3c010200600c030120300d05641c1e409202e2a0410348142009903001e02d0040d400c0600040354104170115070401201180100c0f0740c00364140c1000104c480c0100c1c4203844140d156820480e00911020a6000c8007042140c105016500b2802c04d56400340c0164000b0b01820401d11505008009040282c440c1e5805200c0c03c080080745c81d034041055a10000c00341c5c00e40702000da58408000c031480e0140c4946602409031442088401e0084c0b80100020509010203210540070030103040c21142403900c28072028038000750742c000310314008035503c1c0d605060007544400031219006042002d5001d000c0240200811004143d202940900351000c0000050080c03000340c0050824a01400041c03203000c0d224400c0503004203031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 936843147 1250 936841897 936841991
    0x161e030503191b2d05070e04050d0906080a1d03031008100608250e04030c05010b06070f060c052710020f03031f09021801021e2d01 58
    0x83e25005841c1400c08071500d202c050158510660012034404c02c0e00c01000001c80900031400204201c0400110900d000d00304035040c8800503030040f08200e85080184038064004401c00d420503116000041c3c0b00180c01200d0040c0c110069400d402488003008004a0404179412103040d41d80060965011010080088041e5407882c0148865900805108410b20302500c4040c05809402c1a0001420381d0b9044003040520b800d5606500080c1c0510802e81800400d00466462500c180d9101c0e00c0c002c912345550f02003141c003880082800f07841c0d00340081c0ca544503e05556000034001010f01039010310259a4080500103000d10f8080c1401e00b80202c540c500118110280e4140c82c0040c40c91640c03214080c07006800d070004013030030220710300710013140180f103d00c0034029010542c00034074404103140c40003901d800c0c141210700710720704080c02c1c0149040f140487c420305c4004220300002e04501001c60100044103881c020b6150941ca01880717001e502004000c40b03000040000e00800034200134a080c168 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 936844397 1250 936843147 936843197
    0xe090f060105100815090f040b090d0c06050a0e07090f0e0c011403091216020f0a0b1b0705190501171b0d15030c060908161e03050319 59
    0x60b20110460f51103400c3d9000d010041d03800486080202e03840f008017400204c1c141d10903030b0034418090a010410040118850f41701350480401001000c0010f25010010004e80205000a01d00f6846102180785064590400380d411480070b03054400482d1120304104c010f26171410840c0981d402e100041c65403ea011407914030406060350361000500094003510240d42c0b02401c90700d0244601c42e4420300000290000c1d05900320181d26214845071140100b01c1c2c000a100c2106100c0c5058020800c0340340100c0b81101c1d51ba0342002c05211194106440050904d05158401038212001034030f401140b00c3c1a40800007903170700036280c1e01c0800c0c16601da00003000a0884000b0005c241980f0300600648041c40540045881d41401240050181407401c0b03070086a90700840d081010010f090000c5c90300241d525000c1c1c0704000c000d190003012000d5051100e0705070b10501c1d46040c00020015614030301403a81c4006141c100c2c048a80c0d895641c00c3e200c00f031000009441c4001900a00100d0741d203549400d440d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 936845647 1250 936844397 936844399
    0x3031b0c0d051309020f1315020a021c0b011511060c0a141b010e1e0a0b1305120408010f0605011e03150906140607031d0406030605010e090f060105 65
    0x405200d4207030005407003940c000c0d00c0710151698a10000142100c0a0008003843c80342c0720f000c2a1510407480c007905030411240c0040c1308580c0b401c50102d00f1945c0c009842501542c048504660305043c4007107440c0c1000c454a00a800c3d54043c900104001a8a001d021554400c643d10000600540c1d104951650401e6502d40000d40341084030081280c82900c01000d03440d001036003249441080150034440c100811612862a5101c482413040000140261010007844420b051004080c0c10b507159101e050f83c503002424141c581c0c0100304401c0100d4143e101980d40b10088651110001e0946507840c2c0051103504078960034070002c03580f6194203015000c110340d07041c0c48150140080c200810300e04c0d501d0b800780c402059035030404001034980f004039040040c240c00e04001544c6043c228070341030a12507800b8040c0144020000800000d920440034000300c00114004120b0868810002e4003030241640040c2c42181002e00204102d00f095103014011005a01107401340c8008101854481000340714203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 936846897 1250 936845647 936845653
    0x230f0105040608150903130602010903020601091e0e100905030310060c0807110111030a11070f030b0f2d060906030120090109210311070b0405040905160803031b0c 72
    0x600d134034400062502d42142a0f14182d90401d0005041c008004415030f000d000107070b440703131401c409054052080c54090003d81d0414815082501c8100103030010202040101a541d1082c0b00070200083c88034842d0400711240900c8004001c2c100155203400035581c4981d9a451004001069030148010311349960b40300f0606070810060361038a203070180005518a05005e44540603002030341c1c040c0010006101c850302c58002280d119021146400c5440d001140b03070348600031050010808541210b81d00914000c60903180f540d0340c041c01ca0300f40d01c11510080580c2034450354240e02d0031250304242e02c0b0307007415200a851941e4070010075090340c3e41c030b4000c4500d08030881d90703c0b020340342c100340200035203030041c10400301441d641d8400c1014015a80000a18208520500420140e00440040d880e50241e8002c0007a076042c8040070780b00e48281d104081c426555440b50808004081c0010492019003140509126a490302256125401254401ea07284075005e40c40840c845441f0944904810001c02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 936848147 1250 936846897 936846913
    0xd0e06161a070809121810050a18081203040512030411040c0503060901090e0a080c0c04052a13031406010602101802100203190e041109091504230f0105040608 70
    0x90b001503010301b0032124441c042c408203c0300c07a11038052403e040b0b09142d41d6070f65142c980b40c00c0203009070165076809540ca005a00100031011001a0448024140481051b5651150b01e0054603289408a8865507c20080304200c01d00999000300360200300151030900c07504c908007204442c0752000302c40e92584204008014031141400340d0203524104400c0040324411041503c5903140c680010030b078900d2a6100004003140c5092034002c0c0e941104c03000d0a01c55055041d4140c0f04907041004900150441d80840d103441c0199403403040900541e04408408045007a070340c00b242d01e0b800c090050304c016228603104003002c00b40a100e0f220301c407280320044140d42c408950821210090300d03208241148000e11409a0040c0442c51854500506840b450011103204041c002a00d000205921501c0000d002e001c480e500d130b2001c3c1c954004229120190609811000900100691800540c4410010b940f4264010340e014009019029000c0092066a80c640c1080f042c0e0307646005401d09a040540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 936849397 1250 936848147 936848173
    0xb0f0909010305300d0905010209030f0a020406060f080703020d150801090b010b0c100e010902091807050102070311040c121802010809070b0f07030908060c040510020d020d0e06161a070809 83
    0x321560405101f140003514002e01000000e01e0301d508080a08640d400440b2100210305e05441117500070016400c150183c2c4c42c56601c09080072000030920f2003032580000c9c401038a401c00c0e5100b60380c509030840c010918981c071445554000e08030148102c601007030314400451500030840540c1e4458245000070b001d4001c0c044e02d46e0f006400310242e401c2d0f0641d250a42440140e03200e1030398070f103d4610000c8420001d0711500080f031078007070703a076020906540020400703001081016112408004041d42c0114a90001250031982c0c04144846004c51501e040c041000c03620002e01e812516500076a41c03006c1ea5100c40e244681c843c6241c0c420a15001c904000100c16403070381c180500b40707681c000c1c248403000507501d024031404c00741d0840e1214014840020240003910b0a1306241c0c0c5180391a02c014040446400b00180da1000c0030f408074001d00c0491000406141d542908448564241000c107108540540c41c002c03110800d007081140003054ce042c0000c265030302c500d80a40c40303060301d0340c0100050703400740b1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 936850647 1250 936849397 936849401
    0x140103020c1905030703020d03150509070c12110708010b060406210f0b040c0e0915040204090e010203090d020604030c02010507020a05040923010b0a0b0f0909010305300d 75
    0x1001c452807401003103280c920b4001914003015416000d440a9039032208180340080c140516080c0c1c4000349440d02c481d80105060300a1120b003511b10030fa4051505031943c003015a205404094000c00c541542800514803650001121507040011021a1a51526116158240e0b2004030980c1d404c074005110801c8814407591004241c910410361115920807030b08002001d4540c0245001a02c80c2c90303044041c010300b024494410384c0c00f0346140c800380003003c0000142c40b400c2c0180484006541141c0c0031601c50361543e04450003041c0b40b050812080d58181c600314043d410403144280d00d4020203100801d40741c00400c005105a9040d40d900c9640c96480d0300540303090b00110030a9800400041000c0341d81d803907520030100c4c1140039444a80518110f000072241a2000341e2800066034104070300e040d89900d8244441d8142c402214246484120701400d440790b50040271f1401c1d41c0030007c0e100000900c130000c561309032020030010204942c0c241c0c41032803000018100f100060200c030b0411005102c49003d0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 936851897 1250 936850647 936850657
    0x60b0a1205070e030703050c010e0f030a03080402030f2b030509300313061b0c020f040f0606050d06150837022101082a09070302210114010302 63
    0x1d4240300283c82c0259001c24501400750300222016030000714002203641c0c000d40e40b02e450060444031107964204840229489450703030080101880944400300d030031980e05211403148032815000300c40200449000642901961482c8117140488281403d0300c0315200b8001c985c450300c0c100000b41801e04a400b004a000300c0d40118603020721482c48481900044890001c50052010000300640c14030642015412240348070030250601c15601780c132285140d008070104005e2a011a0358990050180000c40d0243c00d80c0581e07400c0c0c0d40e2801d180840c260340c21001421000d141d0610070000c05c0d480b400d03c40340f0920800501c03004140500f000034030320f15000c1110011070b400301080c00403013203080d10031501c0d82103440c40c0c072040507401048890b40280881c10b103504940c9410041c2e105540741508c0a074644800002e550203060144a5030181c60a00c0c10b1421215031024218005030314180c0d000800070b4001c0505840351021580324403a030714010078142d42c140d5109000204035901d120b00190025404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 936853147 1250 936851897 936851911
    0x240901090b21220b01180b0a090c350709030b3903061309080315031e150901090210080a0608010e1507050f120606091210060b0a1205 59
    0x10b070307501040454411402111140c410b5900c42003d5041c0510316180107250301d240c0344840d16001030140265948071001003100c0440f2700001e65890701d05012540e506c00c020180e07011140c1918840140740440190180d5a414032261210a40b91814121580703052440007901b103148100c0420050b400007020071000180080e1641605440f510319000c400441d549a014181008410001d140c01c00704603515040d03203284000c12140005a948421764000501800001d49110800410030b488c1001055520050300342d1444000c01c8800c8120355440303039030042140c140c00020100c0d5503d00140500340115600806c01481048100011244044010200140300e42c83c4c0000042d0400d0030b10420b840001804040d18800c0e00001307a44981e0340018141038108002004100405500301069400d030451751080700c4096214000003c0c028000c805c0750310ba00080c90880b41101000004050712114202071040c0300042d910940242580103030302e03017000132440d090685011410203521260b0301c840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 936854397 1250 936853147 936853171
    0x200a110111010903030b0102060a0603050312060307030807240c020d03111e070209090d0c0f020a031509020f1e01180b03011e0e150f240901090b21 65
    0x2807110311450a41d810941c3c00d40201c0c0c0c1c1c4800002807940d040c004150b003c044d201080c0466451552072079901c0c4610340c0c40c081c9a9041002013269039405010060040d5045440980c0300e400c00d0170204118121100130821500c032007a200c40481015015002007640d45401030001c070090300609034041c10741381800001c0f040c1c080051001c5208407024001d500941000c050b40c0360260f41c41403041c0100c001d0070b014615801591343d001c0d4250301540c0d490855030f00c109800c205105520214048601e9604001c21f0f28911244000038803005078004070101c3d0084541c2c0e070021704100c0c24003905c001c503490200484901e490340103690354012100710203404500019060840d607641145d00752508282c210441400840040300454251441450064880d0002e0441070f4144403030f820204040c06110b00307003e6410854043d840d5a11040001010901c076001250b081c0d005d101d13205440e603c0403400c40c1c0032619003080410215100015a910031486000b0710300440d44504c04104d9070f080007495280c03174070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 936855647 1250 936854397 936854417
    0x70549030609180b0c121801090c061e030903021e0c0409080a0207090c0243050406141e030316030e0103060e13080c0708010e0d200a1101 61
    0x1607640c42080c580f0100646041080c003124501803c0c0403d000d080d200035000e0901000070440c03400d8240c143c0241403407844840a5900d40210f40c09400e00c22401303844481035800000350a0b400080f00404200b4450044100f14070340802541151180c46010303006900c04a440081d0312052202400206040d81c1103442c5c042e46c1c0c10008056078040ca00440c2c441c6004162045038640400c1030138080c00040005020b1401480c1c130095580c2c050b101c2d0303c1c02912001240c80480c40c1c5114081203001c40c2a4254405040ca006a000c1d01d00540d200d03071030055207001c10004607080c4142c0c1e02d0710603240040404050082000d00c80c5500ca40c00082180e26020400046106201c0d00032221071280c420740f00d01c0c801190960001d0125480e40d4880001c058900c0c2c104850007010441c0d0140c0245e02003102911200d6244440d8580401500445581c9d881d08022503d28080004c644a03648423b645182ca4400491044080c122140f10f10751500d078426030202c00050110200d0030340c0c158043c50011880 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 936856897 1250 936855647 936855659
    0x60c030711100f05100e0a05130618170406090b0a14031302040612031205073b01020d0c060b04020d0f0f0c1407060b060c030705490306 60
    0x11100c0c401c800200a5034803e011100c0c200c0c9800303044d51059001d00c41c920101d1030400d11590004008082407005542c0d80001101720a01e1410250390b103412035001c01c486041456111042c84480000f503548480d20904010f07050b54200c03c035410788609584400d403c0d07180c02e4195407290050307a0030106011025104034600d88654000c1c600c958059600c8485a090300d00502c01180e0740d03504500c0524004103049000700e5008400c200042020f240d0004065a81f20710032600d2040807a40250600500f80481100b0325080181d411503400c1840740d18081e800c5c80e070040ea514074030180300f003012541401903003011507103590065003801c2002e8405481d100c550400c4008a88200074521251540e854221001d02c0c410b1040301d24440640c1000c24011041c400070030042d0084200c020304103a207490b5504581d440f01815248034402c07107800c0360b480360000d15003d519541c0b1a03113041e03070450400c17208008440b90782c180c06006249224285021004600904100445404a150600d51603007800544 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 936858147 1250 936856897 936856903
    0x506010905060f07140a301d03070b0705010f0924021e0a230405060d0f020f0c0d02120712111b1005030c0301060305040302160617090f060c030711 65
    0x51341e40410144c020503540340787c2081d42c0201c107400e03401d404134044018038034400740b960010a025021300f090004a00110050f0300302c28040035075a601801590030001d01a0100e030702900042d841100244158102c0d9a844400c441c001e210140c00c00b20070409002031801100010440c04800c0000540750a81800c0c010403003500c400780d0081c075004001032501c0341650022038091400e1420810030080c2d28203400b05149401a406442e1282c9800035044003040b03d6035120104004264109540700c1c0c4103401c07a644a42c10505500017a030040f02e034031313025152002c81c404002d107940c050317580e04095031070f20391491040100462a06100f6520b002c10a01da00803c80140c440d0480c210000e084400802800a4000840d140c2000d120003442030084008112050f6030541d4050f06d00090b059840c0d090480c500300c203091440c5800f00040d40040f8070150310a00888807108080000141c98403038149441c1d48030003220074106c140c0c100c180031801b400344403c000c5812041d03d02c0d01d0140d050a07585543d01b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 936859397 1250 936858147 936858173
    0x3110f0d050a1d09180307020411120106050c0a032303100906090b01170601090302060d09061b050901030c050c1501080c03151b0f0309010506130506010905060f07 72
    0x200310003007007041030580d100184282c3c1440c0340b84443d207400314440104482440c064016090b042c026100e40e0000d21040054400b8140c00420038003070b2035094882146c1540c04511100103507200b810011072a90b0080045030480f009060013070007038507841c0c1c81c1114040c85a82020080340c4c1480841d10110780d904001d0b5002c0c844c0307080741c0381c40b0303a141120000844400e81e10204aa034100740f132452490382c00850030f0042c00d407010b810401c03d65441004980001c07090f00000d600103008141005003090583c400104c0c20b210340700c2004412010107807425400ca0f940142c200141040180801e1548a50406074004c5600d0034180d0921111240e03e0342800024121100700c8248003004210f4522708002c0807905c040c040d00503054440300c0c154035a1040600400c0c940505000c02004101c2c60b40003022180440c80003440c8036240e003802103c041c0a03000a0303503414400d6041d2698107042605c40d210b020b003e580142c5402c400f03640340405002c1180c00506000c8000c2205101e410f01080038200828 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 936860647 1250 936859397 936859423
    0x3010602030a0f08130803090f07030f051005040c05061e0d0e010b0d0228051903060b0a0522020c0601151215051e28050405090a03110f 60
    0x140c548184080c02441000300c1040078040100513001c0c04003c03814502d103000400c3c3c0000c05d0a82d03958507910076034070740f903150b0420000c64072540c0c0c1b00005000c0c443d00b003003210511803c00d030760364864030482613000d841c1e0540d40034140121200041007145840b00c01003140d01c00c0b5168000c0310751721070b4100f02600e0300f11500c8009034036269207c240c00d142081c4038031840703213408036041c3c0b00d0585d942e00480e1007655035003180384c0f00b0100340d03c0001c401640c0b8069031004103c007c01c0800c85042c031411130301c090386c00d03440111a550b0501d110f11425140c07801914068803005040e1401d241940700e429a14179100b03580c5181015800c0100030f01c9510107202242c00b03806103000c8c50450403200f00000749040c01e15241d01c812540391441840214410a00341800c1325412503000045103004080030024100100c070540e0b00060b40e0284411000b00c81c107a2417410000c3c00b40083d4100d03551010721084d42c0e01101c16400e55040b14805800003402200c88002d500305480445486521189986180800d007807200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 936861897 1250 936860647 936860653
    0x11416150515030303130b1b0c010606140304050a08250606030b1e0403080411090702011d070608220807050f16030b040201210612151e0b06040b03010602 68
    0x2200c0081d8500c0300003102d1005030f0095145140010480b160250314074001401c401c50640810341000e0300103031525540700107113030702603590002c413000034001c214521a000c0070a40d40c1900724403581c0071505407842070350400e0107400c0c048401e42d10260346078000c648105450703502005e10094007441e02c901c1c2589511400000517043c1c20340c00d00380499440204080441e01426024022116011211319041a410b01f00000e050f01c40d80b42032040031182c00e10032a004071100c000c002503940c1c15040003062809010700801500810744d0603503114516802040003159902c000320b542400b0721221107500c00741184203840304007103075910011658801e90050b60340c0e0348008844141d80c1c03824461401107103941c0c03459168941c5945d81d03040700e0f01c0c0c0040c4042d0500440d52135500b194043d0603804a02c40f480400100026500c4d8103c510318a0629101a90710702405072100304502d00742c1c860700804285641d0044880401600c110300030b00400b07851150040b40030712000520b103c81101940c0a40065009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 936863147 1250 936861897 936861901
    0xc0908071d0907050d12050d020a030b190b0a1107031e290123030610060219240207240f0b010905060a09080f0a020114090114161505 59
    0x140503442400740030b0030710b580c0042c2c10030031442e510090307110300e050361080000d9994015000191890b000d08107407a0400d40c00014942081c6c2d5040d032115104074400c4075003600c1c1c00a40042c4070f0130010703140039034007040c401000429040b034001d04c0282c210309003001c2100c507030b60380340d42d910483c01d092108005068800c003101d42040103105e050586100843c2c00703d01d401481e070842e01142c606018403c031141c000c0003040d038418880396a14141c608400c0501204d201b81001248450810450b114490050042864050400261444054889400205004481e602104071480c0c1007a1190310403e465800c200e40700010321601425101c03004c20350454000a40c8040d40034090301c1c660300140e00080e152040c0358080b0f0382c21090040940d102601c805465401821090b2211070540c2c0003101c15100303d510030701c1c1c60700c00040c0c40c40310240b00baa00d404061700f5500b0318070001c1c01541c01c0719010600b801803a0302d013006584094031400e0310140e506190034145454040200300c981da03403a42040e8944007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 936864397 1250 936863147 936863189
    0x3020610060c08040501030b040f090507091103061e134214040b060d0204060e03070e0105010f032307031808070807050a0b0c03100e070e040c090807 66
    0x6158010100360030448040c1d462030f034440409106900401e418960345240c194419100d683c8a00c001d890144003c02403a440e0703042c003540d10013541c800c42284904150500c0815000242600c1c007588014001c0280b85020000008141011040242d0032000c4108003040c12109402914032048109408002d1080d5040c01140d070129076085415940b40001410043c0c0700c645036030401119081010303050602c006030001406420440206e0b54444c20100710000114002d40c020006c40b000e603252801824030050034161120202c0c41005461000d401c0108440e501419101d1140401440c00080d4070920f400302e048c4103c007041c00f905900402c201008070030303909449038400c1400c2240907401101c070550b440c1503031807043e0400141056000708020041090070056207144a50141c0030704503528012444c10351f545c0003140c00c0082e100751080c0004202c1e07181c2003124082c80c0c19a9038101503141c01020301c00a0580000c105042102846c0000340e0383c00b061101c503025000128102001c856022 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 936865647 1250 936864397 936864421
    0xd0501060f0c02031f020c030d06050405010f03150902010c060c0c021504080705041a12061f0302060f03090a1e02040509010e060402152a16030b06012703030206 71
    0x801c841404a078400210240c1d9000030181003100e104034841d0f035082d01000301a0080d001d1840d00f40c44074400828a44413101c0d044d001801562010707075041001c0d80e40c1c7c030412480111284800b808007105051454020010b9400c154840b03801030411258a5495541e404100c1c0c0c44021000009901440312404628185400240c0390240c11382d09410f160810701919241c61852150b01d1081e42e0320708480528100d500e21090030b43c580141288804e0081d00c01e00c544460049800f08543c598200d00b400038445a030401801303594006e00383c1424101c042c040950580d001074854800352060b0f001d0f03d80040d29040150710b02080100102d600c40a1500c1400140d070b00103032080845905064400d110310742d001070015030282d0102c8450b080d40f042c4452241c0207100341e8031a44c1d28444502d98400e9a50500c1e441c115095544004640f0305108011903240980e0701804024032210820380131405541c0f046a1040b031345c49070640781151440f403034007201000c0035a903482203026170091810011080380403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 936866897 1250 936865647 936865667
    0x16020109150e10050a1508070602030403031d03120903011125151503032d0806060f04090b04050601020a150f0216030e03010f02040317030901020c030d050106 70
    0x140000d202000440c1c0c1c45000d6040194025450656200100b1104400801541d10040340e40d4000704030f03900f004004000500801c40707001c51200b8038001d0000c1d000e040040c24900b11446507000d03505203030a5030707402c5400c405212030154606000c000300c0c91096a041c4062400103c41000d482c2c7e60b0100d00b4245030039100040c01800c00ca082c14490311410580c000c00e40b500194000c550b1300d08103642864100d60301801089082c102d0703490070009003c185031041c8518241d03406900d6481b15654a00d030401c409002d003a002c90b01064800307688184140c020009907030403283c0146054100840b005003107649030440d0313210b42da105481e69003440c1103040c41d00c0f603980c001c4001e201900e0585465106e002100100d0f01651101c555180440601c503d2940d05a4000f8448001c0741c12004072281402881d89a02d000c0b00381c0300c0c4d440c1079060101a034040c400c0300d0849620040340c0f5200404c6045507002c43d00002d0403a00695000c00001c40c02c070038140024110038524017800201035041c240c00600321854 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 936868147 1250 936866897 936866941
    0x8030d0603290c0a110a0506090c06180108040201091d0a0e03160b040507090e15010b03010f1a07060612111e040903300b030c0f060f0f030c03 63
    0x15014442010000d8490855030204182c248199139401000d0102c032000c2e14203081e441640190360310f00d07042050104203180190210022a0241d4038a0410000c1600c40c00002100210030600c1c940c1a40d402020420340c030500504082d020244d03124214100344210350020a048801e1004000d901c040c4c41c0b0400b5101c8000034015810032001c9145889000400800648250704000008003000010130010000d08a480d0701880441039405445a5403051480042c150820076000400e0346c50300304d070640303040b5110080503c0205241101030740f440307a180501081e403000c04100403004074080e0f0003158001d165020201461503030506100d19490000400c0a01c2136500803003040313240482034011480c0a10803940000d6084c2e19140a40324180e001490300f008048100c1211229801e00d406003540601d152020f0081070000030805403624800030420354042043c4520725220b0504401601139031142c1510b00f450180c0c01031400201d6001201c140b03451000000c02c002c0001810701044c580303075803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 936869397 1250 936868147 936868193
    0x3031e050721060f12080d0f020405040c0206070e120a08031003020109091112090f2a090c03040b0709180603212a080304060b1219030305070908030d0603 68
    0x424141d8240018440b8030800110448170140401446081d408552009003000410410301c6070310164400650843d00c900c620980c50000b44150399800414424441c10103a5280180034595004026902c49902c030819400e1084070f00b264000380090004500800d80701030340f40a03151031803000401c415241e80110b840b0701d080c5034040c400c145100d0140c801c54002c170701d400142e41c0d440c00c07689848c003400841d40c0c100d84d100c1c0070320b100d1304c1105100500c0364035482842c48811012819003402007816040d80d4045170140b00b00b000034007261402d0022508070005203031664070140d03144c0c1c110908181d218418013060340c3e9040c0403c104401110385012200350645204147c3d8041040070300031211240c64440820040000a4a40480003194400c03550344075003101d0b01d070300301410980020a81412490b02500164458681d00c1030006051491000d000900c00c81c032400696089024003009003052042c03102036000032501030414000703022131002241c40040c045140d030a0104504800a45042c01c0d04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 936870503 1106 936869397 936869399
    0x32a031201060801051c0f0602070203120a03051014040b0406051c020901081516021c030c0306060306060504090506030c090907060206060102160303031e05072106 72
    0xd240c2d5514410310342e0f251003d0008210301043c180301c000100315089000030788800814150284034040241c20144282d010034a40f60303046901e50316170040070400c600d51396818861141c2c80f00d80342031111441072034240410300300010307007036218020390300c540c010000c9456903000f02c4010100a42040d960030343c02c07284c1905100c00c14400303d205a00140000036150400122800300c8a61010141001d454580c028801590100500402c0d40513104401160403c3c000409410301c0d115103020408030b681510040449045070001c0c01854540003090210036804810b503070603511125070005183e211407001900d4400740041e41c0380c0c024060420000c00c6100400d20204840f4075400716002900e40f4001a40c99004110890b40e05829020082010038400d8101c0c00b060b00044401912500c0314039069021b03240c04039541d07004603034031002c039a41002900e04280009000c14508215103 = true := by decide +kernel

theorem cover : BRFrame.Cov 936690647 936870503 := by
  have h0 := BRFrame.cov_init 936690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 936690647 ≤ n) (h2 : n < 936870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
