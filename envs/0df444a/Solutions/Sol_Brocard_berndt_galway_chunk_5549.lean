-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5549
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:14:13.213476+00:00
-- url     : https://prove2.me/submissions/4166f7e3-90af-49d5-9704-6c38d04a6999

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 997841726 ≤ n < 998021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 997842976 1250 997841726 997841731
    0xc0906250c0f050f03120c0c030f0307020117010803030403030506040e15041103011e0b040f020408100501140a06200d0c031d100c0318060903020307290d14 69
    0x200700d4482014600030704600c110407141c000d2401800300300c00c0d51000f03480c0000c540710b109244600003070322461850600740c940000c002d140f540c0f522400301030f485824070120003000c0c924001e030382d450000561101d079000e00f50340030310428089034003c1001070040386c0300b6880341d90400401000802c1e2105442061480c1c01a40007900c0c40c082d0070310301070204020520b08947c0e01d02000342d0007800891401c1110b0580b40d2034442c1c554210b2915803084040035551644500c008c500340103000c6464503103c41c001907a0b10b5210400710032003860500041b510301409200f03209100c0005000c2d5040904014003142d180400c5011a00d400544250000f0344090510900241d442d071642d9410f41c3d642d69040003082d460070345059038108494280300381031507114400319480c400c10398100480380801620781290701c070000d00c3c00104031138001003001c10820b5000c0d5000d0b0841c0d00807400c44603107030b84802d0b031500c4021041380d0b91420100d801c18104000c0c5500406810198244140041c0130709503980c18054a8004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 997844226 1250 997842976 997842983
    0x7111009030b0930090114040b19020f1507051e0708120a141512060106030605100e0a03060e0304030605161704020906011d03011b080f0c090625 64
    0xc540c4c0c2d040703802c0c8a102541c070076445040c2d02602004040826040d489021a400c1c100321058107a1810006140201c60003090100d5440e0703030340c40c00251140e611b8a404c80e41c82006024401901c566940f00140d602c0c078084c5884000d00c02910340400c26103e9a2203555000443c070041c083c0700100341c9109000d810b000740110a0103903200304480244000765030040840800c03d24244005500103840305500c2c0d4010f00c01800c0c40000300c83c0c04006a0001e00b00c4251144078801d4000108840754160492804c130351080e16280e4404000c0c0c801650030390b454656454100230001810000b01c0c030306412001e1440e40d00c4069926281d1261a1001030f40c3c800c48410085070900c4c00180034550740070b40021301e105042515a040c908240d400592030303210261000781000504190030501c540140e00c1144209002402008924007800202c00a080b4001c90b50010038500000074000f005d0007101140304901d480c01c1300b454003010504102107504080f00201c4a04000380030f003090014031100c0c00c1100c902 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 997845476 1250 997844226 997844233
    0x60e010903080106080c0f090d080309330604020904091205090a140609040e160617070e010c0312020904021b0606100c03122d05060607111009030b09 66
    0x814280a050501c040c2e01120170000340d007040001c40c65825042d55000395a44003030039550006070000544100d90b040000d440040000207010240d140060200b41e42103050b01100041801030b40000b16000c282034182c151401d00200107041c070b01d440e900030010044003c3c00003440c28010b8503029a00c400203000c2c20007280000500361403e142c050300701001044400c01c0508207101c408080380c1c0500440c10200e009944500c1200321454080c400b2001510101a00010943d56240018140c640203580c40c41e0708090180481d003217a00c1380441d03042c0d60348103171182c0792500500c2d5001c65000000c0d00884450960a00ac2481950348a0005201015003410f6a080b0020507080c49418150050302d21032054072101c810444240d0400020000141c00d03080c0782c0041169441d5a07800303048103070030400d0081501c45014030f190106002c50b40503006c01c140300304481d80e1804207000943c4a03050000e011100084800ba201c0d242c42c06110280c1419860030f1003d0035a2585c1c8c03019446010340e0040b80d40d81 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 997846726 1250 997845476 997845491
    0x180f2310110414091009110a0e04090c05091009061401030e0a0b070c020d051009120206100306090515010b0c010e0c060d09081204030914010e0310050a09060e01 71
    0x203640681034550002803041442d00340740409002800300340100703240c020541e0800040c0e2080e842101c0f07100400b4070805c1846000c80150360305085601a92034070001c035400b100500600c2c1040d03c1001080c551084000940c10306103820003d10b0f42000304051000100c9200c040340c2139009025202c024014585540c5880030300d50005011795206840b8448075600541450010800b000512a0004400e080002103035503d0f0012840182400c400501035100b05200e100d04603a2650003000410f0041c48005880c0101c010201d03110310307042d92421080020940d0504c085052540011010742c424800c4030022203201c402441d6054090307101040c444008904510070400c01e0046511840c9142c0c00b428038000300d440080d5803802030146013484030345e54120303031401c020750b00045a07841c43c1d1599407099603107020b240041100038103000384410700c925042c0d0a50380e94080c0102c6403c620004016010303101011311000c0003800c00900700e4081c1625564032001240982c840c240c900100e0400105070107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 997847976 1250 997846726 997846753
    0x1050c24040b070206070210151e09050c1603260702061b040f0b1303081204020f1509010e041e06030611130b0304020301060b041502070801180f23 65
    0x180020320b20783c25908076108014005034045080920740d12103900c0050301410507100c0c01a11181e40c0c1000b07503490203640902030205160a07035001118000d02003444181c1d41c9161140041c02185c500030003000403d444c900009000e1000401c058904e611420303850854040200c40c510425a80c0d8005030308110306000040b541c500c2c00d401c9203944428030311b10b450700d000b28003c02e0725428030459090758004035807210101010a0180000d42d040092070b80c403407480900024a594003607404900c200e11000003021642840002c40d41501c3c1090209420811030400640c0c1200510800c154810313603460080030843c060085c0141354010840d00003c08505500c8c09400b00c41040c9010044104140001511320750201311a1056450340e0f54641e4481e10341784080782c05004c940d006080d40760b20105c0c0c0440c01031420003801079142d040390308071000b095440b81003c0c00c17510703001c5500c01e07402000003051020034045c80e00d106e402d500c68110b00304100e50666100600e500702c0c880d001e00e6600903000081c0c24 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 997849226 1250 997847976 997847993
    0xb0418030e0102032d04080f0d0306050102010b09130515090a052b0c06061a0715060f140f12070e0106080105130f020c12090301140105060901050c2404 67
    0xc01d2080c0021803520040004886030b80d210381c82c614a4851071154664021780e43c1c02e040d5030050100300b08071280b004070412a1519006100000b200182c030784440091558414001e54a42410182c0103480c05c2e04c50320603542c00120305240039100e600c1190f05a08100388540136262207808260043c080c401194900716091400344880b580717021650a15412080480d0f891002c04030221b410070040b000403515008018040a9020252103030b920200f101c0030300300020082002900c2400140400b0404400180440e000c60080004402c40d0b41024800f0a681c49101c1ca40c1d04002041001011002800a02c10341e40307801c1d0308a044d4201c640100114201400307403d014015500300345c406581010041621031820518150046498400b800c400620640c1100c036140701e100113032010a0981400b804165000b5100540290b10b0000d003150051240340b40c10f4180c400c010605860b001c2c03d4401110aa0000801c2c0152405070050038000d64810744201c1400303051007102d00b8880d240500b45800c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 997850476 1250 997849226 997849247
    0x8100902070503130f051c050726070e0a0e0d0225120c030c050303072d08210108030405010203221e060e01030b090406110f120109050106020312040609060b041803 72
    0x404240401007e4005980882c80c2c1c03040d00c80708401c1c503d00360380ca00a10b42100740d52003001e400070b00a171080403442c0d00c800103001c0c4c400c070341d42d910a0201d00400c696203640c075000300000400603085052404940110101c03188a0261450241c4101c5602c4040c038410b0451481e8080b1041080300c03070b0030410081800c4100c00201f40032000b0310306144090721070801a5400c0c2400c00b81d1141d0700381880609418140c200840281c00696064403101001a03521001030140c1e21507164500800c00080c480c2400011903055620603400380d400e02c551040c00c0442c0d8400007140401020101e480440c82d00d1114181d440c100803a8030201c0711491501c48090810358074220014101400c20601903c1c64640c1140a90015400322000481c4000344841c8540e6001368226002c00c04800100020200d01c0c200260381659801c042c10020303070340c3e0742100f80d90303034401c0103107243c601211040000d0120300c25620020803d4000e16000c00c00200c0980001c00301d46213241c15500c12510500b00c401855403000940c1c0303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 997851726 1250 997850476 997850509
    0x207060b090c0a0809030d14180111040306020f1204050a060f020f041809060f0f05090a170a05041a030108150f01050409140102030708011508100902070503130f05 72
    0x3100b41000200d5501610540c0015000e00c040c4002249003200104115004071000d0344c420004085080003800b0391403025105c0f00d0a82d000820b0007215180b0602c104e04c0d00030700248003240f9051558ad500c10181d00a203011841d00b660030b01100c120720350500e0b1286d1003244514003618601d2a0361810b5011101c0c410544455640305001141e9442030f0241154155403d80740c08404032141403a02401a10582e2801001d150408160411030400382d04002445020a2814000da5851201c5242e07200c0d1002000340081906c01c802d0a1001449402008105801d162a0303192549880a00c20075800c1c070500500071090000040141040c20320043c9030140c000002e28006061140d5118901d0b441030141d94429980c1c0e0080e9030400024a14900b942484203000f0b648074501254050811030091141400c0e07100b11f0b90041c2d030341610610304c10788103900d8100302580850400400c00c00135006102e080311070713200030403002d00358100c60300c44a0005d0075001c2d0324070041800c010903c603882c03500c1c40805 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 997852976 1250 997851726 997851739
    0x7180602011a0409050f0a0c0f0b0c030703030207170301080a060507180905070315140a0503030705030a0815061308010e0a08091003061a03010303181d0403140d0207060b 75
    0x5903040b009000824004100885011824204500303100c0e080c1100010310715010310400200d84c0405c940c1400500494940d05d010b5a00ca681d50560032074188640e1901c200180c00130020f030b100003030195000d130100500402c42014035000310898400300d6442a08080846e07444540b41408008080c001c0c1b65012a0034a04280d032040b200ca040170f4440510300415020545500000351800d119611804880d050403003484849651079564100c0300030024a014000e84280030042841d0400004039912550310500452900c0c03142c2800300c880080c0900900495040c88074140000d64900c0d02411035040044811850030340380c42402421120a20784442e00c6401002042e00424040000d03590942800c9c4d030301021300110790b84124010009908542040701d904d00078480f2091110014605070303481303500c8205000d4103001a0160a0849206d441062500b40c46035881d01500c40c1c00039a0032510a081c00015803805140684068000c0d5880b0014503502042d0001405000e0040804144064500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 997854226 1250 997852976 997852991
    0x80a02101503050606040528060e0106030c0516020109050607050d17072c040e0f01180209070f0e1018150f080903040302040504110f040b0306070c0203030702090718060201 76
    0x149904c44070020320355885159140300007a41d010943c1d00303889840c1c07800c0b0034001c070714102c0c9105080106000c1c0a0800d900c40780b1030000c83d541d80203110f280920303805c40e101c1c2400d200c113013081442c034401e010070224100010a41e0001e81c581f207078009402200c0c425800f41c004da098586004000001d20041481c84014050a0001c410f40000320701c2ca0700e5444009240002000840440c0200c0f003801702a50000e2510403400c010f01c1d804180801074500700f2000b480300903400e8810941c448003030ba1020b54002e025502140c00e05006200b60800c1d0070382800d0000855845100240c0e44602402c0c1c3e02001c02c28820003006071192030680207019068124050202140d02c04c8001c00ca003040300480000d100c840c40108401c5d00080096800460b8004c000384907030700d001e02d0100035100e141e100031406805620780c80c04c05403403e40900441d402d4094000c0c04aa1760740101140e11622110060760180070410210740540c0307614071740714480c9074a038882c0d20200c0300980c0000180b90f01a4444811640f60045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 997855476 1250 997854226 997854233
    0x504210e1e0316060305040311030405100518130c020f120301030b04050703060e1b030d0e040b150f0702210a020609060f18030d0e010c1509080a02101503 68
    0x11511511440041d40400036205000400e19100c003442d004240c1d081031a0b0700082e4039505400c040d00c102d111f0742d940d440c02d92a60311b0841d540c3c0510b0280c113a1160364540207420541c80349014001800c04944030130115000e8101007141d020400390410580d03912401c00f00801c980400c24140d0140d29440200304450f40c0c11a003490b01d02041c0001820381941c00081014080204142030141d13410000400914181c505083d980e10558410748004070365403420341c0003a1070081703044900d41d0001e484040c031244001c02040f0045c900a04a180e01c40e204040e0000020140d0300a0001040741c1c0d01c20a40c1d0701490300401c1640d962581035541c2c0c009081403201691100800c40200f020b40c1078a0680e1140714401c001045400741d2241d40c00500c60200300308450a041d6100c01480007001c2d01541d00504009008846035460401001e0219041001150010b81101001c0d010f24144d6800081c04158940d90640982e006104000060744041c2d2400e041180030b1050101060082e102c083d5582d18594 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 997856726 1250 997855476 997855489
    0x60d060f05010e0d0f06020912030403060c0f02060a0b0102121c060f03080a0f030207080313030e01022e060b12040c0819060c1e050a021203070c020d05070503010504210e 75
    0xd074000c0c0071700c055040a808000840d016500748020040070080300e04050f080181c0d6942080c8029036800c1d00302804d0140c581d02609821424602a5019210b1a5904064400a031440d290031a0452090555003c11301c0f08450242004040d080ca0b010300d104c4030361a030a015070b200c1d17410004130104522010000a08100c086a54048890414940310315040c0e00582c0207009450000c0c2c00324900000700079502c40c060030301804051090715580d0b11405c10400481e51021003010718050f0018030b482c2000200c543e062001010b040e0303910003081c00d9031201c81c40718194101004810074412260140420041c45070103100c0940840e100801000c6c9980c0110f25400b496000040d1a0550790100518002d12030018011a09040c01c4030281c0c03003d2100000304142c0c811209000103010f14013a00c2c00031b08040080300c2c025070103540c82d0354140700709808129880c0c00000040380e482c401c00d000054207890a0060358131913806035504040c50844c5070b0201e9200c808141c00441040340300c04241ca40b9a6460 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 997857976 1250 997856726 997856749
    0xa1e030815031515061309050f04051b0604050406080606011d0306010302010503040f1406061008010e04020f06070b0a060501090503030901120203090a021509031903120f0209060d060f05010e 84
    0x120500e51244d120740210040c0d81c2258211290000000111000309280c1c3d9140c0401704c0ba01200d042010341c0c0d9400d42d6000c1c00c507081d42d00078406c0d086941c000ca010700e1040451052000c0c0109800d140c203a4070341c0090100c822903488100242c11013410000d207584c0149592010040040c0103e40d10403014000035103c0005001c00cd06101002c4085020b0001a4008100e400d0f8810b82d5000d010001c2c14805584110446101c1d114585052000490511451a175812100d184000e2030050701d6581c2041b00d0f0441c280b4985410501c1400381c18041580190094015400840000360380fa08240004052500c42d4110038040d5104100182443c1da0040444403104000d02c40103842c3c0e115412180c0c10910300505c041d611201080038480c180061760010300200340101c00b154041416095440141d084a650107408034a4042155403100c0035500400580c02081c40300502d0300a181000881ea50880c1c2d03420b4440300e40e140c0041c0410300441c907103030000d48401d09100c84803100000004182c1c0081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 997859226 1250 997857976 997858003
    0x80105180a0308190c09030b0105060c060105060c0102190c021921140f250305030d0b0316060806041d3406120f2a020a1e03081503 58
    0x1100040c000303021440418041c00c200500a014880c5d010030014000c03003940c041550912400c3c0000a8549045401c40c3d1150000d1005441c3c5a807908082010542007800d40ca61555001c00405602c019451001c0c0e001d5005c903152402c60b0103842c010301210041103003a440702006802024020340c01c01642e110504104108210411034961908540b68131111103040c4991141800190000d1408907a506980710300340ca40c441c00101c108204100c582d0280300283c104e402c01c000c00d8000010581015103840b4014048805003072a089043c04596051740c000400510b8040a2001c14940780c0a50010b1368041d5150b0350781079003440300b80c54540180c488203d854010190215801c0502800712803900c1c01d11000d9000c0050b52001c0180505c5003080748080e1a614000d0764081d40d0902d840742901d41141220740200d0107014003d4440e210b40411441e03810762140d1016140010707034214946140345517140200c6001d0030240380c00380080c60040c10049c40c1e00c0200603d1519901c00241e00d41c1e0000c2d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 997860476 1250 997859226 997859237
    0x20405040201141c1a0a030816050d090602010507030501050a121a0c0405030708060c0f070510111309200703050f0304050a210909020c070806040606080105180a03 72
    0x31544010307035000700c00c5000c103010003c0c042078010000c1032440c00390b840100c2c1d4090501100d40f0980081000c81d440018841d44180a498217101017007550014007010130255904049000c41030f110a40303003070448201000005c030560300a000840c2d080c09680d40107800c0c1d09042c0540d504180000d014000c445c00340d01d10700c03005004c0e54000c0c0990801c1c800b03084801e6918440803410002c002415551042c02214040d104540d00014117480018145100785441c0725030034200160401c503444075501844041c1d032036214028250541e0b007042c0c070a425851030081d00055540b50b442d036401d90140201d50101503040d1901d04220000c03103e0b0b00c1c000101012003102d0766a01d901c0c2e407500741c03031500030140516180c000100801c010030100040d030150450041480c0d2443c5034203d1010002c1406814640340029107480b820402c8230303800d8001c1c113222452041a00d00654a86240c1481c0180850381901d1807134440608011001081c82400e400c031085c1e50489100c07481d200c0129980300100c2c00010704000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 997861726 1250 997860476 997860481
    0x7030c06180f0905044101020d090501090201171527070903020a090603030c02060d06080703050304090f061401110c030a0305030f1e13030c1401021c0621050a0c0b07030e010318020405 81
    0x6d080d4111551a049900c01300704044041c1413480c02004001030403400f0800c000c260385240102c120030140300b041485401d0038034854103414060310810b10074040080304220040da920110540d03040d20300c0354400c0d68440800b180382d8010449142034542c4184016031030031100f800480c2c0d2014212070140d8060720300302d64566401c51508001d060701d0348903282501820390044200300020000b1f00844000000a1000018107906d03401212035070b00c14000420f460b00c2c81c40c004e65004030412482100700d1426640c05001034804a4100f660401040380001c00007c2000300c000000310000c0d421030001c8030364003200c8200b404560024034001d4006c1c05800c9090f1103d40070184a131040d84507840c3d001c43c81443d00b200000c0014042d4100d420084c885400b070f040d10200c040d1740352141c1e00445140d000542c0300040b0030200c582503e010004c080da51030003018100004214846003131401400b14000850340c0e03040c00d00340280000081100541010300748061002003e251036240e0704400d40483c3d0001d0a034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 997862976 1250 997861726 997861853
    0x150403060207080d09080d0b090105100e0406080f030c0111040e01050904050109051207050c1005032e1508070914060306030f0d030203090f07030c06180f090504 71
    0x43c081c031000c401320740e401d00309484104401c40000d820002c10303d62046c0701c1084a40200032404100340503c40d007103008621541c84580c81600368a090340d4019100080c1e141d00d441c0c80c14240104108044c01981c000150300300f13201d40034412840081c280b000b405040904201e0000604101842a6032240412001244c00c0c041c00794041c1a0241e03000041700c41144255a00503000d07005410141c2c1c0500030305c00e00350280d04000745c100342030b00740640d0f07907134510380c3c8001c141910303001c20140000845400c440c110802c40a100c064001410083d400c400b403411842c034009151a900500c4141001136051040001351642b414200f0322010884007181ca90b9503040101e80b41c0b10760311402d6035441c402c80101200703264040c0c3c0114011304000342900c6503095005803040c0e40d9040c600c80103000480006003007204c2c0340b042c1d801d4007400700220b0303940b00704550b07541074014411604d030010b14071070303550307506200401c131500201d14000001049003c00301058004034811810b103a45651486110395134800804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 997864226 1250 997862976 997862993
    0x1e030405030c06130209060906030c01081302040e0703300309291501110604021c021207150318201e03241605040302100305090c150403060207 63
    0x2c1014001211041d2820b030003540a90034454074140c0c002c3c812000400d03402e003000c0300064490302e0050010146e40c030f03c55004491404008141142503074012a801d0010383d518010200d54491004c018602d450950400b8014900e0841840d080703ca0070480c50902c9030b695002c41008440a8140000c0400da41c0c18000d00552050b0000841c1d61514503492486c80b50306012103004580d00c4d001e81c04000060380054035040c80090081156901081c001001460044603070261700f403510b168400c800183c1d601042c042c140d540342c22091b9400010040c040d101500c42d900e030100ba800d244c04d0280740054600c185004030781c003074003a1824010464082044400d90301411182c24003500c0b1b5407000702c184032500c035810006949a8440e016220041640d6004030740386100c00200001100400c0e107a075404d2094407480481d200d0140301d030500001025a58041940408680946000c50b0a181000c1200c0c00e100c0607000c032501c02c01354000c1150080d1481360079101541e80c8580300680d65600c1d41062402c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 997865476 1250 997864226 997864237
    0x5070602071a0a06090209010509061c18110109050a090507021501090e07090605010e09040501090b040b0916080d110a0f24020c06060405280b0a08031e03040503 71
    0x1010705076070000030251000c0b01141c03041400060030841d1680341c800040917849545800c50004405014540340d42c0b420b0b0000f040d440d200400504003424401d84844160342528400070021a0603040000501c016010200b08209003440d14090803402c050014096556034050a94000d9480c80051400c81c000c2007030004031a110034001406695400c20340b005080400007a1105004040b00041c0c012014018082aa401610791307a802c0852207041c4030000030000d10640d0150348800113075012410f16000035005901981c880d5504c0d160075030010f13160242d0381e101e40214028025042081010214848a96800910f04810701d248210f640c00e1400348610005006800860107880400c10560b10020607550b600c000c00700d50441a010b002c5c105e000e0107080001d560000b07030000d41580740c5540b21581c0024503148444003101c3c0558200c0580e9141e90f62403055540e1510500b1903850170640c0303c0e004000b4070307000314540b103100c0f02c1c500410742c02c45030440e1032008088045030400074107106031071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 997866726 1250 997865476 997865483
    0x50708220b100503011a030303041712010303120b100c020405090705130f0605061905031308070c060e0402070c12020f03030c01020a0e04110a0c0201050d0905030c010b0d0b070507060207 82
    0x403180d0410760b9025914a2a901c5210700c203610b081d00c9038201c07417a40d08150907180c90040196081d655691070b140301c58102e08803103d0491030700304144009007180321040b0303002c1c501070740c0c0d4840209051060402201c0b40c4050b80361180e00040c00d140b80132644400c121f11000d42c1500c02003070700e0300c1e04150b20340f601c2e00341d8003e56801140510104501141035000101c3c8040c0030b0428800719580380140200d40c4590940c11520687c4907001040d1306004000a50700b190240c01c840304021078603100e003072a0f40c03c6414101c8003065900382c1040030a42c0040307480d005800850701186029001d580300d4002c01d840744224501150320404170000d41d0344013000441e081c800034003926520071090300703914000e51000f05000041402e00d82d5010b0303141020300c00c081c09001d8507040c1c1c3c0c0c84c206c1e4419041d02c3c8204003440c1207041100070044000c0d00d03941405601c5005129000440d00da40340b080d0740c6801e407480300c40f84502920500c18190080384c0d48084254100599040241d40c504142c10300001074459042e014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 997867976 1250 997866726 997866743
    0x40b0414040f02150d02090f0405011d04080f03091006060305130b040501020909091c0203090a062d02100506060f04030b07030f090b040b060a14210a080403021305070822 75
    0x2c5e404541c40f60000d00d590746045400900062602c41000101d400a02441140210612003520612a0544105d4100d40503008440c28981e840360200c0003940112140031158020946580701e1043c1802400e0141241e0300f4148510b00c0c1003840c0300244800244050b0020f802031002c00c06000c400c2d81207401c1c5820103801d0070100c0ca4044440390390390001403010303400c00f01d20b03200790159a840441a1560010000c09085140385041c9080342c4855240080c0d500c0340550288601c40801850341d2a0010510381d00546100005100303c0c0b800c49000500d001c2c0104410030400740c250041d03c0c2101c0540e68041d011603865240c46008400034401d288401100c070b49004404024011501015485180f0504400a1a64900086c0940340c0d00700e108a200303c1d0600c030110105803901b07407208180181403510110100820304460b2785040c04101c1c054481c0d12300041d06009500f0010000440084180d000740311a0820240081c15164004c00c0e01440c401550840a0150b00d9a2901c20003942c001c0750380f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 997869226 1250 997867976 997867987
    0x8030d11041208040315090b0a3c060503070f03020108090304030f051b0d050a021203070803042018041509140106170a020d0b180d02030306040b0414040f0215 70
    0xf4a225440b81c0070680d150900443c100d4549903180c09850f00d195800100d40c4550b03200c142492025180c50380c4007186426075001b008800027004e9140000044c42c66003c94540665100c0b60000c64900f9000f01c0e000e038004c01c1081c8000c00f5401841001c895080c41c2407002551280d0703035242180900c1d0001401a02d0701c00700c100034898000b950200040040c000c43d0018a11042004040c641400c8014403035009400001c001d2320b8a1151003062100d124262480c2c01e64940e10420543d10484040310540d500040301a10000c09031381900300f1a0040e28140fa1180a4503440a030310700c80100001c009420300c006449000c1c115030400980c465100c4043c046521580280901808582c0a154000c0203820202c0c1d00c40c00001403010f400c08c0c1c01810311007120344540c50b040599040201440c0382040d0844d8150180002000a200719004c554003841c1c507402d0900030041600d00540d0780c148124204a1074241c821000d4292a40203580601c90050305071442c80800d20441c4803920100807102d01140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 997870476 1250 997869226 997869233
    0x40f060f0201050a0203072007080d080f0f09100f091e1208010f0603021b030a09082e0c02011b0903140118080d1503080a021608030d110412 62
    0x21044816500d0380080c0095074030005480e00704d0004907854070001c0c451001150034013034000f103409842c440b06c9040e520351503180c2d5040740c42e0070451560507000600d01c00c2006001726010400ea82c1007440d000110600d03042048280781c3e031380e00c0070005a8a140c4d4900180c41003034102c6d0f0104001a901500c0942000381c203400a500386491501e003030303d4140c00e25106031a981d120b01003040c180d07044901402c101d107042c00b900301e0083d00610100000c9040c640a00c0d80960410409806480e18030380c1c0d0501101d00f0b0041d09818156040c0103007040200300c004510b03025071000b00005414000c03080003b4441c0386074200324090300c0c454a0400f170845003114204411035100010100703403802078041d8407403025902505400c888101080d42c030b500c400340800800007459040101882c07805000086041c0400303500e0b06150018542c0100e84815001401181c0c0d00c0d01400462020014502e640301c03514540800c86031a4442c0c000c0c003940150340c41041f100c0c3c0031440001d5501808490f104185225218074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 997871726 1250 997870476 997870487
    0x90f06360c07050f0129040902060301090516050703020c36010501030e070509060913080c0601210c1a040803220b0412020103180204090f0303181e0503040f06 70
    0x1041d1828000c804030503011300014025900588004c05541d0f502d414040718040d5a884900d458070740c0540c95100710340140e070320000070318045d2550000000b2030f818002080360203101007800c076409014050003031402080d0085910414a171056540482d015100001e20011000e03ea0520072144040e54010989076443c80340103044c1c0301c0070b0320100321205100780c00607582c1149104071907000104800103006401d007100b640c4d0304000c1a1800800a0b00143c0d031f00e005035003028042591991185c001041604070b80f43d00d449096051032102d0b40035900913200c813290411280103000c042c18a0010b4103203000204800c4030000c00d100310a4070b44980712a146c00546101c11503110756240d14010012403151495000c0f242159048030740e410060311035900650140c85450701c2889000382c0c10350601c0150303c0d40c0c003400681520416205400464038900602240d0030f1925014900d8901d001c13090006d15035500841d04007810760b880c61003142d014504245144641d41003000c1e481d4800c030002482d550400e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 997872976 1250 997871726 997871737
    0x140f0c1f0c14040311061b15060607050a020d050c040603050c090709060807121d010b01080a0b030d080c090d050a0b0c16080a020106080d0905090f06360c 68
    0x10a4140300c141c0c0100d00440c0c01d10080c505441e0b110804000c20000580840aa07940e004009080c1908041406029428120b00c1c4002e0040e540c010070f0100600301141a17865a00c0403040392140c1c2071040580f501a41c40840c480b00a0050381700c0404001444420000060280001082840055200e152081e100e14009841c00c0c020708056011807102405007145400b562030b45d56480205903500300c012100000308040c1c0c810400e94420340e04901011039801c1c15411140c802c000b007001c2c0d10701000107220303d10003820300c40d07070a00d001e85001c6140c1e000310ba41c00b41c048040c03a10309100c0e203945600c4100c606c5486007181c0d00803040c03280f45c0104007000c41c054600501420008090f9950500c24034041d1251101c0c084604004024610010340040007404142071603100003c0c4058a60300001d03e4410961021800b00b804150100b02c83c1c604201182d500c400e0300c130016080e038117001021800c03089540203a0203039900040d0041c4600d034118440314001d14039507008840d1f641002105140c042d0301a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 997874226 1250 997872976 997873033
    0x40605130b04060e220305070507240e060307050f1303121b0b06060a020312100f06030207080412150911090915190b09100806100303140f0c 62
    0xf0030400060f80300d403c9078030758454200880617102c0c10300341503601240900307058030031001d0003400e22686000c04c000300b146101401070307007441400b55100380c40c1041c100c2006410b10001c0042c02034802c0501d807940420b584e004802401c0c0640c4410b00135141078924000c500342d030b010f0000e001c2c000005211101c000038901d03400f291110f5000403500c9401070118a1000ba01400f40302d0140049200d07030911a0003826051010b2041e242048001ca100264000c016909401c1e1640351134000d00102811580e040000c0205080852034075440e5510201c040c01540701d980307168009048140d01740300340c0400310350004c09440c0c81001804100e1900c20382c0209400718260141d0000d0000800030720f00050303c8810b250110104140c99580d41040c02c01118802d56810f541a469024a6080d40c452100142c01501d69650403280c5c54149001d41d494854018440b00420f980224100046034002942103640004081101d5035540c8a030801c1884e807054030349005180c4504038030b00d000b298803044003ca10309071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 997875476 1250 997874226 997874231
    0x30d061d04110621070c1707050606040b01030e0303010306200a1b110301060e0105100e06030a0b010212070f060605010f121d07120b060904080d0902040605130b04 72
    0x400c40d9200044032801c5800802400c000e40c000e0041d850604090700c1680255540c207282044031100019004000390b448001080c0301981c403204220724a445240a20750201102d400d00c0b025403200e961b9890040d0001d800f50b542c40845603403503480f07234108000a0000c030045030b41e81d580d07a2a0950062955006100143c80b4000840910700000403c0303800c01d480303941c0d4040c0e07100500c10760101502c055490440d480f070f41421005030b10703440070300414000300039143d5444030540c5800141f0500c840702030100401c02c00301a043d80ba00c0c0e900e00f000e481d0410028038000400c00303861030050b842c21529900d08021458049004410031400a94244000740314a50070301165956000641d50788a950004c81c011940c80084452524640e0340144080b140800c1518190902c41400b28200040341d04041c94400420841c0d0091201c04134240740c108905491640840c903094440d4103050166000d035141c4c95844881450555a95810640250000402c2115254001281117006044400c5c581e8007960 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 997876726 1250 997875476 997875509
    0x30c080f0111030109021c060f030b0f0702190302031e071a0105091b120108060f220201030c030f0606021b0a0e0a050408070803070203030406050f091e01020c030d06 73
    0x6028008504070181207407402c607428208803002a4101d0031800c494000c46113100307c401442402814014405d8862031800c0034114206450021802800315070a02c18203003e02c4500ba80c0002c040c0d09190740d001e48000c80850307902d0200e0a500c5400e0908903a01d07000b145551b0141d55120080c03000c1032041e1140748400c030401c844c0d0b0340301e03440034410141d0004015000403503035a042c4000800301d4041111403450102201504140c80400f07070401c0b070042e1701020030044120040c41c2069001404042205030030749980d084c5141e45906041c0007070405d51124a0b0482c807500a0b0000e400001c1c0000e0140100342d1101d000070350303410840600c01000c02c1d1a104810302030400040800688a0742000c03224140d6440c0c1c200000340c80b01a00403502d0b00e004003d850040340c0050302450107400070768059a03480c1081d00304003064900240251604084440900c181064001b9042c10100200c40d041c58900d8007000b17250f0700a0044901d030f284e0130700000501d42c15023150740d4400025151106000c90212 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 997877976 1250 997876726 997876753
    0xa090608070201360605040f020a081605010e040b030f0a0201020105160206130c0f0311091b12090106120c17010e1f020d092f18130804030c08 63
    0x22114480b01e50300140d40c100031000c6803001020116060707054001e24100004585c0d0300c0303004907641100c00f07551080465800d20114a0072192810092032080002c1060300c042c455084400c254074490030b414041d40f0720082d092512a90044044030000030103440080600c4803c540d1a100b18905c22401946040009640161055020010100541d004109a41d252000e0000d0488041001e54460714803260000b01c1110100402014500c07681283e42000b401c9414090324010113000b06280b01400d00c3e180d5298400e13041030b2038192024000854050f19103860042c01400e0503009613001003254036a14003404481a0010201c8800c03c0c000032400c1050440c4501700c1d8003000d0b107000203170040320041051141042000b00c03429200c05005240150389440c00d011903c10316401c50f00c812104081405004208078611030319500d842c0d0700d50003003c401c000298408038240101b00c541c0300b101c01241c20b54240010046215510000d0307250368903103a003000094080c45200b10580340c4034008540c8140c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 997879226 1250 997877976 997877981
    0x9151206051b041409040503041511070e010311061602060f0a021c080c0a030f020a030b1003050402060412150e03030f0c09150306060946290a090608070201 69
    0x221034001e420300ca130b9090365808016078614054010350f410b100c10701c00410513909400d07020300c095096449185841000d145010304200495001d840308204660040005c40c00d10100c0d01c1414400310340700c0d5558800c42c40b20082280e2281000b07500042d0110f40e95021640c000d000740f2a05515400b2102e4850b031290084920440120784c0380c0000da82c400c042484c82060314040c0108178103074140803420450504400003260008543c480000b902c0c0c410725001820800c1c00c918510140789001e00080c81c06401140711445180b29070b100c05020403910300c003030085410840380203407040130081c8201d910600400350b0360340054507001803049041011444001da90011182c81141c0035000c00000000451940c10b25000100301075080003081041c000c145d5200341d583c5c403500024905000041162400f11202280031302e4003c00e08401620400e03490061244201d02103400883c4405403400030400d0100380314a0300c0d400d48010301e4022505690160704480f8401c00d4030510398450b1807030303600c1071022400d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 997880476 1250 997879226 997879229
    0x102130b091003050c0d0e03070b010801051003120309080f04080d09030b0f0402180a0905010e010c0c020f04180809030d03140f1b07030801080f0703080409151206051b04 75
    0x41c4800c0280501d10b140340242c10080d44100046070f210304054003800050180e90480035014565040040c0b070a013080a40301440c2d01401c0460020002443c02440c06441103101d400b01404840060307030340e418424402d03001030740856408150f140c2c4403042c60312444010b030040e00501c442802801c4541c00514820001441100c2e0090b100e15415202c60303c00030040c1001500980e00030400c410142c210044c00500c0500074510020006031041903410407508582c50300940d00e84607410030f40d00a86a642c0184901d01680c0c04035134094001d080d14002500820100c0b103504800c134903034070700b80c1e0a020444024042c40401501901c400400400f011402c5565004000250a40745030100e2804401c0c42c1000d50700c0074080e4454040010b25a0283d51507801000c421400507400074010701a80c7c07001d01c20300ca801900340b4000c0c1025800d640d641c044a000380c2c081c2c000c0c1683c1e0752002c2c12a000e601c00c802030040c0b42e0710010302c03800350440c200b4201502007100d0b0f01c1240c402214140d07568a0303130402140d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 997881726 1250 997880476 997880479
    0xb370e010509031b070e011d0109110d1e180c440115031407240216030f020102010b1905061e0a0c05070611030a03110c0a050102130b09 60
    0x1403a0a00c0c4240c04003130184500401c5500f03101c0c0e041d0204219202c080c00a0181944013005d18007043e0f880c03914410707000d058110304015803c099400480b09480030a40302e4003102154040380500064008262661030001a4200caa040419144e8413011041c08071f80114068100500c803e40c403030b00c3c1e0065940d008a22400d042128020100c0141c50031a0307180c074540e443c500c1003600040c24a101c1800d49000b10b025081000d0001030401c00c0000340000199840304440107403001d94078040c0204c8980c0d1481c942d007808449002d0080b84800d1080c01303031001000007402c0400c00c484e02ca00b49401e136407400c544224007541ca800c040903007a190509155084840040340041e0a070308000034450329400c5090072031031500030321110b0442c2c415410054031070b41c4015514a082c031060b60038560b261031819441031050011242a4011100c80402140c0445400d800d004c6181102007009413014840c00c040101c150040704031180030000c040d00182050202c03030b0f04502400d502e030745005c0d20074401d401c03426 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 997882976 1250 997881726 997881733
    0x5041209060207120f1e0b10050109050d03080615030703150603020705120c1e06250207140a03050f070602010b0402041d0a020c031602011b0b040b370e010509 70
    0xa00001c0d803460b8181d01700c1031055041d03440f00030408288616800b083c201c2160000942c404000350030b9000788030000101000d00e4800226071901c03000c43c03203a01100202070204815000000e0080d1076191840c2c103540c410b11030a41d6a40b8080c50010000c0890791601800d01524050005c5e01a110f4000d45031100e8000c07028200740845000780401c6079004c0c000c0c0700c80741d003c0d045c503075824a1400c3d0340c1e9130800300e48400035260620f00700c50303160134514400800355031081c0d491070852005a80002c01c80255040044500758501304800020007200b1581e000030854820600c59403020b0002103468011070311607800030700c29000c040041109a0003203008440f180340c0391805480f4804000c3d40c6450f08040c030703858014039004810310264210360001d41c850042c110202c94520440d41d00559117000c000141a41c0741440200d5503c0414140c03001d00058000e0a010020038103819074804c9101c4003400141d40d9518141000d0522300742841107180c02c0300c02d5407600360310002c2c200042c0103c500c6883c0f03a030080d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 997884226 1250 997882976 997883009
    0x1a07020d030e070b0705031b0610090b0103020702120c0103151203050f091206010602070f0f0e250903050f06010308040612060b0d050f06180c0d0f05041209060207 72
    0x1c070700811609100c56400e2092000018450180710000d043c658007940195985241d80f5054a90660065900a43c10340c80b400811040f1024440340a090b190304000108211703c0d0310300100c010b8040c407540a94400c0100202c004020800514444000000c1e2000d2003440442e4851220880052080d03014075401006c541000902c41c600400024800000280c00c201000d0040b40c100354100d2401c040c250302807c01444802d40400c2007100408071811a04000340c14009031042a80c060302c01c0300310b81907640e800325624a0800ca131017034410249400c1041c00d264540802040032000d4401502c040c0030350080e0204500010403214141c0c2d0300003c0484ca0580740410403074602d01c0a0b0208018640e84032804605d24161000802c004030342c01a002c100c074242840c3d0340765001e00c080c0c031043c440c050f1a500c030b80c01d00e460010540d5210508840d2251a4180310b010500506a016200500c803803a080412080042c072244007004600a550340c950b806d6229001aa91020b06008141e409c810700e002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 997885476 1250 997884226 997884253
    0x30b07111b0a0806090a23030f0c01020715060f05120d081e0712061e090c0e03062511150c12090106140d021e0607050a0f1a0702 57
    0x301c4190441002d80b004001907503070a882d9062407001d41e084005c607000b00000314203000004040c5c002d0401075a400521700e800d403402041e0350307101b904266a400d5030041403c4000160179815100e8070b0b07411000414820b1400e16210005221700d000c0c49046140840c0c0114082c00e010300004a00c481e6040186243c1c20002c5050f02d440c28003c01001c3c0b0340418015448036012681c031990701541441e11340407014a03c08903448140c451a401580035010440d1404d100c40e101d50420030116440204009410000240c040300d0f4008032420080c3c061281c1e0040c410181c003001840b00b080f0585480d8100e07007154184080f11240206030411070f2139405141480840042081241d030801c2442e20217600e42a4100a031009031481100e802d0300696603103d0401400800b80d00c58400c0074000c80b01d4040300005940042d01c9400c0c40d40c02d01200f11480409602d003a1101004c0740c100c40d03000001c445001206190006a07403249103000c8913081103203620403500c0e100030344030940165026000352101900008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 997886726 1250 997885476 997885513
    0x60e030a090b0904330509161119050303010e010902090604091a0d0302010e0d091d060a080a0b071403010f030f1b06020f07290703020c0303040f030b0711 68
    0x4005503030042d07582041040510000503a0a6048403c5120304000e041c0d401c02d00810b0000369000a005101f83c00c1009040c8480c1f03100c40e01c1d034003000e04101d071101201c941c02600d1321005080000c071203203168130712005001c00040654100c4904020b03030500c607a00d91071a48140d020709400e04e40c01c403c051009102030100e580050785510001c001d0300b4500c10b280000038120314070561050300540d65413446400e40c5042406a03410400741820414155442e20440c05074012207042a00c00660740c14010a80ca0390326511003400816850081712202e000e04d0a210400f40016035244010803105202104901400030640c0e040300c402d0f49005107000e2564946000c1035060080417034013080d000394041384012000b0500806080582d0040003100e0a00079628541070a981000b14541c001c1814402c000701103490000140c41101d6880d511344003249000da1038030242d41c00c030039858040070038081145100c44d95004110307401100c00f00143c1d07c0d412000d507503141c5901340048613500903540e940d40300b43c1100d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 997887976 1250 997886726 997886737
    0x50a02100c06062c13020901090504030e090402030d0c02060d050108160f06080112080c07060e040b041503080c0a1509031403040f022b051506180609040c05061303060e030a090b 78
    0x7544005c0800d40c0560001d00342050981000d03643e42c0d5640140f105060340302d0070450798004180e80c44103060805400080c0e4a00300d0724001d034104040c12015000310344400c0159816003c1600050000756100c91100340c844801800da6009000305040004410302503906400072100e0700e8980040c00d03400c1034250182c80c21301d06002d0ba8844c0e0204418052101d0400400005003025614214ae0384562030411098480c040345503481141000380c840d01525039900040112544031203410707992860300d4a200d042c0b0081e03200182201400e2842c203030451065400100005119680c0c00044d17280c0f0304698820750000b80d0b0098150380031107640d040142041c2c180c440c41c0180c51030000d40c103c0c0ba50384102001820b10302048440350044040509040d0400b2181d0f0b0300160b044449100c211241401c4200d0410010b000d2442030b4100c0004c1410b00c0511641d80d00070300750150400741d5684824000385810900c0b4170048130180e18005c3c50804c028004030540c2c01c7e008440da10105928a01400300d6110b4000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 997889226 1250 997887976 997887991
    0x30c2b110304170f0702030f0d08010f080c09040302160e0f0106050a0503160e03120714060103020d0f020d0b070c02090f01080a150b030a2001020c06070b04050a02100c06062c 77
    0x70170801015039801c02800030900c02c06001012048100c2200411104041e4041c83c085035404006121a000100b039090301c003a0706aa1030402c2c0d5451781001c925100c4001c03180303060710003101c0011071003021040d0814460100321012041c1c1c0c0c0d82e1184104c3d0340e07100c0c010030000001d800f8008140880005003020b140000e041c40c0c652443c0819000090a154901c2401d020040307001803044200880d5450401043e6a03e0b13020b44180d6145801050070020300c500004c00220620459200719a82c9070180e40c5543e401240e840c1551400500180007900d007210160b10a864850025840000c48503945042c0e0307400320041c060501d5203a50700703a0300072103140703114079225102c000300c0035207403001c120803800d4500840484114007955490a0441000d085e0070b54115085804034004075280c64044841444c0d010078403002c990b0303490034814101b11800100961000d6007410202038541e115010705002e501035202008000e561351050710030f41d07000300302c007034a0300351106075000804030b0380c40c105a4402e11 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 997890476 1250 997889226 997889257
    0x90f051b06042c09150109020f0301150c05011d0c030601081207080c0d2c060a08041506090e0118020916020709021c060509130602030c2b11030417 65
    0x862010900e00074608030741e0104c05034803000706220314010302c201d154010000c1032001c615203203400342000c0e0584814090701700c000c3c3c03d503048000c100340724041c1c80092a401100070003034a1055280d02c4a400000030007040c0e03a219080c00300e005454041480b5040701c10080051200c1c0c042c42518400d40d801420341517446040601004c800d4039402e20020100705041c1c3c0c1c46e20032585000141220b0000001c58a101e05113500300b80c440d09440b958200d0340b86d01142d0a007408141e82c4c030301e010b6001810b124044041c10b400e000f800190121242c1107000e24496002c028840018541c4d50a943d1003440e0318082d42c0f00c440741d00800c00c88804000103220051517881502d42d5a61100303010030599000200001014003104007003034400d0304d503204030b40150000b200c0529030703814040108804044052005840654000041101c0e40d05c08012110b0180141502030b0344114a8103ca400310412150f81d264205d00700604004004400000c880c8030359405076a032030300c03c014451802141e420641143d4030b0342c40c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 997891726 1250 997890476 997890539
    0xb03010b0a080a05210a050912010f06030b180319030e0601080f0d050c1b04021309020706060b030601121802061c14010602032b090f051b0604 63
    0x3164007540e2000303044104014403008080b403078600d00c0d15005194001e507543e8890074a0070406070040403100310705024a0095101c00d00240010510300c0c0a4542e8031880d0701e0035000d508445d002c2c1d00b10346c007103c0c0181200c0340240c0d140381060385030710401c020412a42d001084040754004107070540c03c0010903d494002204c03880407000f40c0c501340d001e8020307851302d90289820703030013481007003141c41401c04080c5000341c28108000c40b059170301c584a41c200d107083c1121078200d80b81d03078807594103850340398140310301d0720440643c4ca2024100940c40b02c082986c4940c1881004a45d001900e0101c901408060b510094103855025815008004103c0039200c585050181100540d0b03c007030280071101c901e000003940c400810f00c002c00403110380f1490700f0003114a0b1401000a10307004400c3e1100b2150642c403086290350304c2007107070b045641d083c3c0145504928182c0020144081264003101d0984110700b1540d444885488010900c0c4250000c141d02500401041c40140c0202622034081c0f0032103c110700004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 997892976 1250 997891726 997891729
    0x1002030a093005040620010e01051003020f0f010e09041505010311010315031112030f03010f031a012417040b060a0b0c0303010902131809020a060813060b03010b 71
    0x2551007a14007142290300203680410105a400c509016140b941812440e00b440e04502604407507403000261000c0c0000f09044110610070741081086421110080115141801d00c00e449814940000d0b4007030070601c1c4401c00542407280c84000700600503190301e51150b001804018a007500100200d0b0451280345c4807070712039031090203041c0c041c51055102c0e0030101a01030004003260700c9034000c140c8101c840b140420210310071500079014103406039240810081d031140000d143d8410301801c01c00d0780b44000700008403484c0203182c1005036440382d980c03200454605407a0180480c800e0184804501c0c1c502250004003101000300400e86610382482c003800d9540c13079085440e040301181c003075440040300c0c2c0c100119807a00f801804042c0454074105801c0000403030000d0fa4071b020500400c8401940088d03008003d02100109a004107040b10b050088500300032007a00c0500140841203020f000780c0b0b02e000c54940c4c0a0500140b05d0900981000042c040310384500e0082d0034071143d0345030503550301c0000070804e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 997894226 1250 997892976 997892993
    0x51504030c050a05060601110c09070e03210910020d0f03150b0a03050405160b030a02070501140106170703180201030b01090504140105031b0108011e052106010b0406021002030a09 79
    0x181c0340104c0c00b80c00e041c90000b0001d404004108940c0c41d440d0407031102d10020b6550810510b8000e500c0c0d00d0602000074070000824039006007001140c110040d1a0b407480d2004001074000d004100b401d45440301e6108007164140d0381c42d000c3c0044d00e004100d111403044034180c8203500c484001e41200304114600c40c1e452040c40e510707070301c6241240002a211420041401810040900a8104003072024951031401c1944a0300380405000d0701c041c940c00081300010300000f50424001c000d0a228450b06079655824050913910000c1030038001900300c580040c20703042c042e1044500560840440080c2c010785540110000c00b4501c5450741403000a400c04902600e49102d0950050105152851594182420149030880403036030030388081e4140c0013800c4581d0380300488504480c44020700c15080d158001a83c201091250025500201c605400040741c0312000034030391040010905507419643c0310710b0301c02c50a1081d0700540015034000079600e200240d081c3e0040da03008082d0000051140c040c0d64613602c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 997895476 1250 997894226 997894243
    0x17070f03120513170c010e031b0a031e12031e020d1e02070b0c1303170c0115050111060709181803030c02160f0e060d1208070e0d051504030c05 63
    0x3c14030711001180380d03000c000300205c41c18a1000d0030580d482c0101c44000a50320310b151018000002d0322075800c5845078403440038003406135030702c01d090806080e140c1302e810151030641d260607200214003502d80e203281400ba104840860411484030000d1400c50b00d41c070702c003030f40c040100c0001e00b0b0303991103460140c2e160502d5003280d0310b204000b0241c0e8500190402115103040030345100005041000345400c001e1201403540100c03a0b0100d40c0840345100042c1021030b5005110051030b00b542130030440e1001c0546518100c1c1956826281c0148a60310308183c91b030758000c00ca86200110714003150501202d140010f922a50b505016008256404e029100c040741400b5210114013080e110321940c01560b4060222403a9a160130040c00e076080c4c609040c1034007003080e500c9880d10614680020030030b20784500c0e031001107a50b00400041d042180b014801055414122070540009440e21001512803a004e0703103c07000300e0b8014000749291402c0c80000c4125140280044082c081e40d202c004000400c02d0203c10f1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 997896726 1250 997895476 997895489
    0x308030702100c2624151c110304240e0304150314090d0507060b060705060601110c0306011406071416050418030c0303110f0417070f03120513 63
    0x11080204144001d42a8003540c0c030248035110100803c4030302c0030911715a80740071795110103c03141014aa8003281415aa40e000360001d042d00250140d07161500020000410301c016408204d1030402e01000800341c00700342e90013041c0c080384034283c940150321310301100c540300e5080000050301c0b074180481e0351451344a944107107002c1054080c1203c2e1107426104800300d00700c071841001d0040c0340c80382d11103813981455030006050180110b1000c00780f041540c411000c00e0b001521741d69840706181812903581200f11901750000d034802c1d000c0e03200b00d003002c0b0750001c41c134202500805103a400c0c01680f01152800300030041c2c05c203101b4040707540814405410205090743c217101401807000391403c0c001d07079030141c4e82007540520304010032480f42c4041210b04c0a00340b81c05107401d40312600e9a140032005064020b0044004100214640d10202e0141008004840f040c003104108015980c5078980c80f0b074190310400c000c2d012164410000304004003540b00603801246070091400d2400c0c00b03000070281d09508000f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 997897976 1250 997896726 997896737
    0x31e161101020415030b090f0106050403083916120204091a0408040311030a0c062102040603022104051c02010b0a0906080d14040b0702010e0909030a08010b03010b040308030702100c 80
    0x42c03010b070030707e100c2c0d103a008010b02c2540c900035814080c014142d841644002000c100c0009515290490700d4461080c228501a00c1500982c18581c0030752002210030030b94035041d000340410307480680316019400007211110924451519001c1c0c0030000203103904441601c95421120000c45410b141100403882144200482d82d2590f0a5083c081c001d280218003650091f8003201a65011610000f801e500319000b92500090104e9807598043d42c00c8050000c510001d0700103c2c01064a64068019281d0b00070b040c400e0001d0003030b8041204c04401e00a40c1c02600a400074031000c02c003400d1024184880320720500011880c40d5401c130200304544016448400d02075a10002401010001d10000d0142c006a02d05100482810072140115100d54410b0441e007440000e82403003103900400c03040920100084c0845854a042e440068403640041e65140000700c890001142a0b2052001d4034169500600359a041a00310341d6a500103600107860801580300f6080700d10001c00c0d00f0302520301f6a114a50b00d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 997899226 1250 997897976 997897991
    0x3010207121e0302041a03090c19090b03190308100b2701030203060108070810091109090705130e06041803020d0e030a2d080c03031e16110102041503 66
    0xc00d41d8802c040c41061040500400c0100035241c90422456035041864440e580e613074441c113003011710303001c0310903074442e0404c200003801040c0c10880c0d018842142c1d502c1d0b4042c4401100c440405443c1c5455002c140c1e03458450301d10000110b032095003000c1d804141d5441200307203903032100c19000c2141c0211801041191005010f02a614006020b840c1001028282503055040150028084200060894082101c01f8001a60074140c0e1640700009084e50707030701004040042500014158071001c0c030306000d049003002040a0038461070444c0c1620002d00d005d12481401c000000c000c1c1500a00442d600ca919541c05000e0a0064081d0104491190300103010203060b40c040a40500401d80a1510030b0300710001010108685a0001c142c603040110f03115000402e50014100da4107000f040035006110104140041d684000b0041d03000340c0d0450031426040c20070306041c82c0c81840842c0c0d136100e8101c1038012101e181c3d010307860b20301c4034040e00000941030503103c941c040c0c140751350100d050340026205d561 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 997900476 1250 997899226 997899257
    0x30605090a1a0604080c011e1b0303182906150f0403080c0d1706060a03050a0e030a02060f0a1a0904020a030b1014040c050403030f020a0c060504081e1b0301020712 72
    0x164940315940d0001040c1704a1801803014054004a866090b60381e5112027800080510a030300c0914030400202c12040c1d4890f450030b05581450480003200c4a90700c80d09280700d900340418120307600c035245c014524481710320b403500060502d411421a4a114200c03c0c0001300002c0ea0040142c000c105091009040c000c081c0600103000c0e00c0311080c0f5511981c020000e108068860320100e0711400c1c01d40c200400c19494140ca802d000f4107080042010601012426100043e40814901c0c0190601e08110140d601c0b92401c3c1d4003220059040060080144040400035082261040394010300007070250101d00d58a449080c607022084449581001d0007010a105035024074054000482003a50104201c20035008054001c1c800c900010741880107080150f41200c0c42001820002d552000714a801a80e844202402d03541050048100c94004e20741c0d8910301d109108000c80c110580782006100c8860300c0b050510407810042441d50300b5540030020100400c111182c0100c800c5440c0e03543d940e62044465 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 997901726 1250 997900476 997900487
    0x210050c01200d11090d08040f0b0f030604110c01090b1801090b06310504060f0b09060616051504020f31140f1006030605090a1a0604080c01 62
    0x80308020501c000342110502c254440503a407658160300c50006090321040744101003406084032a41d40003410b03190582c1004012400380c401c840d50384042d190156118003912200d8014081784440654087c800581203192541240e0207210041d982d0f01d1a002010600b20f0035904881410f0702c03010407100c180b15111035207000d241c4010340b060300200122545a9201a070307600014002c68419411302c41480d08100a141290410b0001d12902c91524401100700c1c00280a04480544866290500c030f594841410300401059560080030300015540c6c070020451150811100940501c804418100c0044d6042103c800100d15000001e0341070f140a204102d40c3c186840583c0740203030440002403604001918840781d040004582c801e0502608901c2c43c002411800301c2018036915400a00101da9621100f044c0907515404003480030b0780d250b407020760503601d191140b543c03c180c0b0200007030305013040c40e403060b4a450111408601c0484920700020700940098019144980200503543c0642d038018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 997902976 1250 997901726 997901741
    0xc0706080903070804140307080d03050702010f0e0a0f060e1b15040b190314150405010b0c0a0609023f010c0c030507020103060503010f0614120613030c0210050c01 72
    0x720020352405501d0382c0c9040003030107180703e898206186c5c0c15841c942a501802110080c1600104864603903c881c074004010705429200e80025500c1e0113400c40c5d00300301c01d0107845190f14a01c0d009000c2d5071040e540d1015541c8603080240c405c00d554065101d40c504050043d800d00086c05a503100143d4184010441d04040140328800c5042c001c1104200e881d4800c419104c405105126905180395a510194041c20420741c420014285080c2005650b406800d00b40e0070040c02511300304030380d07a2035202e0005144140302c1071181541c00104141e000450a4206003038035440909101030000241215a40500003040d0442d000780c0541d40d52946040c60399058178006c40e0f071100a100c400708242c03014006ea50100c40203001c10100103901000d59000750095070003440050000c002910961803000e00901c064004c0740481010b00100200178070b0300da100c14a40c0341035180139002c9900d607204404ed42c2500c40d1710841c1403200c1d040c2400c0c00360b07480300c2c508000d115a9407075144d51038100321052821502070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 997904226 1250 997902976 997902991
    0x1e21020c031201140f010f0e130501090f0b06040b18030706020c090a1a1c0c091b0203030915090a1707111c0b0703061806150203030415180203030c070608 68
    0x1e903045880b90b075031002c54000501e42030030103d89503403074010210b415122648003127401c800e403503000c00f840083c0d6502140c1203601807901049100004d085810070303910007008081c1e02c03603802d00062040409910003444403014198410741d903070004101280c144581940280c0150308401039400309420440c0b6001c2d44000584010049210084018100c4964000e6101d0013866100351418805811040e0541c10b50307040000704420a558031000d40103801201a00d104590075048030641c0c20740004141d80c007a00150015100c207031440c03000d40401d03000080080985214002804001c00c049042c00410b07841c488598030340d12180f074100b408003500000040b5003c1c41410381074604c605c03040b96140194952200041340a507c13480c2046000d421139400420350f40169801c10710410752160b004804544100f00050460b803181c0c07405a0312404112409401c0e003400c64120070501d480c03544503410031031502415252000f4640c01291654009618048660344125000e1014a800c00061030b4050007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 997905476 1250 997904226 997904249
    0xf0203010b0d0512070f0803040c0302032103011205120f0406080c180f06040510020c090a02090907030b040603080d09230c01030f06080a03051206011e21020c031201 73
    0x500d40d54a41d07455007205604940b0130300100e9900c003008030418902185d02e030031000302901c0c1c0c00c0a040c4a1201e01803484101d100f0320070542c4802c2070002c4c1030344851029060b03509070b90442c0c0c0390028500c11300d40f40100442c2c85009110512822b0741140000c0c100b005e58410056417218203082018007640806800049035150910404009407880030310000c1250301130b20fa00c1c0150460324003094040c061074100644c400d94080c9000002c0b0350008050030100011038500003d40c40383c40c560401ca02c00c07041d905420101d80000101454025004030f03d482002501c000750449e036984990707031107402a01c81069100d441c1c00000080c00440300c440120b01c0ca141101d003c5440c47e80900301d035500c0071001c00074141601c41940360340d00403059110300010303e8090700741c0ea02d054003460f0092072903002c000c40510900941c00801c149501c181240c2038007121401e602880c140c400c240684803490280059050310710b006240d2691a056400a085140f042c58010b5496940c681d041703890111050708680c41601 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 997906726 1250 997905476 997905499
    0x608010614011805100c050c0a150c05070e10030317010506030a090f0c060512090705010912320c04050f15060c1204170613080903010b0406030f0203010b 68
    0x4101d160880024000d003003e00505010910220800d4020303845181d220b0020641401481d81141403000c02c1c0c3c0c0300d401a21151400300081142500b06030003140c40d6076034462001101e0746c3c001c13041c00d02018000c0741160700042d915440c62048003000c03a03612113420248030041003019044582c1c00400080b080ca110815030510012645c24040288481042c030380742c1020b8010b01208a01300c1c01102d030010303c820000c039190000900301e5804620300c41d26200985002803042d450105106003641c0c4142e440c41e0034589040741601d040b880d1800295402d605001401000b5400c0e1007410503500c03154042c044410510f07408103414811095600c5028604040070404407141c0f000729a03074480f10240e8440c1001d4841d6021510034040c0102e84000c6101e41d0300d05000244600307018000701c6070040509d150f0350406c1c00d625511448180c41d8017000c0b100e80000720000615402c0504a10709028000141c00c0003404001019501c0d031358015110084404000030a5007003c2c0126481c80b031702a141c5c071a011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 997907976 1250 997906726 997906739
    0x1b17251110230307050904050a1a09010e0601030507030605040e060f07020f03030c070302070308040b0d050c0412150b1305010810020a05040b03100b041d062215030602041806080106 80
    0xb1500468640710300c00000043c0003103000d8021b40f8041c0324080c0041140749042e2a06000401e4135044803000312034428000e801d02d1400003459816a44446490100b80d21868015400b44c20090950350030f06032075040201d05a1240c0c840d440720703200090010402414010705c96006000087c06250031074100c4500110a00800801c40c3d8000c5204140389a031094941402c03801c00510750001017010300c1c000ba00050b0724215030040c00c10130809050400541d02c0e820300e00c082c144207030b1080303640307510000e002200403840c61262101446582d581c0400c1c0124410002500f151403404e2051520365a0001030110350400c00140d00000b200301d5085150451540025040380114403480a402000000048203881850443c1000b44032009216444548a0030030f500c440001080e40081507045000003075a41c81c113080700f50014805000d03480380192080e500500500b81a88a41540040c4040300000140591009100170007001907000d045a4800103014140d0b04150301100c0325a04140d01070103030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 997909226 1250 997907976 997908017
    0xa030e010204061719020412050f0d082d09010c080907050a15090504020d0606180e130f0f1a0c0702031506030a02100306061b17251110 60
    0x1c42c00c914441c1c1c09681d134031183c8200070680c0040107032841c001f050005400c120045130511492160082e5218180380a940940d2201d80280040004404002103040210f01c240150348000400840d00308140640004880d1040c0c283c90910f4203070354a20001c01c3d09507003d81c095420040b040b014110241c86c02e8002100354640780079143d18681c210740c40c0c42c011405110001c1c000e102c0540295100c207004644140102440e10440c1c0204001d0b00321000070188048050055403452980080c00381c640d0400d948461040c00030071a83c151600a240d40840e2403114a2192148242d030082c102a0319548113028801e0043d140d10803e54040c4051401a43c0c00b04240300071415110900c41c0d00d0791038100003807501e40c8942002e5008143c3c6c416100c0c006506030045000e64001d0703200c0f000c4085000c940c010307080011501c050a401e42580f0600f188400d03400c001c02d8001c411080448440c81080b1281392281c4401500301d0350403804035079a403500d00707105a0b2244000301c50b041900c4aa400d0079542d240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 997910476 1250 997909226 997909247
    0x1d040b060901030b030307051519020903060c22091b020706021903030b0d030906030510030807060203060102070321080117061503071502010501080609010e15040c05040c050a030e01020406 83
    0x40c103441307920700c00070307518104150b0344840c3e00b003c1290b0000943c1008007803e0303101035403a030307405020103001c21300916014000c441d82100040c0c003d040d0780e07455041d404840d402000c4400303103001c20300b460354945002084d0301001401010760001060040a8507443d00340116600060640d0042401006190340105918201508440c040c190a410707a24003140101400c004066101d000040e10b8014140e220203900d05840345a101006a0384400100700d145d5a000c0c8002000c403036042103c0e10000780c081d0007458000b034041c0111000780f42c503a562001c80203541c0e215801360000c0300000344012030340321130b00500400c10003850348150054180607039180c22000340310340d0680190403a51000380e1070821050004094110b52482c4c280104280280078001c28414551a845914045140c40206206640103d00204000c03c0b10101c1b0790a04058144010300545d01e207000c4c0d80c0001000e886901590760000e41542d02d03242e441800c1c00e0040c08030b44c40310342146410ba00c1400103020341c58000c0000781 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 997911726 1250 997910476 997910479
    0x60501030c02122a030a0e03010e0c1e06030702160909030c1101020708010c030c02061e2802040905090d08060f060d0902030a0b071202181e040c1d040b0609 69
    0x50b03441c41c0d503503a41303801c40491a221000f03000c4061039240410001102510786181d03a65112040c5c0c9141070101402d030340a2030b5803107050b6001100c04c002941742a00c0302e00c10800040d90000d0382040514001505604100c6649016030002c0f4005042148080c06007405030070298030400031184030b07440040100c1c483c64001008221104400ca02c141e0080015000500004000780a80380203210b0080260064140381e102500c035410120b000d038002030440c070301e0913401404e4022143e80d80c6800b030500070300b02d00256145a02c2c070700c0b207403101d6103d140014006442c0414010505040c01c6c1a002d203803003064084a000c0050001c02e210150713803480c4100310490411245c031038a0740190300b0b1240c020000064001d50611840207540d00f04003103c080c5a109002c140c540b208a80ca079031040318164890002c00e0032400c02c514844410b58600214070a8141c41d080c003100314002904404241203444c8800381c40b02140840c0746030441c0c03650303c840030000130f00252014031100700b1110215046000f81059207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 997912976 1250 997911726 997911763
    0x1501050111210703110105010b090301391403040501020a1d0d200405100303020601080d050702012a0302060a0f0207082a0618060a090b060d0222050109060501030c02 73
    0x7542811704c14814011214202c400820140d40d44000c185c26a0344a0348050703001e942040890b03600c1410049405500d80344c28042d4032406880c0380056011020205208401e001103155248a0041894090340c0b00c9d0348114001030f907506540d94090503003d182501d1880420486d00c10900c1c81e12108000c01081d98071191036007c0c0320354003400104422030702d26100d400034039250400601403071580b4604101c0f4080d80a4920607621403512586030080c1241d00c0010500400c031440055100740c0c24151100750300d0300c0d80081801ca40e000b0b144d00280c1c8407c00d4005a20400900a0080329445181c0d452241200c1c01c61401d90250f9410000380140c00110140300580c244403c02e101d00007900221501000741512007c1c0707082140c000303000d03c44046410491161100043c9014024441c40440c01c0e003185841640c0c2c0d840c0c108000d844507030014201d801010b0848114030001000d91014a581020a80450f0a606000041080340ca407540064105401c254440318000d402050002201c04000d00700c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 997914226 1250 997912976 997912987
    0xa0f1d0c0c0a05100605010207290f031627060302281101060e04080d0c1e0f02060a09110603040c03021c03030e0606130c0908150105011121 62
    0x148500e50103403004a80741c80c01680940402c01401003020308400c022001c040041c3c640356001242d441510340100030002c1100f00e100c00c14058100c10251a2045808207641b4001ca034800800f2541c0050b103003c0c061021072201c0700a4190440364002c5054451002c04c0c10034120080000c0c4103030310030b04c1040249940003c00310b9040070119002c81130811901a0a5030300c0405170001000c05000c0e81000196500c0e00310086001c07958800300034055078000105134181801204e03140c000301480c88000c1c0a0006881c0c0c0c074141c050000c240c0c508407481d50340703549440f02c214000282c1880c0005100d03c66a40c0b42c418004001160489602e604882c1a100c55072207641b00c0c902554400c00c40d80000e035000c0300000d64100322440305081480c146101e56030501a80d0301452500380e44610a0701d080398880c0300348444c08122111540010b00300c581500e00880c98968401d00e0604064001c0f414082e000a40030041c801542c20841d134141445550300140b2452034a030343c52004280324031008007502e0340c00141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 997915476 1250 997914226 997914241
    0x31e1e080906090d02120a14030403030c080f0d0504111e061801051e0301091a010f03050c070b0c0a030e21031009020a080a0b0a2d0e150a0f1d 63
    0x3c4c5200041d6010300f40c1030040080d503412695840c401c200486000e8680001c0d510b105070040156401c83c1c0d0726031504400180f807507540101d9500a5400304500a9090000801d81d940b54003455004501400060203640070036403e0007d41c0b55000142c1c034510384041d02505071030301c800023220036000e400e5134028011070300c4400480e80781c030404204503c8460f80301c22080a1924081c01181218924101009507440310280200386903482090180810450303403901021320300030b420595012100d403d2491905030039540e01d40040700144c5004601e0308000c25010181ea805101d1592030107503c1c80100780c407241203201c50007020804089501c2548004c40441d60034910110a90302502c0588401d644483c0e0182000380f8a0508892a419150030301e0301d04600c50031320100010654103000c103540100050350034140c500804100001c4da40c448aa40c001032a24031800155001743c2d5404400001c2c0c1a452041007584081c54004018145044c01c08108810465540700040c803500f881091181e9030740c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 997916726 1250 997915476 997915489
    0xd06050a0e030d06050108010e270c13061a0708041202040b0d0b16081e09030f0f0414060405091501030902030706180e07020a1b031e1e08090609 64
    0x2a80c007012480b011500030107004054001000b0303a40280c0e01d604440e0f0303840b00c00b40c0340000e041e660780a00e0904002c0f1503408256051520503036806900490303161280c540041000000c0c03002410302c0d603d0340c0d4203003402480800040b01c2d9800210318161414200f00f03441da4040d42c03140e48920a1048440301d80c0c1005c54039540c2000300940c100600c0d003c1c0c0c40340300d130900c0030410038102c500400b2100700e0740810000c0b50103400701c1c0d40120038076035465564070440381003950307103100c082c0c0300c42c55030b10080c407920700f9a180800051000720b0611161544907881c11000032010301e50310720310b035100b4031060109014070303111800c801d0b0b4841c1d1100c00e101919160200142d0050401d10800794247c06224030110b00d558220b00c0b651640c06a03008034052645c0e0b2940965444d40d0b0036540000140c0000c100c14011441c10100e003030748444008020200c81c0c2c9d4030369903d400e000580445005c0a0007200c1003e040c40800c00031440000b06001c1100f125050f10341c1c41e034a00344200850705108081c0030030030161945441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 997917976 1250 997916726 997916741
    0x21b01090b03041e0f05010b180117071205070e0115020a02040902040f0e060610080906010b220807090e0303090c1509120a020a08120a03021b0604031107140d06050a 73
    0x40191040d11820f605218045c072140803425549582054003e181e00e08200c0307540640c41549404114a69091900c100c1c8a560041003c00c0745d4815982e0116040d1601800008803030b20890042031000c2c84c124082c0e070f40e568160310035543c00c654100b1020425402080030310f411030341118000344800d003d2000400074a44400344054007481c000d0508080440062400d0040c00c00f00c0d0140351049501a08580c80b0300119850b01035500300c000100644e51000000d4081c401d00543c035004002c6007a0f01040895255500089081e80010020003441210384281c0d245061200301661030340c64a425916581c100f40d1088500608400440b080413580c204142c540b005401800c040c100400c1080403607031420311040c10303403107a401000001a2a00700141c00e42407807007040c1d45e007812f2011039070f020b9009402c00b5099a03069a80d02000c024503c100703004441c4210700c281c44141e400c0300d00c1001945031044903001002c461000140444090ba2005002d404450740414049615583c1c4800c91000c1e0011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 997919226 1250 997917976 997918013
    0x40b0a080c2503020c190e06030123040b0105010f0e0f1c0308180c01140c01060e07020a0c0f08031c02040b0a0503010915210f0c15021b01090b0304 65
    0xe41840c02c800c000a01d48820706010303900302c900c0e03803000c10100440d40c95a80e000c1840c40c1c080c03242c00c0000d02c040d10f0710147e00030030050000030f001d5a10001142881d80078618206428030490400c000c1049035280e02c2e001d400213190031215510b01c0c400280c000d40c2d8000d02c2c1440342030044002000d81d0b0312540c104e06258030040310790040802515000e00411030584400a003099416011035107040000350740e00e4140e40503501d081c4080c6524407003d20542c400413502c4540d5413542800f00d010809031000e1809140c60740d008000302c2c0e5a505040301010029040f000c0c000107554002c00c0b509400009550100e04000558030004910018000003445194889001881d01142111a043d0040041e50407940006410b00141c0c43d00ea800e88041c1d1000d01800c00c464181c0c10102e038071031000081d1400d1742840303010b0100701065a81c8800c582030480d80e002c000035030307540c83c41c684445505202211461701e021600301010b80b03400740043c10304100c60085511a00010000400384003068242040844c42c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 997920476 1250 997919226 997919257
    0x1051003062d02040603060527250921020f1c12050408150603070b070510110a020d08060f09090316151b09140102010905030f03041106040b0a080c 65
    0x80b09000600a5006407141601107450b024000846081c52440301d46c02e244040703034240017803c20443d250a40040035100d861410301010400c2c284c1e00306580e0500c000c0029031141440103240401082e00b09441c640c9644000e50f9000403a00103072141000301c0d0582c0403c54007541c101c9050410300003a040b5005020305003100840c2d20400c090380000083c026103120209484610300300b004108245401550440c0c2c246d44041310411802c0034103005446030358032450541d8006880c03020920165840c2e54203124414500080c1f81c1040d980400c1130703080618a03418a206103180c90000035101101050b111030040c1c0c0400001000c9440c203004941000c501fa0880f003810322050308041004100d42d00c030b0001141d00c0c00c0000074a1300075081e0f181c0500d40740d540c0c5560b80e60b402c1840484031a0145a0954150b42d2074113580310014a041c0007800d2681a04060240c580c034140c14410514840c100155004000400043c4a40200d113011034901d4211810300c1d01c8261240d8401c40614490000403444088 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 997921726 1250 997920476 997920551
    0x4030f1206031b05030703080315040f15090b0f0a0e04140601060f080f0c0a0c08090319020a05010507052a0907032415080603030904020f0a0906020105100306 70
    0x20f0540300000c8001e80781c02c4542a1344507824181d440c501c41c00080c0035110309200040311080e21501c560300f6003901503c0420003040c2c042c4e00314203903103451034100110a500d00c01800b035a1030078800c04000440c1160141c41e4244000302064400c030f0a4000d002c2070041540000b001c1c0151140b160348424a8001200c0503503a644400400070300100f20500001141d074000f241c0d4600c01c2e9034885004183c4800b4007441d21891440c19544103841d60400c44001505204c492401d6400340942550054824140300c0444083d10410420344210781103d070620000303001e450041900042c80001c10115400c901c0494281410040e04c030b04030304200c40c6c5e4405c0c807071010091007a034181c0040050302d14002407144003510019a0800d512464090031a0f001d0300d040311070b280d040c807801040d504480c0c09000e40345000303003a03000309080e64015124808a0f401c00948030303001552200b2400300500c020720003005141006003c41440109a20016007402d0f1650380c852008072511000d1003264203d00c0700b500c2c810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 997922976 1250 997921726 997921733
    0x61b1b06020607030c09060e2707020d0e09010b0427022b0b030303070311040f0602030a08090705060405090720160e100902130324050114030604030f120603 69
    0x86404039400f0002908000d4600c0c0780d54010701d101c0b401e0f50300c01d459032070002c0140002e110703007254040502400c1d9400841100c0c41c076401007914030b02560003503000c3c211025180b10040c0031081e481d120070b409070a0090040240c980d40304141c400756490a82992041c0d1800707807201030890030300c03000098090706c0010015a500907580f08951800160404a0030000c0e5004400c01103a0380b40100c0794050700200300181c0341c20321a502c20308010242000080c241603c07078891044d2201c80381c00020140e840020761404040d00214459807002c0102e00620440d41000e010484030b0007a032040790b01465520b40030502035401800c05d2000182009105280300e108980c6156942071011002024881403d030085903140381040030a206481c03020b00a210280b501d20103070002e601c46000010380daa201d21010002a0301c865842404542c405805096a6800c83c40c503c02c88506038001003400e44203030701c245100d1f20041050b5074415014201000c038640f91100655280c040608808000c0381f80500c08401c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 997924226 1250 997922976 997922983
    0x1130030915011707060f0917030d05010e160309080705060f1005030c0904150605090708040c0f12111912060b0d021f020a0f03030f0f06061b1b0602 65
    0x400d100d54021a074a036a00d1440b4034040702c1001d91031200d42c00050003400600d01552083c04002c4c0c03145040300d81580e0302e41910450403a64804240d654000160240308200c5901840340980024800046030381000000700d0b001141007a1040281511503008000740714194080d10b40040d003100a4075114a80b48400b901c04250481d42450700d9100c01c00301162070f04000649001e00307000a0414142c5842c3c5880300d101200051215980207070b10307124003207500d81350b161445024202d261641c0c58a402c1525143d203c44d03010343c100c084882c1c3c5060082060281800d4424940742d00281400682048540455105c8459100305003000065440c0000c00304104641504154020340c0300700400c8030306408100e80305180460295000119005034203030211500c0224101c40c4e00c9004445d01101242c2e00c08840580d0242c0c180c0110f6916681300c031220071180199a00c910003007404206103410300c1130180400b50034100100158007284404002c010215408811410707109091408059851000954 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 997925476 1250 997924226 997924243
    0x1e03020c07060212090118030501090f120f080c2a0c030f0114180109050d0809060f24042a1205130807020301090c090c0f11300309 58
    0x1072090500c0050518400304520720b100701d402950b81d00e000c0486004603a07070380115800c030482e40f040000000000c0e100b486650b00304e910803a030352220b020460810482c80c5540355505410b20a917807a03807100e00303503000c840305a211180266a64403902d0081d6012551001a00074682000c0441405541c080300000e0f451304610003241221803031078a4452040c01d0b1070807287d100b2010000680450b4040d40501c14082c00f00301418000907941059448081c501002051080c000c1014407041c843d80180c00c0c00441e034402c11030001d0819038101040c01c49580120301c0b4010343c5994068410841e699665080700d6080d0703952f1844404980c6407225000301c0c030312040b508400400e4108001c003660040030300a4603c214550305542c00c180915486200055100150481e455560384440200003100c42c0005009401c491000042100c40584003514082017400e54500b4403000c0c038480b80c454035000071007a5003003142c1e003800990030071500100e00f60007680c0040000300000100811006040c00503082c030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 997926726 1250 997925476 997925497
    0xc050615190e040807140a0308010302130e060402010509030f06090d020c0a03031d06070204090605090c0103141f03050a14060114030604030309030509060406051c1b0e011e0302 78
    0x900c039405501045140307182a10806503950310107400240442e66041c050072000303000341c2040240401c000301c0315041000b0b031003003100415903050050003135081009010082004220f4100160715900e03007000c0d9190401840241008400900400c06440502106085007480310807200d00d4184072210584034103100c82c600e4014071aa46a101c2c0c2c5103803500080301202d07050784440c002582c112802c4e01c0b040102d16180e80d003203002040a000161501e06c61200403078011100000d943c18024a400c2c1080342e1860303c1d0b4101420001041000116000c038a5041781816802c12423242c0c070341c0006014691698000340940c0520103040060180600440710480c030500244d4180ea80c9a0405181002c00303a50302e103426038899000200006d00a600901e409400707410103608000d0000d0025002c1d0b03020b508031400085010840148000c5921030004100c20b01000503c00c00c4041030742030004964455908040086a030060b0300241d01580e41480d0050310388016008201c0385010190282d8044036204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 997927976 1250 997926726 997926739
    0x609060f060604060f090512030c0709110f07020312032e0609030b42090603030a050a030b030109060e06070207030309060509060f040e0f0c0304030906050a0c050615 73
    0x810349114040014401c0700300070003481c02c0a0920404803440d91100080c1001e0080c0e504d0702040035039810001c1c02c0c880d04040c0085940380100f0f01c1440c00e15210398000e0102b80c3c1480352010207440100d050f181b00d1a00314000c1500c411080c0002031a200307800007281144c90000050200b140c80c0c001840006010640300032214110b1280514000907580c440c140c00a90781e00340034030018402c000d0094014260360562194462410b014900c00e031038040300070b002841e541c1150315141c0d403540030300e04c0921030403511842c5601d03050303020903183e1141c140c2500811000060441c50fa90099005110034030020b8003c02c0416501e1030040010075040820400700e01c2080001907a0a20000da007405a070340c55940e02c5503440c9400e2055405070001c0070200ea000100348000425601030340081c000400900310308413100d08000a01002180c4058190034188408004000100c2e0300480e004c0c1c102c0c0d5030f600c0e10035541d0038500c41c220354074005068003d100d4000c1005214007854421800b061202c41115407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 997929226 1250 997927976 997927981
    0x11e0305010509130302100c1827060518041a0408031503030a1710030f0b0105100f09120c0806070903060c03020a020a120302070804090213050402040b07230f060906 73
    0x804584c00c007500014010390020b201c12009103920f802154a44205081804c500011540852580f0345180c0149811510281008003c036000211541011580d920200000b07814000829004007503012202c42114007000481e0400c01900010303405900740303001e441d07c0d5051914041c0070b503610a684a202e0f243d008034401c9180e242c08400c03980c101c211501c0c7c8101c00c0340949100c0c0803001c801000075040c00005400000451400030340700140d6803140d010b02d81558109000c119044051b00e0181d07007040385044105109603001140c60b820b807000711803616100c0d04549091042e409681d0400f50250017408103202225400000300c10540c3d02c00c031018004082a02c00c100c00701c4c026044e02400582c030048001010502a4034003100540ca540b40251408045440d54001f0360b005510400c0700550000b00007a40001d140301007000b900040307806512345481c08081c01c2d00b501410300003030181c021040e1991826a00006008000c80604040c0c40520011074204d540f202c0d400ca85d80080e5000e00c500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 997930476 1250 997929226 997929241
    0x3513060c050414040906110c070801061406031801020f0406030f0605091005120f0d0801030b160f050c1005090304050415030305030c131223010c0f030b011e0305010509 74
    0x540d020740301003c1003d4040ba014000b00009012440003e5420f265140200440762000500403c0921420030040045030f18002085085030301d1070380141105000c401413140c2954514040f65004a1105a60b2600007007008469009200c0c034004155004c2c4c00040004100b0741680108000003d08013003008925a100107210f11032000f00c640a61000b4510401d00c40d603e0100b0b02107180000d10b80482c2d644662010f20700740750400311414100825580e0004004211400e40303443d9111002241d4580d402d00e02c0000680100140d101c050188500407034020480e070b03c2000320f81d00e8200030303203000c1c4101d04003000310945a81c080d0040600aa0510b81d41d5007207030181d400110200e9034181d594625560f185000d4680079080040d2950100b00101000502c2c000403030b0891040714095800c021000c5100c40d5022541c2e000c8a084d4078059041c003d0210101e03411800818002c00030742008900c0450150040301c05d011802c03821001780111122a5090507459402581607c0c1306542c20285502c4030340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 997931726 1250 997930476 997930487
    0xf070201060b0a180f0902030108070603020a0203030112050f0109030e04061226040e0403030b040516020a0809030f0601080a330b06070203030a0807020106153513060c 74
    0xb1900c00c41c1c0100601c01d1490710589508240303d03028a040c040194886603030406100076984001440740d008001401440c03400d1041000405190808514000240b040a1340303a0005202e8030501c501c0450103036061040a000c0303000540e007000c0081028801ca03140c040d0800c404c80100c103001d50318110340850100e00e400104004a0b0b0005030981150104500355140203080d005925580d100c1880b0000d0a1101411420b0061f8480d17200131407015080803d000440e8801440c0c12025245140710700d8200e6008150390300c00c2900001a00c3c2c1d175044030b102107894609169644042480341100000740b481010400c0080e05d8410350801244041d1014410030401c41c0851140e140b402c40901c00b200001e4a510864a008000d001d071070411300303203800207070440c0c11102c88000480c4196081100703040d42071081801500f10515480700450a913030b8010200748984840d40840c2c40e0f141c0c112649401044c1448405040c50b001040d00c52038030900b428240c0c243c0c40801c5440702e0034004207107807460150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 997932976 1250 997931726 997931729
    0x9030605090f0c0d0b0f0a060f090506151206040504140d0206190509070e0604060906140906030f03040509041109010602250506030a1802100507170304020d080706230f07020106 78
    0x10a5017000c40e183c1c10801020200c01a1200f443c050b9641000100440018040c1c0000c0460b40d0f000a40d500d084c10601c0325501c400e6810008000041200307001c0c20740c00c0c1c8091a00894240e030000b0f0b09544615018008801011026600f40b14568108820950004000e40318151000983d112501e00c542c0250a81e2003d8601540c00c4d0011038060101c840d00900a55000b50014000705106907111451000c95906400507400301501d00d031241100d0034451004d9401c080180c00400d01e030740100c0961a1203014078003c841c411040c90380840c0522281c0e03900c04401001c0141034103d156554040a945c64100d100401c2100141d240c0111420b9400c6102c00d08548000d08841c3c90360341c510881d04020041c403608400d070742c030500f400030b0f02584914140500001c07454841954a00e035508040f600390b004402c0f42c40404204108002c0181c4603844007480302503118000c00e441c0e40340361030003502504c2490510491600c002100f500b91040c0b170110700c6d000c1c0d850140d0740010360f02c0d5000101d087e41c03175a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 997934226 1250 997932976 997932983
    0x170417010e0102030c0919150e01030b030c0307180207060f06030209090102070f030f02100f0e070b0c030403080c1513120206090d050d1503051e07030f110109030605090f0c0d 77
    0x5102e1481031f03080a0302c070030030045481015074980c40d0302c0d07003070040404603910034480c001486412050b40c1c0d540c0500c103941000b5012002004101507540009aa034141c41c0a40c0c060000781f8514001c11480b640c064685550b4881030030310200c0c03698424207005116030f1000764480d074460008100c0545061003103509050b000500c06c1c0f055005900c0c25581c11441160000452203040c0c142c1e41442558407503e400c04981d150b002c1000813951008515141030358010940d06403041112251603940002240c040380d0b404654142c0b00d030085a5164202104810040b400c0c00d1030404000c0d90801c00402c071008940700d0600d140a10702c4025040b070b981c2c2d00031178114195510513000030400078010300140805e84000100803503600c2ca0080030041e104110b40c0212960381c131400303c0b240c04042c000203240c10041081e00802501d0f1031521758155040c00000040d00031801c00300315008a9120702641c00145412180c01e101908028051a03034503041040c000b400340c01003403080c000507d80b00e640c60100c3d540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 997935476 1250 997934226 997934251
    0x50403080a050f09031024061e02070806091f0203060102060601180815010806150907030e0c1c12051903020c0106120c030b0703020304170304170417010e010203 71
    0x80549042d152580071110035032069005211980307140d0f50410500344010044440800d41400c815a285614400d00031980c400391a075080521620b0381c400030400c00d4110301c680a0070741408049041c0d0401480d42c01515650003014100201845c0008050b55618001e408038003002030203010110881c0030680c0c100d40141c00180c0401c4407507210b60071003d440d410301008000341a40e0382031040d180200110034000f40a07002801044218020f00c92503500c04412207818041d610868005807100d04028003407000d06596222900351348600f045814000100038151038041c42e2607040f01c0d589040001f000f20b4050180c40c01040110f4071600075111086111044103027034a50040e81580a07400440c4580655941e404c80004d903024085001c0300f03014051511f0b05a2281035003010a003030f13003000340000103260040060000003001034040c40006400422281e03203075211071410710301c050030715103580d42035520215001c0b40078024100d0f1295101170140003044408040b0800c0c1d4281d00080352010034106 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 997936726 1250 997935476 997935487
    0xc070801090b06040b04140115081302010e01051c020412110f01020304090b060c070306050609090d08040f05150103051e071206020304030903050f0706030b0d050619021b0303090d05040308 83
    0x10184c000200e00c50001b4004a44c103c3d04070b40305804c0d000268002c80c403032032400020509080c0c0110055401080c0c400034040061295000a042d02401480840c1084400503010501c02000c0d40380c40b008105000c1c1c1555900c0d5100c10f8071901055104003070300c46804500c4400d41914050000c15004201a00034505140c9031407445802010b0b07903885c10741c12850070407068103100810b0000f4400f45100340000078541c01e081050084014008000074101d03030018061444981e00019001d071f000340d02031840024041603280c201d0030300c45412480500040440b001204200c8040340382080f0039181d03081408007004c100c01150303480a09100380407103644141d4556003c100c0640013154000d0090070220403055a0340e0360646016021086045140c1002600340000e6505000b4020b28510450701c03442004240d84a1a80ba00c402030989140240040f000c0101405181c055a2040c6181c1030540044030610480a03181da100300c80c1e441403402114a0490218045d0f01a1000d880d0003040d09c42c00d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 997937976 1250 997936726 997936729
    0x815040c20030c0a06150f061706060c0610061d151b0313030203060105040b061218070803030f01060801060f0c080d0609020c0616300c050c070801090b06 68
    0xc00d041ca08148280001c00481440d200e0070809420268850200016444c5a0710b22440002c041c6421030000f07148079803410000d45078001e0000301c3d804548050700c07446880c1c4000181c1e4520851100b10f143c2d00034003080041c0d941c0202800c0b011a22507480350a4000c5404e10418029100a0440d41e07014000c8a0302124130052440580340003070382640102d498403402403200340755400182c80c1c2084075520030000d01c210b080a0141c42c1c010101910309000c0b001e03d080001d4403602a2400c80326020060740001101d6100b0700d030301c40700c43c44110340c00c0d40d9009440c1e9518a440343e001711901d02c4e40345a19000001c04070700c240d10540c102e0f003076a81d40c5941811194412075030161001001c0d54607840506c840343e512401c5202d8000148203d640041c0c0e01c44940d121340c0e040040003007285082400399051070700f1803600002e40d000c4440702d100b201a042d0004905440460400380809602185400c09049195030403800510012940b841298201962103d0700342c00c0e51410840109220149804120507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 997939226 1250 997937976 997938017
    0x31210030b0106050d0b092a0706050117011505090408071532040203031b0309100c110406180914100b1c0818030a12051e03060a030b1b04060815040c 66
    0x11040088a000d2501c3c4442d2924400d2f10401e8102800000302010210b07900c2e1801d1159004080d002010408164580800200d14000080001e802840002411010080d59040c154010138025004004100104004102400c1a0258820340d0700c141040460000c2d81c1c5100648115801001140340c50017030300c0d0342160540c14580014991005120000d10341e80c4c2d602c9141c4103410507035525004409581084410402c01c10000c50003686012401c3c0aa02804200004c488174041d0000c0750f6002e50385410844a4690b98103000700e07000d045007014a100300d54002600503002107507009410b6002d214203007a11099030100601b041402c0050001d0050584150300d6800340040c103031003513081c90b61030751012030042ca46036400207100055103904c4009200c03000c0c1c1c140e8a43c00303501c0f030541c5040300c0401d09240c058040a0041050031000800b03aa0504660050380040c1d80da200707440b147d481c24050007114003a5040210892041074130789103400d29104080005050380c2d2024815a981504400d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 997940476 1250 997939226 997939291
    0xb030c0f0417030d11090904020f030a08070b040c0f080c10030b1206090706050421060209060f0406020d03140708040323121602031210030b0106050d0b09 68
    0x4514024440060151070046810581c040c4031000f466850390000c142400701c03510500c5075a240003061141111075100c41c031a00364066410382d1108444d0140b240040d16142c9c04140007042c0650005242c0c0400c801e0080c45c0d4000c07403007890708006550321501d01d2001000a405026247d9000040f800007603d03044c00c0070300c06983c030350400003141c001c0d21000c0746e0304080000d44045168001e5045c84442d502c2000310000820369843d250742014109014007044000380c051078580d0303086a001d488140021a81120700c0104000c1180c0c2da500360181502456801c01d21950001d4014405c010030002d00a0040c0d007020400c09010041c660380e41c2e10140c40103000908160100318004044003000800030800300d0410f101d200c040b1703032103044401d100d038100f010040070407141e4034004000e40b0440390000240c2e00c92072000344401c0c034256035502a509240301f4640c009004100c81b0390000400c250480300a104248004d10103001500c02c080034042111801e0350030380c0c6100342d6240300142c1030702200000780 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 997941726 1250 997940476 997940497
    0x1032013120506091b06040611120301030c030605060405041e140f01090c1509032402070602091e0f060f0705100509060a060b160503090d0308070e03070b030c 70
    0x2000e4540001d10007404030414101d40d254096001e104409908100780b45250300c0c4414a24128414180440c9060265115500500c8100ba805600700c80060141600d900800d009080e01c940c0d580c1000b040c5200340e40704c25918149040080380342030a0034002c0d5440b494102d890303a4103003900118206481c426241c0143c0e02c5515058803a100008180306400c10740c9046000800d40c0c02c21400c1141c0c0303100090703104440700420310140d206810303003080a10044a8215101354148040b41c064002e500380d055100d8040c42c2c0c40000d900003007000039800b40810311010b50b000c0301060650050f16260b0042180e0321a480101ca42600d8000d19020006050740107040c00950304213001350307990700c0c9031501c015002c0350310079151400c05c100300740b040015a5000f000d10609100407440e15100c6115031040c01c1160015102030382c01b05051000030001c03680301c030401414403001c141c40342c14018100e80c0c0a0351000c0020301c10bd0081003036031800084400039550040100b900e580c40707400c09400103070322180304031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 997942976 1250 997941726 997941757
    0x7230a03020702100503011409040b06060307020a2411090f06160b0405030d1103072f0d02060106020106080a0203061302010e180105040b01110d0806011404170c010320 74
    0xb400503140d4950003400c0311550b44456442c5e5051940000f502c030718030014103001d034007800c040202045900a80c50303008401624035a98a07290b10070300324101640b80d5405810702c8070641c90748980c2d03140004514884490201c041014010410088016116188075a580403003404100407007890400c000740300d03003211403d48003103110440e5140003041008460940e4680c101061550f54a200307401403000100c0c0e07601c544c618518000002518403240001400e800e07403166000303000032404011105a504030b90004450304004e480900969039a024019a0019400e207000003c8400c0009070a101c4aa40103018104a584141c61a2000d4210160030380c100304102c01d01b540141c46a4043c0306004e0310364800141d031581000240019500c10050740d03410410300c035800411b2040701040220765400700d0324001c41541c07105001291040f04000b0300344c500e00400500003507480d0b941e0b4848041c003243c4030280c0d61081007040040d030841300051042c030f00a10743d901b862040520110000e1a40c0c00c1c03c65483c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 997944226 1250 997942976 997942987
    0x9071b1403190e0405060102070b160609151d0c130506031002041502071211010e1834080f040f0803072006090d1107050301050403021507230a0302 65
    0x1e09086181907044102184601da0304203c582400e00034140d01001c03c1c0000c00307106180042040b0310740708d102410310117080b40e800f0910411942d9008949850381051110002c00c0081c90700304010400c4405041440e546440e803688002c0000c20141d141e6000242f0440b010a0003244c1c80c1c004d020000c0c080c40d40750242c41980480c0c81c00b148098000350028003044c0a0f81903039041c003e0314001d0715400c40c0742042e90710810007000402c40184030711001020701c1d020381d40b410318130040b4204181c021800b00c5480d2170082000034562010b504080d80b980b108102d00c002c00701481101502c11102d003e140c002486a00c0000d5020710b403400503980092240401030121040c41e1070b0001c440d00141c0c0c8400008207401202e0720320b00194a51440032400f414060300d840d0400101081e030b18605449440c091100e1810a080001414020390300142800f5009008510b85840c2c0251902d02c0c1c41201140020841c0215400d00d220f07d241c550301c41103240b08480c20080d240d041d60825000790302070004241c0c08020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 997945476 1250 997944226 997944247
    0x11061510110c100c15150311010c0b04141005090613031106150f0f01120b010509040513051203040c0501080a110a080928021203040f03030e09071b1403 67
    0xc148400782e0313600c4081c07101a9241078000710b0010480c0c1c00840d41440b0a80d18000c020000c10700840381d000c045d0313517104800c900042e00e58909480019110f1110a0204800d2000c035140c805584c0035008151003800e0203010110088400a5074607a145901c0a800183e27a003000e0b07095210710b01d0003414400c1d082e4a9030b503141c81c80c00c94222600301040c81c092142c0c100c00c0c140309040c00c010900455100b05080b1032100002c00001110b450400016186ca424403a141d010700c00f190310b0443c1c081c00030300c00c600d400341c2c0003014510034442c01c641f644a4024408212649c80c800d5a0140b80c0c490b164540c402d2600004540144000c0c000f0207201c3d42e90220690104d11280041520084a840e000110325201000714141560309c0e0b119601c1c1d01c6110b2400d00040b900443c1090110360440b00d404951051140c85460350040380c100800500300746d0400310030305403c030380309498940d01211404401d90720b8100c21103401c1140091401440400518000003c0c50726021180c10380708401124140883c500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 997946726 1250 997945476 997945489
    0x3040e1503120d0c031b0503160306080d09030c0e0f0c0c1006081b060f0d0509030706061d0907030c050f01030f05010f1d061f050d050711061510110c 66
    0x1a507a0515135840e1390480e800d4040c0554564080c5c1c240344102101e0b900d06014289100007480c80f0b6032010b107a2419920306005c0e038000300107070010500300d650852002d10083d0000b482400306a41d0190000c400003508900c811b03003148103034010703442a504d6486020095280d600003101c00340c1203000d0f40f901108641d07060f205410042032100001c10820014055010040c68208601c60240d2020801101401c5c008403c071a6007800c0087c0000d41c2d41c1e6024007490560040040080c90903080c444002140314200d140c409117480410580e1080c2d48234072000c0342d03031220359200040030911149410446440c24a52180400ca41810089200f003c0c2c18a0b840860301c090700000c5240d0442c030400d1000321000521400c021411241c14517850030000000f420078481080700941940d41d1241c100c1c41c0318170860640740c102100c3d003003d0040c1d0404402c0a81144401400259107200712800a0b0b010801045032a4070080046c029044403106990104d0fa1100041894025842021800b45807600c418 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 997947976 1250 997946726 997946737
    0x702060f03060f010c0b011707050a1d100501080a0506180703050106030c0203041a0c10110430030e0a030b01030609020f090f1603140a0c0201060803040e150312 71
    0x5141039540c0c6024403c02000d0a5001d00d2a81008840a030b580001030001880f14159080010082c9070300c400c1d04003803442c02e80c8039000301e500141000300004806030001e00d444918810703842d81200b2030b60f4180e0781144092041c07240c1c9002030080004a52020043d03803296400c00b5020b016a04407000d0000b810468020a5580c040026035a000401c0300507410300c6200b01d03203400e078070107986800d01c6d09000300d01e0030780002000c4046181c0050320110010040282c1c0303082e580400c8040c80410207d1a10702c44030b422601c00d0341440030582450a49456107044c00c0054840c070404c02c20410a81e907141103174240121240140c0240024074044041031103818418001c61050802050030a05841889075021075403460b54020a4090706100708030620141d010f50098a614400303882146c0c40c0c4040f0003424000811080e0001c3d4403003406045c2c01240c02400742c0e071000d038000740496a541d00600e9960300c035521905845601c9a4007088004070482c0341400c0038a0003d04541e01581e0310041a400d0f0f5119 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 997949226 1250 997947976 997947997
    0x403030c03061e18060f0302060a111006060f2606030c0a0e060f03060601080121210807050301140d05100c1d0f30030d1d06130b0408070206 62
    0x1c80c1000c028130504103010078104000f80c0c10901c009490000c8010f083e00403808000d102e0f43d40802c00000c0d1900c115030800040f8291811184400030442c61040103150f41d00076100003c1e40c82c055120300600910090912414001101d0f1100151680d40000030001808260340350080c052004c1460356228034005c043c1201d441c0120582c1003600800000721240703000c0a0094000c44108030f0260382020750307607044401020f40c05182c290002560348120144280c01071404415108047c00182c081c6074044000040d40c640100300d8a540c14156024042403140ca20601c59031189100a400e00001c00148180309404407500598440e18550590b40818503400c0024080344150554010f4004541c2e0340c010260b4940b0101d034810000300d03509103a500c00015a28420221503052a8400c40b5807807000340500b810703681ca440d00400c012010b0300300d46d40051980c0c42c26042d458a4408007040c9240502526000707002030064680c1d0780da10a1030014010754151009105e603d000d80c030348034000c006a001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 997950476 1250 997949226 997949279
    0x9071e09050102060a0e0a0f0c080a080a080618130c03050f0c030d030209030c210d08070306063e0a060b04050f19110f19030617060403030c0306 64
    0x10038000a10301000209021707005400c021075854400e20105100700c0d4640c122a10b00540c151b1801c142c6045903d80d0700c101002d101c0c216000c01031007100400303001302030a10b07521500c5070b4480008201e0032981c40c4510b04607161341c49c00814a02600203c828514074494075200000075031b40d85a007414480406c001e181d554009a048408615007440301003117011460604500707281251000c29030b2140a180310500904180300c000b200d140000d40070350b2003802d0450071209071038010540140301c04025164040401d04041c4003044960141801007140c00c07562403407584144260007103050818600f00d00c1d041c1c0c07a0841850039071754102401a80c0403113008403408907030076040b2410320080300c0009010404e8003041905000f00780f0741c651030911205850807008501500c11007143d001602c03510a01990035040000c03041468000300c0354400010701a500d0807c0b80d10350f5010100c10f80d10307041d8a0b00c2019000034000900183c020b07404405403550710714002a0f00c0351aa104c2103a481e119000a0141d43c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 997951726 1250 997950476 997950479
    0x9030a0605010f050a081b0139020a170a0f0309030b0705120a0605030a06150f2601060b0a03051e0c03160f0c03050f0d15180203070e09071e09 63
    0x2420000d441c000d080c1c083c010708202c0303091518221041e61901030300341005002c03421410201c001c003041c450b035282c03204580727948428020305488458640f500102c0c000d5419410008040a030a4400d0850b1800c04000e400701e00c03110303981c49005551002d011000d0160000c000b01c041100c089020f445480f040d26030361740d1100304d90a540e0b01400001d108120322130800c02c00348240d45001c00c1051925501c00340204103c0131902c0185011041604489070342885003000140c1d154100200b40313400c204550790000c101d110304030302d2400e0755030900036046541d00800210f0074081c031981c00b00da0300095940c54100801c101e4403003940e0084041d2542000c050020080c004881100035101d200a1940d041965545c2503071840641003680c440b502606003d03010401c03601c09011001164202e680b86a020402d0010fa06a1a9003198150140e580c2c10701076040704901c160803910860b400b580040d110702c050700c040941000b881c3c0100922900030072800c0b40c12031455907064078807819a0007841d29003c0290303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 997952976 1250 997951726 997951729
    0x108060a09020a0e06041b0e0114090609060f0c030d1a010801050a120611280c080d0c0210050406021b032a16060c021503061509030a0605010f05 64
    0x498040c11404034546049038010040e074440404500311019800c40f101da0b41e07640304c001001403050740742d1107004c44110700042d010a540040e044001a0091f01d039240c51520b030200460031801845031150308400c0c10400f07084289081c0d009001e401070b100020616040700503502e1420740e00221441615251150381e20413441a000c801c8015500081c0307402641c6600d048001003180c0403a2050a0300c640c5032007050b005011840d00310b03184000c02c607006c2503500c034074080c00e2100841080380c1341000702d080c082d0b1000180344150b4010960a41200d00c490410081740001c0c0020030261220900b90b03c910040408224568003400c2e01c2a800f5040040e100c20501c0c50b12300d000c00040d0740d0340f4000d800402070b01180000307129141c01d080440e015030b0001c40365040380c014136050f4208a00801c1050a1800041050340824100d0034a4030a694031600c1c0c0401e55917016140c00140d600d01c1e0310085049410003d00c441d400940140d0a0040c00c4842032581a10380d841210820307040a100304040c120140884d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 997954226 1250 997952976 997952983
    0x60e031201050607050c060a0207120803010608071805100c05010f051008190b28020706060b040b0a030c09050a03140106050f060706090c030602030c030f010b04050109050d060f02120108 82
    0x10101650111301d0b1074407030342c0c619440b2403610b561503100c3c1c0804641c0c000e809108101810203400800752a20f0407581c0fa04004c415500244500c40009400c2000101c030588101c881c002800401c034507801c41103041000f080368013290101024208800c08003500d000c103609000706021440d07440800505405c0c04d20401c0f0500c80c5540202c4050b07440744074900b0500e16040c0b0700b00d402d113821001c0c2001a4684d5038506600c0d18a4a00b01418501401610101c4403c0c66004082c038521406040284998030000368100d03024034841e00200c02400d109860341c070307402600081800a11890803041058a0b800090100840f580060f80c07041420b400546805100344107080c064001255001841640000001d456104889008026903100c200038000c11014a40c81c0001d15071004095403240b400203001d0380d19800884002800401c81000000d690a41100300e0301941c40c107079605d030081390600040c0310541e1900e0104541080ea1004503850b50055031014240d00c3c815034010400551400490524 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 997955476 1250 997954226 997954229
    0xd020a180e09070b090609041e0e01110405040e0f0d091e420815010903030207230a03060204051302090f0108180604050606031005040b150d060e031201 67
    0x6440c05002c502c050000300602180e0031004440ea84003a4140401e0305070080d040002e81013800d12040301c40600c611038035110aa4640f01e41000b0210f01480454242d540c1c45684a200c0c1c6800c010622150070b0907007101150009440460300d07420100701000b0318000140781486c000800c00d4500744500d58094404403401100010000221070030420130480882407154405401c07500800d0b1030031036241c40074100b16003000b10300484404c04010b990103131500d5021100240c00f072502e40c000b01100c1d8040c0c40500103403a01a402030561600740300d0184014801c2c40341c0b0301d2942c403580791880300603501d801710040074511034180941c54520341405e001aa0090b2810a15900d005011030109a11140c2510501003800d181c814450384500806022004422400aa40340261020001400302c0000c4c40c3c1d024880503022180c42016a90382002103d03000e5800500101003480402c140c5a00007202c1030100c00014107410002e2880d41c0c8460445141100b50b402c19000840c80c2440c064444034200d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 997956726 1250 997955476 997955489
    0x507180c03050f06060c070e0c040f050612061c02060c0a0506090304120f02150315090606130909080f04030615120809150906040b09090a0b010c08030604020d020a18 73
    0x55420a9400d107070190f074009246901801c00803d41404504d410030002e0020300340f07200c44c80d4650802c0781032220250302c640103100907050120000502820071000b04d40381c943d520b6203041d00760344902c01004044602002c00750b400300340e980815809039030b5200c000e001c050403000081680c0b00c1d0901d420f900705407004003446841d030402c1c842005802d480b682c1800781142e00c00d2845604140600c002141c00c0d581001140300781e54003100f00482e0011007013007241454411104c0306003940e1807c0030801c0301d104290700b46e001701d0300e08203080201414a820010105210304000d40c100090943c1d0280103400951059940913200c25481555000380718000c80a08101d1800c8014014652903944051140c256070794080c809190350300300c1d4800014140c039600000140482d5407541d8a101a8000d6009404c007240308030041c4010459450b40da100b44003103020180c546400101c400d440d4280036810041426070030680030032510851800358801408040700c1382d1100050280c507404005030200c0c054200c0c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 997957976 1250 997956726 997956731
    0x1014010e0415020a02011b05090316050d0f021804150509060408030106200f030705070b0313080a0309060c0906180b030a0915090507051507080d090f0507180c03 71
    0x12002c41c4480320340b211000019000941d0710070314030034124014000415500c0c80c0c3d0440500580f4034640c03140c0102030300b203c1141290340006642085480d21070316031280c150b102d542e040200340019a44140180013900051603041400407415490842e4413040300c044071100d43c00403502410400c0d03489000e801c126203400811003407030283d413481700901c810f004030024440c005085241a550280100c5c005421310416544182400003289030b070b03900b000204840c0e43c0a4641e003ca0121864001d580c4200000700248464003066101c040300742c2c1c410901542050303129030302c800110300c45006a124500150f0350305800d1514044004040f08402811a090181d510104201819560041c1c03a00400658070000d0200c40c10325080d04403003d004c800e4a595802c14a200d000d0220104540c1d003201d0050f20004e1138803403a180070304514419850010075410080c40041180006a4001a10f541c4500390f400010300302174440d04d18150066225005a0110540c034141c071880701e0086041100480c1000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 997959226 1250 997957976 997957981
    0x504080f061905090c0d05070627060e0315160e090609061207080718061d0c310501030b190e090312092107030507060b121014010e 58
    0x4882c0e20400290000040c07030710380010600b00300061080d001c100b04010000c48843c5034600e40700f03450b20001d1142c1e80100e21604202c2480d80c84024600050340504000e040e01c0c1170904400b550524866080940c051107a49101100710700b003c0001d90103811109800038162454050003009020a10741076801038540700148207c81e2100203002e9000742d030031600c40d1581d290006225141400c42c0e440200c4070b2040301000154069100000c80254201001c140072803900c6604842e246044c1511480000460303c00156a6401c1180540001c40101041c9060183d001041d500825003100b83d106c90075485860030041036815100300028114142c0310b41c0702200c40c029501c00001024451100d40d10009400034802c0c43c028006c48032110010741ca55030313150800f200702a030360b0380e0318000d003801c0c0c005445e410001440d00d079010380717a4050341170f982e083c503200450307a5131009890550003890f00202100c16005440109001c250692004a00005031411005000d84140c040691044100140e20b105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 997960476 1250 997959226 997959241
    0x7170703051e090316030605090f060703200406050d14220602071b06182d03050105010914160c17040e010f0503012a0c02060d020a0504080f06 63
    0xa850081d000e02c841c00d0814080224400740e81d1080c000c8065040c0500d00540c40f55103548a524801e480c040c150030020303640c43c841e5165a4403041c003e41039140e40000b0000c2c80e0350380300380c10006409003030107201e030002c441a811f9480b40b90090307003001c4d01182c00072803a070b509642207100f540385000b20074281c0b01090070183c0213140040c4914401d80070600500c1440001e020b05a01180c0880380d10103081e0200d005400c5410b0041d0306580240d00004045034400c0a017910741500e12019205940a0b03100003450140e088541d0307504581100302c03041c0380303004c000012400a1007034a008129001c0c2c0030400c0040c06021541e801d200401314007040403c840719a071401ea0040c400c000c01030f8400e030808198540781031915824044d41d40244032542a100010450803401d210100840c0d906400034008121030918810042480d103d0340e8110b552080c0a5103601c62080c00c1e0740d484180050074a07481c2c0452000440d0681c1d01810f800804180c0001d0200002c810400c501d0b0310a1006001400d02d030f050650 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 997961726 1250 997960476 997960487
    0xc070f030317151f0219050304030b34180806090d030213060c030504080109060f0f0507021b04110c06040311031206060304060b0405090c0102070812160c080307030507170703 77
    0x5215843c3c413443d241956100728000c00c0750140d02c0081048581d0759160614000d40d4a0384a40000c07100a07035408080346450440c0300100024104005461145200c0380c1000b43c0025545103110302040340e07404804030380d1a0000340883c082d007103032800b5005903d4103004091a00c2100140c1404152040022450841c91918800f00307807280e034a4000c1c1501e00d1402c0490f042d00407a004200e40303518003000710003040002c0e4024500c200542c0c20a000d00d0074140702c180704442040b0340850140c3c004042504400517040c1110340d40032401440024404d150b403400c10760540001d024445941e00c00d02c00d0205164005c0224004030790700000444c80c208515000100c61040580760601640340030020804112040d0050a562600500100014a410f104c0c0ea41d840e1080c81103035015008560300070030a000d000c071716088412a1100805d10346401c2101d03003150920003000c26a029440350401184a46042c40140307480d60280d91a16100d240500348040c175011050805030458500300000070000e9001b2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 997962976 1250 997961726 997961749
    0x5070213050601090f15030c0509061801031b030e15100b182206150e060904021e0c0105010801140c090d2f03060105010c080c070f03031715 62
    0xc0601291507120400107941e94a41a0046280c20140000c08036942c9802e00f0074802c0b40c2080e55081c4a8280010010340e0345100da2007045030880d00030060300c2c56640200ca5090614141890001052000300703000f1000300d0042e090400009840761907560990004008002d1400348405800d425801c0002d02c46c4420402b83c4281509004045560101344c06900004010004041c1000e010035901c000303100740340900000b555001c0303440e01e840490b8500e0706020200440409032180060303001202c1c20071075203400404103154419000c00c040c248a0b0008000c41c91440441445691102023501440c0d0a441e4160000c0c0456171404400f403081010040e5a11303000b09144403c02e5854403140045060002202c40203401011100760f84021752205500041881c90021000e5004031104820140c03500b900b031140078005143e92020f403002ca4100d4004216141659044421882d921003040310058910b43c4250003040f01d41d900246551880d0020b554040455034a050b802c0a00070001003030403028 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 997964226 1250 997962976 997963009
    0x1d070b0a050328060e0f180d03090602090a03081215210109050f060907081902220e01021308390402030a060503010e120706050703061502010504020f01050702 70
    0x4021801c8110460341010341d5152104090004d40e8a41d5150108410182c40108110740c042d00007465200381d00d41c0c510050030056000d01410f6141090440182031487c1c07003603074115420011414aa500c0d40c02d207030001d510401d109502c4d889002070728031407440b005003044461210082c2c20002507071503490354259107001d45900040b550420f01d555004014106d0020f215100e5000b403100c1c0c1e142c0025a65104100150848a8294985c1c41041e100c1078840d510401e108034214440c03005203004142000308100200140c0b80042071101030748181d0304001c41c1b01180765030003c0c4079015010354141c503102030040c040041900b03030201480d40d44d00b840048809007070400806070320714110010f81c2c095121242c004105540300d083c2003041c00010310092084911942c40c00f90241e100c0c580124810744110f00e12100c1e1800c0c6001e940300c0c0005040b0041280040554448010550040d0503007120842d0701d169000144d140751620620403684000b0580d603060010500c50100141d85000c1c078107035034110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 997965476 1250 997964226 997964251
    0x30b04030309171611010c0b0609131e0201170c07020f0109080109140715120b04091a061e0f01050c07050a0308070b01270911041d070b0a0503 63
    0x715400c3c001c4103803034a4400300542c2d0600107403c00c61080c000707604000860207403154a400f03544100c015103ca09005800802c031120410001e400e0707280080b5101e038042d4200302140380e600781540d0380305030008100c01195085d0280130321880030755901402d40e4020200031480910305051032294010140070f000402846071020070400310a0303074426205070004150000003407004802c14034000740404a0411070f403886120b00c0400140048589a0103410b420f00307600c403001240c105280c503602800000450700c0d000f540310684400000c0d080c04036417400d605030005034032403420151304000030503411040701038070004840584c4240360388802003a850003c0c01d0070000e80c3c6030310503114241001d0155100b81d41c072041803c000014003003581c0090421030311035603110285030780300c440e5090f003400b402c01203641000d0240c90081c0250016480342002601452000c0b00301825400041c0641c1c0761810b40845d9241d60080c8502c45c03030000c00c03100c005050b005038500d05001c0550402001400001c001000a80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 997966726 1250 997965476 997965491
    0x150c1e0f1f05061207060e1216051002011b030603031803030f050d0f0606050a08131e1b0b0a1218080f0403050a030c02100c0b0f0c1605012301030b040303 68
    0x40c4d40748000c9000506050940d4092569240003030100a4200040e500030f00d11221150301b0f40b040411100c20700080300410b5254603003080e082c062004483c0c108281990342e203001c8420050420034405060358100c0c0d8002c12a40d0441c81c008100741101d40201140d820040c40910000b6002a0090412000c9241c00703030b101d100c0e140006000d00b00aa801021041c50305201150481d0300000030840c3c01c0443c1c585403015143c080042e1020411808040d1002c0e5003800c2c00c443c07109020010f81c40160007171003145084d907a01d0520b2140801180d111b000345800006e0b0510201d5001070010940003a10402084841c00003104c0c14044900e03640f0003003a642c000a5071038440200402924003440e0440e007101c400c081c040c64064040e501e0004240e1058100e4801208060310404502d49060b41c802c22088232619594030075440d980000d060001080000d010190540b580d601028041500920012403101a000040340ea100000317440c0c1c207550131040c001070010560300c0c003580b40c1007a818940002c148 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 997967976 1250 997966726 997966729
    0x315031f1d0f330c0307110a0b01120309091406190503060408090402040f09050a05160f183501230604110d1e0b030705150c1e0f1f0506 60
    0x41c505240a1060403005004c420100324000d58420305580e04c4402c91145140c500a5940061400040401100703000600c00c100c001b5010140e014424100140000e85032400081510802c00d01f00035401003103020444a441e1070390005a007100c1007070003101c5085c10140842d8440341c0083c000781641d140090386220710b0312954121001005d818042c182c0898542210501400051707a11603685420400402d4951030981c240d25043d25650311070340c02c0c1e16000038040d5541300d081c5141c0940940b084100007111316460f900c2d9400316103241c0282c01961b43c04000500e040450a0564851b41e240c041e0781e0f039165a80d4000032902507030282d104001ea5480e100058081c0c0f800300c200301c10b80e650114014031414038603000f00d1025241c4e004511118808800e5844c12030340c42840c0c0307582c15030000000f0055801d02403a02c3c00b94442c41c004051401d100c2d8001903180234004210783c240d824201454400500040c04440a1701c60260090090050030113031031000c4003258101040c040741e0390004141d0ba0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 997969226 1250 997967976 997968043
    0x2010c180e040812070f110606010c0308040516170f070e0106140d0c03020702011101140c0a020f0d08042003030301031e060618150305030315031f1d0f 67
    0x1004138080741040d00c0c15800090a02132441c06160115003c4503010105440100f034141c480e0006070b541c00d0300070b2425101141c07040c030043c0098409000c2d00c03d0644901060301243c5000c0c050740c1000c03010071141c0503030b00c0d03203024481810014540c1004006100c0000e01303c200e241182c00c103241420300b2205092601d0b100f0301c11203018005030752503c490229030f40d800d034015202c214000d0321040701d124000e032165421f0b941901e1280d074450043c9000600c3c0c0303d1000c006000300000e00e20486980704c5103408e4640c034000410081c180452000b03000c01040107500c3c000e100290b040600e0b4071034007080e00804640c0c3e03400180001001c004c1611040d160408100b40036054458220905002c51603850b82c07040c50310401018080d081ca420a007842060000d040c0200003140ea126000b10319540e43d01450020801a0103481c582c540180c1212102705012000320600e10500e848001903c1803a00c2485510360030340450902c91508500510a1030100104080840d00112501d0441500380c0c0700d508400c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 997970476 1250 997969226 997969237
    0xa022d07081c09030e100f271d0907060c050303150f0d060e06010602010b0a091a090109061409040203060a1e09030203130f05100c06110705030a02010c180e0408 71
    0x200381c0ca44080b65060651041c401c0e0f8040b03001780c1b140100e144a0302012102c0000301f20008000c11194007032081e014a580c103011000c8040889000000d5441e4184450b400d88407a0307141000e44426418800c02e6041445040300410050400d01c031060a107a450b2610313800010010b840382d41c155260f001644d1154102e40c0c0b40c1c00401085400c802c540c1c0d01d032074402001c0c0784d01144200d02c03e820011820900500c41e550000c50000c040019080c80d00e5100d5002d40b080032950440d02145522a100945070074403024003818175480c0c00700c5c5172410010740002d9119400b501e184950715074001d11025031404103045030004110740d4081a0080c2c00b520450610780084458411140b80822107800e050b8080050414101c02002c1c54020380e50311001040004010f000c0c0e17940c4410103202c000034680c0a402020412440307401c0114452401c40b1800031a50003090059415400c006110031010384c0c284110b44240c000e500b400c2440741007000082d410301c2550b000740f1503240743c0070700854140705040084e281c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 997971726 1250 997970476 997970527
    0x1060e07050309011512021311040605041a0301030c0b07050a0215070b0c040b190e030712020906040e0d030216140106030b130305180f0301050a022d0708 68
    0x4a040c108480010403550040fa06840380354605082d080346603150607158011500c41140d002e50600044e0200000d1005071034000040554609040c10a0346811010b04020481134481c2c5450718076042030080030702c800c108000504081000180f00103070080030703900d055500e001052a12400c20340740081c44c2c2110b0360000b070b604c8450a9003062010200700c0003855000c2c400c1d080c0c02404d4440250b4201d15021305e004103146680d0034802800305403070f2003000c0d1040c441c1c14a0b01508110709080442d043c4410740e0002219040260700031001e50411000d25078100c44152010459415864046503c8085034625401055000290300700351036200d20038040c1258010b4050541c0c0003200290f24006c00843c40100d482c4104040060034100f003404040452a8054580a10f000103601205856400c1101155440800d0900c2165251001d04c1494850b0020410061f42c8003800c0300072059160801100e1302441072482200c1981600311029070341640d078460160354446c20107000d042000701c00105480c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 997972976 1250 997971726 997971749
    0x30f09071824091506030204080c010503040528030807051306030b0303090a08030304110117280e0d0914011d15030406020d0506040b0123040b1305150405030a0809030106 75
    0x3c180b90015512089292220705140c040103951440180c06a02980c0b04210b1290440d06038040e0380d5000d08011503000703200c1e030213030b90391000c0240d40d0b80d00500218904107003140804414108041e08841c64a03080750b11410018200704120140c000c408810f8001c0004060b100c072485505a02e0400aa920071075000303164824aa850b0b002c055665003003120709071841601c60310f8a689a5004900d42c5200104003c180c441c9981e0300e00050011188002c00704520151032402d0001c498000d2207074141b14002d2002800a6086002c00104400a039400c41d45c40108040c0e00d54001d81c0c0c0055000c0c079460100318040082060b00e03000600c3d03801081e0100c1d441c100c030010800041055070390003000c1e1801c52102c100201d0f25000240812644510202c3d40403c100780c042960041c1d40c0c01c9400682807080000d140f81c1906c44007201c00c50b411496181143c1004e40d9001c2c016031400808001c629600d12488600b803030328110001e6920034604401034050780d800561041207450a41206c2c01914440000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 997974226 1250 997972976 997972979
    0x51009062903060f01050a1a09060a1e18030b06040e031b01110f0a0806031006120302060906070e010c0606080a0f0b0906061518030a0305030f09071824 67
    0x50588009402002070b109004030070000d860b40003403c580328103072900507200c80141c40c10809005100300741d41c00503000191046c0840341c0142e8820000b8a50100c440e9584000d9401c0c10300340140d404840380b5030b04280b01040e40c1d200c0011103404607070b00c21240c210310314a25036156180410020000501c2d1000c3c2404005022665103070000003c0d22030195580080141c0120f0b1044080750740a100b41c1989120703020024903e10318452100d09800c100001e080d40c290519003000c0504036407043c4d00584010ba000300526040c150107101042d40400041301034010341c9460800101036000d041e5469043c000d01c9030030070342802045c0d0b102030083c040c0c14086032a0002c083c180305503445295081111003444d89400507401c0c2c400450b0603401800090070902200c03020b0b800101440c1c2203552a881c0c903120010740c44003150b500304400c891543c06a20784036564100f8200e40074000c80c2c020650030702c1d903112075030070440c880c0014404800b41c0d00094000950009182683e0b000c0c1100b120041075060300d0580 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 997975476 1250 997974226 997974281
    0xa052203080408060703090804030809011704150c0c0507050907090e040b011401050a08010522020301031a0c030103120f201b181909052a01030905100906 68
    0x40c4252070304a0308450f0545c5e0b50020840903102e034020003c24240c0107000810014113408080c280128050405494220f2400c1250b0b0b1022411107080d00c1800c0e0702680b000801231288200e5024400070b00d80f40100c0c1c0c0e101e031151583c074642803140500903038005000842240c41000784d14060400032660010707504003030034010320641c0c1c00c3c0245800d042c02c5d003036030280c1076004204444101c0c2c000d1310784a4080c2c0c41c010400000c0d2203042c1d502001900d282140440c0041648002c5020314030079074454a101d810f854229001c01d1009082c805000070410043c004034000d51107505160401d41781450b04240b60101c100c0b480c1b040005101116404029030a811840c04503a40f81091640009201700c1c050900030802c441c0c01c0c46c0f02860140c0704600101e0080d80004441e401d400e50201e0020491200a964452410b203148604100b0040740281160400c0c4a03411900768128091a06021464041d00c509441c1c88503640e80ba004565603142510070450140c1004854800120f142d40d01144c5400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 997976726 1250 997975476 997975493
    0xe0f01140a1106070f020712020d0308070212040b0415051c0207080d1a1203040b0409050a150303050706061a0406030c110d05090a09060b191202040617150102030a052203 75
    0x420417001d406284008030301c001343d020482400c550014060766500c000c517181a01d501101601000071401600318403a111003580340200010110000102c1e5200c1c6800e200029001e601c000d05010050100103590300401050031105181c4420f00006a641003585801c02580c42000e4204c1010390410540c8111610441c001c0000b0280c05c1d03864500c1d15200c105c0d5140c41c0d10503030050b1300508000740014007104406a00499011090490000b80328940610030030b4000c02c298002c8000400c006956001c0103114007a200042090400122010f0120f03401d105050044e402030b04c08150307650b24911302440c407440040790030851500c1502c5124640480042c402c4c3d00640382140940103c401c009250482d510816046803a100055810006513076450705000e00d003c1300f403d00300440c0101914449800388020070007000c8545511110708055240c01d83c51100041503494880039412240c0b5190760040304845d0f05c039440c0d240c090f40d200c1508102d841e00a1104468072200c07054000301100f00003120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 997977976 1250 997976726 997976747
    0xa0e0306061518300f060a1104050d06060f0f0b190e090a240e0412050f030a060f08032b0e12130806040f0303020f0412060902010e0f01140a110607 65
    0x209041d01c1c1c0c40315184e80c1c5d0b541d00314a1000003d40c809000900744450543c00032480b40442c3c1519840c1075a20b000082000c200020142c42c60341d51840704002800700c0c604158020244001138502d8107142842007607160068810002401000c0519407501503c01d01c00020b0118004000d440a410101c081c0300040c5280030414165132404d02030a00d001d201106e04004441c425004140656a01c1d944c2c0340b4403102c503810240921006001e142c08500d03070742d00074500c6030043c01e08c0000d00300d03c0c001c446507035807842c0c0d48050380300d4004110302154541004c4940342c064000c001403482c06d503800d08903203000b005000161101d230b000f45540c00c0e440c3e08116008101d50701c95031414404094546400a40740c65013510000d0100c3c2e90f00d810800002e005c0d030050903000c201d0520700c508050303441e1450b042040c038900040f145941e85154803c01c641c0c20040700c944902c401c0d00e000c1c074407100440000e00b1142c0c660407000343d141c0c00810b4100790f02d40b0400004403840603e500b40d6205003800b08002d421000341 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 997979226 1250 997977976 997978039
    0x30d0c020a0b0c2109060a2304060215071818050105090712090f0b01080c10081504090f020316030c1a0d050402120303010b0a0e0306061518 62
    0x100a00000c0c03080c000010b807090100f40101400c41082d1290058541c441e001100b80210007007800411400d0b580c400150165900a844400302c64084582104010b05408420b444950050000f84440c0b54001403001400300b00074400ca0b03030742c0c80c0d005c03040d01e08030300d00508039140c064901c101103001501400311001c18207040340180f0460340c0ba0006c0002c4c803a01104c0d02e03000502a411005903001c03541e00300c2000207019445900e4581038079113451200350000d8020b000107501401884480c0d0401c401c0e44c40303640e505454204d0761410b1200143c1080300340c1010152089132103920354030601c40010810400c0d154014100c0d401d8005421081f4071004941c4029624946100400100000c541d00e44000340d01e89000030390302d024488040400146405402603820848034081d010842d201080150f02030640105c80329150500840000c0c0f01c3c04203065603134041c0e004542440300a0316008807a0504030500c5442984032a82d101270040b0003808440300316803204d03200c1c85014545030940b0f03240415201 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 997980476 1250 997979226 997979239
    0x1b030f02071a0a0810080a150906110c100621172d0c15040f12110c121207051002030a0b0108151521090607020c1002061b09030d0c02 59
    0x110041c5452172a803051290740303c1900b0004d03401c1c00003245803124103100e4004010001c0e621400e0340703c0340110340e06141b00c000700340c100007514907407102c0400c01c10340100d480c050b05121070390a00462610065030504621504190b040c0c5c1075042004110010302c042183c00c03601ea813100c84100c48042c2410042010148200204050300380300d04480c411228400825401000ea07015540c00380f000301c00c1c004006031b4014040000f801c0006401e200c9400e4000580d60342c46004844414016080c0100702148034460a0104841c011141012503001003142c0011401d035146e84a506005003080e40c110f200c0d45100384004100102c9450540c40144808401c0ea0b5140041e40d80040200c1951003601c4030540c0304207080140851030198200070202c0d00c8803030f400d2709401e01183c41c5403c01440700303640c1c0c40b100d03400003c1000503030359041000c034801c48402c40c0d110034440750354503001e51164030180001c03542c000120203410301e59561000700e903c14003020b82121440b600c030020080151b212220704074811032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 997981726 1250 997980476 997980481
    0x19060801120519290a050108010c080114040b03060907031505151005040f06031d010605091807050d051b1e060c01230a05071b030f02071a0a08 63
    0x1040c030403007021419405801031070504500c1082d0460310007102004c40e0303052240940d0b042c1204030283c484003118000151116a1700f42941e08000b030301d0050f041102543c0c54088040c060341d41c8451700904540e07100a0803100141c0c1e01c0007003800f519001507110b40602c81e12080c04075100001640300e045078012002c407a051603401c00c2820a965040e9000f03110042803040300312203880c0800101a40e5001800e0051400f07a030741071421803100c0c2507803208002c02c0d42e604090038200c91582c41e4901d5071000754000c100a6003054000b41c005000a1701c40302501d540c1c1110340d04002004c00c00c402c00703030200801c041c2407030065113001556180d00740041c08080d523101c41140501e0505144040a540d030004021031a5500141400119002160034110035900c901c4511402c00908104000d4101d541c04640030b10b01e030240140c0107464000c0c286030100030f100681294168280e04200c422640c0c10b280100004030300a1040b840c100a0f03400840c0c004111b0f0740d410322058481e0000b49440c0d400c036110000180d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 997982976 1250 997981726 997981739
    0x906191d010807080402060a0c05070654080303010b0c0f0105280f020a0c0b010e01050d0204050a021215150c07090507051b061005240904020919060801 67
    0x20314050300c0f10030101c0c1103900403500526002c4090300504500c0e241100649180e520395030303d82642a4440d01c0819141070305404a40069003082e00d000300707040d5841281d0380c0034078440030340040408000600710300c016030408400c10b008440341e801041204222170310307540c4800309151903a216850f500401d1240345980041030a044c0100b502c9594503145070540c43e00344540c2d6458000c8640e04010b90682e880001002100d214405400a45400e030388a440d05501d5140c42201e83d00c1c12f0300410b0b100c18820b801004a036030748062a0320659030540e004202c4e511540000030103801060a141c50001c044004c03c5581c503801c0c4030000013020308403011021503581d007041e4200d5101e00c0c14294000d400c410410b21240d0300c0c50304045d0700405030745401481e01c0b00150450000b0703807842c00c02c005030340c0282042c49010035405240324043c1108450344c003458180181d400c000002c9001c9241ea1055000c80c2c0705400b59120342c1500e0001001070141c4c0581d01c000311072a02c21044601819012581200c0041000b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 997984226 1250 997982976 997982987
    0x504020a030c1e0e130605090c0306010b0a0f17220b0717010f120b090c03030f030f010509131b1205150a0509060103240e012a0c06020906191d01 64
    0x50005d1100c40e0f110580d162a60f00c06001c2c02882840c06100d0062001c0702c1d07850401043d402810403485042e01d452481d080101510750301c007086810031034188942070f10000c1003a0841e801c410390004180c1c50f0750800c1d00f9203051201900c40030304604183c00801c0302240c4c0001103480758140c0702076800c0b2103a8036810030302c2407012240980d4a0300e4680c54810000503d40c540c40b01d4202003000100d80400360001d000170b1840d480030801c001c440038040b00740507041c0c000e00951400b600e011942c0c0141842c24413881d00e2462072061000c1e2580e60750000c2d06260741c21001c03d02000d4000c1815484200c1442d05026a6401034680c0e144000f12004000a41c030110310b1064502900c9041c0282803142d2075525007420808405000d400c80408c601d030402d0803004144546580b00c8502c200100e007003900c407448402d600529501d440c0c0c08201c0c2c0c0c0da141c0c06955101c0324030300c9101c0e80260010384408010300450307003034000e00104510102d407003900a40310b21380189048001402c50b80c0e001000d0281d001c01100c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 997985476 1250 997984226 997984231
    0x5010602030a031d1f0b04050f06210607110f0a080415030e0114010303020c01020c130e03070c060c05060a021201090b030118030f12090b0106030504020a030c1e0e 72
    0x160020302c00409220310913048603090300100301c6580d03c2484600f510500b882d28040d4441c1e20b1144540c9201c0702000d507805020a40f8404660070440c07498600c10036a4080c10080426201da40c240740d040e03240c952040300d0001150aaa401c54410b4904420701802c100c5090b11a8031a600c65680326680d51203000550b424001d0348602a5030503d4a41400c60102c0c02c211086102803540310007199044074400d2080ca1503605001c00c071022254510300f40039003069402c5c00701c40d0464000074102085621041070340c0c200c143c5207690006072210201301140c15401500c800904803000410000350036a403240d000410107024100340d8080e0f4880c188650124070a00c44044c00c0c906042004120400b01c6a205801959001e400420f0251000250b0704c42d8110704001140800c5040d0388261500d54001039075901001141d00800c44282e482d200c03030201c14014860801015201d500007001c54032022518401544d10000d40302609845000d10480070820040340720740c8405000340000d808400e44410f90 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 997986726 1250 997985476 997985489
    0x403050318120403022115060f01020f1f0e10090c210305030c0d021306030c0203180d022101020a0e06040e13110d21020705010f051e0c0a020f040501 66
    0x500e090f1441d4280210300d10b01c100842e0301c01e007100c0c2010a00d211b003842450003081c400816580c20f441c000c2c04100d02d03010b441d00c44504541c829502c41c6210680010840c555404a49500340c1d21200400c810001e07014902124046000d01c50048050004e0354120901040c441caa003103038903d858441d4800181320071340e0075043c080c9600881101280c010300c02540c021b0006030030903180c17102d200548420b81c0d1290940e6642c03052052010002a80d151260594690083c405146009410001c550048000f505014401c0021400301c0c1c04540d00c10700300c01000d5102214450015000400080c001c0d0030103407803880401d41c3d540000c0e606180160849055503200c08a07800d00c2e80301d001ca00ea08500d890360040790030740c020070501207403a641d4890400085110b03540d070350f41840f4040400d01081e04000740f420300b5540034101c00c0c8626a0031440c0c400f8000b005140c100c2e22002140e5914243c41c002184005a6030301c002900142e03030078003050b018400d90096408116a055880600c0100c520134441c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 997987976 1250 997986726 997986763
    0xa03050403030804031826030f04090203060f180a0507080403082a0f04050a0f030b0601050c0c04150519030507150203041509050909010504020a0306020d02120403050318 75
    0x61000034090000144c1150103498040785d040d81d20044900c00d21400e401042126140880c4424080341390310034442000588070155047c22041d012094860040b4010b0f84510743d004400a0107645841035411b044c2c00d00100044410030002c1d0410720905010b540c100d01d0300d070a180020380c20a001b4014a80035a61555a4416941e241305a612016240a58002c0209250911005840001e202812411000c102c5c1d05541d64584010020941490342c420428051800d40030008280f6081e002e6034007400a080c1141d481d80e00c2039100c1c0c201a0683c0006a00529105003101c0b0031000145120580d002518640c01c40440c100c0c008008100302d1100078a10350001c0d00074043c1480c00d1030147d81c0c109043c011a810070342c80c1e00011015198103030300c000000e07405003810400c1e03141400001d504008107030001c00c51800d00e030700410aa45028040503006640008892401030310990480c0d0200107a4525401356007400d2030018004c6c2e009036803c82030380c61501180c0c18040b0001c01d0800304402d403203144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 997989226 1250 997987976 997987979
    0xa0201050d02220303050408010e0f0c01030b1c050c01090803070c1e08100203090c0a0605070b180d08040506090312011a0f0d02070201140903030315121b120a030504 73
    0x7040a54826405001c3e1070700880d424080b0a500b2030032520103140300791201d035144d83c02d04000da421110f28900c40da030b0980c4200383c41d074440c00c000301d69210710240a18003c550007000c0341c040349982e003648039407680348080d4402000602c040811604409842662007808241e640c02001e40d0764015118040c008440c01c0ca4108004850110000081c50114800c0c12038559154400c034140646149401c5078680c0000400050349000d00491809000444071b00310384500380200240a801407040c0200840c1c020400b09403885016024407000103090700894a075502c021a000b040000191002c40f00d600c50507001c500d4042c004400da4241c81c00c03004c1c0284080e80b0308140401c3c1c41a581a01d907080900c10804000c0c2411044000c048454140d500540c0d02c84442c400104201360442040205810501a05a03d43c2e4080102c0340c0003400d000c02115044180c0300081d4003070061440000c1a842010012880402808000300c001d03241200c2c4450141840525180c07180d04480d001800603070304110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 997990476 1250 997989226 997989247
    0x10f050a051803010f1d160807031104020d0c26091506041d061506030106081602010e060a0b01120606050a050a02191a0a0c050d0c0e04020307050c0d020a020105 71
    0x42481c00120003c002181c4824222054030440b00e4408558208901000449103c00401c00440c0c84a040c10402c40aa03030b40b901d440540c0b03c0031035000003021004001c0d4401503d035034a8040e80c10703400c1c0e001410007090b0a80c49001e008802c84000c103081d40304030f08000243e491006590303580303e1a9504060030600c440d8444040700b00304004e11140e4000d98420203450790241c00b8070042d500c200c81d080184110b08202030518013248980240912a900410050107001e41c802e9049410400c810501034130200855400d9000d8a00300180f84070921071002080501c0310180c0205191300340c203813120110b9011007560745064411901842011074001c21801211502c81c80c000d214800b070174030640e441408010103003605881c0001c1c007038032205d1a010201e080b4180940505801c0400303010104141010490058007901660b4180a0101c0d03496501846460203031041240c4903000900c1190b1382e00c1e014034041d0403074000031030185062240e1013480340003600014101d094150140c440c241003c2c00c440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 997991726 1250 997990476 997990507
    0x30e1606030903181203020f0c030a0605040305190324080c01140c0f06040b0601020615010806030f100e1507090b070206090d031e09030b04020603040309150e010f050a05 75
    0x203d04121200d6594400c1049801000e4040d00d00601c50f0100d8100300c0c140281f034081e114070342000c103802420012200b9030740064140000c07580b003840400c15a03550b003000c0e01c09000f95202024502c04001b5501c2ca125070551061115080c1d1071000301060888c0042d00100c00000c1c0610069a44580d00c0104590702890b0110130000903805068601000220040d0410344030b003601360420b074401003d010421041c00e40c6103901c00420300c0103181d14a050701c00d800c03403d90908481e50600c40180007041d5035480500c107010300c0c6610401150681d4103611012001001d1101251032580035400030310000b8150709901c0c40c001c4009603114803182d410900c0f140e0040c0e00011007280c6c000410040200b05440d2440c1d244203050082c0c5514441c2980409065a9040907210321802c01011354014000111140c03140350f0426010388030a5126602c0d4a4151841c0703156030007400c80b505101032501d0070154002d00004080c1402e9a07180141c0c4c40e01c5c00b06454900131022400301140c418003101c0d1504446a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 997992976 1250 997991726 997991741
    0x5091c06180546170301030501060621051801140f2a0901020a2111071505180a0b07060f0b0603011205011413060b0f030a030f02010e03030c0406030e160603 69
    0x2c06850481d20550f54040e0344001030301d070070310040130088010014001d0a01c6010018110350400f21165440192078111a140340c401080750300395640c000c200e5282c10407800c80300c074030b5080c002080191410034071801020307000c41d074180460b051900007880d02c480c0c3d64401d01042c554a03640c121000701c03c12045840750460b0213040d04621405180101003200d1007070700a0460314601e20325448200038000109400c940302c4400b81c59074800102003040d43c80c1c4404141d4401303403d180541e201c03000d102c4881c42c2c071101c1c1360341039078081031905010a400b81c7c01d42c010550107100388420411070008203031801c184c616042d6071a900c20800d000402c45416a0040c0041641c400d100015140c0c0c0e080000405208040d200c01d01c80b0b648200300c2404000d103504c1240a03940c401c680100d00c206900c070010760788503200480202041414400490707003a000350000d0f0701d40b8405a06480d100d150440306000b4540282c03043c40f0029007064203211060341c0110f038480440031030808000e0f485d41440801e90141044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 997994226 1250 997992976 997993093
    0x426010902120a023d021c0f02010506040903210f0606030605010809010e0d080a0e01050f100602060912160506040f1e020d1202070504020d0b031c05091c061805 71
    0x400000c1801501811f0802d03c24030b5807034649000c031458840c1d00078211040100205e004518240b14003000ca600f0888030845a2903002003607501c04840070118019001207064600c0f15401d201c00454801c1c0c16030403a03402e0313a6080e83c4034222555408002401c0e60181e40400a540e00301000b070a5095120302c1080c3ea000c0c0d030b50301d400f08030059104601800c551040f40c00c0030502c41204c00340007280306803a00d6840204007601c0203100c00d0900301d103129243c01410111202107800000c0c0c0e031202d010040801a50550800240c030301500e05400c03c00f040780c014410854a14420a8420035035060f00700c1c1c3c0880b1240c0140c421549404155a0318940d02c100021220651241e000c1c0065541d0317a03800204031050030100d01061082a0b08181407034a0207c41e010184e010840e402d0042003a400015620211380455103108a042c4690111086041d080c001034a41810204080d1140310448030360402903110343d00321420f420349241408140864508041c810b03080b01600300c0040990a85558010f001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 997995476 1250 997994226 997994233
    0x81f141306021e0c1b0111070e1f030c1a03070e010305060f0a060908120307020a0303020a030219051209190809040b030f0714060426010902120a023d02 67
    0x190b50300c101d03080c0d801c00414139240c0c0d88500e03000c00c01c1c0050022130901c9420203081c0280c81d104620311685c0c40302e4150107204240d2602e8000504406c110403800c072030750000300320410022a01c0c1d0420489007030b450b0050140500d003440300c54140c00ca106040701c0c0316920301c2c1d1b40c2054400f0002c004401502d1b018050b150720030b032190000030b082c2d030b203180c4000001d0030140c03220f248143c0385c131003c0e81c00c0600600e094079038404140100b01c1c101c6d80215001d24102c1e07041c43d0040e5100700010003a4000d02034102c458034030b00e801f0b1404440c01600300c4010310b91912800017170304555680060051b541c81941d500c514100e8003801800d40040d04031005494103003002000828003489000100f482e290040110b0100c81e441110100202d482d0049459030906054a04514190600b0b0603041d45d615501d100c1160201011550344060740f080d40000fa0895008051080c8030203640c9190b5a00d43e5458020383c07050403001480760405104040c80e007a040601e0f103c4503440b00004919070042007504c000036040d0302 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 997996726 1250 997995476 997995517
    0x330e130303060503011107020102160311060f040801060902030103110a0312050c03040806040302030a092103260a02091003020315040905070b030a140f0f04060c09081f14130602 78
    0x140c4c00e0085110007541002180d80762411030000901c0d29000d040070111407440c444081c40030642841c03481401c1c8d281650103950b81e0700c0000c47c03034100e80300310341c40341f45c5c03552070004c0102d0718110320b400840c1200d00440d041c820881d040000c1003140c48941c400140280904c1c461080711a0241024201102c0d007101541d050580e01c490f96400c0c804101c0c0e0403001038000260004407a5041001e04001d040c15002c0081c01d14503140b900703020100c0b000005018449401c60200c403001d44240f150b1011a60303492409403500f4210005406034100c1050305100b04201e849488060384170b8800c0d01e12600c140450086140100014440181600401036a0600030340c0f001242c0824020000c500815044000040ca40c6524445206075080038018a82c10303586c140501c5009451301d46403540180c0c1008000426070703596075054030a01c3c40da0348400c003180a6014540b040304d2200410b80e0750b03c84040f02c00d212428028803004c43c0f048045524a01e1032200600601c082412a0701506000b0f82400a494880 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 997997976 1250 997996726 997996729
    0xa0b040204180531020409020f18040605150102061803070c030b0a060902041203270306090506061014070c030f060f0609150501031a04330e1303030605 67
    0x140c05418480604980350000e0103115903104004101e07100050400c46a094400300032020781d1354400034040c0c8959203c4180c0400e56231404419502c28100514000d000072071801e85c00100c1408840642c0c0c100c0c9000300041001010410300249020168007801050340c5072100c01481f18010a204100e40c401480080c0001e060340b06814003a40c082d81000b059403270019510810fa0b000d81d08001880340c0144003c00040e815604071004a9505040a82a510040d40c134003808802c42e6005040120040c040002401a80c3c1d1000074254014010303242281c0e60030052054516660040400084010b014071840000e2200038000ea24894002020115965113808200000c0c3c0d4405486d856a40d007c8806111224400e800042040c071714180440011105404041c00e0380f4814a17040c0340d16403020380c01e48581c10703101040260005208201006958240f1044681004c403c0c5001a22801e1100048400590780004403040d88012651070340d00c4c0700100c450b5903a0414203d040c16112400030526 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 997999226 1250 997997976 997997999
    0x50307061103090c01021204051c060606030e01140906010618050901171c050306060a030b060a0302031014060a030b010e0d0308070e01180920210f0f0a0b040204 71
    0x80148560100d80b0703410080c0b038007802d207411403c5440c10f5511140348030b400d102440381501c089580c122444c07401403429850001c0e9096002c00020500c500e06503010540d1030301503000c10030070000b00c0005c00c030340f1842068080d40d1100555000388030364055001000000d2060409111130000048421a0a9900e0012600c0e0300001e0708040c2c81414140e0400d448001c00300700d4521540c2e038a0103040160008040c0c040d00c10311025042d01e001c0c0c50005082c401c03050080e000015980009084c041e46e407203031722400800a410640d0a4108802c620000156425041c90001c4099000500c0b1a280000d207400c258001c1c26040e13001d07414811490000400d66a400082d80a103c1c0070351660a845d24240b60000c0040c940c8a58250500030762030545070404c1c084000006c1510101035000484194003410119203c5910360b03810b8181c08002181000411940c5c0c1410b110b41e14444048001d4842c0c100e01150500201e41007100c1500c140000740c403e41c07068000380d0703040801800040c90581c940c4001d005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 998000476 1250 997999226 997999241
    0x3030c010e150901021303033207050f03030106170a09050607020d20101a0909030a12020f0703030c09081203060f0a05030d03020d02040b0c06040302010b041a010c05030706 76
    0x10640000642034102c0c0501c0c10100e0340071042c0402140342c0101c103012400112024000038042018600c03440b0401c003040c440c134801c214109042030502110100504106500011013100c243c0140720580300d03c1c060001c1902d05a0b4201e40350078038511a20a040d50803100700400050065403205002c6000c2403061001e00d009003659405007144030400c1d0b02c0600854032000c01e882c0050303108020503c041901086544d6421018070020500c2d240400c848440306805491450703210703082c2c1b000d02900200000c020204440d070707a02e400301d4203c00d10043c5001c07402000b41220820004002ea500000c0c445d9003c00781c480d5540c204a217a89441c1e801d850301d0404404400d4200314000414040b0501e0a00c0c02040b8441302110305009041c01e00c00842c1e11042c01c151302e02c0c00d06402103810803a0744901e0301a03c0c05072003a5581c051b141d100485140f55115030a0740d041c1d000d540f91402e80303c010f0410b400340c008618548031091000b00640303c01111254507c8005403410702092140000040e840e005041c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 998001726 1250 998000476 998000501
    0x90306050912030c03060a0e0c0a110c10021e030304030507060213090c051b120423060f270a060e06070507030c0302032506110c121014040803040b040203030c01 71
    0x586030b151001c2070140e5641260840348c500540d080402c0b107a5a150402c83d10f94040760b00d410220b40d40802a140e00c4d02c9184e0005550010840c040c4010140d07000804250301040c59040064940918000a41324402039402800240c400c020080c00704002d90000c0800d0310001c01420034960742d0380c076088201c0c2c030080b80b1200041c500140d40c0080301c034031a40b0541d1031303880d01002e40044041112001030301d00c04d0703104000d908045070741c890000710014030f141119900043c1070f89507078411000189c00c03644d02c900c0340440403521102c10701d424003441c00190030340317014080c0580880e9400e046040c2d562a00c226200d551208041006c400054810711140b07006600c00c055444c87c85095204041c03d20345c1040303001a0943c504159100760515441c1210b04950703003811725103107406100c0f0b0141c0c184104080e90707a4001580200c0c4001007030b0b001072255006020401c0c10000d0302c9000c0c4003500b1541c41551702030300f411030500c0841c0100c1e400004090b00700b44000c040b6440c0c03c004501c0c0b0340c03d4805212010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 998002976 1250 998001726 998001751
    0xb010609080d2606011b151a0f13110d0c020715050720060714010b061809070302070b0f010e0a05091504020402040f080c030c010e0109030605091203 66
    0x2008801c1d410004140c40c6029410a040c8240c9021040c82240003940c0c0340c41d00141c9900e01084072a401040301103811168107801d41c103d40001e06100c08552031441055040790b103400013013090340140300d2001c088842c00801d0701001e0541901006002c810b1507002c4c10105a8421004201c0340d5060001e0000c0385d000500130803003116510703010342040e1407984448548442061507064055101044800840e80003802d299020031340191102e0302403e4001d1650030100015042c07043c00003401701c841c030901500009110035451101480300758051041d0951056800c0000d003006032406181d400e5200c22036280c0141400403d440e200d80f8440c080d40c0880c058403040006200280446507100e612251410003032100782041050380b0307914420101400212100440070604664984e011140204a646040d200c5c0326200c0c0d80007034545014401c441d200e44102c8210b4682035005048404030300760140c440f0001ba07861901c0b040c1c080c0030300070070040349405050045501d007645540554003590820865 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 998004226 1250 998002976 998002979
    0x1021602090105091e0a1d06180c03120c19080a080105010c0c0b0d0e030c1b03071a070501090807030e19240e0a1e0b0315010e06070b010609 62
    0x501800ca28107800c02400f800d20340c002c00400c408080403103a172000312074a0249959450410241c0148034540440c6c9601480100560600e100001e8803406040c00c8010100d0b100b0042c12443e544251200d90b0a4060f00a21403480c01001070320040c000c03040302c1c201900c900f40a8841004907042081303801304c03820b800100d0820600c81d40919458050402803c0c0844504116128050a648903200d40e212005000410700310008144e00310000e5101c02c0740842c0e8071828030440fc42d031101e03005101c02d604500c0c0e4203030360f0540c3e00c0e002555104840085049000705000500d5081081e40000801c0d41c0035902c401c4078900159203c2c00800c2d0f031078040d41e200b04882441100f04000c1300c0039400002d450b140c00c0d0006001318184105680344c8161110074505242c1d60890741542c00e0000c5e0741c0b141d0752260840000048003164031419580d00d041d40030300c101d001c5884000349050760100b85c0f64220a03e240c1640c01d1444c5d4010301c142003800d07100500b0f050070305800c1d980b140b9122409030011300004072001d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 998005476 1250 998004226 998004229
    0x21b01200a0c0e060a0b1c0e010b01120912080424020d06061e08060a05041b110703030e0904210c060b0d110603100f060315060305060f040e070801021602 68
    0x2224018010040790f5180310300f804c03400106451350030700030704140010001b025014000f0b000300b0281841c540360401c0c005640f481c0c403a03038000c2ca0030081c402e0204440280e130a007002103d104c4e2541075648581c0070030b0039026040045606400081c0200c40c0015040d110307070442c0ca03000150f070840c595038000241e81d80081301002c006440d650360000d42403040034580400404041da440107034000643c90103c51541d1664002200094654011900300703103480602d140c4141107000352129080191918100c005041d45815036600c070381c0c48054005010607140f610703507140509040d6042401031700044402c0040070903107280b00b981002d03a580072584281d000d8080020500820964007000c0b0f8010444440b26107641c4840d0085603034061103000000700103038201c5410280f00d009064171802a00c20a911804098010460301e00c154409002d620700000f142413190043c24802d60001d00305e00002143e40040c000034007040a0084209e010780c0e00003182c1481e0910186c521054101d030001c101084900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 998006726 1250 998005476 998005493
    0x224040c050901060804030e010509100201021e04231323010f0f2904060c0c08011e02030403092411031801050c0106080a061b080601021b01200a 64
    0x3440303507010b110790000400480390861900c030f43c03158141c1001003548404900407104ca01c2030306210b503400003c00105440781641540901a024962445011a214a0782900b200c074092489143d28400846070250400e02c0302010381403241d540580604205250b80d041502942c1480007048042821201030700003201542602e54010010b440c82e119456042242401d8a20300c24000d981140780d00c04080700c966202d0030340358114a00e10b135180702e840d80c0c1c441c4001401749024500039181c4503a07a600214040744103203c1c00345100d040303207440d47c51200503810741c00c06500001d000780d003407007003003080000c2c80c03c01c4400c60317500408221280364041c40724000c003400044115800740c61307640c01032001012001200407d48c1c042002420041d45400c560340010b030140101e0380200d50240920720a01d007c205013900045254086e0200c4520810110b032001c0700c1a10f0211070315401039101c440f11210a0900b100039180f02030062509113107424840c030142542810102186045909c100103800621500c007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 998007976 1250 998006726 998006729
    0x1511030a140a0b09180c06030a0b10211d0d031b09030f02011803080a02100c0201020703020a0b0a1107052409030a120605040903120c14030f070224040c 67
    0x7542c00c0100c00300540209500c59802046894400000301040129940c108109041c00030000d2403640e807071a146c0b11480143c100865800d0103040303029200d09201c7d00541c445240a00391802c03101c40d0f2182d10055502414401082040740351000c41d10910402c020701c0612000615078902180c24545079540b4200104003990300300800000100610005032080020418603130240381c0400794070034500301c101d4070200c542d00041004400107240401302c0c4e0081646a60811900020080c4070400b08081e0f0a0344035031580100107800c104c0b140070006400304107107a001604281c000032110107958000341c1c20780c030522090700d480e400000c4074800e03074443c00e220f44c1c104841c2d44c0d900206824815665942c078002c1000200500000784019444821140e11010044c10000c0050080000030b040207040101d0815840c0116130512040d0402280070303101603500c2c2210510014a581c1e241d0103601065071001d026142140155020341c140468036480010b52050380041c41000c030305040c074003a00d03012040e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 998009226 1250 998007976 998007991
    0xf0f09050315072a11040209030609070303090b03160c0501020903010204030c030b0105042009010201180f06060e0709030809061210170c1806040b13020703020c1c1511030a14 77
    0x40821304005004000c40103240551000d1207005189101001501a004803100290140706120412401c2003000485800303e07402525100002ca4403940c03c034656100403a000c08030741c0d00e80d41d1600c1849115041440205001c0c4d4001800c29082100181c213a91065005940031182550b091040c0300e01403601500504040f00e04124003031819080c0f4005004106403400c1c03012011030719400300d900070341150011040747e40b100c045501e040e00d08190104102d6074241c070880e2030103202203900c03124600d407140601180c1d2242407403940385558040e00c95020f401303159040202400080f102c0d07031001f4506d5000712200c61400519904044911604403003041c2c604205074000c030210040b039110940701c00e91008062a1522046e40c8801c0824080e1885414403900710b100e003403d0100c0708401e9400742c41e42512039801c1d1400b840030070342006403241240100031600010b0b001501d000800d400d03e004401c01d220380e070103c2c40b01c0400d07007010a29001103404d440f07000c2d21850400b600b0746203d080395601c80403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 998010476 1250 998009226 998009267
    0x11040c091a090f090a0f0f0203010e16080c1b1608100204030f020d081606051008070e011205150103080d0c080712051314150112030f0f0905031507 65
    0x40e040c000f038581c00c3c440d8540f900480b214004104001d1036604441c0301014454024800d2900406004000303500c24494040b494030441e020030f07002c82c2800c0940c151402d095440c0849134031481c6030015503500c500860302c1084011418081c003040203101e0382c458809034a01041200f8030b003821190402d80e40c5007070704040702d00c100001d00c0050009800c001c140c0c0e4058800078030324282450000301ca880f4400d0300f401680d1b0707110840300410610341c0000d07220301c410000c0344040c642e8580c41c16503203214074081d80f01c581c00200010300c0302c2010183c903000300c42d00403012a121824079040800c12540c007a0019156500c0009108800ea102c90280d24000303145498080f0007451311041c01040c07090f80e100d002c10425110804141c031024881c891002050304400344080e03d800f030340010341d0b0320b18140c0e00480181c100ca40c00080c02d0800460034114150f05901c44090207a0b108500b21040074540480c00240321f5440710110b0399407000c0041c209075080c150703617456081c101901c0180040f00e0802c3d20101490 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 998011726 1250 998010476 998010487
    0x10509130b1311031528050a05010f050a030818040213031a0705041202010f051e0301080106210b06041503030807030f020c12070602070f0f12050a0807080411040c091a 74
    0x180303078501e6900007142e1490040c40c41c0d225040048650a11490800b51400d000c1070241d880109e5212030b048400d48128940c0031641c40061089038071041c8000340c58807000344a240c8225450a804000c0d08800410051410480c465000041ca10303941060707440d40580245c417044442042211600003034181071503400e1510340311000180c948a038500a04003d591464840700500460a45441c0e07600c0c04003041a4068880c86055990000d00c50b07402039600b000c10000d04003150350801c00c940e1007039101d00d610802642e182c8000c00b1601414041d0400c0c3c0d0780c0b81d001400c4101460750780c040d40c800e5480440609046200900b921341405500500920410070a83e80340d00000354010503040800c20030391940c841e400c00b01c4c000d0194001c050b2440d503000703149001300a152850412074a00c116410103456405c90400caa4a006000b950400300d61043c000c911114003032800c49501c81d100300c2c078000242d03503d030000c41d0a441c4084000c501003517000b0010b02420040c030341d443d40101d507011005070400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 998012976 1250 998011726 998011753
    0x3020a17151012050f06011806120c05120f010603150c020c0901051e030109081b030319052208250b01032a060203181206010509130b131103 62
    0x40d1810f00c00d122950307603c4560f402c20810240002c0310045842015503040e5a903824003600034860180b40301144a2030003502081100c81d003100040c58a8001d010214030b6810b01c024001540d2841d2082c03202803107642a44018540240100400340d8800e804400300b2100081200d0140c9070208200700035504030480c3d810342c0e40c5401d908039044680896a251048047c0b50a59804150040d0382503099424640c2c00c5c410700a103000103103400d005407152410282e24030803010792207000603103001c4d03010380141405440c40303202070b0040781c1c10581464003206100c03001541038010304210700e4112490b200106800703c034141000984014044020303800c0946070f1440e5a05104c5e80814000244020305055039010002c06521070b901c108483c540d1a4044252a070030080c0d03803031f0041110194540820780c1411402d04295120b40d46031001700c00144520703420001007107450f0400600e40030150086000110114000b8501940034880050401c205210305042007495a00c0400106000740d0114005115a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 998014226 1250 998012976 998013001
    0x10f200309060f0a0f15060f0527041e0b10050a020606040e070f0609080c01030216061a150d0b06090d24050a020a09080c03121303020a1715 62
    0x6400b401c0f4000350303901d202410040a85040080c001c1d45814003821240c07031007440a038252081e985801c02a1860010111440e11842c0c0038009070414a0100840d10101e1880c000102d020040001c03a945007807401c051580e0003204004450f0f6038883e011740255041c0f2004140002c1c00034a041494501c92070400384d59000003500c06400390303580c0c010804019800348050406002c0c2500100c51250b551840284600d2070b50048942c42d000d0a0034660040d03000c2e10840c0d071f2a092810141103045c02a407101001040c3d6000d10321a400d040c0c3c0102c040c0d550f5042c026164409048442c1c1c2e07203482c40c1450040840700d84911450141c0d200304141c403d5036032141854585e25512801c0d078074070020b0040761030038001c01d1114000e03d1036003030005009840e02990090111450b1650b00e1180c02903481462965030109400e985070140c010130501c104c0b5402280081400c22071121000c10034650343c2d404a03190816540c0100d22420040100c040c201c1c002344542c8020180010515146051200803440c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 998015476 1250 998014226 998014231
    0x15021801020d052709130501050a09170a020f01020a050c06010504090f0209070c08070f11090403091401030902030703052802150309100509010b010e010908032505010f20030906 78
    0x40350b03040c1c1c40300300100121390b90b0b0640c0074400900961403034103144004a103c0c88031518100c40340d50811000175800d82c0c1c2c902c41c4148050708150a5113035103002c0d1411518a03801151a9001c600445070000c40c01c01007400180012182c664580ea82d8001c0354042e5420301c64113030400d034407440c01c1c40c5827800030400000e6101020b82c1c04640300384007900d0f188070a031070800b6154001040083c2c00700d40030007440f0026844100b040e01a5070100058181e10042002404040340c0080118241c000300b44a440f5900121201c040c1040c1400264800a0b4000916000155100b100c65a0025061040503c00708020004070b041c020070b16a20240c00740d001414442c43c005500450080120010761180781c10409404000d500c48010000340c1880300780036000c0d15a005959010940c039a0f080845944103008460850303c265020b1428840400020f00e03405c2401c3c0d03641807034000c00d04501d5000ca003080c410b0380e4810840407000600d40040c415180000c005040c1e2041d1012010720030003101140110701a43d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 998016726 1250 998015476 998015497
    0xd140a0e0a0e1f0806130618080d0e0c0a12060908090d0c05121612020f0604060306090b0d2a08030a050315040203090706110a15021801020d05 63
    0xe500390001080704032019600c02d0310580202c0d414840180303d51207154041280251540a40f241c4440d8859680c45041d030b048410f00c540d450700d10012540c1a440454214404195890911a030381c80d211080d820144100880341d03030741c10001d10010000c00014003030a0b816240000c840b440c08072414241d1589103005030aa50301c81d00176404011200c8221214401d004206480b24001e81c10518240c2140b4043d507400341e402c6142940024400041c100b400d01460309505041c94204403043c182c400300100120382045403000e400099588450140c13000d000c0b81d5038009115460400304100f035a07400e545007401165130a42020108080005018115485540c58903541448101c51429030700558060700e41c0d030101003540048154001c0082d401200301c0c000c81091482c1500070070080b440700f59405503a07503020260404c180c50141002d41c41d0b0382140c806542c7d03400084d07203440c50a1589a00e41c041c4143e400680000704159840c5c0703406044c1b0302803000b07010307038106020054824451007140e40b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 998017976 1250 998016726 998016737
    0x40f1409100b012705060a0e01030b040213091d0a0b0403090e0c070809011206082a060702100e043b06062407030305040c08010b0307270603140d140a 66
    0xe013007140c03c0c0c04100c000e040240120303940d140b51800c01403450204405940c0020300742130000402d072805d40252035401c140c0e800082d080c3e41c90300301441c00030700a41c010280c0c446015180c5980c3c0000130700000350340c00c1c043c4500003694a4603160040c014100c940240c0300400d0080c0c180310030304161205482e055540507005699270301034040182d0317590f104081c0d8042e00e1410084049072002d00491207040103400705841c281307400b08030070003d141002c20300343e40c981001e0300748480300241c58030396a000100300290400301c046000381004a0300b0759801c0000b01d503d00d00c5c1402c9081118000030384500c00d003002030100035248038003420701c2078640c032010b4052481460300d140030050f07407010301d00c407202c0f4802c0ca0614255203510b5403901034090002200d050f980c81805840000b8282018007c5044181004001c1d01c070306411701c18800000071000003200b200540d0028200301526103442a0000307140215905020b40100541c0140350141d10422281041221114001d0411540d000c0d81d03460910350030720 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 998019226 1250 998017976 998018027
    0x6070906020a080703110a05030c010f050412081009050a1e090c05121912020f12030712020c010c081b0a02060112020d1205090315040308070c02040f1409100b01 71
    0x41b110004002c15500e02070184507104030400c40d0002c005c0407407106020017031162014401e1014216070b070481d009418465044030b011030b1140302d06540c40c0c0c01049502c140014640382d80800088035412104055250742e01c8094400138842c0030511150030740c0901048c0221042d17980d450701c004030b107841258000c0050820500040f481401030f0940c5080d454032520740b4001c2810400d002d20780d403850003000360080e4040c00400c03036804155407181d01900d4541c5031030f507180d00300b003220b0800d043d165841c0659400c1c040c520b0540350038000d0189035001c0340d4030003c2608110141c18a0f20150101c00c4042d40f40030401240f58980200d00b85045540b200c10100e1969114000300d10710920b410001040741100000042c2100d42000151100c01800d804407a01103071003805512300c1050a5a01038003140b40d080c00100702c584030700000f5000314805040400da6080c102e0102003559401086412150241c0e01008540728040002c03984020709050140040040c0c50b0020b00710006085145c40c52162403400c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 998020476 1250 998019226 998019233
    0x203011d06040e03071a010602070501020d110a0210030b01120213140612041b08011e1a0603090d1418011b0203070e07023d06090c05040806070906020a0807 69
    0x42002e5a46040c25280d42d0b035401d107001b0719103008590480700b201503400008103c02d84001020401d031001a0010402c941e80d4000a0300d13910f201c20100540e610503008a18016214290304692140d07544c0c07404540b0f000700100252110004200c0e401c04503205000c14400c101241103c0b4080b1403044100c140c0c8012107002084580c442c03100300498420945061204201a0707200c0b190a4800c080b0001180d140c54030019402e072041000507800071448002d4400031400e06610100030003840c3d003003e400071680000454160303001250768030f00c2c036001000000441364000c01c02c03040d00c8440e480004d00e03001486030b8025800641712205410802102e41030021801d0b007040d230469054000b8116054155103131041c403035100044a41200501a0740a1800d41e58a5071404405000c8040042c8840306840c44c0c1c0d01d00e1101c1020b08039240552101070000c1c0300f900c00c0c8541c218240907561903a548900f010704041c80c102d805090a01080450700e0b0030411158040b030110320b800e500802c01689d81e2400d04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 998021582 1106 998020476 998020481
    0x612120e01024306140c030d0903050c032703030a0c08030c071a06191520060906220302031207032702040b040203011d0604 55
    0x100b07103d031104100c0c1401d4807801c40d40105024414050b4141c941c402c440d5400740229081401805401c0d4402101c4442d2003104105510b400841c889007503030b9114031941c030042c0c643d6034600401010301c600110303020600d8520440341c4a42e14402002c64145c080758031800031103440392807460a400d01205849200e15140c580d401584c2c050b844405455000500303a240071070040081100103800d648200055940300061004d080c5402c5044c440905101130b0b411710000b08580341008055540005548038a06500d040e480954103168244100668248660214016034040080344580024650311441460340c141104850003540340382c0071024201c0107030068008000b080020300900c1200e0750810010301d1b000a6460500010505007001c40545504841d90b00c0000d1066242074003410401e800100c4046145516001e001c6c000040d269110032039085004000682030398865 = true := by decide +kernel

theorem cover : BRFrame.Cov 997841726 998021582 := by
  have h0 := BRFrame.cov_init 997841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 997841726 ≤ n) (h2 : n < 998021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
