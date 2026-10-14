-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1164
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:32:32.468991+00:00
-- url     : https://prove2.me/submissions/a7080d20-8d52-41d1-a1cd-cf2a63983b33

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 209172661 ≤ n < 209352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 209173911 1250 209172661 209172673
    0x12030e031608070302030d0f022e0e0d08010e01050a03061a101701060302030c0921030c010e1b03070312120c1e030b1f050c0a060b030d020a150903050c 67
    0xc2d209944400710b22049000740108070170710810034090b10002e00030050035009420f12103590b20340c10301240101213080030410910155554101010311588002d910090000c012861095078050325201c1c0591200070b40d0350a0600510417501c840c0300b404212a80058003058503100c4592440d91680a9200a80c1060310110003030042d0741d002c1c0e0f000b007103c80c40101040300c0380d0322400304400341d1004642c031071240001000341540506110707001e90b8002c00034265044d0040d240a1403942183d022a411101603915400a45c403485014481e140e0420107110101c140c480840707010903104c0ca424800039155040c03480d480c61480d4055851581e00e013071600c02c00c121481c54520301505250111306502d89066042d8840040240240300e1807120b100c008226210f071482c460108035000e054620404108030381031043d905000000c0107400c80740340c452500401c042c8200c60515161052008042046500c109220004a80e13204841c814030007a20b42e0112740e1701000d0806860303901c1072101e40c101600c950 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 209175161 1250 209173911 209173919
    0xa1407050f0a150b0a0b1c0908090a050406140d020109080601090516050702010c11190902030103030305221211100f0f0c021506010c020d08091302030112030e0316 72
    0xc120025240c0c030900b80365003100d20031010b10f02203400050b000794008880c5041441003c0014018044406600c0b00600d44170032110726070410b80e040d1600840b2802c50100712140189840c0450b40040c01094808006c46d625101580900092650b500da01030400c400148043d640300d2404040070b850306104645503543c0d16003507840100300448420707400f00c0070001c0d00041d25118004032056907805139a126281902c0d40c0b2004c0385562000d0055602030400754a42c90701d501218034043c001c01091800580b2076146040c042d0540c0d00c0100250340e4441c46145000120010099008140350040c1c01d40e0080c00402c00184d9150401141e001400d01c50014a00a001920303000011146e805040a1142c43c941c85128025036020035030341805600030300118a214541c0f100b030310703038080c0341403400b550301180d25008943c0502e5195000d68528100003049102d60500207400030002c40742401c118515854602c1ea998068010000142000748048080c986a86e00b04883c0742042c40c1d00e445034080700d5a07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 209176411 1250 209175161 209175163
    0x702010608341d040201020c0d26090316031703010b07060c0509091617160e0a15020307060605010c12030e0a0605092508070b0d0e0d050d1b050a1407050f 68
    0x1204c00701c0c010303c5030803411607241c20140c12110100c4c0e80b040032110001e4906e50310f11810f1141220302201581f007031044104981c2e0801904800040680a24145604506140a0010709890b10b10070030311040004100b2020f80c03c0c100c452071904208006050340c6960720441d49442107090031503000340a007041c80200e000700301c3e0080f0402d540c0e03100d02450000a1070040e00c0c00b641121001300d4020140c8000c0d0b00c1da07016902511412800406c00d0151580720052581003012060355000140c2c400304018042154034407500000d0582401c241c1410f00442d03550038810001d60300750004140d202e02e19100100d030100002c01b40c240d84280148041d2a00d0141e45a86492184220449601c03520a0110050300075284005503040d1501421005052003e110025400520088201650391101c4450308605004c0c0d9400440703290b45030760b0348440402110041e1215800d56060b1001422494028a038001d000c035440c0d14501e0814072101c1e41c02c15034100d518065044060301c00d00a600d8020340d000c0d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 209177661 1250 209176411 209176469
    0x90522050901090209060105250501051b07051b04092a06030e0703060903050705060a14010519060f0c080301031a090a0b060d02040e0f0105070201060834 68
    0x8120902044141e480350a07607400c1ea034402c0b001940102040003c20f00d43d51080b0300801525919040c44860034404c80a04a82c0c42c0411034141c4159540c0c1c07007404010840c403140e68082d0111070f00c5081c24480140c40c0c240c0c0f526803641025803600450602400c550311541c0040243c40d401204200903d0031000410950041c0c0428155810350324074008070b2080d00038030600e200c0c0d4441d400282690341c11176403000000c108241e4244e06000c804e0202000040b41000140c0c820030300301c0b50124003011a110040d0180700180c1000e1310802c0c400c002881a241c60100d5201120120300c1e1502514200b0f07841510b00041a01b00603201c1900040080709100c0c0b410b030b110010040c90a581e0070950313a50303807d46450784142d01c0001d203d0803400010640704e16065414001e102d0008200148440300700c0703d4640740c011588010701c2a42d4440081050840d028030035407000300050809005040c0f84111800f5480700104043d145102200703401c5d8540c15071204840700680309600d00000502041149005550 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 209178911 1250 209177661 209177719
    0x604150b07030e03100c0c15020c06040c091407020318120307030507020310090c14040b0d0b040317090705011202070203030a050d051506030a022d0403021f0509100905 74
    0xc4120100017102c4005449000260044c99131565800d071480e80d282e184c03003d00502604072041c1c003889400b03003060040c40094002e0740308103615130b50b4600d05000d00040e503160240190205801400300481c1c80d0b00801120045041c02d5405407142e040d07540010300c00d0121003128030840c4804130b0321354100341d00309c001004047d0080302140d6105e41e0403081041502c14801e801042d20002c80001c0000046155904942c03240040000c1031482c0d01e2b602080b00d212204c0b0055078020450700c2488203242c1c200e00c800210788500c00300c03103107a4907104100c282c0e2a0034030f2060307034104401140c0c08000e0505036030649030b0f2950700078141c0ba034580d6000d400a0045c1c101481c0500103e1420000c10600e1188048148180c41d020745480e080d0350364141c1140003900000038011700109000124030801c0742c500210360f94022103a100b99111070030341c01031140c24030490140d070f05c211180703c0440c0b030280d8010041d1040a541101c503900510310502c4220340d0404982c1c000c58122030000e10220100c0707064800908070b2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 209180161 1250 209178911 209178913
    0x8030d021c050402060405061e03100302040f0510061110020309160b0910080a140103080a0f020606030615030a08030a0903031107021809030403050f03030708100803030604150b07030e03 82
    0xd00c078070840501111002d40d0000e41c401000c0108101d94144600036154040b00820340b04d080b0440c4250081c240e0340b003110070076800003003004240110700d440e1095000011206208200e149000524480300040c03034007a40080c02031129000381c04030010444020003201102c019503da0505c04640c0740e80707104040020b07176448142e45020540d405204165500810010403400640710079490946560354058080d070b00090b11024825a004000754006000754400c0c030718203944602c07011000b003810450110040454000c4801c0c48180e1b94002905504403407420440d8402e5410a00042d02d007407120fa02c002c0c100d4a000c000c021201c1c40650041402e18042e49081c07082c00c1409110504070301c10321074001e50040c81403000620f126440707801030344e000030401c084030b02d055100c0d00c3e51880c014002a001a040c0c0c030000400080d59444000560015002c41603921282e05290340545c403070100a00440c00351340d032890742415a04078a0b400b0001003241c203401075900c3c0d0180c02c0051000300d03400c04050003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 209181411 1250 209180161 209180197
    0x50c0306061c031b120e01120915050c070c0f1a0a05030f0a020c150103021801050d201c0219080d051305040c11060702060106050a051308030d02 64
    0x4142026401c010010b8008041909110700c40c0d40c05503145071100707134840004448400b0460000c0c0315250210504140d41c1c0f6038140303100045000628074400801e041c1c801508040301d18001400001035a8074a41000401189c1580e59911460050040c0d903000780c000c0400840000b450f50300b21000006481c005e100308a00e114984696070907a02c16110414001481007000a01c8424040c00c9641c026908c50009450715940781800c5181c0010100b441d01c02c0591903004100710300e0114200720038513420180e14220707580b4000001b00e10f000c80c418082c007021508150030b8802002007070220030943c0d00504110f404400f07071650140c0c000b402c0c20201d0003211281c1c038045e031500007500c0210465640c88000d0025411200741120341e500000d00d1275190039031103c00030602d561039001d0b5181c40302c072940d01c0c0504045003407120341c5050300c007400d0107041d50046001413003059802030480303400000f103080070707981c54500360b0807241843c0c0c0a5020a14074000030070540c0031880190018400f20b4450f07d20408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 209182661 1250 209181411 209181421
    0x10906021204050606011b060903120c030b030f0c01050301060c110a030b0a050f060f010507020613090b0a090905071202130614042307080403020f0706020d030e0d0903060e07030f050c0306 83
    0x80900d4240b008a0308002200d05001c00112141c101402740d600c20318010001c00c40d0020700000707072203800809001007a10760080d8569170034200026290262168020b1040e1703517003440060304922060140c0c03c104001910b844050003202005101034500203004103a2041e52030801c0b6a00307000070780340c8446c1c040c10040410f01c200080309006004003801060225650707070b07502c010744269000200c200e801100500201001c200c0b40d04c6040000c20300d000c4046482c0c1e4a08040048100280d002045c1c0d952a0a1900700480c40016030300043d55510608505450748074000500c4802c403d01e050b000003400d00c0d80100d206801c4c40401c0d800a0b006681c01d0101508100c0309490010046040f00e00e4280300c1000241d015209804a40d0481d00a0040c0c40341c000c00b41c90752034100723503240d00042c01682c0300e00510120290706100751042420340c070002d485040f0300032500801010040c80060030390758461040c0e0310200010321100001b140d20008404180c0e84070710301a5110030071802228803a01411000070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 209183911 1250 209182661 209182667
    0xd0507031101120e0606010509040f02030103060c090602030a08010513090807050703020f0f0f09130b1003120f0806130f02071a07030606050f0c070b0409020c010606031e0e01090602120405060601 86
    0xc102d8030100117450250b89041c0112119040601801d0b4440c0e1111401803000010344000d5000e14064a00032034103024820010705024003d611100456000700312010303035a9800030250b81175880888010b44503000c85500e040240c42d1102d00904000f80000b450020403d0005164040368426200010585150302c200314086452034031581e04804000c0010b186c0d45400b044850307000c84152200c20440071079468406c00440c0031554120400102441841848020b11100100f0052440d08088014160000601100015200501030f10198008580b121420f4120690b40d07010b0b5181151070b11128101102c41b8000704120320360301e800c04c0d1301140c0e280703100e4000e0005882c0700b40c82d043d00e031191116011541390301c808100101d600500b00045140d0340424011700c01090043d2015807a010041000c03400c464540c1d12206c1407610345220444000140d20b132050a2041516000488614207191036001d041070a03001032074a8070001d001c0040103603e048072030103a03008200300c42840da0b54030015 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 209185161 1250 209183911 209183921
    0x5090301050a021c1d030a0503070305060301020301030c0b2109011d01050105090c0315040c0509120a02030c04020a090902070f14070e0609220302012f0703030b0d050703110112 78
    0x40c0d130150840b507402c8651010650000440ea203e81200104d05042900c180c1d402c641000e045400081c20000c01d00490301d51500072941c00c108114000c5245516640d10001c08560b0391181222003c07000c100303d40100502c003c914130040c80b85018842c0c1d0b01e040010107000700f04411014105001c1c0f80c410540045051213198181c540280881780c150700c4104000c42c1c1508000d01100740340ca201320141103070313490300d004000015010792100b64a850064042103d0149841705801180e8400301004025941c0002c0041031481c0644d401a0390f4181c2c044101e40c3c48119400c48200e1500001e4803100304140c50100d20b010a0007080703828000f98001d003000d900e0782550310035200071035401e034041449803504c04002c80d003140e030680405603980d4840034a14555030703070b100c0c0540c050303551000c281c0380070700e040c81eaa8202088040c90312414881080410003ca0203400c10140070103594203494040b540301e5283c1c64400c55041002c03195a25a00d00d081d405030600710b04041c5c00501210b1004e40101a0f9000b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 209186411 1250 209185161 209185177
    0xe07090203092508010903020304030c0b030603060c09010e0306091005010608070c12030612060902030d0e03030d0c0908060c0c0706050a0e0f010513030605091c020a03210c05090301050a02 83
    0x1500c2c0300014115a11203e261007000c0c0e5441c00f0074001c0015809000b445040710444c4070740c01850301d0394650b0030000f4042080c0c0d0300c2031420368002c108100722a40c001c81c4041d0b00030070303c6000580b10034130b800042702c240d0f400f0600d00e50103100f40c00030722800160004182d0340481c5002410700040c0e0b280c007001c42c3c940c0c50689201c4e002c1100c84615400058102c0c0f0b00d040d6950b406c0c070340007403080d079121511400d40020503000e4800da599201240190b044c280f085042284060030050f001e0003200000c03a560307214446000c02e44603500d0245100e114846c41210004003401c004a40d01030910700060383c500c0d444078507810080e01c03401c240081d002d8006c0c8203690341d0710840d4941c284024150801d002c8084c0380c00081504208041045240e451030703401811014500840e400140703464240c005c54a000d00d003a460360901c03902842c405002c182e0020705403038459070501c1c10100f071240520010920192071040f0340340450410464031801a07001000d05a2954103c00034062501d451034602d00328810141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 209187661 1250 209186411 209186413
    0x4091503021c05011407031e0204140108060301110a050a080a06031509031709160506180d05010603060903050a03050601080105011d060702030316030801090e0703030e03100e010e0709020309 84
    0xb81c0540c0503040c40d0809500d8050303030012030041c021082e1240c800808480c10b401082da10192401440d6800190a11450f07501c6411868903080840012a80708955040d504119480d400140c0c25203082d0403001a540140d44a55211120401c0281c55900032030445000038103a100040c03005819400340c0c404894000603a03911282030b01b408034015100c080d60a034103001a00030309400000d40950102c2c480e083c400080c200343c11900d0b2010a06c5100707580014400c250512500c0804010154021700b00c600480e2640c0c242c800324640a805000990300c0640020b14042510301410782000040202148503541004070b40d0b0b03104010b60b501b034001c0c06080c0c006105501d1f6159040f46194220001403c000c00140c20885550b000270700d1503100c2418403180c0c00b02070699038105504000c5050241c000e044041c0458040e072880da40c0d0302c0201d480b001c0d00b00005000c6110041d10140200d01100301d00340c00a201e450300c807010b4580038000c8510b490b40e0620074054000341300000ca1007528003841c1184 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 209188911 1250 209187661 209187679
    0x1030b0a02070f02100909060801020906030a0b010c06020a0c0b010602150a02210901020d05090303070c030c0812091501060216030b060102160f0509060d05031210090204030501020409150302 84
    0x402008025080b6000840daa11200001c4001580d0b03540d001c0342e0a081543e0f00c1220300ea0404003042c0c241d40580d4018640c81c0e0050214210940e02c600989500c040901800a0704000c4000101d690684405001d0411880080e0300301c2e03400c4c0e1119100075483d02440707903a00141d0b680c00c0c040360b607819030340683e01c01c1551080100d03c942e8210340041c4203440c00c64540c8a500003043d100005007120540e1080c401d603600180041581c01580242a804010709020b50b0a61806102c0540b101c05a000000c040014000003081000301080136610506440840d124a9142800400d5543d016580f180450030390090300006149100084407140c860300390b008c0181440c515600d480b08180c01505c0541135004440c020605030300440702440040030311031840d01e0141c0c6070a083c03103081c0d400901518045c0e40d0003403090021690002c21a00d0900d0545e003c6a120341d0340c95840c588000032600034844881c0000383c00020700c081500540203569100d082005080318410300840e507a034803884004d400c11109 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 209190161 1250 209188911 209188921
    0x109140904062c030304120305010b0a03050c281d1e0303040e04201f0e0f06160302190b18030d09031d0103060f090b040f0203070c170301030b 63
    0x15800010003c0c80380210a1103c840c5210103c0c1001c4440c207000080e81e0000c0100010700ca51840d214420161600b020807065042c04001c0450f4420b000c04282859200d00100c2e440c010254119a22000c0c0e56404442c00d801d00c18422020800f1070115100056071855088510020f11400e01c0400780001c040030200d1402e42940c190042e0103160807a4940418800010304040107860503108a05c51021079011710b07401c1d4004500010f90320002ca00810751000b003003446d0303050141142031186150a00b4100d00b601000051035100c0100d05031600120040b500da1078004101d0700412050b8825000d9885040c811a449410706501c3d100c040d10104482c0c02280c80c1000241c4654800250181513a2405280c0400901503a040c101308070700045120701d0f8082c0ca1289500c8900500209103028003801d0710380700030080b040d07400b401004103103991583d185d001603840764000703560f103422060295140e181c64500900320110014040d1206180f26880c5541203140a00700d80c11b890340250310103042d49030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 209191411 1250 209190161 209190173
    0x106050a09181a011d04080703030b030a0c06051306050c030f1c09150507020f060f06010509132a02071e0b070f021e01021b03071703090109140904 65
    0x50302416a82d01040c410110200b8420006003002d40d442e00070020b80ea525118a2000180840d106900d02106900c280000109980200d80840b42c05180114881002c980040e041c0a000380c00240048101a40041c0b070f03a8102024207403074402c208030740644642e1003406656522440001c0715594000300885085000c90102424100e07101a050842540c4000840d01c1198000041650392400518500340d18084500980750301650f20301c0a40741e10910446990f5032414046c00b442e9a03940a080001c111348d100f0340a0710b08850000300300141020300f148504008000c0700e26845000c82100f0400800040c81d03099a8141e01655070091086c1032509100604140111031401e000c6078889400107140060080034000560040303000e10301f900004d10412a1640d18807620f8041107c099510090316078001c1243c0e4800b0310707100380d03144685044d000040d003880f00d213820070719514404c821040160b840000242295000a8850b141c90b991180d081c404441005080c00f40d02040c084000b80019074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 209192661 1250 209191411 209191421
    0x60b240412030201110d0212060a0e06040b03101508010b06071a130c08060603161406160606060c1103030304120507150516090519030320010501060804050f0106050a09 74
    0x102074800020039000d203a170407000e9507104041560f00035402151903240410004903007a0401070440301e2404031494000751500e00a401002c10740309540d01c60380c000702070310b06200180c00002c040e8810051030400c40441040c000003402220b5070f270341ca0441d41214a041040413524080e8000c1d2180c0454088030814500d51035000f807205071007001c010326840000c0d24459055021381060000b42089162135000c2c10315140e055003207680030707020000c000c21204240d220303d980108401d03110280d40d0300404907200b003c00500a40149407614200d00018110350140807003020a01c68040700060301e800d882015524042030324041c224100003500102001e00440c020601c8600c81c5c01d9810208207001032800450b003003207408020b41449a282c08046542c0681d006014041c01c483d10307407a410300c000c0c0b400001581400300605000005031044182c00c01c0045a121154038000280155a120b11008040c52404e65080b5441d20900312407151519044c080d101c142c0d480a00220313403403450000c094010301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 209193911 1250 209192661 209192663
    0x27090408070302010b091e060a031205070317090f06010b030c09120c12030a020c0303040e0c07081c0c0807110a122106051219080d06050d060b240412 66
    0x5035130307180100015203030101c0a82c803031103020180082041131500b400d03e0f87d80d00100340f80d200b10000b01c0280001094600c5008407440c1529203a521410035250580703007204100c54582490390840c04000c003401000603040007110912007580c3d12030342d071034030300e05607a01003038451007078a10050010030810b0412041400320111010701700c030b203600750710000304688542c401c80c480c4180c2c2002400701042a01001481d841550650007185824074100c0032002e809030180848151070700002d140810f010180d001d4440c87d00b501004408900c103000e903408010100d1141c850003040364a0002000d85001d183c8007102c2410600140095183e00c0d9140000e40990740c8044080c0080d000102c0c1c148900f40d0b00442843c42c01203000036025007000b007000304580c1c416003090307455401005032000d0b5541c4012012040e1740d0000006440b50101251074000c7c1056030865500700c85122101014000b05070000e901d03620090310203c0040580704244034a50100c24042da406410402041000c0440386120007402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 209195161 1250 209193911 209193913
    0x5061c0507090e070c0308012702030916080705031605030a030f050f0d0e070e0c0a080403020709050a0903031d120f0408150901060801050f06040f06050406060527090408070302 78
    0x80340e20fa030080644400142c4254001980c4445d044040680000303403180540109001c000c1e0150700302c0300d00c4040404c904410304000b82c000c40030030340145d410088903d08074040759000c5101515164140d6a411140c490240f007032156280c14010718a40c01c504800742c41c0041c0107040b421105440036200d401e039a98200d07041190401c028006403856102a100e080d00c661808184450840001c07031900c6065000300080d814550240090490094210b880700aa03900740801c9654a0342020ba0030003123075601402c1e035036003440c1c108840c00220343d004181c0f55101341ca00700b00c5c642d003040c0c00c0c0b0095078051000a01503404565840580d1688102401a40140026461600d500e40000d0ba04080322800d18000311200e102c2402046a800e003c0c4002070280031000304a0f9242c00203071250310100180c0014003d40d41c07142d801e00705184d16008480504000390040c404180d403407030010300c43c2d40244400140d0030400c80c000c600b0040d03100403110241c6030041000c085601d440c1c50300c4401d03a00440c2c048081d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 209196411 1250 209195161 209195177
    0x40606060e1c0f2916020a030c0c1505091e0a0504020919030b040308090d0f0c05010f0606050d0e06161b051207121803061e090c030c05061c0507 64
    0x748010303200c81c100082210101d660360488a800092030103000c0c01c40c6483c20417072032a1040e0b0303d5000130304980440c3c0502e0445503800342d505019402c891140c102c4500625a140c4455205422000a10314410103036a124812000003000341c9104c2c00000c016a80720309540010851450290041c008801c00100900e000d112001c825024480850b80101d5124001000304014190484002c80c0e01c00d084201070101004001070081584a111030130406002c1c0074952003040c4038003580214000304c4241c00400c1165162200580107810621100380b17140e003045102c8040d00d4002c28014000c900700c2410382c80d0404107840607502d20040d9a81c55042509054454002c140100141c00100c9400d0603c41d0b070340c40c0d060074070724401c0c000c42c1450340c1030005c042d05922100c20507101d0f02c02180c0d046a000504c1240359003500081c0c2c5820f42d84101d0990420f0340f00f009020071090303000308403446120304040c1786645400384105402490480040d4600e0f4030508140c0c0003454000c1984006985480e100e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 209197661 1250 209196411 209196413
    0x30e030c13110408011805010c05070b0a020d09021801030b01050d051905120a0906080a0207051902060c010c050316020c0604062321060103111b010603020303040e040606060e1c0f 79
    0x308440e0500f40c10500303641b03c2d094000c10300200b8401d50104650a15020740390400e103444502d001440030706202080740d40010400f000d542c0c01c1d84800c5040c2d030700520540c01031241c02075410a8900c2800305036030080801c000010039203422507211800c3d43d4000050f0020b152a01d0b030155500c448200142c595000d044242c60b000c40e00c80d001020600516240e041c3c2250400000404000004040300b286034410084400402d41c0024100021a909101316410b02c01503c04207070503000700080c221036507082c28000ca05a80e0408055485201a9403514404c511001c0c8204ea562003074013451134028504020604c140c1c0d01c07428058800101c0804042507845100071000c200da48441035019400c40840241d415100f800c3d42c130304e90482024a414880b4001032141101c4501c11005000c40050302e0044046106801b0740010740110b070010b041c1c0c0d0303d66544958103002c2e101c0c200d07800c5414918216010031284c0c0108040002d042001d0074100803404498180e60394501402c00581d10f803406024904 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 209198911 1250 209197661 209197663
    0x50402130204031209050f01090b1b0601090606080a050103030f0c03050c030a03020306030c090402010f0e0a05040504030e03060a1b08040318090b010f020a0206090904150e0604030e030c13110408 86
    0x4030096104038802582520b40070b04c02845880e441d000548105981400c000b00b83c2e80c44030005040d00c8210712070a54444240c004859103554015003081c490080c50300014400031183e000c030045880f6500d85425640e900894502126000d000c01030100f001c801d016403500c0c0c0b1a0301208040340c801d04210345800704000050f85542c1044103404000f0f27800208200007400d05104505520105171603d80c000e08040d80040c104644240d42d000800010358042081c5a450aa20781c00030b003c007800070000342c10541402000120005c41d118000e100700c202040e08940035103c2e8940c08500e4a4288600f8003903414202d80b00b0700d01401c01d44c10450507c4020340e030304040c3c445030b100030504208000765001800c0005061402c4003c50041950860100da0015840d030504903041d9050807900b80000f5611483c20254680c00310b03d803070204500d08100d1001020000076250302541c0203484205445810008059840345541080c68204445040c1e00500022a03004079802e42ca002a01f07a003850344400000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 209200161 1250 209198911 209198917
    0x41406071a04020f010f0f050a0c20041409070510030b030f07030506011502060406091b0e0411060313020d171606110304120c1a01140906040b0f040504021302 70
    0x10010041e000148002c40c070b0072081c8054200301c20b08010084405c1d80e04054084802d0080082c203209001030301c1c081d0184503940c0e148070783c0d074008223040001b00041c1a1400c21841c01c650a8040c61800c2900c141240f0301e0059a4404d201c2d01004000c024142800d00003164100c42062083c540c8800380f0a065950503c8003402604410001b03188a0380b56003000703854001c040c0e10401c03107200c8d040b8030075019542c0071541d6a031068001d04c01081842a40c9000780e010362103039000f440417181009000c15150100454107002d41d00810348010704107289010000980700c21340c1d5803940d0361403c0030705c1e800608202c00309180480c054540070403192840001034200368069020180c1c03811040340c0660030041148103001d540c1803483c1d0f40c2070844c9000c1c1c1d0341c1d16012090303110140611408a00e500e0811002c0b83d00d1040301c00c1d841c81091019651404d40d2060b90611900741441031000f040056001d007043e101352903010304000c10700008203017110705104c01083c0140040c0d8100720000e5540050146034002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 209201411 1250 209200161 209200193
    0xd020619020d030c021509030408011506030f0b0105030420120a0b01080606061c0204151e0206190b0f0402030f06030706020f03030a0c18140f120304140607 69
    0x12000100e040c00c0e0000e08006400c1034103000c3c035142504100b2010350020700c800500c0c1d201803a081d0191113000105c0c1c910b00640d03224112540c02c0c85140418203003a480c040c1c04441044c1c0b41031001402c00c2a00d24242c0d41442d96403800a88140b0008011070004264682290000d8a140e4000e02c0b403000460604080f035200107226610a001c00300170000e180d0840c80c01020210064a61424854001040d5200c1e401e1212b00700b820500c405190b140e2158100d80040824805200d81e4141e44140a4600d40061440011200041003d070840c50f0001c1101803140c0c1c924291520303004070801c8450007c00282e03e03202c4d007149a50304502c141d91203510080d0300030728400340314001c58540701d010589018480d81000701150010002c11000e9a0004141c0c0c1d08050755404c0410b40c09203200c1c0494002c0005001c00c0002f0f180f0450002e0703065414840036004080c10380d0480001600f060030701000e130444014941300c03580b04120800c11560022400030140d0300082c0f0240c58014292250a0700100c10f02d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 209202661 1250 209201411 209201437
    0x3060203070e15040614040f03030207091a1005130f0e0103110d050d1b08030403030516050703020307060207030e09090c100c1e0201020c040e0f060a090209010b090d0206 75
    0x30034000c1c002e800c80d5000b62110700072140603036002000381a240d084e004910898042c00740c00308201c084400c1d00c10a4034050300340001031800302da07a0781c00d00030740d10030640c46030904607850310028a288001e0440c1d4203811000c05811501c82c00103405040f1070680c444803420f503140c480f2441c0071884d24903400d400c0300104418440c10310a0750442c102540146044081148194040c00000d0000782010551420602050074030500004040c1d4021040f01c1000100134843c20002080004064040e4401f5000c1d8480c1d00072140c0d2403038480d4007980c45214581014015910900280002800c03a4009012891103840c0c0f5915022014000c9922444184d4084ca400d400404842480e401c00070134244000e000340c9800240c0001944034942e152010641c41e503104c50000e191603080d6402045000fa200030081c1041101121500d141d030b481e00c6800210909500030788000c030702170301c8503070040d0115650010000041d0340d207043d20040807580b00f80d403ca900082c001e841e510141e075031750f00540f8003c40c201c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 209203911 1250 209202661 209202667
    0x2011b02011d0303010609030b0a0209100c050106053010110703020f010203060f060901022b0201050606031e180102120106081b160201031811030d050403150203060f0307030602 78
    0x900402110708803801d22110f40d02c00d10040202c15481180d00702102d0b000745000c8003c2d103444044901911a00b042140c00910030000018070039405a0385042e20345c00b81c00204403807915a010000c0c01c2c0c402d510380070b0180c00c68001c4030504001a00f01d040b15900c85004880b81e5101d03607500e1505860507008401c84909d0302182030802d054061220103074802114000f103295262400009800c40b1088200d20300803c0042a109010790080210030307080048030125100d0120920500c10160020381c002e00019400c01011444908001054a016180e040310340307004182840e281a280b03120042c8505d0f07402304220345807450680280700400000704141004c05071981400f0010701a441c02501440c0031242c804105085c845106d415100d000c00210070620840c00e0600040300900040d0702a005030724429203000b41004104410303a0b00000702030b801d43c0c00400040000b40c90324020b40c407010380403941c1c400d00440700365032940c01140e0043c03000f480300300c2c080003400103e40b42594540003214550340c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 209205161 1250 209203911 209203931
    0x2102040507050a0f05093012030a11030915101505040e01060206060d060c0c21090e04030c020d0213020a02060a0b0301060303051909030803150405130203150702011b0201 75
    0x1106403c030035800e01c2d04005190910b48801f10b184031000810322180301c5120600302c080c0300307001e030580b005405000c6e0807940a220368200c1d003021540300f0b54440410614100c00f03808800440c0341900c0c07269100d40060404400410714801c4506c0e0000e1801c04c05a00c80480462a41c850740c000c141c112000d5503803191281d046c1200e035200843c042c4c1002c42554480030400c4400c0e542c07c040016400c1d800340012901040640d4144c0b40040000c2d4000d020352000000803800007840b00300312a080700780d5901da14410b55902800883e120003690041e0004241d988140301500304a004103420034405030010035003401408082040b17800c51500380700141c0180c0e01344240c0800300d018550b80700000300c008200261440e42c2c00351440c800c13a0b00c203000000c40801d85160541c0a400076100a5822100141d40d034503001c00760b40055442c60f0f115500ca10300c0d1101040003a03d0b030703044c4884003603400340090000c104848600007010000a00e011b08540d210380c05a21b41100603030312403119290903000400c00e4400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 209206411 1250 209205161 209205167
    0x30a0510060e01030803041419110907080408040b1c0207050109030201052815081510091a1c0221100504030e010507060e01020a05040501080f040503042102040507050a 74
    0x1807030b40000241e1000c00010700c04900c40008903500325078800351129803450340c25851270520102c15030141031113030b041d28480c00340865801410110401200c882003180d82d210070030790b2008400e65014020801c14401400350300307569001020003da000300401a031141044484050340d0041d0012202c03a5102e84600003016024090581c210b00303041c411054000072160240300301401c02540c1440c040c1c81c1d01c00200307140385100390480503113660415204c85c0302490301029403802080c0d4000d509801440f90000b02c12070507115a0300644013034500d800041035481c080004181003500c141c9910303441c60b0329110069850b086441600d10034000407440d50986034600500b45151b00c0b000410048c01d000c01c01000960201c0d0300640c41c0001d003051902d480c1e00b41081e4004140858803801103610005100c000745d500540a0411600243c0e03d100d01607480c180d10401040058a00a20a44c0180000d018844c1d0100982e880c0120100144103800810b40024041d00c1c015600c00d0301082002454801040d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 209207661 1250 209206411 209206421
    0x303070c03050c09010b032403030406031508010501060504090b03011404120f031103060d0503040e011d0a0e100b06160825210c081308100603031b02030c030a0510 72
    0x3e04540c00c0c480c1d0f40c905001030050307100041041c8030300a05030b241d21316101c40500d640c1c0d8103414040d0480b40c4503520f81d000a0000c02c90b10f010601e07903046d0381d0b100007401d46050044034141c4155039502414185403021020240141208031603065488401001c6910002c5403000d00c110f01402015102d5000c81002402c0588000400c00806040805088038409403030f0480350025000d4446501509541c14020700f540907a41150745a000b40707200003d00b42000c0354021019524000840b90981c40b03540e030050441c0c9090780c00c8612508a001c1c1400c50440c940d100f03071100b04010b468946841071403840b04c2c507007094280c4101c038101b1012070341c040941c1039080c801c4c00d80fa40c20720340a00340b0f0442d500d4402d0b01c030a070010400710641c40703068451821031140003080e0301a94092a900d440340030340000d091603000c00d4014031200707200e41d1800103c400d546015000031250103485482e020303541407150a0701e54000d00406c3e83c140c8200d550100a5440822220b0b07000340c001e44c003030125100c0020581d0300b0380b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 209208911 1250 209207661 209207683
    0xf020109080f130b031303031505090a0c180612200313050115080c01081b0a0c05010207050a05030310080a020f04020d09021c140d0c030f0c020303070c0305 69
    0x685441052000106081d044803452042d91500ea40c86181e2884801d03000d440310b402000107803501000f4044865203c03800c4144884c402c0c1c806220203c2400c646084ea40040d11520381d100c511a00480d81811140d800451450600d06d007500207201100300d4400d20003201e40c40100050007080c0c55190312103241c85040661121112001194502c22614005501001e000e146241d0581011107041103025488004250901214808450f0382c445040707032203102c800c00b440c3c0810500340c0010000034050a20340c001030410104903042c0144240c3c120b960f001507840490302c942d070070081c1c580412020030200440038420380c0107655901d06419440c250f100e2940c0085000d50004c20003500698542ca030032070300390000b82c2c1c0050320350201e01e41000c060949000040d401803418070f4480c0c01c0d0040070020141e45405141c4d40071500c1c00d54102d80f0307a5031075200300b03060020300c0e5082a0070002c0d2240003800000841858105e0140c106a00001e0440c1c0c845102203a5039024410200700700402480300385002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 209210161 1250 209208911 209208913
    0x91828090206040302090a020702150a121509150302041407110307030210090614042109050907080c040e010b04030c06030c1d0d08030c0903010b0a08190311100b010f02 74
    0x800c0340c03a404501c2c82c0c0600c0c00004d00c0b80024000251816009a068403000b54004081170900c009110120059130701c40d5000c1400540342942c2c0d00e00c1c40449015802103150100c605d440d04610b0905e03600000c00c00c03040d0700452520100300010160f6158028140411140340120049050460020785000c1d402d62010000c1d400a02c10000465004100701c80103944003880800c501361203103851001031110510303401801c89030009000038006844a400002e00c00c0b2003008105462a59080d159650940708240e406140380380064062413040316000e82005400440303e040a403940d0401400c070500344c10070500410702040400c00e03c08603002180c010f10190604202106031294003c211049100d40200d02c05804100741d000d80d103c0441240080344c0080c001038503030601c0c100146155002d5950b2600c40c3d8204001c5041600e80010410125001c0e8401010200c1c24100715803541540c030103050b828011b848030201c20749001031041580c01c8503060301c0003c400c00c0090000d0810181c182c110411 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 209211411 1250 209210161 209210171
    0x20d0e0d02070905060a122612041104090c060f080c041d070e2d06030601170a060e0c0913020c10023a0e150606091828 53
    0x4036603004a10203055440460022449682c3d40001c940284113903404440b110130051000824440000740a44003900301303105011581c030700da9541c565280200c4075200151110140443c00060703a8504110b0071100c064804584c0c0d0106446e2000e501d4256072141c00030691584041010a900030460b581c0102c05290b82d0b4100703414001d4564181341059400c0e003281d001c6801040c0320a0090300f08809082d4010b040e0400f0040d80812464200003031154551039489405070b41c805450104142c922940042c1d42d44c1121070141e00b241c2c01c84200c0a80881c280d55071b1403101240303405240302c0c1944500403104a507907441c6580400d10001c50080c001c2c0c0030b045403051111101400c03002c561313401c010200c400c01507111118110349101800b041c0c0451420000c0b100e40002e883d0000f05540f5000c0120094200000220f441c40151100c040c06400401d190701c410000d042c034602600645a040400350403450f203100f141004c14031444058403a00c0b0700c604090310140707512583c100d401102c984045030900c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 209212661 1250 209211411 209211433
    0x60103060c14090d05070f0b0a020f07080303040308250804110a0608370506100e0a0608090a0b04052d06040b0712060f030b0708060d080c030d0e01020d0e 68
    0x4814083c1400c80382c072a4120850990038000c0801c03204010703011101122114990b10001018107a00401480e000350040201c003c00a000100c1d0800132541020003a6245682e0741d6411128203200916241c540400d00d150320040091510410ba8103c0c000e441c0c5800314141810b04603004403e85014903c240510841404001c1e40460700682181468803403121303424202083c060f940d03540090221805083c60240f03003003500203422842c010181a517140000c1024803508a0312494041041c40d000300c0780c494200300491140402d158403040300d03c14ac0d1b2022240359155a40740341c090f101034840341d00080100104a07682c1191520f1030b040700010040d003260310951991299001032001d411b0031161000610303114000c01d85d041c0b400c0d00c5004200721040e180c00344c0e80e00d0003040c0e010070b072650b840d400d000940c0700e805885054040c100c001c1c03c0d045945115540c458055102c10365880050109201b4502c007041603016140151041c1000582c8503029000f180041f289541c524a026601c040314100f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 209213911 1250 209212661 209212697
    0x6090b2802030915102909010c0c05030a0b0a0501050a060c020906060c0a030c15020306060d1518020c0f0d0503150301150b0304030905100e30060103060c 68
    0x500000c0e60510140c0c8942d2181101d5041c5907504010a10002001c820000c13080540107995094500681d2180b00c00c0e00008599030540740c03449210300700440104003144a543c01100280c00c010301c901c803560340c01038032040840c0c140f07041d840342201c00c44d5022040c0a0350a55602440b4094407007a1780b64107005203420350080c003055001c0700c0039000e01031800203e0826215581182c1800124030225402d142e403501d001000094188400c1d034017510f18102103078405c1d01ca802203c0c05080020140b9091524982d0090000c001103151501020912200021200c0c00301c4d40010701104400401611200c2e01201e60381000224000144542c010102c3c034036600d50440150380c1c10440c0340c0380385146410400046401400725584051027883d442e0ba0000d081e900c80c1f4003d5100b1486aa5100c06d140d5070781090207001c40d9209901c4002c60050803030211103040400d841c05601c5410701c1d01164480100722000c108000d9501e000003190052030052040c000f19004003a141101460813140940ca2000f0074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 209215161 1250 209213911 209213971
    0x3060b0c0c010c08040914010303020111210702010920010e030105040c030b150d08070210020c0102060c070812010f290d090201020f010c1e020c0a030303020a140706090b 75
    0x4035041c401c4980102c814404c08806940c094551418104800d400781c50000401080900c01100103600705080021100b20000070349610329032115a494010003415010f94005030010078100442d9644c041032004124540120f21603000c0b080040c3c8480c4050b100010034440505105c903001e03a050100707020015500c8940441225005840495252140c4000146564004101c2c5902042c1810702c4818880914010b00e20356100b240c0843e508056441c0c280e0311040003942450240c0c019800103482c8192040c024110304e482111080c1c82d010f0b108407030750032082d002c2c7c1100000d90030445050004400c0c010703890000d00642543c0070841d680342401000e4a210340c14040203403980385d8038108116402080302c4d04d4130080120003802588030144000f801d600314074610220324400c070400380c5001e03400070445030307030040c00580360040c2c00741551401d42c040c1d80008500403c01c016202c00380c44069500f000b034040780313105d65804038040350941898540c0303000c080c00410905c5121603100c561040f00d0121 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 209216411 1250 209215161 209215183
    0x30090c0a081509070e040302070f0504150621050408031b0315060a0e060d05090c04020903060402040b0a05060a0306080c06041d0c2208010e030a0203031323060703060b0c 75
    0x818201a0703a5200924180003030365100c0151703000d4010900c802c164020500e1030645240e00200ca59040e650000c20042c8c0d16080c0a94a80300130010003440400e224110074040c440c0d55102d10201c075007005c1c980c48110341c0e0132a030560b08060080305015400c1d02210006a802041ca013175903096050000300440140b210001c4203115500003d810310083c0e0007280050103c0310300404482e00c0e0354800c0c86a9000c1e042c04c03940d6804030b002d035805030045450a07200f40c035214003014005104030313a1141c1c00e00c00105400b00440b940003c1c4074800050950394403008100181c0d1325580451b42c00d16210111345402c1030744071124821801440140042d06506405914a10a841649800b0380303692641c09603503c6a8401041080201d00d90180003240d15651002203816045c0200044598030010a40380e0064001e9800140c0042003c50005850f5900c3c07510801c4c042d10004003066580ca991034140b1301600500800b54000d0340c00c0051583e0580704560040c50a00d400381c3ca82074040c8407654484d50b280030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 209217661 1250 209216411 209216443
    0x1317010e07062607020a02121b040f020702150a0801120314031807140901080d080423060403030f050601020a0203060106030213150206010302030d09030203030a0530090c0a08 77
    0xf0040c2c6010740c058141003a01c03201002250f0a084c030b50300080d19452908000c1c0d004001e5100c941d81103500c009144e070f08407541032541c2d02d0b4410302c40c400c000c050140402e034416a00e400b0b00c207103c090307502c01d100007400c00100e00219540d0041c012000d000514140d0000c1a03200c1282010340203e500030840005110103280056500c3c1d41e007030400540c0724502094047c8502c2480030101e085448040c0f0400020360803119081d2aa9983c14061f07070f6840d04140410009414501050015281600b0050fa03a6108810920318201d03002c1090701c2d2610495060740000c0c2c451030580c000058074880c69801c400f007840904007130800da4002c01d81e00c2c00184070303c600b01a80003956000301c08013560a40040c1c1500440d0003c80c401c07650000750b50316820300003a4031a0140c41d0038803140070b0080c2d03510012258098040e60400c00034541c01d07100e941040210041034400310401d4000d03c900303420010031000c0c3c000d5804c41e842c1020b00504d0f00e0031a10403401741c060341e00f044042c0080e010005022480d4120300b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 209218911 1250 209217661 209217677
    0xc03071d0409050f0c0a140d0305070c0806070302130501050306010c0308060d02030307080c06090a050c04020702040b06030a0603030e01050c032a030a030e0d031a0f01050f1317010e0706 82
    0x40c010070028507403002c1c0544030740512408001c070380ca00424504442d0344100c03441c4601d251500d440e40366015006ca03215504c401403400b4900002c1c0500054407242e0701401c2860b031015a2084040d003031003011030703100000903800600326800840c402c0c1002e000c1d0000b840c011742141342900020f450403424078409018041c0c440001511523584441c40c511203507002c0c06503601e8107024030740f02c0b1068106180844560145030001743c1940310000e400088035401c00c0041100121031010300001f5888444c040e40c0050f21403003030f0382c4903440320030096004002010340054a107107542001026006a107141c031341045003c00c0352060f004400410741c0c42290040b250340e0344e41940003e12566400c034060401d0000d010210f0107510341a010340c09030300c885a0400550303001d8041c0e020101d0486088901d1300107140b805000c80d1140e03040440c0504082c46c41070400c5d41c58031801c0ca0b24002260010082c00741c0014850806000d0004283c403500443d0825100030f11610650000da10307112030680c001d80301002100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 209220161 1250 209218911 209218967
    0x717070302032a01020c010902130b010c03030e03040e09150f0106050f0f160b010e150607080307030e0106170106210f03120f0b10080907051311120106080c0307 71
    0x3e5003400c2d2444050000071075840b00640342950280c19590001d0340300d450428240d000500d9a40105041004140d451072a49941560f080e8003c00d0400300c0c92b10684000d2002203240c182500403103010f5020a00104426039400700c13550306c8a0b8000307100c04404c4481100400076141c00a0540304822007601c042c6403250b0200503450720f207005041d8101c0681c100621444140007010032900e05036007161000c00c05541c4c55500c0c0b800c1c50715140c6141500f0080c10400000458817140280d0b4002d8034501d0f01140794060409803d00356061900b04054400240c114880014001d1180a00030440f0040000c090f00360503a00e1001e050302c42d20041c20106990900504161040440e104048184481040860128030f180002005140c15a90046481800003071401d030143d00e00c2171050104000900d585030400082c000103550403003c11501c5038461101c00d4180c4140c4016003210045410800d50b40e40c07404400a2140c00f000e840c440c0a800d0800a000c1c070941e01001c8102c4140701203617824080210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 209221411 1250 209220161 209220217
    0xd0216140105130b0304050d08160309053c0606030c0f0102150a0510050405040b0a1104081b0913110405060d050f0615010908190203150c071707030203 67
    0x3810b40341d229080b000e500208021300c6500c00341d80124040c1c030444854225002342030346c2d118025240750882e284801d0115848a11030f8100c0c40c8414411415101e10700c80c80f103102e6100c4d0101d014826100c91495280307014041c0004404100007041d24004c003594101070011a407103803450b81c2c100e806000b284a920510740d001304822412a00380c0e407540c2c1b25510300110004020902940c3d001c030321491840c030000d46460725008250082e5040104500140c4039003158000801e14021341e00c4030340c00c05200010780b0300420700c0701c00480c0c14501680324034145004100407003000000d0210464004040603003010807122081242850400c1d43d001407291204c02c0060300381c07244032a00900a01c02c2d080c003054a2040442c00c0d82c007820300c0c0e202000f1030345990001518460344074002e8004035404100c4071606a24244480b80c0202d0000c0c09480303000e444522410308580080310703555980400014014100014006031480c0660502c1a05080445aa400940b20312411022b040c0c00912580e03036580100c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 209222661 1250 209221411 209221417
    0x50102040b041502071a1b19080304141f1509110a0f050f072004020c0f06010602030708030a1a0307091401091418030702031504050d0216140105 64
    0x19688680c142c07600e564480d00710305000a000d8020060040d6400010750801903da11041c0313261144400b410840d0303005412200407006031440b0001e11482c00b02083c048400726003540d090b80507090407075480c40c06041031354040c1d6007500011030079400008080c8640c040786140c003e1051515001052150300b2205178880d00d08981c00000c3c02500d03082c441c075424540c04005125072085512080485031043c1c005480030b028283d04189581010010800000d40890728460702d014001e400c1c6a81803c628041170803a0802150044142c1c0059420405000c00700030007401080544003c1d8640b03425540c8020641c00040c10720b41000d5100c5164407500d0450081c500001000901200d04441d500c09020300038140303030764400c2003491041d070020905010300c0c007402980ca1240c0612510a0715484080d0109446120b80704505001c103002c032000588d4288007107064406a210100c50740d040030b042c81800e02c1c1031081400150350050f081824095450030a1204039042c2c000811499280d0a0040c0d5080c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 209223911 1250 209222661 209222669
    0x91a0405040e063c0f0a0f060b090f0303070c031a01120201050403170d050c180111071202010903061401090f0203040308040305030603010f06080607030e060403170408040b0c1029040905010204 85
    0xc4403030308104e02d403205d403e842445010616024840310314000c0c072240840c0c900740a040781c01c541c1000f2000443c1411031100743c0c841006021079103001e04940311540da0000e5074100315000e0000000340c00150300c440c2c0c01203002d0181d60310601407500b42940040d0541c4501d21000f40320314200d400f40840040f1410960341440d2001205004514154103808501c0e800a076009094042000541040b54400c103400e01e0a24100c0b0300400407582003251a0303e0300c54200200b2810405100404400210360b8020482103100289244616506000464090310a000484003031144103008100c003180e8000c040c1c50700140c041c113101d40e89440d0309000c0703805002070600c0415914103107440060310700305c00989103120b00d407030759020010441401c01c03854a800c0c060350701600040d01c240d104400320b06200c525540062182d83d94070328150340c905006038680c03c4034041d0041504100c860b01c4080c845401400307110300c1c00369a21040f0368011044000c0000c400501103014a90b1458007804109013541110064 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 209225161 1250 209223911 209224021
    0x3070c0f0602070b10050114120a0b040b0307140405010e090316030212040303020606180108100507020a1401020306041506051c06051207061e0903030c03091a0405040e06 75
    0xc0c03400607172002c00c84030603115150020f03801a524861240f20740c8207440c0c0411b0709070304032000c50311010080409020304c040160384c815610110a14141d034208240d100501a5408503505404588100801c0b01c00581c49003c2c0340003000d0410031100c1010044401010125050081032844c1d41002c900e007201d01c1004001010b40040c000c424540c0020b02c01d40b048808403038070106500004102091105c00f88240070466008000d02e0390020104d82266500862620441d207003d4100e1f1100d80c03413000b1940c17010180380d500200340015030500303000e402c0e1070034002c4146c020000c0c50840000c000b0f10a01844000f00c80c07a5038643d005209403038000e000184001080341045d11150600700b500d8004034800d1001061f441001c80400c0c1617503082e036405091054440c0340d645451070310142c0718078040080450405c10002c5000c5980f20b5100c80071030703c0c040c40d00f000c15140c034100000e02044400e088a240301a52201003084810542c403541d580340d039010b258144010300074918a01c07003810b540410b0001c01c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 209226411 1250 209225161 209225183
    0x902160204020f13080109080301061112030f0603100c14130914011809030c020f030f011508070b0906031b0c0f03030402010e0d0b0403050c030409020403060209100503070c0f060207 80
    0x10215256000e02040d081c1386040900040c1e59130f02403030881c0c00240c4010030b4600706200400001e40038915046044c80088295001f043c440002146954000c440f0390040304c2c250018088203040c00c1110041d6440c3d901c00c100443d9440010250981d40f003244000c041301e07000510980c1c90b040c4812800002d107180402441136000480d800308565000f4010420121040c400400d00c140ba14000c008100ea050b450f41a0001c4154003031200c401c4001d5071071074040c82980c0e241c022868091040941c81c200b150400e0984500b00b002450a0050592040842d43c80c140f241064640d00c0508903508070b00803d5081e40425080783c0c0f0360710b5501405568903902c0c050a4000e600c4200080020351191b40700340c0c1d4031044a51030408101c1a8065a4006841061110000b0f000240560300400104000400300c03418959500d2415050340d02c183c008462080c3c02040c000c0b002e06092048035801092818201d0031440c000000500030302c95914050801c46c0040350000034031841d5030440c0c00b019002000c02107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 209227661 1250 209226411 209226427
    0x3120103060542010801030f0204021e161511040b0a03240501082409040309080106060507051e030d02070c1a09130b0d020105070614070f0e0f0a090216020402 70
    0x1084600030f00540d01035001c1c07011101d4151311403100d95050341d5110f0008510f075100c0b0740a0100035003118041801d00300080140d00c885080c50409042008de8503004521009018500031001c1c071840406000c44504242c40245580005000c0e02c040e91400391119031600d1180c0411030142004807250342d401c010315580e81d078241c1151415442507d50070703218281940c481103564003400d03102c0170180392418030307a50301000039241250401303030424003910303160301c0b8551100303e4542121036561202d0080fa00c0000c03002d007040010b1140e02603402e460300350508111041810316450340715016400800590002c0e0101c1000b501c01c80c800c019010103102a200340c0c11106907100242e02c0715580a205403a41502e800540704030340a0400314060141c42090341040c1070b40195100e070020441200e0303040c0c807040e42c51800e40009401c24800c136032555403c92980c4100c0806040424414001c60081841440032100f5450b03654500084442074100140c0d507181241e00115001c0314410000d41c00b0f4000180c80c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 209228911 1250 209227661 209227741
    0x9020f120d0e010516081305032a120a15020712080601120603050d0c0602041a1201061b02130b030106031b05030c0a0b030c0705010c0201050708060102031201030605 73
    0x120809049031503810701920b20b0740065806009a511810103044184082e00000d0284000f500580c8541c0115540380c43d16a800682081d108203c1d2510203031610a142d60b040003080181c404640d015201c080e1400440740b107441e00c07422100c0014200c0c00303039180d003400d400e08258101e9405580209510b84013001d2403400502c21b00050301c215000031100d0074000c240d035070148580340840c0e902200602c00c00351001c105031554810200701351022030b404d010008031030ba50068841d02460321600469541c20503400c41901c6020180c010104000003601e003401c4840120300d190300c0d090b4044651480001031100c061010f081c1c02411302c2c2d003550800c00c001003005442200d40700c4e40b400c0f0300141c417a07490702e031003c0c15503440c81880c0e8980e0002e0008030420454514200642c2c02141086166280440d20340300c86007556501c070f40b03407070050303545104010907a036011702181d8104ca02440590310f42000345140c3c941209040c00043c140030782d1080030035104010038401600d690b80240c400e0300d0200200e8942 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 209230161 1250 209228911 209228923
    0x20105091903110a0803030f061909020319140c04090f0b1905150c10090f05120d050a0902010e041d1e06130203071a12040501020c1209060d09020f12 66
    0x80c0a80804d01e0302040d80170f00401668410051011030726100c4c4d039000104101d00302040c280201069601a000c180314440d0b000552181404028528425000741d002800b29049007102d14003184d0780101f0300c0f600d440b0180c2241e00300c0d07009242c04504045802c18040c02058241a03080c0c0c080e00342d621904400b5141e0102108a6804840d60301d64040c80c580c0c110f18610503810031000a40151074410304083d95940000c0096005860100c01041c9581c1c1c0d241c41d000920031040300511001c90541c1c0303501d645d4054540d21a041d0742090010ba101c5600103010480ca45052522036625205041d0b00e01c00b50032640000002c020007122030302c1031204282080d00445090340358660284400090074003094401d100d448640c090010150a454045501100e41d40d150b045160b80d80104002540c61140c8260540164020f100060b0344400d903403007851500d44807081d0007990700400d00809e02c0e1030f59054162000c0c501d20380e002195000789071002603000d10a5011ba190b0004a120203128203500010362 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 209231411 1250 209230161 209230193
    0xb06070302010e0d0305101710050f090d030b0105040306181e1401060b12100b0a050a0216050a140301091203150e0105100f020a02030a0803220f020105091903 70
    0x40d2520201e250030101c0941d84211498a107c01c541e50382000505410700640641d28100d40c01d030b41c0f50310a051503000030350b0029034484d01408440c40c184049014117001b00d0500c1401401c04003c0f443d0440f001829902503880040e00d00eaa03201e05000061410800d8943e0749984071403035052007100c013001d014101520324000d81d610801c408040d24110030520451050704c0c030740c2140c98113080351184140b1410400800d480900d504a000010300e980c3e81c030001d0f101e41d40150b01c409449002d002c0009103000760341d08210001d40385e10001040140c4603040c5000c01e8415407081880446032020100b4090106144003c00c52802003402e403139016456445450070b1818140d00d0b0308140d64809010150700300070301550b0307030109441c401c0d00b00560203800080440308007401900c46400c115000241020046002610708010010130400c800d461214030889081035180c039102c075040181c582e40b10008401400074140a00003032401c0d417542d1810064803181c1102c6981501d015200e191082c035070110000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 209232661 1250 209231411 209231413
    0x507201c0906120e100506012010050702010525260405010518120a14030424060b1e0f0310150e01020a02010e0f030307031d0d03080403080a0b06070302010e 69
    0x15942e1030780440340108681001380c400101400c03003000c1021001081d0150055041c0501b40314851102c00c980404941058401409010b10320202c18500099990090010701164901420050400103400b0207040c00040c1e080805072044011f030098840d03d1401510210100707070501c8040c408074001c4500c5210b288104000d0205813180b10964404c11108003490126030018050741101c0302045014007041d1034145003081444000d03060b40b50765648142d90985805440044c00c040380101d640c0025200e099403001002811325080841019000e02e01030300080b070003107000c42c114a10300c800c103507110262424001075807420300703043d01c10000c0c1d564070441c0240000070340035041c818080c030400311003080c06802911001c03896900458443c2c00d000d000307990140c0c400c1c17080440c1c1e0700c041014206461181e112002090510348402d08003d0080c201da62241c00d1003003010b00001da0050045402c01d505090000c61034036422841c0d0040c001e1100ba064100501103500800e06a05400030601008810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 209233911 1250 209232661 209232677
    0x7031d0c030106090b030d0507020d0206120711070501140f04150c060b0a05060409021b490503090109050307060b04050a2906120109050f01090507201c0906 69
    0x13100c5403007a03038810041254181c2001311746141203801000240800c40c40140880d8900c0141e600045990f013150a28551030b03441d500400c070210b904020300c1d41d61078410b90000c241540c64400003c1800e82445e0944400da08041015101088504141c030050030b644403042c0c54907000c0d508002c00c902d0580900b0b640381410b00c1001212402e000000b001580c4018107414501810540d520001e980040c40248002c031480c00b0321072543c1424800140812f5407000700c1c0101c076104d4041d10802b0145c9188448601c42820351183c410030700c04100420f00105810042e40300e82d10030380b1503801862140005000c5000000b25801085000d521010208004880800480c0c60310014842211640c0d020a44c0c02140078a1118200d40368024408030340200400d0540f620f0102c02c024440340400781d00c039242064659081c0590a65102c04142c003604e120f187c100141e1800c940700914000c403040c220090648094000d954848051100c0014844c0078503c15501c1e035050800144062410302c01c000010b5807403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 209235161 1250 209233911 209233919
    0x5030903100219050a02030717090f03071d13050a030206010905070519080a09020a0b0904110f030a0c09080105090705090109111812060a05220f0b07031d0c030106 72
    0x14400d0325030400f08580740020b142a8440c081d1080d0340303c1401403085d4030041c481c06001070060101c0d90510f4000c150780a444020060601949000301408503200c2d03080000113010803128003810014020b1038076100c0740caa48580707024004507039040001611034000c0385c006609041c0c000442c28100c1d030f0399400402c105d90340e20b10111000d001d605007600b14151146d40300030382503200710125a04913001080000b5109195400952041d489912610003183d012038510750f18038203841a4903895284010381e92070400030030111882c82c40001e018001c000d9554001c405228030800c3c501000e01441c5d00200020700300360114565401c0c0038466148201c448800102c1c14441e980a00020000e21401c503e0400d03080001c443c030281d010104503070300000701070440301c01103e04002c81405011206800034050a12030815070400059501190b40c0b41540110080020394502c0241c8440c0d41040b82c117041c6031545003048020b09140c01700801c40548140c05c108000002058080743c1150440017000f1003551 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 209236411 1250 209235161 209235193
    0x30304092304020105030f0a0b1e09010b03040b011205010209100c110a060203070305090301110a0f02010b0904081c0f0f0c180b0f03040c12060b040e0c0a090902030a06050405030903 80
    0xb103400900103541800854818030fa91030b550344d00302940ca200440d039142a076002c2036a80c80103085c8015024101019800700e82801c0c40e6072409407255202040c6146041e07110009441341c184107103a1084030060000c8103009003903040d2580c0d00700090903180b043d05202d4005210080403082138a86001035011503c442c600065000101e603403e40166061011944042d109030304a191565015500c1da1803440292000c4401041c98004a490705040d8044c0c1a0f070003421506138800300350281c2c50034014400400c04131010b42d18200341c1c0c80d8a4034459a0182e20390390180040f101c00801590130034000c1460240207401944164409a5a4540c402807094001d1010300310342c0301d4541400300400801d408080c0b0b503c01558060b028901e98504141e8a40900780f03804a09401521050360761022162503140600554458126490040c0f0001c442d2500096000500303201e0014070590760100942151024880e103180642c00813810001c40c60700e82007082c2c07254020011a40300f4000d1131450915401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 209237661 1250 209236411 209236481
    0xd030905060a0207060e06090610090510150c0204050f090f16050405060a180b011b0c090c1205010e0105010f020601032d0813180e190c030203030409 66
    0x2820500801542d10785a011900950001500fa10340036140d400c00b00400b44c040001034000d050003001001c0a00e0007150003c50400300b900700c074000500300403d0242d1100c200210800b0b54510342580c1ca0004040c40c410303101b50b080e0b280004e4016003440300304440403130044a2980300d00800c0f801e80360178040d40725060303445d2501254402e803002145601800390782841ea00140d44881c01801c0e0040755611542c1d20350710800c84d1004001c0d5140c941010110950f809658481180a4035000f010300c40070079515292030b18520b014892000f80d6a035501e030318240c440c40380e02203c030000c0002040554ac49120003101c3e14000d008290210300c90140c0301075801d10002e20ba9040300d41064041e0001500701500c243c1c0ca03003041000700c6030040d4408441010942d803100614441a5a01c40c0c4001d080c0780582100d203640c1175a512000007480c004200081c51804940c020110b0842d140c4c08545207100e14041d01c25560941002e034151002184c0410004416800203034622230f000e503c800104005850458050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 209238911 1250 209237661 209237663
    0x90702070e01090e19080d0b060405010f0809010f18120827161d0a06080c0105130b03040b01180207020a030206090d06051612050903091e0a03080403050d0309 70
    0xc80000010072031420303c0c0e400141c0300c6410703030103840261089031000c001c1c540700742c001034400b0200003c07440744100252099920300031083d242142003d140100207800741140b008500c0500c9030380c0000a01c0c080b000e62240309891101007041040c140e011400060802190404a40241504402600d50b9014078000c500c81c80b4080d2401e5261406607d0200c084220038011503020712492500a54000b41682ca034005469403032155803e14030b0040703405a80e854040d000055062600c0c03414428184081509071285000307003443d603901d10320b00300c1240c00b002556101a12032080401800204410f14444504a42120300c10308140c5405900c00b00403031280c0703c0000e6020481080420040c10000003070b100d910b800030081c9141004a480c2c0c103040d00c00445a15540c8403d413003407520419004550a0301c8540c42d40020015071908441c030960300d01c903c0400c1d41c030560350107405101c0c2100c003540c0301800c400c02030074a1091a51368908212190400d000446840c0940701101e20868846d00c01e8005003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 209240161 1250 209238911 209238929
    0xb07080405010f020a290604110405040b030a050a0b011a090306040b07120e010c1d0a17070b0a090512160303030203060a0b071b1203020307080a17040f0209070207 72
    0x414034250040d42c08940305034005040d4007460041c174012422010020ba901401a0782c0d16514a920b621880020752004111a108030f18190704013044141344806d680a841041c3d80000d25001d4403000645441c100c041d00078610700c61184428100301d03242e03071454122400b0300d0f103c4101e40300c40405200d43d4007038017030915051b61143c0f0029012800d80d030b0a542c1c200340349003000440049039000303080545803560075400c0b00d6074480801c039080b140e02c407112901003405106107c032420000e2000400c0c50105101f00701d120341000075440c00c40b45081c000c0030014049003c80560303c20015801510801607445018030072210f0350446032110001041e550010620a8a80c80300c09086903400d0740250406002c05400c241c004a02182010003080185202802510008403c1801e1440e4115100c15604001200005c1080e11000660000140da02455110718050346035152031908540c0d05500c00040108056184e0502080c0004100c00c012918001d40d0711600554906138260303a5001d086c0705151513 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 209241411 1250 209240161 209240167
    0xf0b1803030a350a090201091d160309020303070b010806011e18021204030e19030305030f09010e070303031a030304080a0b0a14041110181a0405031501080d0c020d0807030c0215070b010b0708 84
    0x6500480381c81d00000d14ac032814001050030709500440d140d904503c104668080c0884018842203108101441c01008050a46070190022803c00c405844641c4250040c000300d020500c202243c00c8d4058031040e0151000f41c110604d4142001024030000d02140c034083c0c4850a080c0034469010040b00c800c3c0c0e601906d410f86107888040d1035590030800107204040707a56890a1880c1500003d001010096000395400303d0740f89203c58109107947c1e641c0c41c22034880d5200308810040e81c4000b081b0b0100741904030401c6941d940d54480c3c0d20028003c0e080d944101c980043c0100030400800d010041c40c1d87c1020348403100f0084013191f003030b2003600f10000451062001540b00700500c1030040c808034410f0b510000c0c41410542e44402181c50500c0c00e40c03902c40d20b0111407006103e000010003003001101018684580c151141d9008a14440315141d03015103098400950b2a09050060042054980d40034009400407840003940541e10b802076201214415a80000020018200340589003035a8000035000d01e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 209242661 1250 209241411 209241421
    0x6090803090a05010825031a03070317030408070602070311060906040c0510120608010b01020f2404021804060f15030203060f0405070f0b1803030a350a090201091d 72
    0x3800000003440310000e61b1220740c80040c9100840601c0c201c003a1140c5000c54041800c1911858010b101203c10307009a01c101750402c0441c02c14508641000044540e596884c6c90f641061703c40e5203e03100d40584610300000310703c07082581c003da920910b420724005032655901e6541c08540c50b40b800703603405000c9408034a814049403400c10b08030403003188a41030203071513002c0046128003900c1003517121101c0d03030355161007411480d41c06101c404410b402802c043c01039641c04841c044010b05071101c0c42c001c44614080000c0c04c648071104100c4c0784110150104007203242030319003c0c3c06000303010a42902e80f42070080c0b00d400422030034200d10030f6070790040c0908642e698111544148050080069520f803140071000034115101e154194094140902496603484191100d42150038070b40041d140079070b0007003007050031143d40106c0c4840d1040049109003011035200484854402c07403442503101c00a2400705010815000d9440308001501c00c0c2c0702c01e05801c0d07450f10425800751040023030828840003100015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 209243911 1250 209242661 209242667
    0x1c021608160608060f100c051b010f02030301031509060b041b030608030a231b060702070e160e0f0402220b091305070315260102090303040302060313021906090803090a0501 76
    0x12401c0c6c62072800140404031341d01e499140810b03940003000c20050200408180c0d5912103045401500540010361840d451561416405c90070be400103034065a4401d0a0010443d641c0c00a10784000010818840a441c80400c0c859002c0c1c03500301000030a2815500141c2d102d00441078039a07041d40d6880c3d00c3c1c1b040503608001c1075000800061264814810030540f26001c1d1600140310906150400074040f40c94440d00288c40d181700c41d04800d0010303654500300855145c0048200c40c01c10010302d8004041c00117100428480c1441103c3c0950281c00841d41e01000c401181000d418a00c60031005088140d0710104d092844c46a013210642107120902c1040d0300310300903007103240c02c9032581c80d000840480c00d42e88020810102c1d0864062a200d0300c901c90b15400342c001200e100004444002c500e052140000a5a07904c21440000c1c007640380840003881701044000c207604100c2c0c01074510307805500003040c800841000c5001e00d00105080d204042401800003083c0c8003084000740c16900200e0400b0019 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 209245161 1250 209243911 209243929
    0x20f0307030e0a080601061d01090f031103010e0d02031315050306060f07080a0509010206090c091303021c02010b1305041106030621160e091c021608160608060f 71
    0x160031036a05880001c44c11401c2181c41e000301510b86d1401e4446142c05025070160401d441143e0411001d61400c4c8049203c1c041d010b42100c0d80203e600301c071501c0410109024085403506140c140c00303111010074845070040300410100284500d84400c107511440c40c2c0c88144400d000c0c510003c0c0c030900005505007081c200a20894283c0640d181c100340b0103030355030b03291170784011401c3d80010800304461210b540c040164030381001600018103000c405100120348130580003040018115007002c00e41003418000d0000c19440b440c1003003280c0d154506644064081c0c6840c0340050302901840c2102d0a4052031446400e0180368015016150500c0302c0b4100b003515080900030580c8042c40d05403443d1408920001180e003c84a00c0c040e04645c02d0305000a140f4080590003007050910f0001001490f00300850884400240c9421031b80c500514100220716101200c0e42501840d1500c43d0003113140c5600003031015a6003035440201007200e81f0b94038111101d9805075a1540c01c08006015a802480e080d048 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 209246411 1250 209245161 209245187
    0x70f08102708040b030a020a030615140d180506060307150f0c020f0d03030b03160e06040c091701060e0a0c0e0f01230d0b0306190b06041206020a020d020f030703 71
    0x124500f401d07144d0380f910340315900640e50000f1003a40040c1e031010403601809001d0042415403581080003c0008020300803506007042914001c9000a4a00101b11070b503114038a4011003024a0a50100d01d141c07080d0303140016070b4054882d2052400c0010406006c00040d00c40d00f10384d586406458542410070381c3c4501c203209040343e1241d1180902078060315091500040c2030302968003c54040325600501d07061030030444c2016840a0296000e00c0081e55100348250003c80550b0001044d403100c50080b5000f010f50b412020000050041100e001041500400103481301c5200e074848603160344030000d0031906401030b503001050170f500c00700059181c05050000428010304008012080c0180305104c00303040c8581c1000760b90404140180b440150303100307402c01d011090b4000d10303039030400460a40d804002401003600c40c1c0d4440a040704542c44580603500103080030810b0440f508a030f441d0240c0039400c04c04070b650044c0b0130101600404c0303200003000d110780588040954a450880c1e01c003210b2001e50001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 209247661 1250 209246411 209246423
    0xb0a08120d1419060806010b12040501200a030f0c08070f02011b1116030b04021207031b060e03060c041502070b0703050405100314010b03040f05070f081027 69
    0xc000c880d02400d95040314490b070f90946001e0300310f4001101000448100750007080b1260701000c011b21580028504541c142c200a0740906040d6540d450114090f001700c22544202445012443e01019003420242a580e2860385040c0b292a002c2c000c504105e40b02d10300131700d0014807000c0c040398115000c0d1800d034413190380341d10022885900002440c0040c0c03c100c441c0d04001070000d40d28140a038014050b40b140044011107100d10326245403605400004041c201a2094559459a02e0152000c00415000759803103400d40401e44d107000000390110a40b80300380c401150000d50042400e1034042407544c403404030750701d0f51400d141c14611000e00590030101c034503045d403003a0480441c601c9030740c00280100e180b00b603840395525410704060012000030000f40320141810140d40d0540540c1800b40c090540d20a50b4509480c4c2d600d0341000f130b0403e1504140a001ca010785040402c9090346003400d8800c0d5600101100c0c1c095180b08000412901d03c2c0314803000183c1244101b200c03404084c03d000310910b001d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 209248911 1250 209247661 209247671
    0x90203010209151b03040e010501201203010f06080412050306030a0c0803040801141302010e01140c01050f010b12010e070c020a0603140604020a050d1e09060e010b0a08120d 76
    0xe8007280740006501c180054030000444d8481199002d10310b0074021041144c051401c09103450721541651006005142c1846244160070144480000410401003104011140c15071001120059103034000c0c054820707642494403000c203e0900400d000d5006e158040300c8401212141d00d800c03215038001801a9a00d40150554040401c68400101c0b002d4040d01014658582c5000c40701421520480d000c10983d9525100700a048080302400384c00d06070702801c0190705030380070b400101d61004280705100c170391501c04a4042c0147c6015031020f4403561001c40d102c081031b43c81d6270004070103015843d240d112a000d09401031008003030510311103401c228030341080260b4421642c00600050302079001440020380d40c4840d040020892600590400c00a540c04c52134403d01c00c42c014074a100303580403205d031652242d08100c03d10940301090a40219503a03402c12550f010391900710302402e02e405207000f1543c242030440700645841c04507001100c0b41a001008200c20001c4c4240c0581c011302d080e0f0a62554034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 209250161 1250 209248911 209248927
    0x501021b061603110c09040804060302030703020d0501031506080705130b04110f030a15052b1203090b0a060b04060f0509040906140f100605090f13200304030e040902030102 76
    0x140300300c203000e92003526440c44a01c80703c0701681c0360100c5c1c200c1c220300c40c12404c005d01c408610198200c41c15204646000359a0b039649030701c150060320501c07404ac0b540d585004000401d11011072040440c810060009000b55903881400b50390360403c0d8002c050340301c04225200500204140e02204020b4000f03800403403601c01c43e5142c03402c960004188036001c1c24000080016802d0b1512892a00d1580740a008503410f0801010510300101c620141580c01f40c184900303c82940c5116034010f00c0c03984110f043d00c5e0500e00810003400341852301320858100e280480418410702c0c41d40502002e03201e00600450400d07151100889204040640000900004014150702900c41c2c0c0621601c050065030080344054076100340820700300c0014160440081c080040c001240c04400394201211514034110b0f4540f4140e2000401e55400c003d0b086e544048180380040e10a01140c2040d40070011004207134030307008032007940b100d12440220360050014201403201c0405141641c4451303140d030300180005040c8100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 209251411 1250 209250161 209250187
    0x603020607030e03070608010602030307050d09021002030d150317070213020f190201020c061f0f081c0f020d0f03140f06030f07030209040b0c130f060e09010501021b06 74
    0x20380002d8000442142c3d403a50142070412000c4010305151030802c3c1907600d000c100a40b41d00014040b80d01308000082c440f08000103a80090722050303001400c540406070f90b545c0180d5a9403061700020b03c1e540c20400c4003501c54246180c030008898020303030604950300341d610f1b035405194844c1404a1740b00901c0102600e280b48903102400003403018420890b564004e64100300c1e100c4254881d00002c682c01008501030035000030a0880d00b080e42061502c0c41000d80003206914508990080e10640c1c040c2480012200c000044c0e0100c40f2404002c800001c07070003404200e0ba0050010b5545000d6030024040310412031040000d041d020b19103150001d048126100824520201610340c2c1003ca610340c0e090114078582071042501050a000c010680585550b01280270302c40b004001510341100000000c0300119800102c9000e404455001c0c084a5207400ca00a20b041c100c2c0180c000190300040503070154100845030038140d84058000b84000c5c0c00c2d90103020740042d4603000b0183c00400070300c448210828 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 209252661 1250 209251411 209251417
    0xe040f14180f0f100b09010506070b04080f0a0201020904051303080c0a14040905070206060108011a03130501050103030801080c01050f1804060806070e0405150d0b04050c09010b030f0702060108070506070606030206 94
    0x90050064084131142c08442810b50f0120200940301e420380d04d0041100b030783e50740211a507555200030140f0043d034460600c9241401a040d01d61402c040009640d490a6810740c0141240041110308001030340b1001c080c2c0c84014911000200072501803008601069580340c0a000301e60440e2802c010707880a040350000450300030780c1c4009802a10b0381b00b0b02040d55010321030b01c0d03404002807030414419850400108070003c4185000f1181080c00001701d54440d080b1007072000e555801400910a55075207180040448000744544001400390179071f507032401c2d840764044400c080d11216601d82003410301c94000410b08218400d655001d0b994607000650b0030b500344032540c860030160b260480b4240b03101c414401034407002051104122854a24040259100c0346407d072201c2d0040c1114840f0f507558500300b440e20000c22000355021001000020310364031880029071007240e89407441d00264032800b806903a100800c0c050180740c0e4002100074060386c01c0c1600680801405824003040c029030700e0300071030318584c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 209253911 1250 209252661 209252683
    0x90a031218121d150706060b03090d08010801090201080109050c21060130111b010203070e032d151609080607170411060a0e040f14180f 60
    0x41e0302060912995800c00c200d03964a44060804400f50154003000034410b455110f952001010041020701c24420300e684401b01400d06281c10036540d0824200b0306030b45c2e10503c05d5020002c0c0207100045460141070141d542e5056043c1c5031211701e030b400d00040342c000d804001c254020009050103018407000c2c903150b41403059040341c01c0105003070901e20700040c40d680010f0440301115110386411610a13814a216413414200c5078000a1122094081c0262134400d58448a9500c40c003210031400203007041d40294041c40c41e43d207a8440d0386044206041c0c81ea01e010a402100e00d002c0c4010824228002c103160113800c4800c8107072164615202c0c01c05403800010b891241c5101081040f03078108541004100300503007040030013450140f504101c002c0c1032800e02540c0004428034400840c003004400d000f440d4420310000d21903600d50310369001c01405c005022688610560424000c90800b11151240f805a591010980c031340c2036031a200c49000c504030141c0803400c14481c94292101d9031400340b14042c080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 209255161 1250 209253911 209253923
    0x408030c1204143d020106050604180203060a080307080a0909090506060d11031e06060619050906040504050a0902150a09210203010c0801030c080c1c0501110a1101050906090a031218 80
    0x8404c990000a00319400c94100701d0190300200000e101c07020701e1039a06280c94602c041c000d42c0d80da0300c0f4000300d000314419512540d01d0744404601e020411180e0400380c1904815a80d6038000d840e0b80b10301000c180c80040502800a800040c046221400c0407036803c0c030150300403600300c603a081429001c030b442e2505c840e4038a50044ca21450351480c1c0e40c010710506030003000071030f211400e1080840103902241343e00030291042c05400240c200d81c40c0c40d00c40a890040200034010002880c00b2100300c00500307440c81041f4803d40d007003d403006010402d002034944241050765002c3c24035040405078403494400e0010300b409628020748080050350240a1100c41c140c899a07940403d52640c07030400072100d0300c2d070420301d550303002003400610383d4940f401d9203040c0403800341c101c6c0a010741900305240180019030040f50310000004207286001e4209042440442c2c2040082000b65129030741c00d5103911341504d900d8400d40160b180540820306c940c110b4008601e03d9440020528a02c0e0f030031f4100041001000c80710 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 209256411 1250 209255161 209255269
    0x100e0d020a140108060411090111070f0314060a14010513060f030807140d0f0f051c052406030f091c0201090b160903060f0f020408030c120414 63
    0x4030f581c01582d450301300605503000d000d0702840f00c008040b10700840035804e042210844143d07083c441c003006000e0041c403004000c507d149890303040005040100c2c01c2110014420b800200c3c40c02c0c407540c490040d082415160f0408183d00f800d0400c40030850402c0700e080c4494881402181403514941280300840c8561041c4d55192520304d01013014400e0101185042d0300003451040c94180c01c1b903210f031480b40762403402100c0c0200b103082c185c9542c0540a44480d507154814071305820b40b1000d501650280030300c144141c220350905410204102c50321191181c0084041c40403a0b100c11202443c190406090011b4485020f1122800d0500510140d4110010b0391600642c2c1c0c244000742c118607800c0f0003000441c82c595951107402808903203c521008007510342c6c4072141c940011840d1301007446401818000c0d9500d954a8640c2c2e51f0380e4100944c0d851041c080c6240110552420b00122401c8628024030000812590010001600000c0412110f290b211084005003a0944602c481e5032410720b0001d401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 209257661 1250 209256411 209256449
    0x2041104030210090b09010302070f0b1e0624070305070b0a05060918060f090735030a0f0c020117010e040b060f01120e0c030d0804050c040605100e0d020a 68
    0x2101103c00b084010a0155082c0c0c10b00242c00c0c008200c2c0d0320380100303090241c0d5071019460150794141c0c0701d03138025200d0b030b0102c000e001d03804480c182c0b07144041040810040c0039440d454200400380080354005a07204101c03040c8c8848000750714015046c854040e00304141001c1c5a51940c1c1200a02101d03901381c07880e5038000b0040ac51a04901840d0418105418404042e080d1030b8502e80d1520302030420208902c400740040c0c202c0404002c1c540c05000e045641e01030902088950b00f01c8032643c1d8a0105482c52011400c0701d009000100b45c610304410381c0c0c1d4074007203600c07808029905900c0031807082e41007101d00d2510142d100c50182c1c41c2c600a2038020140790b80c51409003450f0100b01c10240410740310706207a418543c03040c0c2e800503002c2900c002c540b03400940700c1800700342d0510b000c110011f400d07094000c107401c80280d01c1e04071100c58401ca00800070380d12400321140400040780c4080c0100740e8829040311480892502c245d1481c844440003070410985040c0540024006c04e405038090318a695001c00740c44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 209258911 1250 209257661 209257669
    0x90a0b191b1803080306062208030c1506010206040f0606030819030c0c0302030a1409040c08060102160503030a0c050c15130e0f010902091516061409060412030603020411040302 78
    0x300d044100401242c001803c5a680442d1880007400f5544201004500c08018003852000c3d40c0481191a061042040c0d403283c50030b44a81003010b0302800c90007080300c4001d0001c60740b030352507104280503406002103642d5640c0c0ca10800c118001300303039a83e945c1c815010001071120001054021030711040ca4921001440006064981003224003081000c1182c84000194000040e03546090b554186185070340a4105c007604140109651150311505000c4048140d41e041010a400b84800380e00340d0307038035081c450400411000144507e9425900030020501028841e41c045001d03c0d200300292100a02c0c0e541c00564000005440200c0b2110001283c07034024040c402c2420040c40c808000300c40b981342c881c42402c2403000521451401c15000500a50700b90b5a15034171003000c0034407028550725880c13040400019605881c01c00c44419141090750031110148800c034601c40c1c2101d8005128942e1913076901c5020440c81d00380039040c541c075460048010782d00c0c2d00620660103020b0317a2050300d551541c0100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 209260161 1250 209258911 209258927
    0x50a020a090212010e060409020301110403020a0e100905130605041103010f0605060f0f1306030e06070c110f121e0c0405010503100203040c09021c0605010305090a0b191b 75
    0x28080306204001800f01030310180d42444c11510a942040c80702d6481002041c0948040c0b40003c3d0b0551902c017140d01da040c03080000e001960f000341c070090700503a100da101040d9050151145600744546c10b0003049450003940140c0c0d40486500c0c3d0380e0504509a668101c291502510100d9482c043d02d00d000036281024820003800840c0a00240702c228600b801041042c42107414031903141e980001e811078a0110501141d0200030285039000100b035803803400070b00800401d296000103010351001300d8441c91003880e0001034039403c01c243c4080d80c000075003000550400564082d800000848004240a00a000001c109030300003602a0403125200403090619002c41901c6106510b00001071066850008100181c0c220f034600040c0c6c0d0b9229410074011880071980140b281ca800081d011160391200070011380d064040c04000c2c0505500c40300190140d0f403045038410703100d9111030010301c080781d401e00080b078111148143d60b0005550fa6003550080d151854140c01c9003103000314214a8950307110002c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 209261411 1250 209260161 209260169
    0xb13170310050111011b0503040c092003040609141605190e0915070c030314061c0303020f0a08010503190c0306021810080709050a0302090c0307020a0f050a020a 71
    0x1140c5940781100304014040c00c41d000d0681000030410340d812854109500c00f94142d0b00034515094400f5203100c009120b5031003294100c0314400e40301d20005071408030b03000c0d03c1002ca2074080e96620303000070304100c659203400040c400d8805a4603256500d002c180128070070a00c405490001e0f1040202210307401034800d00d5540328500030707403881c090107841100041c180c00580741c0f088002c1d6031640b15440e9080c6003103400c0141b40c0c44580300d00d05100725035400c910540002d9220761014005038424000c3c404d503111048909079044503000b4545540d0589610800b684c080c802e08006040a00c101e500c0c1c0d110780c010100d15000704401000501180c50208400c141452421030710103078902031b41e980d00300901d0640c80010590740e004990400054404100300603540c3c0064200020681940801011140c05981c000c020601040012410b401d02000340c9d015030360050102c2c03030b040d00c81500c4540d0644c40200003c2c11409000c0071000010040b040180d800c90049000b0821420365004000742800141c2c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 209262661 1250 209261411 209261453
    0x40c080a060e15040e03070606060509090a0e07141801180e03030903090f0a1502100b030f0c06130506031e0a0b0904030c0503040902130e0a02340b13 66
    0x4102542106001d2100843c03800c1e50046891540604064514007a050000b418141440d0340030901c1076210028044521003280e9105140c4c84400048088511114400c40f450f0801740c000d01c84502c1c0b0160301c600542c030107003184c080049030483c264003114003a00030070180107130701202c49804103041c0105643c071142c4401070351450a0041c4941e507680f00c1c00c45140c1c0240c001d18003407182c0b661114401002455070340003400010303401c0b05000b501d5400c0743c19000d000c940b501600e150a801c000506d11180810f4400905080800504100c0b0980140192001814120201145584541d80518081c101800404107a10242900c1311091413004003907580003031a081703403941940e641134841c41d041505800c00d0080342d00b2505150703003188160707007098400d00e0000480c01c8600010180c0482115080740c46100240c880145a20a911510b42c1c1c260040001c4000d0b44a0803045507001c0c0b020112110031b101324006d80390368850781000125081404640c02e4100344040c04034809c0103000c41d1003420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 209263911 1250 209262661 209262689
    0x20c0c060a020703062004030501090614060a0306050c0f041707080d080412090302030f0307020f0a080d1209060f140a060312140c0609060601020708060f01090209010e040c080a06 79
    0x148025543c2c001071101401103604d40ca1106460030b8075a400504200c10071180d90742d503d4a90402c50701812100000701c843d10315101149603c0c80e01c02c45901d0158a0080035640010324580b0b84401a042c094001d01e210319040020410700c46a8600a000030980b5050b09412440c490260780d0134070040e036000da0f8064001c00980200941c6c0401447d03801035004000030081e0440c40d1003160340030741680000790940306241e0b00010764100000680b10142c801c482c40d600d46515042400f41d07141e898807990f100c035400450201c0740b0f140038031000320b001c10702031200060001c0d254440006441280711902c01c419a03a80c44219000d848030030080d0320006451007070000034955502c060161000700e030140100031042d40d19564100c201400c56000031611000c85109090111310301d500d45c0015a001805442000800600c0f0800452410320031406804821a268a03000f8410040e41c02000c01c1070401a0b03000d03250b065645c035031040c010708141c01e86e41c24240340b4042c02d00c01c0864020390041d804040c80740d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 209265161 1250 209263911 209263927
    0xf08070501050a1209020a0b0408070b04030210110f0328020309031e0705130c0201050717010e04020f06031005040c0c082512050304021003060815060303041503020c0c06 75
    0x1c03800700d5a654800d4134003807002c01c3e8410402c50041c08126002544507010100000d1456114806041074840c8001524a600d40c4c481245443c0e01c240d100082d00015201000b80707070180580b90868040d0400c03020745610031070007103800d4115407108255020344900005500c1c0d0407450b0f94060704a0001d6800198900700d00480040d0783e86c6807c0c42c0408055041ea01102c140c101c0c148281001000b000d0844a460400201000c0c05403402c0c2d0403110056107000c001440d031912566070039400341750303d00051419900f05222141e0072a4010010707a0007400a00e85aa91521510011441860031032403d00f0914104420002641c8901d885c0d10200003000034480d0103d50801c1c11912100d180301012031101c2280a040f8103c62880e174006420fa81801c149010a9600100114440d80c4200d83e0480303210240e04003a012210103010b0f1380c1065110810f445040c1c1d50040d501030f0802c00040440b4107081d0b94800c400b44040700101540c0000c2d80100381044203c0c0100700441c08480d04490380390914102c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 209266411 1250 209265161 209265167
    0x2130e040f06050405031308030c011506080103080903070e04110102010e0d0504061209020d030206220f1104090501020d2a0e10090e270109020609060a05160c0f08070501 75
    0x4070349025044503900c07000300b02088020000c6500340403401e140f010040d5602c0c3e50907500d1350807002009800d0b5080c0003240c0810407035070300100d0aa070442e4849200b203900350b46a140c4560844400c403034061082c1d1201184d040c0f0aa440c5611440c0b280d10386070300041400b0300090035540940c23100041039010500b03032420380b038112042d50180c0d174032850b0501e4807451260703504014218815000e5002041c07403190720f040c140e022920038881c890385280034081444503200181a07210300300001e04140d21951913100010410070354007018060007040410801015150039003282d0011000c21a00b80d5103129070150600d01400b8500c800170001e0035181e031030144d00400380c201103401014520600509030b4003100319010310401005000c030083c03410f50034507008082650040000300f6001142c8210b00341d1000710881400350b41d9840d075000e401d0b541040c2c07201080c010160844801c1c2e40a00000b801011040c0c410320310f55072040b50060094030213803842c0400104143d007454210020a030000603041c491660 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 209267661 1250 209266411 209266433
    0x302010e0f031203010b0301030b010f0303020d0c030201020d0e0d110606060307030b010903080a080601081807140d050109050c010e0108150f210606150408120306060c1002130e04 79
    0x20a03640a540402054000ba0030408108145820380201100100300c01c640e0601850589200381e40307200c0143d1301c600c258100c1c00200e1200400503800920501e500c68414070b07105d4100f901c240000340c10b20000c000160140e070b4003030401002075440115450b007003907402189180303031a414a01400743c0341031a001290a5100040021040c191245500056030f4483c0b03210000454000f8923013500d4400c030f811300130b003145000e880c01e50005482402043d00700c0030b1203181c1d1141200510080c04101e01c2c00e180c0c49039050b4110311342039120b40c00c1d440d0280819020302a01c00410300ca480031b403048076040c40000d001c88110602c0305040140034810400c0c501c500c0942103038000021034100011032140c00001d000c5000b048007031134030321007441c078035075a0404001416401900111150510401d540c0c001c0810340c0518460701295174080d10003640d544060600840c1c008801400c0b41d4500344e6000c903010b01e40503048200b44005940000c42c00c6201c4040c1034103901608541d000c3c25001d080a44400010741 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 209268911 1250 209267661 209267687
    0xc030c020d020102030909092104320a0608040b0705070519051014070908010e0309091b03091e01020313080a0e0a1202030105010b090a170309092509030201 69
    0x804a01c4481d01568001c03c16140028401451240c841c9843c843c56501c4490120a25858502d100400c803c007090450595027030301c40c4400c10325114402c50318800c903601d001c8980300055002d0484403103459150074408034082e1000c1d88807422582810318050b2140180200410700300182072003254000788000c034602000315440050f14513030038207506201d401e1803088054004100d00d0190105d021000d0741c8001403003440c0b16103480d01820741c2d07400005d083e6245805400966041080028407520701040026007007804081ca15400074103c0c850030003076038006d1b03507400305aa0100324000d0030002d44040d00740c020807240001703508505042c581800c444448001c002d01c90440880d480038124030503076482e1005e0a000349414401582c3d1250344000003c100000e038044d508100010074103850748002c407150b50304041d02c507113034079032500b5002c4003c05000507010b049400104100211a030390f0074085405058984185003840c1e40328081800010b081010700c9046c0480040e040001d40e0f0070900404a40f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 209270161 1250 209268911 209268919
    0xc07080f03071410140114040c0504060309031214011e05031b061201180e0a051903020f1005060f01020c0906150904020408010213170601050d060e1b040c0c030c02 72
    0xc0400c0d902440c244003a0403d81038442d803800140c00d0345017190400c01c904031040c00e041c45009180d40c0c1c05000903141c80c0303002d20380400c10400c800c201d2240700b544540e145070300074a040e04a40f040328141109503554515a030311b042026400504c020071020036007a039607c040e10004500c00b031802c4086900c034145d50040c0c5607580251244131805890781405c4030030141500c1007400c5a503071117020060400707500e0303044031101d24070700460700d180c0c1c0c44005081d01009801400801c018440c1318841100d0701500c2004608500845900d100085010007824240180b45000410316150200c01d002d0f0301c00502007014110340c40b4410b0899581c80e446807886e00540140c41306140303d503481d2180f810621403c403499401510000d00003502c2c03003040d40540f458142504034110310560b504071100402c201d28440803010307044840100701910306030418000c1c40d44500c0020403942c540e10100343c1466041c901c840c18201e401d00c10081580350030701c21141c2c108240c5c10018461445034a008010300044c0e4402802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 209271411 1250 209270161 209270183
    0x603060e0f210910030501031506120210020c0d050105090d080f0612160b04050a0b030103020603010e13060606080f070f020a0807020307030f03120b0d1509020a0302060406050c07080f0307 83
    0x31404003404503405080081d15003d0540d911312001002043c00348401c0d281510414000f403c0e03c0e40600035141280c04d44500c140c0c0704660341d000c0000c1c4a060300250320561003008004240d40d00c41105030144603001d240000341601c0c1240415040c068050209002c0003000f20800510b440351603a0650495001d880c0f046140b801400c00234680780681e40c5561022b01b039a13100103826800e00e0014000e88805944080c0c60940e20102c0489500080c0802503002c0b10902c014010311030741040a0350300c40a2200c07807034008241a15910200d5005412580009201004000302c10019146841c0c10044a150849920300105402510b0340d0311090300500e006000a60701d02555400c10001000d543c2203040f402609074030340790103060a07082c0c800005129003004007030621450152528004260011074411000402c1c03030100004001080c0100d074440701328070011015803101001342001d4680d41e00d441e541c400000c03070110329090055005242035070004003610340f4071030040140c076041035108500f80c00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 209272661 1250 209271411 209271463
    0xe0105072a081b0705120c10030f02030c07030e0a0302010806120a0b01080601170d0804032a03021605091603020a0203041203021b0102010b0d290a0603060e0f 70
    0x800241c280802811800002c11620200c298207101503e441d60072404441c4000d03961800e012001d0b1401c802d548042e00550b42c048102d08203090803402030045883c00041d01c41d282101002203030025074803125014000b003460001c25400c140c100c103540f18120b800c40e0309589980d00092100c0c0004124901824031582d106040050030815850000c0e88020901040c0da100d41140782d403040244070341c1c0c002040b2411000704088011030340d01030720441941c90304403e98454405a030070004441036000c030008512000d005205c02105440c564a1180d4060324044c0c0d1400d88801d4409080c1d00034a20076018407080c40403510054101d40e5880c2c071075090168403900002016801c5001d2513000c0004030425051100c2056400300301080f078031120540d226484201840124201e401ca90b1034503400c10060a07819020a42c01c54502d00501548602950404035092031030319a04419160000555111107080c000c0040d0350103081c08903920107008100e0107000c041e4299a03020101c2c80080c2c46004400c11344 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 209273911 1250 209272661 209272727
    0x20a06030b0d02210d090f0501081806390405120118030527010507110609130b0901080309180a060b0307020a0b070503070203071104090b0108060103060e010507 71
    0x48881d001041e8400c2e0700600b0300945130620505040b56007030302a11039800d61007030080c140745042ea5542d031140084903040100540e401480941000c1e56848404401d5407498002c115080c400d0901c2410b60301c035029070905101200c1c00f910004407040440c4d100b001d2a252515040d41c04881080f44c0882c0410340100c100d6005002c83c0800c0402207040b02c0314141456041030041401010003854000814540110340c0400240d01c04000c0c0015010442c075404500e041d0820f0703604c8400240090b01d03194182000a00020b40000d581d0099906c4550324581c86c07526518050040483e9005949040d459500207181d41d50654103002580310240c001c600c0e00e0015034030071009881c042c40240e41d01c1c1480300001c2e40c0c0f96050142103030245011000602140e107d40b0940b80520516001141004066030300d01c0713012103200a0040e001039031100d0752800301d4820080e00b03008120b0413014003102d50550418009846120288040f2070b0304cc0020701040c41d0303200340962080800002030b00540b40c003114081d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 209275161 1250 209273911 209273929
    0x1a09040608030c0d020c0409020f0f040608011a0102070b070f02061804110c010b0a080c01050a03110d0e10140114030c04090803060f12060a1e09050c01031404020a06030b 75
    0x802001d1002007442500007a0015013545502c03001d8086810207104001004180d0b0701e1078100039007001c621032910407603007089100c8100c2d4081c01803002c40c00544800d900e500311405040d10204a0340382c0c80702c1e000c0030758040c030545001c0c00c024520117103000704a45400f101a401c0c80c0e80203020746400a562030329161662440c00d14924001c5c824004030a00b070844801c0703500520740c07400181d480c1a48201d0f480c50110f2000d01140c0d0840098080101d0000056a240d0004240c2c40e06054075150b060341c00600b80c000520300c0300d820b180b00103440040901101e2500c18a201038100b6127103445001c040e0f444096001d241111907c00c80350000d1001304011a08001031840c940750480e04000904c1c0402c0255006984542c5042e1184400550928204807e4210490941415804c04004201d900d5a03642000d40d1016442102c03400c3d80f540040303140e08850007040103403243d0300306051100156905006240c001a510407540e003d500b0180c0005c0d20300c41e214850385040c143c0c1c8128840e0f180c0ca03a0350398 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 209276411 1250 209275161 209275169
    0xb060d080c01110318010903080f0a06030b0c04061808031801050d0906060e0a020a05190c020a090504030315051f0324140114070f050703060504030f090801061a090406 74
    0x902560810868101c1d45400540c3c00745000d0700154220800104140700e540b09035038050343c5440103519400d1140d00d52507405480c0d00380302d07900c501c00400031a14039050540902c141e448540c2e039651500000611107025012e81d000102e03030b0302c1d004005440c00007045e40c00040c0c1040d002c2010582400068459101d11200e0718244c0b07042400c0401841801d51040040f980041c1190310b0035594100403204a108651203000440c0050281e40740662510803440c80d05c2d0000d040c88809559690005560028a540501b1401c0c0e1180104820943e040c004c0340c540c031640041d2258403505040001d404401d450b450f504002e6000b0345821880e6109811040070b07902014034410980188506040580100d4000d0080c880c59032046441203501c107910280c1040781d0780424604000d0360340d541e07103040181c04030281c40902c100750b80400858501e100b0305018510030307201c440000c10080c1001d04000343e5507112914a9151a0040200680e5400701a1135017104000407a035174131441c00018010055500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 209277661 1250 209276411 209276413
    0x1b090303050901230901020c0303040f090b0402041d0a0b19060f1206080c010207050f0a170a080d0b090609240102120403121b0203031c14040605150402070b060d080c 73
    0x141c22604c0f035503001004402c100380e00b075851414019080c0340c0d8074407691052030380107101c400c0d04000c0e01c685644451078180700100098509650f5240300c42801c0300c1400c84000903482d220521620407114810084841800c2d00d14a001c20150800c03101d01e011507101c1c2c9000c0c0035200c62042409803013015401344910040034100106078946c0c1016981e0034110326130358054400c240020401d481c12040c101340301c1e00010042241141800d65611840707151540f003043c03502c0744070044000525944040c00e40b580780c8080000d1300d95910002c109520034050005400b410f112010700281d071818502108440f42c05058014105084400403803410140681c00302c41142c0200c0c1c04810481a01e402504841b05903441c1c4030240008081c0c290000c841c0e220003540360b801040a03c58103011a81444000a481d141c0050700c5200014003140030981294102d9084d81e88000300940582c140036030645a01d01550118106501503850841d0480050174051060701c0b0b0701c42d032a00308140c8108840350326094070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 209278911 1250 209277661 209277707
    0x180e0414030720100203041206020c030f1813020c15180303040606060e03071508040213090c0806160206062e0e0a14090a0902040b04020a0e041b090303050901 70
    0x62214081403516074040c40c40344c04a0401140a14400415141a00c00c02c040107005e048141e03072501e00950100b9403036000d501040c00b2100720719590340c02a080d07203051495103031040030b4540700b0410301114003201c031104107105101d000700041c00000d17540002004240c0c0c460080c0c4803801904481d540076000e640300d44c0301c0001040304108041c3c000804030340c0141c0f160100704480a0805841e90014040c0701c1121031194001207846106454240e041030000d001c14120b402d690303170610251100d0602c103651000b201d660030041c40f1400c120859000760307401c3e08400400f401010003906c9481c0a09400d110340c1c000309840c601016049100350b08103004a4081003218603035075002d0f044584003410144180c0d0b0b022030020703030015002c209403602e05008090080d0303035855140b160014a1200c2082e0b03005580d9a00c0d15007540c071688010310045006464102007075080504000981c0c1045260380079030111000c5074560b058000111005907a0305084c034a454955810040b01c03001020504284c4440e030324 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 209280161 1250 209278911 209278943
    0xd050709020f0c010c0804050a12050d0c020f0d02121b0304080118060c020a0827040f060905010b0412080d110a0c1103060f06040b010903051b01180e04140307 70
    0x700404602d5040c000901c84c8688446050791030040445010f041c8c0d400281e200c0c00000d1300041004200c1c2c219080c480c0c20841c200d60824101c3d94060040005640300354010035001000700030441c02c05000740700520300201c04624801590117014030070b12011030345a1400d420048184190380181044400070001c000e842d580c403000c0f152043d002030f11034526010842c01d0b807601c08101015900d0b04009001e20f800703824010940030500c100e2003c1c3c40c80945072003040c840c1d51a8001c4203019040001d0100e061806c00c2c081400b00c90041e030050a582004110410482036075003525501150881d580d10b84400d9038000e01c07030142403008010901100c00080340e20305250090719510b800e90058001c0030824110f8024180d0f520710075200002c54415038000501e0618241e003004c0200e83c0c043c9000d4280503502d40c2e03424034000101161f003003c0010b0100032a11540d0181c242c2121920070708040b62801d103040000101880b01400c0548920070400204030121010021980303aa40d1001c0312107051080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 209281411 1250 209280161 209280187
    0xf0f0c0305060a06080f180c090a0c0e040e0a08071e0602120106021605040c110703051b1c0201050f04050d0b090610030c0b0a032307020115080604020d05070902 71
    0x402c4803024030a00700b450703000c6001441010b02d5842080300c3c08500c499a201c80700d40a5400341c090210003180e114800d10240e19894410704140a103d030440082183c280c00030018048842030000b050081d464402c48a940a000003201c1340615005441c007561035030181059003100300c24040c0007080c0300490b00094200844c540c000d062900d0044011401079032142400c98540e08455000c8234100c180100074400e900d842d522188440040c1e0030f10741c10303140403400f000d42000000c1c3d0091780d054000000d510b0f06c520781400d01503540e100c2290f801c0103541040380c031107682205002000e0b04100c07011034040440c28054040310040d2000501503400c050035031a2a1310444c41c201c80601c498000c40010481074550556008242c03036115404080782414406200b01c1ca03042142e0380c408142d1185540f40395420310882c0c680c081d0100512200c124a0300345800303802e40707003959011900c0c022140010050030300c02140c8150040e5044924a00c08181030034240d15100e0b80b5081500024400140c02c0780c8240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 209282661 1250 209281411 209281421
    0x1330905040b010e13050702190f1205120f1003150905120309100b030c06040e0f1b0415030e060910060f0f0605070302010e0a080a110c010905040f0f0c03 68
    0x1108480a2090810b02401121802c00b60000143c1101110a071301501c1410354008541c840c0480c41207900b403d00424207004c0d9401c0c3d134070080d6681c0303004d003503404140300c41c1608542e064181d0b0704010b442c0484104025550500c006d180e0907140382407402141c2d0320071003185070800558010008201c110104030b01b11004140c101011038a61040d00c0c02141452007900c1a41e11644611f400f0f003046454195211001d004074201403503260180d040000311039500c01d4050400741003881c44518580c81e000c82600c1103100041e190302c200411843c002120f15045000300d905844103000b2444032018a502c0030341c0905954031400c4420b0203000d041151a280c0020103501d00004038006000841e40c074010242c02c24071500599200401a0b001400243d01590051442d64868400051011440841e05040890710402103078012400905050700c2603100103034003414000c841c0640821240500003a004900c03611440d40295102d040d207000c1401d850380540004520f00c6001d11411085040c0100142 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 209283911 1250 209282661 209282669
    0xa0b030a060e0d140a0e030106051f020f03030405031608070501060816050f0a1208071403030103110618010818060c0d11070807081303061404060c020c0306013309 72
    0x100c03440142d182c102d4490001110f4024240302071038a40001380d0703411900b82ca00342e00407a405648581000030ac0303071942c03103400101210000e07400100c0082428004c0c10b1003442e140c4484194028024000400e10100455880200003003000212040c1403411000345e00800e8800b030541d500c0d00740e00180e90a00801d40188000c0c00c0080c01d01c40584803801c0000c140f907501c0301340d41c00501c41c500601c0014080b60540d104a8001c82c0c01070300300740f19517841d04e0046441580d60040ea402c00303c010000c00c4100c4d480402d001d070f021100e042c20100ca001f50f400480840903480c904104000d404030b076024052101e840100440c1c0800d0712031a15002c202c0e09410791000c00b46526280c6814208058a09180c1c1a00c0029900c105002c1c0b0f05101030b25900043e8000700c4000d2a03a8901000c0000015030324030a919a1820386540d000e030070b1509050400c01c8903d043c00c2102550003121031345015540100b41b0605654844041004107010290190084a070740750940054000343c4050000c0f2541089000d0200c07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 209285161 1250 209283911 209283913
    0x70b0a0b15030a0c0e0a0b070b0c0c0d0c050705040e0a030e0f041404110103050f130611030109150801020f07030315080613120f0c06020702130c0c02150406020a08030a0b030a060e 79
    0x500c0417411702250200c140304076920030100740301c020009400050303040e0b0007040344e00c0140d080044400c503460820001c00410000305200702844000c004044c41554014402220104000c004003255140c5890425100504005c255016810a559160340721a80301c500a8010041040c1c000d000c0e6206e840260b0b4155812120258594025880b070700500d0f01c01c1e410180d00a1194456035211055007500000c01c07034099490710705055040c801c01c000b031070003800355032000300340c0968000120744150041e410501190f401088a969001160303001ca8103103541c580790000e44100220b4041c0300d401e0840d00480c0c101d006000030701c03901040c0d2103c41612140103005030300070802c00c40c80a0f01c8041c03406d000b83e804241440401d0700420001c3d4007a003403e900103031030700805903030000c5040101c071144a031403004074080c21154010750400009040b400c40c003100c840c6107410700b0210080d40c1c1340d080100c010840036000002400c40f04040d0003000f1204009030803501e4084080c506403010b001e10303e4410000f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 209286411 1250 209285161 209285177
    0x601090303120e0a060629070201020a0b0903070818010809070311100e0301020f0c060a02120403050901051209060106091e0b030c0d050a02030402040e012307052802010e03070b0a0b15030a0c 84
    0x14152110b08481000c9d50503002460100c40c55680e40480d0b070002800a80240000c0c805007000c40c18050080c041182100512450002c1c0c08002400191001c0d1104001d5030103810140001040a075038109908800c495004000c104a00c04031052040d1078000390700741d40041061107109501c0d0f00505082c036801000d6620583d03648401b0812809481d402806032520040071401113400b40e002000b00c50303c185082850085200a0f8070381c0d120003528450a281c0c001c0e00100503203030384000130402401000e02c08040d140c00050240c078280c207050050207240400040401c0f040c80e90001150700304600a1418840e41c07801f0810800250000c032401da000f9800d002d064050400c0620440040145e580950740d0900c038840480c44040304000d10003024441c04001c1c4500b40594043c0c80203509030f58080301c4410040002000b0b09468a840001072540e02c1408000000381240c500c060340310081e144002400000c22002840348485917800080b150b000100303021300032041e0b0f0006a07000b0140e03142c28403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 209287661 1250 209286411 209286479
    0xc0f030c011b1e0815090f010602070f06090b0a0201090519060f0e060a0b0f041406150307021f02040e13060b01080606090904050c15030703050601090303120e0a0606 73
    0x10349039200300d07000102c0405050b07041c8042030084401c079405c94040f01d8250014456200442e10880c002c1e94040701300480600100806541040030001405004410302d1205140500141072074a0300d0041418980e000303e80300b11041c2c0f00750b1001c00c4403070b00301c0110b4003c01c0760b070047d910580c0c3c0300c0201500c85604100c02c000725100503000d024030b9007017181d005101079650144d00c10001c0421200f141d600c140401107440ea10303a80d43c003c111042180507089506801d2000810484481c0142d040d0034001c3c2c24810404455004108400100000e130700c00501050030300e000c900240f203290050143c258109040c043c0d4110419000140e0314407519040010304005030042d06c4000382140c842e540040d0401070407407682844140b507500b09204000716055145900005501d40041c201702c0b8400c02004810041c900e941405003070340100081c00c2c032503002d9080d0789004120110414202c1d010a480740c032140a00c01042140d8551150840c80400c0040d8451b4510b09406803511104070340b1a8511003191 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 209288911 1250 209287661 209287667
    0x20f1f020d021603060c03110c03120906060f060a090b0d050a140103051b03030d0c170a0e03120408090a06090503010c03111b0304030b250c030906050c0f030c011b 72
    0x109590f03a960114901c0c545941d4440300500120130401701010b40b6510900c2e604090a40904010401400516158100d014984200381402054aa2075a00003001d1060320b0b2078080c0da14603901015a030b0541e0b1804481d1060f200c0c07650b5a80b061440c0a40010003801004407980280d001e0715a0920500030340a9001880000c00002e010190140e0000c003a070500e01200709140c401c4049018040e241007001d044c508c0c2c0101c0300000c29402c0413441d0038140310540c0c03019500131075110b0303450181000030100c0030380415664040ea00036070399900c050741c01203410711011304142c0c0c41080c1c009003400b0b08c05455400c000e203021000c0c401d141c080d600b407552002d2194000c0c002d99044201036103c0c507041103980c21402c5d80521803c100c031469400204008004142d000d01810321171041880d41052444042915940554010403c2400c1040740d0001c01c0020b58084440c0c0300319815450403d4482c41e40d2403e003410601600d0710f1041501c00000c0c002d505541c190424840300b4502d1190b40042450781c4015 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 209290161 1250 209288911 209288923
    0x1401170709060e21030a0e090708011e080d02100e12160206070b0112050601090b0612150a030515010e040f1403040b0708130515090904020f1f020d02 66
    0x2640104814420a024240c807440701c208103c40018502040c100c407004100303605054070f40300c0c0302c80d0b6000003030307920b00594004044050891068a00305810f00d82108020100201030003010105408010440a03c1171140e00100181c080c40301901c5625015020103507640d0034114054049509000001502c1b00c0c0200d1810450030350903c405140c000341e483c108041030041030007243c0c004000d0000101003034070104100d020700035020b404615081c039801e01034503015050740000b442074206500c0d002103480b0a4107031803500d22241a000081e1f1120341505022513400114581c00c0854400004144100042d01c100c01c1d03a02980e10900598a5007502030350583d00b00c2c1c01921038000c01001c0000650075100300401f03005070b030043c0c908241d210080039000c0e0b40080d41c1540c41200100b0b03015800b1000c1002a8003c1c102103072100b40b18040255200324070b0003031130342180c4034680f0080003800b591604059030041d0000103090a540307040c0b505004200c0030904900400511601c0030007000c184c000240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 209291411 1250 209290161 209290171
    0x1b06020a030c021e07031b03060c020a0507050906010509060306031f020d050112030207060507141902090603010c09090f021902010c14030f19022208010b0402030402060f07020d050601140117 84
    0x140ca05e860440d152030007481c640c941450b60a01941070004003054080c41101100c2000394041e001c110740d50309190b440c007240d9402c0180300346103850038001c10f60382200c101c90b01402c0076941c281d265900d03800040c3c103100044501c646003000c2500070070307903485440d4010241c007020314808000598039080308622403440e030a4000c1c0035901c21402030040307500840c00707442c40c0b52062141c5030700e844d0220b40b9036007040c402c03000c25901616403d440c07400318503001c0360300e541c032002c00c1d0b0080154020b01600180101c000d881080030295607400c410311941c42d43d80454281521000f5121680c014180009000781584041000001e110181c0d810175100c81900702c9000d040007031100d00854440006991140241c0c610904c0056820450381d103a070f440ba0b21107440401d100c81c1e58031600510b0903024034251101c0f800b91038031070b5204004010060391504142c800c03c02c0200d94003030b120012480400d20354030b600c1002600c54442c400c00011a0311211140c04074802d400c0e40d9040840100708081076400c0c1e41511 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 209292661 1250 209291411 209291413
    0xf0f15061c050a150812030c041508072a030f030b09010f0311090c0a080709050d0606080c0321030402061b0309100503041a0912040603050105041a010c031b06020a030c021e 76
    0x20400e03030a1b8100e000743d504441c54940c050310301030750f50700320700a41315050440c64045400c0700100000541c00660f2404c00301d00135051071009524012480c4481c1d14030729802010720040080d010340030791280e40984040d0740b0141a13510700396100c04000d104051184001c4481400d40b0b400e000d007504005441901a411814480c3e08080043e5001d45040100a00701c170300700f2000d142d0003c0c00d5030700c07050b4075942e19024810000704142040f20403802c1034000c2c01064026808104810f8242c01c08845150040702c00390656500d90b2038070b20004500c3c2c442c002c603140c2c0c0300c0701d000c00ba003800f030030044000c0184d000220384040888c04444800d486501084401620000030381c4401d88055080064007588041c40b401550190380c29480202c100d50800d4001c100003995480042c84607040501c581601001700c042404002150070000a148440303048000341040160070943c84103d0100c813180301d030150b0144055403104103921000303004012059501005101c1c2c15440501c08481c103000810402400c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 209293911 1250 209292661 209292673
    0x40b04060905041a100c2916020d020a03180803030108030c0c030a0206090904020102010f050c070302011802150a020703060f09030e0906031002180a060207030b0f0f15061c050a1508 80
    0x55800e4030055260181900c91f50304074107001040041060004512100103884585241400c0c401744401c0e10000c040301c020b40d44083d00b51a0259000178941070344a50610341070655030915668071280c141036074008401440040000310f038108010001d421589911422035146848036007c2642d01c0100c4c44019410800030040f6801600f07000000c154002e006000229190903120800e20880b801200c025241c40c8000c14500704055080c0580b03807210b0407205a820303403c3e4668000070000000c50f20303400c0e14000d00069141807075000344000c00085401c64010030203001002e03002806010001d204030001080b103080d08950b0b2803d0407096004440c050000c0c8414205001050004e5208904501340c1d03c6920b4801405a90b03149501d201404080d406400103a00c0d601d003c9441e00000360070942c4e01e51043c4100400492005100c0354805000d80461070010780c001d005c00c10b280728401d20a08502300342418425400d42e01d42045000c0e0803851010400c60242c28055040c0080c5402110f403103070001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 209295161 1250 209293911 209293939
    0x111010213050f04140718050109030b06061e12010906050d03020a02040203060a0513020903240609040f08270a05030601030f240902031504050d1202040b04060905041a 74
    0x254400100c802c00a8400140170450003110b6000c00c0341111520002841d41c09442c9900c1500b09402d4001c1c002030070081e40c0c480c19a60350042c0c07984001d01c4140656004606c050169032a60700e41c00d030203040d4450955850640440c0403941d480b0902403407200f5414690002100d04101c0c011507005601b69015015503840e59081102a40c4003402d020350003541010081100e41d650f2002d080304100701c603401640c036245a002d240c1020044140b48070800b00807009007468403091843d842d4000000c580d0f518007030381ca41c50014042e50840c000544114070100380d1031500041d039864050f400705446640400705041760200814101c1d42d00034940c1540080303004100103001742903210b60380743c0700b20004840102c1001c590001688c1d50301d81d009449480360401320035814180490004000c002c51640380a1134642c0720541d030341100d21314400401c079000d070503a002c0310001e6054601030412014003e9459990351002450142d290045034030592800f2420f000c400d60440004580c0d4030054000901d9200b5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 209296411 1250 209295161 209295169
    0x10315050601170415060b0a0504030b010905010302010507080d020d0212100b0309120d0207051204030606140a060e040905010e010b0117070219051005010308030a05130206030105060c011401030c05011101021305 93
    0x188006170080c0341d8a030300010a00164240140045240550740c41d51181d00d1414012400c20040c4e1011000e0703443d002c014000360741e0040c1100d14071500078403000c0d0707141103120000000740b04000d0b0380125944080340481440c801d0310500b074002e116440342c80a0321074903002440e0040c803043c1c0d08032015501411442420050742d0024059487c80c00b07a0050900100d07480d5542042a0490401031050b000941030040080764450100030742420070b00010301c2440c190103d134550001340114020311415501c400069074031034101c00e00c002d5011009001620b030b03584e5520302802d0309112141c0400c1e221409945149900e1403018480c01e01d40d801000b5031254803850720205100e03048169950f0040403586040b5501901a00d030081d44284c0380309950380b03071003104003040b02c40240c40c05041100703049840000d0381e5400240c905680c1c0c12940b841ea1602d4441295004008072940c40c01c0c414002c0c0000014041d0043c107020450f00c003070b25000e400c0000700d0b10b172030300300d1188501040900d285d00030203000e1424 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 209297661 1250 209296411 209296433
    0x10e070c030903020612040b070903031407020d0f081803060f0a2a051e0c10050c09030f010e06060603160e010c05060a0603020f01020c01050304060207050c090103150506011704 78
    0x100905015101c2503c0380c0201d6200d41c0200792400703210707510b101800208260b240206a1068440c81c0201c0400d0850b034000b00000c61006110141510114401b429556207007c06541c440c0d104080501c054180d1629440e907800900d003101d03480702d00c1d9142a080703041c045011442503003c405181300594070764441c100240780100b9185138404005949003611110315591204100c05616029140c50b024120b104000035404407110305c818003880600654034000075150303070b030314580d40300810f5580d9100c0c1005402e018010701250705104d1180c40080c003203410b61090a1500883d42548c00940c1c481040c4031a510058809903220a05040c50205184c4662407900c90002c2c1494160042c4a850300c1c4c0c03038900642519820f40070f0f556604104114a00008840303200802800500101084070780080d01a02004002410154000810a040000071300003030104140052241200d5616400c2019441c038549160101141c42d1001140181d0301518031101d03005075846844000342c2d1559113201e400c403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 209298911 1250 209297661 209297663
    0x12231612090f0b04050f0c0a030213050603031c0203010e280506030c10110d03060815100308030108030a0801140622052101060b030919080d020406081608010e070c 72
    0x80b40e6624500004a056000d03038015805900141640064a8903250604001c200c80d18422400d080b420001601d502004048900000c0380000d155643c03440440e04501c00d85e0401c4591700030314191017140c01183c0e4051030694000014928481d541c421404100342840300c0503100b4289880050b140d404003640090303a1000025090740c1114280e0750206030000000e032412404101900d26030f04500c4410440c82106480ca8030b0706100c65454403000742d440f8041d00d505102003901c250f0001e403510501707030700c4480156404001c60741e4035a95071100329129040000c501b000502c0401c00001e16881c1980c0c3c004103003030000d00542c94503444078050504041800c1041422160700e181c00190b5603500d0003a020112601b8508801380b03c030400c900c03421586503411140010005209004964038000349440f04845c0101440a01c0f01180c10305804601a2004080e050790001801044d0958041c0542e40180d11440800c1c0c0803142e070450985008000b401400600c0c012000001c0b4814850079038480b8203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 209300161 1250 209298911 209298923
    0x7050102040e040609120c0b1f080304030b100603060b0f030a0f0c031d0f0d14120903041730070203100c0f08010815071223161209 58
    0x542e440340010b8201504a6003500c642d6541d071411300078010303070740c501011280540c580a0b640c01410f90352005201e00c0505017107044800f1000700c192a03c10703410381c00090a0b0072401c603500e40e0740d20320708090040000c554600c03242c0c01c45000005c206000f4003400b0306503400c2c001060304101c4000008100f68000410010030180c0320320403004107507041d225114480c40c0aa90216100e16078001c690b8160700a001d840b011076100440700c0e081d0b60800b090b070412580040c5861516126071400200b8107000301000508030101020920010350320002c000c00480c0d440310000c0d0004450f8124540e11500a48682d211018201c604555a103540c03181c00704a000c01501d40300e00301a410740219103851843c00340040903a517941120400e950304802d4956540000749031844030b640c1030440f03d40d110604129243c000045003000700391680c1c05070200340b400c040310b08008c0000c41088682d6110859001445140f111605400304201c2c070070000c1700c10128205902c481c034031010800307044801040302ca40c0582c0d00c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 209301411 1250 209300161 209300167
    0xc04110f190504050d0f110f150a03022701020d03020703020309040e03040f0b0d0e0706020a17120f040303050a06081905120a0c050609010612060506010e100c03020609071a07050102 80
    0x2680c40111045c1480c0c0100040c40180781140340016642924a680d280b10b90710038054082c0c640da51001c01e08420003810010b6403110403030b000c25000781c000c9661030444080c00c00301d03107064511006451a01100260f0032560f45ea94050026000c922907010b020340160400c109500700c40c14241c00170b1442800d0f50044a19059503041c05510000c4650000200024001200400d50b071250281005c1403400b00080c1c004d540c40e0903c0695160203000700184862041002c441407152100c1c06d9031000d0004014004a03468442c1c0d4801c1015011a41100032070316010119020000030b12030601542c850030b0040032703a01001c0b10011001502c0840c11919881540a40014000300601a01149950303469851892070185041400c154008000700d103680c4c9000000c103c146605c07160042503e410450020f125200c4200484e4000e42e14810141c12040c4034000e83c42560307014144500940c082d1b0300f510156151101c2d89600c0701f160742f05042c404c0c40c061591142d6450031070020210588540d0006203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 209302661 1250 209301411 209301419
    0x3060b130c02030d050a020909061c0f0b0f1005010206011a04150201050711010902060a11010b1206060a050114072a080d08010b03060a15140c0c04110f190504 70
    0x4195101204541c0040c3c0021590003000c0d12140070311500545515410344c10000c40c8008a81c0c4100014511441040540764400018002c2110020001c1c0c2106c3c045101c540642448620400d0640e40d100c002c1034070b0b03000214100c24618038002900d1059001e418164030304800c1603030704854143e417540034641c20440014441c013400c10080c00883c5580000c200d43c50021005080b9810041c07a04842da414440c00500503070301c0a044403e07600301c83c00d090142050442d10304d401040e034101c0c05500101100a54880d540c03001611070310440c821289510318130385070001114240c2d80c12240548002051105c1c40004144090f481c00d010b84204150042c1d040201418080c0100d607802810307540c0001e481208140e51043c00d40c0d0262083e840c0c018070703604008021840c1c0c0c003030710b21035162078100d81100012210300c9034172048400303005900c00903101c12480d0040b60711980401081d92241d49000001c0c09040c020101b40c41402d4041807040c2d003402d13031030708000d0708520300c2907400c40c200f00b400c000208d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 209303911 1250 209302661 209302699
    0x3090d050d0b060d09170c032703030c15130305030c030411090708040b070518120c030102070c0f0609150309020d0803090102212a0d0618061d0103060b 67
    0x1001c1c8501d4000046a45e80850a02c2c50404040c54031a40c0098030030004d8070f0411000104445207030794040c28448600c0042081d440503003842600d03243d0305001c00505c140c940324000400340c8480c00e4164196003161280b510ba21500304120400902044007400025900040c88000d1175200740a005150051032500c0009001e001003124010702050f07010041c0010f22100340d840680c01a020700b04a8503050407000c0840c81441c0c902e1280d4420510380b46074424038101804000391811018009540314400c0b4a00700c0f00151480c042c01e52003140340c0380e000a215114010350070840b2424101050b0b800c41125007240546111007003a40c001c4809402c0030002440d007002103100b01d050400041e11800302d40341955900d8602c09130222081802c0003844105c12038014001c040c45160318900c0e089003030864840b001c5028946020450f01d26062000480090b06007440340c3c2048c129104011640e11051803c00500d0268060005121094010b000240180d8014031151100400441060303210900794 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 209305161 1250 209303911 209303917
    0x190c0f060507021b01080103030e0d022e02010b0301060e1b1306050306040509060601050a031d030708090109080102070809040e011b090f0e13110a03080f07150203090d050d0b06 78
    0x140140c3c40500c040c4c1202e01040003c00301154246456181d5500d5501c000300b0180045004034890003042d8060380855599003001000528a00d80f0000100203441f86a86a48290200e08000d5400c02e01007546514042c4114416030303500d014100b070f0b141c880b000924607448070721011441f0180c0401440c010407a10404810082500355280d42e581d00d800d80603c0b080da031014140e49000e5102c201807041c103a801400341d80d00040d42e0300d00000c0031740d14640d000d44071002c0d00b12500b00c00e000001e4020705110250009000d05070082c0c03110018562b40e80d01c103074200c0c4200e80300500304031170510410741a0f25160300724a0301d2424140c00864844040d2a64204001100d40c4510200344001e40812013458540030f00c0004000381c2d1a40240d0703280c800b501ca40d81c0d44052000611768141071103101c00ea6601c0443e408044e541201065031a00c0c0f124907120115400078009444050307480022000902c214001c49100c1d1441c4c0b009440fa03001022810381d000c0c0c110303900402c4030030344a0500900c15200c0d0317005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 209306411 1250 209305161 209305171
    0x302030c100c120504120305070207030c03121806080420220c0314040213060b0a11070f080d21020d020915090109170309120102031006020102190c0f0605 68
    0x10020b0241c0507480068825084499620640350400d01000301040203c1040140060103003008500c66507903000c22800c1170f0780d07038000900c10a0006000302c10b0041d90a0144034540c45030b2110070801d00b2040c01f00691801a100c0c000014161100107000220141c00200100c04642c0d405224429446c0014130040c0380b140c0305d2001c91038814601c208444041c041d5035081d81d0a410104040325442c032159120354402403010740a528010b82420404403254459402000b00c01e15032134031103040101c0140106c00f0303035070f480e0300c03030f01c900d80d008100542c4461407641100d0440d002400710010340242542e504009802e1400407900450103445114154001450b01c0082c0113001039032401c0e00e804000160b00c10a8041040c03800074401d220803a49c2001051050720308520a01941c0307031610b4030a91641c8102031010350045228543c2144035101500a580244481c03004502083d44440b422800c070300a8617a0061180812a0a5042c1500807410001c4140c013411191940300c946403541003d5404c1070b10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 209307661 1250 209306411 209306443
    0x50d11010207081209121614030f03250806010c030c05070512010905070911090618060708030105031506011e020f0d081f030b04022b060c0e031f02070302030c 70
    0x10845e02c01003d011090345001d03801000b80c2854080d0203626060f07010410018203450f1070000e29007445008000b5604090000030034246e9134a0200c0c000a07414407503d000034400e16001c003a002071701d4003502480e441a041a52111410007090703e04480b100c1c50084191510701036000c01240c0c98540c150038100c0d8000701030000ca040e6000b488c010703140100c00c8d400078415602e440001e405403d014402c95090340300c1141d00984811040c64605442c02a03100e80e82da00000025844040048110255049460807010b4481242d101500780c140c0000454880c6d000848460342018800004442035000c0c4000c1d204850710084004201440c1c00a012160004110107000300301c00358041e280e1008100c030103204500b036a18610340c1e804805440180c4000d1180481081d121600c80980d6031511018a100d445a0034100050814400800f17910510400040c211246c0c12010308001502a51a2603101205889a03418140c1d610007500714280032000c41c00200496071241004000b0003030b101048070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 209308911 1250 209307661 209307697
    0xf070611041505090a032d0b0613050415050a0902030703050109050f0a0503040605030a0b1f020d03180b040c180b101b1104020903030a0201050a0507030207050d1101020708 76
    0x1010442d0030010b40116001044003c100c1d03403c8603264070509400b1650b00c0002c0800110301010090081d071070407503480001c0031150090b11305002038803007058050001a11241d540f60075186061b000c0c0c4030102c5010f0045040b81c442c0d44886e084a0303002c00d0b402004071100050b0182c1c00c0d40002c0c18500300358002d0b6400ea440e501e624041c00010300000c004141030b036004000c1040556161501d901852046100b44007020000904815064000700e0400d94010801084c0c00b2044609003040d0b41c011a8010051041d0f80e010030245000340f24109182441c07078002c0b100000d86a07117861603464010000c0702c2c603100800000030040380e80000381c00031a00b8154042540da004200f80501d802c10445441e0070041d40c5212840b41041c000713484800309030003265481e03410342e40d94040b402900c1042d5800350184400200382c0c00c0941e040d03020b180122100117090103562120f9000720140e0103031441c0580319800101d420f1b24291700a00c045250300c0d00d698005410841c66480d84102c9402994180402214507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 209310161 1250 209308911 209308919
    0x1119120501050916091a1507030e0108071409060403300206040b07050d1508030a091d0601050d0905010501060305060f100906030f0e06010602070e130b0403050f07061104 75
    0x2e020301540b2541d03060040507440c88031000c40b40030350b801d4490800c0059480380201c040207100201024400d4000e0940d00c40c03059007100403d00f50340f0000c0143d0010b408040b1350700307803076204040c064003482c0c042d9a441505c01000003990300652003860300540c0980f0401001002501d2241c8102c11028816041c600943d9950341e41c080c00c103800008003085400070f40170000003541c0c5241d02c1c0e410100034a402505ca84000030190f0040c214080c0da104440d4542030b0014900d1000030007080344034459a1994000d941e98000040f00100712200212500000c5001404c20352080001e841d0000210038003240342100ca45a1030708481003a0800e000003a00e4008026032814001c00c0d05c4203441064410b0f505621407800002c006440e5402410201612140b1401c540111030f0401c03a04035406605403031565035100006960b03401d141c4602d200310790024000480c0e141c81c8441240c80c103600800c10261aa50b0381e80c040700c55601443c5100b482c2c5005015010200c2e60710b20070300030341c8802900d11035907031414 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 209311411 1250 209310161 209310163
    0x4020d0e060a02041a03042315040506090705010813030509010207030605040507030308010b090d17040e180f030c060c0901090315050601110102090d020d0204020c100b1806090411191205 82
    0x3500e0400b000405d403c005110024201b0300c1d4020b03003076001c030341c026581455a10703d031801c0404100800103c484080c040c402881030104e003960141c00792000f00c0d019281e585c00152401a4101c1d003054030313801c200c0105404240124010169000148155020340e512652201c044a500380d4090b106503110707540030710802d90000ca855014103403480205090403815070024400d41c030755440082c400f101d0300d4610024a0b02c0201602c0150076134620280c4a890030041608a48158001480700c0d0f00c16040c040215501c0801169841c2c0c0500740038080303070340d1940072480c5940c1c04200c0b03980c1040b80700b000000205410103012500c0c003145d10800f00306801c0c41e00004243d84441c032044c0d000b90348104152070041d03071840045207103183e05403000001d071240d0703000207030083c000e4440059460081d60200e40322428650300460515204640c03050903011251403505802108480254002410a003c540440d202840b5040400e4000b0080803295044d1180d01c0c0040150703a11541544241450b040d0400c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 209312661 1250 209311411 209311439
    0x2503020906060405091f120b1e0903070b070e040c050307020607030e1b0f0604121401110f16050102040612060801110a050f041e030201030e12040504020d0e060a0204 73
    0x40300310b98150515040c0000075101204c0648071b141c2d900d580e8003490320b0780c01e0b0300c0446500911056800042103074503414601402102115040903031909000c28400f528480210342e401815000021401d140341a500d0748046000074112006000c0c0440246409680340e004101c2100b04030b684d81070f124180001d02034585800501048145400c090130350805ca800042c038440d44200081e0840c2da1410081d0101d5803810117001c9040e00000c0025002c81c041c250b04e00010040c3d0300c502c0c5008001a50365081c20308039425001310018043c410850139140e6030228001d17101811004543d5110010640d83ea00c0c22a88158041d6010482d41058200f61111522a210040c0141402401840134045003091079110382d40a140c240070f404034409000072544410780f070103480c0168003d1204150052030007407101640c8005c0340080d092499a000c03810012405d5440000b55040032820603082c0342c00c02c00030750844c0c10381d81045d66550780d41000054003048654042c058600c030040e952420040c00e440240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 209313911 1250 209312661 209312671
    0x170a030605030d0f030c0822030c0b010803071e08030a09031b05060610090e0105010305040f060c0e120309010c02010e0607060609022d0f0f070f031d0406050306040f0525030209 78
    0x35040c082048023080150a00849802040c649003512900c0c682500c400c2e09145d0050510761a880c0040380800d00040100317803640c00b440c5071140f1101403010043d8129802e4074000c0c03d5235000d0020540c000315542001c068648a810328100d05681111803140d9070000f4803054469074801c0e010f2040351b040c4140087d80901807450404511800e00051140d03810040c0701d401d0415039910000303003e00115110165030107074810014024120002d0b001811440250b400c2442080448202860103a0000c1207466040e010b0310f0360b50a0512907001581d11508044040307810403803c01c10200011940c4c82080c001d8032065100585500e58171409140c02d5800090700d04a1101118008000c2842a0140c0341d00f141981001075032452400d19450141c020382c80300409002d605402001011b40015081d4641c581152407455403c428a003007105075000740c41803d170142c1040020a000c50010f1600d0315105024004039440c0d04440b410304912042c503141c9119602018035814003c5240241409401c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 209315161 1250 209313911 209313917
    0x18190c0b0f0711030a0203030a020f06010e0402090402010807020f0a030c0c06030504151a040609020d1a100e04150303120501080c130b010c06020d060302041404170a030605030d0f030c 81
    0x201005610306418425034102614454010a0703283c02c0c2d0b9000c114031000c0590180640c0e880e00c403640f0000c1d5858407107401c000c031306004600002c2064691a00f0a40c401c940040a813070f4591a07940064400340406403840d030031030041d034000f00341201040000740c255034030076a202d21118034030f410414004440b5400c2001018144018480480d08042c420200026000400207000191050004214941040302070700142000d1000a2550540d40500b0188440c29424040c440e12401802c0d181075090445a80c410b20300c81c40801c03030364030598031052032500240000074000c031a0b00e0500d81818883e0702c01c50000341d40d022a0480c9002d2703402840c2c0103003030200080058592400c0001c00f482081a01604030b46e0b9504626140342c0e101c0c910010403550041c401b19912512908924090320b0540020b03802241050211191900741d6081e8911542d08170a480248045c150008100c0e40e1010800714101512601c020516070303402e002d018289100e07503c42d05c401c400c1001015040c2c6040b00c03040310074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 209316411 1250 209315161 209315167
    0x403030315034b020111030c01050c0306030d090501050f0708040909050f0f0303091507020a12050d060b0405030304050402090a03050732090c0a110a0f0515010b0d0518190c0b 77
    0x3c1c101d0028a0100c2c981d090801090881c0c081001520b1402031454a48041d82064140b00302c0c921010b0055028803019000e58041c179284000c140c60128192160f03d002035402c0186501070303207411019028007840ba144030303481c0c2a41c50b100d070003c3c0c03200d01900340d0340c540002030003401e8210200101040040c074940518250300c0d00c0701ca516200d414849880d8000103040c00001c00036823080c808801c0e030a031301800c288840c2c403030800000d109402445441c0c2c0c00d1850314030045a07888400080d01d040320300040056141900381018000031390021010583c1064401401100083c810310840001e80b00300c000c00202d12100a022507038008030030080c01010044a04a4101615038100481c0c2c8001c61008841c0c0c0c840407008201d0705a40c4100014056000e244c5d840030070443d41800b6403c3c6140100201c0d034041541e094001c0c040e01c028400d0801c00a0100482298142c40b40c000316401381403010201c003812403425420703003400311682d142c60b4503508040c00e4204008000f09100050014441e40302c3c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 209317661 1250 209316411 209316533
    0xd0b010e22020105090121090302060606180d060b0d030203210408070b06011107060203040e0106020706080a0e0c0d1103060c030601020d03050a0b061201060e15040303031503 77
    0x11008031542010f81004000111412180d0044046a1070b01b050700721003001100c20010400f00600300d21030700b10014050103001c070311f2500c0e18100703031818403900d040c46c3c14036090300508001c044011807108540041d22080c0e002c0060b076a103900e40b081d03180607070041e44e40c0c1d054001c8416061a541c2d20020400700000c03041c440410480010743d52160307405a10501c0b50f8442d003005031204040040c2190692084c0c5001103405a40440039000b160317503203185007844e80d0321114240d80300c2d50640500000641c000c4002071041c0700c0c642012400340c5600f800e65115182c4c0d100815000540340c3c00544503203902d41a80d00546c00c0800a0030ba2205654840904604083c00002d4a40c190281c004c410076461f080032031040141c40d03000d00c0301c110008141599aa100c0000101c603800240b05010104202000f01451803e05151400b040590079410f07520300740c2196400e50003024800741c10511400c0580c00070001941070040410b5840e00391480d03401d041701c0301081d151403803010401c2c152780c00d522080c608 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 209318911 1250 209317661 209317711
    0x120c07030c0b040213050108150604020c0a1b080106060305222003010b030a030c0308090a260c0708010609061a03010902460507020112050c07020d0b010e 68
    0x61405a02c20204111900d540c00020320030241e01d1500425103107007000014a40a000841d508001e0f400c0c040342100350740c1c5800700002c80c02105802070564200000c200c002980303402d0074092100450307034042c1003d07031542e6203142160041d42010010943c1c0b00e060080001c070714001c000d00c0304044032084203421403c1d03507800e2000035003450f001294100304100000755036080d000035140742c4010f000c85000542c981401010118007400940120715494003240714964089001a00650405109003d0900c106545001800381ca500103940304001d003d5010301c100705000310001008100c002040941c2050b4903001224040d0340102c401414600b2808c014180780c506403411104040790042e2562002001101c507000b41e6144412180e0303024440400004030744c100e090b051810000f102410504045040e10144030702c00010740880c04442d45506071710300540000c0d910015100b0510b0518880e907000c01c1da51842c005049a05d14194001400301350a841c0301142d001c140a0300a400c810b400301da0803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 209320161 1250 209318911 209318927
    0x120d09032d030f06030f060605010e1c0b130605180d1d100216090608060c07050613030306080d0c05010b0d0c120303090f080310050618010804050f0111120c0703 71
    0x1607424543c641c0d10082d04000d00f03a001900964004102c880406134071301e40f40000309440c0c081e05020071040940f242403828005058004c1c00440c10501500d9142c1e41c0707034124002e01c0241304810f88001c1c6540580040d0160080c14002d02c03618403080800c1e8441c0c0481030070001946100b908000c000074044101811059050043c1003060b10220866452070b0806c80c10250b10141d40c4200f204003140009401509900000c2150100401c0e0745498640c1245a5071600c02e00d100078241e03a001074085860f012103400703038a207010b200303040004c0c0c0300d55101c0000d420f144015a440d400f08482203035060500c41c0c00c2c040c440e038480b801c1700d200c544140d90b640d4800c4d50b6903040c050026110440621034007010701030391104207910b40092800d07410f2026032a0142c407580c13048030300d41a100c0910b200081c2a09156040d40d20302c200780c1c0901c148034400e0800440d5001d00080055130144034003030960002d50420321420b010001905000303503803184180c0100302514405000840aa001040b110001c01d6100941c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 209321411 1250 209320161 209320247
    0x50601020d0f05031008190309060201060302010509040b18010914010e01060212030a0e06010323010b01050301050409030507080c030301030215041206050903070c0801020c010b060702030d03020c120d0903 90
    0x40b00d41c03a44c48140d0381c090000c00304d801034903492050310003958140c2a250362105240c8d01c2503a80b4502561600001c900f600c54030311000380071640600c10089145800e41280c0d40f904d0b4060000c0c158007441031900445201c0c2a801101d01070307640c9400403078100d880c10030f990161401003e481c11952400000035525208109804029000400460450115a04030508009881d1b0840f40b96507107030700b0031560201d5a0140c0a0706c01c5901c3c080c01c10115410b0040c021030544c140c4a01d81180e2030001070001a1903042c03000ca0801100f04415400100a03002a0011030b01c60300055462303604510600000c0000c074079503000303400340500041054280c080c070161130035944468040740c641c5030300b4142491170040100050040b0307150071000c02c5070352055016081803e0170034000d103c0b000300035080c4401e44c8240d00010b90950010b01560700c195009ea0000e216458052084034040e100310030325131801c0c1c0c102c520814000340e260404d00c414503a02c850014038542c00031301198459814403650302d18000072604 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 209322661 1250 209321411 209321417
    0x714010e0d2d05012a020606010c06020f0c03040e01030614010b07030302070201140307110705120a171b0f07050405090a0f020f030f010e1c020d0c290604050601020d0f 74
    0x100400c8101c108031000c403066603021000b80710071701a958036608105800d001000d800000d1050f6100ca26200054842c06008180c4504480b0b082d10340f240b00295114554010b10400c003046621548841040104010030710888241129410b511342901030303540d401c283d42101c004880050091010890407100c1041c1c3c581001641d5000610050325851804160b0603400c031000f0003000481c0f5003100c0c19010013560b407401d8a0229840e1001c01001c50b400f5038202c0160351140702c4601c00180d850448111448008201d075090094055140c1c4c445607000560703110581040e4030252141ca4100120f001811303003100c041c0968a88208401e55030124030b01c02420170802544602e05540750b440c0a2134441030302401303540d50207181d000c80380d018190071000b240341882280800005a400a1030090340b02440394090f209952a2500841b00030070004410b40300381d00051400260201c426014034485030903c4142003140c549001000f0440300c1c01440d443c1590006e50311440300c140e200701c0e16460702c61141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 209323911 1250 209322661 209322713
    0x31213060e0d080a031a0102010e070605130f030c080c01080f0a0c09030611130b04080d0807050904060303091e0b03010512100203090105040c0b2701030207050714010e0d 75
    0x1c40050401800741001400b02000040c0408106a05810510304114901c901107801c40140004900300c2c5c0c1000159031941d04003031303010b201d01e40c0704000510103400040300600c202c641300c410324641d100c12580102d541524a01081148001c1030100d0714250000b402c5c100e099182c80500010009002862964140da607210b882c07c01502500c854009960444e40404c220244801c00341025881178608800c0007842ea100080c03190521001c4809590801000c2c042611407000203987c030420180c1000207104003880139178500d031601e101d6500194029600e1250b107a1400d150381c607041010782001854182040c1040c407001c10f900003203904450055072000304c041458119641002600603084401500000070b00007108cd054200f40d000350b009815009100795206888800c0d486804640400c0c82ca04070420b0340d141c140000c1c20089102c040c1030245c81d194080d61400e040003c5500300018180d405c101010465902007002e258485096983c1e80240980d5201c01d00c5401034480200060b1001c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 209325161 1250 209323911 209323937
    0x30b091303020f06150a0909020d390608150a0302090712090b04021f090608070507080d051815060904020105070804080c010806181f1a04030203121306 67
    0x2009001c2c4041044401c1d2500b17410102c400390301c0b400f960924107104004581000c1504511407041c0741460758020640e203608d4200b542ca405040009007080c60040e0139203030307000b00768034900340e50b01e00b8505075820804200c9041000207800c12070060000084030034210b0440c03002d915440700748010381e078049a618490b0b90300e4500c215084a690038103180c0d00c6c0d08002c00e8600308041382280c203014500c01c0305c4103611541d11240404502c001e003044240085c1c3c40e60410031034030303004a46581d000f84031854403600d058550340b1101201c0d8420100002503e030b0350000c0155011301d0000e0001142e10700400b0f400d085080109188400c0405416140308100c0680464210780c000d6040b580304550250040e40c03a65aa0a004c42e08c03109440c205a01145864000400c540b0300010305520000d042c001200c42a25400d44181e075000c3c4c0022075808000086102080c842203100c074040603010f1480d440b954032810f510500d0b0400c0d01c04107203c03c4241c0e0a0001e102d001d407a501c1d5a100791480e918000050504d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 209326411 1250 209325161 209325163
    0x80a020d080f0f09040c0311030a0504030e040207050c01030515150c070f08031207081012030c15060614030c0405010c060207020409080304020f0a030203060705090f0405090c010f030b09130302 85
    0x18a4004207032071500000c0c0011043d01200250007402421101044034000c4110244e041c0d0366200b018003124a070030000680c0b480c01c594020390b0041d00901e4401044118440854220307070005602b99001c1d4130400990b042980c0c9030203180e42c804c1a200a41c41203110074000302c0c21201e201034a000c5210008a003d4803040410000b000042c0401d001c10344245548101c01c5881391b00c80d051115050703c0510001d2000c2c1d0251203018000d00103a44203a035090326006d660602100c1c054022810041c104140c00042607044d0722940000c6c00400c0c001880e1880c0080151a60f000303450340c410b0843c001c4c0304100706808001c0907902155003e00317100c1069950341ca440b40091251100080d48640f40c00b24a6060029100241d40300c0c52099038510700807802d00c030801500145500c402541540182d001440d418441d80140c95900f8001e07015405000003200040e0545004684100d5264040c010a189640e800043d01071068881c1c2000c0003d0f904100104800c0b404c004d008200101a4214030420144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 209327661 1250 209326411 209326417
    0x503010f050919082719031401050103051e010f05090601172b050c0714010e0f10031517010218060a02070620061008010630021504090b040c09080a020d08 68
    0x5c0080590496940410708100700351054001551040349805c440031109405216071416250400b0081084000c0b042c00988004540001080075540380c034074000c0d5032a0540102809101c1c284090300441d070504140140c00e061001c1c00f880311f50b1084a03c600c00000b80840c14198102400c0b031900791808071482a2464421003c01284038440c070400022280032416000c20f03499000da03a02d1208001440c10000e150185140c40e42e1b114511248003081e040c02640180d2898440200c440b25480d5502c000d002c2804c0c81c2606540107940000c0c00d4600b52220820f4500d10306422143c0c1d078104030380580001d6856800340541014040e0b039014608a251181c070f40e2400ba181c403401111003900d05401c0c0066605c4681c82618159070812101184460b03100340c1c0c2c4002c0381c1c09030000e07028280c0f645007201c114004084003030303030404402c4865981d01c9028000500c0a0914140302060106d003240500c01221918200c09d03040007803c28040c00a18004035140e1140360b01154013078000d1250341441d070780b144 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 209328911 1250 209327661 209327737
    0x91509060702030f03130e060108070305071803050705150f07030c030512012c0c0a080c0d23010e1501080402010e120c0102150106051b070503010f05091908 69
    0xc0700d0b13401e0344609030000000030712010307407402909014207a440139604101e0030b003035405501141081c40001d04a03403003980440e034050801d2811403054110011040b440f45002d800640d07032034012000600031410b04c0a11038861124a110084c070300030301035200300514065504d004041050403100c503814144a40241c659000149003400078550b92413403000c01e10151645500c801012200e1035007120540b100c1001d00c10701200d141280f07402d60300c40701190005030003030260100750410302240c580d0003020b100d51070340c0d40c040c00c0c8146207400c011051038404060590114141c041820204110188200080c80310b0b01403c4c01c081c40151a10710050f0f80b0b001c440c03101140c0001141059429030900003500c2402d4000a03026a19501c1400034024065082401441d01058041015001d840a0340e0500821141003000745c481603a1910000707403e481e541d0303100305405a00d80741170003a07180303007031065508d0404a02c000ca6007121042d45c52230001c1c000e1b01e0444103068400840b00034101301d180e1000e0303401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 209330161 1250 209328911 209328913
    0x3081605070f0b0307030b0306150409080f0c01060f1403030d0f0209030105070504170715050306060d050f0114010c02030601170102040e09010e010615050702220504032309150906070203 82
    0x290703849050010343c5420441d00a80001c0c1064104100c1d4100810321303a0007030f983c0d6002c07007007100030303500901010744100031003103400301420003140069900c0c0034050301d601061000045810344ca08005090141d2454001a0120750540b880031901e550010884008121007071010030064a900c000c84020b0045550f41600341d4200410814010780c004c005205560344400116a024000c0310400e603035410138040c1d9076001c0300480c0300040d01d03405540913560010005102d40d1402a0100dc0b013003c0d6031007502c11020f140c141d10018048407000341807400541c00c0a10b800d100d010b806800190b030b900810721458030003401c4004540c512040a4048801070000624403030203600300106203500078001c02a08807101d5103810300118002041c02d00400501c1460399826040010316001c22244012644a05080f0000300030309000d0307400709026061244d13001c3c0d02c401405a0f038503800d0818031844407003142d2074410100281119503840380c0c0d0f10b1040d42034401509481d205400040346540c8a415000f03581 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 209331411 1250 209330161 209330189
    0x2040b0706050106080c0f181903030c0201120e1005040606170a02040b04060803030c03130f05030901021509030d0b03030f1c0b0406060c080d0b130c1403010308160507 74
    0xe001d0150029412184140c2d150f0304950341e0418210381a010300d05a0b40c0d090f100c04c2003420080c9088080200c14224024491035011100b010b02c9004100b50350b10450119000a010783c01395a00000e40c540e4212091400344203107003054903680d0701e61300711a6004c6aa55a0703800402e007844403507441140540200300c100035040314240e14442ea90142c14608034819824070b800111141014001d040031200c406000318115100c6000f260b64541004219111221040c0303c01e03004108500301c0f40324010700800103942e841c5c0d80c0000090500121000c6110405540014000c803110000212851000c0d209400510540100006070652248001407040b051000c0307078601d10403420550540099405540030400880c4060922050750005c0c070515010401c40c880180c00700f42207800406050070302840004942032400c0010700d4051940f104021901e40d9032442054080d0005250820084101c55042c00d41d859a5114043c52181c1482844104905a9401e007040740c1040b034500945514800100c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 209332661 1250 209331411 209331413
    0x3140307030209090105040902030606010c030c0206070602071103062401090b040609061b080304020d0f0f0b1905100b1e04030f0c150c06110d0e06060909071503050a02040b07 77
    0x10f9002540e030315200310110f00000889181a00c919030030325501a0180106658080064076007983c40001070302400b041e0226400140c2da00401404142c0c03180ba00141c81e44014181908800903443c8054040da002c4c0c07090041d412901e48820354101c45103612152843c01764001241e000301b08e40c3c42841300c40310114021600c91f80044004003682c2950b0f2b240e0380304101007a4a1250600b4205002e01070440800211303000d0b01b0300306030001141c0e004102c5030301c029140e5034554601e10381901c0c041c2d803400c1c005414051304516032103e01c0b891011510051000c0e0130702c2810098801c1507440382c4010031030000307030070b101140ca01c60158100e2124012070350303103440d0342e0300301290324a1015900300c600487d030440c04264000c100c80c100d9403c100540d500c00c5207551960360f00004100400c404480300303000b401407040300034440c04ac002c1901d00d6040900308504146007840144040074001d0b400e0b40e000f2040c240040c60008015002d81c840030325000c0f450b62100c50058000780300d00d800c100038000000550b00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 209333911 1250 209332661 209332667
    0x4090f060f1d0d02190c0501080601030615021e010c050306040203040303060302031c030c051c0f0b0d111002030703120c170c0a09080f07030215040b0c07080f03090105120403140307 80
    0x201e400f0a6039020795004040070120108002c0c2e000e04018001ea410f444248000d501c20905503900c0760040c1000907040c1d03200c2c003117511076030382922031400107034403a4100500e6802c8984d0009490094a8001c1c40107180340f140140c044d0000a1244d405180e0120024061621a03000003005603005400d0341e0701030400c2c081511b160a0300e0098680400c0c100b12002c105a403140003120461060240881c07410715142d0040409480c0408203661080e40702d90440300d46699001444007400d2103480810143e628003824840301d140b000814406640050101d4000b1a8000c01020440403c40310000f80c06002c2d0314064444e400900507104500c418002003101140c00710340106040b00d140d440380342c000703641c0d550b0b8a0347d162491000d041054004920400050600078010001000e408144c01c2c1800e40303608203041c2a4000e02c0e009505903101e185d0400003840d00307012107004000084082c5241052640c00178101e44107044042d103044410740001000d06d88034032104880302882c1d02c0a0380e076a003071540f001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 209335161 1250 209333911 209333923
    0x20d020a020601080c030303070c0305070f05030f04050307050a030503030708092404020f030601050a0b0c0102090d050102040509130209041202010e060403090f120b0f19020a03060306060504090f060f1d 89
    0x613100e84034080c0c000c0e03a5450000240d9100b820259031704286000c503584e00f1070b400e03000004125094110030b860b1400068051020740b540701c40302002c407601c0d18941410540390040c0307644800c2c020310241205002007080801182d0b44a07110b8144409581c5449007803d1a1680703124080e2501c1a0340e0150321008102c0c1100140140d008030f95005541c40c40c03004142c0c41d1130f020301c141544201440002c0260201e01c00c0541880500000014140b44a03100400d56101200000700c486960002e000e00091a041d80541d82003546119070100317600b80d81d8041180d07410080d00c06040c540703125107183c040501c06d400c0103100c1c611030810303580c580c10145001743c4074a50300c1c0103003444003120a00c04144100c115010a030401d422200c0e10f40e060b200d4002103000003c4c0a4907141c0360350441a65030a100605000802c91503c00b66000a061451410704004440080e000b55100758103102d03902000c54150749114407400d41002c80010050b40c4c2a0f03450005041d210000b40500151b403101625070390021601c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 209336411 1250 209335161 209335169
    0x5030309010203010320100806030106080f0a1a0123040207060903031a010f1407021504060207080105010b0319050a06091d011a01020304030311030909190606110c06030a020d020a020601 82
    0x2804800010030020500790080d4006c1d03441d08640c1c0c508241060318851281c02e9008036002e0000181140c455101031700306801b500c1101040d030721400e6007a0410401b250380c0150340340400200a1207504040c5407020160280f03a900c10419140c3c010014a503443d86c4c1261401a0b104108100040d114540600135007aa8140c05080410910505042d94041d0005c542004229a00da0035492b91840b0380107120b801c0105c00b640c1045035940d0b030b9880b0a0b0600014409014070703800800070540303031403001800d40704141c01035820824140280120070300388002e0a00c070b803842c0d4140410f0903511001840300a0500742d01802d10700341864080340551400c02d440f550313040c40000c02072200c41803d04100c41510120050a80164420003080000c00d11888140000c0b20080b41540d140c0818140012200c00c01070b94016113030369220803880302840c51445071800415060038a402d620a00180041e00c0d03544050000d401485c0000006494004950440d41c8440c2c180d0021511740680703e0000f5035a11090003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 209337661 1250 209336411 209336423
    0x60c150218130e070603050405070b120a0e0705010f0503150405180c0306060d02100c060f02031509010e0a0e011506020c13020304110f120a12170108030307031503050303090102030103 81
    0x10761010800b8150285441d100b600400600586141520440c01410020002e0b00e16019082012405540340380043c0305c10246003514003501d0610711102c030300b21000726402000642c0110010070442e42c02040c195080c042e24103245407a0b0703444441080c0403200c0d4850841d4402c1c42c040030401c40510840d12040f025080d5412201995020750615aa0385025115242d101c00034080f02401440c11807418507038040c99252170040f111090b5143c10644040740c408041d6181c0100c2080019982200e2800d01310340200c81d0b00c2c10039403424460404000f809004030040c0ca4507403101c112040001d4000d14495118120110ba0300e9640750002510741140c1c208492082c05401c4800700c10484070300030b8a000d15007000c030703031203040c841d00e0100b052a06541c0041900410701c001148241c0801340040401d0318020700001031401d1100034000c3c0204110980050441c1641006016484002080d0381d1301013150b040009140f5400a405a07220605038001001c42c44004200903540006401560481e44110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 209338911 1250 209337661 209337679
    0x3120409060b0c0a060b030a0813091103040b060f010903050a150c0c0507140f041d0d020109030518190906050a0f0b19140406090312020c0109060c150218 68
    0x2c2001c1c406200301080707910294001d00c920030200b04141e021001d440f10080440794200301d207541d111340d1500000e41581c1000003543d0b04002c2604940604004140703a01c0030705145103095035070f00c450800040c003468000c0c8085921001680d004214010146410104691181465150140d4084020044080782030300b41149000e081f802084210542c40d03125020f4441c00341040c800d4550384410301001c69011000210042541d155031055012450800203800e450440c43e0b8405494001c10074840000c580c034100d4900040f81e8402c0c10f0b00c0481c413101658001c108510400514030201e0404a1409214490000680c0142a0703008404941e420360b00c002e64103a9407503040200001c03600ca14280c4150801540408502080c5496111906402e01400201a4601030030164100e03802c14008192420020b2050120080300e01c10368011910060485c030341042c00007089014548600720a01c40d01000c072000b013058145004000040c040c0003152181003910700c7c1c01089400f1504a030141c0d01c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 209340161 1250 209338911 209338919
    0x1107110405010503030a03020c1002210c16020d08040302120303010e06030604081207020a120207180203090d050307140d140612060114030c03060a05071205070f030203150312040906 80
    0x703024090480340001c0203581401840f1000303402179446030703001000501440401850958282c80900f24801c10b03108070a207103003c803088100440300050444145e08500307000c030840d00398880031844000c039415568000310503d24034091849020f107800007035000b50407400070b40000200001640c100e5603481030080741925a1424180c40f0b03242900e02800d604010420414030246a000407600180e90788101c4143c1a1140c540c00ca030742075090742800050b00428810070140c0c040c5141c9036041c4006810442c41e5003400002c1a0303952000092480c1880f4000c000035103440d0083e80c0d00352903114000c00c0c281e50368128800d004c005084c0386010201000004021501e83d0030450030001c100b03030000d001445c041e400e1651a005000020011582c148114444150561000e220071030241c06801d0007c0356604040701c019041d2038a8070445c039446441c060401110f0390788132034203004030800c1d402c006a80e900c411a12901a044105040c0e42511480e1100e0341c2907030340c4100901c200c8401700c1e800c0201c1c60721 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 209341411 1250 209340161 209340169
    0x803041b05010e091503102f09090402130f0203161b02120a020409060b0a06050a0c0b07140304050d03150e0115021e0708010617030d0902040e01110711 67
    0x31400795500180921004a1440c20004007107a0040810081d11050b40c42400000c2d00d00390310000101d1005486840900d450303000d03c034400d0000c03000d10b074180780d00354521000c10943d4001e407401184605171403000700d41503445000d55038035130104035101404a05283e82503100a5481561a11080a800d8206510f210b01c41c9144803204814940e0a10034000150204007440f00107011100450007103110b03040050b556881812030303491103488082855000c0b14100301864400303a10010901c0000c0103d4503950313a004000f81501540700301084140d446442080f10450003207a501c1da9404800802d00c000c1c0040018090212203040e0ba05014080c019003284e44040618882c4254140314000180f003042103a803521200040d240c0f040b10152901d0201d0b40c40b00f2181e0340d4110005401c44001441101801e016207000b42281443c4000e05810032050340e5542c0c459148840034031a501d1200c030085580320b403c0f0441c501554002804440e00d01c94007982282d0001c0021258810510744d02c242e1814 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 209342661 1250 209341411 209341463
    0x10306030822050d0c050405150901061202090d0602030a060902041a030c09030106060903030e0301140a0e0c030d020d080603010c0c0b0c040e190507110d18080a080304 74
    0xa48003003101e041c4008819008002d242d51010040144001100810103880d41e0124800a034010440c0d0500b45180c039040c0406c90310050f01c40790f40e01012003200c0070300341c03584031800c0d0441c0e4283c54103075800c2503030030400c6000b030103461201544134941728ac148040c003400744c020310b001700d0007880204682c4d5aa4299803080f84202c0c450348030714121074055170f404801c0c8500596480314508080310701d000c0001000900312032054010f10041442c035603040c010705a003d40c2165100c0001da00070040c04a00102030403030401d004145040650311140803d06880b4144a840d954034409000c0b00c895101104002c0c1d10707a403036032281c0340c00503051500183c2180b505004a0702042d03829110310201d40e016403074041c01e6032002410030303e6108082100249054100c0c4805204810484483c14034020100407441034031300144c501c03020010090007010003150041103960200416040a62150060f51040440c0111990195045002d02d82019080c400b10b0001948a00c0c415481000d2113491030001c0c0500c64 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 209343911 1250 209342661 209342663
    0x619031b140d170a020304050d1b090209010507110f210f240c041505070b06010809060c0a0903050111040303030e060f01030807060b030f0f010c030c12090318030f03090501030603 79
    0x807060500082e40e0307040e0f40c001072180303a444d4410703645486d8880001c2042c031200c3e0704085034481c241703410040c00858130020500103030440c008150300c4d158600000815501602c40c010f415445074a550605c81d43d01c2085400c40560003400c610100704410303a0b0300c0d03000c00c580c50f610710f17841c01800742c0c541011801040c0301c2031030410820711f03110031804500111406000200002c03008901004082800d164001ea0140440340030b5803030b90743d220903034a0240000724014114a061224660900540c0c982c007251040d885081d582d802e9848120585045440170031650014009500c0e11b1140745090f1403000042065a01a80f0240611000040507503554403044503003581c00c450f5000140001042440101456030082ca800300c4c1c61078092000078200000d580d041001640a0010b0030040321081c001c5070050fa40e1820100610b1480389400341114212003081400307070756501d4802d410140144591092220300f240c1ca0189940ca07890400503141021409030f0102d5030380c00e400626580b003130058005807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 209345161 1250 209343911 209343923
    0x605030a0b04080d060f120219030203100906020f0a11070608160f020a0602031501030609050108191a0403080702150114060a270302040b04050603060619031b140d 72
    0x742c0d1103850303082d00341d0002d02c445042d00e42c507201c0c005440000107482d40086c2c018807200e2400320340284100f00e20300340900c903180c00c0084041410805698003080030000582d101c0008907008500b454500000d01ca980b6a03455a000046001964140c0c010b0090440114070b400311180e142c0c484909035040c080445030004020000e03180844124421900c010701c2e6051401119440c1405a40749400e98008036001d845080743d8403c440034139039140c080e001c001c0c00010400c000650500400f103448110041c10240151604c2180e0300800820b406491070580035501c0190f0b01c1c0c1400d1600809080041d80c100303006110b4602c285c20f000c140c20305110b0490760245000b0b010821304a003130007066000f8621070400d00c001d0742e60000d01c0240c80201c003025100d14001403a0b6450651041104032201010100d024514044c01c019440d10000b40c4a07070408003c4515407a18030500c400714202120581000789001d41ea03820207d08038050384040025074000d441441580304818040c0841c1ca48200343c06080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 209346411 1250 209345161 209345183
    0x6031107051e0703020a0315050a110d2a02030a08100501020a03121b020105010504240902030c071e060509012003220c0e2a030a0204050d0311010605030a 68
    0x8100280c0e80440c000c401008143d46a1684d2600020302e044415401a5481401c1054001588620740b01d0264006d01e482808c00001802c00000640c0c2e0003141250351519aa403803840c8401d0080810b51604c040e0002c1041c13602c1e000e81c440c001d4690704106403120102e034114011070803050b00405607205441c0306034010000d0340724a880880f12044000301c000700e00e6036250050102030b260b00c80d9203000321200790004182d5501d007409100440341e8030035403050040c0a40d0b160001d030030098020716007240c0024102585035140c5140c400b902384108000141844104031034812481440ca119480c01400781c0001c1200b5641c04802d10700b0303200f4001c0d0224001b05410703000c3c511080194017039508502d00c02c3c6600941340c030100d403412080540c000281c0e00d002d0b800000b0000075140f0018103602170910802d41985c011050700141c0446400402c14075021008070004944980d103a05071401080700400c510148049400c014103480c0316849000e10703950070410040f580d82070020300724a0b56680480342c03c2c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 209347661 1250 209346411 209346433
    0xf0f04150804122d02060906090703150e011103130b1005010806040c02070807060810150518011e0309260a080604090503040305030a031b050d0b01020c060c070603110705 75
    0x14a681c1d884c0b088070011074900200d003d4126001c80700304054520b9400900f10343c1021050343e450320400601d4802e465200250a000080c1140010340700d10810000c00300302c0c0c18040300c20502402d00b80c0303819081d103038001c010800300c1c03003c0c00308140c2150301031018a000c80c0c6800b0040420048603010302404240c0b070350003040241c1499484629201e03890f2042da40c030103880b4144a41040c509611500008100109214101144544281c000c210100b5012210000c862003e4094040e8002480301c5010b403c0c03c03401164050710b00c900e00c46041d4001041640ca403003d02600916500c1c9060350082540041c440ca0000400e0892480c030004035505400c0c000d04000c00c0b60034600061029401c2910340024200049081000d00003440c8928095500c0b240084c0c1e0003005c0307500b1002102004040c8450504081c1d030400c003141c0c044106060301142e01c03441302006038030304161160025000382d00042c0c1e421003104086100c1041d500030740e40038000081040c09072803480c001c02070040c00360340042e107800d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 209348911 1250 209347661 209347667
    0x406050901180e0c0a030e0109020a180908030a02270906060c0106050603010801140a060f0504020304060e0714040c020615060a120207050c010905180103170f0f0415080412 76
    0x60510040c4003410b0641d5100e004000401500356010240e0150126059440b0340e00b40c06540035089108008104440d242c0c4c00080340d401c1c0d58031402e5824070340c00c0b281e0f86071f0600a40080e49843d03040700d0b102e0b0380d9082284400000354028025010101032030000403211264a00360103800b40700003059601e02d610f8100403c0455407089035020500c3d980c42c034000030b9035210840614024a5002c0c000600341d004100c4076801008010311404006140c52014032100e40450110380a44205480c010b031603603610302e0329000030404010601941e202d11a40051500b890101c00404a402640d061000850b07000b8141e948810585815071a00c0e070480041046041c80c1000d4446c00c0490320300400745c80d50340300107007049a0250384180c420341c00c0041c000c8225600b042c218002041c044d64607a006181082461600c0d51040c00000d21100010300341048001c0d12005580b43c0100c0e0321807056403480e680301d001c2480d9100d407040c50750402d002c4010030b80b82c9000300e55061203240c000c1500070203030b0f50f01c0c0c40031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 209350161 1250 209348911 209348927
    0xe01080f070b03281505090408040902181c02030f0c03030d150509010308030f0f010311040c26040c0504060f0e0603030412080a080108030a0f0c0816120807050406050901 75
    0x1245842c801c0055034004d140c03800402c060a4400800000e6070200294102c81c0c0c20140f500724502070068003041c0030029013948119000c413010410010b0315008602290100b4004014000740e1089203400d180010008010442c1c1506108038112681e1828841c01c0a494840c02c0d02d159505130001d0200320910a0b440d00888030000068451038401a121000119800402c1c3c0007603820b00d0340801080070816103c02c40d190040840440c01c240d070340c510791b114034090001c0a0428025526542815200d0340603141001a00500288402c200c0316407146100e0920b0f42200c095804c2c264104001846052510801d410b40340580581c1001c1403c0c60303c041c0c00108080e051303942503c003c210004903c184038840b00030691088645c05d079070f0800458000c0010340180c00480d2903030005c0158021440d00139480b0642c40700d2608050003224100e0400784030b5401080045102d1403030820203d020407144505400d4001d02c2c54a60b60071030384501100300d0303660190b80140c4002c50010001c0c00040d602424036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 209351411 1250 209350161 209350171
    0x70e03070506070c0f060809010b090c0a0c0f050303011418091203040302150c0a1205010506160807050d020d0f0e0a0905060622051c02031b0d0803040c0e01080f070b03 74
    0x1a14113107a81e01c5641540c3d04907503038007800000c1c800d03c05100b41b0a0081c0603004000b0f00032541c04029040611514a192040c0032103c41400404036010f02005403031504490b103203400c02c064a40301d680d110b0140e40c0890441e00c042e8403a4029403503102c1141c061000341d038001c1c640030b0000c0c030b10b00c03a262038090080c0d400a0403c0c2c09520810050011aa10035050781381301c1c07040075000325181d00b1f481d030b4050100e420460794211018105001030019454030020b490054410040c0a58504002e0078a03000b41d124444d40a4101d0040104d410000d9400040d01c01d050401c540c3c4003050800f000758102e445c14030f07c40301280c0c00032130400c00b000000c51300d411484d00018010700c030a00e4580e94079161460340c2041da4200d840c036046030701c6c01c1006107401c0d082202c5400404540854181413a40081c2d242c030303541034650b00c422402c124030a10b1034542c8248050b140e640000985d035030f8203182c10048072680c0c8600c20095003080e0100046004070b400301d00340341c803010b521006007106800d1801c0700032540c01c0201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 209352517 1106 209351411 209351423
    0x1201080a020907020c010804200d08030f010609080a110111030a0f020d11100e0102070c08070305100e03030f070210140a0606110d0f030f0507110105070e0307050607 73
    0xe281680540c2c401c660a28150742c04055049c110007080d581c81c0c0201d9005d00702010041c80f8001140036900c80200c5204c079a03130f44c25044414600c940207214058003c601100c002488201240c1084001418104c070190b0085a10500c0c1d81c00c50310341200001c86010317400f4022a018030140140440e545030849e01d8800075a0440d0380c59032070780d2a5500d444e5031010321410031082075041d95080b1364800413124031039544002607542c5940c203001c240e8440c01214401f203204040ba20642404507558130165046507540007120100040c014080302c19805000d4103040300d81c5081c030590841c2c0040d00100c03040740c01e01c511120200c42e041e812101c01d10050030070355003441400182c400980c40051804002c15691640128094811490020042070400c03003032105d09600213986448410401d0020411a0f0711a40100e8072903452149141e01600014000d01c41810940c0040c411980114 = true := by decide +kernel

theorem cover : BRFrame.Cov 209172661 209352517 := by
  have h0 := BRFrame.cov_init 209172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 209172661 ≤ n) (h2 : n < 209352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
