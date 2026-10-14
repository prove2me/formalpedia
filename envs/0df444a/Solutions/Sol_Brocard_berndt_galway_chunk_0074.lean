-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0074
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:42:03.343825+00:00
-- url     : https://prove2.me/submissions/5aca1009-a93d-4361-b611-229a0876d4e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 13129503 ≤ n < 13309359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 13130753 1250 13129503 13129507
    0x9010f0e0307080d0903030e04090215030406060e0108070305060a0b0604030b040c09020a1709011b0f03060302030d080402030d09030c0e0601050d05010605030a11070c09021b0604080702101d060a05 87
    0x43d541250400c0400c5000f0300005000d50800c0003415880925000e591005031410000d900310398010071844c0c6500b001ca6a4010400030200c0c040201d194402802001d4042c08003041303503180c10f103090303c0c0c050612041d907062141d103012994081d607511a01400303030402860a4a424a103a48104c900e6030002c3c002c0e1110b0440000c0060440b01d1800180800c0f61195030b140c6211130f80b1000700e49074103009020400541c1c981100341d020442040f40100c2e0806440c204502a0fa0030700200320701a2003181c0000390940240360340e07811920f4200f0803117402a48202c00791b44c0d11603152041200c189800f448041c001c880941410040103921051480c1c20460615105140205401c0d000e001d9501c00c1e4003907000034038000300700501c005051258076071406001c041c0ca45400000e4a03240d50b8000035004281c00c0d140c2c0000c05090245c00351294002c01c3d490041a56254602802c00070300a4208090076405082440d4484a100c0c2c170612410482d1800203c1281103034411405200c0329402c0403681d10240242 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 13132003 1250 13130753 13130759
    0x30f01030b09101401150809101e020d06030302071d060d080702030109050606030601050a06090e07030e0708010501050112050708040f0206040512030c12030c0304030e060415121109010f0e0307 85
    0x4a80906141105444c00c010300c1c5503d403000074104504146884010403451809020b10110b0100360900e01c4d41c0c85000105403414000d6070400b034895840c201c0c0c1d2203180700040c0000d0b0040b840e0401c1d0b0841c0d000e0307003d070741503c0e5482e460752091170701c40710b500c0307c603084003c000500e00e01c0c00c500c149141d140905010313800c0114646c0401d0840d81ca40c070013074400354444002c1106030b02e420011079000d0b100c181c2e0345508082c07401202a01804060040c40d49042401c400580d817107101e603026401e00034050085a916590780d0400700d00034102030140700d0024104001181c0042e1060040f1801144960b0302d4481e99951030304d81070804d0000744800c9034804801c1100240943d40d103c40300c02440e2084028540d9140c020311103900c0d1051807101022005c209000700001240c5081c00c1e654041c0e0141862200780700c082c80000d4051140e60040700391116001c141c0480075520203441501807090a40400c00d84c01480780041071405408002030015800b0300c90002c0341c91081403861000000501160075940d2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 13133253 1250 13132003 13132033
    0x1505040606050a080a02030d0e0112090f020d0b0a050106030b0d030302070201110303180609061302011206031b03120e030c01230706020909070806010503040305030c090d140f03030f01030b09 84
    0xd0681c0101c1c4c15a02c1001c40030294502031106108440181c2000303c1c09240300c0c0006081701e011065050740c01c42ea110b0002050000c8610769500941e402881002030800c58904051225801da45071804d0034540000410101e01038401c5c008141310080c10031444655558045000e9400500100e0410828111407844804100080c500076001a01d201d51a060042d80d01c0d480c0c01360003041c041056100d02c040c0700e041c01c04600214051a02807810408084440c08818051720480d03000901d41030728045a0940321072103000b2641660b210f40d02100c0926481d8800326001d1041240269142d00035072605038803907004104404c0c41002004070900c82245d84581e10126420011041d514580c000502840e2840c048000c141c0c002c030241007511007802c1100c0000d1031800010700017018044004041000410040140c0d41d914100416038001b000b03d84c43c0400103c04062454902d9101c0da07030b030320280d0340750100a5074424841981d03400b001da861a1100741030000082d20440c9940101040490400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 13134503 1250 13133253 13133269
    0xb0c010207140303150402070206040b22060201052205060a0209010c060207080409060506130b0714060403200f1b040b030703080c0601050103050403120c0e0616060e030304150504060605 82
    0x710b111001d180c5900d01400811034841221000f00e00c51441041040e006070744201c1070f9000d540705c205907117071141c40025201c0301d0802c40340c121822084848500041a0341c2c150080f510030700103020180039071007494800500c0b18400c0b4000400c141c00c0311002601c401402d034042d03c00407005143c0305405203080e407100030480c4e000c480291441071000130140300707005490042e0780003030006594140c0f4001c01e205811400c01507134019561b0128000840d0024844410720340c0c1042c4440700103079001c0d41428503000e07108120100e031040c0082e1118500300106c2034046051640004460007600040d2000450035510007600341c080c41d4003594400e80c040090f1405c01240300035600c1921820307900c141049038246040c00c1680080d04050510080100107540080c8074005050f150101044040e0281c00a039261941400f026800010100300d007003040e940d40651844040c0074490412841d88030b0100700303449110440b40070f040c003801440c0f1001c510129502407544240a010002183c0e0344910000d450a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 13135753 1250 13134503 13134533
    0x1020613050309190504050c0708030112061e090215040f031104061d0702010b100f0507020409050607050a090f0b04120501020408100204031101021501050f03070302130204030b0f010f0b0c010207 86
    0x507514444d000c1c450f6007000d12486402040c03460b00c050070500c10b41c0c8c5d501c16600c814016900101103035907480d010805203801101c2c003941c490049000301e1003802c20000c01851680410b80c800c2d106115641d011011720741c02c036410f0340e000d01000c01c00c0c41d0460315a6061502200e80c0150480c0d40e03070300d002402201c5038604c40068610001a04c101d03003020340009007551400400c19204041d030424a160480c0c01c0b1620060624a0b420016281d100a0000a00a000c003060140580c000c00c0304010b40580d10800138021000c190700c03404440c07501c0e0810546003c0300d0340100301004400700014800d001004180f240c54500c107000151030107840d50300b07203800c10004140d021010358010401b442084581035118001440c01c0c40203206492410000001c0d00b24188a0607006036141002c01100e82c400380110307c091600036080391440f5200300e1450000307502602c001c1e290840708a010910485480400718102c651115820000c20300345544030840d5400b10740f0403045507508000d880d0000384284040c19907 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 13137003 1250 13135753 13135789
    0x20c011701140120011b0504060801060c0302030705070806060a09020c060402060f041212030c030b0d060c11070b0d050108030403050d080a0e0d0c050c010306180209030304030b0108030c01061401020613050309 92
    0x4180764460110050b20b42d0b045400c421f0100a11080c0402e0303900c8162141196928900400091810b0405a040d0f208051b40900786001d10140850171000c0064804d01a400607699480d01a80d900303158070803405990801031168000802003005031414001400c001017150074413a00d0302d60b40c0c504095001d01104c80031550220804d006600d8030f07070548141c0c180001c803070030b050081c54002c000180d01040503031030042909035600a82c0d14200e04c1b0300c00095500076207604032074070b003074039049410b105410003c200310b081c0342403000200f4040008000c2d182201d6000008041d8450808801c0e40d111600810041070582c0d51001c074410002d0400950200100e50703184c0f80032548803810b12a050003021002107052504150041000180003051648490303600360340140c40b00380300e00000e41103218030380c00a07100d4503042c000450006008002050300c0fa98800c000c0003036980ea8458841340000c08001280580c00c84000541d000d0b1140740040d503074911a209981ca041c4e207040c00a1a441c0c249000390341 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 13138253 1250 13137003 13137011
    0x50607020f03150105030d0305010303020c0d05070b0a0c060606030608060703050c0d02030109020c100e0304030813080708070914040b0610030906020a090504110405060415030905030706020901020c01170114012001 94
    0x1c01e17070031b00388900701c140009031600740178644c116100655166503510220f40039242e0055a071041c04420300c07149004d82050594195201804440141009118003060b00e4003441c0c100002022030091140c5012191040d01401c00c660320030100f5402880010805840404e0400ca6540c10b401c40e84001c50280400f4280141c507001c1e094861782c500796403010b103511180e01d840200a03d034600041a01c003160b034483c14265880e103400e80c040081040551010f40c40d48103c4c40003041043d4080780b00e0043e0303120000201b001c12420001d1b0540750341c1c1078501400ca420303018007003441e604021b603801c902c903080d500700411100d030156205d000b264400881b4500042124006220310700c0e10340100101d08030145400f42c141400c0c000007545174811480340c3c0364200603041003441050300a8208032201034001040c0d984403146410458045c0d8840102e19005000d120100300a80d80112a0030b5540c80401d030b8000c03032a030308203c1c0c0c01001c0d100e40444981842030707808092030094068035030f4600400300395002013 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 13139503 1250 13138253 13138259
    0xc03030918060609090c05040e150111010507080103150e07090e07060e03030a1808070e010303140c0c040507120908071118060405100306090308070207120b01050607020f031501 78
    0x580a0466284101c440c0c0d07040100400555500c480361406443d01c9100000701101445400c2d212840755500c0b440007403a42c83c040160000644100081545081e240c030198050010655800c1302c008441080c00315010304014030114540301c040042c592101d01001406104e4118420329140c01c680c00404c1d078580322039a64850200601101c4014440b03401e001210510000000f502ca001e2030402c48104801c80c844e000e024401075054600901b8028140c522080e10b904a00b01e40040900095003c102c1030840403091048140c11506c0201412014101c0164008100405000301410300c0341080600e400c0071410103094031035445210f2180c3c1045558281d50315007030120309003101816110300180342d41440030350103400d10303244c0c4420b00f00d03000501075a0742d4200e130040c0b445a42015000c989045448010141c1001442d40980d43d1074003111281c981c0d8041070b01c3d0202c04010000e10b0b04d11204010411801c1040c05080f007544000c00311980141c02c64082031512007000c90030b921043d0420010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 13140753 1250 13139503 13139519
    0x6030618020a0902040b0414150403080a02010b010c0809040e03090a0b040306050106020a020919060e04050303070e0a05101101020702150310090501030b0f13080d091103030c06070503070302070c030309 89
    0xc0030050001c03d20540c20f051074074141c15031900880c86413082d094400300030901a0ba8902d20f1400d45281413066540e1519120300300a00c254104101d2000550328100c040703003096015481e00103076540c1c0722602910700b07102c60092002030400c40340660054170043c880080729940301c04e8820040d280ca640600e45541c82c40c14981c0a40714181e110a003550018840c0d80c0c003603111803107400d9001c2520341444403115002010070000303109561004c283c242003d02030204000000c00114042c402c1070f034920f1448031054041000040f9548035181e07002440100a1b00e0f05401001007000c9070380350100040c00c010740b9401095440000f12400514020008100700b0040390b58200c1902400c1642801c020300d40c15640c0342c00300102c0107000860741031000360015000406103100d01e5207266200e6041c58907110074081060103483e51220849202c10305501ca07160900f00001980c01060b05200203110580701d151007a100b6510181203c4100b50f020400d5001040c184291080203610aa8071422982c1c50300080b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 13142003 1250 13140753 13140769
    0xf0801090203090604030f0c0c0e040209090c01020615041e060e010602030a02030a0302030a150e010518150d08040e0c03060f040903021005060d0209010306020a0f0c0c060e040603061802 82
    0x140e1861042c402d00008920010329140c1c42540350038051859803998030241c3e03e40c0341c81100103158132810a0081650b0300c04202943c0128429a2802d0b01511030044164640200c40c1c0200d0040c2c1c0180005820700140c003909901144010b80000303280d1607407107503048240c04144940f0207103d4885c0b00800c1012a041d803003e0041003948007079820500f100b01c000b0b440b40f0139850340e0400c064001c000b240c0d281c4819800504040800b034206511140d59500c84a1500310910540344141c58039000290302008441c68035103c0c00c0c0d015000a00100d400d41000005034204806540500040c480030508440c0745031541d018201045d515038482c9025400c1010b0703580286040d0780954107051181c0000f030340000344d1440f540c020041c046200d0b5620390120320124010a006544903642d0800003091000c141e0040c2005003150740e500500c1c030506901910701031141c5000401000e5209020040ca0b445015140e07503620008102160250340c0e600c40c002a0b9619071807498403000711032000400c40c985401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 13143253 1250 13142003 13142009
    0x6060906010801030503030403050703091e060908031c0504030c0203060a0902040b1507030806010210091a010902070203070303030507200c01020607020610090207060b0a18110403020906010c02040e07060f0801 92
    0x303400b00903907040d0340d54940c9a0101810003001e000c0c0c0856481d003050701070a0000b0241c10240b03410b800795441140c0a60501d5407030701c50140450045440441c04400100458100450300160f00c10300c0410845100010040208190304100007280b038000140c2c1c05004542c000c1d40c0505010840241c10b0040000f05d54551210500c6284207000d04420a20020252211075415082c0b440b0a81e99010043c0d0030901081d652100c0c0c14a4450340d00c04210300b544000d2103e21000c64887c81c580e8a46035001c0883c400d0502c00380d0316034810802000043e21940250783c0c4681c091a09565020711102004c046400b440c084c1c681a421207941341c003055a0410040d0350000541c0b000300024100050712009600f00f60007522441d6800251810031b004042d00a080e400b00080d264501182d0380b8a040744c85a180714002c5c002d01c81c207044440002400800036141500e40040c610030751038580d5001500e207040a40d004a070800d07280c0b4801628010140002d0000703114580300c04001c00e98000c001840004160 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 13144503 1250 13143253 13143257
    0x71106090c010e120f1906060b03070504051306030b010e09100908030115050f040803120a110a0503061306030c050111030315010f110106180b04091208060a080f0606090601 76
    0x9144a520382e84103c20074000c0e039003521070140f4013036404c94013800e141d60410142202c0c411066038514084c80b946100308030b0781c01078200b0809141c1710b6400c0740b0340d48400e48091001800a0105210741d10345507a2203400ca0752107101c0041c90b00d0381c955406c2c481e40b0003684112884101c2c2010003240003c00e200304035110303000140c1002521a45e0b0341c1c0e801240010f001e00007100003009075001c4c90600a17001c03512120543e001c929100c0e03903a4264160307250300808505540ba9000400720300c07092414080c04503400301c441d15607410000780300350842d40c3c0e800c01000c1d15840340b21001120342000c0780b48a800051401070369107282690134070002400c1419550b801300070a910030010000c00c2103034a010318038900740901c3d00001d030f80742040c4201c965010904120031603520b4210f0001d03090050000344004940c07440c200381b0880515000304012114040c1d000340505616110b03000380309100c1c0d10304551010004241d001e03003540301c01b02145043d042041240c41980b10303c05103c410310305000710a074414824 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 13145753 1250 13144503 13144513
    0x507090e0a0f150f1103010303140c03070308060f1002010603030f05040e060d02030307140106050a1203050a030e10060816050a0b0a05030406091403030f0a0203010602070311030f01020307110609 86
    0x41d40c0d2150054000800500042c0300c0c42203083c100c058035000004080c000000a0001d80195450030b11150b0080c8011400f04070020881d41d07603800c0e1030b0140c0320340000c0e010145040c40c005880658610301c000300800c0d40101d0552a10141c3d9890005001c001140c0341d00005820b0f00b90f2174050495001843c0c1c200900c5414041000321102d129140359100c0c0081d240c049000c022840420f02c0c41c01580760040480d480450002d1051805500c4041104c00c200e42c40100680e4070360751200c00b1188034001400151040141410041c000c0d085590704161a600702c503040c2800c13a0501d41160715640046c2e406402c100d00000d459200d4903000c10180c0421144040164031749060b206841c855402820140704010002405228450f44050442600b045400c903000100e0302e4920307141d500c1214200f03075110601c8081340c1d81080710700c01d0300d050b01c2040e001403c8180c1161140c4d6218100d004090f07070306110740016441a40c1086c0003441c041d0a00b903d691a0140e8000c10403802c0c020300609540e800da100b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 13147003 1250 13145753 13145773
    0xd0515030309010c0c030f1407060806130902011e030b01080c0c0303041b0305070e0708150108060f12030a0503010f060302030601120e15041506060801030b0a050903160507090e 78
    0x1c000c0782c003003640900308050115003c0c94108001000e40c0c0c406415100c1680c4000e042c0400d4141c0241c02d4503444055501c4135488034401e980440f001c2d075200b41c1101081403000c1045005a01c90340b511170050400c201441c0486100003440100039035104002901da9038186615600b26603e20740200000760b015080c2461038800c6c590702d02008001501258200c4499000c00b908402880003454002040d0740c0c7c0b2540310580c10003e071600b55000c400050b81c0f4000942191308080d0a1782030300744140d44002c0d1548a00c3c080168426120704480e80c8201c2d1264414030351142040102240c8007252110341d00c9601d8000907021201c0c05601c11800d060040040100d142e900000c4811009e000c0d120010700d400180603040d2400302d40b5015100754890300030a0106021070300c0f1a01c1c120400c019400d2016a80300c1c0b804031982e0000b0301c002481680d032400480c0500569420503035011100b00100c03400c04090319004804040365000c00e0760b06810821091003820203074043d140d0801007a400401620301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 13148253 1250 13147003 13147009
    0x4110903030d0510180506011b0b0103020907182c010305030306060708040b030f1005041a0909011401030f170a0e010e011404091406030a02010210020a0c0c08030d0515 74
    0x8603002848210701e40c0d401c000303071000b20805500c00241c01d900d40b540100f03080541700c244c0288010b54446000c03030840c03200030120070a6002041c1c8203e0b401002e60106910316400c1c015a40750280019046c02a240034058015070150300b21401840e8040842200e00411100e038410754014840c2d44044c001e0707880041c0027160300081100c4d089042610041d40d140603134103228019001d180c100c201c00310800401e21641c1c0d0095043c030f9029015840040350700305d50b10300800c811943d0220681e600041140c1d000b540344e140034626950b01242c510000326445008280c0300c4c0549038242c000302c81c03070300081d803509003400014081d0801541c01e48528074504410030f0009402c51442c540c40a040010089100c81107922420101c06444a460b860f230740c03540c2c1c81e40136803000f410484079940d29820203500001c00f0b625000076014582a01038010f04400c40b04040c10b007011350f10180c240740a000100400c0c000140009404400420010020b5901c90400b03128000a446003d40000800c2c080c061481c4081d45d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 13149503 1250 13148253 13148257
    0x51807060c080d020307030c08160c0807110d0503030106020c0307030b0c0c1501120201021902090105060d02040302060301030b07080a06030213150b03130201020d080f01030204110d09060b0411090303 88
    0x24003282406540710407145000c01c11440754241d00010380b13001005024200740c05030003004910f00c0d6600c03081c1e095070ba030510854460b02c84c03440344400149041c00a8012520110080c855580540040c80c03000390000041854120b103050100c4080d4000001001059418030030010081402c41c05080705a240d9140d07807040c107502030b1241c02d0b00000002c038900941410009280801c0c0501d050a03c0c5681d00c2080b51880b110180c02a03001d4010911000d01d2460802e414800749580101301c07e181c0d0f400c102c01c4c00425004000042101c50f420000880903a480201850085104145602041c80c015000404049014100b0418241822000d2006a40d481c0b011820f00210040000300c03094000b0903503052040545c4035000c0e44400200780440310507000750340d01907603000707800300c984407807a614048801e03610460314402c0030440580107200525141d004903902202d0a10b2071400c0c041c070280401c085a44013036049424540e5aa114075043c101802200c0140300240701c0103040c00c1d20200403e44034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 13150753 1250 13149503 13149509
    0x1302010518090702010606020705010c05031209030408062404150302061812030d0e06100b0d09080a030b030f12030f0403170403090305060c0313110109120b01030204051807 76
    0x4803401003100411041810000600448001c1400c401420011000b0f4002d0003140224030040c050064003280310350041d0954001c2a500100451425148040301c1078136000141070f03043c40303000800000880000c00c011444c060000804c09507850000720000c0070740480107401c994060345c1001d44101c0ca031211150720a045a070140c03605952205452b04c100b442c0350781041026800b25891000d661010000809030201d03100b0b03950b0400076140c09165550b5614402c60743c0c890951102c400a00215404101404003a00c08400100b00b04c0d9030b41e40d0b030820f00c0d0410038011001a503100d413403d0442c40c04000d02c3c0041d40411000d08103040503400c0c40c800d240b00c01007000b182c8224030404181050301c40d0504e4030207111206d14100c060305151800a00041c007034032040e685131080101050f070207046007040300c2c00750010804c0415a164260350b2581c006286650f80760601001500c001444940704030003142c1302d0f10070740800a00e98150b1041008851b00a04284100340c1c0000c81400d00c0c4030005001e0084d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 13152003 1250 13150753 13150757
    0x603080306040b060d0c0201051906050306041401020409060803090a0906060512091002040816050306010b070204050a0618090212030f03010b1b010216030e010e03030307050c0102090301090c030201090905130201 93
    0x1803d021100401d030b403407080101844100d46001c0480c03d40315410b500090141c6620200b0000b505040203103d01600d0b16800341940c10b0300980040350001d050f0b48140b505001e84040090304169644580004548442d42b000c0300c40c0d00001214251031421582075006000041c0e010055141480001001070240e000d810034800e100b4004200d0303070b050070402c2c604214078480d0155941e0b51201e03003880d1600350f04211a00d203070100301408a000c1c90040381c2036042c0d03001040402c1c1000d00c1c40c2c0030800a00000381c0800011a40c5a00118004582130200c8038458246040820034003014030511190600a9010703014640080c0104042c40d81140200d034111585084d0540c1c4540e500c28400c5009071010021220541c80014600002130f0803007000320145009440b0b10001e54002c000540e05034800c681c1d40380d030542080000403000c03400303030000e001103c90b03040006081501141c082421030f5020201680c3d01e0103003000801c11580c2c01407074040074000b002d1083c8020308044400c50034007501d0b82d01c000c0c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 13153253 1250 13152003 13152011
    0x20702030304170102091906080f06060d0c0203030613020301050a05060f0f040e0402090106050c0604060e070e041a070224040822030c05010e010801051221130603060308030604 78
    0x1055540030410740e800360043c1da00100c0341c100d903441c0441c000e510400c2c065015850111004400d08042e01450040b1151a29404029629a103810040c41401000d07554042c100f440200f20a41041c807407186141c0d810f8000350356a007440d41c01c00102c0b440c5650b0005000d4010070041c0080c0d10f0703c001c401d040300c40584029807507030350620f204082030003140024050040c01250000742c0c141500d032110700070380c001d856042042e40c0f1a0812a035a00c1203403102c801940c05071003c14006079469001074802c032002c4040d0b94107503840743d640c00c2c10450180d0b0149c03034105566401c900f07120014114250452100d000500842020010584111648a240c19882d00400c8009014040d0000840d55100040900c0c0c00c464103800da194210f01205000681c0c1c0e50078000b201041c0303540541c50300c06038900c0584808100768a030004109240080d009640c1c024003d4001c0c4074801c4201c642a41c04004070200701c1074440a205180400101d1164080d404260900008001080d05481244d0b001041907401003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 13154503 1250 13153253 13153267
    0x70e041a0f09040f17091e06160809060406030f05010905060102060723030412020d02070506040306090c03080a050417030301060f0e030c03030d09150e070506031503030a031b08010609060302 84
    0x7003404600107601501030311107031000703000c60000700004240303141049445200c401c030030341d4805110101030603555070800c2c0104508270402403a9455550004c1c030540340c0625200d0f0803008140950400c0e840140481d44a85c000744891081c1c3c0900c2e4098400b46008100314a40f540000b9500c03c00901104140a03d074030000c0c0340c07034030a4034540caa100700355031007156242001d19040318070524040086006014a0700e00300c090764404a150701c101c90006080c6c506040c1540c551500500c0e1b0090300301c40c164001a0000005185100078000402c225154952101c1c600901d00c503038a40c02c00c0080445030001c00c01403110980102c001c51390070301d09141a03070702d038013107400440d01d40015004003690503c40452403040c2c080c02030300a030228034814424540120381d441180026640d040744c1c009620741010b503081c001824000c0285a01c00c41e01d9220100d1031a810004c2801d5a000c1c13003003840041e8031544620304448106503066100391103480c0c406000c1d0314002006140ca8402d01411040540028801d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 13155753 1250 13154503 13154513
    0xc17070c12090501021005090601060e040603020d0602130605030c0d05060409151d0106080a030507020319060c08091911010c080c0c04150803030a020304031106070e041a0f0904 78
    0x103441548100d208000e214001000703040710000384102c0c0e0040c801c032090f5507140e403001c0c05128058011035008000b00d908041050311460301e0300f14440d40181c4d440340008050b940f00e0409071140da00038000181c2e16154140c07440d00398855500702900303000b001c006002101c21000304803202c030b1441440004484c2c4641001034060304200781d015100202c0e0030342d0072124110360b52181d074264440c021160420264089a00e09980103841101d6813a0070070168880485d000e02c004190692008003500c0340201c0340304d00b078864011925819074000d07980d40f41c07801034540c00481c140c1c1c10a4131600200000c810a4842d103011001a000003003420140c56100041640030380b0221030703280d0b030168115458105a8030503650b035418124509104030300300303102050b44020100410081c0c031003040103145556107030205480a54400341c400c40c10071180a040ea03404d000b042c80f00c07a009035003656a80c8009007000782000240c1720880441c1c0341a1582d08441d07021583c0d400404028801c040d2041280765941d4140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 13157003 1250 13155753 13155767
    0x31b060209030a060c02060603010606140310080a0f020f010503040b0402040b06160305120f04030504090c140a0203130b03013005160303110a080301050103150306060602030406090503010c1707 85
    0x781034041c400e0321034640c200300d610740003541003001517801c903400c5513282c508040c240c0b00305101e031402140104017282c0b042c425800065610081c85006030722007559030109140f82ca06d9085044d41c1c4c51703021040720300840c03030107200340e00400409103041811402c040d21a00c0035580080c10091040b40c0e80c0e030160603e9101e540035581050700160340710710400710505014085a1000b00d40003c4c861141000920003100717040c0309170007942c0654806007400e042548440007041d07684070f440c050200c1001d914401c1c8040200030300380d119191b4042d549800244401101002141d040020244000d01c01481000726012a0090001105c0300c2841d0414041320b103005004071a8001038040c1c003d03132000d14014001c003d4514204d9110fa925a0a1090802c4003541c6616900b90b00a000d0b1400704010840c540c466001000c0b0190347c910f5294031566203640d07402c02c40341d5036070090340560000301d020448907030009480300c000d01050f4000d1200d84403008000300b49103829460703600918220400f0981c098465a030f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 13158253 1250 13157003 13157017
    0x20106030204020a110c0a06020a030813020a030f030806040c021209010e0405010801020403051203040b060d02061216020c0114040302040207081308030909180d080604140a0603020a050607031b0602 87
    0x100840d50350030070500082454141a000c125a4171070640861b81b00e00f010320301f400c1211150760240003c900660f40403140b8400141050180100c5041c441b405039403001003940085101d03e110000311191450060400c9030002d0046209910740709000c001c20784c000c25442007041b030b030b10700b01540e0340c03401c50044c1d0300500e0b000422a0420704e40000840e150905600500036203001c1d50803660409c100700f0501c0c115200031100104101205c0c00440e0846c00e082910301c0e40c692004054605151043d4500f18021600f211190000030300b20b522000c5064040c004100302d01ca083c60f12400440c0a4a01180700e0700c07841c80000d005030340c0068440e05010b950400c1d500b02d4102000001902f540d1005c030b4541e00d801c1001c22a100303a05800120f003141030201b41003030b0032100100140204102c8000251040040101810741040d00c481c810324400401c401d416204200c00c4a00152a07811340c01031103c10303007a981000380620820480e40c40829009507072800750f441240301045c142019450500c01a0049030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 13159503 1250 13158253 13158259
    0x90f151b03040812060a0f0509060103110a0c020f0d03140d0e0f030301030501061409180c03070303020f07060f0206011401030f0203070f14160204020706020412050a0507060806150a0201060302 85
    0x100600c801c100c10580200307500e05044500030f0f0315417281010041400c030343c0d1040d510000040241005a401c084d1149684078005050015107414142810040350344030b45500c0d1300203054040c07440f00710711b40800804070f07984040c0c903401107500b01a0380c05804e1080d207401803e03400c10049800c40407100f45411062051140205540200c01c0507400b66680390070a002c101d4555092500106070b40401108040850000400107030702038403900c18018a5060115000825015002c0200f00948082207800020351190740208500200020f00500300341e900c2d0802405c00000343c00003400035a000072100d054507a9490440d001030354800040c1c1c000c1107401403803400e6038001300c208652030b50000d0200001c206562a41030307803207004d603000007141c0c0f1607c0b6080c1540960b1801070300c09800c040e40038058292107404014905a21102c282c0000c80c030450003143c40b6404446a20204101400341d440100b03145d040c04141d82c100040018840040c01600407402400401c144035a2381c400d4211500841e006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 13160753 1250 13159503 13159507
    0x705190302032d0f01060503070c15060504021801030506100906110f01060902030601031d1c0e03030d06170a020f060306040f060f051813020402090619020102070308090f151b 77
    0x343c003041c401102112a92521507020000140300c90290341140e110310341680c0c4140740d460325544c2c0c040131401c01c0b031204400e0f140d440801003456110340c070040104d07070100a802c1004e4060f080006003510b07030082001d8000c00c501c10b200003d0301d81201010040d20300c1400c06000c0f004a0801030361a1400058500d81c543d0300b400000202103c0710740c0158000c88081ea400e0003032159544803c1c00300464500b076a01c1542c803446121000103440c0220b0300b640700032460101200204100001c1c40c50f000760026601203540d808007000711043d80381881a450044c0006000c041d15150001600c440ca010705160161400100140950fa507540c800c012034049040d00b00001c5031186402e1420300304038050035000d81112100d84040040780f00000703120741268a6510703046180c641c00d100283d048826120f41000c0144900000315a06940d0344034401c020ba070006031500510b040040c0880310180c1140e500d90804031000c00041004130f40102e901813407192044d2151100740031280000102c4007903560039000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 13162003 1250 13160753 13160821
    0x506010c1a04030314040201120c050405030304080c213304051c0507081c0204080d030c17040503181201090b0108010515030304060c030c0209010311030105070519030203 75
    0x1004441c00d0040c1c2c000d90703040104032541000301010820656029010900403659864000c5864110411b03840f454034003c0d08007550ba07800f0900d1074005422004c0160003c400950b640c2c05c001c3c0c580030601280c2d175102c50054003100c42843e02ca07404a0803040c4c00c10001d02401c00c41400b114203100e03034842100306000c101d20b05410074139151600d42c6c890740d9072a038080745901040d91140d000d44108642005003541740c11030035500e0762800700111020181c8117400380000116920244403415900c90552130200d88018201c00050420700e00b644902c418028440a11012074400010741c3c07047c440c0c4d484107a600034510b034006214400043e28001e043c4d0700341081a4100314045000301c3c12a1031000003804141c80300b881e16495034480c002d1150b09584140720400c41a803007a014441698041e0400350700000d0f00e60040f490a036026001524a0b501e101601d85c032500b024401e1300c6d032090051410720b00344442501400c00d190030300d9000308101a000300101d2440d007801d0002c28620710f6410381e116080c000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 13163253 1250 13162003 13162043
    0x3050c070e01090c080a020a090e060307050a03030503180304060509040b010908012c0606010e0603130812160306030302060114131a030601080705010207030f03020c03010f0f0609021303060506010c 87
    0xc6584d5820000482d0403011800c0c1c03550078020744250b0704c0c10740c1300c2c03201c2141800000709018400908242d4544036034075000078140c841800080140d4000d07a2039035078034508055803422013500312010101070b90003004104411640300041d2001c1030700c00c4074007161035512040100e41554503030b0032004245d464a19224007103185001e452402030780700c2d000c440001c40451400c5490314030032074000b40410a10081d2800c603180500081d80d000a038424107460002aa80341c180c91900581e009411048904080c008816582e01c4580140503c5190500c03035141980e500035140c200c18490800190340e229001c0742140e807045440424550081020044041e00b1103540c040c0d032000f406944d01070700907000086200280811104140c070010b03001400c0040c5190380c2c0c0d6040800b400c005404500079458904000d5400380951540da01c0d80e040085102c58240346103c04a0390310368880105144100240d40090b402041c550040b00e4003d080056a035440c840141c03061000308800501d2554108a040c000700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 13164503 1250 13163253 13163261
    0x11040219050a17100306050402030a05070e0f010503010915021b030d050403080f04110d2a0302030607020f060415110406030501080601090c0c121404270908040303050c070e0109 78
    0x8003041d502e1592401d2860700b0281204410348400028504d01d88050001c101d90390043c5420034800b80440e2014000e68840380d0400e115074010504d03200101e014030020003a030b0b07511a0f0140c041140200a0703000c490b51051b400454202904181540115144150842d0052034100722240740c2c003034039581c0404040c00801004104d80450100b10030b000458680f00700400a94403940d802085414002c544804004030b550581d14122501a00b290300d040d44a41c1c407480f018034003880004030214250840c410141031000051900e811035114014105000788005066900103410001c022884110449034034042d2035980c0e07524001c4540024006181541030380681d040380d2100042d94800d03600c509210090358031185242d80020071074140a0082800034900d01407800791b40c1401c0020110744006081180c0003580b180501c00c88104040f0380b00450b4842e1100500d44050003000200d006070394508440c00b8038000941000b40104251040035402c225030000791121600079415580c0d1031050001030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 13165753 1250 13164503 13164517
    0x60312040b0309010f15090209060f0705060a0e0606010f080c070506010608070f0e010807030e0c12100b0a0602060c0c010204082b02011e09050304030204020a0503010602060c04121104021905 84
    0x958640300c1440c0480000e403250000c20390504506c51200d52803c08814043c0d0042803e07140e0090081002c022910081002819424410f81c0a44240c0c90404c00718401c640360100200c055030440c6080003135503030740104100c000040f182050f01e41c030740300c80d4107005442c05901c2c80100315200d408000700b01d40b9001030b95a8420030302e0748d4913515070f000480c80884080c021880818045035520000c118454000d410660a40b000305c6c04448842a01100080b10a40703080c115815540103002842800f1a6174014003010700c006843c803d419918000c0700070354843c0014410400d2403008038911070500c6c0c0a4040710000c04164084820302a1040e24000350511844012880c114440700720f248401c0c010300030304100c0511030300c54101031504484a2000b074450018201c5082c00100004070040e070b10b62000d000641055525991203604040700079141040c042c0040c102d10005202c1000901030305448007003010b921442040c408054640440d019009120072240d000e000350f10a00f051540c010058209 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 13167003 1250 13165753 13165771
    0x901060f0315170601080a0503040b070302030d11030105040b0405010e0609101205100501061701060e01050c06010f05030705010804200a0503100e010b010504030f020f0303120406050708070302030f040b060312040b03 95
    0x1d01d986c1d51000551300c000c02c0600401540060100700b014950200142c5000e500a0054074500a00c1c0000b0600b1100010071103a8010300110050045003400d00c6008400310050b202004654185801c00707680d107400414951003000034100103000403030306406800080050780801e02515030a031410980780c41c2c0084140400300e1406000140f414425004c50816000c011026489039007042011144c1459201e40710741401b208012658107103408001c107900030030300802d903d41118244800c2504000440d4010340c100103000301448007040011010340790780880000c0080b40b99046402060b41022990302c02036043c012520306450400054200d2442ca1000308020081e0f00d142500646503401b4a000c054405500382c4d20702c078014180084030441d0045d000301201c5c2080c1c1e07101d24100c3c40500880d4205c42441e100c00030b01c1045a00500103a4115469040c2582145825210049602001440980080074440100e4507030f860a101008100c0b00400440d42d07219107410381c100d41d90b4020385201c51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 13168253 1250 13167003 13167013
    0x40e10020d050c030f041b0807090603021302030f07030504020f06040806060103051803070305070507051906111908131703090f0307060903030f21050108010b0d020901060f031517 79
    0x2403400c1d400d004c0381d105040310054450161926110040c800300246203144c0701c40d5a104020401c08410002d0b0710080c4800c030ba000c20320030300f9031041c00040b0071040021402c4500520a000c240d012000d2000d9000140d0300e00080c5a5503103000140100240ca05015081000001c0210715a140031030481d01c20542a202449079841e150b000d4080c1c091500d1003104160004e10040000912070740052013454055030848551540b244005154040046210a040014847c04102c020b03040b1100340c1c1c85900b5100900f01d00006501c00c0d0807040651b0800810403000090705124100204034010007419030300480404038400d0010340c81c3c1d0b03a880701829920421518072544010310307000070742c2019100a03960700c210303c45c80c540d0f056940ca1100c40348030007070002044c00040200c0c40f81007074500c5480030001c04a141e5140814032030841e425283e200b80504140f0f95601c1c0961601921141100c0d0149002200420320010803401421110380640741103603a8200015442a000100800902c440050300c5c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 13169503 1250 13168253 13168261
    0x905010e0105040e0a020a0b070311150417090102070306020a030e01090c0f0503010b060a03270b0a05130314030c07020a0806011403030304030c1106070204150602070602120414040e10020d05 84
    0x75601c1c2d045c090001e600c08070510003440381001ea040a4107603035100741405c0703002e02125442207041100750005021451040c900704002e112406416480111440b24244c0c68001004d00013900e0354002c0c08040d124580008600140e81d11a902200c020740e82d01d03000b00410320961400c108004142d206040000105e00004030742894107121341c000e1040b0051855141c00d102d584148c002d0551441c51503003a030060101480b21300202490b50342c01c5403003001001e015140100e000e40468501400006400740750042000c0069080400d44485041589070b1548941d1190402c0c6680e00c52180001d40203072005000243d15080001c2c4a4140d40780081c11f1049244008241039407800b04481c080c001a5006c10040c2c007061502c80c41c6850b0b21405401c4070b107001030540200e0140d40c00b640032002d850661107020003c0d2681404090041c082d10300c064100d120205074024954001d90185000006c1440030b4060240e880358000b010304c08071a002e441001c400c01400350029004030050303000c950b007824001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 13170753 1250 13169503 13169531
    0x160807051c0e0604150b091504090807050a0203010f05070c020409080d060303021b03031e0309030906070b0702010506010e280f0b070309120206070b04030c0206030a0605240307180905010e010504 86
    0x212503e00700036200b151f9039510707481c58a001424020015400176a00d02903400841c58900c0144071140c0a40b0040c0b00d5204903106250131241c0b540d0282c07501c0d030306e48410b110b04103512000900c2010f80440340403548452a0030710070402e00c41c6a150b8001c15150040000806801142503c80300000c00e20b4008991541014183c5030711524040d02034100c1610410b0904001d49005150021980811a4244407600d40410100d9000000c165001004a0704028210394240166a0b1000c401e103080406050741b00049003081d821161140e40301401400302481c5040d0030200140101140104007005036941c4000d4a916400758409500156080e41c0104503500904403216070150301903c860f01d0007105460300745040c04054811002c000c0c10386040b10150396006c000c0e5006801e641d00c0005c102c0d20704000c00100c01c03540385244001141c841e9510145a07505002d40303612100034101300e40311850310b01503000c809040360840b501c030900e440000308040150f182d05030b0680300103540c20800400c2040755 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 13172003 1250 13170753 13170761
    0x20f010e12070f03110d080405010b010201060b0a030b040b060304060c0f020106060516030215090601050f040b0307030b10080102030106031d0a020f040c050913090308160807051c0e060415 83
    0x812441000100815400500b081d0f1000d2a502d0091801c25034075090a03540c58204016244c8440c009004c0e9014841440001e201d6424111424002000000d2a040400302d0900a0100d210103150703071003031500f0903038031550070801d2901c100400e81a66842e040c50820018401d1404003030002d080400a41000c5005202c2c290903141e0035100d00e418259030800381000c00401d0f042c100e045004d00c01818104220640801e800740808002a00c100e604000c24050140f003120041403103141040c20706c1341d42e502d0224111054a40005040002d0340e1008040510624540e000211641c4000b00004460354507600203218034503c45451042405801c1e1059135442a200000c3e40c01141f801601c1e603140b805034000307003120f036481c100a81040203000c0045c000407501e01404c0106c03511039412104142c0d0090384164414a0150a18122403003003000a04419004000c0c101f0310000040d80b204040085179500d441c0c013030b400c1c000e020340440201c613240c940100b40c0302100c0b84c02021410318400074160013 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 13173253 1250 13172003 13172023
    0xe0403050f0a1b061b0c0b010e09010b030d0807020c0f06121f06020c030d030603080307050304050a06021602010210061d04020f04050c120604020301030201050d020d0e060106020f010e 81
    0x2650a090001c000c149600a500441540c818440141241c0110600703040c24a40080d00980e000201001380001e83c2142c41c00c134072248010421150001c1c00042c1aa141e118152556250780082c99510090310500525241e840e07a40d041c840c218001e008190700c00c011a100340110b5082d50303144900b030818030046003080320517540d0200091290b0002c40341c0310380c8216840211f40c0070044070f00c02e500e0000750202c2c0e1150054401600908600005818200404000140741c0d18003080031500d9501c0d05501404050103810030000c0001c02310f07051080c100506040a50002421544e8480990030401c0c6c056107040c00b203025014150f082141d0024a1182d8030848980e40041a401007121325441c1c04850001d204a07404841031411101d0760319075200d50f42c890b05030715801e0341d81c640700030790300740320824005080c3c9115500402c0148010b0740d0110640b41030851344000941c40d00e41041170600a4444180b4204035071183c4400046c02c0382e400030382c0440064400b802003221b101c00032092610b41c1e0741d0788 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 13174503 1250 13173253 13173257
    0x1305150708040303020a020a081306021203010501090302060304030905130f140403020613030c06051503060a02040503031206061603020714040605030d0e01090b030a02040501110d02060105090606040302031509070e0403 96
    0x1000042c042030294004010500e528070503200c400609680301e10301d0f5000560001d0f9501d582103024400b15404100303c0d40302c0010250128290341c90300e0b000914050342ca0100034018000407000c502010f01034031702040501320041c0010089945c40642500400303030224010b0145080600341c010292081000310702868159004d819107584240402c0d4200c00341600890810042c420901e0210304c0c54400c00d40150848004070410a075004101450103801800c0b842c03003640304201c02c10043d0b40000442e000404102c4880050340e58000001e041c0703018a4200950b00342c000748145081550201d05c110507262100100d1113800a618144421580e49005480c0c1560005d001d40c841c450081c4c5440070f10742ca052502020640d120106030303076503800642e40b01041980101c1c1c280100d42e0800440003102d81c100e0000e0a0300c500d0300c10001e6545006110702e42c011012036001c03640301d49071a03049030041d503009000c0780c030340c2d00f4440d0a04c0942c0350105d929141d070340281d200c003040b01e100e00c91800c3d00441d055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 13175753 1250 13174503 13174517
    0x301092307120c0c061806060f060207030b101502060a050a0207020a030803060409020a060215061203120603070503030c1011070807080c03041211040c020609030403030e0f040513051507 82
    0x42649030003c045503490f030b200380914010441c000407546e01030001048010191030014070614541003040d121a5003000740c8440940d481407200540c002011b400703c86d08062380d075480e510b07000b102e0301c0300c40d00640164840e495451000d18020740c0005403540508081c610070007803540c07624003600490142510007503000b410b48104101045000002d103411000003000050020920350000b65001a0795124001507005001c0c2d1081b01c1412062607a80700500f42d4100b80700a08000d90305441e4403c1c19030780000300c016140859183c0d01c0800600c0d01502018040782c1c1e030703a00b840c1e54456480c1000c00104000314106101302018509660588084e150b005c6456402c00c0c1c065a205003180d080720b403d400803031100303100000351090b80e8940c190ba13507406059210701740c101381c100740410780320749142c8030301035601c684248416660004100c804681d01480d1041d04410610000307449030011001aa41c454140f009104010382e004c024406200d00c1101120710756581e4544070b400101d001c4448038041250 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 13177003 1250 13175753 13175777
    0x6020c03030a0c02030709050118050106081e10030506071106010902040605030103020108190501090207050c010207050108061003020705070f050a1a09090a020712020c040e0a0506041202070801020301092307 91
    0xf0308103807a0030b82e00c01001d980d140d90b00c4889100031520242c0c0b017040741c91007518219811088074410035002d0411494000e00301d20341140c0401c1448008107001c4c41d482c2c1e206000460100d811019103000d15030200030381b0740e0360400420041807280718250000c82c500680700005121034283c401c8404440923925036904607031940d001920620700041200c212074641d51165641c4681a100315406003001490060f20b4451701d081c030f2071408810300a0b090540d800418240010b0380c12207e80c95101340107c3e82000c250b0410417045001c7e00542c08004d0540c032400d07002040804020b2100b41c1500c0d010341d500c10719943d40d00754855541d031103132500f450707a100c0801c0071440500300503030500d03407099032680e01604d460301560760805100388071049140113810030500c07034007189854060340100e43d400d4002040c002c6200d4607580c0c0c80b00c2c00a04001d00441c094000003006500030701c00b0900900094000315101d6a68192041c054010a0b841007105004c05501d4904090b4040b04c55005821542da03010748900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 13178253 1250 13177003 13177007
    0x90b0604150305072702190e0603190c03020913050403140a0909020901050702030a030e010e0406030804090b03070509010311010f050a0c110a1e030c080106030302120a0924080106020c03030a 84
    0x4600c42c080c283c00b10205c0709040703a100b002e00060080d0b96008020001052804d80f0091800a06480d42d40c8641420002e00200215106251a140744460b0b400030b4003140400c410f90080c810b2006a40d000300040080804021440e03000a119074003944600c0340d0100002c0845c0850310681107814042049003c007405004801d0b0301400c0c104006061083c502000e0b5000645000300c048000c40c0040d00903030b0010841c1d6402100c01070712441c252000c1c0060350031507450100d14041d90052161580c0c1d01c2130340c00320030390341003140700c00802001c1e0500c4090750310fa052051860b0300b510001804038050102c41d407aa64460011200251003941d60350101942c56502c807490800f40344410759129041c0344002c80c08105503004100c0b2040d5011205040511714504016604066808040164549002080400d402241203005080032181c060f5440f11360074001c0d40d180e070907504100a008401c40e124000100b00d11030524807800e2503250302c010760780d84980481c0e4510f10941d0881e0990400c1c0324010045d8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 13179503 1250 13178253 13178279
    0x1020f0304031d040501180c020316081305090f070e010503010e0601110a05010e010c0201060b070203060403080a0207060609020a020c040b01140d06170c150313020f01020f01090b060415030507 85
    0x41d8014011507405110000044c140d81c1d080e00110700304510741c500d030b00b000711003072082c280e144055001031420486140c001d101c6806408001401c40c0b5000a1000c200d002c29440307600141000810071911030803c0c1c681003074012022600200410b18000d44080103600031700650b1704840445030072020b03540c1c41000444070380c10000b120f44400d200340c15526001a5080c0a01518400084000981c00c000e900d03009080d200281d104841d804820010b590250714040350160340190141407495440c1c0310801103200030b128556000d002c1c1c501d080700100e1080580c0e0014403020300c456003210301c0c03500b640341000211012940400d010500a403861248002d841000d007151100140000032941e9a0b0039407040010084c485452607074011105400d03081c40c5c00b401100c4d15014401100c0d0440c600b8500a4015641d0300c00c01078840c0c10b0b042c600030303042e80c800c002c188548400c0070024400400d82e46080141e85005542d0307603110b2402d0011404420185c800b8000072242c0040c0100926442c200c9000216 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 13180753 1250 13179503 13179527
    0x4030c030201030c021509010516030603050709180b0103060207020f04140a0b030a020a03050309040c0206090706121b0305040501050a021c09020d050d0207060905090402010203091009090e060405010b010201020f030403 96
    0x1750040076018490725809810242c41000804008103542c42c200c140070024205c00f4840a00307052404005001040e0001a40307001e6441107200043c1d100074220740c940f020030b003a1034000c00c80c602c420000b07c01c0200340d4000c4c1000c01c1c13007540c880300070040c400b0400007035171841031501d0b440c440328a0000d00964080c4d04850940d04002d000da0300c5031801500440c4c14480b242d08185e450380d2000480000a043c08d02c69941e010a140c03000d002541084450103403101000e218540401500c2650088960455401140e28071030820a00710a0041004064058401101c059615501e040300266001559008452180c0280001441d0542c140c0d400303030f0000c205007001070384c102c80d92040200002e84104880390003200c45800824290b0319008004088204c290000c07802100c50105000040c0d800001b940c000c001c0441c0c01260144c40344204649400003640407003181c1e4104804215240404035806000b940250300902c10b88445800581c240e00c508960319091020420004010a124005030400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 13182003 1250 13180753 13180757
    0x50703020c0a0b01030b070302070f08091306090905070b0408070303050f09060408030c0105090a0f020603041103030f0403020a0b0f1b07050d140d020c010f120209040f0203090d030204030c030201030c 88
    0x5064080c07801c80e141405048084801c402c0c220018018040044500d035030040a500e07081d4a003d000f42d82e90200391003100c200528402000c070381a02550358600415100c1800d10f0010401d07250f40702001005080751010a80e000e02903040003145440c0400c04450590328090002c240407403941d60210ba580e44540d41403d815801480307a242c01d5900c41d001000286082c900540d150048542100e0071500c1c0500f01c111150b210400402c00140000c2003201c0035501259283e0b1295140d081005140e0000d400040d41400f0000f01410411400805003051b00c0c001e175280d0035081e465601d02a4a84148001380094205c28050031200f02843c1451026030b0120300f041d04e259582c0c92011501108040310103e612070b546d0809003828140800c4851008050b82c030044c8041140d0000281101e004071600d80c0070090000c0c04264007000540444040c0c003c00761081043e4480359102500940054030300b01443c1c0900d81541603030600c00d0080c1d03001d90b5004039050350240d1450380103400401c080b60050781 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 13183253 1250 13182003 13182007
    0x3110406030c051309020a0806010302130b030d050f09040e0d03060f08100c05070827220e0a050a060207030905060304080d0b0414040507030b0115080a090201200c0f100804030305070302 82
    0x5c01a2a6120014010b1546800800d843e50440c8100300030405904444010107151401001d51a900010b203c4000c04250400030303035030310541d5400e9620b841004602d940145c10000303042d400310700000f80c150b00f4820740da408101c0d01b606c3d42025002040503124114180c1e0101e502000401c107590321500000005050942c5000502c3e82e130007007103800c91201200000081210503018500b64003411204400465040845c1c4003a0103052440c02d0528440300741c0640e0f10000b0b5040d52074100010010660000c04507142d1100e14500b000281d442480704400064400800107034600b02042a640a41e6002012a00700141c07201d05500070302540e00d10350b50141d10750340a040001d80c5114280d00503401900602012070550038494144081a4414031340700b581d0300028100c49a00005c1c66030020302c01e42e00030505c0d0006000480e41d00c5900440f03c1e9041301c400c040705507402c0000800101d41c2101380c0d9900002c0c011001004920888800800042140e40d000a000a0302c60390150742e0140303c07820018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 13184503 1250 13183253 13183271
    0xe060c070e0106090501020115080a140f0102040b0711040501060c0303051506030103030c020f1c02040e0106030803070f0206070903170903210703140414150904140103110406030c0513 81
    0x41030966003070388030343c000c214940000e00640d43d082c02402110505011103004807460800c403d42d0f5003a500001a002d10030703980c000400200d0901c1000d030303025582030080d0748403a00d0300b410740210f44c06400221055450000c41c42c003203090501859049805541381e031100f040403503e058014010080030203050000c1052200300954802c0301035800b860080d034030151400b1052060002031440c080d4483e02c1914820381d942c203035060303110300010304035070503500858030010300e40b40a405440d494100030551000882080489644a980c8060703030036450f401c50f0f138a51034042003503032003044074080a015100031000103000c0907161801843c04001c06401c43e05c034811100b111624807000038145032400710b80000c03800141503018601000c802c0b007081c1000c6c5858903101c0440e664172210300c005070141600044481e000041300c01641c0e080c071030190060040c51200600345443c842d007400211468030046030380c5481d50034244503803c03e681d4001a000c0800382000104008003810080c103101c1d20f03480341628 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 13185753 1250 13184503 13184519
    0x9060609071d030a0b010303030f050903090402070201030e010204171005040f02060a0e1003051611100903050f0408010203061203070c05190f0b19020a080703080408090306040f02030f010b010e060c07 88
    0x1a03091303d0148410031900d5045180c0182502d02d03042c40304010a0030310040c040c0340f40c00801242d461712800ca5006030f54286902c01a806059030040300380c5154408a000141c860303617055000c0c1d900c030242050b580141013050031441112402e41d8050080b0005048040050400e2002010760040b2402d100b000b00200a000440c0b00085d41c180000094840301441382010300b00003103151014281c2880091801c0100100b562600740c070040100c40ca403108504000d040c0540100c440c0100301c405140c0c0d0356900e401d0040d007c0d5000b07980e000c0c0038040f0840d40e000c824601100383c030082640301c0440d07c1010f1800c01003260b502e45001c540c03200081410030025090b411a11700038010007030f0700b419584400005800031a84a2103031034100c15074220b81c0b281c400182561007240c4905500d821308528540702e0341003603001801103044054061250105020a004901c5024004e0a02c201e0489015130801d00c1c0311402c0c0ca4a00b280c4a0104040700d4000d8020314090f006802c02e503c3c0d02d130459006a40d14615 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 13187003 1250 13185753 13185763
    0x305030309010905010606021516030605030303090d0210020a0c0b0402030c0d110906010e0604030303020d02040314030706050a0b0a0e0402060702060a0908070503010912050702030c04020a0e040509060609071d03 93
    0x5100740340e90b44040f0101041000c0c0a190003d16580c006011410f1203003049460f000c2000b412013076000b10b007a161074142c5000340c0c00000a020080c2c110b03612490400406a0f5400f1044940400340c1300308072840c0d11401c25802101c0005000355501e00819845075920347d102c0314050412a49030254244a10003a140d41188e5181e680c0200b0001000c0501c4400380142c0c03440103031609041041c21000d0360000e858007012030301103079450f10780180d0328822108442d0003401a9080103020200901104440e40c0c00080948038032070040b0780030010f03038998070b094104a40710ac18a407508110180010054402d00c603441540c000e0000e4400d03880c1101d1540080c1055110a0451000c00c4404c04144003030f00c4104003036809004c1c198020080c003012512280742c00445111110f080010000326507007191028020b0404228002d4420341d19500c400101901d20108840300034041e0b85801c0025656000c0002d0b0140107800240840415403a002c40440300002002e00d440509182501007000310f4a080003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 13188253 1250 13187003 13187011
    0x90d1401050a06090b030319081b0706060806070201060f09020a090905090a0c14010512150904150b0402130e0709080f100e0606030717010908030901050702010e03040803040306050c0403050303 85
    0x800149280c01d1104076400c6800302c07107805019600500c10b82c08e01c0d45c0700b0f104c070101400e071500b40503040c0d6480303240303142040804c2203403400703584008940d0307900700403da402a030107444a05040d81c1b0719a6130391000b24200d620700d00c209058041c0c0c80b0000c200071116a40186206846407a0000c1d034540c480c01d292050700e400303845502c61a403140b40c40e00c0074050300c100640041c0c007018400344680101080020230074005c0a811952500e040c0000c9120091240e020300101e15014065240d00c0c50941080000e91100c2e0501c2c01c1040d0805d004036901e441e1034822261414032a030382100020741403000b0001004001010310341800700102c00030031020800c000485002e01030708020220240258406c000361007160452507c6036000d00c041c40170350755022600304280d80c41e00410882c3c4900000075180900010440513004c5440081481140c1da0190000f92003440c140d002840040003c0504540c2c0744600d1041814071b4005000900c00140340ea0022070300700200c01c0c4d44a0906803030f40c4405045a100b56 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 13189503 1250 13188253 13188271
    0x7050301090c080f060c030114010c0b13030306080a0308160203071502030103030201060f050f0907020118031d0118060c020402091c0308060402030105010f030f0207170d050c0a05090d140105 84
    0x200c003c010012082110829901800000c2c200605080c613444905000600888820000280300707892242d100c0c4900484864102000800c0c600700541c1d04604141a11021380c00a03041c844081203110780010420b40065065131500c0d0703190b40301640703450740b150121294000c50204000700c001180181444c082c900508140c01a41c95244d45806070031600c65510041d94486100f00400c41650341d044400030807441510b020a0310fa880100c100d0060040303841018031160306518032001e140e8440d403d030f4202004010000b038041c040c0f1005580030188100000c40040e070074201804460b11410008008a201420140c10680c200000484588818020090b105035420100d0141548501160740140f000d440441c03455052200003090310408050100902d0744481402c0d082e42d44640c102c4d91810f800c8100c1442075037584a9600d9180e1001c40c4a00240e400d00e0081403608a04e28122080c04020f0340740c09142003a020103108c00e80c03940200603203c0c0300541240006c601020b0084510900030a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 13190753 1250 13189503 13189523
    0x90b01080607090812070803070e1504080c15030127050f06030105100602030d0b060405030a0501060501110105060f010c021f0f03140c03010e0612030d090b0a0b0a06050c0705030109 80
    0x7000100f048046502521040d8820f64490020710402412200d41c1c82d000070752582d81ea0380e03516058030410443c40e4516007042714241c490f48110000e1000d4025107206205940d02003200381e003080300140d00e007144004040400c100401c0070203804ea030050800c01c0d400d07201c114100141d80300728040703400803540c4e6020710701c51400f000325070302d0f0078400d40c1da01a86114141001900701030b030003581da002d410403550006d0350361070f000040c0340c2e1048107550040000408841405241c0d04d01140600014842c450105440455414034607006002c1c0744e10480c00a051000414a904011250781e0440001640c11410010148064080f810304c070014400d0300e0349416145101c030580040442c1c01328001d090107220b15106104a0360355410480381110b9154801c03c1945d00e0382070024090f42586080005644400030301c04e02c1d48022600000440d5000d60580c04450f510303050441c0643e8280e0f105c180c0d00c040c1d480010b00500c4d00407000f40140c81c41f504110344be0b1580f40d00c0802d0031100d02e81d00c01d950342c01e070b5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 13192003 1250 13190753 13190761
    0x2030a0506010503040c0603020307021f06080d090b070b060f04020c0601140607031d06040e0106020601030b010e0412080a020919052103031b1306050d0606050405010c0b0a090b010806 81
    0xa680195900800207103002c0f8910b150507240c44903141000d0044008140d0000041a001e030300c01c114140b00c505401c22601c1541420a41c40c900400c13051040526600500c0d210001c068040c1d10500d085078002005645411160382d40d6001c0f6240050040354010f181c0b442898194540780f000c1c1821003001310007040300d0f50512a0049444001d005998454401003140300002503009002da10400d2070341c2403008007030b03003003000085141c0a01d07048030f018900c00c600000340301940000c070a4100c170b001c0c0240a149036204c03503048088501c201d5029080b0004480496161072003800166480311500e00010f00b480e40440002c2c0406440800303000c2b0717100101070123004500d04203100c5081c1e18203c8c1c0d0003c01e01c8208050300c0b600c074000101f100784448810071f1400102e110340000c40301c500e102c04800d8481c9584508014006070041e80420b40b40390328080003c94404c0c000c00840c1c09552058540c200310008036944d1901c50031005200c145404d8580c0600740000b8403440c83e80b07000e4240c56000e07251a2030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 13193253 1250 13192003 13192021
    0xb070903140c0a0b03060a05090903040308030907140105040605030c0a18090b01031404021c0807060f091406220501020c07031101020d0e0a050103050a0b03060403020304060e09010302060f031b0c010203 89
    0x3d1560018240c00d401007003844000e540300c0c804030084401c16100c0d01e181f0b58a441d0740c00d00714010b41d4006031056000000300140303540003042c01310548841e4820b0000d00c0d042d0000454040c00346010310004030300100301180040d031214003c1c0890120701d03d0480340343d610046402495000541c0082c00b07840d244d032f41901e00c42d82c05000b090b0200481040f0590f11345000c2e0005107148407462250004481907041d144140a12031080307404040d04004148411644020040002c00c01d60030261113000260880034404100450400c2c000e41c0300300344c0d00084c28160403502402c0b5503819030440d00d540d820440d01103610010f0216030300540c0181c2e0078050200c80400003900341140880d03104200800c1d64042c06c019070f00d0858030340c01d5800a28002403ea500d02e200c1d940202031504000341d242c4200c1d4201700400d5800801041510b565907180088014410284060f0340300030701000754008018042c0d942008111030145600246030001c4070800c0d09800644882988103106161040c0d400004002c4445 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 13194503 1250 13193253 13193269
    0x90103110313020d02120102070b0f0601020d021b1908010501140303030f0a020a0509030115080f010c0203030408070318030b06090117030316020c03070e01030501060602030906070b070903140c 85
    0x40316140e4114694545800c05941d4844070640083c400c08a00c03042605645801c5082c06090500e140215070f22002810300100e421021103d10340f42c1c1010701c0020b4101e51000c510f4011018203500145190816079110642016004440300e070054041d181100305040320000d004018410f6000000341c07035050400c0a4514104081e489010ba8400c00a1081400120002c950b100d0300d0118016200d60041ba01101c0720302c41c0240301e17903040d03080c040340c16400c66114842c0011a5030010403120007e0740d02d00c0b910309030f80701800a400540c0042c03000a02041c450001050414400d00d41012141643c295645080071181c006031403228070784003004500e041c0492082d014000190052034071501d103c040a070f4a05c0014440140c403404241070802c1c89008001007400c082d4010705548643d51104c070810b0350403009120a0312590b080060015003a8004411104001c2014007018038003441034036442c100071805801c03030301045540080080490f05200300d5007a500300b0034000d01000440b035800c1203454 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 13195753 1250 13194503 13194521
    0xc030304060306170a2013060306020307030c030606020d05030c0417060405010e0102090a060e0f04020a0c1e030c020111030d020f041d060a051c020301050a02190504080d030f0b040908090103 84
    0x240d03100302e03810004500c00c203070341d0b10181802c80c0c00003500402001c007140320034134682c0020560a0030623001008000c21500690311941040c0d804100c00701007030008400356071841c865140582c1000f510040346502c140c0086900c06004040d10f80340940c1c40c0688194607000110400090700003400b44000c2190030301400303802841d800c009504100c46100003c82000ca40c0c8244402c0c000056101c0807141c8410f443c240d142b0b18024811074854400300c101802c403914580c8116010400d0042c2c03c103d4004c10400e0000094143e91407013244480c690040d2084084030b90303084858030060140020b400310b9400148140c0e483c008001d0380b2585001c250100d08038100c0301400d4000c5c416403c001e55074649030080c108541d0100c841d461490070100801a401540708000f0303425500300810440c0002090300107000c2e44100d280c554498040e1000219400d01680c0503940c0b584d040500f176081300c14800d4010b22541e640d1a000014502d02e1000010200c03144004201c540e40d07004100340c0480e40c1c040c07080340c582c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 13197003 1250 13195753 13195799
    0x209062809030305030f04030309050a11010908030310050103090201110111070b01080303090a23030403061a060315010e040b0310050a0c090302010903080705031606060e01061b12020c030304060306 87
    0x740a0450340d0290050000030b00e49030001e0301490026041c0b5129402090301142c01c482a00e100f85003509041d02c4613001840d4540c0030917202c8800007a07542d000411a4496402c0c52001c0101b581400d00440107020300b0036041e410007030075211010361200b0a100d80c2c40500d030002000b40e55940c641c600300008810580c40300c0e805410901c1000b402c0303e80894086a2654022201c0b1414901d1481040b10b050300000018610310020601008002c02e681c030032031440300301070070350310300009071604010043c4802c0340e290465154004052400e94050441c1f00107450b001840401c2100d03045000c00c1c60030106c0f03030305a021291a4010b0044003ca10700c107400410b01c262405642490540e00042c11281030792000401c100800544042480741c18016258aa08a0f41403442c00d180d407820007101504c100d00404100910110001500303034052041111011000b0300e44180d2142662070b40c1070101250b0701c81809501a0341071510590740d0910003040504035030b031000180d803405c0c400c3c100324007025030951002c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 13198253 1250 13197003 13197017
    0x4060b060405030a2604060905040e0304030201090e04020a030f150609050c070f0c05030106060c0c050303030105091303091509030302010b0303120f0c0c07030606090510140409030302090628 84
    0x210b62000301c4c0100d00542c22014844c07200d031200c11041d2813000c2008185001800100c0c1c0800c1c1e541e0320000e42c0c0c0442c3c1c001c44042c4101d1005c1009a502c84c425440001d01240400c1d004214615803000c01c541e01500040010710301c1690f03500c40ea81600102d0304c04942c01c00d241e4541c522000e40603c1041e02509040c0420840351074580000034291180c40c6000d4030031562021a1020030070403100c068003514015000740003103130390b6a03005005035003c8442202c5910b060f00012402e41000000c2d2412910020000e0000362140506521201c401c08420303010001c5c2100003080141054040040c802503036a00c0072505461801d0082c21941c0350103483d07120781c208100d071801c0c0500c082c60040d0840c410031b04c110720700c1c1c64140d08601c05101d01848994035014800c400014080ca0354480c0040b501070303d0060203d41e46440140741d40981b00d006040c0c515841001e41c01150500d68050003801e486814014074042d40000055819003100a4840e0949800e40300c45040000484e0219862411420411 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 13199503 1250 13198253 13198259
    0x20906041d160207060509030a02040e030306090c190302090607020a03031115010e0a0507090305060c1207020a030903110301090c03080703020c010f020607082203020114060f03060105190305031204060b0604 91
    0x79101d44c800d128100070040c0101d00e01d41180d4080c059001580d81c000d00801081071031085450716500304554441c81958607400090300510340070101c03038101e0000c070840300f625004150282c00a421042040b504040300f03000c40d40068913064070100240d80640c40e48811035020901b01450035250f81c00100041030030100400455015612150304030801030f1002c41c40d030361941011204442154409031841c0b09107010b10080c018048020840c07607050002c140303a25030316041c06030b94038885c4281c0240041c10050081000c40d081041803641755000a0010441c50030540355828043e8154005558a0b01c001480004058041040245100c3d0a00708070320380d018106c50203521141f006218205010312000010062031850b9107050307016903110442607000986060082c002d010006030384411050b0203001c20381510f8000002401304400600070034042e8240300c207100d01c412900c035640120803040100400098001c1c0060b1020004c104040c01803490181400c1c0c042c0c4140009460007480100014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 13200753 1250 13199503 13199507
    0x605010c080903010b0303040905070f0309031b05030405030a0302010b19030c03060b03010902040509010b0a0519093209010c030b060904020a020f060a0b0f03011a01080901020906041d16 82
    0x303020140d0441d0301c664403000c0b60004070340581072420782c166050100250218507a000740d444140030382c15503520f00e07404c401200015011290b01c040042c0118030000c001ca01504c0c00d0b01004d45886119030142c81c181350390340300464a0988001c0303084002d070751180c8a003520717804d02c010902d01a100001e2036502071840c0d03448092241b03559000c05041c160301d905082070f05440c01d41003050940e9015100f00991b00c2e112050f68024031000304460300c2045089130000303007494032000310304100d1064a1605001072900300c004004000109a402d0307880d5040f030380e803004900254000d400602c643c04140140e031810b4107250742118025484041814608580b800c42a200c950030f4580d40001590016501d900480e8140e103804107003e1307070311007034480c0c0020011140a250000c265a1000b070314894070ba41c0310031702014242d600503500f88159840007000c1e034003998401c0d07515a81103498103000515160002c0040743d0b803035101d500020398080141b42c001d100d82c0910000030303601509015030551842048000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 13202003 1250 13200753 13200767
    0x90105010f0203070c03030801030209060414130212070308040e01081b01120f060816090203040f120512040b0105100e0f01050a03020c0102120601021207030813080c0f0105041203060501 82
    0x1950341048029101911180c1c000c0003181c2543c1e801c81e455584079aa07c1c07800900c9800e0900040b03005500f5080441d07004e06107401500050a0040c0a41c142640c1d04503031817082e40c1c01228142d03400818a80c1c0341d22003617400d00503132016501860407a036a0360300700b00b0411a1424103030301c0200d440d4005a0442da130342800b4540c0300308081091030001346040f00d00c2640d001809441d002da01100d8981640041d403d40c0003e141055403a4580f102641e2a6a5032482000c0380001c079030141010211200003000611902440c0c1c1ca0134010b410b2041c1003004240100c0c482c0b0000711000c0b03466200d807d0052009140410000a9000d003e2408441404005d00400e20420f121207010741800004104010000d000f50151540b01300074030000c40d110010307074000b044c000c00140c860a003d8055158940c00e0081524100d84a440d01a100c05010351a0154602c5600d50001c00980d41d1070810f00416001c020140009402c0070020713800450181820709258080d005460390b814141468805e0401c00b40e604085 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 13203253 1250 13202003 13202009
    0x50304030611040e070e120a1a0702010e0303070804050106050907120b03030d11030a060504060b03010b03220f02130203190b040f050106050a08090c06040311030f0d02031c0b0901 79
    0x140110b40000e07a9500c44a00d40907a070003560b0720038440707810000c44030750281042d1011001151b10244a407a1003007095101d9462030300c080c0401c015492601a02d1f28100401508010701e440001009040c1020641c11a0030030303600200046da000c3c083c002842000d000d49809410226520600c1d810404c6000e0280c0388800d01c04036260f074a60700d0a1800350350510540d41041c643c0c000900c00c028018080986da070b40304445600c1181d207004c10125076030500e4407a58040d0742282031030030b1859082000050481e00001c015110031510b03c0c8114030010400020340d0ba859104404100460006204001940440c0500001c4041c41071003041b4289803014203841c50040500d2001410140c50400710b40603044050b0403452181c00e02000003a880e501c18003c000c3c00350030b541da1302102d8030341004194032485034403d110741c4070805220610114030000c680c010001401012581c062604441c00c1d403c0003501d41d40700d00543c00124440138510140491450240d140f088104100306225000681085041c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 13204503 1250 13203253 13203263
    0x8041505040b09011808030d060e0a0b0303160501020904020d05011511030a0c030c12080601021605030607080606070204050702010c0314010e04030c0503120a0504120c050a080d060504141501020a05030403 90
    0x40c070217400312030b103090205000c1c00091041e00d039620803000003540905a02c1c818003141c481c0c0c80c400104d82d088070344155841d80000602840c0b03009104900017051000d0500c06036015503007001103030195900e074401019082d10046c0b0214496140c8511450058085012a02404402d83e9142c030320b0b41c404011103440d802c180c14038194051b41828225640407034404010032070140c2501500300550049050781c0314946c02d03401c0305e0000040c103640c0c07144400c0034400c1d41c1d0164401404900500d0040c1200c560112000d4005420510180c00207400d6030416514000940d41d103a03031028110f981405020406c030300c03150400710039524000401698840041c4042c3c00c2003501c00051082090030320884480304040060f0003220305004807c1d000401c3c0c2a501240c5081e407243c0240e00303042c0244040303031800760424050000850b6a455409444c0c3c8a03c040d18101542c8400100301507695100300c2325429050750040c001803510030640340c48a40c48100e80ca040d540310301d003020b00003480001102c082c0c95002c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 13205753 1250 13204503 13204517
    0x9011a04030501090501050103051921030b100305150d0f060209010c0c03030801150c050c010804030905030106141c020604150c0210020307060c0302091003020c03040306060308041505040b0901 85
    0x9011000500680d00020440c2d42400140028401e054000a050780e0040c02926490300301c514003004d81d075070401c00080455900d0040d054200c62110304a090348001800d010624440907030000f41c4078000c916102010954510902044032080d102680140e40c0c141e44840d038203890740c0c5a800d1990300d83c490050030303a0380006034100c10740d01c10303140e4200482c2d100c2980008141c072494050f05540090050b89855000a6809100d0300c3c03090361551511500310b005400140e0420004481f0194020001e070284804440001400d0300c0900c03034080103000a42e0408001207520f810000076002c82c410b101c0c074a600ca40c0184004d039032100100c408a80c400c1d040300881082c001c105548020240d0f101030740c019404400c0c1c00d055034010000384011403040800300b0003100001401e40403400781c284034540000740345c50140c01e810b0080d8028101613806001b1079052540e00c0da5250199a1607410440e03003a04085010800c582c46680c2c0002c1420301418103604150802c2a00e901601a2602140c108810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 13207003 1250 13205753 13205789
    0x11706040b04060e01060e03060c0d0e070b0d0209010e180c030a0905060c030901150e01060f0302070503040b1306020a03120504152c01090b0601030e1f06050a0b090901 74
    0x21030340990003003078010340b040c0aa1a601c4505206814091040002080b001b040780466483c010464910503205c2d400c0450800e22040c80050003007000c0760381c100c154850305401040c480d41c0303c03025010240440704050b0b5030b80030314000104008118610540203001495803800e030340c547c003500c0960002088107019180d50307441c4003400c09070030f074030388040c00340d0103044144100340c4d1420b40191311079140a40240460414281c13228090001440349210120840c801804050320070724681000058524025041a1881d120541198066802003154240020309900716041089400c0d00400690001e413425403c1034402a0401e8805100c120881e5952400241000040c0500c15003522221008200380e070030207401c0c0c0c108104012044a011303440c4a509151100c414040e400100d944540071a0064603440700640242c00c1c400d110075203e005048440c0c100d2185480c1204a02a0004020494500e0a81802030302d41c00c039009a030174014200b00920150b1205502079044860801c0400f00c4152 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 13208253 1250 13207003 13207009
    0x4050a091113030302160e1312030209030f0105010e010e15011b120207030b010503010c020325020904030203040e0c030c0711130207060207120203030601020d0f02070f03050d030b010e011706 84
    0x2c144681a0410381c10441d01005040d4001021611048035001aaa009032604090f0301107441c1103407a800b501c60180c14420001310390480011003641c0d1410094200080500001d0800e0240d40201240303039965001005402c001800c0305004140030b800485d2242499101c610950074241502c82c10f0040c1c6844040c008100f507640303401d001d50801c1c2006a0b1529460009490b2507407440240d030b521055100108503443d040c0b0591344111480e8004510309041c03020641503615004561400c1d00e03d4010080340562510150948254030a601640c1d5450415030108904403001e82880c011101c24400c00842d00c500104890403542c0200c4540659158080082c001401d5070070029105400130940c03000b00609900589100752207120b0000301d54008606c126078a02089400070b00590012078440c158900545200d10130100c0c4d84199046640caa00c00c012401001d94070841b0a9800400480d1046500d44500810741800746805901407040314002042c001449414901c148400c0c00415083c0d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 13209503 1250 13208253 13208257
    0x30303041403190201020901020705041506080a0207060603080307080a0603030806090604062303100c140f070b0c09030105070201050f0619090603060c1202250204020c06090304140604050a0911 85
    0x75258080c06510749460f030100074040d4010010241c090300c580c0802191600d0140654552100395030503600d2546e24141084801c4a80a0700550ba82387e820892140441c0082c002d45000d54051000c2e55980d00b092803004000603001032109200515140c4240300180d88412101c0e08601c0031144d0300000d440c0ea030006801000c2d02c1d40200c4d4a43c05158035480f101000e030005c800074030307030440070342d01c60340c82240d0302c8000c3e54205800c1c0f40006001b505031450100d149406052800228100107007001e40a5841414540d010ba4029101d50380115400503589800d001c0e060b40881e16100034455801d1042d041d0806c1d6801030300061103006d621228a51a20380c4480800c001c150aa40c1403010b2552818500001c10b80265590001002d0300e041030f6001d54507008a40803075a08402100880018001402c1070708155102284c0c80340d000c1284100d0201c007041414000e818010180d0b9556160280d00c00d401c00811300542d0240000f440200100d0381c23003c51200481d40041d4020a8090398030b0302c01d460314 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 13210753 1250 13209503 13209517
    0x50402061224030f030a0309030c05060408030406060b0a020a06020a03021614120c1207060b0402070308180a0b04020607030905130504030e040e0d0c03051b0606040b060702030303041403 82
    0x1028840208140941800841416240142602c401c215800820b25032221154020084140d10400001603100c0c46035009840c914024600441000f080f07036196410014203175815903d042000c0b06000a11200d80b244c03000070800a5042441d25401d14000313134030f50842d0b80b000342c8241d6005c45e0480da40d0f4080c2d01181d00218072080389d950904c01354030700b501810b10842180c14192150555000c2060900e000311504d5410450081041d0a40750000c2c0341d16034400c20084410316140c440c00509034881d80083e0000c42e100352920403691a1994105006001d0f051020340340c3da014071500c1c008170b1400400c0c2c0e508260195071969940c00207081c2925403101e15031200d90003880d441650041aa03980e444140114800d6440c100340142041c100320540320100550309154004c0c001643d40356004a02040713a03140300b414107a040c0894160040700866510302160103941045040100038039103841500400c44044138050708000c00ca03000302e40d40b4080200010285034000c5203448441808005407008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 13212003 1250 13210753 13210777
    0x4140307080408011107021c050102040306060b09040b030106050105090108090a080301030b0406061514070c090c03020c0613030c12030b06031003050105090703023d03090302060121030305040206 86
    0x1564140e46030201c216441841040d01d01c0d403810a44068605111007280e40050b0020410182c0e059035000061010340c98008c11200381d9420007001001500900544004202d40020543c40350020b00510056803076142445220340d240c1f4005003c20f03a040400d46150643c04c2c82c01c04c0c03160355000409890603000d45000703840000084000003c00ca501101188a80d100d0102400780359a20400b40250a2414441d400403a143c1c8548913168040280504581d0740070f002507106003aa680e40200803100c401c80382c040000d1300060f206a005500f0001107402010310386141e003140b0140c3d20001d0546544100081841d054101c800031920b100303412101000c64020406507690420300000c1000320317440d02c012696035080ca000a022030310045001811607070054400c07142d1951040002d08040811441c1034160382a1307160700700c00d28880c1c60311090708041c40d0b10001001240d60030080c1c50500140e20102040d0580c251400c00300b0032a200c400301003035050801045644851000983c02c0c01000f0070020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 13213253 1250 13212003 13212007
    0x307030803012303070501030e030904050415110f03010501050c0a0b01060302070210020a0f0305090111070b041a0705101802040207050d0f03020f090d020f180703050a0b0315041403 80
    0x1032092000046049903802880c41260380d00c000b485070300e24040380403101d60540104008100325400380e080b80c0654058607064a1521070360700c00107030031202c05580940700300f803840000002c041d2651044d400b1469410b028541006900c0a800c0a503201c14082d4904018001c00c0800700002c040080200c51680503502050540e181c0078002c00135000b00c8016441180c0285000c5030381c0e8000300344001ea880e008041d054030010145c80c150350f2680322a441300e040244031080700c5415403041c0a10005002411240f50b075846c42c0c4406012200d0a00d0020800c5031020481240001c030002504103400000c80c00c081035a400e100e00054240c4660f82029400ca4000969007007044030100c2d08482458141d180d07640c1d18a8802c0c0d045040340500181800018001c00080c7c20f80e00d170850700c00400b10300c01006100b0000d5060040b07590104801c0a040300940b4800901040c26014001e1039030101003a042005584400000030b99243d140e2000d840c4405030f40004182030040c030a05826056440c902107076 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 13214503 1250 13213253 13213259
    0xc13110307020309040c090501021506030f0a0f02030106050102060702070312030213090c08010603020301050a0e06031011070605011e0b160606062c10140d0f05090c040e10020f0403020307 83
    0x42e407660b1189821380e20a41c58a500e920b0620700960013181a2101a402041c00c51201e99018001c0c29020740700700d505115805200b0703070580042080c4001c541c03148140010384035031131060500392012038001e20305540043d800c015005900089650403203410141c80e481c00052040190003d128107601e002020400ca400400c82d41c9440e00203111080160b503840b1056a82c640046040340828050300768003603e24401040203480000003603401160041c02e44101205109126040b1039494080c0100b0010205548007440b483d80b141a0041052603402e016603080140c00840c81030690090441003c004240c1030f09100c030400b14104450780c0709800304a9240c603404051f042010650107040001c1007903100e0003143c1419410000b0a64002d4200116a0b800c1d0304295000f141c6840710081d1030400f403106080200880c0540c0340640c21002002543d41070032050541031034440081c02d802a428102d141d00c00c441c0018103598180c012450040e110f24106800322058411544041d5040c400d010000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 13215753 1250 13214503 13214507
    0x5010608060907080f16050409060e01031b030809060313020a0b0c010c050f09040e03120f040201081302010917030c030d02040806090a030504030b040303020c010207050a0201030c0504080c13110307 87
    0x303402410110341c1500e540e903910a084516041c2117030758100c200610804a4906807004c01d20030140c006e2420039030f0070151190350180071528207170b0201280020040c010802d20010014040500c2c506221048403a0308503122043d8502c07030038110a003c0c2c4000000144010501040c08981d240e0082c06503000e00d650316031640c0a9001407041036660351070a0b8020303152130b000b03030219000003c649040e141826100c40400c401821040240603160204128070854500000c40540c400c4060b4407448800c1e0600e07000040100d00000c00d00f03d00780c194002c40a0143c1c1e04008010101c84494441001601d44950360606601410303402106a200108500c5c00503842034000e001500e0790001111080e03510b49100c0d03030755442c2c04040600402d00070401032010501e0314801c41d40c014000c1c10302500e05014810a903003281c0c002d00c8295106d402c403041840456925003c0c06400c0000b81c0b401034101b03030070f0012084c1c0f90606428800d04c10023040501082e0b1003030f41c1e081148800441c03e901030f00c0e8035221f280 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 13217003 1250 13215753 13215767
    0x708061c060b0102010b03150105040e0f06090a03021005070804020f040b040903020102070b06030c060d02160f03050910030e1b0301090b040b160f0503010506030a0b030303150a080105040b0613060306050106 91
    0xb0441c09542001e68201da40d050020303208141c00c0c490200c403400c903403070079003404020f010352500030082d8040c0302c82c400d01f820303010800039014800c41c500070105044281002401c0c4100c0d0031150351564201010722000300d50040e26035070401c1e0125114072080d9100c1d00020004e222202d5582d400600b45444181459010740c068509140110710b035081076075400301055298007031610300c69802002401141c1207424294050710001401544068000100f03071a000505082c00c4002c0740043c200181e00b107100d080905074414a002c1c0ca040c24000d00d84000450381d01d513844608104032244420100d042507903825042044200d4001001d013035241000c1c2031002d21280111031100b941701c83c1c21410040346100382c2070f20007000e05650791103056034200703420480d0580c00a00030120340350301e49030044207690b41031000718010021203001c015141000400d200f2104000c1d40044001c0c0d25000c20407010541261000b9800340046a5028031102d00280c0e41008189540000c1d0000307240c00000f164458210780 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 13218253 1250 13217003 13217021
    0x9040b01110115031b050919110403120e19060e040603150605090106020a030906080711060c040519120303090215040602010204031e1101080c0705030c060601030e030f030708061c06 80
    0x5c201c50400194041440d60b4103803500c64181c0000050300020030030b00300c08011003040c0d600140c000c00c00e80c01143c1480c1d140e070055002928101182c00a50141c10f40002c4190880442510308400c86401d0b0300e030101403070045116503402c0c024103803680b240907034540d8080d0000c1c681c0320b076181e5001600d80c2c81d00002842903010f040c1c06641d4503030021034031500000340300e0500355140d40c5410344141001c1c2c0403503448402030018014401e401c412604010010300405104403002e4404036156454241003260034943c00c0f0035001e0900b401001842450900400180d495802d41004500d40c101d40c03020400c4402c051100020800c804900458071560640082045038003c2d030b400003c03400000711400500b6540c680041a8040488820301c61707500688840c1e9003c401200c1c0c031401c1422507203030242036910180d21240503401c21402c000013503816125031070640030324800440c10410800000001444080c050fa0188410000090419074800c1c44030703006030180c2245d42060b0052031410b14040d00c4110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 13219503 1250 13218253 13218263
    0x408030901080c040e01030f0204060b0a08150d0c0911070203070306051501032a050c03070b040b0c04060228080d020d06050f060405040b0d02090c07051b010509040b0111011503 78
    0x2000710b070f0503000350303826102034400750b9011502c26440c550710388407440071340f41d0102e8115444400018500c80700c6030250072080e03113503111701c456854580101309a500624074010f104190b090002004a030008000c80107441440c080041c079606e125a052204e4001c40c90003e61620860602004202c115005140100c200c0b0070b04107200c10715000150306450060041420840039886118440c41a0807840d09101c815420240e20701640019a40c0c1541d000090699450001c5010b020401059160a0b43c0c0000703c5819a410310b42000301c001e440c2d50751114110390b090580002c0e00181124448190a07041d400000555610003100c1c0e840003a4103c1d60041c05900d10380b11001a03941010f411004942070020301e140e00d000e040c1001c02000b020302000080c1c00c80d41030030001005841e05000f4a00030b102c2181c07165168115490424a070403039202603140380f8504541000c0e00c0d44d801c401a40d41078401110085021032000004071083d00c85401c50410701d600b424090f10102d080c041d0880103481c051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 13220753 1250 13219503 13219517
    0x318040504050a230c0405070f08060a03020a0b0a080903031e0c09040507030606030b0a0b030105040906090b040317070908070605030901090c0905090c03010501030b18120d02090f040c0f120f020408030901 90
    0x403000301b00442d0702c1103030301070082902034090050040c03140d003038150b000100170003900c007080e2079802040b02840680c008461200b00094580102600070035896400003c80d001140b540c50aa43c0c0103068000c60115000a04030040200d801d040603002079480c609400f8008201c40d1600b0f0b01c1c01005401a8803070200424a0403800ca802410520301c2c24050364400d03862289103928207024440284400d03071094403042c0e91140b110002502c0c01c4c1d2841d01860007a80c80c0800500207080c0100d800a0140c11001400403400b42000b00340b401260190413503215060a0f51241d64001c8144d0241101210081402100309000b11303044036658851805400e14400303c2d1407541d1074600f0f26080f07510038000034106244220004a00f108600e100a41c44004841030311a0580d0361290601217402602075210219000308024000b03090200104403d000101c0c0c052000040750400030300203c82140c0c1140400031003e1a0301006400c50300191262034108804564956440846641365000700308120300041d01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 13222003 1250 13220753 13220773
    0x305010c0f03110a0c03080601030f020712020114100614090301020a020106030c0801020c19030201060b07060504060b0d0201050a0c020109120309050414010501120903090b03010902070209090318040504050a23 92
    0x524013513038000c6080391580440803102d52425a00120b00030440c5040580b030b0813005c3e05203640d07030001d0400d1a01c1000500c8044240010203401d5440c7d0704400c0c414501160f082205503010b00380040b086604a0a140801a1908400c0400c40c070824881c5034256000080c004811039055000000b101c2c0550501c0d40c07115100c2c43c06a090303209400704160681c0c003000001940600c184030501600744a40000907525070303204001c00140c1c00c003101c00e840c0c1c15540c004000c2800014024250940021070f24030b0040c003566030001e071540c0920312600003080100c2801d20116400380f41140c01030200c040315011030b41e90302d240003090045540184d40c020383c10714115035150201c60017000e040c0c0d601619404200745080c80401c0c000c0041c00741c154100004000002409040c0e08001c501801840d0360150fa559901c0c0180020042d0161442442c0d60040003c0c2c807500010240010050344122000702d02c6445034100f041c980503121001078848503001141784c06d04007483d546500d000c0c504c00161002e03400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 13223253 1250 13222003 13222031
    0x80c0405060f010c0605060319120206070306050d0b070e13090302010b030a11060703030908030a020903010b03060108070909150203090609060106082206020c010e03130b03060a03020d020102070305010c0f03 91
    0x5482e00e0303010702080790120030300c0000301c080d0409540010050219051081c020120700340c1800c0705242925460070b00380030070240d44c1e41071101c00e07440382490170301b84416403500e400706040d8203481601410210104010541c01c0e4414110741104031001051024110300040b840c2000f4100103400302d0143d8a0208a0b030254100403440c1807181d6040008410306030300d04814880d6030740c0101c50071010542d80d441e003c000103204402650244591000050325800e2450615007110b126140962181e4030040040224030000100001526011034021440c40041d25014450b040c6040c0e440c0070003800401082420400020302920450b101d1003160500e0741c2c0c03208103848400c000d0b00d80b060400c20080c804541c42c51710540021013580303c2c01c00145000116001c10342165170b0040204c61035003001520340c106c01c42c0000e4072030140143d040b900d451410110300181000e00340b0304c002801000e1000140c015a13000740308400055820400070f0211500341c030001011000080001c00202c0c3c41d09012420b80d032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 13224503 1250 13223253 13223269
    0x90506060a140f062116080915011502010e01020403080304020103060b04061428080403020f07080a060f090803011e06090b07021212040b1b01050c070b060a050604080c040506 77
    0x10401400115000c1c58541c107025640d8050f1081c0c0045030a0740401c0007005d001703020503a20034250f5402c400340b5040e000343d0050038608090312080d4680c1c002c800a2083d480920526411140c1c44002c04000c02590340e402c1c0e0241c5640e4401805552011030000103001d019001184510320076038003001415141c041e410b0441c000e9020f19000680300c07020001824056030000c284495549080d01485224008040d9440310380c05500c500194048042c40300705070b010410350041c50500c1000d0007a2034100624555501d010700d102800c03450311a001d4220175003090348410051a0008100b44d03480d038407860241d000d0a42d8201c0015508200280090704c10721a003c008181d40071802e030780d1700c0c0c60303101d13007c100002d1403280c4c07503008074000d40c00b0a19004804200800080c100c01c0714594132942c1790301a00861004203141c221780c0d0b9042c041041840208001181d8445070f1001c12803040f901c800d0086080007103035070442d03600710748002008241d414000410900044c0c04070350174002651010b003031000d04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 13225753 1250 13224503 13224539
    0x610030903080c0702220c0206090c102001020a02070303020c0405041505060a0b0406020a05060a110301030b07030b190e0610080a09020f030109030c02030601060507080703030c030b04090506060a 86
    0x9014800843e8003404482c0c002d000c5913000422451a200301180180e48440d0b09540e0f503500c182d5500398043e1010f405100295008500201500c071003d0640040764200c40185d44070313020414001c000495010b18004000e40d000d94031f400842d101c0c40d0802001e59610424002a40940f041041c1c003170072441d00d406840c1c4200c1c2c2c0a80400c0b0382185051003400075041c09000c559110b80d04240200d4540e424001610060105038000c04080031a07003802c44c01c065028101c0c5030301c28140b2802c42c41ca400c07190200d07411281c3c0401c2c40310b05580d41703039000c40c010440c890070650700480001c0307100d40c0f108803400d1600c1aa401115000ca154440c00c00304403c40d050511200082528000082c0d4840340035405640054000f50403581c540040400082c00c44484000407404035170a94810401c1d400c0412026005d410241802741c917001d0592a600164001c180c0005d04140d120301c40d00944612075081000d82250203001803250751075901c1c0040d141d9034222611f6020342240b000016400c102c441000200d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 13227003 1250 13225753 13225757
    0x15061b080412031701033309031211030112080a0207080f1e030307020718090203030d021809010e04060b0d05030705060714040506041208210105010801050105030402131d10050610030903 82
    0x201f40110350280b40d4440300da00441c49442640805100c8442c0c82c011030710300342c0c1b0070740e5108185a1054481411500403154100301d00000f40300500c1a5083d0341161541c188d049201d03592194501c140407413820b412604401c80c90f00800c50b5904252000158440030320311000000342d01408404c0b540c0d6542c1c0405c9410f440141e0103584108004d1102c1c01e841d045042c0031100c0400e15003ca40c0229242d40e01c134402491400b81d00092006030b01000c41d100001506080764182c2c3c0a5161404003151018041c001030002940c0e1707400800c1030b42c0d80b030094101e0542d100094944517066428515200e017822900c1002094542d4102480b90140104880a48030300400040c141414209e4210b401da4520f0000c66044034100034900c6481c2600310500282c0d030342c2c05107941c0b466040c40001045c8a0060b480301b41880410700074000181c0d02c41c2c503400c41304c41400d00700194400080e130f40c1d01c680380c0000c1d002490034001c04402402c00c043d590400c512802080e686521012a400d0040b07048460164010300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 13228253 1250 13227003 13227023
    0x902030d0302071212020c03040602060a0c0e0102070303080901091202010203040209060301110a081b040f03060606090608060909100f0902010201110c030403080c0307080406030209040f15061b08041203170103 92
    0x111350750082540c44150390078400014185401c2c05042840d590194100d400985d02c4a41004500044c0d40a4000c56441502e0301c42180301003400040e568601500001381031103405800075000007402d6201c524040d030480f5240040202d4118042c0c000c1d03209840c203a020340d901c000006d08500f014002d400e50140b1610403c2e1070016101e03c101d40e070b1003003c0e00c561865800d07038140c20140c569079400780c8043c003c800d568044183c5586041c5040b00c140f58000b1080c044181002c0000640103015150300c903e095400d0b01aa41e2906510b1f03041c0002d081200c10101e20b00482c903805140140d00c4800d5451007078000b00907102c2514291112401417004403005503200300800c0c400a0780d0700002d04071000c01c0d0001c0340c1c00d0421956445801e600107421250019a021804100601d0719000720300c84000840707400c100611100200c4c1ea10449175005480c280210b46040e010408000506268983d4000490603203840e16401d184041c40e07551881900040e0444030481c0c0c0c03003a405014241280c2d40000c00035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 13229503 1250 13228253 13228283
    0x51210080615011101050907051008060306040f02011e030204080d020705030a02100228030305130512030c0403020904050102090103050c0f04030b060604080d17011401170406020415030902030d030207 88
    0x2028910036802d06040200307242802903840d01c01d000d8503016440d900c002d802060b08290070701543d00e41e0121400c0803c40400240140b54501042807a007203508540100c40410240c0016220b0328660680024244c5c3c120303060740e000d0380c0c0c542e0207881034640100544e03a170f800e80e8480c00c0740e481015018817540360b00180c50410041c581801004160001c1d801030741c103a030b40c1e184a010102c1c450036800074141c01d0318002e800c0800d40d061188907030040d804203a10500a000c0d4448030b0380c80c4010852a06858000004111080707860320a8400841d8001e1001c0309500d061f1810501075003140010a003c40c1c14100400c40300107044003514004550302070154181451525140d1007000301410691308608100710100b42403005120030344403043c0035100d010400340c0752420400c90b10350507032062180b8642d90524000f1680d100c56000031140c0c00c2190685036490318141940280b2855000700011000040348100705a0150042c600340c4e40201c06a41c2c0c0c144204501360705902c1407000050162010b800c0030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 13230753 1250 13229503 13229521
    0x50703051c150603020307020c100c02040c020f030f130e010303080a11040b0304050f16051e0f0301020406020f06010914040f03120203070e03070f0803040b16020402030103030512100806 82
    0x880310201c221002c203800480740c52204a031106604820b001075000400c01050319010414101d000d801074400d0001e900d042d00004104040c0400002c2c4150f07203d454031400c0d5803003009000c080407410000c1c1c03070340e448905001688962210800510042c1c1c442d500003000060918654100e0f0303050744515165694944c900d0000300103040c0c04024801050002142d50040c94002c6c0d44a80c2c4220000c00001d05e000300d16600d0940d031483e81420304102d0070018030483d12849045001e2407071b072580c0c16007034800b18800200e20128030707035440350558400304002070b049600180c1c0f240c13460407420a0300e0041e62a0080c590a0321f40ca070822841d12190310700030500003040610244290f500900e854109602504400d101340e84c02a65000006031b11441481403a250a1245c0070050014018a070841880e042c0a607440340198400c0b0912800302180e020320280b40b0004200b08164002c00465407580c4a250103801c0707070442110b840f000310307181002421030044054000c0a83d00c440b40204080d40e940114 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 13232003 1250 13230753 13230787
    0x50a1d0105060a03020705060109050406050906090c040c03140a0203040c060801050315040f0b0103152313020105070501060308040e06011d0906060c0a120311040e040807021503070c0302010c05070305 88
    0x1a1000701a406c012010100f44203101e0f17140a402c7d0043c000c06c0504160400c0001c0c1e440290070b8101d260010414410b0440340001d49040700e410945001c210710000500c164000d080b0b0040c2c55101105d071508001300c0e200c05900640c400c2d0700c03c1990380d440301e46454044501041c00d008042e05940704002501094001c0700c1c02c564845d01c00c0c1c8039a6205441580c0b01e0904110a130f20444180800c00003903000074149014001852156040c0c0b010700c20403800854805042c007401030282d80380807504800543e403041c4100d41c034041c0c200c4000d025496403441e0500065000e442030300c55145c41c210108a196214601200741c6000400c0d00340b207407158150402c144c500c3c2c050308003035015030b040100809594090060000c0c0303a000d0092502019107281d405801d485074007110745005a000c03c0180100880110000d8006030480b00c41901d407500d6101141c1c20a04500d4401030507200482000035155000307031410f40540c8281c0c028803110462403029100360040080080c041340c024030080d05202d01e0411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 13233253 1250 13232003 13232017
    0x9030d090c050d0f0302070b09060706051b0c2a03030a210609050f0a020405060703030504050a0b04060902010f03060b0f130509070906080c090a120515070207050a1d010506 76
    0x40311a55403542e4000065100e8500101240d4003682d800e604010b0580600211005109400d0054542203030b503400900035202e910300040441d039903000441c081041c0302c68658109a40405103a90780c0202003070342c83d540d00c002d00810142944925624203265100c0340011800e860143c015400d1402c0b503481603403c0c0c0c01c24030980740880c000c40a800c1c285c620a01655004066a610009060801d500c00035182c030030052042803400c3c01000208190b0721030b01c00710303035400350546000105500c5901d0b145051a00c1c40d5006041800054184020301c0b00c40c1e406a04101c3c0b003601c921075014401d800c1941031b03a007035201d6800204401e0100c2c05075115024010b08024035425045070050762100c0009201c0d08041c3d0301c900000751304600510903260005a0550003402c080c1e4494100810003002401c7c905007401140780c1d04e165111000104403080011840c0483c400d1030364103203450006d0000707644124602c0341610801121000281e0030301083c85c101020410404a5451030b801d103000e004407030340002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 13234503 1250 13233253 13233263
    0x1d041a01030f1b03060f050a0506070b0c120411010806030d081506040302040908040503060106030204080c040903120501030b0912160b18060c070201090816031b080a0516080609030d09 81
    0x101d83c100c003240004081d480d9000907480000c1d4035402c000316802c07003031591f402842c042c031280c11043c01581c0d03030746c4161100c9030750241041c1907a0b030b00c0303040486460107000404860031456600380010028000081001c243d0203903503040190341c8240c1010b82d142c0d600700811000c1a90a0003144000c0c15142d0380b00c08902e0301805061030542d07030340d012030101e9103051300c1074500800100d000e001c28074050101d90300501c801c1c9025810079003005401601c1d410103180300c034800c5980ea91010200b60060761224000115002c0400c195a0344c1d0901001481c0d0803030f04920075003d04c4031640388000d41941500c4801c04c4200c101501030b941daa86145a030800504102031130360042c0f0305141c00302c400304010b501ca541d8518065865452501c0054070b00070a0303422490342c07500300102171040c200071000c0d058122500a4a000c00c01c0e902c16141c082d0200050700444028043c05a84d070052100000d5841d00740c0d02016400d2240c00e943d9a42c0c16140d4105a4681500d900200320f10080c0c1405600049480c078014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 13235753 1250 13234503 13234511
    0x6031f0c0203070803090703060612080d02090f1003050103030201050105011805090417030103030e100801060e09071b0506040b090102040e0703020310050d0f03020708060709060518030106061d041a01030f 90
    0x10344410b007098108844010b119400176105108210781070080360018242041d2540bc03041980d9224800c5000d28650306108683c08103683d009641d1b040a00c820089003d0048080240c6011009000e8003090105070055820319000041951065052400c201076400e48641d6440c2890b0421888007070260054034105807145004a20480d400300950080d44281c0306c0d04502103100c410b003c40e507502c4035564400e0200c000c004000f900d0700a81c5184800d40b0807241590265203035034041e6500021040400c00d043d007070500b00f42c100300700092110b000d00d0048950070200e43e1074140c0c407420b0340b08074014603084445820110796568043d07000b851f04055003038000f001083c0c0380c0d03004c1010030034030010560302103180781b46443c02d1680610503c0041d14201018101600c0e00c2d410280004d4583d00c1070604021000034200540c043c1d03032024000c0b18030028001d000199039000300820865860401e00300440c4085a2854185000d01c100d801d4022000c0464a907400317032000540c0144440d0038088030030b40c0c907 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 13237003 1250 13235753 13235767
    0x105160213020f0304030306060c020612041401050106020c0109140105070803070c050102030a020301030b0907080c010c021203030a0207050f030a09060c061b050a1b0503070204150b070507030b06031f0c0203 91
    0xd9002030f00465207020900f94980c9001c0c00c00400307035000d943c018000e02c00300c070002d0b40150321031004071a06410008074150480e115850b20b608600b41c16180002554601341c00400c009601081b4602c5d1154244d80b081030312900c603004072441d94508000e03207000c41d20402c9170f01d0014210b5030186134043e943d030800c444200c0d496201c2c1802e9034001c407503480708158000014010030144041941d0030030800c8c001000d003075042c901081d42e5841011071007810300490403141411981d49541f40418501100140c0361a4181017054034060b410401d030480d0766004520b4080013562000041e200c09440700d54428843d00d06d000b0b41650381406524040d00c400ea00c5503641007490040c1400c180e04204940d640c2503503a07041c51001450301400354012080401000c4060022030400025105007a804a8001a080d03110300240d0390180303d1076102c4403200c1d0300802c404050200206494040701d00030300e90313841c0c5555018205030311035031050f0010f0803241203484082601451540504c45820413801280d1070320360 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 13238253 1250 13237003 13237039
    0xa0b040e090a0507080d0f0507020a0e1902120106080106021c031508060708011809032304050901030f05060a0b01080a090212250b0703050a05031b030106110111030601051602 77
    0x784e03a411011081e40080384010318540d01422082941e0224900181003240550018540544034881d0345490154080803503000000302041005400d4081c1e400c654540c0d2841b82c1c904003400c00d00ca1240804e0349040006a20390001c030340c0da0442c00c05031028140041c10500260024101ea80250a0540113640041480442084103d0183c4890f1302d95405a40c50404801c10006c500023001100c1420581d0060000b600031040a0300b07100303406a406591494000c81c1310003030040d907102e1940240c40300d00010500000500c04601d09001d4410b45850796610220002a03400710b00703006000801110000701a02e88076404021075070710041c0702502c0e03d03c0010b9200e02c1d181d20f101849a141e2000c00000c000d2580300c8040300010440200ca2034100080350314064110700909811400784440000000c80e15108100d0410039802e00b51100f61712942c60313460040c900400003001558130340c600f04002d10091240e0040d80c0c8160b03016540e46240012285000c2106c00b05d00008a03000030750440c20007421a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 13239503 1250 13238253 13238263
    0x25030609050c040c0f090e0c070b190e0604021f0903051608150601050717040806010b0d0b010e100c030e03010207050a03180608010308070201020f10020d06050a0b040e090a05 77
    0x81c0144000c041410740c4070104011500340c0f14000b020b001c080c0804c40356064000811310200c072081107181c841070b9112503c60180d8400c41c14010001c40320001003200e0001820324561107880190b40c10807154030140071041c3d45110558001c3c0d0b000b08610341d0307054012090352800e42001c5407450300d016147d940e99201803502c0e42924800c0c80041402c0018000b50508220354a410031104880700903a051410000c0d10500c18010081d18040d600e0107031820030400002241c00a10380ca0040307038400d680d00c107281011904140843d100300c0d403c3c098585c03180e620801d403440808000130308400f42c90b80d00043c161031031142c20f40308070180501e200c0600e0b201c1da0300b88040d01d00107010b48050b0134007808030b14004142e010740d0481660390074040300b0240071803988940385e2415a44d00c515660794900c12800181e00d0401c9440c04001144141c00626040c4032054010b0205401e4441d0140a580c1d03e0300c080010818442c001c26513048000d000c1008030014014036503400042c04d90030b45501d6606911014149 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 13240753 1250 13239503 13239521
    0x170103030e10080408030f04020a080a050102030103020f0409020102100f0b0307030507030203061e04030e040b091003020a0803040e0c1803060906070f0c05150405030409020c060a0b03010b03250306 87
    0x208019451000c201d08010b09400302e144110328280e291440d050762012400e000c003924032142240b10000180864030745030107420107011002e04a8001140743d01d00b0501030b43c424003080740601d030100803014903804c0c24041e01c00030030b60503000760140203200300080006004110215140d40d03101c08480101e41c4051040d00042c50040b00581661800c500515152801c0600100c840c00c03400c1c118041c01400004403550003581c103140c8405641d08080005000d40b1440c40300c1c42e44001008240071580040050031001c503813080d10a00070683e61100c038940c582c0220310034400180005c100040d00d4102c607000403c0104045a0281010300000c40440e1900004a501104a070300c910103002d00d26070061184c0298809624003514500d100341d84a07a211404240f040209400c0f04010404000040c0151000340c01045003c5460301c00c082c0714650366403004d4408a81d001d180844000c134a050600661041c010301400414482c010042d8041080d80c1907000c2480c2e640007410003000042da28001c44a403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 13242003 1250 13240753 13240757
    0x801050906090d08150303040e0c0c1507091205160b030f060307031101032a0306050a051c08070c08060708011d01030203070603020a0302160c0806100503070b0a17010303 75
    0x105103014a80180340c890090030341c5401e640114030003805164494001c9510104009001400d51403002c0400d256019641203c0b801c0d0180000300103010311144068454800c0d644110740d07845a8000c0744403140a02a00c80e40002074610b2414420040c0c12120120110b100341e04803618124050141d00b070032420341d001000001400000d0190440c42101d00d541c01500403009485614915654081522a079a5801d414152140c40c90010781c40107203442c8103088404d40580d0000b1000c200018000d00309030003002c2c4038014071f08001ca0300d4280b440c101c82c2c040c01800c00000042180f5101c0d0f20380758220303a00c111502d107021080450280d03028001300c1d0080300303242c550f8a0554180000c8514013a00c9640d00310007a5a50f0b001003001d65000101c0100303c4215080059039203081d03070803c90107403141d1911804481c4a04200c0b00800024025400c02c4807140c01c1030300c202d511214200c802e1400c0522640768135a0041c68240b080700390300c00c020602c645050070140960000030b103070302030040d400340e1040c1c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 13243253 1250 13242003 13242011
    0x408030c0106031401050c0901080601030f0606020f010f020c03160813030f0b0606070222060302090c0403050d14090603071b120e01050a09120201050c1b0103060506120a0b040b06040801 82
    0x400c1200d020496600c031003c13000288010b24164407014024040c200e0500d04220101000c2040359003e0350004001c0300d103a600900030b031600e401c0060350313800409050050341d6182145080501c02c1920985003000000c4001d507140070f184000007090002d86100540301d500c410048494500b000c107040c00d0046210300807041c00c00c0d4603801d0600c40e01c14014034590042804204900060340d580f081e00340c4503a0845c1e800100c5800315105180100902d406c005d40041c505814024916604400b030300803070f80b103a41203401d02881c402080341c07100b0701021103003404c0009129005491030400b015651020f41481d2200801e5407603c1c20040c03117403100c0c5085d40c10300d4140100c8139403141d0141c0b40d062500002c0c01c01510700010080000c01c800060711030380402c420404072344021a0b110b10304407042c040342501107031664040c414134032aa8001c20301e0b00d680800d1609200181a040480a403007100c81000343c0e0080543c0d9034a0150080c00d00807224682c095074603103503400203564460241000c0c1c210640009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 13244503 1250 13243253 13243259
    0x806010e1b0703020618100c02010e01051305071208090409120f030c0905040905010e120406020705010e0d080c010608031c0f050c03040210052104050c0a08030315060408030c0106 79
    0x1080344400d18501d15094a4100a8840820340005401c0d8011500510340e02c480b426210302c139828459088a0b04990909100c0d003040c25944c150092294101c020000b00401d071200000c8141c4400c0c3c0030001840c0c0d40100004110f0585045510721a860140d02c2c510b250116a800141c11100f07465000c850000310b421284903800c0c0d01c40340141e4484c0c01070504110808001c040a08070349441c4c4601c5100e9600e1301400c00810070b00307402c03003074100840904440f8010080300016010b07400c9401144010300c50074500150543c1f1035500011008400307080c0a94106540d25803004035031216074806420341d2115000078049404000a04e001e200c0c105114401c1e49152039007805aa0a000d40148140d08240a00c165106444100c90308164110789042c030400b18084140c840380a0303d8241c440038590034101c0910403404080d0544144c2c81041610034211481b8100709e0414401d000d1040d40703620a20019018403072000c0c100e0176000008025604084d901d89a09156500603140030300309944443e020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 13245753 1250 13244503 13244521
    0x110601270b0916020a050304090207051203011203050a0e03060c0301090c030203100504090f0812070f0f0e090903070602030405010e06070f120203040303020403052b090e04120201060806010e 84
    0x3a8264000201403215445040008003402ca01402035043c9810600304003006500030814030800d107a000d010340f52aa0794400070400290441181699140102038280e40f0501e0008102d03816a101030038017500021a60301d08590781d030080c03401303002480207084080030aa5010080d251240344100c0f103842e5a581881101c00c01d81d00310b2812041414014024050707078003064008441a02c0c010f807030026040010b400d104c1d07418880144083d020040000c0d41c0b100c0881000c64003442080d46403625408480e946408445000418103c1e00004005840e85560f070f20384211b51035005480c0d0390490741000d0300c544540e0100d910983d02114a07030b64503041003003040401d20030f183d48034085d030500852520070440007030701c0740c0202c8912260b101c2d40080003500b05800fa0341a280596045012140e0480c0e00c015840468880c03002503441d00c5070700502000c2d64510503107200c0140c91003082e6141c0c103a212592020400d900301c06000e0700b0b55482d1107021640c1c2c0000c104581c0201a034a50036900c6051500c08 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 13247003 1250 13245753 13245809
    0x102030a05091009020a090c1709030d05070c02060904050901020405060d020405040e0c030601090b0a03080a03050a060b13050105030a09060c080f090304030809060d0b0303040801140903030708010b0a110601 91
    0x482d03641d03810a04e0b0782015a540f40142000c50302e4002010410002e00329084444492032180c44c1c07245900c0a052080f4104000080c0529010fa008200702039140c03100300b43c1e92130101d400025401201040320072654280b94018507040310091002504142e00c0e90002002a00402c0c02016101da02280c10095132619000d200c1100000d04060700a4246030008603841c1c0c2c105014280c1030306e44035003440b28540c0310380700e02400a43e0400b510f503441e441c5101d4000d018007c02d1702d503824207500742100130400c02c11780c034100c5c0e000081d10340d41d65110518003001500d65800003030440803207903a038030b44440204000780507221810341540e44000c802c0c50710010740059840064800909a402880180005903441086030340303040c0101c90064071100c0b40c000302c80103410581b00740e5804d800f02140003c0d894505400c400e900300030f0b0343d0303d800e001d994038030001d035990100325140c000040ca2030b401000070402c07407001480062380750b00c2e009000300b040786d10591030310b81c0030380c0b100f000064514819055007100700c031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 13248253 1250 13247003 13247023
    0xa12031404020607050c0406060c0501060b04060203070308150a0902030109050709060e010f090e04050a02030601080f0601050d0f06060609060f020109050d0f051207020a1202060f0402060d020706050c04051002030a050414040209030102030a0509 107
    0x3b1150f8141801c01a0080d13a900418100030203004800e004220f0002c01c0c5008001d50750740050020541c1038652950402a400a00c42d10040703508000c0841c1220b4040d00d40303e01540ca65a80c0c001c46554000011031354002c00c144684140061454041821000400c509200390b0080c4010f0800005601c140f40c50300030705a11400301a0440c01c4585109000030403201e0450304100c0c1d0014440c03100d42400d1b40401081c48009002c1441e104c400103400e600f00301c1c603004442081d251039034034202c8103400b43e003a1104a2002440c2d40c0041c403120b0303a0117004104000449040c1d00d00b181c1012200244040302520a64031000582c0c06650a4410804010540301c00d1703100500c080d003824100002592906075014100a206c2e010100d03800b410050281e060f112400d030030103420300607400c261590902590003401040e01503641420780010207800001250303507600055485501c0c0c28940780000303092102840145a001747c00b0046c201e1181c0e00bd001540c0501985600010142401c0e0416403a11a80c02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 13249503 1250 13248253 13248269
    0x180d140f07060c0809040e1006030201030501080a080f18100203030f1e06010e01020c03070306061403010c1202090301060e0405010222261507020a12031404020607050c0406060c050106 81
    0x1001c140412503002c1c080100d031076441103449866000c0702002038080c0a010030240300034450b8008050101200c0d41049085074000e0720100300030b989074034a080d190000350201600b60001001303400c0c100700d0400d008010070700c1529021014400c03000c00081e081e006032010b2100580c00401480006090704200310340100084954204209400385020103920000713048505010f264003c0d003000e64020b01000102090040554141c180c5901d4010000c154600800810000002d1030a00c141014441da840c0076519455501c0ba15054400c0c1d50301951100203d181c02d9502e40e940081c8160070030313000c940150710070340002d42ca94100c03c500c0301d2407140b030500304c01808160180420038003d0007400110b90040c4200140941c603203102809140c020b40c5822800340503001020007641d16804101041068840c0c007540d000341541d40011000e649031010090102c1260700041001850074000400c040303407052041c0e4000200c1c410000b000c840c810791007400407600c2403420004205080c0b0445014100c0c0c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 13250753 1250 13249503 13249513
    0x509040f0303020703021f1d030a02060621100c020d0c0b13020a0b07080703020d020102122e060f0f020f070302060c031303030f09090b030d05180d140f 67
    0x151150303a0048142032018081c03681c0003840d401814800d1100790071214040080c00c4a01c040aa0104e00070000c2ea880060307400081b220107445041e012040b41c015082075070090030151940c508214104c010304001070f2220041d04180c64082d5824042c103092a004c0510000c0d052000d034038080d003810010491039040108080445002074107021440c1d411400c0716004180c2c44d501403003c2021468150444035685001080c50700802070041d0080075003601c668291100c09504107000d80c2030740102d0101441002055000429480715003040181039000c220000104449082060700014142d820401c00540000741c1281e030301d500201a4140054603100500f01d0641c0d1420054850141d800028824800040c117041040b4041041c0c4503101d4044480c048241e5607032030040c20b1144950701305000f08400c11800101d0019030b2241d03015060000c3c020f814940249c02048072580d10078100b00d800b4900c0b040c40d6030b441c0c0c4c80e41c5000380c4000e84101502031403202c50245107450803c5c895a881016806 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 13252003 1250 13250753 13250761
    0x30f06190603020a030603150b0307060c0c03020f04020919050132030402010e0a06080708010e0403020303060f01031803020a20060a030c0201020702040c08040209060f0315060409050a080406090509 87
    0xc804080811a2424603006840c0d085800d003c5001d84000e80c406000640041160180903c0c55804098440000c47c211317001c41d9070742d00082c3c500381d10707410000c1e0920131040d50800241c1005400100d000100a1005241040100c00250508445004031107a0031030041c040c010b550300004482c007201002805070700c043d10100c1c01d102416142e06440001003501101013000c5900030203910398408001444800b07640c0e21480d004000d41c40840300d040002c1c540e040002048040055442e0241e501075014624541e07521041c0008401112041410141c3d5800350420090004147ca03c0c1540700c3d80c00b41101c09403500300007441120803001400c8401000910302619601d00d401c0b41c0803038107281008030784010510b805900a0064820113500b050400d20028042644510554802d605c02c50305000c03039485210a010040d82c0142809825038440b82c2541480604450782c250711100007040454501da503507480b1401d000b081c0104030750141002c102880150340000141002c0c1c20b043e40c0c41851898 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 13253253 1250 13252003 13252039
    0x6021605011404090203040305030f01150c080702010c14031804020901091203020307060f050a0e0111030604090503040f14130506010504060804150504050f07080c0a03120c0512030f06 81
    0x48148181414407207205101d255481940041e98024034808004640320701d002c0c14041c003180e00071550f544a10900b880041101c0303a080d140030064800f15507564000c00c0242c0e0b0f0341c04c0c10358440c5400341d050201d031080c40f80018441800c210400d901c2c2c038000d10303100c950380c1d5001d000c4950003e500512860040c0301c90200e60b6030101d0044100c0344410080606060182000d03419442100000b901490074828403618040054100900403004071b0810050500c01c0040780c3c0c200c50510008014102040011414910781500440d00c02030040d415603140c10355030300e148840c60080b60320448034518001040240c900d0301400138040494040d0040c0958a00074000030018031032806141c0610944101080c140095090101c0400b954044100300034185801d166a8505ca03641007015948114200400c422a011504011009002c0d1041c0300041c219561481c54503070303000c0300d8401c110003d0032580c0429010130226802060300d031407003552801d10b4a402152128010801c9004485644100d09191 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 13254503 1250 13253253 13253293
    0x9060509060402090d060e011413150b010909140708010b030103030c0b0406020705010903080a0e030c07090207020103090512040302030106150516031404030303060806010e0601020304060309080d0f0b0306010602 93
    0x1c00071240180d41e101e11100003141d00c819114054440b031315003910300f1007210f015404281c0e640d08594001c042c03595607180a02c0b100710700c1c0302c00902304400701c030807041c203060683c0010840203014100840b000d5144e8450310200d500340ca60701c074504035022091240e610b810901860151000ca003c0074659030650320f010b450803200c0781d8000c0c0211034010025060001681c1a662541d030300c80300920840c0e0071130400806811082d030358900940d00e0075a400c0068040042114110002280504007081c64000790400941101c54280d05141e00c07000b002d00014818043e11355604140c040c4a912142140189400c49030320350000b0050501080b00b441c0e6081e081740030384074040380301088010303140729602d400c40d103240842d800c4050b2030101103004000c00d40c150704041c05982ca01c40031111941e98650050303c0035a8266645400b5810810003403003050b200c0e401250307100c0d000d4800d003894400b20001060854164240803020760741e0714941e403d62450305001e070a004118901c01000a6210303031182072084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 13255753 1250 13254503 13254511
    0x5070303080a090804080105090606040b010c020105030604060308041e060c0b180a02030609150f070f080702010b030307060b010e010807120b12060406091e0c0e0c09040c05040501020709060509 85
    0x100281c0400034a10030010b07000200b405038000100303a2070340d81d1501c050b0b01a0800f174590025900817440090554180740c80340070000181691031202d49035640d0010340d855803010303120a03000342d102c060200209030300f40020b10040018911145c550760090030300d1601c2000a400010804c90b191b80514007251a504480da001286050b18802e1030f00e01c00c1d400c51400402040081d014042c100800c002c610740401d10410850742c064901080e661a60620f4000350360440390800800d00c5429000c200c50b12804c1c807550308c01c88a0000059490540e0700003413560b01f02190449155440d058100383d00c0d60300c41c11a064040080c2410051070501c002c001d03001c0b803800300411b138556590b40808482682d500c2002c80c615207501d8180e80d55400c180c203024020b4180740300d060700d0f4600405e01407541251845042c0c45800e4201c07510740b0145007002000c1602800c06422008948810b0000803130344c0e03880c1d00c00d03c3d5030030100ba20340721395480c40e0000282c1005034a5000c1c0308880d01d8400b00b0072036612060391071980 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 13257003 1250 13255753 13255757
    0x90d03020a0c02091609090605060409020a09120803160519111227030a03080c0304020d2f010f0c12051e0306010e0f1827060a05010b0705070303 64
    0x301c51920030120750002c039a00000e5401188103080c001100c1606a01c01c14204440d0366217812a91260900f0040d200180320386038200b0010481048503a00b550b016209a01d22440c0c1040e5803503a65010034030012075400c06a41e8034400205200c1090000003c03460141124105181800031404141d1958809092440309110b066402d0380c40800c0244100036401c00702c0f0a02c00c1c0c503141020052000c00b003105c0c500180d11a508aa807014a24001039441c05003941a0345560055031420100c1c162a00013410883c0c0000b2440a046d0000f450002c1c1d0004551140754021907014880c000c4018155038000984d0521410904000c84035601c4001d4003c010340150081e401080448403c840c10b00c00d091b40c0440c0100c41000209891070840b00540c01401c003684ca5040c055031802c200180c031000f02241590280d0446403844601c0380000d2402e80c425034560144c0c5800d141741a0a82c045400f0065900c4950011020412030940c00e204840c09020641c0c1064140b0645030f803810b540700310034000a81 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 13258253 1250 13257003 13257007
    0x6090c0d02090f090f071205010c03090b041103011e0c0905191205030c06130302010b0303040f031b05061605010e0c09041502041e030201170603100902010512040b070f0206090d0302 80
    0x100d00010008000003104107004c50303c60554131b641c82d480d114480c100441d50b6500745800a03940c2b522078041e804c0710a4001c800000603444991f00e042014050500e940e815540711344024130f00c02000e0158441d140b404200100d400055030000800e200243e8102c0380c031501c0400c0f0140c00301d070141c00541e001c0d1200241500001551410024070758041c82d050800e0505c9944104010510480035000c0c01c0d0b4820380003800342d18a41410180c0340d000301d0107000c00241086008002083e0030207002520900c2070341da0380e0103260300d82c0302088031540711a0140321120401080d0340d00b040b10034401c01100d2000e50010380310803980d0300c1c0054032503d0003401c00340c550480166120f00c3d07014030303604541c000c003030702c410441209141440140341036007035200a07030111380b045d61503450448040c0381e40c1e0311603c0001d02410340303003140286010080041c0303941681045418003190303202c440d01862542c0070b01d004102c0c42c0901e117080356005041410b10440c072400c54008000307006031400000f4003291124003a040c09a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 13259503 1250 13258253 13258261
    0xa050702060606070804090c020a03140f03071413030c0f08060402060d020c07081f0b040504020102070b0c0c060c0105090106060f1e0c050307060f0b040b010203030105090402041b0206090c0d02090f 87
    0xc0101c5c0110340201c100949090800c9048d2a0000380c03c00700c1c01d209445807910081140721203e00c9000b004101c1e41c04440070000240118882c102183e400142c0d0705010b400d01d800d20308400c403404030701d800845101c50624014080e10a00c062248010000d03400149075924190b804070720305008030740e1a041043e4002c80c040402c410144020b0000d05402400c17034120440650310700e012241c03162440c2c1503441c900b00702c0305414103050080511568060300200021842d1552040c83c2e58480b803500100b60146071a0000c150740e4510044c01d010705200700106031400d00c01c1266003110960380c0001c0a00401d103140d0030146401c100b6040c05804240080c80d050101d45406807860040940000c1c840c1c0000102c2004010f013540c070411244001c4902001501d001400b484100d034140d04840d0b001d80d209100400c81c91804006030340e1700510152001c02e174211202c14103c04581e900c2c1c1c9c0340300560401401c104088030104000403603900106d905c4007101c403107900865000380000c1c200990385201d480000e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 13260753 1250 13259503 13259513
    0x2110060b0c070b1312060b010e010e09190f06030303020408070905040c090902040f020a020d0207060504081005060303070c03080403110604030f0b09010b03160503060612030f03130c06030b04050a05070206060607 93
    0x240014061041720302c10810741072410500030402441c04601088401c01200000d5100d000082094030b8040d207080300d56140c40c0c045494485801c0c06086511b9280c4034030308000c1505024004c02180300352800740e01c860814018900b0003400d03070401403030039240004000c0850312601c0c1040480342030301000200c05441d07001080c042e08803007034187c0100b40001080a6001e600084019040d50300741d0076180e21540b00d079001c881c51311072446146010ba203e10070b26010a00503a11040c2c10900050840c0d02e0119a0b50300c0c140400e565500507210300401007800c00a11000c0254082405000ca9085107494195900c00114800f001c0010700380c5999080021a101e4096006190924005080ba4140070f041c44031684005010b00800380a0300402c0041000e600b015201d000e2903103003d80c0607504040030400c00e5442504010540b480c448076000c00c01011070801c03007540f0043d00f0f40f40c0c0c0119030209501c06020a844015120041540c600001c0001c015400300d8450780003001150710f150781d41d04600f00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 13262003 1250 13260753 13260787
    0x307020310020c0a120903022e0801050907030c020c03060705030103050d0e0112020315040905070f08010e06040609170408010c080717061009080f0a021206040b060d022110060b0c070b 81
    0x4001e41000304185902e0b00d0401a40645424807489d1100100790b44203c0421240c01a080c0700c1d140e000031015000c500c519000303400c281031300301c50b41c030413180c0c0b042406000030b15107501618213602080c1c00000500c107111046c0108541a036040c01c100c00e9000d0360100080041180c8060140c0c07266011000c10380c050103801c0d01c102980c0000f08203102d5070245080181c0c4170300c0c451207540d510044054000400480601070364006110340d0010b00810303a203989500026111505045030706214040f0001c401010702e4018001902e1202d000140422010f207003c2c104020142c021010300c01d07a00c01900840da4820081303544440113031604105844850003d80308000180c00c54101e07805055490011034a0009440909a000f10307540002d0342900451103495100a03913020b0f02c9140d11070009061820410608465144050b004a40d0300d441c1168006440009140c05400c2e6042000807013031a11050181c4001341401520b4240782000d041c50082d074600d410310401102c254080b551660044e0ba1003c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 13263253 1250 13262003 13262009
    0x803032809030e030105070c0206071106370c0f060c02010216030315060804020904080304020d060501030f170c0304060c0c03021005040f14010503060609210307020310020c0a1209 79
    0x1800001c07854036001d001c8240301401e43d80203600e0400003800e100d00c2220003c0560303401802042c13914040ea150103540748400703050142c010004024a089104c03588d80c07400d0b580315029442c007103403600f6101040180520211440200891402d00d14007040d001c5084500582d80142e0005041d0010001640a8000d2429000e5074103034440c020800c4c503805402602101040c0d440440310244c0b41c89007a260100c0954010707401520800010b800a080b0034006c541203400140001c01001035a074402c419500c09800450300d00d080c20410a080000e00e4031540506c280741d000913401c02003080c4e070440e0ba034040d520030403040202c5900c0c50000d008805107184040c41d00508000e080c01501107000d840b0340c1c0030b0300c2030760828180148001181507004200414800d81690f03020f103035440c1c007000c0144c240c00080301715030710441c1d0480e0400c4010402501400c103440c00c6002d551103400c030303004040c1058002040c03202840d00402400c8032a02021480100d6142c0c800b40ba2651005030703010469a0074440c1d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 13264503 1250 13263253 13263331
    0x60301080f0609010203010f0b070501020f04090606020c040902030303060d030c02040903030507110309010e04050a0b12010b040e0604050703020d0512030106050d18020f1201020f0415030b0a080303 87
    0x214403484042a000d610403800d80841d0515116907050a080384000d01c14400c0316510487c05121800c440d800030070701e1a00410026041504c20740d41881c1c0c07075005034402920640e986200b008181c6c2c042c003c851041c44101c0b81080758411580100740c4030300c002014541300c6c00311084101d00b01805001c01c40c00598002d4410844000c40d07190140041c0429034040001c078005400c801110400081103c0346000103941d0140c0d1459404180405130101500f1699110b84440107040c1c80e46910190340360240f1404000b20f9404100ca090004580e138078800e07000b403a00440e0801011500c00a0303694112a030650f01540749000c1c90415078184648013a4010301c0200c00800050806d034040050180c0c24460b000c00c11502e03044080c1c04c2080a2500e070f00035000040002c3c080b4203490800c044075540d281d2100054604007500c001050710703a00070303046000302000c41c101a007060365251255031009517081d90b5401c560b83c2084803c60341c030702000346a0181c4030310a5060805c034041c41504208524004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 13265753 1250 13264503 13264507
    0x15010b1b01021605060105060703090902030601050408010e0601060e04060b0306130e0a140c040203160315050607150e07030c17070302090f09010f0b0a050411070506040f050c0f0f06030709030206 86
    0x640083c00100080300090301d15200f2803002052600d0014120384a066168440403649458401c1e580041d4100070500790522105210009131000c0c20b000304001d454070740d80074244541c10324030702030f1803a0381400484d4002c1e480c001080c48460aa401103980194048818a40c1000054904c2000e05000d00a44609009481494082000d10f4030190400741c0b0800665004200540500049020885445c0c1d941e030105020004514000d900c00082c4030001d4801140384c0d910b54010510300c2d8454002101c2c04070600001c2040710382c00b84030710314001101502400b4198615140d151440f045070044d16070110304c0c600381411b0708408000060007964050805c3c402071615800701d80746040304480350001e65080030070742c1300304284901c580c03089408000d00358034000342484240001041500c1500030001c50400040c1d0104d00d04005040c40740e8030403440c184d0003048034901030f0f08000d1061080f501480030b034000d5410300e5440d40148e010585090340da00781c40c2c0e40c903030104980f54146d40c1d001030741007180 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 13267003 1250 13265753 13265767
    0x7030503090109062f070b0619170709050c0f03071209021009050102010b010f09060e01020109080d060302011706100e041b0206100f0e06040504080d0c03020405010305070215010b1b0102 82
    0x5c4440d804a020700501800c512003010f15496080501c11440000c10b010a40702c0001e000d4941500c0c1034025091444216a41540b40c0c403211100780000000c0d20310301e5101c100104038282040c0180c40d8040b485a84031070412003a0743c0b03841c5c12400043c04840c14407403082c1046407030000070b620420f8480c2d00104150203002460300060440768050203014015428841c0c010302550060748142c1004280703556040d945803401104803903901c461b030031250455403101108000300348903001400c0b010000d10320000d4103030718500c00944074121030712440104040e4101080740507550542101c581072100d0501960300513030340700020020140c0c1120907104100311024205a29800640c651240382e0304824403441c1034549005510000851080e844010000c4000800d14180380e0032058015102d00f040324241036006440d00c041c1c0740d079050480300207030380442c0800456a00d4000d6540210701d50020b00b2440c0b07900490420012014012000b01031400560040090305841c20b200e031030400c8030700131034071391b11 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 13268253 1250 13267003 13267031
    0x918190b0a0b0325090f0905070302040b01020f0a1a0105010809031215030d170a0902060306060a030912050304061b0507020409050c10090305010501060f08070c030e0a030501090b0a020f0703050309010906 90
    0x3c444c0102841e07141b40c58030604d150341080c412a540c840c1c0200051001c103145a003000054088984e02a0460082e1000444e10349420000210858810100310b01460002e10000d1500101607201604001440081c0301c044400403044a403031030184864416155901020000f00d840c9007400300e5007500c00e04010340c12099201c043c00d40340071100c000e082803a40711541c01c5000d0fa000301c07002079030021041001c160700d4500440205900c01a5040c00f2800e90300c540c440c3e0172480c54022040000c80d200004110030001ea512402800c5c00701008128058200c015000300140102c40000380107540d038101850500c1420006c0b201140320050800e60010580d02c0010041410340c40120350369800c08001090060240d00c03600103d02c85a59000705541e5400340440748100d03000c1c420b80c103018840200b12003a4540c90030b040c015500400c00454642004d180c0981b400301c004007100703155071050103902840840038085401040d01454242e40300d89a0702c800600400c50204000c0000e8507001241c04108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 13269503 1250 13268253 13268323
    0x80403050105241005090411030708150607030c0f0609140304030606080601060806091e0c070308060a030201020607050711120a1202010501180f0b0918190b0a0b03 72
    0x1290240d07014150300c0000d1407039982003103410f4a4640c060700907120080340c540300380081c140301c0f4002000400da408a07410213015072390080d1074850001d6030040400c80204410449a40c11003000e640292030072a02c0e8600818481c0000d078010f01c080d10180c00c040501601c3d410101040d6001003003080c2c80d8034043e4816603240d00c988002c8038210309003100020026000b1912a04841003929074171420340d151010005080c0c00142814510314080190540324a00909a144036019440040e0b0b43c2d04c800b410040c1c40a070b030052150b4070460340e0000510045c2d902141140e04600d0074100365449054900c0e000013000c1c803080e1490f40104101d0181c400381d040014041041074000c12421501e4146420100d00341c0d00d090140c01002030b80c91404843e42483e031303440081c006075019000140c0484200c00075000040984080001c14a452031441d101802800269500c140c100c2550032031001d81e0351214260701004100e1217280c1d5583e58604003a8074240000041e080007120600d0110181c0c140e0342d00c5030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 13270753 1250 13269503 13269511
    0x9081e1207050c0901091a090c0909040201050403061506030608060915070e0d05070303030c050307050403170409020304030c020a0501020a0302060f06030a050304060201140a0501050102100e030409090602040311090c040e060607080403050105 106
    0x15003038000847ea41042c07080a8010070144203002d29155284081c00122180076100f00c0c1000704c200030000204149101e1b40e0181041740b815080210305d8034000800751655a000520076030444414803003500740005500440001c006d1050146076a0141c040d2900f28409542640140410708082c081180c085162000d0703c1c82510100301e0070781401e90840c0d0310b000807240d07000825020402480415a094110701d6283e2007040c01c1d629203900d40340c2035001c0e03030810b90303048000c220703d50040011890283c081901600d820320060401c0d04640c2c8000303544050103080d6140d6101030740041041a1818020315074415001012603a5881d981c01c4020300030400034054400503008080443d1603900036008042c126241603008001607026402d0082c02450400500400e601c001c1000003004102401110b100c0342c02003000584075450350501c81c00c6560349201c40e5210340460810081010002020765050342d44103440104070f03030784040100e1203610503800081c0c181180818004104901500078030701c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 13272003 1250 13270753 13270781
    0x1713031506060801061101021b0c0102010b010806030a06150306180515010605030705030a060f12020310050f010b070501020f0706050105040b030d120f0605040c09081e1207050c090109 81
    0x40c0c041a600000111400c0c1c0c002c1c0b100143c442001000301e40e2242c00c3e40452840b01c44001071a10100790320701410b1107180d1084107165009003002038050f40e02807142401d104d00a0a1040c00c51401170300103610f41841c844010082c03555040f00440d10020194000f026644c400300401c00180100341c22401c881e19240111903d210349102c0202c12285c0f22006412200c00d510341e28155224030005407541d400082441031003d80c0c642c0300183c071800104d4088001c203002603907015281820300616042c5006801c949d01800d0414041c4600e03016030000d040e045a042099880e1103040500e40303640607124550040c80e20040200340a01802002d80c402030484a088600700032100c6001d0034503850302140344408002c52140700c0d03010b0241942d41c1040c003240c251100002000c540355030004007200c40b4401a80005585110b00344040740b0b08010f0400c1d40b900d184500705a038210304078455681e800c89280e4040403100030030050200142007003410792403080204505201d6845500140081010010704d000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 13273253 1250 13272003 13272023
    0x60812030f1b0301090b06070c0308030709060201050108070501050a020f0a06020306090601020c0102100213050a081c1409041e02120402100c08030a05040f0807050c24070f171303 79
    0x1500741001c00740703502080810840358110785c0f03410303000b00c024461442010341042080141000180c002c7c1e1041001d184a2903031182c490800d020006c01048064201c0c009680c503120040c01600d80000d80ca6041fa030017481d16030344d07586102c1c4080341807104a034440703030481c480da03954101003001c11b07005140310303190540d40511640d8900c1c004a982d01c4850301d045016030400c43d20030fa50f164103034005001c03d8880900b0620226a85c0b00403d0b10402d0907807140034180c004980c40c8244107159100c0f00e400b80098a080750044101240e0810680701c2c0400c0c40b40b145075035107105001c2a001c182c8000129001000171911054141000c2d2141d43d41281e0881c8140000f04400d03007242d005407009600700d5044184035045546000d4600c009150180043d40c07604409e07042d080003d02100020204544070350090803203841e03036409101c4d80418110880303103d5850003510b0407010a0700760030b646225403c0507404412003d14103000e40d4201c14903850004085c8001240e981e030001030b0401004582c892600c02d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 13274503 1250 13273253 13273261
    0x60207081203071b060e030a170f0601080112031b080d0c0302030c0702090c04050d03021018020d060203060406030606090902010e0604150818030403060902030609010501060e0112060812030f 84
    0x100c0180300c219040f0011959070700503c104e0f8a1441e102c891503601c5160006100020000b1480c40c5412452a00d000503c49400000595141040d0350350400380891658407a801d11800203020f24405004030803480125039503040c00c0c14482e281d0304220701c0b521004144081554286031343c2c140d02022103c405d4604110495429078402d01c04c8911070b40466044034185041c4e07a00300121004040c3c0341000d401414000400c65984804540014a110350028481049c0040504051300c154000e90001600054804000f40c0c036654880c1e24443e43c801c000681c2c3c0d944520004000300446e0b007010f02540e140c01d0003c00c090040b9400035518078001d0300e601c0c00d28050101003110034031490085080d4400c114a851a5081c041c20455411443c24580008003846e078050552540e00941e105960054480c0304440070340c00e0601c05140c01022400081c8559814400d000e0200040008254108007154800540281c0f165000b0005401e00105a4000100d54000f220490704181d41951542a00030049 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 13275753 1250 13274503 13274533
    0x30303150506030604090c031712010906060206040b1e0a0606030e030f0405010507030210020304240506010f080601020705030304030c061b0507030201030902060c060f040308060105090a0b0306040608060106020708 94
    0x5802201d400501d02880d5075601300c18031000d08050101100c0300007101d440480012120038018040e84208110329031204041050b15a203110f0607880b540301740346400401d000f40e0360b010864643c425001f2842200c1c544401011807a061040160b00c82605161818004031841a81020088400c1690184141c11702d00d07806980324482e2107181e03040c00d10100020402940514040e080c0d25010b401540e00164150000c2416a8011a0202ca2070640e40340c45000701159682d001c0c802c0a40c2c1442000345150420010f481c403103421844100b404107039400110703243c3c400c0003858090100501038a84455603413030002c0d8280400d000c2c80c000300301143d2015100040088c80600711642040062032018a0750b0015001004103040c16600f005040051200d0601d08224860040741540302c43c80c00ca25250038004c20003880a80b6460420030704124012155480c0301610040e521502d807420340c2c94032500c0000d0006d00855021b20407500800d030000460369008103045040301d004c54140c0c0c581000403445 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 13277003 1250 13275753 13275791
    0x201020d0e01020307120203040e040c0503010507090b030615091503060301060e16050a0309020a1202030601050f150d02070b1614070309060813020603090a02040e010501030305030f090304120c030303 88
    0xa00c82c016841131091a02241089928140e4210b081c01a61303d440c0d15140700d409500000c0303400741d80480c1810001c100c581400d105d03032a401004c42c50001295420a0b02d40310f035a102c0644401c2c0f142180d00f00c11003014203900d003114411b880041000803a0840f02e02d503944550412a05188a546080340002d0708110390b101c01841214070341c2d10810199100c15007518242c20600d031b04010103070340c0c001000c01078032074134003940140440810640b00803100e441014a0514141c00c550300030340450900d0342c0941c84484c04080c105900c3d504080c1c44042c40c240e020020700603640c003d0030100c052000c0c01803c00780c0c010b41c001000000c0c0c3c1d82585031411540341c0c162fa841042c4e00140002c000c0c000807c5121300c00c00c05036400c00388807940c0c01041d030102c0d0005003246c3c0080c1c078044070f035422451a410031440c251080c081000d40b000028847d40d031441d02d001c1d00900008268003410003c030000110300c80c03000d00844000e4a1000c1c3e8120b980801420144107403401c6000480c013003417800b41200c00c04c480c20070b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 13278253 1250 13277003 13277027
    0x40b0d0809061b0312090f0706120c0309020a0902090a09050412030513020307060306050f010c051209010507050601030c0306112b140a05070f0518011404030506130201020d 76
    0x305900e0590000d0038000e03141d0101d004040001582162441088418801000c258901241000050034002d9010341000e8000d0130a200c10342c0203102c1041900d4100c0c04007010030010700800076680c0b07500369055016041c41d0b000254000e90b503500c0428000040e0b805000300c200b05465590650f51518000800c0f1a01614060300d8140c03074000c4105000d20a420090340100c503000d544110041a42c0803d14060345904100f021a490748820310142c03c1885882d11310038002d190542c620610b035150fa0381c0314500510144007901000801034190b9000300115124164400f003103a4507980d40781484240749a06000c2101c60300c1c113100d21022500602d4080c0d41c8401050300e560080c1040020500f00e025280d420003800360b5455403040007185182c0c1c1000303407040d0340d82c40c004070300340c989058005c003444071420140d0140082030008120081d1084002c049503202030070b110210030003d85000c649401036610041041c030070303130040180c0520014001100a80b00317030200c2c3c480a04500064500c82d035200c3d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 13279503 1250 13278253 13278263
    0x3060b0a1409040609020d06090b1b0f09030102040302060d0501030506070503010503100e1002070302010b120105010806010902030702010902041b08010510050f0702040e070321021b0d0606090203070905040b0d 92
    0x707076581e01d40b8501041c20540241c454180001c0d81403165001c02c18903070703401500390b035070035a20003041090146041d03502d58048080d4140c1225400040303400d04542c0a00f080182c00b004012444520984007507040b00c2c065600201501d80f280c51000001e4003801c404d0008440502a05010a0906000314203881c180e0360018080d00e004821120b0135002051141005100383c425410900352503100c1c2d00c01480d115001e540045801d036640005d1100030400410f25201c2caa241c140104410980403540740e0543e24101c2000d039407600c80e4ac5041f4003405500001a42c881d25140d48a000019002c11880710460319403103c442a0f0390301d504100074401e40c900c02002041003040f028003201c0d1560001c103511840144005045031031448414940700ea2034000711140b500400f40550a05144c8242e641002e09074030040803134108104011f0780c600e0300c1c40e02c030f035004a0040852604000c07094001d07030082c0902410464403031610220040802d6507e10445005a150422002c81410100b241c481169040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 13280753 1250 13279503 13279529
    0xb0403020a051903060e0102180d23070306020d020c06130203070603020706020f0a0504050102060c030402030a02010c02180a02180901030f021c05030a05030412020606090609071205010f03060b0a 86
    0x44014840e034a00c0121840610f414414004000655079124070281104080700050300c64144509407410f18440484161152900c5445100000d0013414410110030a684154280d0f4040240007840d03c2c1d00c540004005900208600b22903a0460b4060519021400125183c584424400d4044443d8032040603415403c02c0005101d41030194005105542c45414014a00710102d10000d42d11b4100300d1660700041d4000804000540e1b041184640020801e8042c40c518201580001d039211840040241400441281d03031081d5034179142a114440c00000010860b443c0c426403d60081d806004100014454031140000c0c80c03c2c200c03225030507240d102a002018003140d4003005240e90304a0707480307000300d042c569401e00019000c0c0098020800182c6403241c99052616001445410b1055080c007151312030341c10025191f03070f16044245c016409440e412200d44512000b11009e81c2401107038481d4a0400d0000500070180600c07440072030b4007481040201d000c8685c10410051018801c6451b10094 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 13282003 1250 13280753 13280759
    0x50403141b1917030d0f0506210c0904060f020d05010e070504060215090f030a0210050c1903151205060a0501090e06010605210a090204050708070210090614040510060b0403020a 78
    0x640f0160b10356600030048030304080000c1c22010030781d4020740202100b940c03140b082c0599424002c202c001c4200c0c0c481d240d000f80500c1101550755900c149210540b25801c280081340a000303ea6000f40d03041c00d02e50006540e10719984140002601c001e110702035030201e50100107441301d80b00d10305581c1650090303806000d2402e812a002c054086000e00020560f0041550800e94400308100800040c1880c0e000303003820741000207414045410007090788030a00e1003040314449c108010625440040200d04000407108414101d4101004440d00000b4011a40c62411010f1180015075244140001c0b4824031442e0788904000e41a10143c024000080c0d205000510010307000e0000307840001213151104c5007440c000c03540d46122404c1030340c0520342103030740701c0c90f141c00d600707190142039408199401e0a85580c10403036002036560080e03908907030b80196210b003500c041250030340080c1c0d0100b080e0440d0904509103402c1140e1600381080120035418a01140041c840e040305040d03c080369001010302d108145 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 13283253 1250 13282003 13282019
    0xc030a0c050309030618120f070210030609020d0603020906040209010c2a06050703020d0810060c050307020d0501020a020d08100b0304050f010509030c0c0604180c050403141b19 78
    0x11084004503510b000034080301119031400c10120303100e548141e4220301d42910104500e8100304070724080c90121841004102413480c1010110745070345606444000c5102003000d401c4000300303140d402c1881c650b80005202d900145040c0c110400f40c078003c41d0480d880340c0720380b002c2104900c11102b100340841c806610350740110351101c01c00460b10b844082514095507421122a541d000c040e0001c00100da804184030b001c1c154100014250f500c2c060401a0460820005102480110380319803800c203e038458003982000024015a812142d0140c50b0310124446841e00c103010f9000401c43d400103200e030701102c4524511a2554500410445850401141c140065408545d04c0100161058454504a44002d410074481d2612442c3c2c4440550345801c503800c1c41e00d01b864048043c0ca842003000b8441445082159414150762124a48000170311040c9404159460700031035002800b180060300c008001c1c0038001c0b8004400c6051501045c00a00dd84002c012b03960001c0d40f03801414802c4010b007030101c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 13284503 1250 13283253 13283267
    0x91511120105041812020601030c05030a05060606090301020c0f030909090d0804020d060b1c0204050106140d1805160f06080408070b040204060b0406050d0b0901050d0f030c0b010b0a0e0102030c030a 87
    0x20300041410408540c103855088050007042c1700880182d0018004005010502e0901006450120060b1800101c0c3c0d80b6210798400020b00118802d000c0041d616081da94258102d9100c10600c8c4d080d180c81442c9049016100e800c0382d880d1134003606628000494030140070440000204aa03291481c2070307107a980a029101c07025610440e401aa21401b1100541d1480103415407403559070951142482c041c1b052106440c0181c1c4103009001d82d42c401c484032115007205031840d5103819040004c0d4400342d014468075901034100c024103507010b0802c01038020303080c86007003030280c8803620024244d030b40c2d0f24a4202e80581044902420840c0300744000700c002640903e00541090000748042405a00d03103002240a5109030300c840b0105034000f0741c9016039082c07070203120211603048136900001d42c54040401d0140b01094801006c0c0384071034580d4010540104c81c19a607454101080c0c00a640e15000ea1068543c8070105403408502c103520030f84140d40c4004110b802d0400c0c2c200156081c242c9502041e5005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 13285753 1250 13284503 13284521
    0x6090c0c080a140301170f06092509020a05041403030a09050103020c070e090a0506090d09030201050f0c01060902090103051308040b0703030605030a08040f06020307030807050a0e030109151112010504 88
    0x141c3c03050306607100f0001e001e1070107405d585401c058010603250419152085402007003101e82c20140c10055200800324240c1001c9807070011501c15141100351403024030040360882c001c03940c03020a4042c4e000380c8c060040c20554000030b0f010a44d00d4056810140e890092107550b1000a03501c0c03d041c00154802e1300a40810351100007100c013803585550141180345003c507500c0d0442ea0200e0034150500100b08500342e0864040c0010701340501607080001c0c03091505000c042c0c14400d00056001c25640800d0850b49181c10604c000c00070b5031340300e40081c4041c5d84140443c0d40000e06200c0071603508000c2500c0454416031100741585820300c1c0c103018a50790f410504054080c141d5070500007400e510180290081148111a420368903414040908540035207600b2440c1194000d201e0f0000003a0020302480c4c000000b82806912481c1000c001c49242840c0244284c055080034104000c1254043e499004101c075000180075050044039840355900a5103512a10321800200400071420a6441003000e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 13287003 1250 13285753 13285757
    0x20a09091115090307080d120e030301050402070c03060e060f090c10030c12060906030c080303070804030507020a1502060a0c030209031507031103090d0f05090d020405090f0106060203090406090c0c080a 89
    0x104841c003c0068102040e40d030200b801030304418a14100650301c0300810b08850350f00001001180d5002c11780c04d549010501665025a0b80000e10f2400d01002282c80401154420b0050041007100003895480300000c3d640d08042c0306122001c500f08038408100d02c80b00e100c1c0a0706202110300354100860242031410900c40074019655114282506140502005401c10400200340c82d8518900814416840c2e4012300b075580050007071100065008100359005130301840c200ea298401e0303000040d421111540034200d00d400c400180060990041850b9101e00e078030260401030700300d0500003542644501041c880d03154202d802400b202118261041ea00304410303242c001803290507800d200c6460b900075a280162944a508115803a50b0310182c0c402c000051440c106041011031008110313208261070000380f041303444100080340b0320401c100448003074035420000c0c080c47d83d6034800691242c2c444a4080c0c0503034108000414080d200d802903004960040c0d0f02e900c03051030f80307444840054100c1425141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 13288253 1250 13287003 13287007
    0xd0f0201181802040314070f03141203010303081501030c020a02060c0f060705040f06141b0c060a1713030f081b040303030c02010c03090804120302160303030504020a09091115 77
    0x348100c500854440070b81001000503030300c508604103000d0071254103d00c00398951007172100b40400000c2e8a0b1120442e0340c000261256103040d55601c03810b064a20140240401010000005043d8032440560184422601001c2c0341c00c0c210004505840d004080b481c056030003c0524001400e15500518031410501c068460325040040803d040060070368032080055000708043c88006a03400c545002008a81001010b00010b0702d42e0300d8090043c0714038030030b52020100842d015801c050014102604000b0000303a5140b21602010b025104808400180700b42c2c1c100000301040c100c58082c2801c2034050312943d1180b060042d0448010700010120328500c1d1b120143c0d2100645e96002820185119403004651003001c1d910007070848507090b4540c41054101214080491810300c106d8050f6502c3c18280d00a0000070304080c2e00d8681d0342d55a12402c18070300361000041c95415805640114800c940c4158503e50762210003080c1d4840e500c01401100c00c50002003024903194035944c0d400240b081d10341d8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 13289503 1250 13288253 13288259
    0x6130c030203010c020309011e0f030e0102090918010b060304110d021203031021030c020105090a0b0403050102040305010608030c0607030c0c150b031213030206070303110706020702010e0d0f020118 87
    0x43c0c00e40d046480210003590010a4950303141d80c000502d024145844440a090300d4090807000f05002e490310480d005065842d146011814802e4044440d4200b000d0700fa00500e0518000c01d0300101400c02000c5d03825440c10002e40b031289070003001c0f03a000315048214050b2903000f02080041200046c1e104a902810134000701480c11b03001d1000d50711400c100b03800d1400c00e0f441c1400a100f03d100100d0f00102102c208040752000a400251140c0d40c1602032801075210103080d00450300800403038200c51200c2c40c0102e400410044150001c2054904c00c0c1d00038044070390703100092690381c06045089102600500c0001d12031900c0703548030944650080c584098101d242d51501e00c242c9541496440c207058a4842030411410104106402c45401c407000a00d881103103030341101c104d9075034000248620310000d980400c1c940320307821801000303030100d41150351585c0f940340c02c000941c042d00d0200d0104000513a80d240c41d2400c00c01e020603842d041071343d1459100a69004503030001e006c0c01d89540c007528101c808 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 13290753 1250 13289503 13289509
    0xc0f03070e0a09213207050a05010c020105010e0a0504050c10020f160503030a080c0f041206050c0405090105060a112a030102070c0501080a0209090c03040b10050306130c0302 77
    0xa02d00461401070001403104560600d208480b40901c01c40b010300c070018a454542d140c1c420424481c002140050100c500200481ca8000041100b084c3e100f260000c280384080c0b00d404240440000e224400801c80c1d2594240107034240c0d14244500c240700f1200c003000422035180340e01b185510610500c02e03210000300c0e400000f00c690010f2040040141e000e40e084c0c002d070b81d03c10000038840628030179081c0f40ca146000c00080c1e03a8071800f0014020818850040b800b080c0da154160b43c54000044202c2c3e885640350b12201094000e0032106543c501c0c104008a88907000740300454040d140040c3c0502c5050782000c09016650b400100c1c0d00c0c00b08002d0500601840d0000d2141e1080c0800110803100c4803101f100c034100c4d40a003c0f4540724800d074810040940060400c503100d004986080c201044141d5800f81c00c50f00070f000d001c00441c0c11000002c100102c0c144d0b440003c500c50340c400c192a0b200ca89039651000060487d0780aaa41c1591000c40406e81c12101f03d004844014070a45184900d65220303408 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 13292003 1250 13290753 13290779
    0x210021204230405010b030a18020d060e1006050d02090c070c09020306030c04110307030c020a0b01090c11011404081305120709050c0307090b09040207051c030c110c0f0307 76
    0x3091420584010b0086a42c601c9000b545001c0007140c09110030f5040c00b4a08013140320103003480b00d40756038038501c0215071080305002d001e5131078006080000c240c240341031601c05000c141c110740507035000d003586800b2600c0080c400c00c02a114094145509038209500380241404080c0a034261001c00b030000d10009050040c050340503020480002d601c078205074050514281945a1003489141802c0c0400c1a151008041d42d42c0490245408919143e850070103900340f0100500203013212600c00c0001c03c1882d06a0030941c121042c568030040c441080d03030962400c80e02c032030040ea0304106c0b2003000b207000326181c82c014008000300201c92205203039482c000106ca0010301860184260400d100800c030240720340c40358039441491008014598036102c0d400801c03005060107250860b10300807440c90542d4541d5070599a4441e4040126148a004403202c0746c801d820450710600040d0070542546d800510036000c580d409170341c1c0801406071241041c10000c00b00c003c1d41c00c083c4c0500c106500000c2103026601 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 13293253 1250 13292003 13292009
    0xf06050907090f050609060d180f03020307021f052a03040f0806060d051c05070c06030e060106020102190305040203030c03041e12021806190f081b0604030210021204 73
    0x10b840b5102d502e0840740740036182182c1c0c0503511450080c8600e450b0780c0c451500300d84c40c074142180002000070139040c00040c0008202d40191683e0788070f08070302080540000003480c50a0084880400c01c610b0110031020032012103070b6040014401384006000e04015960011401c403a030081d00c0500c030009040d2602e1904981e11840d071a141074907040008500034032685030451426035202e4030580d0030382c803031541d501e60003c2207403102c94006407400041842102950348460340510100c2e40319a48a1004025000e106102c1c1082e020780b100001e208c42c014421940f014a442440000441d841070040e030050800401c245d8050008014000610100384028005001440da60b0421050700000e105400d01164200185409174030082e040969240d4903901c440040848148a20713a0307580303001c518804070140201c41045203200b8046518150f0a222038203690300c4138100c44a20304440d41c01610349003030700201500070400b044188007608020100700920200c5004507a1170759008500348041c0c0e40154 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 13294503 1250 13293253 13293257
    0x70201090512010f06170304060f090e0a0f0c0305060f0d0804080106060503070f030905060a2703050c0111161103070e010b0702040c031b11070e01080a06050f04030804060f06050907 80
    0x75200c00e940e440131702c20704002c1c040005905c0da80400810203e65a8801d600030482030003e10701e403246030140f09040a6016103082002c0310414200344181602410b00300c0b0301030000034280780610500e6071003440765602c1413800130311004540c80484140040094001400c2d100c0034810080130071144001d0046c00014061581c44030780c0c2e4036000c1c500070040b00407002c0303440030942400d40c00004100001740303a0350017042508c000601e1000c05030a984540c009044031500780700d01b01868009040d0400003a0101c0030010000307000440f6000761445080c402c442401000104600200d408250800703121040c00b00007070100d034000350700c50070301c010101000d074071a1b10303106c00001f047d10031403c1c1030159030359900940c2002c0c010004a11250302c0c10100401c03860007000b207030780790401c5d50080411410b030051070960038020003940c5035043c490b00c036510340d00306403140c505210102e52440700d0049401d214a8041e55a10010b40303030340c0e03151409042029103d200b0b658540c0e102081c15500c039100180941956 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 13295753 1250 13294503 13294511
    0x90604020906060f03010303050306010e1008070207061b0602070f14010b011202070503030609150a080105040b0903190e0d0606171005010506040501030f09060603031706090601050a030207020109051201 89
    0x140c030400c051071000812a81c06100244115080c90403054252415030758982400c6072030765184001211a01500300b40c0541c0305048241c3c48070510340201141d80181c020f40d00f514011707500c400c810345051070480c00d4816120003041c1e0840110b885a405031094610034140d080c40b21030952110030041030364050221050355a0341c1c4540d502d42e04181210030850f4264000d60801e58191101503d9010040186005283c0140080c544a513010310189480c0c0004120004580c0c4650300e0754001c0c4000c5030105c070300442c00350114180c144004240c400400010340100420121184100c40f01030b0414851034100d081819154005041c5025110203010a003810700d8074030190a180d1440c04030500f040507041803800c4014000c2d9100d060456054070303004c3c200800c58081c203180400080000c41d602500440c43c0490120415500540c151024108901454040c1c0c4804040280c17030842a0b4001e400310700d0070840509098020b0b0081c0c00b843e4014145641078558503408200300b030701d00c480c00407080c0e55a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 13297003 1250 13295753 13295761
    0x4020c0f0f010c0504050111070302041b02010b030304140618040c0c06050601080106091205070806010609050111030a050306130f0906020904060807030804122301230601090308031803030906 84
    0xc100088015034108070000d001c210105100645203220303038000c0c2410025403819280750701c0401c00c420002140e018008000d41c1010001c81d86002c1c1a00f0505401942009034032140b5250010a840503200c2011460010710510700800c03185610010a01c15021030f56040c11046070396911404030010100d444030840c1a40c0c514180040721343c003c08943c10f006002006002003548055001c091307800850500803400d40c40e0400b140380006c1940110b07040d10500c0000314244c2c1d0b0010010f0111402071721380c48499a09424400e40301c0c00f80d4020480056030600004246203405880b400311031240c00307400030b500d402c460301e04410342d05410000c0d51002c1c0c00041d52030326800c00f403207480002d200002c080e1180e1419a641c045141c1715910030f43d81d001030003c2014080c024100f210150b207184410340c00860039000c03804213018050701007100c5402c2c0341e0204840b400e0701c00280680c4c8118416520040c45a0550342ca40b120358101401d0915002e00000407011600420001140130302d0042004140c0c0d40780c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 13298253 1250 13297003 13297033
    0x19060605010810090c0c06020c0f060c070305090d0303090203030a0201050601080105030d02060105090408121f09050106050a0c0c0f0e0f01090b01120c030b0a03060518030903030403020d08070204020c 88
    0xe601440c10040c118040050144142805000b0b8a03680300c07000c582e460b40b4800c00c640d220011034018108900c0020040e000c0c8100044a820000d101010b0302c5044d42ca0260500c0c2ea0300540c40080c0c00320300700300035100c541d01c1e0050380c02081c14820304000840c44800d0700032900d150896116840980c1d03488080c84000d41e00039540c94014070084008180c3c180c0035000003522400103120360760043d85060045403c001c070f880c1c281ca00d41030040740306e80850314080340120520f004288460b403041c0c502c01c90105500388030303029043c1695801c2c1c84440c50082d0140341140c0d501c1540d141074800380880c00713021400c40c41048404009100d0300700c40e0031040c10000003c008110041c0d000445442c070f81210001e0a98124260010100d102140001c21041d1108254007403c0d03000d4040d68000c0c0051004401c00c000e40d80003d00034400b003469400c00d03410704502280d481c4034000da4503a140e40240420001454884058a9070520071301c1982d040c840c3c0c99010a0507600011b000000039004910102040303c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 13299503 1250 13298253 13298261
    0xb0112020406022b0c0204050604090b040b010e0c0301030c05010c06060f080307020a0905090d1b0203010c0c05010507030504020102060612030d02070c060f0c0b061201020705060c04050a0512030307030b030a051906 94
    0x801c0100074030309500541c80c0640048172000000303000300d0301c1e580042c29598a581c03000d203030281c104020504915181c0b4080742100c600b4010689024410000b08203264541400c0d2410703203074000b08030b4909509240043d10f0215241008403080f60301c907400400c15580c0161044000c0c08000025070b00c8001c10b1040101403040e0381c2050380714134508010032281034000140c0255206413802d02c004084e49109440340f00081d104400380d090742c03c2c0107480101590110300c1102d41400b8200030840341e10b42010440c2600c2d010740f406401a8046004140d96290259201d000c0340311040c21280740001c1d581c64642a82c0042c6d10545010f02204000c006c400d400c121110054a40342c46c2c100e0750a14155140c1d0b003036281c041c0c14a4003401900200380e92402c0d0950484440940003411a14103142280401c050742d8000e00825001d1601004002030500b00b2000d5800d082c0301603c05075045586c0c0360720841c000c01006402d541e062085800307400100300d0612090a001050b01450a080c40d406d0a11406072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 13300753 1250 13299503 13299553
    0x6061103070b07140c0601061206090c0f03053402060705040e0408070f02130b030705040209030312040218010801060303080c0c030904090305041a03160503060d060b011202040602 79
    0x54208101e5100080e9400c00b01692020360360038801c0d0f0a201140c60602d00340500d8080c00050300c81c4000125050f074028040a60381145820144201c2c0e8035110144152440169000b000c20305031841511014001e4000e039601c518460321706144040c141c40c0300300b001c106030300082592002d189050000260b042c045280e00040c1418034901d01441c202000d0403a210050001c1c0036000041042020005103403804800e00d50000c2c40300c035100301840d031800020900399480c14840e02c1829000616801c003030091350b6010340010082c500f40807002100c4a244000100304a074000b40003403032203510208200b0190b0103442043c2c0001b600364294a0080d0018102800702100e440c0c040c00004800d4000104030f40d080380d400da03004518090149002c0c0d46030f010b59001590807a503105840110484140b01561107200014460098041c0d6520b0130341d414801500d100b9000020700c80c0245c00304481e90800c4024040600d000305d82c407903e40130300030200d80250b04401c00580014284441f410a41e8007031801c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 13302003 1250 13300753 13300787
    0x4020f040b03060c130906060201020d0605090106020d08040203070503150702010e011107140705030d0f120203010e1b040518010302030d110601270905030a0906090e0402060c0a05010e010606 84
    0x3101c820030001e580c40100520078550400c0c0055221002c40c22003030000e0041441c84014080641c40b0007002e07020f03410032003881c0f403124034101002a82e403a2440c1c03114100c0d0300031b401030100d564041508841115005000382d816100e40c900000c4c03580c604108505058540045940c4e0a0414000003402d5600362032a50b0342c26070414100250204d03808045501712940603011140300320340036900b0307070074180103600c41c540c5400703a0755000c1141a0071005480d101c1c1c14a41da41201103e592103500d0480c0020302640d21482141d100182540b50001c504002c010418084a4103080e46c41c800a4035640e5400342403200754011800400c11424108111032a40c02c65040c1082170498002e003840e40c4e0300c0144514040d0920400c0c6507480d0302120181c02c0308440e4103032814000d500c0d080c10420750340e900446008000a44c51b142c000b405034440d21100c0140c0e00103403101e21590300d0f56001c01c0019004503010345000d010301048280000c0b02480307404003d058410010650700d20708600545018018808280c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 13303253 1250 13302003 13302011
    0x310090905030906070201020f07030804080d0908100e190c170c010e01200f0604140307050304091109090f0106032301031e0803040302011401050103020a0806010807050c01060303050304020f04 85
    0xc001070002c8140c0d504241d00ba1202030322070020f0700040b89409551120400280a104804803d002c8014011301c00c1d100c261088401c400a01c4c0811100040c0324881d500e55a0444141d600c1064002c0d007240000d41c005400f11115501840b150b452075004034101101c1028540404118010048005500c01c04100001d0000b0b02902e0300080c0000d01541d01c420b0401102603210b590703148107517107035903425816041101c00c441c40f000105680d561080e201a50003010f054554403210800008071905240d00001560815190000880182c160b4a19500010900b406902c032a51680d21801d40b103000880c50800146d450044050b003107680040302c00d40b8254850b0b2261400d0100d603d0043e044a501801004e111210060300848100c20b68034010f211000000900082c1981501702020344c82903007040360656640c41c001913080303200e141c214002065002c40003501315070040445942c000000d040261034460b031034003c2800c40305660001c80c0802d0001c8144015803c0c0205118dd0403941a54104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 13304503 1250 13303253 13303271
    0x60402041503020d0209040507090e280201020d110111030a0c03060905010b070b060d0f05060403030c080f19060810140604021201030b0408090303030a06030203060703052202040b0603040602031009 87
    0xc203541c6044e03101a0054182d07402040401c0380400140008018600c0308010310a07600c1185510b03250500002142e49403410088900701000085c6241c0701c0d030b0305800504079001300148c241d0305500543c0040c1b010b9566245082c5841d5020320085100c0e00050200040002009001074200e40705c0790030581c45586024010302c48820b02c2000c0b111004d41280d50011141e40c0c000c00900800009000206029950185074041050008040b80254402e440501500070a00c0c41103031003400c11240d0007112410034010030408921040401f103441c0600e0f02c080790041e19122140d25052080070b025050aa5458600c2c180410400c6e200c0d1b004041100d0561030b013488400300c00b88484060001030840201403010400300101001141e041d180058140d03600c0f0714000b00c50fa8010015440180e00a014500004540c40c1c880d128a03449483d182095810240314070040c00c0b110b8113007690813078015540300c040702c40d0f641d101c0010398402c0340316000240e40da2404082002083e00b442d80300c180e00728104080f40f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 13305753 1250 13304503 13304509
    0x6030c02070f14060c01060914090a1703060d02090c03100b0403020d020621010801050109050703020c070e0601120e03030601030606050f041206020714011b020304060e12071706040204150302 84
    0x48880790119118240850783c0012498807820744030500d5986001e40016002140e9084101a26007080c44003610303680d20307041c40303440d0008980300030709904c4003070050000c07119100c2c0619004003000d4080c0850881580c0840e0314005d040d0b603807010510011081012400701044d45102600303044030400d00300740c69940420400c400840f4002d2088502041d07403002010107149024416100c09066940c41d6510070036103000307081c02e006054109040000082c1410b020740211401d07801400000e121311442c200700341d40c0e4150041d104a042003c20f4850031002c0d605401200050b42d00c1070042c55603824140d0000d02181e031650f0240c4140141404150701c060b0986064408882c02803000c0c2a90360030038076095009200b800c4004010040000c2194420607056019000e4058120000200c6012074842a40d0381e0080e88201400640780851010003400c00503d00e040007005282111400b6880f20078912283e0401c15001c0c40e15400704040000707620b00760184d42800c14424103c40e143c3c40c00e54000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 13307003 1250 13305753 13305779
    0x40302040509031207030903020d0e060714031c0e010c09030507031103030f070302010b0102070506031003020418050a030c030207051e040b0d0605010b0d150806041b03061506030c0207 81
    0x80d200d15030760710025801c50010f0040740c290341444281e00402d49012000940101040c502c254018868260f4410080f03000302d40c1066040c40042c000c0d0305040f039607922410201c0c100152000300d07000c05d2000740300c0b0360181955a22202c190240119a0500b08440c040c2160904080c1c0001c004040310208082070340480c040c01075942010091038a50705000200c0d181d4814041c900300e902c00700041583c1455810f500400e0303040026829034158a0b918400c0107602c0c0410b41d058907550f18158000c000616040d44028015503840115403c001c6040e210141444840c11081e008034403e607425104250b818058039015080448a96842180712440761651082c640899070290b9560380e50391a0a555518a1030002d0354821818041036071a40003500d41600456804000c0b10704000040c4024100307014418240c1d1141c0d0010702181e40d403600d07140f04003080455042184081c0346004404070701c15004400340c2200003621810701c03501d0610028100da40407400c18085420000701888161000f0306 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 13308253 1250 13307003 13307009
    0x6110c090402100809010e06010303050c0105070801060f030b010c0213020403031101020a050301030f0302150c1806040b030a09020a080102191704020904030f03110309010b120706050a0507060b0904050a1101031104 94
    0x1e8031319165640c0800d06401801d800c044c0d0349162050780c000004144d48503004000725a9100001d00140d10742003019100341400380a1003021a0148a85081c41c44c420f40c41603d041c07a0515018010b48895001300c0e654032682c8130030948040d0001000d205058100308403010043c3c40100031807424030126002040c500060000401420f07801c102d14007418800c000707500095082c0e603120380c0141040002d84075940d125040c1c050605c6c4409214440074030b40b034800d690480340300b8803e41d440c5a903408106401000913501c00c81e0722107410280460103803400d2001e088900c20007010140300207a00070b000b80a03034460071441503c800d0340200308401a01c0300d40401b81c200303a050a1001848071604019406051000380301c8551a2001c010095449030540045c0c00410b0203503406d840b03c2041c020503d031224154001c4202107007007000140d15507031003000200303402400752800107a5140880002602171030256000d80c1d050340a00c00300020301054003814808072500342810010a050aa031480403402144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 13309359 1106 13308253 13308257
    0x5090c03030901120c030e07060216091a01030c030f0c03050609010e01030305041701020412150510060f050702030c0306010602150f0f0112020f090106110c09040210 73
    0x807040707640b03011042e9904400390402e6000d00c0c010300121a007110406a07101c461140010301800703800041c003030030780c050302e01c003011016160103c580b140c011600191403c0c00385001c0100601c100f640144081c2404260315000007025402042440300324400d9a0030301a9441c400c0d9890352102d07124040072100742c040c0e13036251101804101310900004010800422050001c890000012640c0c14203c100140c0b07003a48a001407440e04d00000d00840d095002c440201c1111411802050f0f4050725081201c00c03c40d18046008003000c51501042d82481701c005803030020f640342440104c480709000f808450f10b030b580d5118001d588180d601082c1c040081c6020200b2608507110741501e0040407800001442c507402d12034070200040b1346003c00ca81c0184c01c09840d0300c00e51180c142c151300034901503c4500c010340500081c18140b00036103140901c20100d0004000c010703170b1030b40f031290a042824 = true := by decide +kernel

theorem cover : BRFrame.Cov 13129503 13309359 := by
  have h0 := BRFrame.cov_init 13129503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13129503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 13129503 ≤ n) (h2 : n < 13309359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
