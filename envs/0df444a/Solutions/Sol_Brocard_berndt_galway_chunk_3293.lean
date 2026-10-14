-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3293
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:13:56.385768+00:00
-- url     : https://prove2.me/submissions/52670b70-03de-4e82-984a-fa4da3300a4e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 592086330 ≤ n < 592266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 592087580 1250 592086330 592086337
    0x1b030601080c210106050301080706022d0a050d1d01050a360f0302041808041e181505060a05040311060408030d02040503010f090b16050d02040803070218060105 71
    0x8100003456620b0040390806400c00251040c4a00d50f04036020001801c00e500ca001181201c00d18000c0d20b0a05850b900e0480c1c503596408030010013007002c0070100c00ca81c00100c0b650f02c0d6031001401114010181581c81d40e05000702604543d020035140d00c8105000c41030103043c9401100240380580c50300240ca98003401d40d0102c0c10007451240f2102030a002c0c03080c041d62200c5c40c1503811705542c2416039a0b446c40000c0d02030450004030700550900414000588110310400002c03a8401405400c11f07080088050340569150880e0102a10300e03040010900307215941c148450004aa012518003005c1242030b42101c40f0340e00c402d01410040001c1040030750320100351001d03079034410045802d11003801e000030501c0c015a0082505800b000404800d110140d5008104542c000c0e0020701551940d0280d200840e00591300140400d0341c10000a01c0c54880300c06142c85c0741d51a4100309013021410300703400d000ca030401c2c1c02c640c8082e880001d4070801e40c45c001040c2409421491030550992510f580001c00600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 592088830 1250 592087580 592087591
    0x3160809060f0c0405040f06080d050313140a02060d1b230f04030515090d030605060f031902030a1a06040b04060516020904151a061603020c030607081b03060108 71
    0xb14288081810480380d64200c500401009205000d80b1940070a00d0b07000b48400c0c03003a5280d6100303490b10756000742c0c054400d6038414800d002da0b9030300d41c05031911401c1281d03002d4800002381e8001c0d1848400107035585c0000d0866883c050782c001950750503246007500e0000c06d028401081c040480b09910350004030103d900004100720400a442e0760810075041d10501903500001d281340101d005002144c82c0001d0381c2ca00c0303030391520120b45009200792000d4049032030700d01505800207410004000d030080c100340210b0300701d403126008500d200c0101500c601260800c1d15013445041e150b582c040c010780801081d0740e25005044607400e107070902d00900090b0620640c8500f409001c0d01041040c000541c0240c007610f00740d00680300e08840c2c58245442420459002d201c204040c1c68055980b01e04001c0c000c5044240b24050803051420020344800b154500ea6039400b02c1c114410140e800318142c5082c0034080c010304858684d01007900b001d018104150070046040c0d006480280104485607921002054106 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 592090080 1250 592088830 592088851
    0x82203081b0a0c06260c04090c05131707090b0303040302150c010603030f030609021912020d060f0e09060405070303050a1e02070618030b0408031510050316080906 72
    0x21210034070030724102804608050b14401201c0c00000d4280d400c003007400207a18a540d441803d000c9940805d020120741a03680000c800c800b030000f1312000c02154080418001d003410001d003000c142d5004e80c1e00581c00c0ba0801e07440c002ca00703000b007044118100b0203a00038201120040c031108500e030010039901d0155101c0a0311a2015800398514005000101c2e000c460300319001f807129a84a040213801694807086220020380742000000c0c0e000154429544942080e20040c00240084030088a03003842d01074104680319400c1145400b02c00c5140300d03c8004000900303854485030705c0c01c0782c0418010780003008032899070040020000018408118a003d60703138036040064803201200750407140c101c0807030100017221030f468030201c0d031242d00003c43c1f6040b07a030b807651500c40020039500501e00480007440700400100359200414009210700002d036a10005041500c00c00c03c0301600002c6494013a0100c500c0426800018810086084034120b814030700c044c14066064113189840035602d0800401c0d030304c440d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 592091330 1250 592090080 592090117
    0x80f060d0212031201271104050d0f02041404080f0307020309040504050a170406020309010c0204110708030a140f01030f1a16022104031403090d08220308 68
    0x11640d030320325003010158010307180c1c041600100040540d6640720031201d0f030700540c52500015450156410391095540c1da00d00c0820000c1100405070060039411540c4100000180800306032030b1108030742c5039081d40c051440450048654010310040780c50542404022100e9041000b000c1140d4000b00c500e18180e66109a035259150380049007980202c9000e242c0c85414030083c403060003c002405a9981d000e015465031304000740046113040d00c101d00c0355001503001400384060560040b60070018042c00580081441c3d22003a640c01510b5201c040111078400004c024849064014410503480603440d820700742240c01c01e46003003c00d0110500c401014910401c0e5120200007440f504400705d02004a0401c1507800d001e249104a00302d0481084010320410041d1b00c4442500300c0d0200c1a032015002480c6032604585a0140191003101f41400501c01000001103a4032201621001240141e20613a12141c2c400d8805100751031441d40918140c09409040c0301040740442103510081d59009940c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 592092580 1250 592091330 592091341
    0x504061103040308130305190309062601081c050705060c1606092d0b0423030c03030709050108060a060e040b04020c030315010c1a042f030706050a080f 67
    0x1c1e601c11900018501200440d14510b44080c004401066034441c1c0c05030340e820300041400803920201280094009240f401e010420a401689480c00b01a9180024441110107411001c031242d400e0340980c0e0030717a00c6025030500c0c59051004200c8511068541145400c0d00c03929015541c8001401c030211a40001401c403291480d07408600380c14552140c07003400f001c00c541c00c141001c0c040d041c0c180881040c1c000060b2010072105040300103503e40c054010b02e0140c803940c840004003110281700001d89041a8252007000300300b00090080451083c00039a6030381b81200c401401191076034032040c1409648418800700c1c1d80c6082001c42526600e1800050314810840014054a40342c0340d0b05800500c00a042d450100c1c001c80210b02c074088401c100c684441c004401140c410020314800f40070710340f080d0b0421400c1d600000c8240d070001c0c010a4100044078007082416800b214100b006541c0140ca0790410400f0b04050010400506250602e2410485040340103001c15900511403010903c88400050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 592093830 1250 592092580 592092583
    0x7020a2a0305011a030706050c0709050406020c100b0f12030307080601031b030f11160b0403020a0222061703040303031d031c0605090412051809070507110a0605040611 74
    0xc001c5400800901801d940000c1225154908001d80e6000340585880407980340d001d0000c85888000060003481c00714644010313100185400340048800323a4081200240e841d10400090392413809041000a0318012002001100c0620b41030243c040e490701d02c00c0e4003643c0c0000c42039950109443c185042590b4503800107d0040a00d98803078241a51184d0212a200fa816408291641200c0400304034035441001010440c2c010044041c03a00303114210304500091440320000d800a201b801207600241465000031456001d00381495843c99000620000c07602083c050300008000c0c0070300b0308003035211040e8029100e01c80ca01001d001d146c0c8070404004030725061503045003505811026651610700c552081140810a149114460fa003007280110701460841102c83c001c541c041d02d407014007240c0250a84040d005070290034a1540b01c0c0352030b19406e03164041000e204075999646d499075182580b504000c0c40f0540c1c148640a40031424003808225084422101681c44905201040320300e640b0643c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 592095080 1250 592093830 592093913
    0x806011209030c0512040915030b010b21130539011e050703020d11100522030809010c02070e0a052a090f10090513061a0c0607020a 58
    0x14402c0c4903c0c8104500e40d05d1a6000d030081d40c14004c8140010300c002000c41d031419070240006410418500010040707203070306100614041201d0703038020401003030f4100c0d1504040700c129070520800702d40074402c1c001c00c542400750071400240c400e030011046e21214114010003610070041744000e000e8200c91070729030b801202c032400c43c040b011008520a0060303100040003a0000340c4228051310800210322885406072913041441d041d0500240202d51360b0000680c05004c010700542e03400704c030018001700d01c07030100203020986501030740b100b40a90a0201440e800c4403001820f8004540044109229980032a80400c1e0810074110012499032100c6078510000070000103402401041040d1543d0103048110140000d9001220550369582c0c1000c207100e8606000703031241c40041c00754181440185442c8203400f81801c0400b90000b0038a88501e00080207c013109101d0024000219094603030142c208510f9503c40e200380f003e0101c5141603071300c00c03800c00c001e43ca242c0450400ca02c2040c107065212030a4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 592096330 1250 592095080 592095083
    0x12030203190e010e061308090f12010f051005100206040b071b0f1a070e130b13020705100902010c030e1f080708010906050604031407030f0c0905070806011209030c 72
    0x81000748500c107800d5001340491400c0d01c0182c0600d2002510100d0080641b070407240d0043c0101e80742980c404100880ca942001105602060050160030083d900b44102250340d815500c000850f800d0003480c4d42640d0b20158001403180a000109400140d03011401c1c603000750303005042c49005e49404000307542c1821448580400a0900c1c500c1606000c4049036000000f070082c019640c90348040c030014200003000b11019004100d00c0017880d10181008106586228946c02c40043c2d045074800c00120107a44034035000c0403481d004a19107051100520101201c0044c0c0350080146003041c0d0f00190903890003003c0a8184090b9400c007100343d44640c40c1040102d1168a0301c046c3d030303110000003e03011510035224034000a141c4400482e0032032280c8948001d0310340003002d41d410b191641d903907442400d00d00184591035018400001002030b440641d4804030501c140d40e2a40010704188008044030b1008248408000811080c0035480c1d0304103000800010720000f0115942c0d450f03050542d06205031500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 592097580 1250 592096330 592096381
    0x9050f030d0c210909290906030f01020a020a1b14060d02040b0301090f050a0506031f0e19120201090308061201091205030114061e09030f0304060503010504061212030203 75
    0x50f28400140e200040c030041d144001030400030046800c810707105600c8541608040b0003e1601e50102520b0030320201c03540304d40e0040458452881030302c0c480782680c10501d01c030300141e0b02c9015104200310b044903400914510490b45140310600c1c0110100c0d4807018401014020880040c0c011802400c540484000e040414816a0b407940d5600c1b003071004203000c42d25102010316100c082a250030f01030140d80d010f000000c0c01070a401012080390300350203c0040a02c4403081d503c00c91128001d0003401504418850302410342000d980c241040300f0403c0c0f40c040b401d8216450f1460b0000084d4004c500700c4d4010b041540c84d04080c02400c40c081c0d006100c403031000741c0300908103405040b070349034494001c5050f68007925160300c0130500c074802d00c40c990152b01d1100c40c9080f080f401410400e0610300192465160060840d0546028000700034115070080d040a03002420020043c49141403a003d09001010f003036103040f40740300058441001441c48134120b402050340000200d00120050090340024400112 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 592098830 1250 592097580 592097633
    0x20702060d0e030702090604090201080a0213050a0807060306061b11182a040608040f0c12050a031803050c010c060f1e05251110060b030709050f030d0c 67
    0x5425a50794000310130032440340341d407040040c855003854041c80e40c18660603120b001c002d442d2249040081d4004040f40141c1405604000070700b40e4806d210750000301306d510301810741d407428006c0c010107543c4950843c02c10301c1f041c0351010711104108001d80c0c4407150450212400210301500140802214290303545100c601c8906010000c03548004181289041e5824042c10300c2c4000540d44060245201d101c01041d0403400180c0403401134090f8149035403103044490001a1a040792102c0940c0f00c401c06c0c3c45561001c4100810943c00030b2281d000d2480107292002c030b4614540c1c0302c81e80c841c1140f84150403c40840108030402c00c0f035420031410014100d105105610072540c482011440007441c1d108507904250201d0784003c202d083e00706011074540c1080e4090040c4a2090760492102c0d0001c603901e100e20318040b00604082e1080401030203620001c50f60341d0406140041000c0d1407600401e100307007117500c2c0c0c0320490354001038554900c034031030300b03080c0c146003030b40d0a200e45145204444a0769010411 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 592100080 1250 592098830 592098851
    0x40905070201050709170721170a1101060e0105191503020904141003080304140a11040e0c130e03210106020d090f03080906190f110f060a020702060d 66
    0x64000504c560b41540c1c130b2201070b540e034480c08040441c1340d0b000120190058403061150340391a0014580e2a100c85030390080c0100603a81d50142440c910091104220f80032801c104130b035034004852021960594002d0000c6814548854805501072066505c60b92180b5410f02d0982c40e10115400182a0f10701e0350104591150000303006580184071862046280c1010b0000d0401c072800c4aa0203104940c007426402421503880b603142e648003400650b43c030749603005a1405440104502c4100b28460080c188202c203940c401d00080e90616404024540c2040a0003c1141c40b0b10000b04a401c450803c0442d08003915100c040c01c0d442082c102a000044501c922200e8100c0c5000c0241200c0c1c0036400c1b50313a288410041100c0511030741c060b51108880385d0302d0800101e010480a809d401000038200b61802c200080b8813950501481501e10218420307441110703500b50418040e280d09402c200c06030840048103580701c0c0d00c80c040101102802540441e0f51001d545a400650741629030041082001d03103101d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 592101330 1250 592100080 592100083
    0x5041b030c180219140708030c0403110105121603110d050702160305150606090904150b12061f0503150f07031a01140c0106090e120903070b030a020409050702 70
    0x39030258250b1650742c0c900d0300400b00700a200310340031040d00d00140050030404907011a030080a010016182c00700500c1500046003408000314003590300030300c84a070744074514640030608050403685103042c080305100884618090b1f6550700c0d40981049150614041d40ca0010f80040c82c000c408201d0242010070040300182c1150300c024007840c11502203131801c3c02c0450807805556541d01000b46260445002c401d50340d13100c5500d4030b400840050000d070074003c55601007906400101d600340c50952070fa14035071003e10454458030a00e01c0c019541d51721410500d9034010341d15000603140154071000541d10311060340f440911400a883e00800703540980d40f07481c1403025030400554102c0e0103d6285400715113810b0003441000c0c1d0101c401c40511910600300401911100480c8510340c130301c0c801c200300c41c4029050a11030900a8507114000088a81c4582c910f02e01e464100901c03500c0c0c4100c02c000301071140e070300040c50030100c81d40081c0607681da984000300301000e401207500420107181008144100c0580 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 592102580 1250 592101330 592101353
    0x10200403050c1206100b03040606050d030c0b0106050a09030b0405031b030c0105070c32010c020d14041d04030c020a030b090c0306041212021308160803030405060a05041b03 76
    0x4102d407120b0b01106080a102e449000070784117503c1901000c241040858004006140e00c070f405040000365560b5114040343c00e5214590040b40009d0000c56980200100342181030f000d0a401c3c5842c03030501103a001c028180d1141400b004d80b100b4004000074040240c10000c41e101c0c0c100e46401941440d4505158583d60b0300b142c800f61840c0c2d400c200008a10740e1099a125607850b401034841c41011587c0318a0600b0000c04c024407103038400c00c030390114a80307031800d000d8514003800365801441d007400ca0b0f1030001c1010103595864500700c03004120401008000c0071190750320310040c01c4c2001c241e40b203d24065501c8081002c0003034100824400001c1404112040c0ea44074940c3d11042c4c4100001000c10151103100882e0010b042c140d00c56031450f25244140301c00400e101408200516110300c0001c6d00540074541d0344110445e80c0041c05080482091002c10f600400e1008020f5003582003640d039050311081c1c0100114074090303807000024240304101d8040b500c1100e41c007280d0506a40c980c00e00350901107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 592103830 1250 592102580 592102603
    0xa05030a1407060e030a0209071b0c080c09040f03080c1303291014010c06020c010f06120c0303030b13050a140c0918100b120718081020040305 63
    0x610200081c3c814091400c13000d415000070b000d00a503502650802c404614058201420010041e03c0891441940d00c25000c6c414000d000755200a13280103c2c2030316003403141e9190b501941d031603803e1000154110030301d85c00807513042c04c003801596242c8114034150700440404000841003000000140804109062646d10305602004404101242c51181060b41038950f140281e01040003007280c8842c400c80324228100500d00000c074000261100800d82c2c201c02a03848407659201d0025601850b5442180000c1030340315205090b001e5151240a940c0e5110f100140502d44c4503000c014480c0e5504400b04800d8003140010091340c14428400401070440c0783e03070a10b080720304074080f40344078194a0680d444c50710000d0402e9030a01e8281c0099148a00103882450407230760703038000460600b01ca00040c0102070003000074002c1324030348580000c2c00d00c091510803030301400c10b003001403181c2900400e01c0c112101c40b01801240d210061840d00c8d0032140703c0c0c40045980c40002c540070080050220b074855980 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 592105080 1250 592103830 592103833
    0xe03070c03020414060603060d230304050a0807051f0315080303040c09180f050f15091002070c17120c07031703010803040e07050705070f030302010507021f02090a05030a14 76
    0x44c1684003020a800c00261502540500184001900c0c0d2a15464682003a40306910905c100e001d030b500801105001000340303503120b03000441c0902260501220348801051410020117140f840e2030f01141c0304007181324070300300c800720032203920901140244c00001400304104035815626039101c2d4810745030340041d07400b02d800130304030100001e00100c240610304001541890003005859207684d800070710b03001d210040f1070358011030741b100d0440d26043c08054070301c20700704030030820500e41381c1380190a0017410707103c10f0340d42441440180701003031300d40109500342c64104004046140c0c1c00742c540352a005e16071042e6080703090f00140b400c21040c00400c07844d08491152211169000200321415a980424002d04080c0d5109000400460208041503a00075210741091032034260380361030b03160500c20b00340c0203200680301d20034041080641c2440b419501c104940b0280203030780d2902c0e0280b031960205218a4102c1500451050380542d100c0c0c4c6000d004100007000c45010f60501e107060342c2016400c800305d444c1c6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 592106330 1250 592105080 592105091
    0x30f050912040b0a020709020d0605030d020a051902030c0d060e0c0a031502030c0d09050601170f0d121e09030e0d080412061107050c120106050307050d060e03070c030204 75
    0x100c40c00240041800c0300c0e80300c5103042504103526a0040c0c3c20040311401148038910300014048054070042010284d1104007041d150f0428051503d070081700c003d4030045601c80150000031900100e80319501c0100c09001d84014451800040d00c0c0041c083e031015407014a1500c2c40c0100007940d0300554500c00340d40c0555152400e000104030380504940300c0070b03058450a000d9840049901d6006581c8603c442c1c5106040110000b50603046610b0b413032007101c09130700000043c03003010324280c0f4800c642c0c03c12600802d84150781c22251519084040210800d10074803a01c140c0d0309e09c550360800f407001002c5c0d04607811482c18000c0003101505012030143c010403101c000000da54142007190042041d0007a04280c0340a18124040078802c85410054400540e10400070905240c0342c0024042580180000d185507224441044000c0030101d01141107603142c100104410780740818400c0032144100c03440d203c1e03c03080c3c0c10244003804e6001d50200031400001810b4040007e003c0e807182c2aa030081d07034200311 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 592107580 1250 592106330 592106341
    0x906060a050d0e01060321090b0403050a060509030903030706390c020f130b0901050405070f0810050d050a06060b040f03080a0e031b030120031311090106030f05 71
    0x100348a40c0440c0c6001030000c00402c100c800040c0c2004103a15100d80000442c1a541d480e810042e05e0310000843c0701541015030040c1843e0f20079003560283c0000000245000d146a0307840d650390150b000010039054840c800a02c00b1b401c01e00070b55042010150a50b9a0303280f081c680311300102401c09000c50342184100e4441c1c01801b420742c50480c070344440011680085015501551070320521041217a00c500c4803a0014401d44503060302183c11003a8060114100024608028000005030803c40c042d51604c0204810381d503100c0faa041458a2604151145894290343c1598461a9412090300000c11039500410810002001c90303c150164008100f9643c90341650142c600c514450b03207030100c1044000384045640d100081a08100a08044a4070303886040031a0410580f0350310810890401c4460083d2803d080c000c0752040c0441240c01102007400110091007400090700550160b40481c00400410202d840c05a00c41a002401c120700b82d07a59190040c050040d1542d040511401c1001054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 592108830 1250 592107580 592107589
    0x181403240f13020a031a1608060f040e03030103110907181503020d050a06090b0105040b1209120d2315040e0c0a03060209040605010f08130204060e070e0906 69
    0x82040008a00d02090300d4507014011165006016038018100c1c10805100580d81e04081c0d8008510404400741125004080c003401c503100149101811980e05440e1400c3e1940003144035800042103592400f042900c1d804100100700e02c40b45005103100c0000040309010351140300c0caa00c0481119400c086540c2c910040311200260310130300414a807a14818050888600300301096200300703140060a15500c3c244d010244c40c800d60382a50901d40d9080248600103890081c2c0c0f41003602800e001d40762500d06503d049007889020300741c0c2c050a5000300480c03e00e107010301083c29012451903585407552200d907110801000c4c0c2686181104030f01e41c40d9001e0915529240521540b03400600c07026248070703002032001402240d910002c050183e44c510b4815907a520307400340d0146028401c0142c5410200050100700ca5040e00031605000c6101c80391080180d2010f2555807100c45a4680280a902403010030064080e980040800d88110010010802d81c0700e14019203c000485031a01203840310014003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 592110080 1250 592108830 592108873
    0x50f0f0d05071502180d0f051c050d0506180f01261e0f0f0a02101803030f0c080441060c07080604030513081209040c181403 55
    0x820028801410300300d00552940a0700d00c10382054100541407405600294542c21222401c03680b0047e03c0d4200b100703000c4108aa01c4000801062019038074403205005045801103009881050382c8584c00070300603440c3c0b402e06424146117020001014108442910f226400074000c1203040e0f0010f82c03d085410107c40040300d4220007030703405000c41082c0740014008195801c00c000f84940b040104614402c4803c21100f0300310070b0014090030402144c2d00c100280414001070b01c0f810029001c0100c15030300071078418102100d03031509107103064507241041650100d000e071034003604101d008031740060100c503450b000c540c8003074001140c1510366035600010300036a80380342d01005542050107180c0005040c8000280304460040c403c0711209555501a82d1038000101d030104e00180f03012421700c0d460842101d12101820100010b8045502010200612402030042c5203200e140c50301c2c214400c40703000d510801121555800110010f42d11074128560101078403084034001d10422003407640c40788001014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 592111330 1250 592110080 592110083
    0x70f0c080313171908030612031804050a020712050c07090204120203190302030f1803070605070b010806072c0a080717060f15060c0114010510051608030c0403050f0f0d0507 76
    0x22013142d641d030f214450140c200400b0742e80c00c10b00d20048211070000802c05071051021000c0380300400b641e980c0c144815158003034411100c4e00d005009840c0014115075080c400207800d0714010391140040c44601d46809881d5115808003440003a000c40e21171041010882c0b032a0096040b180c0714513110b84103805a0b0000f040c0600141c2080c410316007034417040c400500b00261441029040c241c21800040d052280551103071022a10008201b001c02c62000c120740e0050006c24003030314041c54501c0029041d03681301405d94801d050994403402030f591009445481401001e0700c03a12680713132904910383c1c2d42d0203903004510340c6044241d126040380d0300c0060658400c04440301100f45603203035481c0c410040194151103551085003402172280c03d20f0240325542c0c000181b401403080a500d410709001406034440039580400808002200700120040d030740a40d030755400344800c0d0b5243d42c0c04138610b100380140d410052441c0100741e00380c400d500c1c002a6221424510070195007404810030700680f002c1c469600e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 592112580 1250 592111330 592111363
    0x1806030c0e10080c03060a0e0c071103031903050c0c01050709081e120a02120d05010e0f0f1302150a0504030c0f050109090506010311070f050c011103070f0c08031317 73
    0x141311100c0c400c000e0350704000c010b407001c038440e51078100e402c0c048030f001c990b00214200003240300d20600a500d8401000c0e41400d5025500e0012080384115400d070003401d56105040e02d4102044401c03c0c00d504070f841152840000304414104000d0050006510f4454041180b04250070514504d8650100c000c07000da003a0028555a0710300554403a45821a100c1e02c019401049400c882154071a00103149080c062800021070b98140180e0071103600380602005503601c02c000410400c0c00d400614603400c00d80054001040108601c000b4500c14552500394031940e00c00b0801e1404590440c0113802902e205d4070b0030400440d01c03000100c0340321145200781070019910002c20003161110b17502c0960015010f14000c9030000c1c6c0c032980c0441907030101400300c4243c1d11054000040c08000d100100140809207061034640170394684603170f070703c0c0914a0094020703400c2c5120a401c011704144148001c205a1094a45851500f224104050321a12410704503117501408403049440100b11200d98011010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 592113830 1250 592112580 592112597
    0x406090c0f1d0d210504081c080c031f0602100b040903051902030d1a011701050609100c0b0a0e07060c1205030604020714010b01030f0b100c031806030c0e10 69
    0x6040104000f80c803901901d1001519044083c6100503040c01452035400c1e80710703a0354940c5824001450b010550400c1218040664200103a4a07031190340240c11000e965002c50312030f102c43d490301c441c0590340258030314818103000002813002c2d004503940ea0841009070003000340d40b215905201c1a00d68800b002400100200b056802c144171700c3c000d1000c030400c04d00c1100c0c00c20ba0080700e918111005803100300001c0c0c08442e80000302d90381c4542803a07040f00e00790424007110351500001c5105d0340200319250f07108145900400b80380718441c840d442d1049400580040560034014202c800520b00018040140d0003540310100d1028050403c00c0d800607400401c411080102d03070811202604050507207588540c003000900080703044a0b403295030262000c0d00004821140700005170407969060012607099090240e1030200d555a005001c252195034141103540d0540c81c9021146100194004940f652490300045640e42c4c0c1a8400000d0000b40d407181400d0020900c20440300254a2180100055042 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 592115080 1250 592113830 592113887
    0x50402030129040b0303192a080d0609020c1c0e0306130204180308040807060b0d1506050111100f0605060c010b04111204020121020705010e0106050d0201090b0304020a050406090c0f 80
    0x7644230040c0319030399010202c1c1ca07801d0b03031000e002d0302030a02c441074801130b001203000100d040c002c2c481c0300000c0403009c030110715003400e1140d9030b83c0b035a9128021385022560950300419080c043c0c40c0940c0b00c1440182500c0280c0741c00c10442007410010103090380950716200e080c4000c0006569030303074082a01511002c0082d55155075002e219404004129111521005d03802496102e10382c0c2c941b589417184a0340c0750700c501c80b84080d00403248254403440c100490f225403504120000710b0b01d0b02e0f02d80c032020700202d00000302003145806080d03c2d07480550000d900240c007a44020065100000461088805120140300c401825140e401011054003515480c4000704006602902c80c40b1a40304102071100d4404201e41d01c1c04040f6040414203441c565140d80c403094800e2030a04c101c4024000071144004900d200703800003407040849014181c1c2000c4000081415507648240a10040900900c103200b07280c1c45402d103070054007072525031001180c403000011820500516850540c101003840f0515200c202 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 592116330 1250 592115080 592115087
    0x50c070b0313150609020406030504060f050601050d051509010807150207060e100908031b120a0c140c0418030807030605060d0209060f03090f120319050402030129040b030319 77
    0x45400c03500060b40c4d880000307021049800900f0080400f81c0b030000b00b902e05810150240c403e0b4208000200d4035010800410380c0e008410746040d00341d00322001510380e68002469188007200107125500905e000000035a00784000303060004d9600c0c01d854035100e07151128041c1e070b5584460140c900032a1650001e103105080c842ca035198220210b150420215035106506070450344110000c031920340703c500d00200f12290421103414640340040407246406003440c2c0007040ca0801000051400040d11604002407604100215184200070810044c0310034800d00b001100344a60022004192440e000484181c040e104d450111030000d40500e140c181000f613180025440340303a03030651215003885011102210307400610b1148940b14005e14056419801081c5420ba80915020b50103004008100e0f04542041c031400030b0001030400889c0507199440040d01400e000c005d44000000d8603803041ca00d5144102010018075803c0d40c04001082495090549038811014501c5445200303800402941c1e10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 592117580 1250 592116330 592116353
    0x6090605090303070f141515010c022707030e0303100e13080309010605040525030c111005010f120f0213060b070c08060a020301030f030c080f0a050c070b0313 70
    0x40c0142a00c3c0390821315540c0c41410b40754100c00f600d0345102d032030206c007150100300911581220080c5031943c091a1010040405c8001d440c83c050401c207041040c00111345076604008c0d60b015201d0700301070344800812a5200300e11421910100040d0078076920b2010300381e004c0101c07400b0724459201d1a01c40d40c05c18818580d81c84003e0b20f00f0360082000441c1b1000705800300040e40c00b440c1e0080011825601d0030041009072840a03110410108019a442107000c5030000070b01041d8146084c081071101e82d40e08140d40e60a0b44054500c4503008411030329292101d203902c01410384030302c03443c2040404d0301c2e14480280a850704100809860090400b000586440c01c1c8200d10b040050901142194440d100189144c00181044901c1e1208500c2802038110a00810f9403002c85407004604645c51a01d8005251070301d104050b082c45041c00320b103800d011a5078100c91041e0914170311640e0711004540020302d541d12540034042e06d4002c244000c1020702143d0103c0b405810049000c076140446d80c1c07588481d07a031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 592118830 1250 592117580 592117597
    0xc0f060c0207080a030903060f050c04090f0204050d03020109031103090607031b120c03080109090b061c1b030b0c181005160b04030e0f0109180e0601082506090605 72
    0x220b00030000920a8081020f2041c80b442941c0d03401181b4954540310082c0c5481c0c0c070040b484907061100f04011300d4610010340d002c071000d0070400708915810340103a0009104940000d40c00000750304402041c075030150400c07007202e1b100e541c0c0c20300041007113445c094036401060001e07035210070100b00f92000710348030341c0c0c40301c010044031741003009075840594504041410a0f075804012641c6480140d05054100345000e0040007038610600c0070103002c0d510021044001081e140c800c0ca60310000301101d036035003003814022940c801c0c4024921680d4000300c45110103544421111140d14038009402e500c4a80c2c1078422516461400c0720b8509a61000c01c00800c42d42d4405d101004414020182000150285c051040d8040c040781141c50802e81001000700c81c218400c00d0140c4400041244140d80c40600402110240e290202503581c469a088000e003010440c2d9802c45d100d00030003c40d0385800480c04141c1c2c0120030100d0f5005160304180c0d0140310381140314000200d14000300070400036000d04001e10070310 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 592120080 1250 592118830 592118833
    0x2c04110f030705030d180b09030c2803060b27040f020d0812071d03071503090506040803010504381519031a0f0f06120a020a020d0c0f060c02 62
    0xe0740c80d50f0202c2d1901d48900201000210003c6114101038125542c10300a81a40050a840c14034070101180d41c0d6018810f0203402280d08403881e00d804140e01c1a104d464140a401030400789030f40b0304145001e0a00203010600c030344006608450220345646010340c2c01641c0841e540510790702d07620707243c2c0c0d00038001a090780c1180007032080d640020805401810315010282c150a080c0c10702040041160f00e0400c0021070000740484565001d5900181078000c17503600140c840010f0a5202c021405407110400c010a47c1c8640401d010030015018040d6040c0e0b9410f803002c100d042100c03d101c0d00d000d002c01821307850a42c074220700c0450040e41c100011417a124094100c91007034440108003441e0344c0c01410b00c05165480b01640d6003049500d40900b4040b210000d070341540041d0762100151a0043d81b4410f5031080c1c8a40c0c01c100308a443e603200703031010041030304016080ba24203000310740040e601c20343da0320005020703000d08050202c2c0121a8200c80b11780004012000a4850ba1a50028503280c81e412055 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 592121330 1250 592120080 592120093
    0x3020d0809090f010608060d02060d15080313140415060c03020c0901060806091b0a03021e07030804060e030a08060907020703060627052514042c04110f03 68
    0x30b07448980156010703410b5041814941d614048000303201e000003400443c0b06201240108026954000660301c80c8643d0300f2000074140c401d44031a41e94004294494030302c5000100b924460000036001e0401100e1180707900d4040a01d0210812003180c07030125203c0d60219502e00c092100d2071240c800d50028074401c3c0111317281084040c000030380c2c461090344800300065aa008100c11fa003414100940c029605c5103001001145003216100c65000d201c5200041682c0859100801e031803042e96103e4450402c9150380d074500040c02e00030078040c03045805648180c14948500681007000041300d14525003551a841982c0b500c0040100740c80c0d016100c2c8085225494021000c52514410312009040c00391200710003c9456400301590108603c02c4004645800200441c402507280d907210110303101540e80c000665002401d950a110099640c654a4008034000c1070680307464114240145e440724208220a11034008c0019250702254000c10602d039500000c901810a002c8c1082b81c01c000038182c50f075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 592122580 1250 592121330 592121347
    0x30207030f2a081506010504060e06040504020304050d02121305150d0609020d0f0209100f09081c11030324120a08030618010303050405060d0f1b020f070e0103020d08 73
    0x20546034070b540d407041c0316100c0c1c4010024060b0401205100000d2007807151050b240050010340381d0301503480356000344030704092084803555841044401170301c8010701c11034607400c0c242821956010503848000151003403002104113a03a480040d51505181c10500380700160a000c05c0c005600008611580808018883c09004000d1400b0f036001500054400603100d1a200c03480905480c09449503244180c0304001010007a155542c180c0c5d0600214140300e08082a00ca074200c500940580c0255070900800c4d48540f8203c5c8103551102d0900d16940c2c6500310340230380c6c0600544074030050301d413109448005409000784a4401c25101801100142003207004c102ca03054490070711010a070202d4803030344000308119451508010403881181e001080c0c0320b1a6040d6030b4068001c3c881d038001c00f0320913030020400c2e004a0340d80ba005544103807560310b403d001c82d01c0e0f8002032050802d2215901000b502600310140e280c050001aa80121614441c0840b02a4038503000e10401c80c400b00c1d02078520450420031080c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 592123830 1250 592122580 592122623
    0x605060a080603010b0103060f030807020315100f06031103060d0606080f0606040f02070b0c0706090c0303120e0f0d052107080109050c070f060c0e12160f03030207030f 74
    0x3080e100d26858803072452030034504150841d01031184040c10726180078824449d200c0d01202000070340382d102c4043c940c5c4022030b00010b4540120080f1220120b0006001c1046d440024080c020464541405084580b500d440d03040d8242c44040507280f02d015820f000040300c9240070990b09600d80d0142000044150b101c000250a01104c9a03800c60143d0224040c0000d50410740700300c1c0254052010118182030030b80d80c4082003ca0b010380354101c2c0641c0802e00302c040c000c10740d0020f50520352090424004558034500607020154141d070b2105402e103000c841072212200803a0300540c0c1865a405401202043c501c261010b401402044801544012000200481080440740030710804c1d03d030041558903010340d10058410040440400450030b001d803000156089601c0c511030b55000300040394100b0341d80c10443d40d00cd590789006a0242d48800d9621440c0804524064a404c0108851100546520100c40781e01011b110040050703000b00000c20100c1c00c0810250300c6035104611450320340d02c1d1f00c20390b030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 592125080 1250 592123830 592123837
    0x806010525032705091005030604020d1109010909030806030625140406050306030d0f0206070e0d0f0602210405070501141c0f0f090c0306021e07051b0a08060118060506 74
    0x3e80300104446000c0c01640b40003c0c841e0750018402c0c814400c050b05000103c0e44078040507100030300420200300100c1c1000608482181c40a0000d84801c40d20369445203148080d10741c0800542c041080900031800908000c15114414003c2405c110740e038240130b0300d8562101c0400010102007180c00051010320440300001400207161541c0c941c1d40b02e082c800704050800302044888403e0024103007540ca080f42e004280b10f40e00034540c1c2800c40c0c0b10030154010442603074105800030080b034050903400302000b003180c0c0580703000308858911141e4000301d1600f2180300d00d410b80b000f4bc45940082000c000540c03080c0c41951600d00d60400075801c3c510641000c0b041c68a90800841d0000d0300d501c407450250010748510303207611701c901e08103221144c05a112070440420074000500340c2d94000038032684941c250318400000c4d980c0d4600040c4c0c2e4080a0402c41d48440c0200c181003845030311011035940c01d143ca86050000e485016001d002181d192810030f414500090f10b50074100c0782c48200000b81c650303591024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 592126330 1250 592125080 592125137
    0x2031c0309080415090e15132301061808030301090515151e04120303090201050913021b0d02060a0f090f0302011a150702090c0721080601052503 64
    0x5400241307005028004000542042c180c1d44803481c20000003082c5101b41421031401a2812802d02d0000040d400c06000e002e455141c1c420048102c1c402e11840d8041709904a901d00c0d07841c140400711220405406202074459410254014801801aa21603900040d0000360006000c5407030804080400d000c683c1a6030f04e00c81c0700401043e20030301c640c0041c00990070580b14442561034175042c60600041903241d00c50150415980f60612011a4007034402c40e034004d40300908050784009003c040704080c2d801004244034429010a08800703045000032508c0d4a41296000f41c041682c41c0c0154074024281c0d22484140e4540303480e4002e010610380c2005035002c502039030002ca840c1000742620030180441c2400700303014030a10045c00c030090200e0703801d032a601c80c7e040343c200c002d40d102d402901c24180905600540b07460103040c42350505040103000c480d240001034a98106607640c80005640500941d2050041203102c03207048035424946502c0021014400c1c2001c020041150100c43e2585048210 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 592127580 1250 592126330 592126349
    0x20c042d0e0f0619050f01060e0102160807210201050405060d061d070f02060105030715020c0303030c0a02060106090f0b0304020d05010903030209120a050709020c07090e06010e0105010c02031c03090804 89
    0x1400302070384181c00200c44d20a10480f0921140c10b00c1d8104801a9505100d000c08000b4040302c5c5040716882031182c00e8581003540011b060f896255030b03500b41c03689254810700078080f500e0107500c006c56100d80080100c12703405840e014105490101400fa01d50320468026460650756a008200e038102e100340407900c25840c45c2d40c401c00b40b800d00f001805884022a044e030940d400780740100600c0c0c1c1d00007000e03403d8910b001e0080e4094840100141d103460400c2c3e88860380343c0004400c00c00e11284940103008040340a508a0700c1690341c1d490281d410030340c80d028251300c051003150103200b00c23030444d001035420500c0608200c0561086841c2c0c5c1c0d085841d0014210300003500090103810600d800070556100843d09030240c2a40c0d18507a6031710b55101868030540300e03116004a40c003858414148454001400c00c28000d000002110560540307e0100340103240740c2c016041b002040ca5442444c1006030700b039028005010500d1034030440312900c6401d83c00b0780201038403140f8600c0054100c0300030b00018580d490 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 592128830 1250 592127580 592127593
    0x110a060f060f080f0a02040b030712080a0329010507020f090a09060e01060b1b121209060c0c030a030e030d150e06010809030d0911060316020c042d0e0f 67
    0x9544280c1604540c0c4844403640c44004c0d055100305000c44c0002685034100c0d0009400e83e002000f1030305000c0181c4c000d01d05005250310754002c0c0183c50008240c48400c50340c0410041c0c400001c039002000802c2c0754031544202c02010000303e07501450003401d400c0d000801400001042c0c00001d50980400c0712241e00c1c594440054004000b1a030003030341000b98600000b848224140b07070710141c450280341c1e07032410b900f0907030800c0500040381880710300c00c7c081440a58503550f09292401404491090300e40d00601d206e0300c00061034402401d806d440d141064100591300e050284003048000e0070741850000c1d4903010170030240008248034862540c0e0070b100d8818501c5500c3c680740c00840355000040074141070001c408200040e007000031040304c00003d070180002500c402c142c00c1c00c0b200b0b0240c0b880c40e01e40180780002800000e00c44078200c0b07c042041a030840c0e18004003102403101b51b40b030800c03440d80055540750b1140e001d812510700c84c079000c00c2c1018000030300c101009501842e2000f0481603e100b9080781 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 592130080 1250 592128830 592128839
    0x9060e0c0f060a0f0e04060306060e07110c01140a1206060207170c012a0807081206030a0213180c06030606090e01180e030909010602062a0307110a060f06 68
    0x12a4181440c1c108603882400d110150308080e040300e8106840e80700b040401d185078500c0c1d584960108015640200301045200d1b01d0b01c00c9036501c40e90036101140441c6070062010300010000890604091042c0d4038000070041203298440b070360300024504418000803100b202c11050040c858003006094941c01480214038260750030406c400207054160054001e20700f46121641c0284100d00c405050040007000e003040030300002c7d04370420140c002d010b107a0024611043c865918090030780e400b5442c180142c2034541c14101991001c0c0484000c2d0403210040c0d03001071035203481c1e103c3c581c0000a800042103100d9240d40e202119000c0b9003114000c255140c0b4244981c2e030784103011201a19803402c207151154144a841c44041e1035401c040454992184c0034a04244c0050060381c1c8241c102400200c0d855840300b001945400c022202c1c1f020031008001e20407204032b120006440440300d0307050910300d9911070708070403110002c100050040a1058107016000550780744500840c01d81a090000b42d04be052 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 592131330 1250 592130080 592130089
    0x130c0f18050a03080a0c06060902120702010e1002161b0305010605060a1d010504090203041202011116140f06040302030a02060105040b01053709090c0801030b0115020109060e0c 78
    0xc0030000300350624260911254680b101c0b100b090340d4000c41e142d030711900c401900b210341600e02800185000c0c18070400080e20007094000d09071040e1888e940d0f5200c0da440d00d41c22401c07208042d070744941d6035012500d841008076103680101441859080001007507840398481c0c0ca1381040700016210060031452040040c04828820b0390090441103500601d0141c103071100805560000c165200c0c2c040786c011860001703a02a000700c800900b41c0790400d644074603250a10624441518144d40099400c240e59141900a28001c13110407c0c0c540c80003016010300b40d02d44401482c2a0554200c951080039600e0144c00c0c400c100d885d1160f8440c1d8002c5070383d00d6280c4030080c18402c06030322490095080c03d50184c2d4607a00003003901c501013000303902e1008440106004c29510800c0001b540407808000301c83c1130020b0381c08203648040e91680e038000e2000199800040700c40407024840a011401072100500c50064683c0d4000800c080340d10022880444545481007258030b2070034403e09580c03140c4091a242e051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 592132580 1250 592131330 592131347
    0x8060405060102160e0718031505151315081c030c020a0b0f0613020c1014062b05070f0501020d08010806060609031903030603170901050a0e130c0f 65
    0x742032015010142c1d038044005400c10b128002c942c040340c550b1000450643c490101c407018a04107120080300f255890030000e0901c0382e0403009120039400c0c007001580040c0b444001038403210f07001e0302c003000403040c60150b9001041da2000d110f003a07c040007000034000d10104541d1903045900d4417507164841d80c50b80007804642c4410b041100f0342d0004211200442c1e0071101280d803060040e041080c079603946a0010f80c44001003070307540144e54804640c034205200002144007001028490030000700c04980c0d42c4000a09048803020307881310020303148503030101d10f00d9204c1645000140705000507844076642d0b181040c840d60072414810703910400c200000e40c0d0401c000700e05604c19003005055541401001034440200a003d10301426000036010a0b40c0c500308032808450301c0d00c00c40d00700d06002907c0c008014045030320080d00c1400c040021480b10b41d41042c11544010b405860f254a04a005101551140050040903500503880410035a080b2841d001d0340e45665240d940d108040a0a69000f800032350 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 592133830 1250 592132580 592132591
    0x15060408100e160e0f09010b1f11010e0c061e0301081f0905100b0118090218011404030f0c030f05010e01050c0c06010302090a1e0902030c041404060902031c08060405 73
    0x203c0982c803c0040707055044100340c004803041c0300b030025550740d8003a2031701414040032641c1d00310b201506040415042038000d4204d44c8007513620604072114080c0420b0a0b50591020034455812040550384603241c550300600103101e04c10b80c240b2820001080c0d525164100341c0c8005046e810803130320160400b1521100080c0d61a09050802102c6425110b10355600c00c10001443c1c010b50f10500074580340c1c020841003104260310a040c42c010f90701d951002003c0d402c07010b1202442e49000c00c1c800d110b076004411010080b03110400303036420140342d0b841d0090705210141040d234400b0b40401001c4041079408045080300c501920000c076041003c02d0450f03003118002003c0381c044000c1401b04d21400d00001c125075045135012201c8243c1500c075903000038020711110403103900e40014101d4182c0003000e55040703418181e00032030a13101612000d00600c41540d01c1d0140d4890010005800140010132a502140300140082c003101c0c1d000307400d41101d1a0361080070200318041206e00003001541d00d041e019413603100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 592135080 1250 592133830 592133863
    0x915090503070f05132915160507080c2b0804060203120a1104060e0f060a2d050a030c11030409060512070b070b041a01030f0318050915060408100e 65
    0x802002c0b0321b0304402c644125103c1c98107440300400710003030f03841100516010701d1166810769a144940d00130150b0128800044039280911200003a0036000410003092405001e00741d210a01106034000c405c0c83c420603c0c03081d01c0c243d551032604c00b084460014002809858004540e030700300c00b00d01c8a0600714000c002c85910b40c2018a800981c449200c19241101c91074204425521f0444000540c04c2d9140d051b40358114401007412400c155000300b0328285940c80303141c606070111030080e11040d032000350704424006c1501004441a190710aa02084580100745003d1000096032202e0300d0941d8070551055005a8a50b113082c06103150004602c03940c80d040070000d02e06240341400040703c038052540f0151448110400140c1442000c0d54840c0a50f15108000329003582c5920b0074032510090048180c0c0018904003030300c50300604000d094011b80701c1c000d04007001d40c2ea805078600200816030944a0704404c00303120015044004200030041c0e0030032004081450303049080d0740c500e0a505a510440c0c0c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 592136330 1250 592135080 592135091
    0x10303090e0901060501021c050715090210020c0d0b18070321050705100c17010603050420030a0b06010c081303031704030815120a03080403080702010c0915090503070f0513 76
    0x140e0300011500072442800b104002c00e40c44048050341c240c0900c07040034084507034030b9085c25a02f407916841070700b41c00d100f181d101220318600c1e11300701da9031040064004c0d0008a08820703040400d42c038003000759021660032400354910390721041c7c1500f07009059008841180400c541e607411602c0000f54840d42e03d1316454910b0030510741c0e48a1701c3d55240b2042e890f40c022a41c1d403071840c01f205d22030060f0341e641c01c1200c030341081c542d40d4508006005120803a0142d50600b6019a5034600007002c0c050300c0d801c003400800030000440b15032a82c500b80310020708405d06000440040d1000a40307001e01503c1c00f0814142e44031001032a60130060148d03855030a42d540968070003010480029000201c20742c0106405400201c040d1982d00484c0340300b0041054454035210b40c60381c01c2d0416034080f00040c402c030310a955160864441d064141e007a01c0085600c200843c90040d400d0180141c45205000e10340ca080c6020440242c1d1980800d0502519800c2160744010840052005040c0459043d583c8985031204012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 592137580 1250 592136330 592136339
    0x70b091e0709020f0702030d020f0705010302040e0f1f0f0f0e04120305090102120114012d050705010b1519020d1b050c100309020906040e030919030506010303090e090106 75
    0x7180e02103801840311040e40480c2d10a0840845000d50340300e241e0140889816510340440030350b03101d000703110b015000d100e44100442c980d44039000340c038216815071010011030f0304c8401c1c201c86690f90082202145211040c15204503000303c1300450010000504410111410701107141c460412503004882d40511040c240000903000c510041085401480c0001ba951104003130180a4070500380034101c442c0e00c042c00420001e4160a04c048000c0e4240c860030200e64020715103441d0700d035214100344503800486180000d190301610080c41d005206100001d2848405800030741080b0740c1240d0040320110101e58002c00344801440220040c42d6800205150344211400900e60044406040e55408c02c0020100800408005400c2a070500600e02d0451058596000700103000074a41a0b1042d201c0c4030104009003002d00c110251159154051072034079008c44284005580b00341ea002c10100da00c00000400302e482802000e000c1d6201c1d649045181e403401c1c0100b503d4441c0601102641d1349032060400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 592138830 1250 592137580 592137583
    0x40f060f05060a0c0308092a030c0307080607052d0406020f03070b1504020c010e01020306030d090806060402031803070b040b011d0106140d05090309010906050412020f04060308070b091e 82
    0x810170790519103011a43c0c0c03440001428105282d100c05a22132080c0d68010030300d407421515035600034003641124070313607070740701e410161f03510704521403518290481c030041011a4852402864800603072100c0110381d444034080c4d0000c0454103001c1d801d056102150a104296041c420180062581401541411070f141c59061801102814070024254101300304082c6440e540c06803004a407017480204103651741c100106010750701c2150054403901400601c5503a4901a50410066645410007072640d551a001804003d46c4090b0000f030b1824907075682190b96103800c100402060f0b1281e9080b024134101740c07030038601201040c0c11040301d990f000300f005e541500c0f0b0414081d0460b052131138400d0306440203105980c403034810a020119403d00f09030402c42c0e01140040180362400c002ea8405454681d5014121014000d13800b0350100c60307169880c40707005490107a504046501c002000010340a0740c969031070b1215404840202d800b030580078100110443c080c41007018001403600180c0100c228641540e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 592140080 1250 592138830 592138847
    0x161a0c031302010c12020a0b012c13020901090f11090d03080a06150c02191a07150207030e0907091202060d0e030c0303090c0f010903060515040f060f05060a 69
    0x40035145070740480003055a100703050b80d5881a03000306100a5001907250002d464250004040d6039402990000203818000c0e024051451922643ca2816080104d910451982c1c40900599080e50044c083c1c18050307a0760300940346c0240005c020000c1c0451040309020141c566458824101c1181070000071410f8544940140000c2d43c103143c42915990358070040c20081c440b43c1c0190000480104110174211b0304483d0140400d8021100381c0c80322a40340c044010f0183c034900903039070100220081d840074092403201502565106484110b4040c40d51404e18089801c13503c002d40015403130030300c5241d00381010200302e0303008007644c0745c42e1010505000500007503106044009018104c0003c0d1250840c8440d842044100b500a040c1ca03500c207800301c0195a40c2d00152140c024a0056081c00200b034a031020054810100685a403010345186031104c0c002403000804010311640d410641c02d609658078032030122001d00c01600012a6070515800b0505549a6005140504410000074400c1d94001c03929 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 592141330 1250 592140080 592140091
    0xd020d0c020117060d150b01030b0405040203120f04031506090c0c0506060d260a090f0e0402040c0e12100b0102030304110f03031e04030605060d020d060e0111161a0c03 74
    0x403069604e0b82c0b000308900101102020b00b1001d071702075810014041d00d802c11400c1c903509170303828401d4940900400c822604141c030000d5065020702a1406028015005040c103802d04d07521081c1440d40d00d03151607480c0c144102d1924510399803441e003440101c04500c62658010081e1420429000386170b0342d0280d4400003d0700f213a1080d40700da50380c082041180c014694203020041c644840030096520005800c0d049002c03040b01161a8180200f082c00ba03e20405045400622102805881d5038003840002c10310b802208081041001c2200e001d03443c2c002c684600301781c1c460010324101141c1c800d410202d4a2000341e003030443d0030800910020510b080719000000c00200c40300f15050446d8170000b4954400c00190304800010a55403500805185e405401140d0107200b09000e40d40d510010012130b1800407400941c0703c01001001004201d1590000c01d034501c4000001034a04400c458100054000f8124603001d40d203510b81c500200305100350322440e081d01222002001e801d0850250905000080030b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 592142580 1250 592141330 592141367
    0x180103110408010911180c070b070c050d080103050f19020f0402070b010e0f0a0e100b01030e0703050102071e031205040302031b0102031005060313141006080d020d0c0201 75
    0xc411110a41104540003001004000c0088884503e40350021161140740e00d1b00c41c1108503444001d400c0b10001c10f501c01e401d00841145800500e94400540510180c108030401014400e0140003031001c20003000c0e1421681c44103801589186480d92411540044501e03c68100f0305c503270410300031601541c41400b80c0c111480b00b900004c7c0c06c0424024058050042c0c54a4424000024038060107072605e030040418440c010030681ea803003007900940c1d0b1180e442c2c50310395025a01350989814154045c4041c500140340214410b0300040740c0a03e04542600251840c1e5070000d111020003000600d54100991601140c80c2c55805940340a0080c1141c80203c005041c2c4510004013054824000c642080780e601030502080c2c1010051103000b0741003118103422000380c08070041020319040007035038403038280301d003c00381049544d65942c0100c400405180d850351040d204840d241120300d0203110064021000201840186074200901d0041c0241054017480251507040300540d901c0303803d0b5021805802c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 592143830 1250 592142580 592142591
    0x51b04290c0607080403271e05060d0c0e12060c03070216030f02010e041e18060c0e181303031a1f090609050a0608060d0602120402090903180103 64
    0x5011001486440201c0015008210410000580001069000d41e009540c1c0e820505207031020089101010f200030f401510040b60108100715050030b8102583d160028640c03180c541d140003190190f082110310070800c030746607240301d42d8065004002c0080e00c10101c0d1f00204091008045036224036024000c40200381d400400510b500d4000c200d03004810340c40c0350003900e08580c0c908001e000142144001c900281c060b503512010cc0c5840c0c0160b8a000b103040072132810612081d42c00030001c24400e800c200e102a100065040854064401c420705011661078440400081908002800b6407019019442d01100b0050005126800302d000b0405585802c0010b21000c21548040f0852440301500c1e5000c50111821030903012a0a013481c0c01803030b542c030f801c100b503034456a081e5544440c50250a03001002042c042050030b00c18088103400c800042c0198800b17040c00c0d02c0d060140c0e840440003440d0003000c4811b110031410219032041e40100710101850800d0708250440c1130b908202d9901504040c0c440e07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 592145080 1250 592143830 592143899
    0x4181104051f0308040f0e16050901030905060c030f01170319030b0904061d010e0c1e0a0e100e13120908031201091506020303040303110906030a051b04 67
    0x140c00c2c0b203104440600c900d800300d940389002600da52050103140c1421150407000601070001c0070034240502d4912070701d6420816481012a126004081507904141d03e52182501050041c040b2501448200d03100e141c2d01d02d07003440a820140010307482410007440301403003152500d03c04815a0340b10341d8200085c41c1c0304152404120090030740b00c4072055010302241c05010030403995038060090b81c202c8a42e40d8100c450324640040c205e030341611650440350480075050303c3d00d19250350b1400740d801d84401181440030b10900070440404c80c5030822032582c03400809102182042c81c1c2c030100100130184185401c1c0c03a040c034003420865221403004101e0f00c03841091204040c0600703840310103011100100c90b1600b041c80f013494907600b020b10600584034507000a61f108007008030f6082c0281d0b0100c0d00298034540300c0796811802440c09142d40c034481c00d030500a4481542c1c51000550080a280c00081ba07d400e04504070345101c0d140006620700004c0070402000f007900f01080490040003148441c0380e00c1c0000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 592146330 1250 592145080 592145101
    0x50705121216120e0102010e0615090c2505070503071d061809010f0e030307090b0c010209061206210d2106031a0a05071205130b04030203090418110405 67
    0x407000080050301e11a0500f03098a40c080c0140c82d40242c240d000380903510001d03105a4070b852043d10320820707184010034400090309180f003055401115441c02246803900b554031015034003103011860184d0a009280e540240720042001d500949022006031101e10702e0710b0f8210802c01c015403035018072540140000745445d130721007200200f118510149601c00703160009000d8000c051140c02088180c0c07921070781d60b400000000c26203203c0c1c6095140c4045a0f030800b80c8040c62604002d28450866400704a4802140c881c1e4010703012802c1480a8404103050200400003800c0559402020b403203000b504000812074001004007600c0c141e030400c0b100503082c002040000030f80740f9101c5203415050080002c10040a009521501c581898004000761070300f009550aa6005a8460001a00907140c0c0c5410045503131125410004441601241780c840c1e5845012000c8200c40640241e0000310316034007035081500401c0401e003204008801c054000c1d588036003c4800700a6510301896030b840000d04103a44 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 592147580 1250 592146330 592146367
    0x14010315140c030109060e04350c0303010f06030b031002090307030206220b0c0a1217071821080702011b060207061a220f060b070507051212 62
    0x281c03416115151030b01c0310204031250320078030450442504d0520005030341d041c0500140d001e542c1c44401140031840c0c15600301c1c5201c0c201d12400c0c80128180e500b0b200a407001c08014000e2040c0b90020390f48035890188040711551983e03004009060070680c0301403050340c0202c3c0c51000200007850040e160059440401e14004064200a420000c009004240b4401403402c1880422071509101c9081c0d0302c880308401c10303009020000300198000401003000421070a0403a02038105031170610441c0381148240d8074400e1044e41c116010901e014210301c00301d52107a4120740a0701035142c200082c1040780000e1046400d0040c1c02800d020300114201c0c045a10a8001800b14851010032954413441750512100070b5001540c1220700c0c40c6042c3d101111101c00442051690900178903000c008020308038040304a000c494200740a0660b82c1a40f402c00001c60b2044402400c850b020311502c550b41841c0252402a403508124898035420040d110002d5000072100d080705c01c2040c10315282c880030b02d2000c18861 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 592148830 1250 592147580 592147601
    0x7050a12060e010f0f09020910050d060b0d080307050a021e030708031305120c160506070b0a2918160f03060302030a12080f090d05070206280f0314010315 68
    0x78103054101d41140f80c03640146c0c0c84240200d41c184566100d581001d40d050b4014860150001d101c1c003621004580c450b131200c034080d90f0182564440e42c00c1e036550b40700d055108442600120708041401d000c41c580c1085810a0040054000c0701e03800145940c46540780070303a142c01040060b00000007510302c6541780300642c601d9482400c4418010282500c018103803c0081166a140300e05206d4180080c6548006002c440f00070309040d10308100c0b900c8200d44c088008160814680c1c644004010088020050000384000d4111140310b1221039420410703000d0502c80d02d00000e20303014050019940b01c0c411640707815141d80c140032201401d030340402c0d000307440381e60700181d810700415001c2803d20298034682c2c0c00284581e07035070051903550b02c043d500c0540000e6688068a6012103020f40078980071788010860b0f2400101045d0030804481904031082c400d83c010583c4080c00d03080b261100c40d800010042e02c0d221107040500c1204a5251490341c019014880608056108074481c28407071702d9540701c1042003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 592150080 1250 592148830 592148861
    0xb040b15032e0b0304081204080d36140708010b0a050103020a020703020f0a090509030a0206070206160c080d0c020606100509010203030105061b1e07050a12060e01 72
    0x146440303400e09031900101c1d41140d40721164042c50040e003115080b00407030000341020b1154564100b607210300359604003c0040398040c204000e10650303034504409661169100340d21035980c9480158411080e110052580100300402d45428910050781c10800420311101980d807403106286810031000381c5030075402180b100d00445902044004040d008208085401d40d042481d503503549004504034401c440b000001a001103006200510700001c000324248401000419056150040c03041111000d4408103800c0d4400261181c03640c0d014072403150700c040316001074202858403c0e185140100c40002150422844812240c00c10061905407804071100b280104095018004080c2d42e0325001c7d28989e100d62501200c01c0001840751040b03400081d410b82c06541543d11303020070f110082d081440741f201800f000a5401d801c42000704540c140d000945a466009000c101508904205494000ca8040c41c8100e000b486a801c4841c0e40c042c500340d0142002804003021117105e8010078400d6500c0128 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 592151330 1250 592150080 592150099
    0x90606120b0d1a040605060a0e1503010f0e060910140406110d0516080901020301080706030e12030903070b0105150415110d020c1519051309020d09140706120b040b 72
    0x140c94031118a031300c200c4c410b01c0c0802068948000b04400070344588607103031490012000042d099a55144c10018286020300041107014003201004240c41500400002070f600c14010030280701c03403c022121044000746000c10401100c0e101c054207245e0010809071035961141807041c0148215011075207002010745007000b5a050007180884078486041c0c02200044410000c100c0460707040c03007100d04841c0d858000340903042c504003084d4083c150424010344c0302d014115181c05041d1080b40250300c030b00400c00142d47d89240c2e40c9061840e410f01a007205000b00c07108103d81070300c201248100d509403901c24a4809a12040c2e00301140c2c071943c6d008488031940550076125005940016444101705401c070b0703842d0150242103580c6020703400342c020300f5844c05108103c1c03024014025001081080d08810400c030b019600c540c0300d8400e907880f000e024801d85548141c1039040c0608c02d0810651502408041c100b6946810001400003000d40520450180c0d5207030b0390080f17642c89070701c2100c2c80344001d40101c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 592152580 1250 592151330 592151363
    0x6050d052203051c050103120e1509010e0d1a0603060c0a0c030806042307020f0a02090c0304020d060e03030709080a1a27010906200301060815120a0507090606120b0d 73
    0x46021090302c042c4080760409d4110481807070b1110300c00ca06298950882414140010011a410720041c0780e542d8006990460b4100881c400c07150b168000300b46251100c41c42d0030704a091600d843c0b8000c0407507106540510240340b803035600050400138541c1529100d14503840c0d1000140040801141c102680341850b01c081d0703c080e4200c0c261920070324180e000d8443c0c100c2c4100c4030070340354004204003d6001c1d003204c00059880840b180030710340003030018148500301340c600c0c0d0700c6000b203540c15985c800c46580088100309640d0792128000d000b4199002c0500116862551a5040a41600d070000c0441c029a000100800300300c24008074103842c496040384000019902c0e41e03008001010094501c00d0408401a1801ca040c0760700c62405a0030690051460b13180c806c0440300c0d01c00c090702505104000d0b00c0c80041ea075842280c04050040b95030080c005101551900c18501311199000301c07110390614004006058010b500c1c202010105003000c98a01503d0002031050040780200400300c200c1c5420f16407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 592153830 1250 592152580 592152593
    0x3020307050c1005040618020a030b18060a200a0e090c16080706060b07020603041113110d051006020c150918010305010c0804120c1b06050d052203051c050103 70
    0x34007450240c0d604210402c3e44040c00308007c41590000b035003081c000b10b82040024203481413140d2003030303440101c000700b1031260b80b00d035041c00300544500d41415290340304120031002040a0014a20034940e441d031030100c68150240003860b03005401480384c03458030b0001c0e034003074070100894184512150090b800318a440c035165059400800b001d4070000d02e0441d0201b10142c02004440489030024082d9055955079a1000d08503106882980c0c2c001e8400000c106900030b050041c015103510000c40a07484d00100598081125402400201d84030060344e1708211840d00480d04181008042d20003641c00119007508100c0f80c803410740d81c0e81d005100b250141c01c4020107070950314180c074440e20090252302000c00e0100c880940903600a0280740400200100450107030003680300039445481903d076500d6248401c410040401d40c48280480c0c00000c40f250380710360610809900942144031411300c1101406481121003400070000c042c824001a0494401405200441d084841e4803080c082c035a113178a03110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 592155080 1250 592153830 592153841
    0xe0c03010e0325020117100504060b12150108011203090b030a05010303180f12021804030806040f1a012715140a17060f060304060510080d08010603020307050c10 71
    0x50001d050520140343c5490200821102650143d5464041180011160950a60140280309034001c00710340003c281d112030145000804040e1001c0b903d0b1107024900300a212402021400076110801c00c040780d82ea0020300c070605641d8010503007030300421030380b80542d00000d130358001792507200c004000c105c0085401d4001c5416240310340c0d1011540c503820020f2a40c149500c0c000c4001c9520740d04014407802c00c0d003990034910343d8001419144031180d1059820300300003060b9010b40000301c0c0d6608124542c00c007801118001d003c1e11108000f8458041d9600d841042c943c0e078114100310800c1740d0034810608400e00c800242e00740c00a80c03940c4c142d0b10420314203024034600190700402c00c52503001c6040700c2603809445c03400d5030b540c42c2c4101c03032079001680b0705a40d20010602c0c2d503c100c088040154984804010398841c0784104400116803d1422030340055201c9584251020340c0306001c00c0507865072243d815411500d050901584035141d2010030f49160040342000200c0d0f218015a030400f640807508503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 592156330 1250 592155080 592155097
    0x501050a05030a03050f0d1b1706030a0302030f090102010b03190501060e06091801022b0e010b010f0c0c030209090a0c06030b06070b040602120c1312150e0c03010e03 73
    0x148219560424183c0b5180079400280100340305100c0007200b000e03440010004180034540019800505e00b1103103d80c0c481c111308103400030300c0701c4040c00c25006000d40e40580000d01140180320101441e50300a60b40e00c50204038401e503074000300320240b00d80d0003504420740541000301902c002e100c404030203550100e69800700b03a50540c2052400140c3d01084e100d624016176010700742c03080e10f5440038100080241000c0002c0301a40d800c005454042150700c5602172180f0800d09240c1c0700500c00d403d65000c1e58800000002c1c503900d0b0200280150f81c01c0140c030b507014940c2d400c0c04490340c21141046c460096440d480603401c5010031082014084021074014000e9200d8442500c0098031000d0407412541d40c0e284c5680c0101c0100003d1001c6841c0d40d414030b81c0188292030141c6007a20a80200706070310710944003082c40f40c00100350340c0895410200214090800100d80d00302e814500c1d20703958440d1401c04031402104d60f0701c1103540000c0c3c000380402025180050002e000c10560510129944e6112512 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 592157580 1250 592156330 592156339
    0xf060c050c0603040209010303050705070b030a061409060d020904060f0218120a1e080f0c070f0816050d02012c0f03071503020c10090503040317031029030a050105 72
    0x81c00340c81c035240c815070b0f02a0384c000c0c285540503805e554003515a07910425080d41c01c1d10402e40e0003e170340100c942c000c610591300c5504c04108036151071130081795200300c20266840b950102e0100a59038580e0032110039110380403104440213444a08003c40100380001280c02c255000103404030004202e04551204e0001c181c885440002e811042280c4134194640d00601003120b001e000c0c5c44180c0c1080f0300500a901030403815260aa20101c0714104c1e80c0035004070896504144402c001843c0c2c00000d072001001010702800c02c0322034542e40300e0740e00c018a00455100316440300c07800f81564070600d04c031012030140c7c0380c110711000e451107084e11603007031550041031182d030300c150a030303021410046282d000f219140c20400014030300803902035010790000220700b0010f11450800350108202c90095100b541c2c0920b0182d5030740c40c2181841e8072050049030755690641401c00502c680c2500001003202210324038280d40d035905840b8030403002c08040c00c0d00c85c0c5400442c04030901200d004941c1c05541210802c85 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 592158830 1250 592157580 592157593
    0x20d050c0f040207110d15050f040309050d170c030c062a0406121512150b040b090402040b120313031a010302060a0e030718020903010c170a0507121a0405060103021905130f060c05 79
    0x42c100014041c0c045002001d2119001d030800cfc407801c0c41c6002d84416180201640d0828482c140c48924041d0100c0d6942c4101d401d02001c45118181990f1200c40c112070114a00e240c1414020094401204030700b00c1d10600d030313032220074011a50f10148018041e019924907402001c1c2d450505030680611450000b22461a1100c040382e00e01d4a417041a03c0390340d021302400718544d07440e0200300060a883d030607182c11101041261481a43c2440205204038202d6100c50980b402c6041080c910300481c14000d14401e180c02c011f20250360b07248240c0d4892212032400c900c2e481c80c0400802e0070f0040306d42c00558000030700b61a1111341c00710f07600600b0520078282e00030403900395014011540206164410607040d10300501150001415801280d8080d07060f05080da4494480752900381100d07a580002c032081c000d00c40030030f0b196207014042c50b50444001d20701941000301c0340d80c5402c0422024803c0d0004d2200000707441d600c00781e05030701c0e0708002c1c41084104117900b5500c41015050300711490080b1510300460 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 592160080 1250 592158830 592158839
    0x2010c0905030a022407050d180302010e04150e0c090117010518090703050a03090815090601060e030106031205130f12020904020409020d050c0f040207110d15050f040309 75
    0x36144481201c500074000c20420700641c09118030a103001a03101026100c920110045241d11002021054819002400007044000001340104800d20b014407801c3e0002100b000542e91000c400204480100d0340011040700210703002d40e100728075170f000b0320300b2400c0c40040141a03c00000909100c84081c2c03520300d450304005a104413515407d02030160f00840c1503914003200340b000c850305a445007401088400709503c98403000e282c0020f151048000462196041c400310100313001e103102800400c0602d6020341000480d45864031814010b8408210a41042032119502500508000d607040b85200c00006003000c8003c2407503000910350200d000d41d809000448072621700d075810440380281c04600644520703a0800405040180040c0d034400c2d129129840035a880006250f5180d21500c01002c1e841d50660a00c05003d80709402240701d40c0c414084c2ea00481c04141c650120f998046031101360309261840c3c00c803610021481c40b209140d14000800c001c240c07403483e07001d010314080d03184d452100755038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 592161330 1250 592160080 592160087
    0x2030901090e010b031314060a290904080c070308030a05040606080a050a060203151c0209060d03020c0906010212040b182b0606080111070209070318111f08060102010c 74
    0xa10130800d0780c0c3c1d002c00020700340d4200d10350300d640c9240c414988151800e001d005010710740300090310072546480e52a20140c4840858216491000d07400e402500d2100307900700000b562101740108040c0c00451700148590404c401400004081c40d40811f80700d40b00d0803c22441001444c04807400c580b050300e40075010070000d400244510045512a0003400079040550b141d0000c1e4001801c01d6070040d04070182c914042d80c403100f100424801c600e0440c400e802e101d004001250308080c04041c05500c44130b0203000480d602155402071400c081d10740a1080e103414004074908503140100c030100410125011400201010040c0070602c2612100405540c400c8200301255040d010800c56255000c0718600004036014200d50445024240005e001b980c0c4810301c07425074002c0542a280814001007590451070441c45058118200d0b107000c10070b144900da29082d003a210403002824000c00c1004030041a0f5580a0812020700340020009250f07a0428002c2d01c9600300346e500502650810303000400544c031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 592162580 1250 592161330 592161359
    0xc0a0303020114010815011206060b03090f1506060f0f0c030f03090f1911121605010306090e0606012010140a0c0917010b04020307020304030b090105040b010506030901090c060203090109 82
    0x2a40300c0c0d04440388d10302040790188000703c9404480064a4840018000900c6800386110704c035620058115050541c501030304200f40c840a02c2016a94001488102c0d12028161290f00c080355100a03900c4c0144440007016000d80c260009491200150b04104413100c01d01030350062207101c04aa20002d0044440d948426924140c4038a507503400070900e01242405040d11541213010b41051071407048440094200b94a20031019690402e81408000b5960b1600c690070043c04148001c01100042c0d500c080d40f030303c0b0080c2034141045410803d104450b82408400328602031520200c030001203c000c030410141107017604042c01c410401d0001440610070340140903080002c1da96400d401402d00c3c42030f50b101604078081300120f41d0307151560302070341c0c40300d1004501600803500110b0b00d40f0714500d481c00c2c02d640c000b0001c4d4026410710041c400010350b03480015040d24812201d840d2030b40c0c1c83e4a0721900416591002401403ccc640c84001000313a0040010240c0107000c0c1d0304d020344580c4424030040c2458 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 592163830 1250 592162580 592162603
    0x1519020706020a2307080d0e010207050a050103020913051303090b071115040b03011e17120d0b100801180603030207050609061e04081b090f090c0a03030201140108 72
    0xc2001507a40005504c010040305209003442c041540d502568208518040042d04402c401c2d521a1011448080e0401c0d4140c0c900c100c24070050140b1421f180c00f007012a1a035201c1c20f414940c010403000e41a5458409072240f0241c00c5070104140e20300502041440110207034140d0101e80304070030100d1045007440845680c5504102080c40d007a101400380041e030500f40b0002d182030381d024040031500a5000006600030050340f00c0b40020841030102080105800b0b40c01008200d000d0281300490420110789440020303e00f0150b1703902c8640306258040a041c12000b4a40e10038a800c2002c400d594006400034180c070307000a6038000c4082c4107600342003161074502001d00507074031424040040c8c1c582000100b8888401914141c02c0c80181d2820700481d001e0b03504000060407000c2418000c1c80410402c0d000c580f000104070422007480b00000c110b8518025005c841c011804a00151030001e0401c07421307004000150034004c1165490400134024245034480341050030b6010000030300d145000517941540c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 592165080 1250 592163830 592163833
    0x308060f180408042c010e010e0a0b060f19030501090b0303090d0213020304030807120603081b010e06011e291b0a0c0e100e06010f030b151902070602 66
    0x710044942049905401401214015020440400c40c1468010034140b103414811400b00c9001d40b600e4411508031050b0883d0700c013004520010418035401400e92a0800e4400c0c40c00569120294046030b000e10854407848003806000a07951440b030020180803c1d600c0340703550200300ca43d1b2120914800c2c1c44d00c501c901a40b560052100d500b1038500708441c005d4261000f0703c0c070b1a4640115540740166002180c058002c81c088104200c801c0f500300b039003d08841c00000c8200203190956580c03104074050414200c41400682c0d0344180303001c3c400d40c8444c00598034402141c200303603500c5804003202c1c5007551000c0c501421204c00007981c80f07039000c5840d02036540d00710141c8a040306400c5604203a0808c0c903140450405d0341e00c2114034010180121f0303503013500500d4420590b074207141d1060340c5218050011009601000030801c0540303045a0810740040c001d1802e810707050b00700074046001d001c1340400281d020468020070703403080360b03a00f00a02c05850008001c1100468100c81aa158181d911030718026 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 592166330 1250 592165080 592165099
    0x80c040522290106021b01050f090d020901080c030d030b0a090b010e03060f07110f071e0909030c030f0c1106030603030c06090115060206070c060f020408060702010903080115020a0b1506030903070308060f 90
    0x109c1c285600600306140028103004407411664002a500e907100307911020094100089107081070506000464611030b45007002d12840307410707001207a041c034418072448640d01d50700c07104007249a01c00e54020041560040032103c50b41410f0708150001e400556005020485695460041d4000414400b07269a04d0320044e05030b80d031902c60820b81c0320820b24016100407140c08030214103100288503010b65070f4000d45d2100c0d91001c2600e4007034081501040000284045440d00c0390008584113032490145100340c0b241d549075122030002c0792450203420285a6103015480400004581c15401080c0380e002841b030000c0c0d041d07911041641c0319036060b18041d0010786803202403004a406500b0004560b80b4411005151980d120105410b20030290b0f5540f00503512076418a062591016429014242000819642d0384141d4030296944401500c010601a80720000419441c2800300c180e21402020f4036403541c0f4502080740e1a243d0340006401c40114100002160050501c6a2aa5103a04020b00701402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 592167580 1250 592166330 592166347
    0x30c060c0906090819060c1b0506010e010e0f06010e130e06060f04020406090e04050304050a0305010b120309030a030809031210180b011b021216080c040522290106021b0105 76
    0x3030075090847c0700601c8040c06180034000342c1c0d1000d65071124081c802408655041400c12182d01c101030b400800240502d009000c50b8203007802030543c10840c00d003003041d200c8100002040d4100103403055192160b16240c030300300da6050301152040c4143d5045406e41003240111007001f0482c090fa005507000a02c1c404c00c18005a0101c041d65078029001e4000c5030b042681d60f00020f8801c000540049030760307945640d5148510b05000309c201500020800141d414111181d0100e83c1c3d03034254020103420070001c2c00c003090307001c1d034180129090600030b10360968081c5000701d590308840100f44100100300c100100f40f8151944a88502d0003203150580d0341c60150300b28415000c008880140301130381c0c0b1400340d00303440121041c04c01041e2014400070810500417848e224100342050407940009014a0070039023080002c0401100f4071041400200e9a00c48503002400c2451000a0b60741001c038002c00150314112a2060440049040340e00903400c03030b01e003502ca141c0d004441c0303651414004d0100c3c00030700c030502c0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 592168830 1250 592167580 592167593
    0xa050601050d141204080610050f24030403020309092d09012c010c03020c030403061d0604030815030d020709050c0d090f0501110421030c060c0906090819 68
    0x1598038002c85055440f551440d0920303081039201043c06000c1c143c00103040010800030721a4540c012071000059540c9490500801c00610303204071050700c5500d4116030249103060485d8400d448501000e00291a40740070300e400b80d0303254015030340c162181001000003a40c24241101c514a242c2a542a01c00c00500145c0d40d414105405400440c29540380d203c060038540400340c04111141c20b41c1680c1040307031143d10825007194800c4136404101401003041560b0700f03000100300d03000c82c6c0d0b00183c00580700426103220103207503440060309400750092000380018168040e030000c0c0540c5500019060100b1000308040d03030303241000d14840140c4c01c10305040010321520b070720080e4010286114580b13041d9040300901c04135a10300c1000c40d804131500c1e52440504c0024413529403059882c0400c94541030500069155a0503020205c601079113282c1c406a041500c00c902c00340c0450fa2149090000c03000d442805495010036002d0300c4000365004500050070b02c0000b4000d07050751500f10300c0d44500145604c840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 592170080 1250 592168830 592168849
    0x90105012414090402120106140406090e0a06051201091e0f06051f0e010305070b0306150d0b060318060705030c09090a0902120307120503040201142a010207060e0a05060105 76
    0x19440c19002c0c08100703140c1c0c130340f40000e000345980c9400c1903d00b9814588090309405a811726989110304c203020601c0b4550b0085000c1c0c0c00c0c2c170080700c101e03101303613880803040030141030590001a00222241802c081d1100c054016601c0180314407103141d281d0003481d0701002881c10181010344505450052407001c512258802d03504640700d0003000395032500b2801c41014010040e44030100c0e02040f80010803c0c058103100240103003200d02a07280c610708200700042c03403030324a4038094004c0060001c0e0320407948019600070207800e400501620b8580c44c107110940145407812035030f00319500555002648443c07244040340e1098000710300c1c1c00d041c03140303460904c40a030307900a20044000380c2e128600c1026940d546a2419000d20990003103540d5016450b0050f0200304c001c000009208081c010b010040c1c0e005000360966800d50304103561209808407620307118072803030340c3c0e00d030010143c1d0078032403d02c00e83c1900103101541c0505400e0065104098009a8400342c400024150303030051380c0180304524140202 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 592171330 1250 592170080 592170107
    0xe0108040b0415051315090f390602010b0109030510180f06020307020d090602120c0c0d11010201060803040e0610050d15050145030602040e0901050124 67
    0x401c0740203151580d941d0104d54050314643c0c0904036024020007001407043c3e0702034802584040600c003108403542d4003a090b50f50b0350f0f8010002c420308114040c00402d0416045080702c410310002484c50804c241504144405000702ca005501307008820002d0350289803c00100c0e940a00106031116018082c4002030100109000d4050100740c1d14030082180c400c0079413440e6004580050750780c1000c4d0b001030301d0490100502024095186020000503801290000c0c6944034402440d40c2c41010182d02c508209040f50a2a4000450003c3c1c0003402043e85040c159510281c00030045952200700d515581d005500ca54112084800001451810140d00060131138809091090804045094038016111562440d507000f040b084d00800843d039019010001c45104440700300815640754850604c10100c00020065030310001842c8480035240c18024401107402040854403181c441352041120041624462030030344c01c0c01d0021800c03140b0907070302843c0d0801c1e00c0c1d0310384a00300c82c2000c2a21074000303071140b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 592172580 1250 592171330 592171343
    0x609100c02070f080312090a080405011803020301090b0604150b07021002070302131a04020f12062115010b13090506010905040609050403090603020a0c060b0a05061c0b010e0108040b04 81
    0x100203a10701207119030300044d1046501940c0c4400b910f8440c4424040001c06d0506264890345000c0d01240300c400854007560020700c2c096802040c10001503400325080d910094040d0302c7e01c1c009000380001d08801e980560401c85c1c0501006174200c0788104c129041d40110400e8010412000006280c24010010010528015541c04a40da900011407036103020765400141c58844400d440e02001e25455105210310845045080c42d006c03248242040c040d6603042c031005101c0c140410032075500d0559441c0130b001007184450000c402880d40c0d07034603003412105d003a0700c070080e03040082500245001510b40207959040d02d8401c242c507002031613014210150269040c064080b10203c0c0c01e4903140112400341c640d014000c120340c00d02c0e1400910420a9600c19403c05106200404401c2d6225440c0c002054004001090b5444081d0000c0d000a00700d6110301d60280000130800000d44250390101802519602c0400001c01180015030346019500d448600080d49840040c0001e40703c0c51107141c0143c012034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 592173830 1250 592172580 592172593
    0x1e0f0111011b020a05010b0d0b060603090703050304090209010206090109080304020d1106160b061005270d0f0215071703070c051204090c0318020f0d1e12020609100c02 74
    0x30084505100c60b000100300580014041c0d50910030240200c9070812000e507090340c840251901c400391071500180c000740c85000004003017071a0950400c0000e000c0e40d00441901d956503500d446400083d03010719126405402404c0c006403c03c0010720500c00d4458200b40601d1640d41d0b1542007040482995008a44919207a00380c10004c3d11950080c0c540303854883c20580d140b081c207090410482c40300400142c4202140380c1c005410b903030b208080e52440c41003400c0183c036109a8128640c1c0c0324141d00c03603680d0801e981040fa8801e1005910501c0803181c0280d40f0350f928054600d50804051144510140102c2c0300e860302d15981030440801182d00150502e890403441c1c4a030f035107403803c1100b600d070703103c080d4800400d09010fa240f0350701c02d07810b164145003020040c20800300b48c020400520300b60003900c207110500b440813183d2201c500ea8900e05034010310f00028034500d106503020300042c0c4881130361034000912103518000c0c00001d1f200d0041046400074501040e40c0203141018151801c0b4440c02c43c00b811 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 592175080 1250 592173830 592173851
    0x90914010606020d140a0c030e011b0c1d1311120a0302070603050a0204061d030304180f0c080403230d330b040b030705070b010e061e0f011101 63
    0x2849041d0182400360b002d02840c0315240ba00501ca030141d214400f03171a13007041004e0b10446030450f00d615421945418a074101a0010b00140e90703840d404a03100308040550045a02040b8401a01500380c904000f5500126056120000c1054100702d0380c141285969582c0740001c111074456050031a01c008000c26042000103130392900b040e9003004203e01690001d00141b2425402d4000c041e40301100c0001181032034544000102a2003900c400035000e4114010009802d403028411200944401c20492405240e9610030f00003c0425007021004c8a00e4411a1111071740f04101f01400346400d81e1316400603451003100d07504224004518901000d008000d07001810207180162841044140480d082d801c9041074081819841350f10012403021500c10148440c8104034159401d81d01221807143c0c1f20740c0e0701402540c1c20300c1180809484041e18500008054260030303801072045100340c4070903a0310f071001380012180c040074054890b8040c1c40c04e4101900c07135101d041d199444c40d424000104800001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 592176330 1250 592175080 592175083
    0x504030305030c0304051f0506090a05090d110f010203070207150503040f020f030a051006030c1202031203100906030f030e012a210305010503120304031b02010210050709140901050a090914 83
    0x101c1e4807d00b100307441303904004c4a841c000040d41d85c00341c140003062142c5d1a01c1110070303803a055450000000c2c800061030a9280c0c000400c011960480070400071507407400d120030042c0d40c82000307110702d200c0d0005040240032044c1c032510035203008592040c0b1565007050154200442c10001e0f041c202e825200362903220380814010441c0b000d01034440d05001901e1411420060042c0055403c42410300344a04200320041e100000d05e50010400c0000c09500d0703032241920700540d41000c2d13000d60050341c1012000310a010b00c00241e00030b0320348292074890851040000640c6d900107100c0e07010301119442144031404841a050500c0d110348980b01424002c001e01740801c2440c0314400c007540020352b4600041c0040d0900b00010603145400b480540d08524103560020a802100e03606682c40c44100e103502d00469000704045410700c03541d0101400b8a1800400003041c40410f03100e04170080302011178000e401e040c10b001180c140c60300035201c030102a0801c00050090f011000045405040418030b0f0000304c0c07030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 592177580 1250 592176330 592176373
    0x160f030302090a0905012d03120915030b030c12011103040803012108190e06030f0601021b030307060b010e03030f0309011505030619020d0e0307020a060504030305030c030405 77
    0x2103a100140c40308442c07002d12844101e00d803c0031484a15040040c803c4824283e581d0703130b007220100d0031a110b0000035107030300c1e98040407940024000701a0008441041d03800c44103080c190340154044094401004030b0440c00e64084d5502c1e180c240c1c00003180c12543d0f080122000b8020010240041400d850508802440d035004540556035410080018081c0c0500111208003030100c28003a180001d0560701c80034a40c4c0308030988441d14038065040170786c01c140150400300500500501a80e00ca281c21441d104c14010308450309401130003484003038080c0e540d0314065a09445000740c01541004003030303950744005140c5101c2a9050205811801015540400c020104100c130020030b00d807681400d980150950740e1100c80118002903008060145440000d07049a1060780071881e4008405404180750003480307180001c030741503401c001085500d0b510010042003145d01c240d0344800241da0b03580c0b048443d80243d01004000400420200d040c440e010000380d50854003500a84458035040008440d5090 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 592178830 1250 592177580 592177583
    0x2101050f0f19151d09120d0c020705090702030d051602070b0903010e010c050a0207090506090705070615060903031412010605180307090504031d01090515040f0314070602010b1302160f 81
    0x14240e81c080072a40d0f40304c59215030008014001032026070b84015041c61035000d410f19500c035035070ba01c840d515001442084450002e21002d8031054041c18043e50094481d400400d0185049040a0106800c644280081281c000065002e801c2150900500c0c00d11940841d200350360543d200e41204400c44420f205000240c825600d405a444504840c0a03081020507845001241e1070241000f040f0b440300c0486e01e81c4001c80d40350880d59101545000350052061a45047c96045151710204210750041d000c00d05482c000c1d1a20070141503ca00d02c00c0c80c501c24030743d000b481d140000c4010480c940c015000360404888410060285041d00306c0424038104660b0301036510703540c40741c091000341034008010081c110012426144e1001c50800080c2c104141441054080c000a5005008884a04058030302800715a03000e450243c2c0e0300d09042000d54061444000d4500500d01c0000d0610f0051003104d42004019229070310140100789500000e410080da4070110350b8860300803800003080210a8040107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 592180080 1250 592178830 592178849
    0x150c0a031d030c0622030c080f1201080321040804090e0a080c0105010f0801020c06150109050d0812070c1e02040f0c1d010e090a0b06092101050f0f1915 67
    0x140b51445c480701040343d00f0072180c0f03620b0031010520000310b40e114140341801c2da00030503019540c01d1640c06100c154481c014440759001c804c41d00100d80d409010000b0304034020603407000344c20901901c0580c0ca04181c150b400a080130820041040701ca03d5982018440360042070540301032440a45481c101c50340005008200b60355100014844004c0c49040c00000e0b002c010001c40c180140d03403038140e507103882c0030b40445081d203101480c110f9a40e1007024070303078042d24026245089400952405078040d421110840d0442034659001440143c455041c95050680103507011080400c0c00f014a051602c0031030050760070588905107100030344018003481070603180710782d103901001d01d00e01014840d180403001c04504012004120b48055500d011200d500450302d200006850260000080c40620885540903001108511503081b40e02d504507d40195100d0b00000b4809a958091307841d140d2101260304140250710400800c0046281418026401000742000950400c4200810590084940c04148503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 592181330 1250 592180080 592180093
    0x510050603070908120702130506061b07030b010501080408040605030c120106020a231005060a030c0803030a141e0a1d0d020106212006070f05150c0a031d030c 70
    0x884c820858108840202400c56040c17082c55070000e400450001404c08951340c941002c1240307981d03240110744c1840044070821161050314800c40d6141d18042c442507944002d40d03070001426502688499100719405a102d41c6024204001500c964102500c188440308061102e0310784070201d550b41502912154004140c20516440c2441c9540c2c1411a081590743e2402c11000e024400000d0364442c000d034030304011071560340b000301203458180c80364006444030900342c00c002010700c0e01100660155504403402d00c02221000725007420310100361401c150310514940d00381e45001d01e104515800c41c907240700200d82220011044c3c0440b4250050000c06900042d521a8045409116910050031000390b40e0921444180c0c3d4140841105d010181c4103010101503000403000f00d4103900d80002c001042c1e00d84070034181c10704003410300035000210b80911510a2400741c40400303880140c450f0401d031401a140008402c421400350a01e08a003448581c4083c0b035504030781009001a1418547c100300800386d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 592182580 1250 592181330 592181339
    0x72c10180c0516110303030103120801080a03020c0f12070807090c0206220f201c0222090f0f0605061008040206030705090405090a0b0702070b0d05100506030709 71
    0x40800322040c1154540c0c0c5020300054445400000780e64203030f030029150728002249801c010f809804030300340301c035030600001002101f00314420000354030143c0950360301a0560f0704c821205680740d507010300240150f4000700d1944203a00c0c100c00114280280507241500302d0001c2c4220318988919504a40703a1078100050a010102047c4500c2406000901c010505401c0c181003c00407003880e0398500c2c0f8003845082c02041440b02c00c5c2444500643c0c80b8403500c0052112070f43d84070241c04502c800a2042c1c01407203030f0245010440c0401030713070550014104400301d50110845468280c0e4103414900d071a44409903c07011612130b1044c2c0c50818051001d80c00c8000c6246042000c44100402c0548140c0c2c440704000d07111075000075101c1e481030f07040d02c14903541d03120396a00340c9547c040e01400765802810401004100000403c252071441d00c1101c0483c410703200d03014282d0b01c41c0d03150f010b0300c8001c13a401d00c840b00c0f104a580d00400e4100c1e40b884c0c868503030311ba00e44001c24443d03802110b800d008248070000420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 592183830 1250 592182580 592182599
    0xb070302010507020d0e13180c0608060315010e16030b0d110906060a14070f0606080a0b01080c06091306030f080c070f1a09040b0303030711011b02072c10 68
    0x803005503882d09035141b107082d40010701508115a031090a883d62003903401130140c06080160801d036002402103220342d5454600a10180003294200d00a01800c440d52000012040e00d4070b040e540c104030540c0703c5d559440301a05d503420000a12404042d1158001c5241c0c0d211000c061034014000c60b0038044003000c090a002940318080c103443d0241c0070400101001e10b40c0b000011103000e1142a016903500024240481c0010701c0c0d40b8003400380e601d0000009201180000c4c01c1c6d080c40d01c500c21081d4182c0e41e0710f83c00ca8503008a00c1c41607401141c02c1000b004a072030075041410150802080004070146c0365114140c214802c500115951032000400100468040203841e00604a48910340c080b1410304034041d10102080740c0504040070041401d04450f900c0d03400048940714041d003180c0d120302c1d01c48070003090030300e5803510005154603000440f04e00d01d4074181604401c02440d0020850145809050341d07904548260b06a44c0078404a901000e5440341d21100303010300c0208140110f8903041c2903150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 592185080 1250 592183830 592183843
    0xa05250e1203090f090408040e0a0509060703060e0601110f030f03041a0402150306030a0605070503060a05152217030909360f010207051c0f020303150a0b07030201050702 75
    0x1900c980d84240310040d250350b44c00400d00710f084821381c1c10440c16161480c103c0100c0c002c541101d080e822a090402c00ca00d0016408540314564010444816032101c001c00c1d01241c0c00c50203690903604040380001c0710355006980741c03400c0c521154121500085010b100c1820340e04400403061200000109010501c03072400c0c440103040340c1c2154880600d040030790014070f840368200c0c6081c01e000c40c007000103900c5030f909004020000e87c11107805d210343d24214200620580c0112041881a40c0440c004102403c08404181c00c1c2a109425540382c800c402d1a4409502c4000420b070140c075403851404200101c015914902010700800215200e14002c810001c3c01c4400070300151001c119511484010740034034901d0380b00c6030300d0342407000811880502d82a003040e10140020181d50b000003001003c11000040390402070b82403076844101c1c1410b9401c1105c3e50200c0142d4480140c1c4148085200c002a180c0c400b5010b00300240310b9400c0c251345a50780c0c06240c11482096015075519403c10800c160140040b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 592186330 1250 592185080 592185109
    0x101209060914060907060c0218040302060103060e01090201170603160e01050406060e030c010c111806031219030f1d031b0115030303090507090207230d080a05250e 72
    0x1d418145000ca101a40d10203852140f03c042001c0c5021f07400640d2140d946081e016041424604841c1ca020309000c0e503215028401150700a188c10202581d440b01846200110380c1e0594514030301080c8451030002000c000b07070803568580140d01020303450310300c2800544020b00146c800303070404d50303d410200300884100b94440020301501010418040d5004501011a08400d0908004c01041c40c1007480043c1c000701c040b0707500f003001e84001c06102c0b03402d030040700d124103030440803511403c6600e001503419003e010740500c1007521544881c0c480d11300a800400441442020000d01000749034030310948102ca403000b4449a070030000d800c5884012040c0c400d07075104101c0000b8040c101448001d6a84003010b8031000d420141e030b031106030042100900002c80240060341065407184d020f820160301140d400045240c0f03002e060704801e1090a40410302002540e0f054440440380c0d45c890002074041c00c00104146025401d246841a05904002c0d1140c10b1140664a003550880070b681800796008041c5034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 592187580 1250 592186330 592186333
    0xd0c060b060406080613061a04081009170d0f060605071401050405030f0a0210091b0e060f060d0b181e040b01060f021218010305180705101209060914 66
    0x2c01d101240d04000929009082030703444444003150166454020026500440400c86883c98054400545100030b082900c05000503990807004210012088509405004140c1c001040c0c40c4001c0d489050058100d5070501c4034085804040031582c0d40403521582c1107a8045480411000144034040c902020790b917603c000200b1079810652100d035564041d240000f40310318000968103c440744244131120001c0010401030081406c00e2624001e5041c0a0488126001c424440000c160300c4080e003181c02042d029000800f4070b03401d841405203035408800544002e40d100d100c291226202d152159508180c0110b841d149420440c5a6281c0b210b619140c041d106000b4200344808510b451081c04d045583c0341c18402c082d281c45910590034405c01041401d11070b01c0100d0112050020f050074207020700005d80e8200602ea0f50225142090400c2000a400f2544245003e00050030484165000c030600350a14134580b100076001c09040d210103490860b1040c0c0c0f00c1002e0002c100c0e06c00b0000140a46000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 592188830 1250 592187580 592187587
    0x30106030b040911040e1005460b0409081210060908250b03010608090606101e051611040506090403020a0605060a170d0f020706050414040b030d0c060b06 68
    0x219681100c039952000c240c172942d43c400c544038003440700b00480784600d040c7c01d0b030521441c07908070451810900803407220540b002555051460f1009021500e0359074660f80108403e80309103134882603000b401c050000a40056a440300a0041500c1c6800752115468200c03071079809240c001928141700405501030340034001c41610601c040304002c80ca41c1454411203040c031101010000e054204414554000001c4610000000c200c00d9401152188582000422591213854480c00d11001d4040c12130345000085031850381e0381c00c105928000c82c0b1220280d107081420001041c40c440009a65403004a0308002c4002c4001140e052900515078800382c1121148050301c1c00ea10041e48518444c0ca009021135603900014004e13030390300e407030a08c0907103503209035840700e900c500c1105a0f07a45480008007020070042d852900c0034078030008007107064455a0342c0d80c5041ca031900344458900da81004016500a40710f90b042c03503240c0c801700245c600070340c074543d40e43d54031003d24280101100d845030031a5000e00d4080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 592190080 1250 592188830 592188833
    0x20310081b01030207020a0e010b0c1c050d38010908032a010912050703180605041a041505040608070516170c070e060a1d07050705030f0708030106030b0409 69
    0xd201c4088000c01e00b000b5940f2401c80c070003e808000a50440698801410004194004203202900c141401d240c1180d01140310700c80401020303002c40c0d035802d0015400f000760017540e52858100526503807030080445024000030b1802564555001c444403249c0720746020380400c960f40014448010690580954605050300c0480c8594258280c58600e01020b0548101b54010302540318042e05070f040482400e004952080060207644409010380000d05100e003e00d0741034030500d10b4581210081e4071150b25040c68206821101d4075a210071480210b0309000000340c0e0540c81d05000b180071004d954039513496042c940e01601c0303040060481d8040010502c4034003800d98a49440d02c0388260002803c11341d20504a0003507296200e4801c1e81c2000b809801c0001540e000c9041c80c060242d64111031406c40c098881c4c0402c3c0d020214500300020502c840f101280b006402a03008042150154040e02c0ca840d02c141c48007038041d400303250102c2e00020004010007056030305105001142c24102d60500c010050b9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 592191330 1250 592190080 592190113
    0x712180305070c0306020f07021201021215041104290310060503130f0b0105040515060712090537050102030702300319030506010c0b190f02031008 65
    0x1109402424400006841000e01100c40300780401944d0040f01950f80e8070b0714444680080c0c2003004102e001e80e0710318802c200680d1060003610506241d6a8045890350369185012100b0960700d8015900240e48800380020001c40d074000f04003401419004a2045802101045451135000100b03104c6440500600c007850320102d440c0c104071461842c19a4483e154014010184a8000c41c001c043d001c10398103174420000450a840c2c12504e044808102555450400c003400743e03040307001d080d07001c003041140e01c000a5071400040055a06450302c03100c0d0301c3d143d8010501c007031102c103030312451240c0c207841000468a0142c1c803a95562a03445c0d81520140c50200042d68074050024005d1142680c1201c000230801709240d024800d8001c401c1c4040d800c5804130803243c036544440c0d6002160715412100c412242c1c020301406006d1078041c1c0d500120311940e600c0c3c0d9089c541c03014041440a49400c118051019002c0c0110020321040c000010b81e03c0c14080d10126907285540e000e141c0c1c582202c1308440c4607210 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 592192580 1250 592191330 592191371
    0x91e0a050a05090714270a050604140904110306040b09010b0a03170d15090c0201050c042625060f020601030503040b0705010615021f0b13090614040b0712 68
    0x90f141050700c40c00c07510082201c1c45024003000c1e19005200f0b06e1610003044e0071030703c041c0c11002003500c0e80c01141c1d03214801c0c0b007018819402605490021000c0030041070a080010640c0940580130340e903030410320440060b041500075030313040d03520407a660140610041c00b032051002c2203e00301d6801c41c1c02c034038655a01c640040c1c05099554100000b103442200c2c4446600540c1202c1c00b0341c10510308050300e44030024024413031070742c070480103610b801c0003e06418240000ca4055030000070828014081d1320803010f580210207446507030103000d02004540c0b41c00e010352540742100d907844040c2c8111418014001c040c800380102c0f12085605c01c8004201142c004000c80e010340324100803c03641c0f0700290070803d0250080f82d02c100854405a104084110303404203d141054a102100441d00104843c5000039142d403544481e0b400160b1802c46d09490701030390b1120189510403172020400784018050442400c500320f0303042e502c0b561800c042202269001900c1140d00a030400d0410482c10b955141100504 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 592193830 1250 592192580 592192591
    0x150301030b070e0310090f0203120d0605060f040b031b0d09020f04140a0e0a0503210601021209130e0a0c0e0601110a0f060608060115020106050d050a060b0402091e0a050a0509 77
    0x190356611b618140443c0301610852990060111a64000150034549041c1c1c40310503241095454500c001c61700d46400d4007210761000308130b602682090f0410710080d845070b00250241641040030103481b981030700000d01034442c2001c41c4030001074100d0940107015010314101c02c070510651401c042e03000c00c48040100140c0011000200003003203010401150324203c000c50015004c0d20000c03410340103d6030a285030721800a101050032040386c90345001660b40b507589145003501584280140d02141c284090701c5807001ca10104042200c002a13403810f41002d808410650b00003211100c18000c0940b00104990016020300e0030200910340f0399111a2070319848000108000750b62014031003031110702d8000c81c0c084c1c1080001d803044c550391345c00022500d207059001c1402550809400040310720380600c0c925603498100014100c0301c0403964404004040d80d55810354410745c284100f0440343c03244002e44031080c0b61007a54002d004003090400050400c507038030061041c03114407428482d0b034a03031288180c0c012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 592195080 1250 592193830 592193863
    0x1506060c1e0c0810020405120303090d08090a060612020f060301120b04082812020307050415020f01150e06040513080a030e120703080702010506030d11010605150301030b070e03 78
    0x981642c0740041c0c24848030342c0125494400c40944c6181544180d0082c011181e080f96420800c40352850400d84a00003180c410030140c102c0314036414110300030b20105038080440c0b015540c00150b01d40d200b0048071007641101100b03200c0c108004013141040c55034511020400c0720781c6400c7d0b42c03403d02d0a003d00030300c0c10780040a2802c0e850214041002c000150358290b82c14a4081d440300312a150107a6240890458140c00101a080001286090380c82244e00030340039940d8040c9854109824420302d403a400d00800d013184108880800640b07001c1c491500030082203c241107017a441c0000000a626001c0c5c03102d03100714500030500000c0d4038084e0301d590030554041503090701c400c41c4500a034010a50902031806034041e58030440508920350b0000c115041c46600c0e01241921080000c03400c894040314002c0d0143c0c4110f01e9030f10900d000d021541816046040041b0301192181e010480300c3e000211080701108001c801401081034039a03046a100031549044160950810700080e13036610031201c406004c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 592196330 1250 592195080 592195133
    0x3080a0e2d042007020a0b030c0406030c0c120206061021090206130303050d2a21020408030a030b010f0c110a080d1e030e07030b1f031506060c 63
    0x880c2c441d500103503c900421402503c1042118180154650000710201c0c402d110045e8040743d8406000300b03a902421440c183c0702d0416003081c40940082441d41511810b1200d419080000074905010b4540320108a40c00340070981009418040c010b60214014000d1002c20800001c4044c0303025403c444110103600042020746003400031404074030489456008230000c5003404000d258220700181603510b110a810030280111440030032400c1d0848408182000d0440722003030289218002c25200c481494488020503501201c0010403640310713501c03041039900040b0381407030000e0b098402c990001000782400784803c04000802001072102010050080e031030150701c0b41302503c0d58206c0e08050001340040301c402401060014241d03039000c5034481c0000408070310320a4428481e0007224400c1461030014010700e402e540d120b080d001c800800e010114030b030a150041d0195110a0200c0003540261b043ca40c4088034441050280c500c650400410302c18602e1000c400103030400744084528500c2c40074040d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 592197580 1250 592196330 592196419
    0x20607060b010e130c0f0503010b07020409110409060603020918101e0216020f0301060b072003160911030c0405040f0e060106050c07080d020d050c0c0a03080a0e 71
    0x1000951410591342004007113003100c007501c0303042c0d2007030825124546500748145640c03407048605120034050030b0350b140b205000002c01414181c201c59002c51080c1c0c101301041261202160450703400d04420364885840b45402c200358101403448540001c0c541c6c5c01010f00303c9005144656135039040700d000421560318000c1030940b400e03c02403290162515201595500b0050440e041e406000d00c2060380b180c2d810b00300184091405110350802c940c509001c160a0040340d8545414000b00482c0c3c02d0021101a9844003840d0350501c5220310012600c52021b01075410301205800b2601542e18104c01800200240043c1116140c00c0d03030100d07071040b03c2c08503100a5118029026100d00c00d80c03002188030f031400210f403184d0008042c19400744003c01f241c0000b030390340c0ca1140e90f58840b400c030000541c114504001d443c91140c4001c1140c10245401c9030485c2d000000426010202d991069880542c0850345900311030f0f00c01c140c420b280d20100c5000264114000c03042c0921030100000303000d0f05100755007005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 592198830 1250 592197580 592197587
    0x6022106121c05070c09021c0c080106031e020705010204170c0904080a031e0b0123070b1e0106050a030e1606030f06090603081308070b030f0601050d0513060b0a03020607060b01 78
    0x143c4d81c0c1c0c0d2049402d11403642c0e072486000a034200d40002032410f244a020018202c440d03100311920f51101d9950354840b6403800505130018882191800400c490300108015100b070540000c0c4001351081c4001a0703218541220061a02c0d0441c01c01140c580200c842c0240c0c03541c0e40d4621640013500070990302c0c2c3d2401200010740c02044a681030304000c264100d068105255290b1144000381d4080c0c9540e40300c2003844004030385d09280d641d084013890b2000c0c0030342004241200c00d80355100701c102030351102c03024901421948c0700009a00c00c1001a03c0021084e0000c4d5143c040c04601405000c01010300c0100d9040c04000103c5900a44003056a40c00c103040c2c8008027034101320020412444100b00650f01c83c1000784155000d04205034610090080004000d0000507218084450700c5c2131190840d25849a001089500030f004c41e81000b000344241c8800840e13620a00f4044c0e4800704880300ae01c0710f076291102c2903030300c25400e0031311492030301c40c040000d0b0f141d1504903020030703501180c0015205030800059 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 592200080 1250 592198830 592198837
    0xb0306040b180f070f1407030c050a06060329070c11100504091407050712021023060f01020d0e0420030702120702010c061806022106121c05 62
    0x20798030201c29115420141031410b0764038040c2d8880318a00f80d466407520420340f1402a0185150700045d580500c1c4540d00c80d9203c00f81400512038502254101d1580d150a841d098400400b5550580d032804108200001841483c050480c0306034410041d1625640f11411150018440c1d01401100030740ea00408c001d0000b009021a00207080d4820700218100090443d005401201841407030842c0c0358054084507801c091050546a0740c080c41d044cd250740380d0381500c501094135001e51090f14505503d045d0786010395020f40785807680f9800b10443c1c0d20091005000007408060007004406006100c90340c1c046102c075100c100134213242d5800c0340841e01080042801c21080b84104e078100c18800c10552a07070740194051071160b421034030050601d45500d0814031800c0b0000380460407240c4910700141e06a0007030302d034140152500040c011000d41719003059034410455405510310380c21a2400041300c9541d6103801c180241d81c1c002aa0014441b002e5076001c016265117050040360003120207092180046 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 592201330 1250 592200080 592200101
    0x10f050d090c081506040905060417070512071b050306070c08040308030a0c080a15052701090c3b15070303060501030e03130e090c15030a051b040b030604 68
    0x14080e450380c0d59001940b84c0192100760304c0d880e210040841c00318601406604909500702003e071507191265681d039094010113884030310044205110740d1003c1142030007802090421007880c45d5507810189803010644621000100b0700c5030340340c4018403c60b200007a245900900034100031a80151900b410384081c0148c1c3d10043c1107541c00000c00004845517007240305909078030f4541c019141c4640210405403000502100c0c11b801030701d80100002c1c94504008040c2c00b9510b082075a26025682d076404000074240c215070241c5480c0d01c00d8440c0e20340e000350018804401c8480050110520005001c42690300000c0d0146014101d1b64001301c41c1e40700205200c081a0707170000650f580340549009000307014240f01d07441c0403c0c68000c80c5c1c61404808403c03141403050400300c000025013043c030740d0b8044d001c02400ba0041c61098400180454681a038054210f6a01c1e4000985a28243c1c0b0030100742c0d08000c00501502503224030400c8001c0300c0350151001d81e21510502c0b42c0f83d45c1c451010400a01d82e0b081d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 592202580 1250 592201330 592201343
    0x12080a1401062f010c0e0a06080403030b121b030d050c210f04060e04060b0309030313030207080a0b091204210231060501030c0f030e0703020603010b03180705010f050d09 75
    0x45000c01201580510310014691721b402d004014150f040040b00d40c0507110b0740001c90b16900005000a00c2a44850160b1500400d00960703c140341030041e240041000c01e404480c074801030104a0f0385002c2107a00000c0c0d600345012072070410f841d40c149441d81078080140c03c0d108410601c041500f43c802040e00c00281201c20a00e407110340d19034005042840300c0310041e01941c5043d602084200b654400c0341c1c0314100e9000190301d036450b040e0410800b85c0340d284c02941103002d11107011031020310521038842494014600070b0103034140168414204204660100b03c0c0d410304000401c4200c490000c032404001000703444001c11250b0380040342900d00b215a801c205021900d00b84800840c000144601c80407815004004e010745507001902191401e84211000c01d241a0410700709520a80154840030f0000c0b00741e402d0300360381e50f0128105400a0b0081400b01c8000700400c4820340311400384000011403203006100903890300c00040c0c0030500840080003000f0000607032000a1146801101c1c01652002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 592203830 1250 592202580 592202657
    0xc02010c020d05062502120a0804050721030e09010e0708252c0114090a080a0507031a192a030501081015050603090a0f12080a140106 59
    0x6174040ca035120705805030400c1100540486950b03034400181c1c45100705440180c0c0d0b140c60101c0e242034940d1540108116024422004003080400b074403d80c120743c1c442018004160b404851401030301980025100601440703200d00100205142d015809411001904240100351140c3d11814080380c6c04480d01c1c440d041c2039490254482d640803100000ca400e0154410400000c01d10380c9054026001760218001105e07194881061610315005007400c0380000e054400c041d0b030351480700d820f19640146c10340b10382d0010341c2d0410a010380d4402d440101e180529071003156181c29107441d04135100858030504495590700318080b00541c0003006000501d07005001c80c1c203070703e04805d005018240900468246000d41000d00040c02c400f4060611110918004505480e0410061000c44d800090410700f0902c1884804000305940c14106c04200b4040d400d0709030301410140340075000c2103010b40013a062034078100c4001c03079a10842c6070040c107440c06460100b2508651060f8512010b070400b001108065003130 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 592205080 1250 592203830 592203841
    0x140c060708040303050f060d03030e0102091e0a05010203251118011701092102030714060405010b0904050d08041110020102130501050c03070b070309080a0c06050c03070c02010c020d0506 82
    0x1800440c0b003244256414032040d0707140c485d500c03204e038020f46d00b654202c9014401c3c10000780c0a9005802c10300f1070300000509105400d40007c8510000342e48921000f480f000641d01c950602e0101a00030305000c0c001549865075a604028000c001038100010600100c02d00f8010804082c104c610b01b4200107210b040040c02d4100307082c2d0075040a00c1107030508a881c1e41041c400b20810b00032b00002e80d4021030000c1c0d42290301e08203441b100d540504000214001009030f00005011140c4050590b03a00c00010017592500b480c005003110004004184140d82c203008200019400150b8541444658076203401d864846140c4103004602032680507501407240c2d140124071641c15409030004018607409041e407242c0d0b80006445130700c1080255121074008000724804903801003003143d0000010719002504404030f0304e8007038036504901680d80009001d1405070080c041b90b40903054006440d901654035500301b1b50b0018001d8450800001d0500c0321a240000541d80c801690030b004641103c1034421a142c103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 592206330 1250 592205080 592205087
    0x602010506030607030c0225080f071502060c0409020c0a080c0307020f0a0e01060807020a050d0840110406120510021305040b04090204060f090e1b01140c0607 70
    0x1101d08500910030b9030300081c5418413038000c44d00c41c15503a8002d022079001e080c01c0008000208005800f641e40465400181c0d035070208481c0042420400107800d0307480c2040100c8540305060008682158810f0307091203442d841c2041101c0481c1d002440040c2d840c0342c9200c8007030a144141030058002100070411054505011000341b403890301c200c454038070100b0034100708265040d95000d08501009000014041a4000c001281c0c0044071401142c040301c0c02669900d05d000100125000000c014006002d4640d880c8003000411004840381c06840b04106010850050707160144041c62146060283c000c0c040e0004a00c8401600a030082c0b02d503d84801d01c1002e0441d401a04480503c542580e502d640740562080d0b03a08050420264240300c1c2c640000c00c8040e244102155500507680d00d4240b0041e40d452181c81c0c0240302200c007910b44907180600000842d420b040864101c0e8102e09113603200301440c007a80400340c3c8400d08041050441604100b0602d014016020f0014803a04042c4503140da00f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 592207580 1250 592206330 592206341
    0x15020d051b070e15010212070209090a080d02070b0a020a0c0204020a1205041412070b0402041a100905030714090a02070305040f03082212030f2c03011406010503040f02040b0406060201 81
    0x1032131041010010404012a55124610409181d401061199070018540518925001940001121000c03441e03904e806d80360741d008005c0203a02a500042c980200481d000c046075002032880d508504046480f1000341c20f91000c00780092240364001258085140900050340c403150714040c0c10401c0c0d00d001e00c2c290041080101c03420303286109600141c0c481c4030721101104c005951045103180d40d5111642484080d10020708880c2800038502c2c030b5a83e00d912003e0102c080c0d2800c9640d5421014034210070b040c2014500d811441d032505a148826080391944226641c0113511400c0c01a500d1030325040440e0540201e812002030703c40e07042e04c0003091003042c1b40a08030300d1a071640c808001c020321040b1501c00481c1c5103c0e9800c40e4912002003008680900c401d400b2100007070904000f00e40300c00368a003072420521082903800780700b44035040d240c0381001d224112986a030b14000309854200440003822901000b84000c0041746031044810454032103401c250000f480191043c044540c6601003e4081c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 592208830 1250 592207580 592207591
    0xa0c1b061e0f06270e0106031a0601030c111b040908071a010e1501050705010f180c050d050304150507050619050906010e0106140c060709080715020d051b070e 70
    0x24100719002c140140e01c1c200301308044581142c06145107402c3d111075405004103501c4440a9569080c0000109401c0301e80c003213551074000ca40d028980740caa0005001c5440340700055080103105125811040ba0014084c0e00840300c00c061240e80c4658040001c02401c400d00b0010060040403515108102d0b50482d041541c02d8810443c09042ea00c86112070070702c0c1e000300d86d007010f800114607000545501802c0204020340c0100004500e44c180145000203440014151020720107502e1181c400b4410342c2e51442c0c025000c00c0300e0500300c0780c9140c3c89090303890080380100c00c14091401400341546004401701e400da1544403098841c03a29002c1070814a100f0460030b551016800c0c00c0c000f07451503e01141550503684140e60300703002c507424014102c1e0307091400b00003c000f0620800002004590400c0041c0c400c80321a03983c1d4401504000d001030419100d41e04c034400c05900f800582010a40100f1400c3c0c0c110072615003141c98221082c1503c035100000481145280a00079011402c0540f00940700e1240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 592210080 1250 592208830 592208861
    0x8220f15020309120711120c040905030c070501020c090a0c0c050601081612020a0303050315092d010303020718060e090f010e0304080705120114070c0204050a0c1b061e 74
    0x1131126100d0108140f1403040000c0107030b81e0000c0044803900d0010390803a42c7c841600d0446103100007860114086039180c079819642948042004404040e0401c00d5802920f001c1c80580607500e0401d02050045074040c150035003160310742c1c8212100b5845002000901e5410804407085542c2d102d010300d8a41c2c0d0b2112203194007006126000c5042070f000c1810040d0712b58060141c0c00001d00d10784040b2400d41020740580d685130b09440c10150b00c0d40d28a080780d8010600c03050035a140d43d100d25201c5250300265034003580c08815103001000800e0b0046010070031645001c2c11050040001207070b800040603e5000f4603031258011040c0b084607a4001014126440c0031802008400c44c0b4400882e074a024601c140907565000362400d000c5420a84030800d500c074060000031a00a039418260249654200c40f00c4000950059003081540303018081c040d0000102d69003007120f10b418210061460028400e08421a1380c080300b6030f000c1100302d51241c290000c441040c0280440d014413600d000c0c00a020200245 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 592211330 1250 592210080 592210093
    0x60c0c09070f1416030e040213030b0f0f06030a06020309101d0709020408120f0f160c0b0412030804051c020a17030106050a0f140a03020904050708220f15020309 71
    0x103c6150032280302c0c19661030400f907844100c3d501114415035600b00c02c2d03000ba400f88089800808644201d00c0914417440f0780007d1890201c074580c594500040a4183c8018a803051014035100401c0000d1b815030849405a40d070b075141d5812500c2c00d001034004101d01440d010714561030824240b464050150108283c81c00147d407840316806a020b2801111902e070080c6070800700d2003088400428034080f8800c003031400c0041010390b152250300140d41c21107980360203005101c05c00901c1740070000500f00b14041503060034100564070304906d01840c4009d06001c50403010800f07105042003030001004051401820100c0c3c100700003503da000429003104e8420480d6480180145400140c906981c010b550302801c014950310101c1c1c0310b078500d10202d0b0900440450400703035501e17410001d104076500768501603a45c091843c1800200c41c00100706000300410b50044c064a00b0b4800c5005551400e4005000d203040c1c11420411452a144000188503000c0c01d4021402442140c004c0c6200f00c0100d4142e580 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 592212580 1250 592211330 592211357
    0x509010b0c240a20040905180304031e32010b030715051c0203010905011a0a080718080601150816080105010f11030a030e10150302060c0c09070f 64
    0x114502c444038103080303401118000440b00c0002c0e900024101a07420980e4985400040103414103901c240c005220f4542c9800410210212201d807075010705032020010b5190504d19240c401401d1400315040d111802c0340400079084c442c095a529100701c003000c500021081c404210b52071070840c0700729200019420105051800e02e0041002c0c2c080307030b4040000c0744030100c200c0402ca03a103921401c50402466891520740c1c81e00005032010b0b501a06644c1000503665043c50303c65071922012196800e0f41c42020000301081c29130000500380c01c10360301d0500409400c0c42c05c26121005440750030551031441803000004483c0800d82407102d000242d520740012071f8490021412040bd80403031801c020440100c0100701d01c0d40b15203403c1c1020201d42c900310703040d1500c1c000c0700d5042d0340c400090030f030001e510f444040d81610014004600ac0c9541802c08110510a18100c00c6803040c2e91b00c800780c4070310380101d1344844680303092018100c03810005288801c2840c0c040f02c05401412191104000621004403008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 592213830 1250 592212580 592212613
    0x3030e0a1404020a050c060a0e0c0a03080904050a0605040c0203130b04121401090c082a01021e0109020d0c0e0a02030708131704090f0f111b070509010b0c 68
    0x40c2911a904004580c010400301404003030340c001e0311040200403003003145e46044402449041c1c0100c141c110040362000c5ca40f42802e1500040003486031241807411410070018046c0350865003000c1090f039002c6007170390785c2c0d9a030400100a550f0041d80c0090a208074680031a9000c0020000502d42d09101810bc6d034440e49a40c2050140e4002c40c00060f148402c124085048405092910302c2544000700d140403185d642e244184600c0c0d8410540d80d80581265030f003104894071605925907500380c0200c8000042c5000070b581b4904a081c0804512101c0d091809401007074003e8a101034014010110381e031201e150440d451159482240414620500414101c000b24001c99000b5040365030b0b2900140c80d1078090a10300782c1100401c9894103115100642c651070f141024100500b4040d5000542004406040c015503007001841c90509191800c8074214140300401e49048444003000700300c80d40c130a540c0007844e100080d000341d0390102d800c0700001550005203008100f01c00c240819100280b1142c3d6103030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 592215080 1250 592213830 592213849
    0x2e09050a06080703240218030607080f010b0f04080706180605120117030d0f05060103140402101103040b130f0e040b160c0204021b06010f0f152703030e 67
    0x480658228443c03c00104200700c01d858011181540c0d10407884880b01d02400c04c030b90080724010310002c3d00c8200207041d442c00b4401c1561040d010304109000785030280704205601c805001ea004146004038206041d0ba92a0055602a0850704220741c501501c0701d00140c44038420314a0785030065824500400c201d07100b942030310940c0ba00c01010003010313424000b05402c078a062814a206500c01030001008102042c0503290780c1040c020390002d014107218000500340c8040c2100210300c0381040e41407100584440356a240003030741502e0100800560303054940d055120b982e1198080d08004a0f900b8110101c402402e0f003100ea40f90f119660307455603101c0b03014005a00301c4000d03003003800740300000702d0b2194414803801040c0e00780e1800030a880c200398005012138110300c2000d040d0700c0450900310711002040144601502007400d0b003200c0d0b01e190080061509903107013344100701007802d6a0310b2105021303030155030619828140724041d0074081121070090360354521060340001c00e05540030307031141001d0388079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 592216330 1250 592215080 592215089
    0x3060501050324070518040216060605060406020a0624060806010f031a13110703050301080f0a020607030507050a080d0504061b0e30030c01061a030403082e09050a06 73
    0x2883d84590711400d00359a01e400032090326034507820b400b1491b00035a85034070040c03d800c0f00030150304518003c241040c80445059804c118006e5100b00300c18401e941e00003c01c1040301e40d1210011981c1d0050340c0c0000b0515058180e803442501c650300c40840c1c4580c003c0c044520454003a41d6946202220500440c140d89440f035614070203608000d000c0c015400e21a44c050400740c00c140011403012003214600040754400c42040d4001a008801840112024000c00c3d0700d0b420030100600c000400760b0002420751040000c02418800001848402c010080c000199000e810804054a4030b058140c20b0700500412a01203074128034000303030120605d1000811480b00324280e03888103001c001b01c0c2e003807221644810520800a45030700c09201401ca101031b051340041021000903507298803160010601f90b80c550b8000945945000464803c03c1165030f01740d03030b40715800d07140401b1140c8070307410302c01440321600c0f0348039000c0701c4070040c0d0711203030031a91007031074100d900c5510204510768848107048210342c454040e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 592217580 1250 592216330 592216393
    0x120c06140f0402010503060d050d030207031209030905010518040c030b040b0d0c060309060b0607030e130207020609270f01080c010c020604090b01050c030c07090b010e0f01050c0313030605010503 86
    0x4a07025500c268042c0d1f90102000c0d01e0780e260680e40f616030783c0c94058004c5203400003d40014059081640c4031642d44080000e109044c8014901030754041c210702854000e850400401042800700e261000c440801c0c00a400740042042d2000007a00801801140300510b0003142071091950160400100d401c0d0703581c0d04519942001410a84c044000d080007241c03d46606440c2d07550f4051643d01d01c001000403901c6500c8003400700700070100f408401d0102e015410907071f0f0710500903d40540c4a50044600c080030403100c1c500300680e0005010741440305500c0c0c500892100a0404c41800c542040d450b041c0c0e050b190440303c4450b41100110303142041c03450025001181484200003000c100d42181c0300c1e400c0c050400e94101140900400d19580003100030008036402540104040d04140c843d440c1c2d0004203107040d0f4050740c001c20105100541e0004118100700e03002279a000100c0c02801960b01802d92800c481081540e2418120f019180c00e002e0148070303000c1c50800640070a640070300448405107011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 592218830 1250 592217580 592217611
    0xc092c0f06011706010905091305010c0203120112030c061508010605101202070c0e0f100509041a060a0506070c151107031103030d0203010e1023040216120c0614 71
    0x2150f0964425024003000d06100301d611020699035583c0000c20f02c141d01060015601801d01d04040d402d4070b007082104130070354008000e001c0c0303400e075801c0409055403403c0c44e2001200c813651908603145d00d5103c0002d0030315860100d642c0b5960180c50b543c60b04540000c8000d00a4980715010041320096107040d24011611000410034846550b8001e4240e6a0150721813400e01f42d41c4184e0000405800c0720312003220b40d44042003010700c80c500e00c003001c040c01081d1640505403070103a03140c94034a04003580d0300b49503066000c0000c0095072802c62000180002410060300c2da90300d46842c00326442c0f6405a60000c0703050744500458548640c01040f10300c1c503540002c003400d44c655291100c41180c00d00d50550540800c0022561800d410b000443c0241082d00c2c110026181400d42941d041116400031b0f00c40080c85040c0800d0f20390f48121000310140200c1e80181e8400400c00c490300c60400e011801001c0e2261041c00f400d1440d00001e440f5203290040c1c1d014448540d03003c25150504500719446664a8240c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 592220080 1250 592218830 592218857
    0x3010609051201140711010c14070f06110c03071a13120e0301020a0807030c0f2c0301110702031905030712180e10120b06040c092c0f0601 61
    0xb004102000800000034440d054003040c4011041c0484100c008141c0b041c0c450410710388240f10b0054540121320b00302c5c02c1e41e918820880d640e84154034000d4074050f5071102d480c0a00c0a076078451116902c0101d180c59881d29142c10b002e4590304102000d44586401c030b00785521150000c2000d91240801c03202c42e1071106255915849800c6003066440204160100c007400140c030300344001c02d950903140e07c540c0312a00d0b041c80000d0136140300709c010f41b0811034803407180b4000c1a004154a14540340c54000001d0f500a419848960032100c41c103016403542c20b1020401c07840c1107400c003c040540c000d0302a502c494064420541c0c0d04210004002c01c9540100402c0e404600c184011030041ca29a19064465001c0342c40340c0c0b030502d2480c1c7c0059a841080c5814880c0c010402e0003004010302d018460b07500c0c544100d846046c0e40003801010700e801a502d403030084200130311400100700540f10000103401c00031202d14503100d600304202e41821441000e2804107440e030304581145449040141e68608000401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 592221330 1250 592220080 592220089
    0x70501050c100c0903210f121104030b04110a08030904022505150915150a05060c0f060109420902070b1f0605071a0a1a060301060905 59
    0x1400401d40d07000d1641e039021242414000e07070540e08000da8407288190f080d4103002c2e280b210b40d00c102da41815507282c05c2210703007508481c100c100700e0b007a410810041006040390b04040e00b0046071000d140300c80081d011040001c2801d00a00690060144603a0300d4400d01c14004071480714014101654418405e0984510b0715400420708015502461180c3c043c0205130080d510800b500c0c00c6170700e82c2008590100a1084200b001c1c0d20803a54802000780012105a001502c103019184011011030340c0e00601e56600c1d001c0c5224002d100103061903a0310606c0007200ba4a40302d501c000244640030304000011061041c2c0102d8584588020078041e0310742680c01a9146450b48200000080c8000054410f00d40c41107860301000707100b00200940d0314550342c84c10350780c62038004049500000c03503000003d0307603560084008070030341b500750502c0c50303171107038282000ca10540d070304581e944410b0000c0d000c0100c0d9540503006046840b03080062a10f020000e84200f1040c0c1c003003401440d00003024603100300000d151 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 592222580 1250 592221330 592221337
    0x601050a03260a0309050c0406051c0501060518074508010f0b011206080a172701020d0c200d0b0106170c0f070b0a0e010507021606020f07050105 64
    0x10b006031010141d1800300b101c25101c0c0c215001c4440425618038a42c0b00303004050141046c4140300301d400f00400e0341032a0018155100271181407210305000580017040201c2544045c025210041003030202203600c1c0204192100b0480b114400a0705c0b40c06861a1100b1215040740414445000076160403071001d40c031206c0900d4840d488541081000c00061421000e21800316141006035021854003000e80016200d50842d2600d64240741c40c0c6542000b00b8800842c0c200310040d0321050f101010006502003a0749402a005204001e80d072a158690120081c56080e07409504283c0a90712074034003065050314200c0ba1050003400074017040d460025074500030401e203079540300020314401006500713807107141000c10240c11078004514075000c00f0b40c442c01c02203070340780d4055800c0495615260703001c40d40340740901498030014084070001010a407620047e0708200a4608103000030095840c0030300c0000e681d02005041e890131202a24404030300103101043c0c00c031550113842c004062161801c001102c0745e50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 592223830 1250 592222580 592222613
    0x20c1005240906010f2007090b010c0203030a0f09031b09110315010e01110f010c0e10050f07021503240406051c0c0305030a080106021204150305090c131d0601050a03 73
    0x5401c0704002d0303001c003d044d4031046c480301c00c4020407080c0d05144403241240c2c41140340c0c605001c02242d54000694000044400d28202482c1010007400c00c10800c0c0c0da1011141c20041004801c2500c030b00d80340c5c071a104900f084803881c038014410003000c010101c41078070098a5a052498040321501e190307502481031448901410b1400075504100c05c090242455600544140e6a035154030116041e55880710141815410442d034604e81c04510500c041c209101e008044480c60703101203041c2d0309547e03c0b03407a0340b903082905042ca19601c1c540609800c0182080c0701c20308840306521100a03030755061901c581402d96201400c800c01682c403030070040c290010303a41000c6404c860803070b001100064050001d49010001504e9004155042c500c000e400c1c041c00403007903240d5034000e00007080004081086e054403030009050008990321450030040c03c0442d0b0311100f13a000401441d010f0f48855140e402104900c13000361440a480c4100c0d40c400d81c61b22303000c1c4139540d8440010300050004c14242c1ea0101100b5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 592225080 1250 592223830 592223837
    0xc1911100c060c05090618150418200406020105090105150a120807050d09031e0b0f0405070509150423040b0c04090c050c0d090f06030c03020c1005240906010f 70
    0x40a480c001761b0907511a030b4a819008a40e007510020328201100e51418040c5551100d03400c060601d0300804908544114041c00242c0750304070300c0c5106200c5032010880b03c4030b00e16019502d40d103654019019280a075a0b03004190310300000103404801100100c507012000404400300589812001814402000400e0710780c04000c00c000700026108010f0469408126110664043e2441c10044551071400d555000542091030f50100081c04a0340c3c0030364051038465015440d81c03201d023030880c94401c403178104070303000b0580009001e142e0442d85140001c1d03400403982440042004200075402c0341e8a00008000d40e010800070400144500f541d80781c3c481c540050003814030780d641000d101510b03540d20403100402e800013841d2522000a00c0600b0704c2c4460350400002c0645400101c1e0844e15291261030105903565190b1403020348250112042203045200703c0f560410303444d44c124010030041e200720000b0002c2038030001c4210b28034400d0480100006040e600180e945000554641c84d10f01d4024080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 592226330 1250 592225080 592225087
    0x100c1d011404030b0105010f0309020d030c14010518010f1802040c260a0b01020c1503060d05011a04060510081f030b091b042f0c1911100c060c05 64
    0x200c090840030300001c0d401440c15401341e5252074005042d1440780c071500d404044c02c02c565000940c03038040e620400700745c1c580f8040c0340c4a1080e05148042210b1040411032950030001880308103000d1400304116804030800812600015091407000c4903401d090444201078400050307070241c91b09600600c0c5484060074807001d42646c001c1c1545c2184000c846612021001c001402000120384c0701c6c2c10260082030009100d040c05800014580310680c0c1d00200e1a07040020000c0c2842d100c1a8030a2400340d0301034001e0100c04950a000d002680c40b403071849000d107160102c0021146048001c0001090310b90b2580d0a890300d801c800c0955408003840d403400d01031240500000050303401c11045108040410103048241707130540d01c0c5614120200f51040c4074505110480305a1803065100300154410760520741001110240c480da07060003507042c40403803801225070080b491094404412045441014600301c0d819420003008074124080007040c0004440320041c03800110144c0c04602c45a00745c0c18103505 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 592227580 1250 592226330 592226357
    0x305060c1e13030f03050307090501032702030f030d05040b0c13060e010917030909100f140409050d081006080112020409020d0c0b1c05071e180314100c1d01 69
    0x10758481a04c0c210000340d4000b00700b001040d4480340c0000980301c01d290601c100c01c2c000d4000e00d4545a40c5c10a10001480380381e6107011035408101c0d0004400703884081d25141c1e81400004001808100c1d4144c0b506100b00700003903407015950085440c000150134003c041542000411038805030b5a1344114140280d81001090361100d07159082c4001c2109001076aa62000b030b02401450100a007560bc1c00216003078041c020307a6050321b8101c0660750943c1c02d035102050640c1c0003801402a20034003620601850b21000081c4e640f01e48080c2c4501980c80c0c8480349566111700c2100c040c1ca00b4031501d0010040451444014501a089015150b000800c2c0c102142225203480075484a6036108114803c00001c0e840e85860603c139942c01045a0118100006d1030300c000c3c042c01c0d641321501c8401c085601107141085080c0103440001e03c9007800201c0d041c4442d16441c3c18080c4001c5594410903611548003030380c802d07d110340901007004100381c0d601640803c001c648240340b051500301450600900003021035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 592228830 1250 592227580 592227593
    0x60f040f020d0b060102010c2d200102031608041a07030f0f05060a08120306150403050a0303050402040b0d0c05060a023307050a09050f061c060305060c1e1303 70
    0x80c00d03000d0f81d034080c16414000006421290041c18550910459940c01c0c0001c55684101a0b2084403041200900c881c1021007141d030a60610360751b5410880c250090881d070941507014620604040c4808150204611415112200c04840040401c00014640f0f034403481040c40c0c076900701006007808110300c100400c03040d098645003018160300030380c0d40c002c00010780340661548008094040240119511524244070144402040c160141c4440480229545190000c07100115000b5060395480f211518004000d40820350b4240d00c0f850804142c006280b504449058440d544500c411038468038040500001d604800b0544056001b20a6080c04070104c0210510001082c10300b0802c041c08042d459400e01c1d90080c010030300b04076061010305401d58110f40c151050301c0080f10003034001038003000021214440c25042c100051400101c042001d00340e5080360f41540d10500a8645955880c42d80580500400c1390f1503900c00201003403078200301d0000c0b004044120300e611494400b42d0b200c1d2600d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 592230080 1250 592228830 592228849
    0x1415030c07031419020607030903080612030c030408030403021e010518032806060e070f0c11130e060906060303180307030203070303021b061c05060409021201092003060f040f02 78
    0x2070041801140c0601c544c60741400300c00d500c0381c0c060900b005500c14030b4038000d180000040c5110b0084407849259500c0380b030200180d8044d812103100300c9503565101d40c8019141d4100b840304900820070550b8080350f00000c82040341c0c1b12041a07581c0c0b41458824895104840504900c4076054042c031504510b8505000e1603030302c8101c400c00d07440d03240c541342d902e014030480301c0c0d50b80002e003800300c680c050141c1d159100344000f001c1401458131b42002000360910b004001c181003400360380b0640d507600c042510700701500120020945001500e405030394280c1e6881d04c0d80402c03a545a45900708000c01d61089852404201901c403000d8210740d4210345a90205c1d1400406410990150740040051481c8500740300c000c407807200703080d6003043c10603544001d9100c0c07401080351005250343d2101d0020320310b51a076034001e05000c2d800410310381a80080d05d80b090300924040700140c440c14280e2044104d88011441940301c8600090b0040450b070b642c00708031120410001e48203d5941c3e02c0c407070140e8050380e1418241c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 592231330 1250 592230080 592230097
    0x20a0312020a020f040204272301180603051f0b0a030602030f10031a092d0f0102121501090e0a0c031d071401090b0c03041415030c070314 61
    0x30701c0411041d0040003c3d11a040301300900c200d0040105200c1da2030800c92142480842c00f400c881c1001246e50a00003800003018118030310559150b034080c091510303602c3c1504030b071001410070400c0521407000c0c00603640140800b91040e4081380c1c001015046d2000c1c500c0f600016004001040c819640005261030456401a20780342d8011060250440e001041b1a8000c0d54400c00e00c403501c0d01e1641d17101c3c0000541800f0060705202d200014029070400d10038401014404842e8070095652549064001e250421310140a886085100c000070501442211140711800420345015130f5076101c040e41054030400320904021510070b0009101242d0892240104100d0328081690304500c10010100d50340c44158001d841c03500300341101444400b144c0c000640d44160b002d42c8100e00c032900142c0d2040f0f05175020024420700000c000540c100044098400e5912603034024800740380310750401903029000c40c0c4003a84502d0410114482ca078100b40100002c91090802240280b414444003845070481040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 592232580 1250 592231330 592231333
    0xc0f0302010305060909061501120912021635060f09060c040311041d0703050a1104020f1b011d061e1e060a1e1e0509040f020a031202 59
    0x6204568040c01010f50101040c0c030000128548074903910355544002c0c000340b941000200300b80200342d00c0b41440c607440c42c40d036100038004600c8928090101603c0311004500500a00c140e19441081203000b0748101d400e0a552808070008410303040c5d8650b84410100c80c440f80c1c07141200145040203111841c032810950444450034503109900070b04041c0000e00300641d0003410403040c00042c98a503240d8405200558000414101b602c4c00802c0e00b00741c0058002251080701800820030100007407804411f481600142c8500a4010a000903401049800300d8084001e100c0380d040d4140410030001f42c0e116490000c0b60006c628524031604014030704600301c0d01e80000080005103550410351050440c0d001400181c036243c440d80c0d042c0000080f00200420070800c0d400f291155032081501c0c0081c011511038501c48800a0480e4015844188582d03441d5040500e0041005408010700104403800600440820f6545903140d812440d11650101e9100340394240c08804280d5900320740c414074083d0f40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 592233830 1250 592232580 592232609
    0xa1b0f0b07170a050d0f2d0e06150d03030f02070c03031d0a0902070f022107080a0203061b0c0d030204090609050405100905030f0a0c0b06191503090c 66
    0x100b10b4140303440c1c1105501407903400c01400c140e50341e011007207920181d21010000b44000040325488043c0603400e0010601c0002d600c0c0a1800310314000c1c198950040601c010080c504070030203c80c0c2c41e103500311034001030524008515030503810440c0664a404d0702c20b290000d107420040c000481282c104200a54a080030b101050081540000314107481034190804607041c42d0402000070526107090050184036900400c81c2002c001c807989100170082d83c003c004412070301c80218006e10a809170524042c00b8810300741d001034201c43c0404e480035520b4014000d4403599480503d100c500c1c1c0001d03050701c0c90010b810440050601d105100d1600d10000540d80540d44070701d49200d0340c0554005810004480d440c28080c0000617200080c864002342a01e0b4010411032031908000717043d4086c0c0d00c41031003004e00004620030401d80c4100001d114601c522055011600c0e98410700080301c2000c030761010191a01042840703150141840b024800a0a241c041000451540c940c4c100000e940e0001d601980c210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 592235080 1250 592233830 592233833
    0x200d0801090e030c0a11040f390c023a0506071103340803060a0e070f0e1203043b15011b03020303060112020c0a1b0f0b07 54
    0xa0090b407019114100042d424440055205611003200f440000d044101c4401d40b0101503c49800c074042004840004101d40101c44040d068500d5005240c0c1d0000012003a90481400380c0104100414015598800b0072160640c03c0c405814048600d2540c07204401100c1c0d00b95041c0c00840d45101c7c101c605064420b6030b03035481c100345000d0000c0c000c101488043e01d64504004e0380001034501c907510050b4104481c182545900d115041007030301075011910940500024089500011801854103843d200f5827a0741d00c02c440310f014a415600100096405852184264410040440204c5006004105400e64040b2803407442c0c0c029400300814071000c00b114030340d2000e48200059080c900d80b07400081a50a034503210b011100007801034810500c502d05010099200c1d95080c2002020041d107000c40b00c0c41400c000c0d40d0780d0806c8449034001403018004104410f03050007078a0803084000010140400c040d5140d00903031501c0180650410220400001d5500034800b603000244408604a543c0d200103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 592236330 1250 592235080 592235099
    0xb1009020417072c04060204050306071d10140901030b030303070e091501021222030c0e132103090c0e0702300309010902040c020106050f09010e0106200d0801 70
    0xe40c48010104400044101d12100140d074024480300c15104213801c1d607885d468004024040d540110760540719450420a080c4d0700316086805241e0154080e00c0908444800c021480c00c1141c100303000100741d604055820942c06016007000b040504010070301486800101e89140c1040342c10320005512201c1c1080349061080845401c0040807170000000e8008000103035036246d070040522810480043d0b1201c6404103541e01d440070001269a96081c6030f42c4e070030424000c2d21913000f40e8143c640001d003ca80790b2120049101800d60f401980b0446900361f00010426014071840d06c03105160321151101e00259981e4008004cc003180c85140601d8100150700030b181c84101002098810045c01c40030240c0c2e50441d80140709591840026035580d61860101e034090942c07400002c0d08541000c080e01002034040d042a420758405469007001c980c0d040003080b024540a01c10000c1c80c014500041c40203a1094400c030400030074052440440082c80f92030549043d00600c40e890002d0059070052051601c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 592237580 1250 592236330 592236343
    0x240c0e1c020d080318010501050d0f030c0f032006041101140421050607050c06150112020706050703200f07080702100801180e1f0f0e01020705280b1009020417 70
    0x445d50020001581001d001c42c000c64900100900346101000701d410425200d03800001c0c11561285005400c1c07070042c50041d0281d11040c0c5802030014070f00c0d1401c800407070300080b180c2c41a0740100600c2469504d41c001910002c00750b01d41e40042030030070480800c410b50074041c40d400c160388490030a040c079040c42c10810304242020b410301c4200541002020145900050010b2300480c8800c0f1101c05141300c0401a9520300c0c03010a80110720f400401c02000340704071588602d118403281c4e18148070441e00c007907072025903401409080000c280d05008070086194607001030304000c5c3c406c2812602c1c1148176000980c5501c080c245200002c1c1615005010307103004548419818021810140107081d0183d842540315801e020719040c10300303808211031440b040c482d00120303000d00075500c0070001c0c0801041c481e4041d42c1b1402066aaa00c21601c170038440c86000c403c000440383e000c1c80010003503940e40d0f6030010a80006000c9103807040300c458020558941c180300400051940000710400c0070000b188032400c18a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 592238830 1250 592237580 592237621
    0x31b0512190c0504090f14011707120803150102030901020a3507050c06090f1002120307090501080610020c19080312012301120f02070f240c0e1c020d0803 68
    0x605005031000c07c0c04400b2000e44c1541e00d80580c00420240d50384180e483d00c143e591184410481d107900b40c10920501c0b500540c00340e5004111030180100b40d0006a030703a0700c0340c000480d005a02942036080403800f820801640300862a804d107119038a224000b403450f10b02400c046250f0500003462a0401030104466000000b09640c031908142807032000450010a0200d45401502c09000c1c0a156510900c07554100c0034007550500e49a08240f100107118007281d00416011a1101011420710300d0560541c4000f0843c41d80100b100c8958807007442808010440441d00e00000d031500402c030440140090441d040540511201c20362500700c407000440c401c001d0310b260340200151207000310b9922035400c04505025a40c04182040c0724000d600c02441030040207096903107400051400c10400ce1b07091000c007a60100702038403100d00e0b139001c13108032030941524201050030160f04507143c1c28000788003072841c442d04c940c06202800316008603040741c1000e071048400346000070801000504642c001c41105 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 592240080 1250 592238830 592238861
    0x6010806070801150f0c0209010f06020c01030b0a2c0712050105011b030807090f0f030203010c0801141908030a0201060302010f0e0901030618050f0d031b0512190c050409 75
    0x40d40741103101128969454100c10421000e5040810618006c2c03101c40300c5254054841c6001d50f0b502d07480c5d4104180f6a014000050080c1c0109030300b90b610a016011010500074440c011107458581d138141106040c404407001c1902d006641b01e00c9d40100100300c2c1c85080a0b44401d1002050b0a00b20320459005812450500805800009800c42c1c0c2c8406120b00a071725041041094a40640503541a80142d01510f00b9103c4c990300450550014120101224400d4009200c810341031203043da10b001090180d00c180d910b050122828915084122640040c540c140c1c80c40c07040e07281d0000d18295403102e0f201d000540c4d190b01c000c00465078084841003200c0c0b0a8645079105161280014882c180188009005a40c42d203099541d100c0d6140244064107034401c04a6080f0392000070b8241c0c40e5500070b4600000b20b4601128800c20092000c5000001101c40d5107591034508081603004009201902d419003c00541e46200d005440c0c0740302c0c00c24070340d2054440f10f480c0c0e403030300811106031180310b64409101c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 592241330 1250 592240080 592240097
    0x6040309060206101d2a0c0d0302070515040305090607050a0311160b0d110a02070f0e040210030f0f1505041a0603130305120a020d050702280309080a03020601080607 73
    0x3400302c0c3c0c20905131404801c0c2140046d2240d501c5080501d002c00165042521015180070384e000307540c1d00a00c450040e038019510f0b6210a020705074201c2c000d0305c0010307100da00f0100000c554203c408607082e034068400d0501c0d50900d0410320114980e500304e04070440383e03070f44000e080070141900107a45000b0301d40f224004125441d4800c170b40d048014958404e240e1a500302207013980c0c244001e600b00034540d14410005a4560007440802540c40c5420310a45228260200c00407413001801480c082c81290098000c155240c40c4c4481280185002204d0401d00fa60318501c0c2082408940120240410480380c02031005003082c0800c4100d6948440f01d01e800c01c0398050440240c0c60b901c046e00d511605c0202c10f4510261a070034141c036603200703051180100c0c14103141040071a02d0658080e14007407041c40d00800565654440503030703564440d4000700c19414541c012206d480117603901e01c2440603102e0319107880e034196100034003482c0912508003100541c00c20001804940c00030085140d2010326490705551 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 592242580 1250 592241330 592241339
    0xf071106160c050f0d0206060901081203040f111f030b04150303050325020304030c080c01120e011d0c10090b090105070c051e0f0406030803010e09010b030604030906020610 76
    0xc244035011001c0050120101c020018410140082c20315202d00200383c428140c11600b00070b403600c10441e40c252140c69140c00104160800044032240008811009880c6072125181d80c0542d00c4010070880e0000424409004d450b210681e024070701c01d50481724241c600c44407290103410744008601c4180101d203008070b06d03c10011084484011a905800e100f6683e407122240600b40240103c440c00c5904a03000000070090f50020081c01101e0080e034825004540310f5003a10b0b2505010740d40c040c005541881000e00d0007100342d1204035080c0f0302c140005030306070b8205801001110304030750075032554102809245040c101034000340c2c00580a4034045c101c840c10040343c0d5200d4050413000904109010801600300714198180c400540001040c03041c5406102444200501c1e10450f01070040248400c0c0c0d0b0410308150045209480d4094002070460382000c031380078825440208503c45542d21907140d108075840500015000302d0095903020415800d02c400070b480d1440c054510700301c03600219030800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 592243830 1250 592242580 592242601
    0x3120e030334031d01050f0a0e030723240d090201020c09250e21071e0e010503030f1605070b0d020a030e060108151e0f071106 56
    0x6904a66200395102501c1000101c480c03600e00b80e82c1c0480301d40400c49044002c0c550000a40040610b6400d00358140c52214001142d00d40244012a00703403030720521011614078000c400700191030314090121009a40d1740c10301c16126400b52203030441c0070800c1c441482414108906030311203026600b055000b440d0146501d1301c2603841110000c1c50380c80d80c0e614030301e011a84203124045c0c0391342000309072440394245400000c2d100c521864144003102d0f551456014071a00400760140b10500c004d041441441c5600343c00074240c0c42c10003110080340100c0c01d02113044103c50501c499411012900c4510403820011036540c0e260040c0c1001e4480e0703006000280500200301c08491001480803048025003044e80740243c42e015080c0c20402102c4130100e07484142400c02d40c0905603804040d0780134440140000345442d02d461080c01100c0241d000030703080f4010804550002d80d000b021050303420301c1c6000d09101c0c842200030151804a00c0c0e02120703050060141d800720340024442e0034000030f00900d060294584 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 592245080 1250 592243830 592243837
    0x417030a0b24161106030f0f0703140105060a0212040b0c120c06421309021008070909062430060909061d0a0f03050d02091903120e0303 60
    0x3c103514814001c2910420120018044461001030600b9440707041078060710701031400c11a0030b0f03c2c505915030300040320980f00b801201c114982c4e03100e600c003e507401e24081c0210341c0c1c0240101e0042d8840c0203107411400544030b0080006100800004c0d44696035451a94108070700480c1440d052841442040c10380748010410075003003d010200e00b007010760000044181c900c1c0d040c440314018852402c0110340d034520100c13400200740049801060382d000301d682481c11240d8155000c0c0d0410f501207244c200c078600508020b80c2100560420708251075881c1c480c44140d51142e0080106406018101c4103490710b803103001086a0120b05004024580560000302018005401d094810360808121b586140b4640e0058015010380501448044041d05040001e00340303911034a005c00b005580796401907034010a5111102d0b51080c00340401035407a0318111040c2c2c00240c400d440d2540d0800580d00f40c0d5a40302200301411440c680c045200d6840c41c2080d809103044010980c06110400350300e0b09483d507010045 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 592246330 1250 592245080 592245097
    0x5010c0219030912140d080403030e120306040c0903020a1d01060918110409090c030213020901053403030504050c03010b130e031605420417030a0b24 66
    0x10151414400d040110401742c841500e9003840c0540011a40c00562012200344994000d031818070403401151080c6039103c084441060080c0402d0004c110b007850281c000e8002c0319041d2421201e01900c9400043c410348142e8004400e0704450301a01c02c146d040507102600402241c144080075603d403500f04005d56200b80e0702c441c41c85684484180f480440030060f90007406030540c0400050f12103180250020029000592140003603409181c404000b900840e00011410b0b543c44e410100c070b40d410700d0340783c4080c02d04207076510380c0e04004605030308221281806100c1c043c2c2e6000ca00d908050400505152101c0b0b080c600a07414050000156254642400c4550610300800038141459808540c154000d204145110412200e00b4200b030090001d0a4258205100c05506c0c0c21a5400d1034040d403c10200061a80e0260a01041022150200c200c035803140c001c801c90804403c030b83c8400d13680c5902c101d030141200c540d02e000282440c1401d13002c0400c0d840c400d08210705108400d0644800c6405130300e00c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 592247580 1250 592246330 592246349
    0xe0f010c08090a08010e24010609030f0c0e04060902011709070506070c09020406020a020a09050f13051c02100606081b0307050d0c0503010501030c0e1e030312010305010c02190309 79
    0x80b440c080740c4420112030002e140ca900208100c0080c0768507542c95201540b0420345245825009030b03040000060154102c54917611240a10b500d5035840c410f16030b21014040c1e44000718038400281d5090455982842544210000103100d4030a200241c008540c5174000d520981c070500400c4113032240051042c0a5510454105440320751528080d000100250080001940045400500b6517000a40d80141c14402c0314030913040c40c2c03a46160300840d001100c450b00110341141c0071030f00c0ae040401c502200580100180c0301003d401c8150760740b503061402070140c01079100595400c034a645030302c68440075201c40c3c03528410038140809000c00c05145202075600d10316000010035003180c0035030704079001c14403107075014030584803c000041c043d50000d20980340400d003440c0350000514803960a00e400c60704000d00c5403401614841a000c0f09060580000d60940300410000e1088807044940d2402188900c0011460b158400340007070800d030760343c5202c04440501a46100009411403440070507141c4a04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 592248830 1250 592247580 592247587
    0x11060603101d0f0f060c03160f030609141807060e1c0b07120b01050a0219060b04180c0902030601051b03040f06020c01080601050f090607111903030e0f010c08 70
    0x22440a18070040380c0c092030b41880340054903402540045610f2461405500c1607a5450396800002c840c40e20040b1071080c0800c40d010003080d03005009460303200344894545400039103561203919901c00ca03903501c81513143c03c83c0c41c3c000308003098a80599100c0d40c41d030410040d10f201850034002401c01c014000f052403103441a03007070703241a07044204604080d8a0300b208545005040149024042460b403105100e100d60611146982c5540550111b90040318a5401440034107058201c02c4003124449004032a03043d240c00980c590380e9213500580c00214501c20403204410381c145400c0404406d50b60011004074014801c01085070b80210a03191040d65080d080c0c03262151031040d150451246400034111440040e0700466503a500182400801c1c4c0282c80d02c4195450b40340041d69540240344050345214410090301802e404c02801034030341e541c0300d6082c0c4040015032070f0015203a407403661490f180c0364a04c0b544c2001810750120381e590005a0940300303034503514000c50009192020b8550050300c1c542000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 592250080 1250 592248830 592248851
    0x31e030a020c03070803040303051e040b04060f060807050a081203010e0405012318061b09060403051c080f01180209031c091707080303070f0210020711011106060310 73
    0x58040b6041a151070041c1c0b6030b64045464003203d50380080c0c500b03800091520002448a901d901380070758120b010b0401901e6150b40d20380e6401d682c03400040003142d0f143e84a16100203840708600031b139005420620007402e0071505000c24000d00040643c030103903041c1d2008910300526100d8104403415a0148122090f00b580c40e03080040c01362659211000740143c02c08000320880343c0b0602c1f264094002003c80e103000e01030708280300e551080e00751f6159241c02d1100c00103103544002c88004014180c0c1c0605142d0809613030392507541c205034440d1816400f0072840c0c01d0540d00d00e071b40104001e41c0b04c5c4404030044c405504292148003032880c808088200b10345e0000e00c40105503410401030184504c600b2001e07046c1c051300c820050500344c19118262051035800c0499449110214200d41650170000c01581140d85032001100c0b5050918001402c1d03004403400c0c403104140740d00041ca591402461000521103c000004000d060302c92640701254101d0400d0040c9517401050203042455144000708122020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 592251330 1250 592250080 592250101
    0xf05220519060516081603020918090f060105060a0203040905041e110108060328020607050a06060f1d07141306110c0d030206041203140f18031e03 65
    0x111145a2440d00e010403112080000c5504924428071300040010141002214103440015094440b01c0c5c058507a8034482240601c00d41c042c00744450000c00c4005013064409601070300c3c00003604c00d06115040000803244540040140e1401040c090310300d03600d025000b00009459000d01c3c0181c0390100e8881380410f09001340781204d401c903001c06e0710808a000941d4900181b08141c200034841c0490109400650307540340c0460300340901a100c148080400c07000c2405a400c040032142d040740d1000c000d000030703001f1039070822a0302c04c824400ca40016250b82042c0d65104805000ea21180e03642850200f07150740ea8504103929a00201035040c1900c1e42409019042d00a000e1811104890080b00c0b0000a000760300c50800b0310a6a403220594501000010500254005074070b000380141e071020010500040e900910b03241038910714500095042d0709060000d110200548410400352961003d000c4014080720840b41f414002000440c64180d04600c080b905a10200b20712000260100000c0c1c0070509 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 592252580 1250 592251330 592251343
    0x611030714010f111902120906030606040b0a0909050105060301060c240c030b0a0b0c0c0603071b14100e06010b0702060706060605030117060108100c0203070507030b0a0f052205 78
    0xc0c600d20074026000524420701050300200e104000c2441050709040d81c640c000305120300d1f40308500130000e240c200c2d85003d102499001a208a820035000c202c00502040144042d200340d9610b650b504406524007046142511f00c10b07001548550010001004100d81081a03030344040e81c064100e0345811740c001c1c0c6484c0c6121050500400a60608440f500f59a0f455031059190810846030042a2519950218030b40d0041040f00c25440d441101440600e14107000603590021035440d18403100c0501d03151180c0007001440007226441c110b9105e500d1100800e012486441d607520300104240060008041c3d620315041c469484000e0002402205641310070302218403480d000103043c088280d840b5401850b40d407003485002c025606501d2030401d0002c1c0840e915040720b080078028407140032000a810f0040c6140382c5e8000552004011280006505001020045000d03480d0a2118502104004c007502c00c40200d84001902c1c0c039082019200508140e0040591080c07018010900c182c5403583c902034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 592253830 1250 592252580 592252601
    0x209010507200919060803070203100b0310060801050f07050304030f0305190207081e0a050304061805010e0a050f0304030507140303070b010e06041109030c040e120c0115061103071401 81
    0x302c50100102400d2070007001498507002c150402171140e86040300c1d40c5034003400d00020b600d50070000800c80122140e4000b03041c882401810f0b1a540101d4801c1d9008940b10ba522403d0903035195820400c074881d402c01600d82c061545e0401c5071851505543c0204400091075100e02417556480104440808030700c8129100071204104560b1420b207401c0601c0f044d0001010b0001c1c900c0ca01d10b00e101d80c0556070007a01d003084040c1c0c90f00380c00ccd41c0707803075481d5000340a40410009640e02040340c018080742c42406420345411800028003100f0784a030819a09192038550440d050741c1c01000100009080045c2e60012510070f054010210014407001a0039071180d00809405014130600107c0d01d49a000c3c5828000c4004450801c0702004201c5001c8180c001c8a50456140e00030f4004400785060a4004500e02d4100b5820f0311007160901d0810841908004c0200080f40c1d035400418030300f1500f40c4003a5019100e9820002030501112040b20b40d0391260030300080c044901894005540d207000d41000700c82c1d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 592255080 1250 592253830 592253839
    0x200712030203030405190317060415090b011404050a050607020f19080c040603030801090b011403090106030201030509070803070f050c041b0f141e1309060315020901050720 76
    0x2000e09000355241c005550a1382d503400b440c09400700500380700d203901e040d6a070b06481e11920560a500100e010140051855800c26160b0000c425400d501003003a40203400c105100180350304480300014098041d202000c0c0584004201c10311107079841c00244000c8a0080b1511a0344030903910120b82c0d02400100c6d069040040c105843c1e000012490080c4140d800042c21108a0341c1d00c00d0401080e03818074800030300070451040041c0141d000c290401c881c0d0324410706155000b02940d4442081b140d008840c07074003142e55074050a10031503a0500620707400c410070200802c2000e0070308030010f450380f25908000703010251481301c500130040140400c41c11b02d04020000c0002d003944074806603041e99918006000103402c1d13103c5038043c9001d400d03441c1d03111040b0030b600350600c620041030f4032045040e10300070000d030b04c424020128040d210103040400b400500d080400c141d0310f94900b500c51040071060680030391b4014005010302e0b0341d12a0035150f03815004001c1c2e6050704200c0349401103d000c04051075410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 592256330 1250 592255080 592255109
    0x901230d06020c1c031415010c0c060e031912180905040507140d0309140a0801020409020a020d050708030708040c030b1602070602010c050904092307051504062007 72
    0x43c03035001c15000c0c80300d210440d40720300030348501408604481c00961040090340b44000450300880505d14109280300040c1006814480c49407100c0e5403c1e83c03c2e600150000d599400328490508050001185000c0a056121121800c5586002c0d00f10142441c2c10204031080009000d26507120b20030000422150f0010410790a040c1001601e40410340a8100c1d1003c450700181c02d242440c4440c5d00345140c0698400b0481410081801c1d90360b03900880c1c0550103140d505022840d401c0070b20050005000a032001039943d11558030103410100520103243c1071050034000720000c20540812690f02039010f1511541a503a50f203030003031410441c0d400c00351214201d0400c01030200302c004c0c2e000c24003400580884141c01e5403000201c0c280c030302c00c0030030700b00180c801d020000103410140c1103181154415550448020419545207100d80c43d1241c3d034080c240d109844c01c200900b002d0005450400115081d5032401d82481000b6007001d00108603e182e00702d820146480b010b02c14405d500181401c05c13a0b1110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 592257580 1250 592256330 592256347
    0xb030106030f11041a060702040906110d06050a050a080d080c120703090303060b0430020d0b0103350a09180f06091a09070e101d0901230d0602 63
    0x44000000113801589480071900024411030403a58000c88000c0200d07180c140c46a007030101610129030b0886015413510382010b00700c103002e009015848100305001580714038180c104805000d4680c0224020259880e05210b0000041281c09018a0501b080300d00c80e01c50307141043d82c84c0b1881c0c00d03500005145034140008241d060304103000c0c49000399018021541c580c109103d1038400c612424102151620300070010b81390454034240f210700440a5604d4140542e000304080c078881c02011903d1030428030061080220a09451158005e8403c243c1607545180407090760009000c145484000004112000000d2080e8034030b0300600140810201c084620f485148040c1480d44400006642401400f00341074200c1d20514042401907905164501c01400c180a00c04801030f089c0c1c01040400c2182000d131780c58003e000881403034940e6407000054821a14a42c465400d881c00038411f8002c480104580d0030001c26503020040d17040000002001c203500025121080944010b101a0010810b06c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 592258830 1250 592257580 592257593
    0x1c0f060204050f04062904031208040b18150c3f0f0a090c0b0307050315040506090103020918011e11040b07110f0904050a11220b030106030f 62
    0x1c02ca600903506088410881c40401c400d9400324002c924120380b8405031042199030b0b00c5900c1160425046400d8a4551a51614280c8450007503114010034030001c1800200213003228110341c44260f003248420072942c2c0500246e1152200440d20304d020301f0041c003140c203120100c8229400c09915407010009a2151200840380d02c060301c3c0d901c0c40b18500c4c00100001d000307144501a210714915110100d8640d18890b10000504108100769241040d0035000310728000345400450090001c0d45603a901d034506118074007600f001c0e00d003129014a041c001417144c5510380d8103d050540354100c0f0605c4491b0399071580b1134940780c40c00400d0403140d800c2c200c54084008840302c000000c0f841050080c00101040c0c01d01d801507200d01e1150106050007040403002184001e00d10703d6400d480103101c200581a4103002507803400091358227490039003056014600700210400b01c84440e800c20f8415100700025a02c1e4065103c1c0c90203548610b443e240c1c5103490442e80c0c00e60007900034544c0204002054009400c090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 592260080 1250 592258830 592258837
    0x31b0a0e030609071a0c12031308070b01091107021f1e05220e0a09030e040203040b0603010f0c020a080c0c09040b01060801140f06090d0c1e120c051c0f0602 69
    0xd2005a1804200e044c40d2801d0904490b4160500c000429071f80c0e102800105850f4401489100406685400c41001810329402444414001c0801e80d00a5041101040444c0c42150f100c1c0341030802000060300507203402401500124804101c02c819440045044c0c6030401210032060641d41000103d403a8140c024002e0701e0211200c01da407180d10407541210552a024038001e120b8070300e0f98007001506040c101c0e007104010341c0c40382c900829811245008903080e03030410380c2c040b9207550111080000c40d0909128040ca001e24840007840010441c5601035180c0c80c1c8450050854640000c88104006007000242014a0003130000e003401c2c605402c200070004021300809000900400c00000c2082c0789004804040c0c20040890107540800001c00c200769200d240c400b5001160410a10040b402d9821000e00608801c2c0c031259060f1000b05440b0140031541e003040590200184a40000c80c0d841c0241500b905e0080c2c410115070615235a0020b541c14a80a00405400d4a41d800004002080e0040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 592261330 1250 592260080 592260089
    0xb06040c030e0607110c190b0d020f16050c09070906110c0607030c020120070e0915012c1509061206090106051e010c06022b020406090605031b0a0e03060907 69
    0x20384a024198004000d40701190b1490707803240802c030480600075200d8400c014050980c1c00000140391608240424524cd0000003150054807140842d54061000030701204404e03107402c540d0186d0a1800400242200ca040c2c00303844200411990540d0740144100214207c4000c02040740b5140c1d982031400030300310801c240080307001518842e440f031302202542c039809040561344006400113905196001c0e08809004011002520484202d103040944001015000c0d100750300100b0304244440121310555140e0780140303060610694200800c00a40e1000e11440c20021100d50303160b5159038000a0078003011038030710741c05401000140040c407407056002070112102640c500c2c0084002c00328a9401d03911500c290360100b07800503040e40006006600a000b104030120310350a0444070800d2016030f4101c412061030116034002400d00800f600060003000030810b81c58180c0c91880c0003a602031601d002c0310381c1c041c4021004141c90001c54061043c1c0001140e016048032114900074841ca40c0e915403a104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 592262580 1250 592261330 592261333
    0xd150e070e0a0320010e090f010303022a190819050c04090b04020d0201110307060609050a1512030917010903080916050909100e030a020d0302070b06040c030e060711 73
    0x2601e045400c1079031004080302c0c0c2003484031000b03a416803034400040b40c80e03056203070410a208181d02140d40d1a040414015074580317406198070360440c50301a18148128400002c10030b2259101401900b120128030507008050354542e0307800c400800042007140c055045103c2034021070141c09040810080c02d90701e0940188201d92402000c0e0f024441101d000d071102a0500f0102c100060160401183c0c81d902035106140035080d444038228164110307000484112034040c0c440700100700d40c40780303030140315004440482c04015007220070713200c01142903031031082260100b120740c0001c4c1414090b000074030050641c0040354424104020b0350030b0082c000040308030085074086011504007200010340450340d49409106410081c1800308115552000030001c40c040c1c401c1c5000b918100c074190250200c00c0103250011525421500c1010741400550200c007420144140840740214200614254010f0b5040d03800040c00901007030b080700940f2139082101d21610440c020f00003500da1214611443c00c40420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 592263830 1250 592262580 592262597
    0x80403030f0c0518030c09070f02062203110328031a0604091d0d0215070c02150d0e1509010b010c0804170a140610060201050702120d150e07 62
    0x616680884448410b1100000c1003801103c00c103107481215100c0c0854001d0854044250000001c0e4042c0c808a6000e8000b40b40580c2011000e0303010024550005040486400800041c500c451000034090b40050200500500c160310303000b500340202c40000c50160310540d5240400c0200c12440c80c00c01c41000000f03841d00c15290291114004a540b000b5070042c016850b00b480d0001c0d030b0000c0c00a0b4807964011404040002760b0140c0200004004448241c000d0040c00058a80b5180c0051000304801c0a02c240300142d5001130755a10707074040b0340099411000e900c401304580240003d10494101d0080781c030444404200760002c481800b40319804480003030080345401c60044903105440301000f841070354280400d000350071400080f1214040480102d440010140d26180000200720301d100304a50048d50070703c4000b8071580c1010015081d1030000703000f01d08220304002d50700c455003030150f008218040b41c83c3e58140343e580c0204500845415070b0034412a12416442200780c804d03a48800070a0354203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 592265080 1250 592263830 592263851
    0x1b0c01090902030f0103060e0115030c0e09061b0703031b080f06030a0f0f0503070c1701060611030d15050a030305090901121e061509050415060f260d08040303 70
    0x14001c891003144884d0b80d080d00f5034030b140c4d5024040c2040100102c41c42d501c40540880000c0c108014500070760041e60207004c0c5070310b40982c025031000c001d0400c000c5504051308014407640c50802203031451020311a025554150341c1412002441401e620040b9200780c9519011a40d900c80040d50203888000b0429000d40c031a41d003096521207008200030951140c4466803000304240c0701c61b551050340100292440d01c3c0c015a1422040540750300903290201ca64074040d81817440912a5101408103400c4c16544281100d0426035240115030014150944a00740c1100020390742050720003c000203010602c845869260190194010b404094001c90313608000040001107190200075564211140164165603140c0c005008071003444203844903078492002c0c26000507640e2000c001099003e01c001041d0a040c58a958409807040d40307900e05e203040100501c426582050700c5021501d0070704400340114109140300140b01050b290071210742c0103000408966580010205210300c0c071994040040e0580d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 592266187 1107 592265080 592265099
    0xd050d1404080c1212040b100306020c010902011803080a0807020307080f12130b0c0d140906041b03150b011101060602070f21030806061b0c0109 64
    0x40003071194180402408850007265090707401303600d802c000200f5400114006030001c0c2c501030358400443c000800e07041e070141c011070b8840019501c4a20301c080480c003c000400703040e03000c80c0ca0f100100c00c0c00030041e443c5100b5654061006410300d040705a00b110312100c02408001035104c104030481c041141e01c0050524034613089070607950780c1c1c102d18030700d5003038480544103004030794039103001e240081c5100b41040d60116503414030b82c1d182d8101942c0301c0090700101c21244615400e01e0140300b0002c40100d50184518003400703c6031895040c0c2480a0804d600318440030b41715901c041a176151400164010081c1604145410f441d46800404e8542c04c48046601940141c0e1105104100307921801420701d00412030b03254404000d0b030965002c5140031221003030040401400200045843e5110001d4521a80050360032482d007903000b08015039545103138901240480d048100c005000e11a = true := by decide +kernel

theorem cover : BRFrame.Cov 592086330 592266187 := by
  have h0 := BRFrame.cov_init 592086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 592086330 ≤ n) (h2 : n < 592266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
