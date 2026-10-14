-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0542
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:21:07.105565+00:00
-- url     : https://prove2.me/submissions/2002aa5e-25d8-4163-96d9-1aeb6777a40d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 97302158 ≤ n < 97482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 97303408 1250 97302158 97302209
    0x8030f0d0902060d0c1d0105070515070908120306030d03060302211e060f090304210302031b0a061a030706080c040302100203040305070b040e0703021b10090605010f 73
    0xd07001260301c04420008000c861490344541c00d031070007455448030040083c0c92514080c505c00b2481050500800340015400907400003401d0058000540511142e502c5040003a10f410031140c109116a02410312032504000000010f1441800214107c501303000d4190003c0d402c075142c1e800f001e90000c080c2e000001004da5803488104044540c101250340741c08104401c6d0f00344001c1c1c4a00401680c00402c280700c0c0c00c5042c0d4519076040007103039000c1c502d400d103841c4010610041064140b496800301114801c140b6000b801a5034195100608020401034a02c00c030701c0d240c03400c1c3c035011a0224078051020f00c042403180c414101030030f400382c000c2140b142422000c3c0c0d0246002400f1a0340d0f00b00800c00480161598001b003070950110790010340e2540e086203001400c010321900202000031060004003d540da401c0c1d465038000042d81001a030300e10140c51f42104603a480b5208850358883c0c410310840d58107c503801544802e0041c20b003000142d8070358442c0c0312800502c0c07040400e00c60b0020000011038946 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 97304658 1250 97303408 97303421
    0x3010308090108040f06050108210903031215041409010f0b0105030703150306020a0309051c02070501080c13180b0108010807050118090c0f0f0e0102062706090d030608030f0d 77
    0x240d100908400b1040e1b441500b5210709802c6240c0d1900480078000e6504030030003404481c1c1da241e2007142d091a01d0f44c1d001c2039407402080e0000030300704420030205401c00038101e40703a108901c003e48140714410002814034203094041c0d1320014a90b00e082c5503045100500d01c41c4026201050396624615143c0d120210013804085162810702d0100900c004005200c034401007a170815140c9012501a80d503041c01c605102002803071488100c0581c468025080d0f003c9620025a02c3c00d003072200040e00c1e9030b00004401d008181d075011001c5406000850507071421922410220342001007840380c4400c0c4001100c0400081c490f00d0003c0e44000c1041c000c0d5130003000e049808602c5402d07421000c83d5100d02c2001520b02003a11a40800d0072800500c000c00d0740044852034501090414031926131417400000c0d42c0300001051008040007055420100a504228159040b0124412a205c03410030305100e54654403141c1c6190040380c40c0140000e00010040103491419402503245400c040c044010307100503080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 97305908 1250 97304658 97304663
    0x6020a0201110711150418020f0903061305060a11031902070f11040b090702190c080f0303090d0206100315020702060301180b03010519020c120708030a110301030809010804 76
    0x40b070380380c0724140c0d01000010700b0000e4001e814040f80620300b40705010401d90000500f0082140401090110451800a0036020000010b00580d5035840084445050141602c460383c036028101c01d10060441d6084908605402042685c0249c1c60f4403035210304036820403940c0b018a0000b840003c06250304c0704d180301c4003200b124902624007021030741d8980306c01001400440b0914210417036406c2d20b003454410059441ca096500401c0c500301104041d603113a200c44070a812104d4034190309810041030041c0b40c0010448842100d03100e00001e0005503c0390800c0301c0607609803240020404926100081c600d009940100296402505503201d003101500c07525001d0850580070400c500c0103881c0c03c0d00842c002c00e6501605c1000d4503a070350602c02581e40c142c1159220760b06110520a07118155206600399050307407000140d803485000c074128102902d40290240f0600301185640c14804401c1c000c40c0700b407030000d01c00c10032104101e5182101c5d0000307003c082d203c1041031001c00945d5006d43c00b0140c0050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 97307158 1250 97305908 97305911
    0x1409101107080601030311070f03200d0212010209191a1308030a080106020c0906010f050d0b0d060c2a060e0120180402040e0f1008010507020607080114090406020a0201 74
    0x945501a07140f030110203034011000601c1070244034179166401d2050701d01170001c20444010140c44c603155124004641907100c4d00110618400848594440091410050f800303440c090349221a0a60395000307420078100d060051441d000a0350080644e45e840c1015a44540d44a0b1060b03e503a15074000e00341c208074142c4900d4154407001080060040019064074a4541e4a02149605141d4002e0400c0030010105019002d590184080c030f0383c010030600c910040701e180c00e585441100304024090b0a103202d01a421618042c01c250511000713800111546459844228404000d6080c40341484a00c5607072580d0b00342200100b0300061805e402c4845482d290318004078001c106882c151959101d050b01d04515420001101005140c1c0c4000024000340112030460429107000e001c80c41d84c0c07000900210081e04544001001c070315031281840058840c80000300114540948003941d01c200907169140451030303990002555114510f0000346225000c2d00748403058136940d503400040d40144070000d0955 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 97308408 1250 97307158 97307173
    0x51003051906030b15061206040c090509010b0d1b050906030606041d010504060803040e010b090d0b07030e1504080d0c021c02070e0106090302150a05040302150a14091011 75
    0x603901c07800b41001550288800c01c240b818100e420101c4511000c201c0c2d40600020300041280c04010100182c0c025803d0760045540410003004403050b4040d90845540400500700104e4100f01140142041109130304082021001d0300d562489040411001c1c0c20020f60204250a458180300000c3c6801000113400e480c02c20703813128100521000252040ba608090003401003040345040c0c0a480000c02c00e18024603d01400c2609055014805002d000e410107400241c174141501c0e40c50240800c82d82004100d400c60824170f0005018101442400c1c04612655114084210740003c20a001e16881181c00f0304e08810384040b81e018003142d612140070b500690116242c81605003c1c40b00340318000b0341c058020302d402c100110081c84410382003d000c00003c0c0c0c42c11300050302c07403042200002d012201e8a5465008049040781d07903100703980000390001e000c11003001c6c103034900034003800c2c10840680740c0394007240e0b00801c01003040c014660340a074403041140b0801c1003d4001c0350602d100c0800c0030140e4411 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 97309658 1250 97308408 97308451
    0x30c03042102100509030d2a02060c0106180608010b210109080414010206010914040201180f0b04060318030e0f040f020c030a02070b040e0c09010203190306051905100305 75
    0x160325600b03550303002007000068000305d6854240580c1056002504144e0814460000c040e9000e403151600205040c0c0b80305511001d6690b420259800c80c0c0da2800284600c0c0c0e15a9140c0018003600700e50100c4a504201001c42c8500c0103024071003900001501c000354015040018036a0860f03450045e0113030b55a40c0018401080c8407400400252880030702021152100c0c200091030458141e10445105107070524010240200c46003850300141c0900e418000318102c00d40d0400941c04031781c0034528284a1020014003500404050000c5601d151010408003240e4510101c0150008100600280404049110610780140c20300799019014200244041c17410404030120303132068072039001700c0d400410103880095040248801501600c01c40d14101031420707200f8401010040c0c0180b0903c007002c2001701c81e5900c00c0044c5d40040d1201e417144d10404a0380e510160082825001d980d018442c040340042103801880d100300d084410103821429119240a02100100350242c503140301141d42e100088a03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 97310908 1250 97309658 97309669
    0x803190c02090c09130207050c12070e04030c0210030e0c04020a030209040f02030103050f1c1d0d0c080106091a060304030c02150316080c030703090809030d170108030c03042102 78
    0x108240740103a040d96850381341d08005a0040801da448622801080104c0000304d004c6400300140806441104e65080d0340d80c0351034200380654000382e80d409001c000300320505600002d0056040e0080d150360480006012045051300c003440328400c2c895101d103042451906259004020b1800e051600605001045000406807181c40010031041ca8001c8014001e0007414004103001329680c500400c20b14840328100c0c08803400d503403002d030184a00100840b03500039401d56940d0304400010240d60b1003c0b02454040c40d03203401343c003070029190310b08600810320004601c140fa0b100d440d10072503141c0c52a0b2100401100e984000d20031020481d040d2205d5005845401c0c1c118811070400d0b405036140d01e03150710f0403100326440040410130403045100344080300b803202e0200c1c3d40103105071601195170011070400d405c1d54400e19207610341610030100407002c8642d01080d41d01c02e0007803421386404142d9850403055a68000c0a182c661079400800003000303034440880c064407034904044620180402144c00240 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 97312158 1250 97310908 97310911
    0x90708040b2a0c0132070503060604050406030506071e0903020d05071a04030b060a0b03010e13080309072402060c030702010608010603030302040815010f1818061407090803190c0209 80
    0x10460b0f07464051229481201c01a0b01c05800002c00c0170038003129140356400302003807014107a074050100c0000030481b151907a43c101e401a01000d007080c015142c3d0380c03420580da800c04585010004490582083c3c8506036100c0b8144014103594440c1030f11800c68080000074002210111340d5071103002d00c00210f0842c00d01c0360f10130403c0340d02200c5032100c0c50b6080058803940e001b007090b031051041e41d07014004c194500040d00d055494907080c0c028503940b040302882d45407645141c050003d00000c005c02c20700f03400c000b03072400903124846000788510a66008006c002510303c45140090b230001d0700010207800603500a10752100a520000c140580d031800b11908545240e002500041d400040034042c030402006041c44003004504036002c0c96240c0070b802c0c182540704d03004e500004400a0b0108484d0f01c030541250a00d84801c0d103c05228201030303e400b100034116000500d0b8050039540001e035089010701070041c111030301030300a54900004a6a2030028000610030351081c00300c2c0210f001c001d602d446801d01e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 97313408 1250 97312158 97312177
    0xf0c050901200d0f1701060c030c061e05060a080f0d0c0201090b0d06030c0e0613110909090d090501080c040509041514011e03020604030204020a031d01050105090708040b2a 76
    0x1280310007000052902400c117404511070884030004224041c0d00101258941c0e03090310300602500024580140545140028407240b580035a503d0001c15080e5808103015150480b03100d41d00503a107480542d21179040d40b54888180d0098165890320074043ca10003020284145001180d16494820f481e21640108000419042e0364400c28020003820100c0a80a8030311000280840d107400740c0052000c400480940341a41e448041005040b055002074510000000784210713414503110079155030395480c4006e103100240f94000001503070b5001d00c4a9500404640510900d81401c000030701c6a8840b02400c100c40707040b4581454861441d00b40300304140c140a214080070319502d88501d00c45250411a0500c10b0340003850f40800069840d0011035044907030540d40503880c2c4600020a80c001c000303000c0203a074220f1002c048042686410761013181660801c4440020544809004443d1088101c0c0c00500820f08027010030740300281c50b5080c0868490303900103401581c25906100f180754000c003152 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 97314658 1250 97313408 97313417
    0x2506050a0606080402060702010c0309050d050c090f010b18030a0605150901080d020714040b04180507120803010905192f070b07050705030903011107060f0c050901200d 74
    0x5120a41005010307000081501d4504944a4142500007400c64425030740c00a040c004002c407200201401560700070b009140003004000074070a241846600c40c518214110712400c10180000c5a00200ba60745c10705882842882c94104545890072429040c0c07000041341d454454181e12000103a03560103514460040400190f0400c1601030502c42590410381160090303802c401c040710400360780003401e203089603018455a016680000003003001014900d143c9500241850786604441c014000703c1c0c0c14207446001107500c1c0580d01c203482c6030010440017005000300e00400042003002801c8d00b2040d0040303910502e8802d038400400040b82241d540207114891550000400d4481c100c010f000c5840e0056807120071450a40c4030f0350fa15800301002003a40d018002d0125001d03003888010001d4941000002c3c000b004000c01c20044884942c00a04003140e03a030f418000c010400b020a0b000d0782e46545002c1e01c5136070038490500010368022400c181c220208080004090348049000c00000c0c18850190f110b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 97315908 1250 97314658 97314661
    0x21002030904050123030d020d1b08070b0405060c030106050a030e03130f050307060512060405040807120302190302090a06050306150316030e030406081b040e0a05070905030a0503040b250605 84
    0x1d100c0107174811202a4031a8211a5400c0802074000c501c2c0e4200f10340c18504510040783c0c02400e881e001c00740f900080c2402c0c00124071401001a540203160045002d54111603980d5280c3d426004907210901410002400c144140300407107000f90801c0006d44049416281000542a804c03071100d4159444185402504501003002c5c1c14140602d41c0507142900d0900c0c6043c2040c0040c101d4604040e10a50003a603940c80041c091056140035114802d0b4083d1008213140038071040100079410520071a842030080e4850112114060301c2120b40d0724070090801c41c200c1d894500300b078405401c01006103030080b52803010020008510b0004510850840ca00340841c03640c5880020221400055803001e1680100011702039150440401a40004c500e0110801d4010049440460780229400407102c490f14205002805803280c01040c419000341d611a0040c2d6594010540c0d203800220307015040c3e0300100b006103d861a40e0005000c0341d8818550641d1301c400580c082d4016540a2a00b5100183e03940e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 97317158 1250 97315908 97315949
    0x405030a050d080901090c03140f0d0c06150806041104020904020c0619020301080712030c02100c020f03060c0406050906130e1504020306090a1806060b0c1c05070210020309040501 79
    0x1001c05800488410080124800507a59010111f030303070380000f0b0f2650307452610841098104000400a106c100c0d8261002c40d582000c014000d0000f00d4021149142441c00141c64403902141d00c208071390b0980700828041d00c0700d07199105407440742d410454009408201401d01501c46000030034171080608000c1c02c1e0b0b8503041c0380d950b040540d100c0d100303092107004000402203030743d0008224003900c080750b151f0001d400c0c89140076035141c8001c3c0760081d00003404040745100180c000114046084c000c2e5592020720b0030340810507849410444056982c048103010611003a403044001c0c000810002e010940380441800349860260101d0340904141c1c1e5803030040100c1166034400340d09080c88141c0c1c00707500f1820b1400015a00d014010003155140d80c2c1c801c182091503071203950840c0c4250b0450ba0800030544c99810b10400340d4040441741c0868414103041c1e09102020070a80380500c03015a86190503c01c4c654204150603080c2d010100c21032009105080751a9203070321409000b8070194039411071240d582c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 97318408 1250 97317158 97317167
    0x7060909110702010503150a030f0510110d0e0c04090501020c07060e010504050609180a020315030604020d0b060613081608010b010f120f02030f0402013903050405030a050d 76
    0x582103000030a0500d424007626581038425034010581c2405c1403901c950312100201e1101e10300030759499018140100020031310500b0700400061601801c01d8548030410805014196010b480c1c2040b2070240070400c100702085290f0041304000b01480a494401d90b00304006019240403500079100c0740d50000f810740c940da004110103001403085090002c221005ca20020f03000b40138a21690707000c0c010004606500d0341c2d5088002c24080b03041420054079050849010700290000c0396420300c01d8542804000c0d19180c0001e845108a0b8002c140c20b0082d091540d40400f0f030701000e805150010b00c18450031903110902c1e5405000b520001c0010441000d144c01200740b014100d070b10042c510b92401402640a907801b04400082c4510b40c1000e20403944280003c000400d888600207800501c0441440030a1a140015074040d038001d1b601c01d00c00008500104203c12600112414081100e41402481109002d041040c0f04d01a003440c0e4101507645000c2414803004400c200c6045c0c020740c20038400607410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 97319658 1250 97318408 97318427
    0x321003051606030b09190203070306080f060105150702030a06020c0102070f03031401050901150e12011503060b04020a0206070c02010c0b09060619080a140c04090f0507050409080f1e0301080706 85
    0x483d208245030401101c04118041b41240080d00180c002000428040c025003280b07004007081412150101e010341070091701d8510a004842c801d0031440d400210191401082d100314680080c080e00c0b21001c29900c18009610070003110106540038800c00c8041092641c3c0040d243e8082e80b008140382100c1e084c61421342805800880c070881c0030303c005018040c65074821010000c518100300054070030b243c0000340301d03c0d243c00320000150309046928150313201400c1c1410440b4455034003804a607403a40e0801c0300343c0c0103803131841e00103a0000c40095001c5201d0180e4074506401070410405900c56920b500700940800c480d0714005901c204140300c82400e00007003030418841039008192021f07042c10740d010b844400d2080060700106803652071441186050100310f040410080c0b041040b16040c0c03800c080e039484009019039103401343d003500007014141070007500c4c04540c2c04801240781003100c41c4e5905554200b441013024410b86a04951488041c0038000c5028012000c0103003081440c0420090100c0c9a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 97320908 1250 97319658 97319681
    0x30703051e040f0c09020c010f0506310b0303040b041401090f1502010e0102030a0b030d0201140c030c1308010e0d14040603091a10030632100305160603 67
    0x72100c8454070031801445410036031014a151010443e07003092a0141190380001d4a424070005041c500300d2015802031400100c443d9090245030748020820410034286200518080e21003240c4054000e2140c40081c108102c0c40c500007080e00402010900d0341d002908000a500c00c005000e01216a01c811240700441017483c0003480a03041604042ea6564070788121090902d000702d00c820300c0740c000e4101034001c44009008540b81c0c80c1c0307117049201034108040c20038006e005d841c0070240ca0701e2043c003031408403100e40784003480e481d1240028500180c1c8002c1540401c010240800006060302e40d0748034000b000c2d102c0000c2034078000316010609052000c42240c2c14031910a0303072544070f00d5a40b0305540803159203080002d040c0180b410f00940c80044020010b118904107420400c6c0d03c0e40e0365882e4000c1d240540010230140300222001184400291013507042503110f18454800316030100c076500d0340701c43c089905030100d0780d0380c5c0d03186842c3c400400714004202c034040c2010b1214507410302c6407130010310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 97322158 1250 97320908 97320931
    0x1e06010e191406010e06070c0510050c1c080601021b01050d020c010203070804020a290706090c0b0c010501140915040e030a05120f0c191b0803040309141513091103070305 75
    0x7d0b880c1d69041440480c0341b0a640c06104151941192180240300b03540603085030303009890004072040591200c2d03c19462012012801c0726011488070351001410702c0d40c448241489001c09140540190f07895008101c441440c280c0070060000b400c8000e001070b41c0100f180b0707180c0f40300718107051040140350450f580151720f941020304004250310051101401a40310a145060f41c0d4042030309112015081300070002d01049a4003100103100a0504010040066480000c20050342c95082d080041090313645d0155000d28048007042d80c03202400901806100014030014404041a15190458024161500104201007500d00c07070f02c5c214010095110710b17500845542407810050007032103070080380213000c045042440a544000d010b05010700011128035035042e6107140b1443d15945c5648100e034110006910060001100c4551440c50040c2070f00007001099006554540c4184940213440d5032201440000f1001452a06500c9081e4019076106001956850812805815943c002e0944100311 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 97323408 1250 97322158 97322167
    0x2f040b12100b060c0d0906030e0c0120010e120a090b0304050d0804080706060909050c0904020f010507060605060408030406020d0206150f01051b0106081e06010e191406010e06 77
    0x240c40424004401d030203030000002c0060026000c1889402034075240c4041d4800d40303e000050941081c4042d0495400e55824060b20540d23400184e220302c084c216590126070030035603110141c00704c0c2001254030550900002030602e09008094609810904c02200f0084001110780d00c0382ea002c00400054031002d80d6030740c03560400d0769406079515110b03400a010050f1130400300b003c001007081120640364100744140a4503899994420080480c3d2000702d40ba4481c1100c25400b9040840c502442580c004001402c00301c2031071b0054405900c200c4080781d00e1942c0b00030114080e612100584040c00c0c3e144000c1d0349481c18020302a05d007205c001c01c20385c1550700135420000c04d60701003010024400740a440d801c00b00c050820060341c06001e28803442e1900103601d148807080321780551000c030841d07513988116407100b00611085c0c104060080940c121a420007030051000ca003515110310b030895000003101040807401d4070040b00715090309502d0f00d001034000090001c65a030182c1c04500e0507074101c07411481d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 97324658 1250 97323408 97323439
    0x70501080412081812090406050405060d02060306060403020406141212030114010c06020a180609030203060f071103070c0f09062621070b010608070512042f040b 71
    0x501103404002020003240f0000035a03034041d490b40e0000c6860701603007200d180242c011084806500102900380c00356261140000d80c502e02802158011003020b40380341d2001001e41c080c040301c0d50006002981001d0b0820001006890b04d1240c14010038400c801d502c074031040c0c2d40401408415030800d114040e4081d10b203204d000807806048038115400a201c0c444655151030050300c0c901c91515015024901c041506242c1c107400026200c20840e00c00307545186c803515004183e50043c01404060342503480306e4005070100f0100b400300390b000501410808a41d134000c0344294a5984410411540d030b541c086002c002021005100a001d4411f04205206250a241103202080d60401a00760600c178202843c1c424042d041c803241d08142c10142040000104c0c071483c0108036400401c0c1140c1c0740c237240000145d0b96101d104c000b07000ea081503841503e0716050a44036403e0010142058441c20320038180001c032030070a0240a0f4154042c050b00d400b04118090030030048403003030510140566511070038a0300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 97325908 1250 97324658 97324673
    0xd0e07030b010b0325020102030402010e010504231201050103080a02070509060d030c110303030c1c0504020609060304050c090412031503050d1b051e1605030606090601030b0a060f020705010804 85
    0x55840c100c42c3d05490750b40f4800c3c50f1685503028141c4045036044e08400040c070580c10b400a5110b18000e0301c9040e100f1001c00011103841c0f1031751280050347c0000215020803200d440302001d5401d04024003c0020481a48500f400c54070207134030442c0c90b0303640054080081c0e50140281001081c0440340039070240340ca000800c0168041c898002c0801c0440e003824020000d000d1596210b5140143c112600c0380740144005541d0b904c0301c00319420423240c070020f00768503100a000740c0c0c0c45658007410701070501d501c1c5428042c05401c041d000311124052000400115242e4622040c45180520781075120044074cc1350180c103c460801d0021519041d50b10700340049413000400c1c40d08000d0b50300c0c0260204003461000c0312401d500510062850042c01c0c101c001d030401540c078801d0045940305c203031160020310070b00307032031540186100301c44d0150443c100180503071529001c02c0d40e110b40f040c1804103500014400040168140f60402800b18240404030000d00f03904016201c0948801c2c01d11001ca42030517103444c407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 97327158 1250 97325908 97325911
    0xc0a020601090f1b1110051003060903021c0801180902150c1906050f0622090f140601080106091e0c0c020307090b03010510060f030506061309020d0e07030b 69
    0x1800c588074608950303858504c2c0d120510400414158007400c0c252000c0c01803074000340c40480d1426104050140310044014030030980503007885582030811501d1a5590800380c042c070f0405400b980940c0300b00000d915617015010001c0e65003960b48400c598181a0840385c0718498101c998021441c1140550040e110900310546581da07000070144c0711600718801601e0100000040c8071007114840200e810031201d900298000e905403a07640505555880c144084603003811078000034484190b03012155509a40d002aa130640038001d031154605190700d5aa0700c00800411008969118800401000000780f0800029203e508400d020b51181c8445801003072820301200c40190780d5610701c2c000706a0146000c0080ca6901030f054440c103954a101e0000244100c01c1054042e5081c8800140c6800900180714240c41740b41c0c45042c01c3c48803d500403001818000c0c00560070010030030848503103181d00417002006240440e00542e07a05a0710241c42c050f10509441c01c24654000c00051001a0150303207901d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 97328408 1250 97327158 97327169
    0x325030501050d0b1f0303020615010333170f060105010905130209040e01151a03161805041803140c061b0d1b020c031203060607080403020301230c0a020601 69
    0x2a1404d44841144200c1100c5080d02c5c0d460f543d0148200004240c1c012a906104d107203120040c0d502c0501010055056030701001019001e202000e07200b00f252088900d110b0000b42d9402d408200751500c9039841801c7d07a0641e1004041d0f1380c001200749000c298100b0001f030242ca001e18141d07580c01d280101060005064110101d40782e500402d080c9459120b580c40b185600005000034001900c00704409049801c450141c18003840205840c40400d2031080110b80c01381f90b10b01043c104800c3c4c850700445091844a44105003034101e440300250b1650395008525041450302407009849086142c003078049120500d4080e1280b400b4403c0c0503114001154441d4044901401070348500c000b04800f00305845200912a10b00d4642200c1d44554103904030002c00020f00c6030200c4004221030405c055423100ca408403806030710420000280f1070305000c0043e000840c81780c2007141c2000e07103a81c002805c1d80c1c3c2e844010680f003014411100712034000520855001141d007201c00b440c0c800700e0f0b90002d4860005000c3ca = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 97329658 1250 97328408 97328423
    0x618020702060d050a0207140a0f0f1a0103030807030c020a020310020a090b04090b011d0901031b0e010e0f060109140411090d05010b120d081602120325030501050d 72
    0x1500654482d40102ca5040340b5448003003010303180c050760101c001e42040000b0b0703d00041503c030700c0343c044030000780050505421007421201c0c0c60060f500e480d0210270322041200c48025042e03020000310815407110b07018500c00d0b21100ca952a200310300030100d035170040300d00d02158481d1510030056240030429180130b9240000151399140c1c000400c3e0741e0700c007040d071042115041c00200040c0d0000c0c164803850400b0000d83c1e8040581616140c2402400c60b0810300300d500146103001000014810040445064411404500c40c10703501c0505490b42c05099110340500d07502c550070000e02a0201d0101580b28809080180744be42c1005c5442d64444a00324010b4011950b03a0000302102034814291812250010443d003410f801e030389411406844082ca000d4010242d10b01100e030741d0300d00441c80d11005040399070355a04503520303083c5449030014800700200c00e501404071aa0001c0c400342c00110b1042c0324000341d400504000c2c8942002c400316950308002014504001400603969001d020480725400a40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 97330908 1250 97329658 97329667
    0xf04050705090406020405010e180a09050f030703110105060102030708040b0a03020f1b070f0506090d06140103050a0506091b0609010e130b1503040308040b0a0906090305071203061802 81
    0x60661a0603269042503070310a42c207200300001c03c00250002c00c20303036600b84e8543c01d407803041c80e050160031000030710420320080c0580002180521079901030114640076004032200e0110740043ca904582c44824258002041a418040740f0798003406100d4000c2403e20042d07150030038039200d0300c203240142d000b032281c0100c00251501e103251094040e140e20201c0700100720b64508100d1412082034251040612a90188080002c3c0c04000002c12500f100c1000e0a41d900d0702c8400c01c00c01540001800e02122019a6100b01d48908501c48050070f0280d48501d00520300c0807207900f0f1440c50100024003034103c590003c4001c46c2d1044080d241b0043c1c100e0251283d644415079600140c50380000c942440341c00003082080008248096002415004c1081e50071040d903148040c0c00e1080d6210844001c0d0108a803400440c00241e00203103503560204010f580002c6401455450b034003a151280810b0740040c002290890500042080202660240382001c2114070b15100700d540402d2620035a8513041603000c0b9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 97332158 1250 97330908 97330913
    0x2030702010f0c02090109020a030c0e010e04020901030603140106081b18041511041a070f03180e0f01210b16030608030c01020a020d02030a12090f050a0f03030b04140f04 75
    0xf038021850741d500401d07000b419a12210760707000940044000038000f90500302c4d40f03510603018014104200c20180d40d1200e5000c04101844041c0d80310100c114101a5a0340b000400310701040d13850704c1d41364000000407030b140c1d10b003880003413422499017030b00243c801030786100729243d90381c002100c40f501d44c407919484429581e03401c011a505076480715584500d82090000303d4030b812140014815210185e0076070345c1c0d4410050b81240ca81c010228000c0c440c2250a0780c0300042402400c94070414111031500b08001c031340305c444c1e00c0c1c0c00b0441511291210365420005100c20b421607050b10210020b603150301c20004102e6125510300039405400340c0000382c18a2006045a4805e40041d000760800404483c6e0360305c1c040f05c51070b000358052a0b0010041c0250380d1204200c0d440070044034100d1180c0d5842400e0701c10442040d1000780701103170b011502c003200010308100043d81402141110f0380140700b504e0300d419031820007401f500c0c0b002d9052440b99203490780c0850640c4120a80c02c2e0010505040d8100740e954a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 97333408 1250 97332158 97332167
    0x8010c080c030f0123040905010b0a150507140c1302030403030c0804052109041505031905030307030b03100e010c2a031b0203060c040807090203010b0a050a020129031204030302030702010f 83
    0x17840e040b90805c0c203090507503050200542007004a4481a07503c0b41500c1e5a4015220034051191100800140d081101a000c500040920807518846100b80c03891110700700d00141d03848109046440c01e0716008000c02c0305164061203205191880c40c280651103282c1582c4582d11000e000f80001ca29120a25281841c5000401a02c014040250003048010f081225000016046202e00c504c24860030100001812034200d204c130384240c2c010010740c15515a020240c01404130820095010300c00d02562aa1a800c030b40502081c00300d0f034400000720046401002011100100c0024020080b0224080f80c006c032600c00311202650540b80820340300392445400d0385e12178400030020350b0602c0781505001750404908000c00480390759008483d0001c0d0760b20a403106074002445001c0003c0420311094074110300850081540350528800020b00c160880f280700c408840348400a01c2c00c041d481000003403414100001c08403030a0a40000d0f05080c41c55400941c4c903c2800d50083c100078000b081101c01d18080c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 97334658 1250 97333408 97333469
    0x90a060c170d02120603160e1308031620060a09020f0a0306060611160b0903011b030b01090f03020d020d0212030c0c0f0f010e0909150108010c080c030f01 68
    0x31419618000b03070b112400030b50030001d40c2628640300c14000ca183c2e40b40004106003000e413500e003400001d61070010111201c0740b001300b0200d41510f071070354420001a4200300451003240d0310b001003c081600e030704000345810649402030a040c8000c40c0925428030700010400d0b0301040408012980300e50b00d101103410f81d031100030b042e500075103100408810440642c210700d040e500b240c1e950100e44aa04004580c1d1510214400490300300c00000621420442c0c4009005403070025001007010b00035070200808e0544640003032b0000a0742c0d28148502907a02c086040010070900340060406411600094401024080300030312500720040c81d031045454030000c0c5181442041c0c1581d407911400f4140c90707160707102c0221a51140251b05501003241c40c20810b401e09040c4180d50b41d00c9018454024890b010002409051051241c4280328030b03c004104d525a000e09038150002c140380003005005809510040d2181c00700e46024070402100030300f03000c500e07070449070304011103d0402e00c802d0b5540d1003203c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 97335908 1250 97334658 97334693
    0x1050910090b0102010e100b0420040b2505010c02060a020a05090402160b090303070332040c05030f03040905150d030507020a0b0d020702090603010516030b0a050306011205070803090a060c 83
    0x141f0500480203025030b40c004140c0c00000d440c00d010b0305000080c240200c140142100d074041c0420710003408080340309800340502400a18540941440c40214007c00c11040d2a0807900c03a91606100003d43e54140a91034105980100940c01d000c00004013074850f0264120660149070701150003401c04904034003202200b900108910224103080801075100d0340100c030000301003030424150f86100c41f0344280c06216900c031445075500b0400e00002c50b180004000d44203441c55560240c022801d03950a0040001c8206200000d40c0d695203482045005d80d600101255260900c015a503030640c0c0b00c2c20040300c00103501d490074a640b1a41440003801e90242a08900d40180010a003810103408071b50041a1507402282d1004140d51408105426248c3c1290000158008c4004041e06603000e6041041180030080006040303a03182e00200c0c0c50140240d100354200c0c03e0688486040c890b0a016031720217000c805001c0c40c9020107180100d44480b000c0d00c5290204060403c20205101620000c88000c88 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 97337158 1250 97335908 97335913
    0x2030309102403050717030702100c020a32030105040f020108040f12080108010f090c1814040302011b0e060405100302221805220c0911040e01050910090b0102010e 72
    0x540f2424095591941c60041c0745844d20b202e0036a000000d400015240310540c000c044132007030304a120049070120204d01d01241c02071680103000c03603816600e40450304841072041075490320a921003240c900c0b0200c80225580a03074545010700001c50600c7e12042001502805c0903169a01c45150400305480d85120160845003a02c124003a16a4445000c078100d5082c1002446002841210f8030101c40006200a000d0300d19000101303d480d105e14030302c50040b40c0182d000602c40c4403489020707000b07950840b02100140d544658024020741c0a911400c0108030615040094020302000302e01c561056008081c03040711510200304045109070105c03a011982c115000810f200d601c03000c00e080c00400c0c06001c258000c0d5506e0208881c03158400d051080c02c081d400ca58110003e9600d42e14402200041030742c01c101d045002240308599405900b00a038603546401d90750b0342c40c1886100e812101078000d80c1c4503404e01c80900941580080491060312504840003c24507094030040c1d00419801010300b0450 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 97338408 1250 97337158 97337231
    0x90f0602031f061d0111010b060f0d061208030606030a0209210105070509090c070c0503070611070504090b0f09010e0a150606050a0207091109060313120203030910 72
    0x40980c001d10000410900b0455802a070300d0b620252907808149410811000b0b490080004940c426801440c03080e91100000580444140c080744c80e44c1d02c982960302600c54005841c552542d0720b031040300010710011410450350140c99640000520000d00b00c60b204210104c0450325283c0c0c1503040354142d00d0000c122b10310900b016410944501c070310942448465103080c000403003681c000c0c0101c8001d944d005101440654694001701000d41204000340c407028031552011400e510104114000350103107880d00c90a803100c0034440c03882d240305500114042c1b82060045d0000811403150280c1101c805400a07155640e030801d0103005180101110801d441703216880001c1c000000481050807862000501080d0348409050ba201d01c17801800b500181d1055008100144175076020950940071120309a04d0300f11080001901904266075600c1002d00c0450020204500924a040c101d4103600182d401c51604c0b420a58a603d880d4100040305600c1d00c0822000c00d003013030300800ca15486d19422880e407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 97339658 1250 97338408 97338421
    0x915150e0910060e0105070609081b0111070b06060702120d0509120714060d0209030706090512070b042903070504031a09060703020c010e01061e120503040603090f060203 75
    0x20141900d40c6500076807860002c20b03082800c00140809a0740300b83c598100320a040f60044400e40d100c010706440d0340e40d41e19402d0000804840051000e8980952020074205101032540d086038241403000790f02000821074100011400d001c03041e07000c0411100307aa01c0b250180003203800c1c04c0708014065110b006025041c41d07580c1c0c00001801d01600c0c00d441c102c00411784c00344c9041d5030b12410700944810252410150005140140c02400b0a800e42d0b00050b0500407060302207458890140c0000c0f0100311280008d0016003030250403490303012f000f44014407170145020400042c900c03030790080e80100200304420515803218442c594000c0c85518201036641d141404d80104075800c140011954090b88040002c10b51065404042c01107143c030026000c075417981e420540080d4481c113001080395407240e03c1c0100944007841920004c010904442c0c00d5021040246000c3e803050b600a104184082710b00140403410000a41e02035030400d040010780c600310b9080500d00d071502c01e0001016240000200040e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 97340908 1250 97339658 97339667
    0x6030203010914061c1509080703030509031608090f15190c03020c010810030b07110609030a02030421081c1112070f09090603030201150609050109091515 68
    0x100c80b21000c1c100200380b180c90311100c280070281e07070040e8400010805400c04c2c21078602034501161140c0200611030008080700810303581d8044054031040004200e078000d00d038140c011a60702038100340256103800c0d90401045d103007130300300383c405030003964007288202d09916a11314624901000424010003c82c0f11404580b66500002c840701000302c41d001c9194043d805104240d8074240c1c160040c007551002c010045585c42c0b0010f04015180c1d400d1031000002c1440c952101380241e4240d0b981e1107034001a4901d091910744054000e0480f54400c010030301e0041d6000c010b0790180e445c00c0101140c2c203001d40c40c180c200b05c1390b0600058048540010754281186a80740d50301d440130030f07450091240c80c480000d440e401d0701550804184c0c0400750070000d400c051103942c01c0f035241003050408031007460f111542c2004644150b0011405030707640e40712110a00500d0486000100103519252449a0615000800c5808a403180492007521094070300c0c1a20200d5000c01c0c040c20307030410400068a2044002403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 97342158 1250 97340908 97340911
    0x20d08040c08011103270303130804090507050c16120609150e030c060f10090e07150906020105060316170a050a0605010303030f110405010c080c03191404030c0e04030201020903060106030203 84
    0x640a0384c000850061b416142803a840941c101030045c1d4119918908010100c0c10420320071200c000c410000031030b4644180c4a030501070780d1555103203038490300704d404018903007000c0c0c201c22941500084400c001c00310b40350520607465640b2907008107071803100385014044004910310380031139503080c0320348025801000000762402c2c0820b201110354079242d03c40c40e10084081036481c0b800d45550880700317201c801d03115000411800d044008450007a40d5594990920800700c8864800098000c4e400700142c6c6d909000341a0002c800b1005003c124000d11300d2508001100d01c02d000c0c003a0543d0a900d000810300b408140701b890f40150a444049526281580c0240000d000031030110b0b01d8042071000340c88480c442c0700b02c04507890021600e07050612005440c0e0700b04801c01140d03034100030440b1081a0303400b03001800303201345c82d9500c5008007014000040c10340740b01e41000d2154500d050204101040000010f0421030b030082c1d40307000301c54a550a0803030180c411101000e0305841031100000f0301a5040d4000c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 97343408 1250 97342158 97342171
    0x20d061212090911160503072f0406120b2a030106120902030d110a02060708030402030f0d0203030105101202070b19021804050a02041205070e0f0106020d08040c08011103 75
    0x41c880e83c60b0382402045540c0860380102011050001c040d6a41501e0200c80641e405101104d0804030a03a46801840b48407400c0d820001500310000c0c0116101120b41d5030354080115001d010150401c913500080703141c421f80181a090348480850380c010400c4040d544200c000220200c41841e028a004c0021f41c402c1c818440040c203031000181c020951440f91554160340100541600e0208c0c54007140c1c2010801c65001d0140280c004190060741da01d002411440e1241d503402da2640740500405040c548000c040c200d003074100100310b000d19680403044a0542d0700840d08000480d640072001c4504901341c0c6208000d8a100180711410320440c051003602c0395040003200d0042c180601c2010702a8000c40450600c2543c06090007622032405800c2075900c040481c0c030040c2040e42c4c54800c0071150b5000142507a2907002284248603d40c50301c841c036607200981c611501e607a54900000256a002c0c0d0f802010204176007800424208030120b0030344030080281400078840121003c84d892410303401aa0035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 97344658 1250 97343408 97343417
    0x4080f0301141f020c1e030d0201140105010e0d120c020402070303141614090f0409080a0e09102105010e0f0c030106080304060809010906020d020405040b0a0b030604020d061212 78
    0x21000312040c0e40f501040a042c069002e4030071290b4002c1803050b4591010400b060061645201080c0c0340c40801500010004030741c00495051009840c24810100680000d4100070480c9030503403103502d4280440d48440c0d0702c07140c100440034040d01c04a4009004660003135200380001417204c241540340c0c104510a445d02c0f6886031060701c40c0070409000c0c59030710034800042000204a01b18802031000505a000d0014290611001d0858000380031151034600459611201040c3c00e4040c0362711003040d5000803c00c1d5280a81401d02500506000314a0320171100062510000d0004810991013000201d42c4d1081c0248208442d81c1e266589880c010b0f040c5003050300c24030070200c0452405010f400100c6034100e01451902d810080e088a01d0782c03005003140040d64941c407402d400030315241b00914085074070031801a201e0307051008000c1030712503405400e44078080303500c02404690801d00490b80c0082c0e0450b4010307561411205086d0181c000b40e07100d0384801600c08501414000c10340020656440c69a59 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 97345908 1250 97344658 97344679
    0x803150102010507081302120a0804060f0e01050717070204050a06090f02072001170c0a08010605070506070503150d06061a030f0c07030c080a090302040b12060402060304080f030114 80
    0x124200e60b4112070b01d80005c2d401d1000319101c05680083c0c00c25060001d4070705881740c0f086d4280c01d4a4004808011148a040001c2c00c100450748003c03462410b020525206c0406510040003d10b9806802c2c1c000d000c0c500c0442c045c1c403188440c0350484003507950182051004c0d02d0300040c1c03480104058030500b4856030a11400c400c0010740c40c0700705d41006030702440700301d0030030f2945400e007940080c1030128034140308042010b8036070100c40d2081180324000c030705605503842c1d24141c0700401440040c0d001d0300500009102c02c800080c1c01041141d03001c4c0e00c5140141d01c0399160352500b1503517860400c90759000018100f82500307100f0140c004000303691071441e000d43c1c0002c8070044803006100031203030410620280f03000305005903d400c0040c41024000d02c0d011148440c15150301410fa0322480340d503000b044111000b00218200b9005080454504032074040d4400130b42c2031025100c8000410080c8101000030001d03042103010400d80e00030004400e6816140d42c1c4a0880408000c04c501e0441c0c40b90f460240c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 97347158 1250 97345908 97345951
    0xf1009091511130b030a020403170702101b060b01020c060403030201090614060310020706021207170711030418060f030f0312021303080310090509030d0e01060605090d080c0106030803 81
    0x1411200c52110f240306144105180c14080511a00082c0114044580070000000840d100005c20911082202805540c42c40548100500a041c0c1d034040800c0c407101e6007080307801d51407210b100c01129800900c0031804100e00c10040b428803005800d1160304c5400410040306240c0c2c1544041c5c02c0d9071080310100070350131701c1d0142c4103050134080703408603410b030303c0702c201c07280021800d8020700300c0c451084a003d4240351404d03180b501c1c0d280d01100d0400c0010544021099410f6114450b80c1e0040b101f41891790003c85035601841d142d03c5079019462098461803215010841c1c0b43e07200d403005181000c50000c09948a00d8800008410304100b0350015040b401720821804d1640f00726460b10003c82250710840e880c55803003200c2900001c0946042032440d503000100c50140c1e01a91b8070400f011000f5658484010030001e0456800303a040c150075a00d8a1400e2000742d401200b240d141d40c904550707010b0030000c64540402c0c40d101c1e0b100d601c4450350030050004204100d44018500980e9115078040c60102d000d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 97348408 1250 97347158 97347191
    0x609140306040c031b09021209010b010f0917030418020c0601080c0a0608060103020909040b01080f03090a0e04021f0305040c060c03021b18040803041202150f10090915 74
    0xb030320054581c0b4140f00003000004d00005a8481c481920101c0b0101256034503000c4040b038101120944405241c0f00801021510078821030000709424204100c0c40303404418000c2c11100d041c015510000000554220f002d8000c00564008007001040090030720100d010b40703000394000c201e0b50704951203148000f094003400401e90034400d28010702800340f41840c094040314003c0d4090a180d041c1a400c010554590703c5484846103e02d02507620f880c21549404411868042c0b0301041e20271a40060100c14295520300420740700f10b50029812510544540c00010341c0c1200260401405141d0190200c2d25180c140e080710b403045018060b890f040e01c0c0c0d00d210580e42c140704000c0080044e04102010004892220710020ba10700e40a0050404400e10f00803107180c500050f40d0989907148003000704006c00184507a416400b100b5440038160008240c2c0c190407001c0000707424070700e052403d1400038034052000768070b101c000c0000c088c00b401541d4880c14055142101900c00c10700183c02c0450322903002c0241c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 97349658 1250 97348408 97348411
    0xf0b1e09011505122a100207061202160b0a0e0303010306091b0303051c020405180a06050301060506031303020c210f0105060d17070204020f1c2007050a08040609140306 74
    0x1c210140281c45845e14031103540d210701005a05101c50751041c040f0140d11902483d07460300380c254006064150400201030a9481c10305032010a0a004010700344203510782900600d0101d51180000c4e01e680c03180301d03110018120f0350604444070b10000c000001440b01d42d401002005004c0d0600b16002481c8140001000040380400f4010601c2040071080e0b00c4910082040e80100c054001402c1c2500e0b9000034650704a0405400c03110b84041083c4512100c403481030340000d0101700c00812180c0d03d8000891a140002000010300c40c0b61b46900d0010f26000b40406046203400820b0030308805040d03041aa0030410324620404140704860440c60f40075414442d45010303610051040b407070b240f030a54680010b102d02041d5009503803810700c400c0c00143c54034006844898020b1600c00c0e1038034150017000b44007038000480180c0c103a0502d11148080d84100c05c0c1c58022040e0460300c1603070b80c400307030500520b4808205002050560001000a15030354000d03c5042a551021040b02d014288041010b030394050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 97350908 1250 97349658 97349689
    0x2010804030806031204061d0409050601051003020408010c0507110108070206060f1f020f1b090105010309020414041103010e01110f13080714090c03040f0b1e09011505 74
    0x469401040109001d01c0300554000d00080494903802240808030b0b03115001688100c010900c0c1ca001c80c00850307807140c2115003a03d002c2e1000c0000b90181c3d11001d55650047c400c25009a440005000b0801d100743c0458020740030420080c0084030300120001e02680c48000f0035a452421040310480941c440c14100f030107120154001c00b1603480340020803004e001c011901551000f0480c0c0011000702c0c0c100d118107008005500a81110041c003244941040040720003001d640c0ca01e2403200000780c1c4e450340c500307054490a10f07002880c55034901c0410010150300c603601e841c640251042004100407058030714161030042e00280b26800711040d01a080c1e44084c81c1c0b02404200500c404c12048601c10054450f0505848861400981e511400b6060090542054810407d588126080b13030804007103042c1c001c0184c7c48a40d1a510300f0340c8071802d882c0d10301c2c800200480385601c0401c09400002d00c031000304105401b55411642449402c10b0700070141d12594403040354120700700142c185080034950314040c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 97352158 1250 97350908 97350917
    0x60708161106090904060209031e0106030b16020601090b060f07300905120120091503090607110f0d0503011d010501080c0c01060f060f090e01060e0405040203071a031e040201 77
    0x45546d81c2d4500070b900500e0200d60580b00300c3c181c21040011180071104064480000058001d096080c228110000200130401e40d101c4004490306540e80002c80c10b044800e032680000307035500c5c9400080d0780c81c41200d070b030200c05200105584c0c0920a0b0000010844140200c2c0781c44d014089594401c80220702a00c0030000c9203000204000381c0c18a00040031890f100e100000540d03100082c1401030208000b0741d0030248410115000d4182d0914411440c01201c04015050a51400a403071079030300c200c0144180204550020350215441042284601c400e0060003640c0748060000b0004000360070074400d00345040910180d0b4111012400c0b4554141e0384103949441d02da646000c0d40300450344c01101c01510641d41c0e800e002500ca28000300201c00b4006990b51807205407101400182080842c4c0c03c4010801640300040041d240c01104001000c8020380c0c010641d592103000003402c0c41401d0f400785800d0045402c543c100c000c0d031000210b20945141a0b880b0928260072103215440700d003201d0003070218 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 97353408 1250 97352158 97352161
    0x1021902090402060d05040302030307030b0109031101052217011d03031305070824070201050f06120c04020c0708100920031c09170c0d0308060607081611060909 71
    0x6041c0741d4880703a030050010702010315119201c08600f013220310448007540180c03c0030050121081e4140640c400520b82403a00b141e0782415a03c4501e201201140e5250602c80000b51100701c11042d00300c0c5503440c0905201e10184559644c980381108c1d685806440c085510741040011800307219012a1001070264004500b1550ba86600740380c0c1e42210703030f03041e5851b21503c41d00096040e806c204071111800b191a503104400c0b4220300c01584498064580400c0da4107101c200420300300075580d40340d40490101d50141c0c03a01101c002c9142044603001000350414000511150110030010f1804102c03180c00d0101d8101c90703c80c448150882d140c0240c018024445404014080c1d1940c0004071a50000141030b00c0c1c800c410f030301082140c001182c8481c0302003130459000b0054801c080380417000c405040c00c080e05e40728401000040e0201c0782460010306100d1000e000c01c0c0d150b1680c03070603910000c3e0722060741a0707503c4800391070042080c0c030003000f01c0d04016506081d90030343c2040420758009000282120115 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 97354658 1250 97353408 97353413
    0x1170a230f1203180712030302042309150a09091a010b0c030415030204090f0b090601020c0f040e070e09010f0b01050910030c030f0f020c070e04020907081005090420010219 76
    0x5003801068001c44c1c40c407030358401081d00303005500700314451403083e180180c0d0b49117000b540b4000303861580502c0211844d0103a0b4445c2e0380c1c82c1c0d40c1c00d0b20750111707003000a0385518030030000188040115400510001c1d150816001c2086a40100b140450100008210050782e840c1c6c2c070070070360b8030810b050300c00240c20500007041868400440480c40c3d407802d00340507050940790320b540c0044404010302211401d4840440b800325090002410350441c40030310183c40005021001310f82c4060460026a008940d0740c150350451541c14016030380174041405841829081c038034010385c0a40008a4400c600f90b10700411118070350b0050007115010000500600803003002e1070810340007010032601a80615031103403164a04d00910b44180090414140e0005845101010301285803086d95007201030100d059a0134000540c0c2c8031405254019090f14009400c0da859074159440364615610554000520400b40700c2005040104481e40400c50b0700b464030140206001280d40c3c801a0003070b044000c58060310b1a01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 97355908 1250 97354658 97354681
    0xa0b131a0709030b0a0f06060503010503190c0806040f0c0603050601080402101416030305091209090a0b130f05060d0b0a0f1803030b0a0b030f01170a230f1203 70
    0x7030180d003500b40084540ea49071190415480c0488201c02c0c2c0e16607400c3e00c03502c1c910b1030b4407404020b0211454a1411503041002103031351090f2011388130ba802050130b4810410041040d8900003e0601001074440c1802c044c5842d204286401d03804841d5420b4031080412101c1c031903c10140b041e03405075102c00941d10385400380050040030304c000a00f00074103a40c103408124084001400581141407290400c01c649041c000c1c21a00084d020000580000b030f103e60b898030340c000603190041c034100d405050310740b05d620301e460082c2140c84084c4d40051040c505000c6114681e4820384401421071814402035032820300b040356240c00e081009081d401204082924404141d00c00303114261840c4000030401c0080071a202c50441c90a0708400003512a045070482e410445070b000020b1000e06019411420004004007011005008036451000e406002d0300040504000e50300c4d07000d0300814144100b01d00050804086115074891030440d11404560381081c06c1d00117904041d8a80540c0601e0440d2034444160701c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 97357158 1250 97355908 97355911
    0x1090209010303050a02210a0306081501050402090604030b0708191b05130308040e040c0b16020105030a02071e020a1a0711060912061906080d0c0212030c0a0b131a 72
    0x100314441e0308810740700981c03802000c7c11a250050f4010791160050300d030007025030381290841d2585410611071580001c5104030458195230084601684614035003000c986a80a16440944102002018007502e184c00400041c02024400761b407001d8101c111607013074240c410410754200500016080d032a005c0f44100050140c0b41c4100c0000c0d221241e5030f440741c0000d50803e800140c00b0f071200e074080c002080017402c16203005210000b10300b41804c100c0d01d400c45c10203130018030190501000000043c1e1459456040303035a1250300000c15609070003007500d514880619203204a0040451301c50105100305842048422045a07841c07092420080c0c8c2d50b010442e4912140194020505101d101d0844da146c001700111031034400001c00d05442c11091070313500c0c460b00607058014180740c1b46040c0b01152010842c8035007c100390070311042a1545c5d10100d09510958400b0917064040400c44402c03000000c80c204001134060045c2a03e5500d512000082d507280800e00104100d1040d082c0d00f88440041041c1ca = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 97358408 1250 97357158 97357177
    0x304080a032a02060609090a030f0507051f0b090604060f1a07060c020307030f0504030b010306021c11090a0e010b0702090901110301061115012102030f0102040e0601110109020901030305 82
    0x1c0c0d1640c041c1c0e071400c0c0320507404403502d80d015801a00c00c106150510906c01580280510000e20400e00c032a20042e010011a00301e070800c0080000300281804410003108105148400074210601a1460040020003d90100c1d610a1030b2440228180d840c00307000d514103850200041843d843e2406138514060b03c616001c5c41040c02c010320262003c50413034403c154041806401440d40d07200f41e840c00500010f00d201428050020520040c00481c40c18039015065a40c080c800690f50b00301070000d07a07200a07504603000c2d02da9041503507070001886107030040c01c040002598081d06050320358011450306070b4240a51a10f90605002c44805072070480100380d044040e4000000d500e1030281d01038100744d0f109030021404900c101e05140030750b18080011020b05c160b94003020000b07504103400141e01100b61203408510000d18103416003507541c00e0000402940c0c0c0c080c006c66949a48411524401c041225814081034a07400320b201c50402c103004a808895000b044440e140e800c0d40d40072741d907030340225601 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 97359658 1250 97358408 97358441
    0xf19050903091003060302270c041a071e05030a020705060918100f030c060e0f0306060f0a0801090b07020c0d03020a0b3105011a0a140111300304080a03 67
    0x5a01c3d2403000008c946040801c0c02d4141d269003a5400c82e240028090540d81c2c20100420003449400038200d03003003814508075507596981203061041000309048484803603900d880d56a01c00f00f10780040202000340c4a90243c80017299101e08000d80c90140c0d00c00e00c1d400031031161030451034140c410a403960125991003160000740e00c56030101a5002160011110302c003041c0818081e0b5508203548004000003150321151508480b80404d8a038407014000707a000300252120007000d5503440380c19002801144000f088050700f00e041ca00d800850540d481c1000d4041c44000700c2c11414442004083c0a4050300208803056a99481d4021007500030440d440c9019090042000c42d40d21402080070036018002c1802e000c6941d08000e42107034036000b00155038a04c603511207040340d11420030190840c0d800ea200a40864011801a14405c0b003418200010740182c9401044882d1682002e52029051041096030020102c55100343e80c40141d030301409041c01400403518241c401d800a202000c450500c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 97360908 1250 97359658 97359671
    0x15130b0406020d021009020105070f060b13020d060e0405120a050702040c180501050315060d0f02030f041103070605030a23090106030308060f01050a05210f19050903091003 76
    0x2414a5904241c01003001a00408080c0c0040c550400c22065449418007080010402c65400a0158032406200400104204400e04207006155009284c001d201502000404c14060000c80c0250b00040300c0c180030724501003001c60341151407540b0f00e00c50f5905c00c00030080384100340442081034020016410030040200076100044e1240c0c0124003050b035584e1603460100e02c200d01003640c0b8107107a40100d41046405d004000d485c080150000000388816284280d4070800d410b0004040c142e41940561121b0000080c08421002c04801c14411030240c0b5031598040410707410181c841225115003400110b00340049802c0e025194414104020020075480c5008101c032000300c05110211005000c9954515081040c5901320482c654403c00448940030347e001c81e14006003881c01200c0c2c98900700701001c82d16140703030b8141a010612001d45102090058504042180c1031400708488030f400306030100c1d4001501c18044e0099a000c3c0e04280b018604004030142806841d10f05004e54604141e102c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 97362158 1250 97360908 97360919
    0x82703040b030708090a1515051f12090c03020405070c021005030106020d170c0f070605040c14010309050c120114010801020a0f08090309010c06020403080a0210060f03021513 77
    0x20003040202440d088541e240e243ca404060304a00b001007804803990003d080a000180700340c0e240300c0c20861032101c00155002c07a80701605d00a0195008190003010040c58414503a07001c9482810710b801799940c001440e10800240425684000d000405403210f60700700b440140b80c6a04403980c456028a000c001400d01500041c2ca0340d01c0204005000c01d400000611850754184107541c048860f90921400c030a00319021140304420080c0860510100411145164500002254001e42d04007800b0322032803c2c9418007002442e064490346404025a203a002120750003401500c10090700304000e0429401d440b400c0c0802ca0704502e0000c0303503a5580d1080848008841d4034014041c1c020480016140c030805403002d842c7c030b045405480c05000b04c0c00700b0000c5100d0000215046e0140070300c0c01c05060b20003890300c82c0c041d018682008001060100b040040d03c1c1c0d000520a546444c4000107210a0703540e01032003132a81680e4003003c1d40190a20740d4080c1d860621a008095034101003140b0002541e684 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 97363408 1250 97362158 97362163
    0xa1a0303031f1d040221012309030a02100c110a03050918010522020d061403060a0e070911040e07020604060f0b031b030c030604030917010203070c1203060503060106090f14010827 79
    0x1940c0a03234000110700345104051520201065001d40b090740154501610300e013010356a010000d0b0900410740d11020394408543c89104140f041c034011008458032a0300c14540580303583c01c448000d42c05422003481e41e9a08082c0403141c01e0496001416480c00c00f0312540c01c1140740e018003103505929507003c00c140306400f0894420303c07000b03003100d601014400307220308105800d0010103800c80e2440303810141081e031031ba00007150400c129195480001103101e181c0d4119003007401036902110b4040c07840001c00038000d402041e138903c40c0e4030990040241009150f165801c903085580c001d5019030101807801e004603140d207400c0900c98002000c1f241112030300c05c00039141a070200c604800080d6021402c0001e0900343d2000021003801301d00940c154905540014000e100315000580031000c0c1030703060a071f070038026880344001e007401400341d8829684409004e400104580724540700ca80c0c0409001424101c55415040b03002d07816500c0e1980340d10707401d4480c1900d00055030407501e07540000703c442850803000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 97364658 1250 97363408 97363421
    0x30601020a1401090b0a020a20100518010c1e050d0e060403030b01080a05070c0f02041506091508010506040608041407080a02040606020d080a1a0303031f1d04022101 73
    0x7914004181c0000a182016180502800401b00da50050110341034440d008180d08880090182d5080d1080303410650040c506039200c0041c00c0d42c2890201400050002c010b505040000c8920091010f00701c0c082c0d08648191042c401044c0f400c80030417203d8000c501c142d0003070144040900c00030644281c0e420003281008003c0d1011004a65520540c08013560070610280d030001403104108064a0501006041d003561403800030110001108103804541d01d40c0d1040d1440c0030302c0d035408242152603007006400c40c1c1c814041d415016400c600d42800107031050009905884001c2c04544c10140b40c10020f41d1400c9018101710351500b0486148003009404010b218007e0207400001c000d039407401d00502003124020381090045400c00801c035884250002841c0341c00000141001810040514818484c0b59010051907032500002041c4500d00881040b01c0c0d0740d440803c543c0715441551110b01d00a00d08001804003221110140060054a030411b020055044440e281949155200c008103007140d4a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 97365908 1250 97364658 97364693
    0x50903071d0403090f0f0e04031407060c1107061704021c06021c02030106021b010203090a0f05040c0512040807050109020612040506181e0109080301080601061206030f0305030601020a 81
    0x41c00300400040c180d0266001d0002c00c0e98030341803640c042c244954030566a00c14000c00b0502181080400c0c1054440c40c5511403103082c40710b840e03459130450725210300034000300c44046000501802e0a46a080004200301045170f82e40d80320742103040402d4400c20348a4400030020380e4820041c9100d41c100394a000310140800388202e2005170307500c3c04030703a414214245e0303291603051080c81031005000c1c840e00080d400740c2ca9201c058080c20852a070000403483c0d0b10942e0241ea40001c4144d50010b001303600d9030310450a440c0c04680602104030703521412106806103180000f203501d242008200804ca946004004c3daa01032000440c0300d2055030042921a40050018080380782d03007204010030b115007408002e1b00900400b0005001c0d20701070610a07603a50861488040c81c0c04000005d800302c5809600c102070b0b065119140703a89a6a4031240c56454100c00d1240001089001c1c0940d03402d440ca51250a0640e94040c003046020300781c0c0d480c200e030301d600010040c0381135100341c03941440841c2e0400e40080707450b403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 97367158 1250 97365908 97365959
    0x50f2805030702060c10060602031305060d060305010c050a2613080403050613050f0601050f01050c100501090b0108070f0503010909060e0f10061e031103101104090506010509030d05090307 83
    0x12800750b03a86d00301c4034140d00c0481150400d010b48807404a1607082542111001c603203460700c03009400304210040400380d1004000b503181c0f014044032160042c0241418140c82d440b41c40300300400c4401184ca034190328ad41080c0141c58a40003407100040a0000141c1502600c2d00318181900c0c0c1d6542482d140d000d82d02140c08441c3c0e647d031030040007000c0201c007502c00d0a80c070282825500d00800f09000ca0400310301d1303e052140c0131600c100e40100401548032504800f001c00d0115582d00c86005006000e85204240000c081c0030000c6c1c20305000c5c0f030708403d2240b100e98401f0b140da8a0311603550b00903c1240c0c41102d255844401a516110003008041c000c007114402400310840e00120790402c070740c4540d22100341603c80c030b00100245128101c82c01c04894229400f00340031400c481c0000d040003c01d60203d80000e01e02544042040d100c04040d01c02e54075007080030000e64842c6001541c1038000c850555900d0f9005402400010b07115801805070074102408035a5610340740c150b15803210800b840c0048039807 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 97368408 1250 97367158 97367173
    0x1b0601080105010f1e0509060f04022d030103050607080601110105040c080d110307020d050a150902040b01030e03090d031b05010504050d0f091707030c12050f2805030702060c 77
    0xc0404220301001000c41e0b081803540440030b144040881210392140507c280c9102000600c50b459500e8642541c2100800442d55096000c030781d07014803582c50801c1d60f070f8401450140500322189808690581c0d41000c010a51130340d0f0280204c6095400409043c100114036030180b42052090040358003e41c841c00701500143d041220040c40c09600d03e5010381003002d5910300200c60f800100c01c0342c5031582c041c0c0b5440c880c40001d0412506c0c2401c02100103081c0211841019218503080e03000c405800c2c42102c0c1405821412801141640c03642007581c1c0701c5400800c03120040c0d103084200389081031300c2030501d10340e410114400b010300d11044910503100380c1d4561080004100c810f100d030b8000c0c609c003030501d00030700d00c01d8180040511075039008103a02e4450382100c120542d00100040b40045900c080e80d101c03959142c0711000c481d543c40d184111000c1c4110704a1a0780300002154120110b104901d00c4a0440c03a4408864508001074000303a6803030000f00008009070300c42d80000c110b007004260051404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 97369658 1250 97368408 97368419
    0x403080910030203130206030417040f030501060f0609050108060d020303300c0f03040303020f0a17100320011e02060601080f04030503040b0604150602160501231b060108010501 78
    0x3101e5240c4501c0301014030420401c400964044064115150180e401c543c40b5915450011082c1c01c801c1d4030051182404500020055041d41040b4140e1384681e0080c40400c4d500c00080702c5d86046030041d28041442100140000d5200300720860340070100a240c0b9411080d160042429640000c0000d001c141200d03070300800000e0640d110706a0042c4d0711140399424984490790080d140182c405d42c924034440080450207151094040ea42040d8030310181503600c0c2c05543c0090070f020504454800ca070714080740010b01064a0280e400122500705070351072036640700e82d190089448900243c0505000b9182030007c1a81410307102454050307056002006141003000000d001031500500f1403503211504010840040c1d8041c09403500564440d50780320300f644582d40002d000d81241d18102c00d04a104040c0001c40c1e55001a0701d011007070a200800108907121001103501903074180300b83c06900404000304c25928100c80040c601008100e2106010740042600079060040c2a8880041030391183d0040c000e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 97370908 1250 97369658 97369669
    0x70807030f0228170f0403260f010314030a020d050f0d05010b12060d082a060403080103030801080102070203070e0a0b060409060501020c1f0305090f0703240209060d020d060b04030809 81
    0x44c0b00c44c0080400d0603c0c240720214034041d0010b2004081108607450110305801c45071205e55074004034143c080c56890b0001c0f06a024000910090341d040f0100d4001e10f079921800303c21905000d015901400c840d58080c5015039840c1c0c002804400500000c10448103408914811036003c4c255041002d95114220791455a100d030010345541e120b05070545503040041d490b00d084550504680c003030854405580040140014641007030f0686602800c42008105940140210705a0b440ba4852500d2070f40ca8220039400c038005c94100035003550005d1800d0061000800b600d50780b00f20b1104c5d02040c0900080702103110b41d001540314401040e191072080c050340d80c041c41115402071064608120b5815048980c2400d034012a41c12814959100049900e034181840b840c507041c51074070110756400eaa00d16044070110620010f00d40e51400c54042c0190312a0a0b000701c0f21300c460000d200c0360404210302c4404e8003d41c01a110a18420342d81d1800241a45490f00904011400703800010f880701030080a001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 97372158 1250 97370908 97370927
    0xb04091a0a05060a11150112140606010c15020f0406091404020306060d02031003060c02030d060e010e16030f0c0c030206060f03060c16020a030b0603070602010203070807030f0228 79
    0x80c85030720500d0060045440d00f42c181c8440610701d14100c1c8540305c054903d40d0a003c0d01e00000e20040d00b4000001c11640640100c00196600c00e0784080d1845054101d846d07210740094a901780003420810502000c035100f08000c0c100c0c000900e1006240688070348106001e80d01c141d20400c08580c0f400d000700300d000103000b22621261800d40e4194998070b458400580140306580b040801c0d030798003101103442c4400c40c12003070001e141c0c0540c01b0000340f04043c00107940d0b50045410005800e04104001c10320400594002f0b0488481010750324050f01c0c1c00c0050401d0300d0900c0580000c16644446150300140d590103090343e805559110000d03030b480c0f5800c0003402e140700204114000d801252130b0a019880014403540d000d01404550354507425007500c40d0a0320303c02d203400a580040721001c040184104045034600402040381120821540c0c0c030303000d034241c0c001140c40d0004510080005082d50b070103a0001180035011030720045c94003040c00c2480c03146106d010362440d10a24440358042203070760001e5401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 97373408 1250 97372158 97372211
    0x12181c0b0901110412050c0406181a100c14060a051501020316080307020109060204080303070318030507060b0a09020a03050105030105010f230a0312020f2802010e0303040b0409 78
    0x34484a06108a5070f2120300c658480c100000c9103448040040c8142409850607000000308288149952400c10714112401daa411085e894a041c41c00803440d1140d80c01c044000a0280000c404c5064561003561010f000c51002d0758900404408659860b4051100c9841541e94050002e0907091104035403d03880c40307603208903043d98002c01250148516800200c0986644a02070617039a80d640c0d0000ca0144c0042200241810b001140200d210741d004406113201d070900d550f0030070245440030303161034a6076440c110160100b40100700c03020100b111a08001a90500504000e051903510790802040703901c04189240000c1e904e40051000d0319084c00b42e2801030040020784064a8100a64446d82a141c05081d91924200d0360b82d000064454031402001103400c1807900f0800240d60a002e51102e0b41840f2005c1030340581090804207000542e00b103801209a10080e0704104420360041d42d603458000c020543c0343c40180000602c40308008010400307495032000119040b00310042c0d5894035060210030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 97374658 1250 97373408 97373411
    0xe010b041a19170714040902060f030703061a0306040e06060102100e070305030c070603151d070e03250503030403110603040807020a06030c17070212181c0b0901 71
    0x110081580010074030740c2250000c039403042d46564552084000000c4070390000a0601c040c8026128002010035101e04950043c041c00149050360b604000c11200b20640081d4851414400940c044100d40080c651003121401d0029a1079125400700c400148560b189a00c040000800c00415081070f0141d40103851712a001000c80d07013000310000c0d4031544140080e5000640d1900c81004a05003002881d00031a00102544c2d80e41c0c4900302419103541041c014070011a08040d0814005000312400f030040f501d002040354252500800c1c01c40458001404200c1000484a129100c943e02444240c1841d401420b00240008601d0701c903585001c0c00d680140c0c442e80042c0070820109103440d1f00590368240440d0075650300c2e9550711702021305004d46103020b504075140003c0401d40e16050741c0800e01000042d2200c01c581c07460b410140b40b0f4008112031200c01a0894814544142c003144042c1c40c4c05002c0e642014510540c40000c0350740c10600c80e005110098a190300002400709c031240711508040300400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 97375908 1250 97374658 97374671
    0x1050f010306150510120b06040905010f0609050a0308030a091a0105031e06160207230a2102040c050c0f03120c07050703020108040f050312090d0201091709120307060e010b04 77
    0x45c60000c5050a1006206040100d5060410258000640e10030000c00d600e0b111621205110002c0600340120104110f00a002146240c01100c54504440c0020030f203540303031420344d41c0718044c60f00081d01900c9016241c1e030509000414414001c41c185001c1200c4841c90b41c13503c020140381014161500101c260f075142808031800300412600d0340b1001d0f00001c4c1c01c02e500005412440c011240e1b1081450208800000442d2001640112240c00c0c0407108404c080741c40c1d0b84203801800d440548802c1c1841d0701c2074000300500346500003210070006800c2c8a0700301f8005803c41800c7c20080c0c0840846600b00040b1055010070001550350042d80048125040140b01d541d0305603540b4985c04040d0501601d0310004040049520350000c0c42580101030300c1d1a042d40310300d46810100152107a400c54000e07c060013034038501c14428000c1990300900c000320400510703c1d0100300c603031080c0c0203280c11101c0429145010b80b270400080000521a00d00000c012052001d00741c00c40c0c00d1840420300c59420130340c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 97377158 1250 97375908 97375919
    0xc12060e010306090c05030303070e01090605030f0f09010e1603050d090302060f030c25033209030f011422020a0519030606060c050f070e0c070804050301050f01030615 74
    0x14000c40c1580c0e4003101c00a8100141e0034000e9050505900641c1d1610001042011a0794441190741000f00c017030321341403000e548410f400e03200760004545d01c84140002500080910401d156007a82007240c0500015100c0110842141003062003074814058100d6000304108000301002186201e20242c900300391620b046600240340c5200d121500401003401001180e11a4a8181114620740580c60000b010010161104038502d41854042d004112801c80306c0914260240c02e179002009840401c40f510032805940d4038154218032000c58251289400c0c010800b0b60134802c907a2221a1b6054040d01c80c80e00199540100c450070039889100880b104e403200050310741d0480350301910070899009200e071110070344000b40c10385587d0001d0012414400d0026111340c010b42c03e4050745000302c06407881504040001696006580314002490182000085248101d003000e49a40c0e07220300b0100d0710709940d07070000900b0350741c044c0c950b92000f0180b507004208200c0580b04104500c0e422400d00307201c051808 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 97378408 1250 97377158 97377179
    0x41b030213090506180a2304060e0d020304120503090405010b090901080708030d050406140a20270a03050d0f0e100e040b0616060c03050702060f04020d080c0307060c1206 75
    0x600703c400b005844000425440c9829402c0700e4a40380b10513447c5215645c000202e0449594242c80070340d03605107041c003108801000811200700a00311500110b18003841c0580d0300c801a480d81030113485901017440907030555980e60042900030481c1e074170001d0702ca449110030000004410f0f030008156030301c188001c1007101004029248081024000005e00759580d0510101800c00140210b02906070303070003001040031456200d02902d244c040c140760140c164249202240344113403000c1070040007111b038016181c040e0703402d007082c1e070080d000e45200e8040d540c030303030360b4a203041030740141c48010850104144e201580e024070300b810301000031119600750450b096030291a0003a805c0c0b040c1d0150361650803e6846072128812603900ea452070880303a10100043c102203000780012080d2000007400c5c80085070259100040c4180603895059803040e140d1a1542000f00980748150116414041840500348020050015119581c0582c001165041d24014024040c88100390514161450000306101243c7c0e80c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 97379658 1250 97378408 97378429
    0x150a15060207063f0510081504210e01080c0418050a020f0a05030f0a060f090203130c0605090306010915030609081e0c010509060705030c09041b030213090506 70
    0x41e0800003210720400c6504c0790010142c00c0240005043d2110412020b12031281494018124020800c069100d40e60204400801e610601e41103500a0395074005030282c401049421038424202c9040303010a20744903000c0c0c252800101c001107030000c3c0341c03283c00d1358201000e11b07806408010785519103424055800c030000075190106000558500c0043c495801c154100d46410020700042ca40714034112a0041055000b10740c0e440750b4a039814003181c0035603039038003c04081e0b45580c2d02e0f0346001820001c1100094100524107003080c06400001c2003c20300c806640b07030140c0604d64450347c0d5901d00b2402d0600c3c003001a8895190381c0d2a1010390a03500d544c540001090b09d46c41400403807200c03c14104074905004040d0404080440740010200140a5070000d051102140e0300901c00da5882d400001e4883c1d008481d40b0003c600200006000c24000800410130460024800100f01d402010009c2602d41c0006406003c81d030b0005038002e00d220001c2d03802c4002c203888081405a40fa0540101c2c6480300c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 97380908 1250 97379658 97379669
    0x20f0a0c11060301090c02010608010608030f0a0302160c060318110607080c030a050304050f01090203070b09120607030b0102011503020307090c140c03070c05032e0905150a15060207 80
    0x10303504240d1003005100414407054000040c089a16561618010707402405694040e00c095880c195001a4140341070141c5421520b141015600301040b03981c41c2d48540d401000f40404041e0700702316103280c0289a000d031040b118010480404401c3c140b0318041c0886411507886801c1032081d200440c00581c441421240d00d13131003910a070b600d445407481c1c40c1d8094020300700000d880c2d01000c10f00d8040c03540d0100c0a580f246014800b00c6a03210020209035007200c00b203010280d01600481000e001c801420401030816420261010f00e4851000080b1420403c0540312072002903242d400c40340f060b41e4240204007544458042d6883e4507440c0d640080c0c4d98007403a21590f03da032912821140225800344100300914143c040c03820b5602d10740c42c108251070b07034400c1c00c04454043c03103914045018140003802252622900927100c070181e0048883c075050b0b00302803c00c0c450702c40d164410540012010f211125190000400c180158217004c0b80784030940b0b00003451100d0340d0b011208200801c5038000303000c1044a4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 97382158 1250 97380908 97380917
    0x61710061b020a090b1009060203090405150301140402040f0b060301050405100305071202090c030c070f150204030639030902041d240106020309011b24050109020f0a 73
    0x8001c0901c0e03aa5415464101960281203584002041c00007504881d05000c8110f914070003d0314545010340b01d141c014010303030005074010710403082c5a0600350f011907046034200880f42290140000042d0a5461582c0c84407410391600c4144811030a0078042d000052040004c203025982042000c15070f10701051041c0f0f4031403902c44010842000a45056901440e0840140c030f00f13094554010585011003105d00321700810040380040c58140b052405d9034003401c055417206141060b1900c3e2100510f5004200359410103039030b0441907500c03c00c4c2c030003000210b1241c1008103a5007150780c05840c4400742d000f00a090700b0100101c035402d40d4058003807c40d290303000e400c001070058100c0c00890000c04440e4078a1140b0000c1c0300c8402c040300b000044540c1d403c90340384803030021011401c9240d07075482000e00c1682e000d84c1c02071122882540c007030300000c0d1407001645c0580d440110151210300340c403414000301840c100f1074044d00c0300405074240a038a0160450200c150310f4402040740c500881d20541d4001ca0070031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 97383408 1250 97382158 97382177
    0xd020112090f08030106080603070f0312021c020c150a080106050f04030b0117011d030f1c020f1308060103020906040b011101050414072c0c0d0903020706171006 71
    0x30203a40080c039110703048140003038500241d00d088035440d0302c280500300200c3c02003400100c00f85070005851050310b60707010540001510b160388074201449005105010740c0504181515074006400c1801a1040785500a06c004034820b410301c544601c03114450a4100020000a88010b27041a41181114227520389190b640c420030340320b00c07418007464000030003a0440d54000a40194600f400c03444100e0494000c00503c800c03a170300108a22981018608660000e129440704d40c8154000b42c2031444030680400c00748607100600c14120391000720280888070300420604004099441301c200a41082c038024620b42d4110380004040d0302000745801e1080351104084d00e1103900c5181104002800c0f10001d016500301845c000c103400840d44081c0d08244591580064a121545081d556888041041c0a000c12014980000700f010052140750000c2c0c040000d0807010740b05102d10200c0d2030203135018010460801800070260303651151681c11404681080c0504150050405401c4504504100224 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 97384658 1250 97383408 97383437
    0x1b0e010921030909020c060a050109050f040809030709090503121807090b0406030209040b0402040b0d0807080924030a050601050403150e100612060c0f0801060e03100c02010c0e040b0d0201 83
    0x60541641112060354004a11035000c2c6c0d4001408034007514200a00740f010b40c1e01c8040c0401140d10032280300305000b0207900400c01080c2000010411a030000d425140f4150b110b454001c159280d03417004684940c40095296076488040380c80e203800c0040741200f9824500420081c1d42e8440d294000c102c0a0ba50b00c00d007161160b40d86603c080000c6502400f00040703860642000244041b003141c05a00803400c00320361210030b2400000c807050031603104076103031308085e013545030001d103500030f0020542c000191401c9646400c0043c0a5019620a040100381c0d980c5884e51031101a24800b41c461418017000b0b00c0180005022601c0c0303141c07140d40c2c00303d0005000d0b18a626061809952041b03030348020f45025004070780c107043c0d6500115114055a014054001c2070201101e00c03030030840f13402c130001740050b0062200074840c02d00b6038414000141222002c100f011580d004503215030481101503956100e00c4000640c2140d0400582e00301203400704512140d41020809243d049807000341041010f0404800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 97385908 1250 97384658 97384667
    0x206070e040f0e010c03060b0f0f090301092102070509130b0a060b16020a0506091c050a060221090c03060c0c030708070807150519020912011b0e01092103 68
    0x10ba04a11402800311110450350203000381200d01c2d4080009090100208140900b601159400b00b152043c0380d00e07203100c90302450095004001d0059045d521000c0c994085185510400d902109030101030310042207410002e8030b460126070206000c0e0003a08100100c240001801001d8a608160b00c40015030741c0000b0100140500c0cac0204d21004e07000f103140d0350403e1700041043c0106100b928103820454895003042898022494901e5100e01140b4203a02641810a40600440c2c8036500311909580b4940d0340328143d80104654282c0d48001000201c944440b0700460341c1c010341c005002d070060038240000700307407104001400010f4100c800100300c10342c4c1d0b6082080300c1e046600f01c00380a40728000741c0f40094455000301e600340e909200043d02c50107110440d21616010b012a01c8490560741004070b40040a50445030520342d00820300c9464864191003800392035959601d001c9140c0c0328895281010b013601c00c0211043d4100040340d87c0038468261303099054500900c41d04c0c0d9600040c0700304d05c1c0845 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 97387158 1250 97385908 97385921
    0x19060203070c020a0b0405011202090a05040c02031c0207060c0c050a0318030506010314010509060705090d17071211010213210c0303050408061b03040b07050c01110415030b010206070e04 82
    0x2d4104d0400180001ea88408601400c140c8209a80e0b042c440da088040000c16030056910040e805045c0000410091420b40e0200007a0320680c01501d0420b1300e41547c03504903926420a00c0c0415400182040c10080144074501c0d44603818201901c0c200260340354030381e40b0420800020184541c141d030702020302881041c200d0003150700ca02155501d6849141200c0051045031103400b6a600f4203000c144c000c900445c40611824a903929203041c0000340d400c1001d0320040302810385403402c0c421071110311420214020100240150002c10b8803a100e20300050030802200c0c8845a264410b000f1651104601030060044070a80d0140c003800c0404074146101481d03030041c0041040604d032500004142e04000a8003c8611541c2039600d10740e900030070204540008a1001c40e45e13181000060002a60341e44080d0704240103142c070a081c0540300700001d085075212821901841c0d00814104078912402030302e104c5001c15450144071071200b403000030350703500c1000c0e18020500113100c080d103c2c1911564001c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 97388408 1250 97387158 97387163
    0x1080c19050a12120219060c050d020d0b1018140a0e040516060f050703180b040602070503010f11070f050c030d090509060904030905060a03020409050408040e0919060203070c 77
    0x1800c089075030b0720b03510303c00d0380405100700c9848105441910040f0300108901038020300d81d03802040082c1156a48800400600d50303400c09010023400100400180e51024000904114800140180c80101002250540414080108080007404290030b03008038090030122000c4903102c021079442c9600042542d81d140c0c0002d203008401a081200788680000c5d136200449410344007603e0241c070f40700101c40540920072607a000c034a00304224000030740320340d888810000e40c60032100b8045e40c0303070289109243d110b40d01000c0107920102c800c0c00149428403901042e61602e54042010341d151049840040c0a5550090705a492500c610001d000080c420380320201c4005094a4010200c02c502900c0d08115000340c2e800b6645140002c1d0305400c2c0302404034062605515041c40700d5140c40c042250507800080d84600300f517021b000c00a1384003d036016143c0035501c100029034071075061040224060303a0003403511505a00c01180090034004400364003041c260407403005a92a522010155503d00468000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 97389658 1250 97388408 97388419
    0x11010209041a15090607080d0e060103030201061d0907030201080601020a060501120c051903061a03060903180315070f030e1f0506040623010311030a05070e010801080c1905 76
    0x10b1241d5400030590000341070204840ca07a43e01c1410b4501100300d4040c50200680008007000500c0100d841040504917a02c001341c40421440175030007107141042820391045000d43c1d124901400500012010709422054a8110b0b0f0b140b403400c1c1e03071419584d0409110203130500520358085185a4800d01c5411101034000400b80b2155950f100ca001186030701e00c109170340c2d0005c10800803845103001d640860140d218401442103280c19a246e820042041058504107601800480c1c007103074900780a41c0384103a524102550705d542501e9603107510034070402d140740d22036004090f28040103078144051540041a0b07284c410851a007d103c150700070700c2030072194102d03841075200ca007040c41c04540c40c0c242e0214141d01c09109a0300e0700c90a001c16070704c0ca4012608600400d40180b0050700a44242a10307442c41490003245020700106003000759481a21102d214a454104101400703400240340c1281e40820310f070a134015854480d8990316640e641d01894810032042c0c2d01d08c40c2c000d40c1000200d000d0170000f0507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 97390908 1250 97389658 97389671
    0xc130203040819050702010206010b070201080a0c021f050105030705030d0f0f02030d020c03090310020c030702280806090f06010303081305070b040b040e010b040312050309010f1802130c09061101020904 89
    0x701134020307007040340c0490041c07041c0400440c1042d840b1064543c00c0703a06860310304054803209a848040e0908407418021440340034082851a0031001c0341d410303001c1c04030400261950600092500f8a2200c2c0c0041d4025444a80e82e103070b0081d405949013038400050701d44014801d9035400101d065104400d0400103407070010850000c00318020004000f41001281100c0455082080728000e80c064068048007540042c0412400340c1000700c0ca1403105e15a00607201c4843c0000da00d50301034614160045490b5501c4041013011110f02005640102d00c403113401020300c0e42c51a54010030341c1c680100600942c005503003012040020400c80640646610740104d51103d4407100c1c9044150030600c5403c0c0500b00c60400020713294844070440713003a130350003541d042610004840280d40356400a00041d01640da24400c03500781d0b2204e84100031501000301680140080d4600412407840d0b03003443c541000b2031400340c1c0f90180b2604401d2030f40442c0e0444c03c00c52581071312016010300a00401d0540ca41040c00d200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 97392158 1250 97390908 97390957
    0x10515060309071805071803020a060c03090905090d0207060203070f020d02060904050903032a0a08070915030911040507021b030102270103110a0801050d020409050d030b120c1302030408 82
    0xc100398414900f60f9500c04147e0042c0c4460b09882000f44000307500900c51940c03e00040380308411070740b500707402414100c3c0da0030b83d1503101f47c04943c0200c0d51351400d074100100ea11142c59040c004000100140c1c4015400e03d803003502c403001803448031880248102c10400e080011034440c0000c1c0d80c0310160081c0204024509801c103d030302c0c1c1e80212504884034941c00d05041d900c0c8044206441e07050150f2405e83e0403c2840031081d15080c0c40501040180b1807a014000741c5c0d10f0f8035406c240f8642049503000308080340f0324600003410044645a07144520700f080d0810003402d81c0000e403803820010644050b154218045d001c00c2c024858404094041d8040280d440a84500d460313400d07101e07080a0740c08122441401e00141018080c8102060000d040400100070701c1c90041d00c4203101d10b0008000083c4078100d555036a14011351810910046611b0710110304041ca4008940741c800c0d85410003518000b21144001101c5c4412100c2c10ba11040c0d001c404034007840980000d841d40c2120502c0541a10390516 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 97393408 1250 97392158 97392161
    0x1612020114060d0b01031e021c060b010507080a030c110706021509030301080d0f03060509130c0807050d0807080412150e01020a050a120b03070b090a080105150603090718 75
    0x14000c80c0c910301c0d003034008a0610300704400c40c0403c4a402040c0b4044030303404c556650a48100044400000700c0c42c900c0f040300035a4a07804002c00c8988001c2c980406030895252100542c2e84043c00181408021f101c48404a200c00c011100c81030441d00d40000c10f00a8801c0596880ca00070030050328500c1031190200382c107900000d040e401420144040000d590b20f41c0300d245d54030b1100740a00345003600600b0006000d240149000c030103c81e4035040c0864031503180c402069148030101c5109014035100102c5205201c0401c0b50300020781f14500c05000c0480c10702000c1440d20b5041c160042005d0000594036081c0300048080d40e000e800c0345141e151350000103007003003148000001895115207280a410b01e940007014800c0320100d440b1500d0b142d003040c0c0c070f031442901c111400c911000503454590340006001d58090120b0705c09450705100b1b45442d101e94100380042560b8503008041181e14040c00e00c80381c00b070003c01c2c024104400f01e030444d81c0c950b80c02ca0300c00e080c088160b2000356035001100203071010790b656 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 97394658 1250 97393408 97393421
    0xe0a06020d021b0609070324020a08010501111b060f07060207050d080907120206030612070902030a0f06030804090203090a05070801050a0f090f290c0405030705010914040216120201 80
    0x50950030700c121810b000c081d07184d12003515981d600f540320400800005d01381d43e040d0360440c0300340401855181070804440090764000c481d171100043c2d22100511066130400712020b10712041500414030741030100141085514200310b414445c1102154a0140088910445051540c45001035444030f0551034902e54890804544c440450003c01c0010700e4098009003d00031180e81440c2c40d1401c01c100c3d000d120266001130880c03034205402d10128921440200f000310014030300460700595a03d0102c20030421100340140703030501ea0341412401c1010411540549003a82d082e0000142d032904d071078130618545042071000910718020f150001a0181e010740c0018410401610140711004071011060100c5150500040c1501110382c405000f040003018040304005850031800c01d40c6803081104902440200c5c1d030500740c1a4002024000c9080c00c0c804c0100030329080c02c3c20015242454503041060949400c0607015a40c045a0003586a41002485100a8000d0710040d000c01070600000d018005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 97395908 1250 97394658 97394677
    0x4020f0d06120809010813051501050f01031a0418050d09061d1305090f0f030903070605040b07080901020a08071406070504080a03050c0a020604060c062007060e0a06020d02 76
    0x98007900181036051103052000741540800204d01e440c03c0030700150381c0c0c40c1c400385c084540c000360703840207000160741001240401c000b4a21600c40320b42c9030400300101520343c1c400302d9042604014900344d00301c02d4006048d014501c200d50100340c2c4e454603c0c0e0004411140700d0050068840c4001104419030882606403da504076950360b40b004000e200201e17150030b1104000c580007003411040c0d00006000b40c0c022038009604070700795180000804116031801a190400c001c590308001210145843c040181100502040c108242490720b0301c3d0250582d0700918101034078020f030015000220b03a06c00d0000c04415540300003096101d034614140b8180c145a52103c80003244240808501d803580607106440480c0e6809000b80007090440c0d42c21a800c2d0003040d80c0b08018400c042280c00141c0da41006440605116640d280ca00b480c070f418140b061b2220b0312111f2501c501159103403001207450a0490700c015822001c0403801a10304ac01c0d5134980813200d038024000c0c603c04541080b141485e900200110360 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 97397158 1250 97395908 97395911
    0x6130603080307030606050702150a171e0603071406130803040b0c0c01111213090c020d0816140319110d0e01151a07050a06090201030e0c0102121804020f0d 69
    0xf40c45503010b803490308c00c0d118083e512a840c00d4403010b8a1250100404440d0304902d801c01401d81c00322003183d820712050b642190401120700c6024640090024000c0e403001c0c00b100203000075440d004100b18611501e4111600505000a0391180100185000c20003030008908403903a40da55007e449010b6040040305004a0040072000103940d0700c25180012840341ea880505003048003003220940701e80c88980310403000310b00c2c0c0c00001221022403041c40c0740c4400c5900030380241114080000c0030003400404821503107400d1090b03013481e45e910481030225140ea2003010b40c1d480d00c0b050806c078080c50403074400f100414205480c0040c0c18003800c004e02219010603070284402c20880c07640f139090758007443c1850290321102c2400c1081907000440e09031801031200c842407800103162207550074030782000d0302528580d407211011002c6580c1482100700140748080030f030610158410000f500c0d404ca4001700752060340e020803a24854001c0e0740000b014114010b108640c4d441210f00c02c10b529410008a020038507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 97398408 1250 97397158 97397171
    0x40f0e060102160608070e030a1101031b020307030503040c0509090c041506142b0207051605060702040e01150905010e060402030412030e030714031206030102090102070e0613060308030703 83
    0x6500000c3c2005820a03919040c030101424100d045075600c900030040700c1001000c0b00351000c65213040c060079640501500418089900080000d020f540300c0c400703803907503007a030441c041100d4641c08016208466410320b0001d82e2520760f801c10450000203074200c0e45d4001400030502801c0000002c1c80c2d00c8506054505200310f040b0007496401c42d000314450840800d001e540304041d04d00c03081004040c0c480e1018108080d2141008607054014494208150180d41c00198002440f80410114030340100802404411a080070702007501c0b03002e0080024002c680f40c401c0444000001c0d000400000c601c6034030320548994030401000503003c0ac0c404c10304049441c03008a03801d0300340341c000c0324803c94024203c00c00c0c0081400d4100c005104110000125000911109002401085000c0c80140005005588560354100842d8401c000540030700d2090703104203d4480e00366001f1800300111080319100506a43d0b030701e004034003404c001615604015290280100c00c01120a01a5004050a60342040b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 97399658 1250 97398408 97398421
    0xa030b010f110c0105031b0a050d151401030917160204150f030f060b03070f08010c020a0c090e010605150309070b030c03010e070e031605040b040638040f0e 69
    0x140b45101d042c52980103a08500c0c0f65500800003560000c50145202440c600315550b25000da070401e44500000400009250b11207102c2402005500780d9071148031155641307000556241d030080c86409605050b1141d035540300f8404280c1c2c210004c1e1441c060110741d00c101c1031480102c1035802c29000c034492031a00c41e441264001a00f103c0007507441e00202842c400382141c4400025400e4444123341d0180c80300145455510180300d0b44000700580e140380320703405052080050039248141a0132046601c10511440800d981048010482e05a000000752540701301318130501604841e000340382c10801100380e5120b1144084000c5110b01401820707980c903540c9034031241d0344600c8140c034403d40c050420f00050040c60004008140c0040300d030304081d01040d412101290618145600b01c03030b18042407010820060400d40604550309604032000c03c142401c203052480d030568584001c003580382140540e1078516182d448010215407505241039207070350396110401003030880750040c00c02c564980b0010a05 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 97400908 1250 97399658 97399667
    0x3191d090f1e090c0609032b0323070e0105072306010602070303050906030a0605030f151f0902030705090a03060621020904020d0201091505120105060a0503040b040606030204020a030b010f 83
    0x30350480c01c00707007858120302c2e01003004a4000d100da440d4580109084900b550f92003180c200702300c2079100e0100c2908200d012001d0122070040ca90803070340c181984004518190100704035a07020b421402d03e00816218400100e0f02406200d100501120605074081d60044001544609025200c82194816a00c07401704030b84541152200802144c420b2001070220b24184029603030090500700009080da41d6030740003e00d000c41c801d102106c5504044c5084c0105403580c06055030029036080c0b0302070860443c0c43d40c980990007500ca800c904950100120790b41e14410000c0b030f0606000100703034024058032428142d0040c43c0600c07401c0848105040303134019000c80300240c030304039036001081e8055540d03c80d005e0158140540004078100580b00d0750101c1c65040d584012806422161f42d002e03159100321403007808000c0d040c3c00c10391141c0c1c0c007070110201255101c02203a9000b5072007007000b51151101d140c041c001d0042904020f40c418004901d210b174041e4960301200001c80c09989001e003085202c44140d9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 97402158 1250 97400908 97400911
    0x60714041a091e060a080417160506090c1008040501060f03080c0c01021207020d02041409010204050109050306010503070b160611090103050a060509011215060303091703191d090f1e 80
    0x5801c4a000c0c000d10031242c0c0200070300747e8401c1c01001d0360780b40e0040403501c044140d8041403d07902d0014840d00340100740102000000e5004040400800c5030114810000e4010f00c02c80056004204050780000c04004c429042100240101031100135940e031a454030302110b1b0045d000500140c441c2d41503100300c035880002d405a0075100100750700c0ca080f0b25a0244000440390000a81c0c00507107034010b6400c0c1c10030b041140c0313101d5100030740010307120341c06c041c001042591964042446a400107006104540c0c0c049440d004450101019079502c4c1301882d400010019210000f81000d80341c440200381c0100250020040114240e030104400c6d513174000a0301c00c031642401255000680315005000c0c0140200c18440c24074061401c21019074440d00c190001d0b5140c0c2c0e00101c00140031030350200085081c0002c500950300c44513018500f468140d1940c0c440d1990002d6901c410801b0500100d1410881d69440e480c2c40440170348401d1140c0307004640e500c0150001d98218429104040348846071081c1c02c002c06 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 97403408 1250 97402158 97402219
    0xd120605010903080714070e0105040f0203010e06040e0a0c031217090c190b040306060e0606120406110d0528020c07090b010e03030a0f020d08040203060714041a09 72
    0x41c800d60550300c0c1d034072a9070085c0c181254641006041700c1007454040007280010301d5030700c440071142d41c1440c0030320050740c01c0100454000707801800140450072580c4280c59000b442510001030011601c84680c2c504000c0b0741c00500b040ca1140800300901519010108842450361542c2ca0141000070824041074000c03200c0140c940c0000051403c9032074521415131015040454100d02e503512400d201800341d020713a1003169900e6540608010000040c90032981c0101c0c00c5070a01c0c14003024580112640600402c010840c50380c460305e4004017901c61045d00c1a00d00280d07810080c901e06002d0310702020f03030300344242402141c552243c41103240c494021503084c0b051130009000403514010894014140e04900a4184414a071101005880030000f1703200c0e43c081a99040114800001d0182c100044e40452004011524003000056100000c0c5160000c0d6980782640304ca00000305445402c0c00345070407201140a06281200d122048071000d0000d141d8200c5620082008428280b180e280e00c40641 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 97404658 1250 97403408 97403417
    0x60403090e07020d18092901080403080408071502030405010207060b03030910050d0f0207121205010b030112060f0c23070b06010503071704030906110c03060c0a02010603060e0d12060501 82
    0x75599001d21030440000c11542c81c5d00071034030f9552504404025106c0b40020100c41003007a40c10400305031200b0f5050421740718207003031080031030a0644008040070001007000c2c2c4094000030300d00f01009201d003007881e800008060115120308043c03521b10b010754030142094a14504080700140b007403502108584281500400d5010090304280080d070319070308002c0d05803460030355600b000040100140018a00c0310b200b850515908020204041c284842d44045885854900310040c03154030001002c80e41500d84102c441c0360840e4144c075150000d840900c482400050400d01d0b819405a0016036007605103101400200f2541f074201d1100c001c500601202403c181a44004101d9a50081b0300440d04120305280610072004241c240004c3da0030142d034110700160081000f001926404080380001100d06000b17042d003640100002a41c5200c041c28142128030002984c0c68054000d605c04002192b00c080f0a01c10403940f009400e4503216815208400b040100308a41500007441c4241426030348140c55 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 97405908 1250 97404658 97404673
    0x7060501140f030c010f090302030d051201060206160e030a0c0306051501050304111207092309031305090703151203180806010303050f1b07030201030f180620040602060403090e0702 80
    0x11146e84542e11002c50511003042d40c084050b88007803140040306945a1501503a9401c5541780c40c00e070243c141e0101003190019014007106150044045490342c40030f18005488000d9040003c2c00d0840d0036400400e1400300c080000704021032500b02c1803084240c40c101000c0201c48500545040c40100c030001c00b10444041000c4076850040b2000c02d0468030380c07080301c603856141c150346401c0b81c3c00103012492144800d0b1800c0903900890911541c4a01c01e4000707582440a82e883e600b1240d07412b4000c5510071031101c0009a4007a210380c1c0440784d80d100f0220a4002107940b8244849140e4000c40150002400d0680d000c200c282898445021200e00c00c00402c0d00d070f0b103075450885440c0c20040031031030000010004030384440401001d1018281154000e04400d9107944009000ca841501c0d8146403181022024046282c90598017100c40e81c002001160030054000c8052000d04200041003000500ac240400ca445c1c0c001240d81c0f140c1d1194545100c069111100d03640c0d5080c0c1100c180005a00101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 97407158 1250 97405908 97405933
    0x1e0c0d11100c17091f0b0f0a050d0b1b0706060810151a090d0b15220f0b03010e07030b010803070809010c0c05030f150f010501091a04030807060501140f03 68
    0x2046562144d032150940e41100c1c603d5000d0b40f01240300d00e01200020361244103240140c41c010228a404d92800c44e0340038101850b0801251494160800103080d441203d0005150046481458150220000901070360780e026460200000e01c500c1c0501e0406202d00c00141c20075141038800d00030400d07941e005035164540340000321040d8803c440701c0720262a0041c0f1540001d92294000c1d1300c2400d1040009041d60b25000080c20b0000c4898196644100b1101241100700d00080000340b2040c02c00c40004110164000f111034060a1203102c1160158030317002050740500d40200d04542034900c60124080241d99a8134203540d17134041d80300003802620b4100301103812503007d0030010101600c01c114200c1c003190f8450000741440c5102c6203002d41c0750000040d0214036082c0c406010b9120a955100c07690319418180002c004021038050b5412440e40d0f841000c0543e03420308140d030015940300031030ba69911400c2ca042c001030507003803280b0300080280b40034452140c40c0c4013010400760007010780148070441001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 97408408 1250 97407158 97407197
    0x50411090406020f0f0706050a090309060e030a0506040501060806070512010509150405010b1b0a0f080f0f040807140108060102060a0b040b040e1b0d05031e0c0d11100c 74
    0x1400444010750700b0000000e400c0c1014015042c5c5c0c0e80c850013101c0c5c60b00c250f402c0107025a580189405201441d1101400001360082071070000c0e02c2107441e007001c8061064021914140c142e405c0603106100d01c0e01000100701d41500864240c504400640b1140e481d40f440540d000c0c09145a80c0c41c62100c00d40040c095420241e58032a401151030300040c0e103900354000410100e882c2a00310494030000000d10000c810629406000400d0304c4100800d44400c0c107480d54950340004d403400800500d80082c0b028186014642560700340f47c44401907558031035640141d950303140c1e01c0c3d104500100c1c0032070100006540c0564481ca21640741a0041e00e895600c3c7c8442d00e0041200d0208540d02556400c1904080c4d2142d101e00240c4803010401040012120922004241c502e013407500d105891440e24907000034004010380c0d116a50141c050100118006801c66039401504180c007014894078100010f1154003444c54800455841c0070f4800201d6640003500a5610422016010860300c100300649040c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 97409658 1250 97408408 97408411
    0x3030f090212010b1905180a110a020c03060109060602061b13030606050f030d09030807030201090b070c0b09031914120c0c0114060f100c08030c0a1205041109 70
    0xa09000548000a500041e954140304902150b0360795500c070032071000c0c2071800d94100070003410801003d80c14a000009528180c420b903184e000000344038040f44220046030807172a0b83c402c804407199182c0c044000700941c2c4030307600c0282030700c41d103c1c0400001e40c2090f00e20032402940c240398040c0c00b09584100d01c40d0003130004100890001d00c0100076070f8904e03140b443c0c5103101030b5100d90000304040c0e192904011ba1810300b03001651003038210400492070150843c4e266002c40b640462800d44940281c00c0903401409200c5000e44071b94103080800403a1540062070506543c1320f03403101d42c1640c481d00402540c9001e0500c02c440341c000d09100070380103030b0700510300418070080a00c401403919031744d1400802c001c1740c2030ba600c0c284120046090a03130004280a864014030010b60428a2032802c08001198001030f41c621031f000301c003800b100c8110340384111a500c440641082d1810340d0b908114034074000b1035120225540005880050085908140740070301d40c05180c101e070100941c21428810054010030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 97410908 1250 97409658 97409681
    0x30515040903110706030f060f050604060f110102070303050612060708010b0706060b0d06030203100504030504060318051e0f0f030714032709090109020a15030209090c0a0f020303040b040303 84
    0x440300540340c0000c0100120401340c1246c1e90007041c0d90396030340c002400380c41c055001040c00031084e14080c819134441009880c1200c0503031030070042852001c0c0090707600c074031401302441c0d0b5075000103081d009164040e04614090751003034519503245c075035004403140c46100c141c81c0c0e00d000905210041004040460140100d94010f0b0780010b082555810300051580c841e1058564042d02c400003041945820300c8481c94503061503038144910b10740341c1d9005002d03200310b0245105250703441100d5840a290048580e102e10380c00401c0741c912013142d142d04084000b804000c3e052612404941084288005c0bc44441c1a10100001c5060031100d03958114400718a0000305c1443c4000e200309003007007402440d002d54850b46c01c0314000d200e84600052040910f002481600d56a041c0602c180040e01c03074a403503404880156000e0b2071861082d10044001c0d100d280c0e02d0395482449007041c441c016140c40014946812286c42d4458104025102641c880c00220307400b4010ba004040080d0102c2c4c02900312908800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 97412158 1250 97410908 97410917
    0x3020912010e070302011403040308060402030a09060207061a0312030103020907020c0312040513020a08040f0203010f0c1101050a0b060f161e1b0f03060b190b0316030515040903 78
    0x40000d49050031518128600001c69010000c100195604070050701c002c45014040c151552400c3d8602400a80024040318011540000000d170200e51a5100108450303000303009540d00e02c5241402c0c0c0c003908074001c4203056400c0e24403040e482c6240004100b40945011108075066a00e19003c004550200a14038015070040040c60b0440d91f8050001501c00c10b8400c01a86c4c4640c1004c0c1840f042d91483d0355401c0300c66204000c07044945030460043c90340b003640301c044c00c1c03640209840401d015007001da40c41c45a0381e0400440701d40450704074140400d5010039000030131155480b0301c4a40c007610004100ca540040c81088103160450040c40200780d0b050f500400a00c41f1303001c681c0d0307018950f540301c09003d140c0c1925046020400c00100f08011880d12076585480d0271600b0042c800c1d84c605214400188030326914520308070507898250349024082e6201580d86e072025502c02c1c0200f0598411515041a0440251850381c410b000c1d1182501400c0b014000c010b100c02c0c0001404002c01c0e04010660501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 97413408 1250 97412158 97412179
    0x10b0a02100f0e030f0a1713120201091202010902010314060907050d0e0d0302180f030d0f0917010b030709090305030a0509100510170303160807181d070e0a06030209 73
    0x60b010001004008003961703c8503524180ca040007450007001a1010030003148813010720048800c46c04103002425000740608401c0004c402050340140240d0100800d881d0b50003019210940d0198049481c1c14001c0c1c80c1400341e0b0540c03018803141c2d010103d07801c0e5401a045000314049600c1607006e4410510708a8000803107015560005240403100c2d10310302c0010b500020103071420030a45801000b2030740c064076100c03c083c440d10000b0741c540041551840401a00004419800e4812001180103002c40c0710941c100a0524201c28064546140045d02074881e1910004021105105284c5050740666425040d030325924200740c040c12000d000c081c106d00ca8100004e0903030000b482484d0003071b607800549401140c5042030160201d0040510f01c0d501d030b0024010045028414100614075010510f00002c045d87e2b00c14040d250796205120b18104150500404208d04243c4128110340038118030307802c3d00981d40e402c01110301410407603005030002c51141d13041045c1c0380203401604021030001d01c5130581 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 97414658 1250 97413408 97413431
    0x50f011107090504150603051b040b0906010e0a0e0103150606050a0813020d050d0314010801020405150a0311070f0507050607022206050d0b0a0c0305070f0c0201021203010b12010b0a02100f 83
    0x1586c17499001076840d0f811804180c020680070a40c00c82101d5010384042c001480c04c000004d1040324020b01190600508060b207803200d40e100680300019101e20191040306584a051030342403096094040c03004a4605000810300a01510075282c03204810303501c1d00d50640d20800303030f00c680c041c0320b00d0200d03040b0311800d2107000050820701284181600940d0300041207084803c0910707400c0b2040c0e11862541e48100f109102603110420b4010b08406042c2d16103641d000c1c003c03011002001908240c00d0407090214054040100141010700b8543c0140115541030b034451042128074401e252000303510001c0c03450140c00348035103240150100100c1403000038001d030341c801c0030480f40d04004000721810540d02080007c4640c01d03205640502020b403608000900c0d1042000d02000c6407200124140105000301e0001c40e80700b000301103145540e00041e141c0703d580d519039890468026010007106144588004203030740d04c0000507101e03154000d07070042c551588404101c2c40188086d0481c644102d40720010f0500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 97415908 1250 97414658 97414661
    0xc010219020303090706080910020c1011180312090108090f100b0a090207080708030c041203080103021c0302100f092003060a0e060103060507050c0115050f01110709050415 76
    0x40440d5600a150340e443e05803007241c10202660410001c0c4103900c4244001d15000144401489a01c00e40c0140d84521039404035107800741070b000c0e0038489403c090b80e442004200030003519600c03880c070011814001c06001015111680a8142c03001c01206101c18113444d0300c20707030102e6042540c080541d80a01c0c1c850048d582800200814120b1254541100713840e6401d103a5880f100402c01443c0440c2040305a030380382500391040150180c210300d4003001044808507010120340050810302840c0d81c91119518003e00400400d11080c0c3c4503007021140203281242e03031101038210581c035a002d02404152210a407004004000301104402c2ea5480410005000c01d01c940420f40303c0c00e42d000000c80c203281c08040c41c084c0c004100880d82e6083c079004540104002403c00c1c15a58042d9021071565210002213850340a52011181d1a60811030540450303503420111348181c60040c0c2e42d62400456101c0151420741c03002008650130382c4664420044041d2070780c0001c0e0041e100744a175441c0a036101003001e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 97417158 1250 97415908 97415947
    0xc0302070c08070f080c03070302040207032615030a020904030807020c030609061609080a03050a03022503091505070b07051606060906050423060604091d0c090402030a03050c0102 79
    0x1000d0f6000b8501400141c1018400c5002030031808014460141000c020a495200e1880020300868000c2400c804046c0a0050051520544140c040705500165010312003010b0503619041d0140a030110403601d0b05001c00c00c424202d4000e8040c4881d6103882d90119110200280007504502a2244004140d030b0140031090003003050100624140c14001468030b003411041c2503080620100c118100315003c1c0200c0e240080d01e815003000f41d280d9210410540103423144000c0e4218102c400311400c03075400121080141d549001c1c4ea01e80903016165223003035449900c12074a50007c15810300c80f0800003858111200c1c0c0c854043e10b82141000031000480d1610390090303808540d41f64035244240407403031031481000e001740400c1750140101207000141042d80c0c131500348810b11fa211520000b031030176100c060442e8010314694104005071500c4126100c80c0050600c4c19440f14007030742003050a14070b4440034035409960001c0207803d101081d0b0f0380a0305c1c0c1360b001c0f040700d55140d50240b200309105a90791b041e00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 97418408 1250 97417158 97417169
    0x711060408070e04020307080105040209010306021804020a120c0306060921061506021903050a2d0e030606040504110925030921050306010c060e062805130201030c0302070c 76
    0x12031a5084c2841003505240c602c0c2c0064103160716003410031000d07076611180d2604507508404010707a241c030701080b0044050008641250040e0000400664040c0e0000c442e440e018072000c020401031b115144e0850a80e08940310b058000360f442c0405001c0f62402c86003500001d030611000c004652113035030b100c0064035038460008070a80803284041015a4051000c902d04022000c0001801240340e64080c00724001e50308038804004803401c1c6206035003803e1500d4148009144184000c41c100c1e400d00400c001210010b01b40640140c1c00410f072542003d0240700d00456024540d04410146a000e00044100040c007000c5010245d4030a0b81d1007001c070381a0008210050b035030104000c125420030180c25140711010a090a4400c4610f882c955440b805480c2c1161003440c210b400c60206083c035001070300c0c2d4a45068400d0081105008400c054000109140d090b06124500c0202000d81c8443c200c0b0801c407a140e2444800303070480d01c0150710a03403103014040040d090050815421b515050002c9100d038224 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 97419658 1250 97418408 97418429
    0x60403080103150e1009020102011d060a1d0c0105090d0c1d060904020117090309120d0e1801030f0309180509060903040f03141e0106090609020a05071106040807 71
    0x50041c0003920711411540c0f5608402402094000700e141079a0700309090040c080036585240d64011a8800c0d00b1080d0310a0511412090465240c060703030f9200e04007076400c1d0309101d01c0c0c282e00e144030102d280800b0461039042006000004001001500c1e554826401c46a12a8121075a440080d41515481d0060315107045501044040400f5000c08200c001c1d04952056002d203003044010b0ba40410401c0408100100d030b9000358035148802485c6000e60300881d9405948035842d041c10180000d8400184002ca941e8024611040300500c6010340da081d0b2840c031000c1c1d1020050000c02d60040d2130310503140c0710b440c000c050281c2ea9103c0f82407a5140c5401580c01c40c0c2c4440900036040410080e580e04408180701031480c0502d4602131420012f01440f004104100c0481042411a410300040440d40001501c442d001403203400058000c1c0a5406401c401620300400850781c28164400c1d40d000d02c0c130301e4948031301e810000d849181c03000c0041007080e64003d804000c0450a10740a000c03103c0207080c0980c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 97420908 1250 97419658 97419661
    0x408060a020304020d0f0303020918040606120803070e0604030218070311030907050909030c0a0b04050607090b0405010e0d0204020d060e0c09010813030306030b0f01170f1c0507020306040308 84
    0x105410114054109602680148107100140c2d0300c2c02d40d03030108a5413142440300010310a15054019014005505a01100304003001d01c1c0d40b50b9200b4481c0c815840384c1010401941c40e51850080544200400350a1100500c0040c40c2107001750b03460042ca4200078260340c10242d4035030015040c41c0400040c2d0082000b01c0042c0301d201d030f030140600b2540c403c42503a41d505610700006910343e20915841030301d04c928940340100d444558288100d82e40100c0d2801030b14031480460a0214010070151002c4502d07104410001d010940303d1100181500d00244010b0310b45450980116040c000080c145544a50b000200000580d520b20003040c840310741100108031640351610011080b00014500300d4070765030030071214105a912015055215071004004450070344c01d41000c41c0106101e400040000205900b840000034034503c080b41200d07503120302d542d030042d640012941c84118844c030064840e130004440c58000917003120b6642c83c001091130001e0a211580c0c002a241c01d805441c1580800d01050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 97422158 1250 97420908 97420919
    0x703030513050c040f020f030f10140303180310091103250e0403091a091002010209011713080414010f08090c22090506061e01081b090a0b04 62
    0x1010361140801c95010310780c00d9661181502c6540003035140d07109698406414842602c82c0d81030700d1240c20751904e015128540003080c0075500800356a407941c0c8030032020000884111030039000e9076408003d4065414000d44028040911010b0450300d030b451b006003202d107040403006104d00803007180205182044130100205242c1040501e0a801526011017620044c40701d01603a0810126410100010555921810116500d1072150048260400d4031040e040a92004201804212004460a41c000c400f0008107034200c0c415489018085a03142444c1c858103480b54141c240c0c040c6039004c107a54080c000e80e44542050780240c00c060a061001c1610300025648010200042e214a080860040c1002200c080d500c840c216161071082000c5080160f104c0b12244000900640d1840700740304002c03480c5001c54807004200c0340755009180300c02c004c14504920800b010346450060b15007a6081e1181d005150101c12004d00c0300c4461001008408040d40784e25849600400416180395116030820 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 97423408 1250 97422158 97422161
    0x309050a0b0906040e06120a0f0b0703020304050c130f090605010e060303040e0a051e0c030a0e070b07080f0c0d020703050111030709060e0f03010c090302041b020a0f0c050a0308070303 81
    0x9030000350704090700740b01e04641034407460211000d03105629544805541c1e031000007071030b10504d0060092580211540c41c000c015100b091400c1541c800c2440008903034032005c04a08902003240c2c0038001c0c1c3d014070440446400c040a02060b040d02413040401d15598030380146013520f0002e40115005695040100444100790f050290000d00840c007452034a03150908000b5503800103084103100c03595540214000410500509030f90314507640c054521494480c5d0141e00039003048940c506024200001e22180803000b02d000c07000da0364501c80c03207801e24a031038445a1a80c1c0003040740b17000b044001c1107041c02500003080210000a50355004045d0181180b41450a4a00d12442303c0350084050082c000019001444581540c0d0186480d82818441d240041e2010055503405078041d468000d0710841a640304000d54240c07070082c4c40070b01030344030320350912040d0404547c04c0c9801a04002101c03c0003404060302541414001d01c4461141d41d2a480050002603031940304880200340000c6136410150503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 97424658 1250 97423408 97423429
    0x13060f0501350c09041a0103050601020a080a050a050403080d091e030e0105091801081b010206040f0b0910020a0503181605040c0216080109060b06130905061c030905 73
    0x1910740449418080d4002c0c20002e00d0411105040018500014155140c2501580d03201c3c14020800d0100303610300d074402c408039181583d07003d000905100c00103070a94000070700c1c650695848409149045404141101c2c4c1d60000c0744c00604010082200002181400d0017600b082590348400281c040301c83e26040d41c408020100741041c61103118804008282c0056181c850560b0a090440e9200b605400080760050345003c030180d4884a41e00210300e50900182c2e0902114104084000401d802801a40d640c20b045034020f22070120350b59010300041c9002c030030036080002c0e10204c0d5148403001d000034007682c0120540500040d40401080700b0400200940c10034816030350003820b40141903030040140d200c0b140c0125802a43c070750f510801168400c0014078079030001101c004035951b440700a110701030000008207a421905180d2002101d16008003102d800c2101480d810900501d80036001018003070045c81ca070703804501c2e20aa001c8804a1410003002c40e0311a0f66032040b12800c1104100300c9008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 97425908 1250 97424658 97424687
    0x80109020c03220806060a030b01050405250806010e010309200a0f060f170420120d050d0501060f021b03030d060b09150406050702011101060807170f0102160605040213060f0501 78
    0x1c1f001d170104045040d03041d4044c159002502e0120365aa0342221903403c40d04590b41c801d0401e41c00d0258043c0559200c1c1405002c2c0030240d856480c003c0b283c800460640e01030000151504c1442c80703d074030000d4407401a000280b403014110240090b954056000c50210603485000415441d0a03a0207035198015151941e040d130006081009080640b0782982680005140344061000006075103115500c9252140c07103216580107d0700c0d01315002c10014103640080d4007400c088c5062800100b00e6600800354500410500da009044090385a0040c3e07d80c101d4900409426010400020070400c0443c01128060081c0b40c4030715956094440900c80d10814115550406400510092107595441411600400e40928100e846901c0600c0561300626003540102c1403841404400a11108500c2466200408040c29a05142218040c4501b81e21481d4013140e00c03106880c0d202e10024a042c1d0101d6003242c0090421500d010155400100302e4a480e00100c1c400000000d04210a60f0b01c10003801d403410b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 97427158 1250 97425908 97425919
    0x102030405150c040f0b07020a03020303040801060602010b040507020a02090c0409021224011407020f06032d0f010b1b06010f050f19050f0d050d030507090803030403080109020c0322080606 83
    0x380385ca8a400300c1507501d40039440b0303c2540061203070150341d50321070360038081d40e0018150303503a6554440026000b89138a00c01c0801650809074811b04a15091040c0340c4107910903000b502c08400c465081104202c00100350100c4048144030220300c0b04046e20282041c0611541c2c2d4510a0901000c00031b0b02c0680b00d2000340c1203008604941001ea43c1c070252211510041121039074aa400078800920131291401c221a040700000c010040c1c04019074210944040305050b9461190341c03200c0035000c4140d030480da940c102d45450001006021042002850003500c201100e1180e00410181682000e0302a400310310071b210115070600003460501586035501000304c640003404a5001c0c0000c0d0b40100074842c10f84908861081074803d92a00f82229440340c0e4064240c0e00f02500154025000707060903030302c40b0300243d200301e000300e441c00d0000700310790141e074054a50100a80c40e1000840196101007a0f03125540400d005620f04911000701400c030203241818080400d90429038401c2c9030000040c2140c0c42030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 97428408 1250 97427158 97427167
    0x30e03030c120306130e0105041103120f0d060302030a050706120b0d02100e0901030f1e0f120e030f301b070315020702040c0e0307051c050102030405150c 68
    0x1c88001580c007600c0c1c103072042d12512507403010f00081740d21400b220000354480c100644490000b2040d4485440303640315040d01000c2a000b84241966007005501c0b10741c10110800400241902c02c01c090907a045041c000400c0c0d0300c0d200d07404641803403c40481210326900420040c44882e8020700c2c40394018500e100d0030824032002c9d400117554010780410103030003501400300850056100b04050661140d01500c599107d59507407905c607a44500e10001620001840010000e15070510354902006a8000c20200d000d4441901c61b80030a030140b44001081c460b0752445100c25803010301089603c43c2e034640c05091142504010030680442118a82c032441e04a0070026440c0f42030030003900ca4010506140c150b103a0301c075544480c0f804055030800740c90303208c0040c2d0449484545800811180d882550140042d016201c01610420b90045015a041e00843c42c24491303818401110b0300d142851000382d100c4002103840d4903007203a00958040d82c40780c000c44060f45c614a84403c52541145000310081d140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 97429658 1250 97428408 97428427
    0xd0207150e03120a2c03070b1602100902090604050910050114120d210e06040606140405010323010b06030705090a1a0316021e100f090f1101020a0609060504030e0303 73
    0x4282000f44003544454080802040500042054a40c11f40d0300c09460596800d1502c800d000008907580148010b100c0c001c9403680400312801103807299613000c3d05d02042902e8100800002c0c040017402c558080c4603030800c01c4245611400f03254000c1c01e1103500c2070030320b0440d00203001c0541007001281081c0c4d445075068030500c0764810031440d00303e07020140d80e11b94214050001d00181c402c020000c6007a2040342d00b4002032003a668009000c81c0da5059010400400c880c0500041d01ca0920000c1c2032180c3e107007490107501209800303d501f10b09540b00009034841d10305002881681040d10410700040000ca860a0281485000070020305100d20444540002104440f80c542c40002d06545203082101c2004c0c1c0f82c07134000c1040d810410181c554160300340c04020b0b903041c2c1d1200310b130380c00640b0503040694805101c04a0f201c2c0c00c9403240c00001503103c010154444c00022034440348041d0442c45070441a40101d1074920035101ea0034030404000c542402c0604000340980705c01250320b486a00204016140d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 97430908 1250 97429658 97429691
    0x1b07020a05060702031005041b1e03260409060821030c090a120303050406050604020c0703020603060a0f08010203010801060e09100b0621010503060901020a050d0207150e03120a 78
    0x2101e8040340e05503611541440844c0c00c0001032581141600d081c0303001e01080081c060050b0b400d40040c0c81d20054000e6841e80700b04d031051400d9074003001c000b08900c820300105907029003c160300a040c01e440c100f04501d0714042c001c154800e50001200310782d00c6000303112441c000e222160194004003e100741000389081c0307242c0144005400050a4000010004070079201e95aa04d40144401d42200044052030b080c00390240008650490701103240c000000e96914082c4281c0704002000070052015030f0441c4d0a0003003581c009440030341e100342d101400003180702214040e40d0207044080700140e01d9516110356030b829143c00d41c20a1000388407103010041c1071500010303071600381c00d00340c240401e0b107055120200e00320340300f0059140c824900c51001c0442c030b069030030015030480e903003074088890f80e036240c070803179800c0740280c480303101c00070300200b03c50019100350b5006800458040ca007460080c0300444081710856038018468041d681001c586107040c101401c6015520000c0306c0000e13c98160740d8002c444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 97432158 1250 97430908 97430929
    0x170f0f0307081c1119020d03052a0d050705040603140421110d0507050c0f010c1202010b0310090201030b0f060a0f020a060c0207030507060329030a05010903081b0702 73
    0x303040d9020254640040c604540281607000d00c280340d01035541e20000e40e113205d04080075004170050310031160710b000010300c83d101d0544035000ba07100c0c1c94880e108071081080c40b1106120500e06c0c1c0d100610840815600d01d100d0517004940548840b542c4500c0c0100250644200301e000090154101d4104404200081641c9000c5030314140700701c0020054000030f0b207100e001000564482d1080106120600c0d810030004c05d400c40c041c0c4112500301300000e042040121a01c1c0303226000078000032000000800d41801d800044005000100340c0030401c1e0003191400c2076546407010115291000841503580510a0001810b82a500e10451988140102c0c4242c800d41c14068100308200008086451092101c0da070307000d0340104280030b03021980c48020340d41c01d0280016581802030081c0020107030301074400c0301621901a00807641d120004809030421a60090b0390035014066800c0b0030b00090130138883e213641c2c03611a481d00c48113410300c2c031003020103941c18100820410804000c0d25025030344003484c06 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 97433408 1250 97432158 97432177
    0x8061504020d0f090c090e1f090323120606071109090a020a03050709050601110604120c050d02070f05010201090f06050606040f0e01031509030e09040201020304170f0f030708 77
    0x96079a102d2240200700510b50703d5090340d0b4031480d00341c0c500108a49208103d0440c0c09003001030000b02000d000460f207601d4901d2041d80c0c00840b01d007582c1540c80c1d1940000e44030358024208900074459243c1c01d4043c000f151800f681c2812000181404402e0951018a40009003902c010381080c846540f104000003101040610a0508000080751058104821600c0f150301521100d270540c2e41e4078050780d032201c150240907074060508001503200d51080d410803041044030070003415035450b180c481602441d106a582d4080280501b038000105204000f640d1700509030ba0300a111300ca141048100c1042e540f03801c10f90440e4100384082002c40c0e8070a940f000041e810410008441d11030100142c002d106030342c80428101900e040001303128000301e810341c0c1280e01550034440d400710307018032038800c0780c600c0d01008000c610140b02840c050304040401310b0b807051060044038a841e443e0810425450540b9001980c5a404800011980101800b41d10f0400c03000030004e5007070080c26030359030780b07075010390f8112 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 97434658 1250 97433408 97433411
    0x3231608030a080c160309050307081501140112090503090a0501080c0d020f0702100c0b0703050606040306022127160b0d060510030506010305060a0e060f010507060c081008061504 79
    0x4151410381d0041145e82c0c0c800f0405894041105624010344038180c54483d06100e8083c6e103800254001000c540000e108090329801c00d02c503824840b0f05151049c1124485040140b00c880d00078000c0e5242c441e810301e690048004580b42c0402d03104012241609070030090420440038244203048801800b55400c00c80000000741e00c0c0c0083e01c0001800b4001d40401940c4107225200b2440000c2d0408905441c880c09902d803132800c1c2e031ba0400158180c801c140c490940104c4100400c201040b0a0f038094082c5012003810b020702c1007039156010407184000c0e10100e2041140c0c1018072143c3ca03024030000100b40c2c1400244c01e005065042d174001940d0b49220f0302030202000110f2991400e440c0d4820400340000420340410b2020034040100284030450f006400b1030b1402011840900d03040505100b103541d00030803040c059031040188040d40000035511818410240840c5002402d00c2c059080b0380d541c0c0d43d64125452414000101c3d14184603484543e0a410410503c200042e07091030001d40d540080d2f60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 97435908 1250 97434658 97434661
    0xc02030f0303010609060f08070c020607060b091f0e0c0315180f0604060b070b0601031d0604050307060b0d0f080a210605130606020703020d02030703231608030a08 72
    0x219050401195000d03030107000000021442541116005041e1002640e82c980910040c3e842070b107403207009890138000b081e0302c0340b032100052a0400040000324803a00010610104480226000100a417402e0150600340500610f80c803c005840030000c00c03078191007401c581080c00c481c800b540300240c0111607150081602050036110003046940030785540341482418a4020044a00840280c903428031071428108001741d0030341d814040c6c0721030a410038008a00e90b240c42c4019002882d114440c402148544500300440e4a000d006c0c40d44076500540255a45081c1450400100c50314400100d04c5042d640401c80042070000c15401c10f110340c080320700ca99802c4220002c1e035801040a40292166900a40d0a048913a060708038808850054500c1c0b41c0c040a083c070b4090959179030b8040c0c2c13001640324420400245c9480c00200140310f0001c0c05680b2440d44a4681c20001a00501c0b0704030029a0043d1201604408000649506001c8064000200c1c1410045a00d13445800a50030401a1510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 97437158 1250 97435908 97435913
    0x60a120f03020f0a0308040c140105031f080709050a05070306080d0509130501080c011818090206160b0f090a0308010e182508061006050a020f0d08010312031a010c 72
    0x12411507510583c1168501c05081c90028503942003186c003183d45004074240001d502e2014014454850016100d16045036246580840702054500800e401d0706001c00d03000501000500c42c000241c01d0600010500380b42a404070810f4a002401007020940741601c01c0000700741c0841c1000d07844200c1d00c0c00319601c00c00c0c3e4002a1b11126107403400c1b5441841e000c00040c441c0c4000441d98411035003a210360490320b040032111400250207214205840b03813024031032403806d030966021303036400b600c010003042c104503012003200b070061407080040715071504150511414104203245154092a840028040000f450381c00811440061040900c1a0300704400b003002804600c24499001c20ba00044618050030070f20302c140035071440803551800c404804008507084038007040b9184104641e90068551914000e012121544283c05da1402c50280255000700340d00c1c28000542c00076190381e5540c40039411420048810070b0312102c040b09151500c0e900e4020b040f0000c48101e07110509081032b070ba10152a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 97438408 1250 97437158 97437163
    0x303041505131806081c05090d080c060901050702060109060f05090403050d110915040509131a25020606010c03030b0402070206030a050f0609071b0c0909060603030206060a120f0302 80
    0x2c2d00f10103002520380081544401c9554070510840f50024200c0d4410b580c0303030002400500c030140000d0001541000a040582040c4002c2c24001c0d219410403403804881d5242d00342040700903180b005299464030700303001c82241e0400c85540074102d500300411407145003205204c0408450b106090160102030001810b00d80581c0c00d490b00784868003024004804580005800c60384000c219034440c85400d180d448004519a064506035440030b848100300752144440ca0307501c4060f0a000310f6081541da48044003450b2814256030003030790340040301c4192a030000060a40c000110203e10b08640c8540100090703030381d000720b03080303d010742504000804050020225019105051010b900054004140a00380da8240d01a5128068255a800c0c51791641d40c00c10042d0304c0b060b01c0c207030009804899484a04404100c240500602c2580d1070760445940d0a1410183c0c1ca000300b0a9070b06a44c1c8407020018580c06101c070f039034050011990300702d005003400c0414940040c403000203805002908000e10405008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 97439658 1250 97438408 97438447
    0xf19060b010c082214060301030605040501090f0b01080607050a0e010e12030a08041b06022107020a08030a0306061812050a020a0e100501080c1209070302121005060303041505 77
    0x410f0b181580d680c10707402ca0031102000070020800c1c1c00314000b00003409104010100900420050480c0e04d16440d503100c84004d008043e100751081d5684c1d80c9840f0004416003070011400d846450441c4a07580344c10304641c1006801081c56003803000400a9122099110401800e02242400d01c400a01c22002c0460340c003088082c10000140b100040d61598a46c00840b02c41c402c920a000b800405082071512551107492440303400c0c050385c4080c60700c0d5000030450518040340c00b82d020009041c1001e6030006142403000e58082802ca0f000051509441075150203950080c050074107010b071b00f01701076500070303200725110f44628000d01281482d079604104007801314101c0340350001e00c010f0500741c0303480380304480070000d84040242c402d0101000030b841d4050031915100d00580000c060504030504d0f2100c0007034100401011181c0198000840143d40d061030206034190010000c1505030304404c8000122171014004502ca0340c810700040000c204600310074545031180340b42803501c4254400a04594858 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 97440908 1250 97439658 97439663
    0xc020d0c0e090c030c0604050f06071403180316030308070f021006080106051c11090c070606081c0c080f0f1306030b0f0d0c09050601020a05120703020f19060b010c 72
    0x10400c082c4110312000140042c1e00800803001d8648012003541000f105104074032031550011794a800180c3c0c945405030141c07072024020f412905a056040d100c2c682143d000403080d040c0b0300b0013681c601c0c070181820440d82130760074070b01d040f0b05800790f00719113028081200007001c031000c125005243c0104144280400c166611103040140702c0103465151280c00381181d0700419006100441c500d52403a54040c0d03851440b1a084886a10903c015506200e50381c080100403440c8883c0c00c202840c000754007807003400700424000000d4611243c1108010301c8480c041800c00c400c121501d845240481c61980403100f070440a80c040c1aa00c0c000460700c21a14010490210040c5401850002d486900350300003044188003201d182015408070020400d203148043d102a02c01240c3c14420312020419501003600024140100c404c40307001c0e0b9455524111142d40c00d0807000401050400405404001c4c08210341c403040e024001c070544062550318200f007404000b42c40c850711626000c020b0703401904103419094 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 97442158 1250 97440908 97440929
    0x1206061b030301140910030b131103031207030b030705180a0b0d03020a03030c210c03020409061e05030106050102190f0b0901090c090e0d0804020f06030f012102010c020d0c 76
    0x42e914800c2c1d07040c4104800c0da0a00171803e1200041c0441c0c070203422201600e81c0128510290317120003813007051401034402d044600300101413a202c095a001c0000e400390042d10307200d074072040c5003014005050303988803901c070b601903800290240503a507526040d003207100800c403400003002c3c1e036900000310241c0707240c28613580c0040010904105055022640a5040e800398071309200c030401007001185d000c030713a88007000c4811111181000c0080484d40080c91981001c0c40c016041944a00e100e1003241c0d040e50107943c945003120340c00140d6400301c0404200621007100208106c500c3d040c0082e4031030880503c0c0007a0014080030550800000c5044c00309080c3d00010818107514011800c3e60003020842010f40300045080d01c0004d40025038010900704002c002c01520800e0000801035800c11009030040b0381c044406090380d0f00c15101c0c440614400c032480c241d1040a945003000ca0b1724000c00c203103045942c1d01e81090300c00d00980d800074025030007164160f9046124007803909101107031009a80001045a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 97443408 1250 97442158 97442161
    0x60c060603072106360318060912030909050c180405010501080c07060204120602030612010b1f12050717090304030803130f15050a06080c10030e07091401030b010b1206061b0303 78
    0x70018141001380d45c9129445120486a0540b4190951511417280c0c0300090a010000c3c0400403440d54042406482030400c600801d848101c413405a03001140d0408801c0000704a000070103d41003c55008507600740c808105550604000030100c40c001814100d0b0b568002440000b0080c01d40e044070014010f0b00038560494405140007000380d441a1159032003551078800d0b20386c2421042c82820340c544c0b8000d10b0b000c85807900c2091055000c0510b15820b00303000d000022501d9003640c2703000e064032612403940c800c44810700d6518410751411028002510aa1041c4010f00014045000316a002a4400d21088040240e407500f07440300702c80360b6001451180c1a18010712055410380042e406003580c281c0a00046440e01a1141c0c1d80d002d21042550003401588091060f41c020703844002a0300000060b0342e240c81d1120729510907038400c0718200429260500040041c040420141c501404d03e03900c8603440d10050500000748685c0140c1a144038460004075040c04a0300105c4100703180b90401e055946a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 97444658 1250 97443408 97443491
    0xb0c070306140106080105041a0906030312011403060705180d0809040c120509191b03020607030c03080c0304151a12030309061b0304060506060702060c060603072106 73
    0x4070300207200b04c2010501c1c540001c40c0d68a0f0074010b000078240030240c2440400d244400b00128802c001e04080e400d8001000361032202d1381c00e001454041c049500b0040c2c945000c500a0500c0c19800400700303410014240682c20500c03005840c00b40255100300c0d90705d0507118543c206a0a80c2c0f0445400650051500076080c0a4a030420109000460b507404100440d607510300c03c0d261600d0140da00c5416141c2a8801d041c000b980701c4001401074164122205502c41d1240c1c080f625039400306100f80c1c0424561303d6100b0805a002581e40c1e401603040e040769055042c50b50301c40d01c40008011050340c400d0b0b144c5034900c150384c944d8042c54401d82c0000307012400250311140150748030740c030648012415024120001d04000044d003198101800310040040c40c41da1280c42d07a20007400301a04065111400300b120a0160366010b014001030013815019044a003001d0f800c061911440d64800540e00f46205aa018200c060031194501d45030411004036040140440d1900c1c10504010140c03410710038060103180d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 97445908 1250 97444658 97444691
    0x1e06081507020721150209010e150405150304060f0902010c1425240801030209040c050d080c0c0d02130e01020c070b0a0909051303030c0e030a0b100611070b0c070306 73
    0x8000e1700500642d40d9003405180c0c40e00a900c200d070086404110711510811706820048100c1c11110209440d0b50b0600b9103900005140020b0300c0000c04a441000c0180703c02d100c82881003074103c03c4004410019540c43c0e80c0040c04016011030b001d401144418504a20440140041c803800800f0041c0400c42070100034144401d215203005091100c48020550209214402004144030000340c03500041c6a203194200190302400410440d10032251081c0060075469014651803494800d25015886019455241e403500f0704190095200e0784440700c400d03015841e00034014407650560400032440f0714841d01503c0c0640f10b03141146071144203904002810b480740c40090300c208640703503940e07030000b60b40e0368440010340d80e054909140098655204000181c025404500155090704010125241d21000a0304107188c2d48800d498050030341c02000710300c0041d031b5a0341d4082c08203820010701d2000c540441a0340e40000340500e13460103400044007942c04100304900c500442d80080f040c00f9005581c030b0a0300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 97447158 1250 97445908 97445969
    0x1e03030106030614030c120a060c0504051e010806060a0201090b0406061a04030c0b0315040e06010603050c0708040302120c031f0c030b0102190204020408030c011e060815070207 78
    0xc002918011010818480c01c4e041c0901d6040700400605c171580d52042003041d0302103900c80e0070185205800003200011260f000301425488140c64042d1143d1614061000c01d1074500c03080c200b15010784034034007003c3c3e812040503508042c0503140c0d180c81d0341d92144264014021450003600d002291f000300020451070340c000c3c40607104071f280c401000304048250f80710240160b000040c08051185030903c520814400a194007041c0b004031244d40450f80e0010074221146040c2849154109000521015815015103600204456402c1d481c010031a12984814042d5010080c0b00c1c540c24260390000c11820821620829001016a042e02002d00410410301507240c42c10000a4101191a94800d0103849213410441041c0c02030a205d90030844e080700c40400b03040040740d10643c01d01c030200d0481341c100701401c031605800e40002640c03408500b0004103000c01b44e4504032805e080038030a0080820101340b0a0b00c008204061001c56160b00030180d003004039681100c2c0f022400c05000c40c80d0b0120b0400d010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 97448408 1250 97447158 97447169
    0x1020c090601020a150b0a03110f090c0415050d02030a0e0106060516020609041b02060912030f0403030b040f020409090501050c07080f0d0906180317090712021210060627060804051e030301 83
    0x80050452b40d02c10b1042038442100c1140300b1000920080103500c040a034040b20388002450410b20344225811a01d089800071745084c114183e403120b1041403003100344101030141c01c03181031041c02c2200030340725010001400c09009001d50382c04100d001860301d59070400182c804c1809240071814a1a00000355a03400458504809200d00c0c074181c3d000750000c60441c0c0c014403c41140c0b0100303941e591020340141070071401d0150803070798404600e601d411041c4050701c0070381a82000880d007844281071850950300040c00744c000d041c400f0000f0348001402c000031211003807240780d059922001c1a00303000004004103400580701c1d600f0b20003102c0a4070070690410656501c03a0301d803c600040711000b5004070350811074402102d03900000f8181306800d031342903503810396510050000c11500b1307130701c21850f0901454100c0000c400392640000c1c05410b42111110618204520080940d03415040000d50310340c445214400c00d0000c0340012905010051110303150312403d80700c04440c07000c0c200c50301541d00e0b0303c01d1085 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 97449658 1250 97448408 97448419
    0x6050a052e0507021504050f28080304060f08010506180d0611070308010b070b04031b0203010f020a030507050f0403060f0e060f0402010e06040e0c030a06150e01020c090601020a150b0a0311 83
    0x40c0705d040c0103001950242c070405021040c5441c180300502c1800c00700240014501c0c1404a51205013138141c0412001802d45100a191a0b519089000c2c0c5500c4204210105001508005008684640c015201c54418415014094504100101e10141840c2d80080c1c080c03424400d9181400c280380000700180d0b03129a480c0e1075203a07a101c00d01081030141220003070100d501003000c100420300c1554042203040c1d03c29820800e02072136034006401c540c106a01000525004035011b100241c0510660303621803513500344586130030450400110148124000100034950310740505603a004207034001e4500240300400c4550318101070942d6121000111022400100c01c1244100c560802c4010b68003180d481c240c0480346030f01c5000c1122510f82004040002c8580d0b1071400090445403221070228444050300d400002034004000207003010844030704d05000b94a100d081c131000d40d9001445d0324040d074016041c1c60225040442d400090310404c41400e90103400d03901c000c028004001110200c40c07404031034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 97450908 1250 97449658 97449679
    0x4141209010f090302010c021207090c0810050d0503030a05091608012906072306040321050403080a0f0b090c0d0609061202010807020f15040506090106050a052e050702 74
    0xb0308072111410b07400028005407000309a10018203141c0f412003010f60340c100a6a0f0800d8440d0807100440d481482aa8001104601802010701a9061120140c201900c0552540c0d6454403020741e41e1001600000655a592000030340c0000140038000d5500548c50094001c0c07039480c0c030010701801489501e09600b00d901c04080c00110304e0341c01408c0620001820b07803414280f064407408103004a001e500301c0045a90304280007200b070305009181c4143c0c407903200c50501c81e0319404240ca000c143c103c0505d1015240c0010301c40401d8000b540305034041c65544001c2242c200300c00188018007090387d240c0b90400c1c80b120600030b0003000480034140c1c05804a40400c18965600d205c1c4003a12610300c605044840b480003494055442023202d02d900804a004652045035a40031051401940002e03a5080443c00024401040400e001194000081100031f01401c1d040a0004250b050144500ca11070a400c00302188d00d604801d0319185044585407450304080c034145130243c56a40800001ca105900072a03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 97452158 1250 97450908 97450937
    0x30b1003140709050102100c090e040f1e020603040b0601020307020307030303020c0c0609280f0602071a03060f06030a0f0f2310062a03120c1103120414120901 70
    0x3c3c1020446005034000c107032101140f12490010f00502c0802030811000303500100c3d41810700c0890500072441006c18040c4808039041c00c082d088841340009400d04031034005a0056039410741540c2d0441c0c1c02c05606411916450300503803440c4220302c0e0003905409510400070030701d90103501a21300c102864081d609614100c0041100c903104451150780c3c44669200240d0365628480c28286411003100c05002c440c030f032581c51280302c0b42841c0d80b0031001070b4003101d014403070100088180c24034680078440480c21814664005129804801d0742c260140c8008400200c02c401c06410083c015a5005410030864107649014406045182c90418204420700d002075050090a0346c1c29108500b02e90400071001e0030300c0403c0310460550141e06026035500840d1801d510b0045242e82910f5200c1d4481003a8064680b81107801d4070b00da402c04005000d55014170034041c000100403503d5510b07000e8030458245e80c580c603000e0405800c2d51032605042c8100041d00380140012001007005142c240c0341c0400061800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 97453408 1250 97452158 97452167
    0x801120206030a11070f0602040906050103020f16050c191a03010303080705070302010b0604090b040b0609030309132a091a07030c0510110d0e0604080316030b10031407 74
    0x46000075040141000090742c041c3e65035010f0101d1640b5605050f1800d003042c0c662500102c1c200d030043d29210350000d81046460150721032000104020300f020740c240203040c02e014803103010f00307800352903503001410108040200a000010700404005c040321034081c4000f981860403000c50050b0b02c0c010750071250f036440a40c800f0040c1c0e4100d070340c1030b9682030465582c0c290443c2c05811681c030850943d034882c1142e106a65440300030b000500502d078800200d5503d41401c11007558190246036010300e03000c000500c0319440120440308070740d4040d41d140070020030205a040003400f60100003490340054074202e070024108402c00020009070b996442d064944c0300d13419030100c50140c07020301e0040c3e01c00700f1200c400a80220100c038100740c06082640c5000f1407a03102003040d112101490514588000744421403110240309405203d00c00400506c440e2800d552001070030310029203a4401040d1102d081d400107846500070381c04810010f007040d584545608005400341080400b0890403d035114001100c05208 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 97454658 1250 97453408 97453439
    0x1e010201050603120a1b0204050406020909100602060c09130509030403021003020a02070608060d0605010b03010609120203070e0402030a050106120606150212030702031b030a1416150612050105070801 88
    0x1d03d000d842c170f070440310070003a0740c01c00070240082202d200d4144004090790340c0384100c85c49240103a40241e0b9440c100c404002907504010010449840c001d0401c0c00115400a1501d074003009102c801541d481210380000c0301c1c05060a2800440b9040404100e51880017002800480748241c440a031000c0e103109080e42030340a00d00c0c1150040c0e220b408200070040c4140c01c19a0405000b0f0200c054100f0f4030340301d503070070365009802c200d0301704c04000300402109501c40380d075000a0085040d030a90728010399001a84070620f40c4520424100b280b0045030540d42c050004060095021008101c510b56814114003603101421058550078640300700003400820800d000c2416114a9001d405006c4007190300540c142c001074000002c6120900501c40c2842c00c501001080c5c1e40c0e440011038549a05540081011030300d1500c3c0c41b19200188402d00c0e456060369554100b155110b15554041c559140b2008010704d0350360300880c0c1c26030401d59414207114065001900034800796550030030907070703e031f2802e05c040a19 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 97455908 1250 97454658 97454683
    0x7090321020607110c210f0a0b0705040b0f0705010212090703020109150c0b040c080a0c050907050f0d09150612020301050106081302060d0b030a03120e0109020109050103050601030b1e010201050603 87
    0x35100c5c098052a10b440306102040780040c203071083e0f0721040701c01803034550081d074004900c0d440300f0464028400645030940d0b000703d1628029152508184520090380201d1202d51420340c004540001005800c2d0180c0d5513090b224803c1001c1c5c0d141032000b0566900c0d2a00c0140d001c102a40c001042205408000307403072014464440c0303008102d080d41c6507070340d108000340150707840394088601080c58075041c0010100c86010345001c00d166401d000c2041002d5901401c00750a10400708032280080b0000010b5074040403190300000b810007541d00300007008001101d20b140246262110108003944140c41c034481d007900a8000300407503a00d4030420349a44d842a544610480b41400080bc0103150003c010040940380000c08900c94a81101080c038014003c0780c21004105601c028043d001c816104075066070041c1c030000d00c0365202c0d60b00043d000724070b503001c1c0504240d164000100030b40d0086d04101030031440500a0700320162182e210122101d00e110a950040d401c20f070114407a840c000448002c082c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 97457158 1250 97455908 97455913
    0x3060614070308060409050609010903080f0402090105091003050706030203091603081e07050304060f020d080421030212090102130501081510020a08120f010b130e0709032102060711 80
    0x6299440544040320011300c0c1943c81511504840d0001c4c0041c0082c41c0210341c03070000030a58200c20700c0e01400e900c0c0c00804603800c0d07038555010400540c0e120403a10303044801c252090310f0b40352116040c001000300f040c1c00140c110301c04c004000407030310360560083d8803841c040c0069440700321034110705800d0140a440301500105090104600b0f0b041200148545074030071854940c900042d42d5a0702c0c1c01c640099000201040c0d20381100c622444e014040c4901e121818a0803036000d00d0035a503a20301005016920340190034001406510042c0a81c1c120b8007148915085042d281ca0701030300f014042d5003c8001042c085402d00000180d0354019520070b0f003e0081d00050740040d1102806002504680e95544811803041c8000840030481e44001401c81c0403410003002a81d2500254004200e0010390022030032050801603d140044d42c000402e080d2080d8649852003510b6000c401c94001405800140103003040010318100100c4050b212000e82200340c095a80701c1c1c3d182070003074070b003c07a2007180c02c1100e4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 97458408 1250 97457158 97457167
    0x20c0f031506060c010b0307080c011e0203030f0618090d0f14030a0b0607020d0602071110081f1d1801110403111302030103060902130e030a080c0705160603060614 72
    0x525040000d08451340700c96000044c00b8688800203031030b004856111081d81d800a407100c0b03080303503408018800b5043c0d049010754903003c090780c0000c1da01d00c001028083c090100c0d4000c1a4031ba520145100720b000d801d45000d00003030a02070040c0b40c940c4940c1e50064040b40c0300c4505141c1c0e05000d005c0c110701b50703015040f000f810741c0d82d89007541000d08040c00d1210361140041001c01e0042e0745905444002d00d004120058480240c1d00d8800b44440402941c0c0344521120041d2003681d650050030380d6400f800030343c1040911032898020800030202604101e0441100504110b80059043d407014490203140c0d94020b85900d5506583d4201c401030001800b80320400c11050001c0b0f401c03400840342e050030103401a0742c011030310301c810812a0000e0704122032303181e10744000c07600750b1403c640c6c44000031146030810422107a468886c250740307100320420441881000b000103030f082440c501c01da40c6505d422030f00303035181c0103083c10905c03011080900482c00420b00c0d105000c00e550784110100301002068a107680d02c0d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 97459658 1250 97458408 97458421
    0x522051008100305010e0a062d0b0a09022b050105010903080309250501230301051903020618090106020c030a0b0604021606020406030c0c050d050309120a020c0f0315 73
    0x100d100c001d080b403021020404001002880c03d108002803a041078024050503a01c03443c000b8180c0c0e01c0e840310784052400450200e001824003102410b0700c200170b8000003600d0340e5100c010594040c21a4409010240b001c42c5180200940c80c1c401c80c010312090311400c403140b000151500442d1740c280980c80c00a00c00450a1000850710802103810038003100403036540090092007401c500f0312202a0f09807030389138848108007650b0085212380990720100386207135203003030b9640298040d13000512840341705090b0290014071080441d00c10f0409980c014091544c2c50a40202281501c2a003503005400341000400024200d44086000341d1001ca0040241020650648800c00c8048018002940c0580d00f0000400d099510103d0113a100703124010141cec50380d20b03050014007120120319101040c042d1401000303000a40c04500c51a01004078200300c1e0b00c035220340315a1454032429001000c40e000000610544041d000143c140900100b201c0e0244280700c24018140c441d290002d1300c440416204001c60340c0f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 97460908 1250 97459658 97459667
    0x160509090d050a0903051209040501140d080a03060302060412020f090106020a060c140703080109060b07050c2709060a0506040c0f140c030706060510020106050102031c021905220510 80
    0x10f079000d003440c2050426483e901d40074280740300201d00300f40701d900000d09107038581050b01130303240140412040c2c0030042c04036401003a604902d038100280500b03000501c0d1841d0382c1c000c1c0c0c0a0405103030080c204603100c1d0781700c4030840c0c01d20b1b0601c501070748248400050290649020740c0c1031410380740c2940c007418010b6200d944010142100100b81020700040184041201c40c000c0c4c05440d2803802680c65400c15450400c0e90341c2182c07820f40156180b810100080d0b40481d00014850705506026a4142e84a050081d0300c080c00c50b800b6110b031644071070842c05203d584a030001e0614051300780f50404102310b8442104110817200d21a50450115035184c0c103002c2e41038010040546181203d0009030b1400d01d45d0b0340c4a40c21079100c1001210141c1c2d40b0803040c015810064a025161a5640000c000203410b010010350389004071000310442c2c0e01c010030385140850403901517503144001c03c4455001c40e006c50b4130203030031508441349421440030003d2045e0b029090b0701803150100d48026000f810910715182003200c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 97462158 1250 97460908 97460917
    0xa0e040b09101206020f0304030c1a06060702012106080a030e010201060e0c09120d020a0b1b1b030415050703020607031509111b0106030209010e0702030405010c021c05160509090d05 80
    0x1100e1617803d02c40342c102030b40000300640c0315501c256107060f05400145000000340d17440484508011240c03104000382602d0f400708688400f03409080c00d810342103003505151000c41c0002800c860070340c240303c80080c00709000180428051301c203840c2c4040034840180124200d902c544503070302288100c0070104126071440c0008144460016100045140038069018904144001091700603070010300c415050001c0c1401064100c83d50b02c05401c01101919003103e00d501448000c00c800c0000f503000303000c80e01d2042084030010108003003002401d0091000182c500e80081e0815800f43c0600ca00150320030f84240314070240304460042403140c0301d0910061100400132a10b038400042010040d24007082011150080000740072400407801601314414451000b01c180d103d64011050710051111054003c015603054880c2887c3c5513000d5003107800000c80307010002003800b40c1141c031083e00340f0074403002040f00411000c003c0796010840e551042400700d082012100400b29821200814501610400060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 97463408 1250 97462158 97462163
    0x30703080910021c0c0f0215030a0c090b0702040b010219030c03031103040510020d020702041a040e060906131703160801080a030203030c07030e0901090204030302060a0209032e020a0e040b091012 86
    0xc0306c040040d41c0450a401032004031074a4403440481040368851507170059045031045494a80c1e00d0524140c0782180600a80030000d00c070f59110740d44009641d100300b04841c0c800603520b4180c070a40d05d4908010b130541801c00e5050300081d0821300c0ca9451140d041045900865010000b03003040c45090034104000d4228403192111030743c08001c0000943d945010b0802c1e0300c09100052040b01121008110803074590300306814098200008004441c8004902a5030200007c0424444101145002854900c0540c101500d414011050050100c03020f0f0740c01d0609252074850840302d9885440007036030342070b0b141c100130b005038002c100242d201e40400c800360820301e00c01d050a0800d045520300090000401340c0101c044240d001c1000c10505504000c5543c0000d985a4118502181100466190300180c07480099212040c040555100458140c01e140d04801c081c04540310441c0c444002c001c2c203a50030403248114141180c591107854a40d2040d4010340041d00c1604883e442c11041665000d0700380000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 97464658 1250 97463408 97463423
    0x90e06031e010b030f1005060906061b0304031a0718080d05090d1202150601050301050604030204020313050613050f0102030903120a0204080d0c03030e0c060a030e010605030703080910021c0c 84
    0xf018164a040041401c940301403800b90541c0f21841081008442000704614170484965040c1b191540780c85080318040713580c8030685201c4d0350724400305a1940c42a03900003005c040c2a0061a8030a5034a141c00300d0140e46103544102e4a00a1102d80c50880d1200d402480c000f500709900b04066217020344010030403018060003141d444011a103803c4110380c906681d043c0582c00540c1300b8280b4001c0c803031100d40d1016090920034115410a004590b07a402103000007405698000085410790503d200981e10499200080392140d1510000d15450303008800d40072903031442140282d201d400030600070b6a104103001401181491121030011101c00f2014107a10255582040b002c500038406000f00500c0406644540b444c0c43c3c094a001012665001d81c003500f01c0d0805a68103c43d07660b8034040300d941c0c150340c1c5000308206144058890060540b03501c07066051243d84400001c21601d00041c1c030303030100120340021a00d21064800d030f0700c2e507a0010317800700510305c0700c1c01204805014032000059540103500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 97465908 1250 97464658 97464671
    0x10e0102070810060303081003150c120905030c0708010207150908070c0803090108010501051201051e0d1202010e0303091f090b0a05060a06030902180c1201120201090e06031e01 78
    0xc60b40c01e01014062000301030382c54820520030b064221042030b4002109a056122591650f00c80c0521000b01c40009030309107442d100501482846000d8440304030011080c00c000c200e855107400e99a80c0c1c080314001449005503c030004d50064180b0940e62a240c2020200c0018140d0011001c0186a40e038030403580d030101440300901003811071000c00d000d0030240000f5540c89512100142031844140e00540c1000b804010204000c0340410750030707045070010b580000c16500040e601b400a1a00700d900c0907000185000e41409010000b10034040d1004260001c02203803030040c1c0314584070310080340c090307a080c0d0091481000e4241901881c514040000500140b2a04a84e0b150000c000040d41c050481caa203070000e00c8076a01d82000c90340010300343c4d03080c204903c0c1055804581c10b100015002c0d481480c41c040062000c0c5420011141901c0706c404a6003000d40e11401c00c0b1401d581030900c180e00103143c1800100300700010f03d1055001d14002130050034071110f04070340c000c41507281040340d842a54903001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 97467158 1250 97465908 97465919
    0x40b0604080303160e09090a1209090c120c05030105100c0302190b04030809060129070206030103051608060112060914190201030e15010302060d02160303090b0708060f010e010207 79
    0x101841c003803031400180c241c211381c0c103e4000f80202d8500c4102403150042c0400c0c0b02004500150030032a00e54080c0c04422514540300c0c081d18003035419880b00b048a8101000c5440701940701c41407242a40d1004400c110f03890034800112400e020074000e10390041045048200041e020f0b40341200483c0c881e00c12504400102d80c0b42d03800380748490404560861018040c0300805400411195106014800405c0c40d5850180354940810b4080962002c0074221019008903210500c00c6481040d00a803040d580d951f524038000c0d40d00c040045006241c042c100394003040030040480c1e41c0c2e0407900c004850385d03903800031a1104001094410f030101c40c01c0300c0c0001000b40112040c0310a009208074007034101d0790382d001c6000160542e040302a443c1a660018803084030395250701d00c10281502e07010780303142e81c49014489100c0300921802d0340011824014031103200406a154004445c1070788500015800c40d254510700b521208010f07940070358400441e41c402211540701d5512010341c001d05204441441d656034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 97468408 1250 97467158 97467163
    0x302012003160c0806060103110306120a06020a180902040503030414040f05070801080f0304080d08061201060801020a09050d02090613020d05090c010e010915050a14180316060509040b060408 84
    0x280040310070054502013004582e0043c0b0405a102d40203080030321828003103088441c4d551200410491140700f50603a9605121420001504030340d6211a00710341e52111800c0c040c0c2580c000a03041480404407500104007880c1d203000703070f0342200c0002c1e000710b05240c140503001c43c504085451103504184d45680281ca002c81c54043c150040415481c1e007507103035052191060421014180c070384515402000200034030031380090308811251750303840c00d8007031a11804c0000d40c02c2c2ca400b5681d20491f40c03c022022400c40812f5008154003c643d45610440751303607407002c0c0110121140700c080d600070180c500158060034015041c0d403481c5c3d84000010303d0304121000c441c0c1224001c2e02c480d10294403400c019040d950b00901c102503100c1003420288a414500000d02d6603041c040c1c0d0304041089404501c015400f4007412a60580c0303503402c01419100c0329400d402c030410350f0f0325104841c480d2060714131540240584202000c01e41d042c0703a40300340c0340c910040140400707030084010203034200d081004000780c0003009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 97469658 1250 97468408 97468447
    0x60109050c0702030a24090f02040905011103010609081e100b0411040303020102071b03021c050c0a0605030708010b0301060e010c14070f08060601050f0307030b030c1512010f0302012003 82
    0x6445949007100c0c43e489000e004c046d4607440c2824041c6030040100c0466441e0031840781580c1d04880c042041600c900d0000e01400f1046145801c0381c1002c4004a03c2d503030007008840a607129003089441c82908030409060810524040c1e00950b04946090b5500400c583c01c10321411001a2004c41d041065602911440c1e00c281d00a40040c0d5012502d04100031220001c6013900a002610300b018a0840d00002c00180c425091140000d14840c6007404010052004a814900082a03500115595240580340e5407080710001c0028107900000706104490600b83ea05a031201d5884841000d007413001581c030b1461104d02500c07148034816071102c241100700300c181d0140503006aa0b804152605840070300d0400040c100c00d05118050010f1403007082248203581c0d1000040ca00800c006482e00c2c08a030401c42c4030a1855006a0a03644c002c0340c0603101c50041c4550703030421540308800c0c5c0c3d880e03140c100c02000d240002400030366042d07081c0384240c814114904400c000c0d082640c2c5042c440010046c1c0b040f02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 97470908 1250 97469658 97469663
    0xa0e0702120a0509040513050606060a0e090a02070201030b0405010e01060e0109030c3f031d15180301110301271a0909161509080604060501030b0711060109050c0702030a 75
    0x82c0068441342d43c2c140ba0003244c0d08008071386089424940b00b580c42c5912640c00424040c0140004125500081c0c41654003507943c845c058058001401c0850040010390702925043c3e0120381015001d02490030103214030350403079402a440c103040d41d0030040222404403210781181e041106401011012991810403000109141014404084080b989241001161800d0002200b20284100e2440e201440c0c1802c1d441e43d140c5060b103070700507401e00803c00700c14040302a640c0124400e4268404004800d000308000d0b01600005483c01e254007081500761400d00101112117402840100280d55091800d8451500009800306090030400c0503081212000a1403646843caa2020920a400e00c1c0000540014912010b003800328060040b140281040b481a0841c0310500001280c2292207001c068015000304030a0319190b0030b02e4184100a0700c001e003c1500e05940d0240407602503405006500c9814124901030b00c0e50707a18100c10350004002c004c10109891034200140c4006913001d100d40080c240c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 97472158 1250 97470908 97470917
    0xc1207050c03070605091c020319080a1424042306010903050a0f231c03020f040603020301090e071214071505030703060605090102031e04090615021203060a0e0702120a 74
    0x6100c05680fa10581c1007ca04005542080002107828004c0d00b1600c0071512103030800310001c0e140c202e5030200406103400c0d202032200700002440b034103004848034445482e4048811401101100e0304000c1160403040c0e86a40d040c0f0100102000401201e80940e4050014180486070075507a4403102e0510713044100445005c2800b110a9003004516030340751141c0300542e1208a107070000503a00559032640e505911224500340c0e03d0140341c1d20303c0790301101c6c1540300c09120140c543d40e480a015001c0d400a01031540d1440c01c1c40c1e590300a034030001034000c0480d510045807035001390706070300c4d100310034031140300c0038125400303401c0c004210900c0314a581c140c01c40303699503001d982b440c0043c001400c42b2443d400c040b003008030030400320321103a0b8000309481d0068144603031000030150061212820388983d522074040c90782030074000a06001451035420a07081c0a40a4030750b9041207174607003c62440102c8159902c02070807278051005039035140019520803204d00440b0f6403444002e100d4075843c2c00c401141d80004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 97473408 1250 97472158 97472173
    0x90f03030e1804140d0201091112121602030106120206121506040303081806040c05060c010e06010f0f0803030105150d1e0501090c09030807031b1203050f0c1207050c0307060509 78
    0x140130401035009000380c01c0c802046203031459640c075a0030321324203406c0c5403084942c07100c5050555424488155036078062021581d40f150310001083c04246140401e9100f03510308480010081c0000c011406200d0303005240c42e103418100c0480c030440c1a4040c004101d1307118a40007680036911610001c00246000ea10303005032a181a0110745801440c08084189540102060000003080500b101042d500c0440790240c6400026240500401240003040090b200301d030000a44854200010400d0f43e0340c46032040380260321b600d0306030740c3c4c2d00c002e103d041d8110350340d280c00200c0011402c0c00707010807071b01001020800b030300054030301a4414540700d0004001e554820040140d180c1a10540c070b0328070400e0800340b260900c0c54a4890301c7d40200314000e400d200c1200c0c40c15886517440d2000e840c00c10b600601202007030441800041c0180811620301134081880e4002c164151262819100165038081840c041c564440c8001c85407030308403002000c0e242c8028805130000441e140290b500c600c80c03500091415 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 97474658 1250 97473408 97473443
    0x8040b03010603090639110601030b0406110a0e060906090d0c090f0c020c1009030b0702010207030906050f0702040c230d06060c08030708040309050901031101020706090f03030e1804 80
    0x7220070a03654000b5031310b4204026025240642c6006c05400006030469100d8000d551040c3c40752589021010403d019071030001c410081030480c0307540218002c1004101c1000c1c42910410b9a2286656400110b140914040f0380d03807400100604900d90302909440c01d2410311000304a0b600280d0380203c40c8507541c0d032014020507c251254000400c00b0303e07401c0c040d692000e4400707515000302c68440c5004182d100c61400680b070281088200450f40034807912014034110303400a00075042000224009800300000040e07041c424010380794107004d084540c514124003542008000d02c4490212400c1c041d401070540c0060b241c5042d14090300708400c403180d40d500300540e01c2d8000c880c0103400030010300103c04a92804540b185081d80d500c0b009a0501a08039203c40c00c0540c0d5070242e03607003ea80e00c228440c00110800205007c50140c202c001e0302150034144d10340105956a2000d03001e40580c0c160007070f10400100e0300c07802180401c680b01808007800d4040da1910a03010b12412241504e03a81e80110200c1903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 97475908 1250 97474658 97474661
    0x1a07020c0105040b040504090c050907110606030a1101050a090e0703020a020c15040b0307090e040c0302040c080103051b120f070e01090203040221010b0307060f09090203090601050d08040b030106030906 89
    0xc4200003441c01c82e140ca03060800c80d07503050141340a668015642e0f0882d4a0411880041400c040d0170020f002600350714046100400c0c0740d0b440188019540a908082503107410f0004204a6943c2d000300e844121251300790045a040d0401e103407031010000c0520000643c401c252034100d008000c980c1d40580c0d82c00344440041d1030700f0400003190303014003000d2003070159804000d41aa4192003c0340c9010750380c0e40f10034200300c0b803103038080d000510740031200e005010410110b401e070343d0202c80c801d550500070449420b50942c0d440034240b001a0194020401483d04200407038558400400000d09050b041131101c01180c2ca003400b422001c0f1490750102205101d60080d042d8403500400c2054415031a40c546580810003092641608070031102c51000e00760030410342900070008100010b402c458907a9a589802001d002c0d4589401c00458654440410404428021244240020801042543d1034076051240c035926550342070b0b80c0e0403414000841e800007003000541c001c049030754010480581c0b5003065030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 97477158 1250 97475908 97475923
    0xe01090602070b071106071a0a050a02030f0a0c02160e0a06051203040b030406110c0109020405060d0209061e1905010306211b0b04090501031a070c140a1a0702 70
    0x40d0342c0840c03800c1169180c91001c481c102988080d02c9202000c0080105145008545005244512001c9044400695174110510444900d2028803070740e2162141701c000ca103c103654100410001d00006070580d812608032a00c0018680b04407003002c003150219440c0c54410390894803c40880302c050003940c81603401a140a402c00b141d450420f060105080e6580e0311440c4113130307490792601000040500c0300c260302c180071030300081d1165640d902c0c0d12203c450082100003412031150f85020f0102e4400d0504500340345103164040c4c405149511800100046000004500d034000c3c01940d1110354103848030660280d10190419164080382c0c1010000b402383c03401c6402c11002c0021440c2001c1c8184c030441e4402039611f800030740300034001884000001920704c440d00111100080001c000a6a0816901041c120b83c01082d40001006005402003010101a5600307400603000c520f00002003001c07146440d80c0210241e0031140c1d100280c1d610540351500150902c2c41140c2c05204210fa80c0750144401c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 97478408 1250 97477158 97477169
    0x60506040b130c030b10050a090806100506030a0e0f060106021207020114090103060306020f0904050c0705060711010b040c1706040501230103020708160311030408030703030b040216030e0109 84
    0x144821091640030854201c4085000740c00c03030f5203a004801d1980e00030307400101c150b1400352502840f41803103013000c0e1040d84940c80480004020304400070f103018000c21084d000e03e01102521101900d00820440e460304003a00b45010256210984103000604220980008035007101602e5158500b0102030f040c821000c081c010004410880540103030b0380326545e0002a01c0001c041071b112405003004030018282ca82005103d24800142c0307650300c400b08070142c201003204407020f000035525401c0003800e601403405c00812591211300840d0406001d80b00d00200408200e00000c2c1030080000014180c61200700c0e4080411404520b070041c0f0002d564203150f001d402503c06200d2545803058140b480e00c9010499100030f0451042c0da140e503071281c0c048031841d640054101c0e0700c401c0300050710022540402000c50100c2d1003a50014035451010050f10121341010010b0342c01c00415880a5010300707010350001c3d502c103031708100b00134000e80c02c5c2801c03510303c9001e90342e0030220680701c400142c03011070181c02c00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 97479658 1250 97478408 97478411
    0x50f010614090103020c0c0d050f0d2105041a1303080a0905060a110417060609090a0b01030f020d081b01050c1201030809010201060b04090219050c0a0b09071a0706050604 75
    0x594071403680d400440d824000d0030328006070780b0b40c07184140d607040811380240c41d980031610056000a000001844c2003000ca4074100340d075081c4901c0442699520203141011420680040d02840c5242856104591003401540b0346520704d0075100410b030711907900311548000301c20400c81e2031087c140d008038843d0744455407810030001c41c405905c1da950b80b04001030040703e44a855101d403403079000849054800070302c03460b070070340031802e907814410790b203900701122501e010b07120520006030340001c0060060b0911740c000e00c3e03560459096031600e61510350840b00603608901701108010010309440c00509008681d424984003036002c6880035425104083e0400000741018080500c040039012200c41c11680d0001d003040c1d0300c500d00c0e130060f4050001d075408003c00031008100011304000c541c0013002c3c0e1800c0c0c40308020181414440644044c01800c0000344580c0c004c90625000074a8081c10710b4000a1401c01c131920070b980d8040c901140300058158600002001c6941c104005241c0641c68001c0c108640 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 97480908 1250 97479658 97479677
    0x403020106031514040210030e0a030309050f1903121506021006052209061b08040b0c0a0504050f011404060203041d010302030a031b020901030f0510050106120902060c01020409050f0106 82
    0xe4a071310100500040d00c80e444503e0800c40c00da0081e80700c5079420b081481a0391a01c8010304010700205101074040c2e540380034120151500d400081007420f00540310801009070700600d038408031440f003030733902e5008201a500e02940300d0f210380445854000f0300c0e0590041c180d810f2501024000d90b46242d110300e010704440407020301844100034020500ca18401d50004031050541850300292255400740c841041000301c0c0601e400d6407045442d4419400345003450019110584078850a00c100000d500024070180424801031400c0072100020300c0301417400c1416030003800f10b095256403055000c140941e00004042000314941c800c4484540c0c07809041001540c510740100e900e4a101160003802c0005480791010f800038101c250b4200d0503000f40010099684a20b080d05c100d122195040d5890310400402c0c0031120784c0f601459050340d1180c0d0b0f40c10183c480103041038014000680f412644440c041c40b91682c4040c09101400c018130440801003058203000c0300c400705031007043e0002c000300302507242d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 97482014 1106 97480908 97480931
    0x3140408010b0916020a02041802030f03030105040b030703050309040c0c0512280c030e06040b0c061e04030203030114150c0109060f0911090405120304030201060315 73
    0x35540346894540408130b45035500464560341c01a80a080b40500608254108a21212140c0000e00501989a000030b0038840c002540e508580d1001c401001645003d014902c0b011400b80c1c0a080d40c2070a5803181074492281c42c80b040d0003240c9521003c610940700340c417031421058115080c0d440e1480e0440c404461548030b01b422550f84c07d100c0704142c0e07405034108280141000c554856200700a10740c0d6042d900a002d0210b0980c0c0324106210000d01c151464009010b00c2d10800003420b9946800c240e41d5441c0c00e03078240c41c41001e500007010803000940000440b415614043c1c111416840c000000480a064800ea11491010007045506c4034407015006400401d01c10302040c4522200e80500004859070000091300a0300110b01c00d4845041c12200380740c001d4060403c0d902c251016a0a581c2d00b87e00a94040700140c1d5600e00400501180c04a0125820380d00e2006100592a11 = true := by decide +kernel

theorem cover : BRFrame.Cov 97302158 97482014 := by
  have h0 := BRFrame.cov_init 97302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 97302158 ≤ n) (h2 : n < 97482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
