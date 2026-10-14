-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1856
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:55:14.351549+00:00
-- url     : https://prove2.me/submissions/66c80f06-f51b-40f9-9748-5705f4c16df9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 333633093 ≤ n < 333812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 333634343 1250 333633093 333633229
    0x3042f01201f05180703030302130513140906010b070b060409060e0f0c15040e100512010b010e2e0c060203070801171515060418021b01050103030509 66
    0x41e01001d42942180c0003803016135905c0c0c509100207002c0c154002504030480400650000c0901400340100100101c40223001c0010312090411340d40e03645000003c40c640c1c1d90041f90640c121180c03440c83c075041c941d464407008200d08016024a0b0b0003540c402a180c0050084d0241c1e070101c0b4501c10103030509103071114046082000c10700c207080c441d201b24240c8031003400311101640c003980c1141c03440c1000c650782e40f040201e03401103070340006034000a03240038141640015009106a64401c0ea121020001d0007001d10500c11b40c0a020300038050b80304118504a10440002885410a246000909140c841e19110200c1e8001c0d203065002079200d00050018462001217016040d800380700900c0b00066087c08924110400341480505843c4d20b4440e072040d07505c0c803042d6400b41162401d00840b4645a9007608003d6011028102c801b038a041400c0085241c180302c1c40d412a50503445a6207008109010000201c451030000c0761041c0007214496409c1840b0b03020a003e020701440d545031a1040e00c2002c0d1801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 333635593 1250 333634343 333634351
    0x2006010b0d0b0103060f09051609050d030f020a050f061b07080d0203130f1a09060f0105150912010e0d0207030b0a020d090b040b01080c0d050a1b0b0c0303042f01201f05 74
    0x102c01c52b01010010307900d61184032140e21b80c140c90101351030208078004909000302c80d600070b880c0d481642c01c25110340101140d03060080000014061105d105c50442c04010b000d071010140030755500340311020029000343c00135980194040308846039180c40c6e5603500c43d105148001a80c1c0d62207100c1d01c100c1100c14007034156410021a03001400180340001c1c03078102d00881405114080e01001b0004441c1403480c3e81550680d0900515a40c00b0540c07035103400703000f00405e41d4812000d00c0f86806064100d4000b01b0f0010a8981180d1004481d581d08800b0a010b5401500d580e0080c0da6114415400301e6a8240101d0046104140394441549041c030810701d080c011041d041d01c10321081100781e00003000041c0d400100c5612481d69006682c0a030740c3c401401465602007105840700160341044880c0100085201d94800c03007200c81104408841041e0b6080b1403c0790040340780750001034241030340c00350002c41c0b0900d01e1801440c2c00c4229030b216041c185440c59a41e65145805019062a0355107507000307a07a44 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 333636843 1250 333635593 333635597
    0xf030f08010b03130204110f1801080c0a030e03070210030203041109011203110c060301030f14060c0f0306030c130903030506100f080703020702102006010b0d0b0103060f090516 78
    0x5554148180c2e64010300c0040c0c12041030601c0388050b04219141c83c0c001c217080a51401d019a11280600d408000c0c07603001040048a03006c1501441c403407580511710050041c0c030015000d40c2050302c07001083d401042000f40c58030341488144030030b000590707550082000260480e42d02688034202868207008085510306410322a000c1400103204003449600c1c00c41d200e540600c2c0034810b1904401706c0d58185a07120680540003000040080144011469507900452041c1080318151141c0c0c2700050316400140d070420913000c010000f1000e09010b01b03014642001c4d004040c0c840b41041704001035941b460200c01911040d40303a102e10030506400d4070075194003590507502580e9440f024000109546451403807007040c801070202041310f02e4440ea040d1041d00d5400740010756444e410346405408080d0300c3c1d10f40b81c40100f120002c10b9183c04085551412144484040342c10b1060f451642000b410450070018101b41d510407002401c8000d0082c0320300103000c400b0001440c0e0401c80b40c2843d00d001150001d400b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 333638093 1250 333636843 333636857
    0x1b0f12020706120b220e0d05090303091e03010c020c10020304140d0c080307050c150a0c0224030c041707180f0906021c0608012706060e01030f030f 65
    0x1c0b02e811100700c1d601c012100a000510945000c001140104e00c00d0518100c1e452400c178114800c0c4065115101c0d920900f02203e03442540c68108440912a03800038a8064105018080306410701c501185800410758510346400e46400c0003080c2169810580400140c1c005904440c141c10482e01040b842d0710144099132034103013401e080d050722555654095001d112101110002d126841c0000d4014003920780549503281094105195103002c40f20501f07100340c1c0d00c9070102c101d8104400c02c0b41d88203e403903281c4810300302d035540802c203440c0021307005030002c02021b00030b41c07290034000c0340214801d085102d1029101d40c00c14402c240c4c0d64211070b03207075880c0d41c2c04000701307200b0814041c040f6140c10882c184082003a280b811098805041c103000000c2c011800403440117120030301d81c00198a145140c9004001e101ea540d075429007640d104c0c403c60340c1103014066900300c40d40000542103104900420020500742ea031a10380202402090b4410b41c0c1d04007014548070101a840349070a444200c952030410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 333639343 1250 333638093 333638099
    0x40314040617090f0307030207030614010e1b0906070c2409090908070804030f140321100e040c08011b08060f04110f040305010b03030a020c101b0f120207 68
    0x548620418200c00740b0040c0c244001410b480020007401a1261070390064940300e400300d18000c0d5483c0540d00085400c84d007010380580d0400c940e0744038603040b140303091801c000945501200310000e40c0140903008003a0350403c03404c44c0c0c580310031008000a602c900300300c1c0003440c03504459041c0490240302000ca042c0c41c05010306401c0d90301001e4131041d43c0130310000254501c0b0515107403070785200da00d10003490b10b2030100340041407200c03810000d0540d500a5001c40010000c5205c090789a04c2000c1286406d03000720300d02041000100424140c0c02207040c846111826100d002c05032550608607811200004e50704014010050203004050b910304c00101004d40c2600b5510f00038108400c02800d650140d81d00c00d039981c0040d56030350029031101c020000b0303c642d50304054036800410f5205c2d020607600d80d82010030405140c280001121203140c0c07581d002e001ea058110080207550141c0ca40079900b04581c0d82802010fa005000b4542c2e502486034420758851101c03440c011000442c045883d40554010754010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 333640593 1250 333639343 333639347
    0x10b090a080a020303071b1a04261c0918020316050405011e02010f0f05090c30070f0801020a1d1f050f03090106060207082b090302180403140406 64
    0x30f1070340c080e8403580c0384421f4200304800c108071001326841040021803081d24800501e2240e0010400d4649001c00c68039001508808000e4111082c41401c4059020400940170044000e00c604030311410f40c60800b914540c0c070b42d1140d0340100410059100b81c0c0c0e0001c1404100c60a5142a07140312195040081c01c1c94505800606a290680b600d807403140b106601c200100c034400e501180445040b800100540904080640014a011210f2001521410600942d0340c601140001810901103644414000203e0204108030700c0c520190049441407940203c0c0c0c180840301c2d50005007280b4800142c03540040032000f0322841c002d1000345665002140640c409860701400c0441400714690040d450034580f2104485a11800002c6000790601000303108552a0641185c02120300507400c4602480d01e50744095125001c048030941da049003050200c1c2c01042d589040c03442c0c58900d0804400e06035a80e00481e40d9021548800c9941c0003c3c0d1082108060f004568100700f103e4001c00941018104400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 333641843 1250 333640593 333640597
    0x10204060818030d0507050d091b090603080405040e01020c101e0204030b04020d02060d06060e03060907050306070c02011404120209071110021b0304060504091802061605010f05010b090a080a020303 87
    0x1c50100c2a171240001503999010b9021600e076041041010808207030242000c01194022054164404c0000c4c0c00010350481d180c0204801d99412001301840c2c58a0300b0100b0001700710414252886540038440145009000d0014260b4552007090109480184189490040b00b030180f03079068035441880300b400411110300341168442d5041c0c0ea000c1c040350b0b0350300010b8581d000d10392050f2030550400f8004209540e100d0802d0840c5181a811208a51a500745a50b03da02e840d028254056214600186803180b00d0030801c5c2043d40181000d20191044080c0018154031580260128203284940d1300c04605001284079401800303443e000341907980030500d11381c42c1c45c00c0348840b41c442a004a10b00c1c0030301101c1030203d18004003a0007103aaa8564550b40030344203400900c0340c9520315180c00122a8a0004502c212414a500800e41854840302c508050344076030048600fa9819980c40c02c18480381c2000e032040074080e10440e00d0b0b468030343c0030083c100000c81100ea04a00020b40020030680700585000007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 333643093 1250 333641843 333641857
    0x9130b0a080d1e21050a0b040c03021e0c250f0f05033009030309060301060804021206060108072d110c06070f0605190f06060305070f0903060b130e01020406081803 72
    0x4c00410710b621012402005002c80c4607415506c685015514800300b90143e00505026000d0043c035503884100301c605068030300840300b5600180e000341000c4041c900c0f00d200c9242e01000d01d840310038a803684448410414040701d41007240c00e1810f50310248a1803900f0481282240d0324108014004005807540d0025000d12910105e030002c808034501030785507001e205680e046003001d0510754a03580d58106c01040c6c6401076034143d004039100001540062004240c00c1e106110684403c4800c1e1242d8408946203400818800d50310000050300c00d0b000c00030030204140d248503d80d580e028514024911a0400c070700c10442c203208080401407000040c1d02c1d83d5440e2805034100c0c00c001910b644881521410807140000b01303d00f646800640c0500003000d83c419403d0322003581d001c11040d0303103071503054801043c828401c0c0080b4003008400c00000710141c00421302c44034040c140c031030320341c44507111041038851107064655565000724051041660140e5055070062107641d000316182c00320541c040e100c2c450a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 333644343 1250 333643093 333643157
    0x309150201090f0c030606050907020a080904090b100501030e010e100c0908030d1407080c0d0e0f030f0304060c030506060406030c091205030a03060b09130b0a080d1e 73
    0x4801500140e000b948190b480c650010a6540746802500c0c003100c481c0d90f80c0c042226040c0c50310380b021131541800203540384244050780003400107981035100d0301c4085c1c004201c15a070040d22582c40100043c1d0940380710340160611103032a00c1c41d5081c58005000d40703c1d240082c3e5481e81c0362807140c502d81807000a021080518008000910b01c9240d0000c507000c00d12904440307802e120000b820b000c210b104c0d50007a2040c01001c5401800740e2181b44c81181d4100c070542e50084408020f000940101416070b000180c1c1c800340000300d40d0070400201006085821050940000f1a4080f0802041c881c49010342c5a150700306150400441c6040000514540914000e07901010303510b1051121480c0100a60b41c0640001ca03000c81920940e460a80c0e600d912a08507000028140140058101881e4040d00c1117038200901b607801000070084104000c0000100065000c0d00074070340003500420511461542094940e542910b06048064142c5924030640c40c0008028044140803031921040b224010220002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 333645593 1250 333644343 333644369
    0x9050108040507030b0f010303111218031608010c12110a081915230901090c020a08070c0f0f150807021c020c0307120b06060304021c120e0d0309 64
    0xc2c00d1207842e1103000e0b04000d2003460000c0c148200079181182480c100e0341310303503200c2c429441024904c50b11103e03003194050041b1010f0107901e008400042c4903484ea00005801c40380c2d1065107186055002075240d014100c10307503564041c103402c1a4000c4040e220010a810103010700d03444101641050300c11644240d0400592030041140c0c40c0d543ea00e0710f448002041000e01c008100312050780000c1e6103500c10001024020664161031a030701d02d0040b94109001002864181c0ca0f14100c04007420421043c04118094816840e0003c0e000c44064505c65004911400409080c031640c00801503140d00a03600b803170f680f41d00800003c03106078840b941d500c031186070085068640e9038040c0d1506420103003072041c03030651030b45c05083c941d400565107820007000c80450f84140d66600400340b6950342c021010f071004035210b00240f020308000009542151001d0401c0349140c0c0d00d806240805244942c00712811002c4194550241c1d41c0300f01450b44440c1d0407241020280344596024014002c54401d519600e148 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 333646843 1250 333645593 333645601
    0x12060708041e1a0117060a0e0a0204051005031204080d0c17030708070906050a090e06012c031c0806010f140d0506040c02030408030d020f070c03080c061609050108 72
    0x14411203010444800041e035101c88142c5030001c0e203a0f098030800000300105600000312000401c00751140d42d90010041d00b0341ba01c6445044018102107a0749202c2482203440c050f005864070300c41c40f4450100342c00d004608508000400d8100b603401800c07240360b0f42c000e00c03051200c02000f06001380b070301e411420005001401494480c4400d842001607110014011042002c103a401c8a00148504000da64010055488100c01c1c1c070f060154050700c40010b9040003041c01950f00840c007260b007280c0d0505002c1c00c0082c01e080080b044000408110302c0542070403002c03403803d0504014903c131100c2d4a00a107003c00e1a01400180743c2d90005103403504000d54082440074a80c021300b40e6003154280f0043c40d075641c1382c0b004c4ca594050681030303c225000c0c5140240c10080c040c40070007594181d40b08003014610b080d40000e4064040d4001c11a00c00e081031040000c1320004544001030300c0203602c1025402c0d241c42c10076081d07038140600244580c0100a078204626925988603550700c0c1580c000b42030001d101d0b15 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 333648093 1250 333646843 333646853
    0x1c020102250b030108010c030b030715081e0408041a07020612040f020405090703021e150c07080d0c031b020a060c031205041b1211090403030b0307060302040f051206070804 76
    0x48662101c03402e810000004a42102c064100c0c40210031a9281400380d00e054105041d030b21100b500c0b52000b14040074048100c20380c400d00c005070708000d8804190b6404c020300340c01c0111032101503400300c82410002404011020361416078140d600101d040090810803141c0100d0800d01c07841151600f504d0320390740094104241079811020391034001d84200810700d480640260344aa80d07000a038440c00c5481441e19503141a4458400380580242445038800480406104160018074074413030580691500031540d00e0781045107640b4440b0950701d44980121038103002d00f604011840300c10340c000d0100030700b101580f50b40e07411a0494a041c54a011040003505040b40c0d04550380e684080302500f404240024002a8065591003d480d031121121440d0780343d05a11080380d90900003486903000c281000014a0094404d03079205000782000f1030500c01d40c10010341081c1c1c2d02d40000010950100c1e0500a960362151039501a100958444500c08490403540ea600c000051031001040401c60000741080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 333649343 1250 333648093 333648163
    0xe0402040b0d05070b04050310050408370507060501060c0309051003150801051005030a0b010608040c090f0e0105060d030804021507080706021e042105160902091c020102 75
    0x283c0c002c400c4d00c1295846107041003503a403203441010312030701c0b911040040404462254501499115074054a00348502003000702d206404e02d8048581492170700b00107403200300c0c29842e0214040341d6580507036032025444e00c10300700c40068000b50204906070518200103504400340c44103a4000312010112200e42c02821800340c501096040c0c0b018000d41c1d000a6840015048940500d007201c80c0e2a84081d01c6105040c0e42d80f0100d48054604007421004112141c040c51115410500aa0724100c0307103901c6106200035102d00070303141451503a5071140115410820702c1a075810000868011880e48120340380140060030282010b03100d0300311401c1c4440705800040c01c4490803507100c41d00c00e40b03c0e2410308024009401c41c0d1040e14001401c41b0301c0c943c1e446070045c212415100b4881148a0003000c40004e00c5007a00090000c46262182441380b500107102d0031465401888001c0d4050381c0c81107004180082c00c4940d00703402c0c03028081448103100607078000c01c0215102c90714501004140a0241c0c0e1420f1070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 333650593 1250 333649343 333649369
    0xb031308090d0303060305071523040b0c0d08011502030a140705010603080309100506181e011401020c0a0303091802160809041b0f030207060f11120a05010e0402040b 73
    0xc000c05400406806400c010101d078041c00544240541c0c413400c022001f1000144035001030035000b401011148522b0210402001c51440303541003e03203030707240c442042e03122a1192110380e007c001404070340c035805800c15014201c980c1242ea22191020000f07541c80c00ad00020740140035414600c000101080b00c1507407485034101000703000455890030604059441178503500800d004810403c3c030310741075501031303d8040c0070042e00105180703600100d03008032010b026195604c2103075150340010f81040c086d002d00340070b0b100708041109040b0303002002900c0c000c1c0302c011007409601000020808240c100d60000101d410420150014003010503420303000340b10700a03000001d00c54203002c10b010b10000602811600034161010004044444c40540000548026140c00a4480342001303030071901c2a0061700742944100e901180402c2c40c100c001044e1800241c03a4510b0100110b84c501ca1820b84a1400d0b40010b58928100410750601001403c4440c009202900660301c0720001c040300e0315500c103c8081e1f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 333651843 1250 333650593 333650599
    0xc051b194203020c0d0c020a09050a090b2805061c050a0b07021b01051903020f040e04050c0f120a082a07090c030b0901140406031703040317010b03130809 68
    0x11a41c01016000f90050346496100b4400c144640c0d00d02030080c41940d03041c5400138006500d461406074200042c01e0001d101c80b5000c1d46914445000403403010320b09004000d00c001e10300400d2140e4100d2440e0021034088690924105004d201e165190451418000d1681e8804180b40b03040d81d041107440c4c111100801007400e078060303080022031503000c242c41c540c06100502d08185842c0340801180d142c00703034000e0f0740700e6000c00920078523256029a0062400c0d1804200307940c14a69264a03032a844c140c00c0380d09448070340140c414a1203e2030001a41c00d0486401c441030044560074918240da220f40d14040100b24020010751846000500c280c01c40b2150134002c1c81501a40081440e07540300e00300d603c503c82c0583e0600701c1c8a10b0302400707401100320030302006d881c80d030141c1c0c6000c40e02c40c41180303039007846608155a9800407021a020026040322a0a0401d416030703203091502d0000c00a9560004030101d40500c0401800808040400c9035040084144c00200c4d0346014201600b0620541c80100d034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 333653093 1250 333651843 333651959
    0x203100c0f052a0705030a03020c2407061814010b0108010f1d0606040902070b01060909050408070b10170a06110f07080a0c051b19 58
    0x2104581140006598a964403624140749a9094507540200854481c80d40c00d4a0304051241506410480f02d404818040b034000326901c001280c2400c01c0000140e005800c940c000540c41d0034890301c2d0005404100114907882002000c1e215142c2c003c51100070503040d20341040d58100c05030340780344584040e0021554901211280d0b0b100740201058400300d8007250b843c20001880e81c03080c00b051000c84820b1481e14002e41c03480d452403c1e808100802c5694030503002d00001c00ea098007407016000c02407064401d11038650418201400f662096030145000e0380c01c00c402c000c00a00418107540c8030a0340540c00c03a0054481ca01020980680d58121802100c2a03910900314000300140300400700d03001c0c4d00100550820800040f41500c01c0784641c0c00d000100b005800002079140b0010503014440340f4204050b0300159030341c03905180d0b1000d086110f10302c1014446403d0301d8880c1c240086950ba81301c14000580c500b8103894450f2640d19000d41c00c00820740b580403050320001d105000e1805800c201c40c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 333654343 1250 333653093 333653113
    0x30f0501020d11030f070e1e12070b040e0903040f060302030402040b03150a0b03010b030706050f04090c0305160c02151809040b0f010608010e04151409210702090a180203 75
    0x60f4181c104803040c9540b5420300e008210f50b14040d0620f07007181d20300a805440805504130f1900c0305c41d10380c000c00c01d070410402c00801b1649401803019901130702c10400c0c019582c0d4501200030510306009032010400b070b00100003c03c41209800141012107045040c09a100d0350340740001802001c83c66111609402010340c4c07282c01c110f0008449114421007a810031040c0000b006140c02c9400403490b070364041e44a204148180d5001704050b0110001030040c0d40c2c589a25031070070009840031040c00b1000711761200140040e0152182d05940203085038582800c1625160300003a000341030361307003001c501e500000610740720f03001c00c201c203886200340301800c940701c581041d10f00500c0c07450080b100c50b500c0680d903000100d000c0f032240a12031304803042507003400080c0d207403902c0b00110840001c0c21180d91a5603460500480c40001e00340500c101404806000400c122514813080d10301209060402400100704031070040c1d54621040342c000e40d07842400500c050042030300c10030344030001c14080c0d810301c2843c000c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 333655593 1250 333654343 333654371
    0xf1201060f03020c030319181a01050103050f06040b04240311060c061803070c03050309030d02010c021e01060308040b0d06090c050f16020603090f070e10030f0501020d 74
    0x24100c900036500c0341c590081451049049001d103c002d50801d820810200d4200c1d80082c6031041a000080000200da03011040d82d4035040c0f00680c011508900c2240d0701c00040ca88066142d401004203007070510003440c2187e02c102c54218001c055501c03d565170446210740f80c89a9215525180506003140d4814100c814a4044002d0070700c8101c901c0c806050001ca0316013041829503185010550080c00c40d80c0315180001c61580c103010540300d21703201c240498004241d011142900550048000d142d8901c141d00605050034800321f106400c2d60b060451414059600040031951401560100300e10428010b0740c003405010706034400341c4031440c0810082100b14588008004002c0c12900c20043d1a560740b40c1002038902c00d08400780403480500c424810007446e4402070680e003184140300021081e00d030f400902950415101c02c903032944495610b420105c0700b080f441c0003800700342c5000300d43c074603011442c0c4d88071040e94000140000c810b041c070041080025010b45000e40e2a82c90b091101c804503004c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 333656843 1250 333655593 333655627
    0x4020d17040605120a06050d0b0a020c0706201b060901120606020f0f010608030306090604020d0501090f0f0e030405041d100c0806010806150c21071a0c04030b0604020f 74
    0x190702184c008802c0802e45c5090340c0d100b441c04680018001546800140d200c492104000a14040140d5000c10202a50702002e00280c006400030751551203209010b0b04c1c0d00001c01040a030721400a91150309103900c1903007072041c11800e00310219031042c3c0c1e4a0604004a4a0500300e80342c54441c0350910304041405074020500031001d10301c0d10200c034150306a0b400c0031030036640940324070a00d42c2c2081001c02c0d100d0524040c0542d1062014101510700704410000382c084482c242c1c00b03180c541e0303074609110000070390070b00440c0e15400a20030b09202c450004c552441e200d10a40c41000e03c603c0d07481040504005512200016036810003046d03130b08075580d107050407014240c8a24148001068000025400e44c05100d8003401003402502845042006131401d010651002481880c0d9200d00301d110055000540d0016680000801d1402e444000914010340203003a546074140c0310981031010480d5003503594081e641100d400882030400f5803102c40c0460020310903e90b43c00c0204000045200c0c21100a0340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 333658093 1250 333656843 333656857
    0x411010c0b1e07080103033212040b060a0e060405090f06010b0901032a230a17070309170304060b0a1d06030c0102070923100e09060402010804020d17040605 69
    0x281030b08080d5541107080315081c1090000401254840001d02c1c1181040901c50040001d100c4034505001c249900c03040c550342000c0c811040c00003040d002c01007001118010340750045400e9502c070b404542080144a01904000e1419025a039030303d000605258042210314480781039803007900d4036561510250002544680880c90120342802000c524144444a8406000d80c0e0100e10a5100403100e0040350881016100b08046031480d01d802c982c0020310302d0003400f8649890700c03480050301280600316049a4010044030a041ca0041d1040c0071900a8484410045084040303560343e0382d503460400001c100700c001840d00108010700c0860790807090030a00c01800c0c40f44005200540c4c4450030141e50b0140f104070640141c001003010040c00b04140c000650000054030680300c10000701004040d40d9404480d0410a245c1d0300c3c00c100315400740c0001c039030f401110400107012181b40c50340001e482c500c4041c2c4024050080c0134850001c0c481d01d0300d41400c2814410038000da07141c0d995a8020000d800c528 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 333659343 1250 333658093 333658141
    0x20a090c08041109220f080307052d0318010906020a030f0b0f0310091103060406090c080601052b0b040c1e03051c090b0d060608010611060411010c0b 66
    0x403004103400d1070b00328542da120305c1016800280c0500401c03044c101c00200b149040f560f58032002d030800d001803401340156200d1040c943c2c86a441d40a00044050342d2030218060541e03c2d14080c19481080c00358a04980d80201da191050247c1139803c03d007140140700e8200301801c0c040c404680f41e07024551541040c2c282c0e441d280e6040c490f00c00343e40108071480940440403545640641d802c1414000c00b81c00c0301507da4002c04013000b00d203100a0100f81401011101115a169a8107400b01000110315486e009450a28001d00c2c0c03942c14240803071001d2412070703c420381c07000451015100091000c96801c1d02e03242d00c0001c0101a00386468240940d0515001d000a1303040301249019448900389134110860303070400020405101825010300b842584004540204640c000000c90041e0111000381307050302c0510800a0f00b54a054002805460103802c1401084080161090038000010b0841d40054210500c0780e0340c009500c005840300c20038008014081c0400600300030f0031900c1200d2a010080080c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 333660593 1250 333659343 333659363
    0x52e0909050f06030615130e060703050c1201060c0c0503010906050103051921170103030906020d081504051005041107111503010608070203040b030108012c030a0507020a090c0804 79
    0x6201400d0760b01004944882e0164494000103100800d42e00c00f05440340f6014042807a20303488200f00d40c042d100e2004214503664800030a00ca074281e0700d07205107548401100380705401c00c41d55080c80491400c041c401c4400f080359044c8800d0500201e03091280080038020002c0044e5800e0f071800e00c000e414248801d40f040e0041002018003c800b110711502842d0b40006a1083e445200480d0381c1c1c070100c81100035007080039040040aa011600c20100d001e103000f529208503140c41c2540007171a020350b6071681001c0100c071200340a002d5103212500c00003031208460108056441780d031000040820b6a010b41d0f840741c02d00d20135800c41c118100040c14018080e030340440040c10080c1c01d2140019105801084c0c05c030003040100f001c54480d404060300843e45105aa1030320350341b40c21400c03a50f08207030000720711a55141c003042502180201201d1701d0007490281c2211144255026503142d01030b90781000705200c80016000c04650740d44481e04003504107004104640f0500610040180c1001c99040b20b9030400c1e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 333661843 1250 333660593 333660601
    0x1103010e1f0b0a0c1104060b0c06091504142505010810140909010e060412020114010b1905070f0b01150305040b010504090809032b0c0507052e090905 66
    0x74000c81c10191074201800a140031031081c4200d41410181c1c1c01511810303095645149540d46e0390007100000d20a09102a03143e1103400000c034140080a04940340b03980c0103402c02170801280c03451481e4001d4003c000340b165003c00300561340c00c1134440750001c0446e81481807082d0a40c1d1502c0003000a0724020b0740c440340160364500254000c851360b406507900c01619208200801d281c2027030a56804a41c2100114070a241c03501c0c01440d0200c00c1d582200c00d1403580703281207000b580c24400e03030001c0b145d1740e000d003102545402c50148061213104007a80e604088150a482c1e22405001168001a40300140d02e00f00b526500340f074510810213000392241810607203140c9583c1c91080c01021300664100500c5001d82e46410b080100a243c0714000712007400d414041c1001940d03051156100302d0215400668001e42e480c040ca403036402c0303c060300381c040c8030703401c2602000708038009034034400d8400c01e6440c402e100e070304840c0040381c203104140828464256001c21103481a800420341c42202e190a1051001d611 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 333663093 1250 333661843 333661891
    0x106111506030c0d02060705070e0a050a020724090b0414010c02070b0f09010e130b03010e39060d060609090903080a05070302090a06080402100c0f080903011103010e 73
    0x30703901c1a40c594001d01403a010f42c6040525541d42c284024030722803400e01d880c5c2c1c0d69030034104a0b40c41440780c480480200f01b240319440c082c01c1da200010040071450074116a5072904101e0001680c4140304202d1028511a034802d036001007075440c0c20900042c000d16141c0b0700700c882c820580181e4105d6509000001134060b0000552005a4918007465410301c05109640c0100740c1220301c0072810010800d0355241e107911a082c00f26902903038151b01080d0501d55106044c25281d9091403055143d004920100d0078500c0c0032013081c40d940d5400d1000072800107481802c07a902d010403800d40d501040001c0c5409900500f07500c5002103403055214103592030754031003024045802486c0040d011441800000340d003030307009510040c2d019115050050030302d80c06c05c000c00c8000c00c0c05d401c05004a40e00c0c40600013036180115540b003030b6046c3d03072a112480b038860b075075215454182c061004011000100f0301421903642908000d00c070840500100d520b139030303403072a414010740010794140d100b070084450010f0b0045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 333664343 1250 333663093 333663133
    0x706020d0207030b04060b060304050f010c020303070e04050612010510060e090103020109061101150603020a03050c070f0f110d0f020f0909030f0705190807030801090c08010504180605010611 84
    0xe440c54024004091940e120a0390501004004488603651441c1d83c0203030755246c0b0007440c010341c080c000414100c001e40400d01c0c00c58480b02e0848056520034001c00280d95481071010440300302c01da50105407500d510000c1404d250b14404c1822241d400c0800300300c80000c02865070b10031901e00317541c1e15070405104403d0000c035100030300004c0d001072601c50381446a24050b1140d0890100c081000017804c1c200940c8581ca60303c40354001e000001d800141822030030780d06004094115016803141498000303242c0e1081301070b01e00b00da00108090798010022040c070115510189081c40054600211704140e46802104145c507044103d10654441e900c4140c0f030300b8944800ca06c1790400600452402c81a0301d81144160008102251680328860641100d15005005280f07402c0c032030078130b95446208518000d00003000580042100518080c4080c0c0d4065012420b0b40c11254241d40c0042da220310301b85460515041d070100648403c0c207000000800329413040b0b00030307414803120040d80c8800070901c4241070342d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 333665593 1250 333664343 333664363
    0x60a060c02010e01050309150a05070e01030b06070201031509021309060b1911030d11030601030b0d0507030213110c0705010809030c120a0c051c02150405030706150b1605070602 78
    0xc3d0900040310019400707030009641041c80d440c200c1e01300c4603c1010541007440c04943c02d1079680d403a20213004429030442103c2c0502107003400c09110b50030024010070307624007803201d000c0d04043d1981001c0c40c150341011042e10180030700210942d41c44c070590242c51044c07203803403080150551070401c0c005a0000d6035000d8030b0441d0701c454141c0d07000b079150881c00c4a14144400700889a4041000040d200e440035200c0d842600d50b42400d41504e03840c2c4007002500b1215a141101d006024003644000001c10104152081c0c03a8120340102d01c460091299030001c1c002c400f02d05071151800180e5070440000000c0c400c080f1102643d403134034282d803100344154590055214940c803da00000703c81c0e682802c21800f5000c02480740c07610301100d116648403076162081b80c420741e14160b000c103c4a5200240d0600480c80496500711281e5480e0425643d90307603030fa10403100080d04280e070b1034a44d0038815246002c4100103081390002d903610b0f00c01c40545140101c43e110f1040312180f1804400040c1c050010802200f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 333666843 1250 333665593 333665597
    0x2030a02070918060c1101020a18050a0e04030f1206060c05100204080703020607060f061e0b131e0e19150308040e0a09061a1e060904180f0b060a060c0201 68
    0x403c55a695030b43c000790a40c8a40c6074203200d140407140ba03240c602480174100d0b610369940d4841681840002500c03c56a441e005607024650303e840503c16103001c8410300360855458984084120032074802185e042203401359106c070b080e003415000200c19a008142d0007400740100e084e120f0b4a80311801007070492140340300f03014154002d100100301506c0c00c60054402c8500070007005c901440c02c80f914604460564000090349450300320b0f8101c0c0e60360010444005080124420341c034020080c040e0540c1d0315101d1058603280d940c1c02d00880000342005203480c00800c0600f1841d80c04d030402c3e0980c0701e41005030304652405107142c003400190740074846080303100320303a040703541c4a00d000d090181c04e02c4091801000d40c02c035151a98000000950284921250143c455000600410500040008009a4400c00002602409100280390f03480c0001c441d0a08412100010260a201d4207500480d20494000e4100390012580601744550590400c0c4140007c80b03681c002107485100a549840d9040e0001e40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 333668093 1250 333666843 333666881
    0x3031407030902011e0e06030a0c1103030c1b1009080a030b0102070f0302010f05130320030102180603090a0515090c0a080604030503040f0f050f060703060602060c0d060b0a02030a020709 82
    0x403580700040345041701608900e0880e0301060614007103a02980152401d0300082e81d94902200b825034003940080f10020050041e40c51420082e081480d90b029001c500141062404c0905200308030810500c0d040d407210306400d200201c0b41e0704201da00e98020140801c0800d003042c1c105007003584042209001d032080b0800d204410ba00b1900119201c2400406a01c24013004100503251151408081001903204400e5205003610b885c4403000180d20003061180640c0c01400024428804541c0c07582c10340380c2c04d5590548075503610151a2034019102009401d5002e50002c1c0303003100c3c02a9800a00c120344071400c695504005100b8409144007600c9001215001400030500181c0304038010354001e4003072165191142c3c0c5075120403444000b004022146540250504001140706204241e030040700750400700211031030400d0181d140c21008080310140080080c2c0f08864205c194081d6000c1c18024502d152540e5076070002039540e03131001d03043d00094418000000740d42d0782c05004a00c1102c042c55800f50b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 333669343 1250 333668093 333668117
    0x705011125080a0503090109060302031302010f021911090f07080106050a02010908030c070308010b041215020c061009050a05061c0f0209070306030219080303040b15030304030303140703090201 85
    0x20040301208021601c000101d1000600000800641c00403074001c0c000380d503407a080c3d8800580010303c207600ca10103250041c42005a028142c90b5084003540d02800c1a60300d070008a18128201102c3c00d103a80c8544900b2500320060042015002c00c90301c00c1960100303c1529850001281414212549000504204010b00041d4800e00c00f625a0184900011614030490760b50103000350000c443d80010b8003404285e5609040c0c2c0b0081050040c0b00c004807142c40c2c141450301d816071a61700300b00007a00f000c0100442c21f0541206a0450750507140e880c1c1612418209491043c203410341c144a1900b030703103003010082440309025119140c003c0400420b5a035150028003c120041c00e200d0768243c8807052590040405615200401031182c87c0303a59000030081c0c214030400250440c01200700345402d007182030611941c0070000c00c80342c0140e080400320b0015500c41240044840342180c400740c143c000030500004240c0c0682041e50600f40001c003011281d0788002c0121b046400c01003002e400030724022042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 333670593 1250 333669343 333669373
    0x305060c120414030f0d050609061e060f0c01020403030c0308070e0a05010e01030e010c18090e1504020604030807120f0c050c060d060f080307020306060303040e010b090f090702070807050111 84
    0x243c003040c002d505490a101201404950581040076407040d242d844800f003080c1d502d001c1c0c001c5a4007500c11034003510070218002d0705454640780303894540c0c0912000101d00c08102006401d0702c1c00c8c0c44508000b03568940c0c9a10b401440300110b440e04030003282c036801c04074100500a410341600034102404640c00b9600c2c100c0111000380303980b042c1505040c0d45426002600d50300f8090f6040802c0692503c1a100115812a400302642984103600540c585005205c51200128115103401a03110458041d41c0b580d00000c3c00d2441aa84000c000940000304881086503030300c0154038448854441407222606a00151a21a02d81c08002c2640d0020120340780580380200c0030703101d1480342d2400010740304d840d00d0403506400d840740c01448640c2c1c8045103100c214a4108401a84508203401030b5090602c2d003414191503200601450048640100f03500001d0385400821900340100101900c0035800c080300041c4d11341451703010708211030040c9007011509500030398049000d001120300803e660b03a20007041d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 333671843 1250 333670593 333670613
    0xb01111005070512090105090c101b2112110f0904090c17060610050a02060109020c010f1802030c03031c0b040e0f0708070609030f0b1509010902040305060c1204 71
    0x242c9000c1c0300052205158448075484900d00c10989400005214101202482c0c83c100031400c0c02886445500e4180608540c4207080010726005c50003895142c3e02903180200200c1c5210040307d00c007030701085120744401da00081c8440f070b02e40b448404001701000c0800d445a140301d540b6042101c040104100c0d08541010752100c0102ca000c2c904030710364280c4070300c18022010040e80080e40281d200d001448594542a6110201040941005031034401000006500c6260501c903148440390b000ca0f0300600c0e18029000324800d040446000c03c1740003000c2098000e0884080004e034041d12600500010341c3c10000112201508000c016018840d030400482004d424507660351504152906c240d600941d40c10040c2101d41d550f2907000e010550300323003400c0625100c040d80c4400d00f08403410030204007086180710318501042c0c020525403080d5031484081e012001c0c4d24040d8541015520b00005030b881e41a0380544142e03886030342a01c202e41c40e20b44092880d4010305424480001110001c500051201c80d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 333673093 1250 333671843 333671851
    0x1312020d050f0307030e0a06020d14070c12050c04090b24120105070f0318031202090916020106050301090b01300b0a0528050604090219090b01111005 66
    0x16031010460640c1e600d50420810301840340c0e141c0c1c0007140e2082056085203541d51105015512048810b01d812002540c82c88421030710400d01520b07910018150003920308684803d5044440a211240e40d4082c040c00840c0303402c0141d80324003440340d5581c5603241500415030525004654500151146a1031500e903c07110081c0344204283c400044120b070f00d600200035140c505c960000181c80c6000344018043d0580c00e04a40d0825140c041922304030035501c000c0749002034061400210202d0800c150b4402032040082460b8410038401c10421002000101070b28141010380c0203000440da03c8083c1030030f0399100603006102c45010401401702885031010440c2d903d14a14a1010000c61034980c0d6540521410080e600d40226600f00070048206000381e0f85c100444420b1812400c060300d4100301c4100307411200c03020b290303222404120581c0e9940c03c1394105035001402d10181c00c00d180000003188206108001c034903420003120350301070f60045401c20724403c4410301614010040d050f40f24000d01e0010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 333674343 1250 333673093 333673099
    0xf070806010f170c04061e08010909111806010201110a0c080903013801090302060306010305270102030a0c050913021606090506072a0f02150a051806131202 69
    0x540307112482c0c3c08a60780c02c1d00400d1080300c6660b07503d0400360010b20817841c4862156800c25648910000140d0040b4143c0c1100d010840005280c0c80c646000000c141d401813190741d104184101340e51441c00403822a07400b07008240c0003000101141b6410280302d0207013044c2c8401194208840c000820ba400700200010b40006000003a0325034560002c0b107036001c0092000340c44c01c545240ca01c007040260b02c401e0440380b8003400e01140d0a461580000c02c1c6100041c1950304254a800105005200170380da6842d405440700040160004000d60b09030003500202c0e00804010300305000000e0050190089030a00f8002400001d4021903003400c200180d4440301c55400180070514044011030028070982035018483e0028181c1070034007a800418064545540c18070900011113180810ba0400351542101070f0f0100c0ca04030101c1c51800000c002c0c0d0700081c00d5000e031080008020380070503400001405548007101c1c00c031071300c10150814040c0324003541c203a96504900c1d0340818000c03500c4c40802041040c0c401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 333675593 1250 333674343 333674357
    0x1805060304152c0c0604030303020c07030210030b0103051e0103080304050f0102070819030606051606022a06151e040e0d050306031506090c0306011101060303090e0f070806010f 78
    0x4a0303000c040310341071a0400c080a11142002003107101d008030501811420f10300400083c8150300004810344100d2100400b0300d5030009412403071560501120303004680003030080b00845001c4001074040c0020030215070000e4230b49400550030300d410040500394020824032607101682150350b86103542c0d001400c01d079954440c0c0d810340b030843c15090000b4000180700c0d00c0c1c850f4941c0340e0f0310880b1001c03040080e02e40080c981003c0303042c0301042d804410364420000d180310204000c00d440c00c203007009100d0f026801c11b0200d000c0280d6031016200c0b050704031050741c0c0c00c8100c2e08595603116018840540d1021a503901024061075000200c4405000b00101030004000103600420f42c44054540244030061782c003c0f44012040000c0307498140320001043c1140710750742c8114a020f20005e402210002c05104c402c020120105955034410740c654022445148020030440e512030801400c2c0c02450300c07070381e150300c1e2010b0b002803c51000c00d03511a00404d5691074290032034942500642d4604a2024000c00300120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 333676843 1250 333675593 333675623
    0x10501091d040f0c031e0309060503090a080a050706022208060903030624070b01060f020706021203070203070c03081c091104200a120e010c0203030a2a030c0f1805060304 75
    0x2c001c0c1c0300e180100c20f42002846c03031020714015011401c103510003010b001d010301c10002070540204102c0d043d154081041c0760b44990810054845000703620010b0145071020580c0d40c8001c148607901000b49a1496049804a0352210156039900c5c0484403041c407500148003145007070a01c071440c8640840c005450030915041900c00c0c0c1000d80100394140c0e140010302004000c000e0b0090805142c2515601c0503210450420308042e40d184030328003100110000001c00203c1e8503100344151407945902c141c03c41c4c0300c203a0300d06041102e9000310b00b6403584481c7c0ca1031044e4503a005446030482917603015000003403604100c400c220082c001e6008002c001c0d4944a01d0122000c40e20004110007035a548580c003100a003004044101c0b0303e40780d1940c200782e140107611100f1940000c00c1d03e0b4030a006401c081058840d10034242e80c155100c1c0c51031654012610701d0000044c0c0c01d074100545e50303112982c507120300308000c8030b00703d07000c1d00030f03041080781c0c903101003014845400c20000942d80540248124042080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 333678093 1250 333676843 333676853
    0x50406031116030c0303060e0c0906030405030904061205120702090112060b120102070507140d240f0e0c09040c05010302180303030103030c12030204030b01060e030c04050708010501091d040f0c03 86
    0x74000714110300083c134000c0345908141c0c040c800d02c80903060311441100113291101030840140328581110317108020100c005030800c1020000c0312a074440242091000e2903458001031030b0440c00c0c0308115824003614840c0c02d0041030500540d080c1980080802c02540d283c843d58495040d81030405450103511900c0e07012041d01c404e0591174115100c0000103a4443c1e02e030030498108020303600503a1200c4081c4151000e10f56580e1010003005421140c03031080c3d803000c0228180c21111000207a17904c01c0c2402100340b4020780c0c0741e102e10424030a4006850700e070b070700503001c21031101c604841c000d2504d0301700315080c041940300754080c0c00451081260f80d603011401e00b000038503641007603008900041f11039501d001000444208501c0b20140344c1001d50134a41550741d03241c81044140901810000d0022800c0780a86c0c08025003010058064010840350420040040c000a42406000d02284507002e0004169002c801107041322454504d141100d0380b566a103000c000b415100e000c0c1c5a08024440c0440411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 333679343 1250 333678093 333678127
    0x6050c0d03183305010305030304020105090d0b090a0b0c090112020c16151103070b01050904240b0405220807030e0603090a0302010b0d32010e010605030c040c0504060311 75
    0xc03211415405000c6107200f402500d0140c100c9070042e07a28142001040001d900000f60b0341c000d80e090804588031045580420002081403001504180400080c40160040414a0710040340151170461240d61555a48501c603c1149803050000741a250041d0029a0036030142001c60b03000c2082d2190100001038040e481170140c0c004056200c51450400c4000c0e41145440c1c1d1a0340d15040510300b17124558031010b400d00b10500c5114090801c89000504220004089220010002e02e65484081000940d100184000b594603801245003001260078850202c2040150242074086800c40360312981e14180e080e00051400c509008007120001d8050752000b000d9071141d91801d0051100c013101d1700f070003801d580e44260020f00032090320031101c0c0440c142c45150340c144100c08468400765650040c003c234440c0c2140f1250213055203403080c4009440410741120b41295000c60807500c001d00f00c0703002c000845100903e0b003c0410010041080102d020390000494100d20155280c14001240e02c0d0807044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 333680593 1250 333679343 333679373
    0x1060812041502070323070302060c0109030207290d020412050f0d0309110402030717070f0e0402040b09190b070804230f061c0c0507030906050c0d0318 67
    0x4600d0201e41030181c48480a0700140016441c401070800c180740d51140e0303e04400280a02c8014071440e810008489000c114031001154080c084c40d40d5001900c0503a03000b440c82080803801402041d41c0000c606852134011420b11401c11308101c50701078500c1c5981210b520001e00c0380d0a1319002d110020740b07034460800d0030301550f010340c001d08003004401100c41c0c10090300c030002d2810b040c0b400e0340380e20102c0c080c044508a080d0080d07a0050307690329140401e90b510003038409100c03001540e0400300080380740d010200c189104555245c0c108070000240420059004a0107401280300b030600800d00b49150502e140107101104060030300b8030700d17180e00d240f240d2988030071000d54041900050402c04020581c13643c80224410310240390103c91404000750f40c44855100c1c0da4800c4c0e001003503100c410511641c2c0d00c0280c4070000020410110005405041600720840c10340105150010001352140202e0841e0301c07240340e20b0090410f1662800055006001c18103842c0040d07065154854005030038040c02180e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 333681843 1250 333680593 333680623
    0x30a0503040801023c0703021e032d0a0e0a0807030b15041e0b062a06130308010302010f0309121d030c0307180b090f0402030606180703050702010608 66
    0x2e40c130440303031030700c00d42c040303449100a584501c5c1c9241c045000d0f08000030070060790482c01501d40d80c501a042c12480d02d01e81c07807400f88822070203000903a1907084c000300400300c101c8102807500021070b0640040380c91401010142c110741d10208034200e12a0711400d8000c1d28103070300070083c0b02c9207521103841c0c07807404581d42c1007199040300c0e04d0280100b0b413600300c0402d22040301c1240e0500c04d00300040032110400c2e20a8059800c495243c5507140c90075901c07a4141c504405400101d800e008101c6070051109001ca80e8201e4454041c0d0000304102c1841480500002034140c0c4803200f182c0d01c3d40d401107481d58501c00e095000c06589a001800081160443d07460030030b20703980e4603440c005a54200d8244c201d0a02201c070b100303070300003108202e5a8401007680030444114801071031111250850010140c05a4050300e40e109950f6410860740e6800e00500500540c000d5003205c4403540c54400b84411360312a00440c0240266410000b059184130f90040d170340c4a142480045901b903074621700b60f031818071451407002c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 333683093 1250 333681843 333681847
    0x8040b13081c271a120a060f030b040f0f03031407030507090608060a03050303010e0708060301050c0403060c03060f0605070317060f130b1306170705011409030a050304080102 77
    0x11081e8204107040381070a402d118031038400080c40001e8a40039a41000b5205100004800440305040c007004100800f221000100f14802202e00784016a00032140d4084994800300400c600c03113900e100701d0095940ca9684508103508540340c2c0c095107003000703000311100039030070300094002003050710380600c030f54840d072008254231000d03034990703009010003d180f1000c05152504126103541c1c0800300303070304690703d500b401850b5464440219501408036000603020344400000018000f445681c4035205003d95520b00406031500c3c0e00309401d0358001d4a400d9940700b01808140701044465028850a1a00c4e04000540ca0781d580c40c201140b21351503010301c0c080b90300418020b05068001c1707180c418903105041c040a01d0310302070000840055000454501843c280340c003c0709002d0035070340980042c0780014441c8400e82c01c9406040081c20442c0620545c20f002e8034080c0040010006200e000d54805844000480c0410000d015042d01300d07031a01c6078184141040075010440505c0100043c107003220000d6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 333684343 1250 333683093 333683099
    0x509030a1107090f06180e030301120302071706010f0b07120f03090605040b07030c020f0703121403160f0503191503080309060720060402090a06090218100c02060f0708040b13 77
    0x841001034032000a500306c1d04000080782030391800301c202e03415101111405201c00e94503081c00c03480d0000c560040e0117480b403143c010300c60590340091254122030711200c1da19202502ea40c901c030300380d02600300010120019122801680c901901c010716200c455481c3c0043c584020b07480e0381058400683e804d5039101d007102c0038059055410300450380b0510407400141607080380544060b59652261101a103045181600745c0c0c44144180d0b000441c40540804c0e007500d84c203200781000d5001400380344050110780c016000315178081c0100305807480f03005624025400305a07041884001303403212422001c0c503142d0b03009000c40081c8140010350f01a03800c401c0106118074080502528000030124601c419500800d4070700605c410000c0d400d540300347e041d5580d07009611140901c1010b03207429000717607809034008070b800240341d40c030b18405500e4100101c8540e0060880e414059480c00128000170750040380c1003001c2102c1100c1440240540e5204030981b0b85406e540d0408000780760050060080c1c1c610100e0410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 333685593 1250 333684343 333684359
    0xf031005070207060504051503070c140115050a03080307031e02040f0918050601060e030c15270d060e03090a0308030f010812071e050706020115090509030a1107090f06 74
    0x160041e001c40c0c01c5c124a464208000500081c000c01c02217841c0c1e4200000080b403091013000c0d00b4940b50340c041710720442c0d10305050300c0f01c0c064020201d00c8100250003100014041c90003405007400c90f500086103928644800d002240948441c03011303020b90030b01c515000c4046003054030007480108400c000b00041a400c04a000054882d400c5a03600f2050f107015004011900c0403c0d850f0444403030f0305041945112800100c5d0510b454112039590151000021009031580d4800a20003880408210401b5141d09920304809400320304110f40c01c01643c410071000101180d100d1400100d81da400c4900f000b0b0310000040c02d003070498208a40c0c0d041c011050082d00440300f2542400740c0b041d0005069046c902410344c15040c010030034094041c10303504c0701040c4c0b2880c11808203550144c000301940c1c0000d0b103c0380c019018200ca0f0003080c1c40800000000120200e16101e9103000b40440400b6600e8404d0000023160009a25003440c2c02c10700981e480054035400c0c912840031159560080441c8403403401d410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 333686843 1250 333685593 333685603
    0x26060a05270105030304030308070c03260f0906160e0a0308030a02040602160e040f020609041b020708060610050307050408300306152d1209031e03060f0310050702 72
    0x1e0700a40c03046c0010300c00280c018580075840200c510b02031408a03c0d03400e007112420ba000c80c101200b6903a16480301035200346900c50b10710070444034a40711510784034156440c0d030700c1d001101d030310240605085410306110711400e10900e0080000341003030400360310b0340c9401c0c070558010703202c4000156002804121146c0c0520031400c1c00e203003c5015035005032500507851141000144024128142d40305007008541e41c1c48207640c01c20601074400c00811409404c4030106076104448600584155000041e0051000034141d00c2070001522000341e81441c00342c1903d103504080c0c00c030014000284000b11348400c04000303042c58214400807c0c2e980d90f1000c4021026091180c0011181100401c10005035441d95140c4646411001a180303a4549000000d90009060385400a02007038148100320b9002c805d26001d840d000c1010800c1d9045a02c1c7c21368050ba40c0e12440d2030545076440920300c0b541050950b000959844000905a50140e0b0841310000b401c141e048100d52400581d9881400070440d81000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 333688093 1250 333686843 333686849
    0xb06010207080714060c06090a0b18070e0709050d0803070815010f0c0302010b040f0b03010c0201180b040c0b030412020d0905010212072a031226060a052701 69
    0x79000e00d80c24008400d4561103240a20b42c1e4460340c8500b00c00c0e042d01c885080f54211080342042e980e96052000d8002e40702c4a1914094901300c4001d00442c20404455040c8011440844010421649410600b06805c1c600070022414420b109a00203400c2c2c545600c044500c038882c00005560b440d0035140542100c0b00580f1700d01009141ca1743d41c0c03040d030360005402c1450202606082c8481c64142c90101e01500400311050340040c00c016a507039440300c00350012100c400c0c00310300901424039240e20032422a00f00e500030300e5400d11010082c0b40414405508140c006004824127019a40c90301c48101103680161001c4178403007901c0318491380711903040c02558400c52a51600110a52804000035907600403030002c86892400050172004100c8001c03e18040764103074403810184400c400721a440c24504612040c1c038422407929240c040c00b0301c541183d52070203040113004240c003c10a42950f009003c0184000c0d0440190903000c0781300d6440310012a00700403000086400d24901804410f61240e06034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 333689343 1250 333688093 333688097
    0x60b03070206090a02010f080604061a0c150708060d17040e0a0b040606050301090c020f0f01020705070b27010c0b10140a1518170c0901060c05280b0108010501030b0601 74
    0x80740d0741340181e902c226200a8000c0070310b042061078940d0b00c00500248140da01c001e034004070b41020307080079000200c0a0850b0488000a4511380d000c06030240460300d808894620000b240440040c10320314080c84152405c90291101040c030340128482c0c01203642c440e0308100c84900c07568003003058042c00c50041c00e58881c4180c400307000041c50640080c1c241e01042c003410407500c1d100d0203c440640e10800c0092072404010046400d41540f909166000398800300c815a040d01506c0e2010070700080c00011140c50341e120891002d50803901201030307844a550300e864241008960b0103054080b40034002d04a0140e04d43c0c6584000c0740d0702d40304070042890302581da440d021300150780081200003481441080d00c98102e0a028243d01c40c04080b00c2d590090b00e030012012580c20802009020000045060705a401544d1001090f625a0001d403100d01e1800300040059010352415180440c0c21a41c0d518031340d100000c40030b800c0103c2c1d605d42e07020300400d8014040c140c0d542c00041051102c00640c072a0003110038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 333690593 1250 333689343 333689353
    0xf0606090b01200309030604122a1b05030d080a0605010f0e0f0f0904050105040b01090204081e030d06030809101103040e0702031201180c031a01030906090204060b0307020609 77
    0x40341c0040c000050512000d0159441045030380c50360a010300440d48801c0c0014180d4030306140900d02440c0c260140c40001002400d140f1080c1414155034030390514103501410860760703031281c40e500c0b0314589144001d41c458540c3c656500040d82e4604125610a144041e12281c0e0680780a000c4071084410650041d41009002103054a5243c0c0140800d00d80172070a940a50f00000303418046000c5003190070701c05401c164004108018410194001c5001d01e2141d0720005c11079990f0340c142c3c0103038040c9001d04000e9400c182071821f402041c0050444168075900203032401e00404000070000c80718954001d494010002071074030310038504144004a02700d501d083c0484094210104150b42e40614044e2480d504807010214800f24020000c0e00d881d803800070640000c541c0c6902d04400c5c420701d034011480c011410142407440e450300a00a280583d407560503002c03074030000c480045001e0b21008805a07007a90380c0d11031110141c0c81c1d9028103009443c0c600ca80035501d0901810082c940240117154400307540103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 333691843 1250 333690593 333690611
    0xd0509010c0212070806070503040309060e010f23040801060810050c0f03130602030a02090117010503030307050d1514031002040f0b07060b0d1202070b1315090b03040f060609 77
    0x220392442081e019190742c02a0351090f20660b1600566070420340f1144a15000c0010159100004610030340c445c0d560284184d5652905403880c00d0304062090100d91620300344c41e034091184101440c4007180400d1200b04601c2c450419107940c0c0590043c02040c0d44680080c000000e080100c00860100404100810b01c0c155443c0c0d000341c059005894072000000012982100140c1040003810781c12400231580c13800c08114034002940482441400b0407801c103040da10340010355400504a490203006140786507141c090880d0550b02404e69030444a5880384500b19020744417190384084e0110443c9039103e90729850416140200802d20410646d00400090095141074000c0e04c0032100c6110b800e80d00c1d01610705e01640500125409103401c070154025900078024031802012503140d198007170390031081d112800684544911451004103601450f000c0240303802006000d01e0700c0341140350a19541c1e0712503510013010390003506c0c00c0c0c40c000300407881002400309034824803008100f040d80030050080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 333693093 1250 333691843 333691847
    0x114070f03110903030d2004270e100e010e06191404050a030c2a030308130206270d060209040c030e060f06010e0301110309011d1b0d06020c0606030d050901 69
    0x45003080c08042c80d910350747d0703241681c7c50444c2e00301900444980e4903030320ba9454102c0160002c0781c21240e5031454590740342001c0c20503968401c450601001c480a408044550b003051740103040682884000c40d980c490300090040c1c4203016070b500860b1007409a41280d64000c210400362241a090140ca004420081c0000610002040c22085074141002e45040665083c081d05c004103c2d00f00700e1030450300c03200340e04011603080a8001500c0c070a44031050543c441040340803620404005c02508041d007040055010b4104a00b0345008040850841e0501c03020701c0f0124000903100c017012925030b40c01080359101450a4040e54041d103070302c0d10301044810306031000d20b0b5640e440504001498600d0102107034a591040c820f0b2005801c0c040d009001014140400305490f0740100d4550b01d10b54641100e00e040130541443c41c2c07a112130b00500408030555010201009200b146141d50780c0004000203920010ba034a00103800e00c4d00902025001e40d1401c2410b0600300000c044502c010004100b00e0000c0b541e03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 333694343 1250 333693093 333693097
    0x40c050f031011040b1c0f021602090606040b120714090a061b05120a09090926210601020c1f0e04110301031212060501120b030114070f0311090303 65
    0x503603034480441c221a02512000c3d452203141c00c40007844d580020f6180ba0440c403118041401c0450720780400c00700c1c1d07410040008a0017150411400c20111620324005444c0050f03150ba0850001043c0c24945079803500b0503007150340101800440c0c00c000e0707004c0159003600501c42c00e04240d2040c0e40c0a16111450000034292106030140b10706104a4619240580c5001c156186a496110040b80c81040e00d0324100c0b00950070100840300020074400d004640c2c11500d00484102d6030344403a540a0410646160100810504002041459080c0710030310100c1c0c01d41d542040c002014551640060900c880024141160284201d0180580b0013001041c00301c0110240141c03032040c175083c02140d40304d40c0000c024102c0350310100c08076080400003005010702658000c054085544402400300060f0545005440080c41124007060b80d00ba2849040301692f00b0418888200400000c1d000001c070b141003146001c2036900b00000340c40f0b40141c04105070507104060b1132600d02080340f810034180c000004e40d01c2c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 333695593 1250 333694343 333694363
    0x60f040308040602210403020322050f01030c270e010501030e0a0b0613110c0d0f08150a091a0111011a0d02120d0309030e0f03030d0908090307030308040c050f03 71
    0x540c00115145c407516031003041641c030310401640900320b0801d0b0038001d550b50441d0203d001c107a0340010014a03003604001c0d500c0c0c116031025000f6000b620213900150010404000c81300c09114a224401c906669030f100b500f4041da643d59195403c6031b08001620204810580115050601d80448241c803102c00154074400c1c1580700214003800d54802e000302d1401401d00014000250400541c040c0444034200507200c0c1c1c440b454100d4803505144441102c3c85c55a1581d1040031820070030101d81540c46c03031307104e0b140c5c00000a8647c0151030350b180400c0c0111906104031000203040c524240d4070940c2d0098800703c44406150003848100440c03500030464440891042d840341d990f59060200315102c00c1c404141090424040d42c4c0d642c402c104c80540039014100c2c003200040c9001c1c505c00003614000c91050035510700500203505021a80001400070914060107407025101030141010b185e50030840b550140d8403c2c3e41d60403103070034a850113000d221a5500400e01c10350002c90a61580d4800003562000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 333696843 1250 333695593 333695603
    0x20306182503110f09241206090105130b0711010207080d02090a060305091b04140702060403020f0d0912060905060130080901120902100c02090a1e0c050d0c08010305060f04030804 79
    0x1500e00340000c01044c04007035403655049441080e0100c1000f0008c00d100c1d110b08a1280280415505d11180a04e0082143c20080c42a051138000c00d00c1c241c425040c40001003081000146000215110706402d0380043d24505c042c4c61300014011410b082c01c070060b02c01071072241424401c6040c24158070352240c0804c12008858005000291402da0740e5411000e02024405680b05c0c8504010600940700d00044800381c0c01f43c815680e00c0544c1140008444851000581d1101c0c1001d00b0302c1c0144000c4c01c0c080d8803e4a1868485280c48042041446481d000b00800c01d440301303840100d01c80400e0f8400041d0008052407640c0c0441a010842c094100c0d04100400d1802c2018580301c0740b8005c008100c2c1400294024585000c0301c0701c20740c0c2102c10800c83c64000c486040b0142d82c0c4041d14029940360705081d4003800d2592a0f4000403612a80145a000c1ca1605001d402c04240c42e06200880c0c0100c4503040000714044010001e214090015580003400b52000c22024500343d00c01070400c0a024200800c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 333698093 1250 333696843 333696871
    0x16020c0118120303060302041515050304020108070c0f05060108030901030e2a18010905180102031b1c02030a0204150507030206040201080411120f010c02010603020306182503110f09 80
    0xb00700b500c0b030341c080c9029540c010000c111031240e03008a0341c2d08000c54010806003029230030400207024064400c0e81d100d0740e8140c0d03861030240d4440804441c6a160042c040300c0200c04902c1d0440090002e100050203024800004c42d280c4000ca4001810f4601030390000656402a1408441c0080b00d090303503244e00303c060b072140c4011070303401d40c04915080b030400090050075061304008100000710340c200340e0154900c007404451050380d4550080c01c038030066070f11180b900204400d161100c0d5a4902603c604442c1030090754000d400e88880000313a034422501401d0f100c3d400039003403000308a2178400f1070a400c00c0e81b030200e083c0384042da406076650300f01500282c140800d0400180c01c0042c51583c80e800d4201c05400170000008000400369107001403480141103500380f07860029042d105100b031404980c1c0042c000c107450b4440b040450311128482e005448d090148000902c1d00e04404480315501500c00010407103858650700b840810a900c503040c03144220300350004260350b540d41400488e00484000c40f404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 333699343 1250 333698093 333698129
    0xa0c050c120c0a0f0606150e030a020405190603140d0302072a0f080606010e030d020a110d1a09101b110a0204050c0c10090201080c130e16020c0118 65
    0x183c90a00601d41c0100703000100c0002004100160f040f410880381c0d80d2082c0407400407100740039184820160041901541300c9e0800d80007500d4036400a58100140c08031112088007001d0620303046c1d603240d8000352409040545510480c0c0c0040000306140c02035490114205089555622241c0c81c08019403800c44100c5188d4480c02920744181c00d0080c03c10b006915101c2c2e9079010f80319100c0e20111200c9005c5a03180580d17203c0b0381408680124180419405410265110380d40e181c410554007031602d820144440c2c8940c0000d0703480480c03034001141d0001d101d4040c82e100002500e04480d6440140baa1400c001201c0c40700c0c2c0c007c0700c0c2c107100001c06003404400d02c56501d000b1480c140013880003030f502c81c0c02c0c48140941010220014420080410251800700d12120301d90420b540c4900342c020b00040d20708001440c01d0808801401c5240000c80c45c800380345070703034400300c0c0d90b40001a544904c3c5a00300c0d1880044950f010085542800b80a08112000850b801d0141e00a20324611409030712030444e01d421 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 333700593 1250 333699343 333699367
    0xe150405070f0f14040b03120a0302040e0a09021017010303050d09050d110c030307020a060503100e07030c030e0a030905010f14131a070c120303020417060a0c050c12 73
    0x164090564003900b48040e5641d00c001101400a0b03124800c0024074807804a89141801c0c016070000341000f400510f4059111800c0340541d03805164a0420180d09000204031005000d0700107000e40101ca07404100c003800c900402c614020b60b007084506110180314003550a0422000f2181100c0c0c01d4141261500c500c00c1c1c034280030380003848005106008403211041641e0708460b600d08000108400c5a0078610500e00781030303483c811800003951054a012041121070300c1000290b0b07000c1c0303102111025045d40c40001c841c411000340e078110086500c44000002440d8148120a0803821100042c001c030f08150328040c20440300c42c05164104490700000429060141c48500b0603c8116003a840c0e40d001c2c00d0305484140d150ba80110b0720451503120346181e035048002d0540d510b1030780088922203038600d0045450036103519120110249a001e000004102c0d43c0c00003d07003900da100c44060b00003880c14008540888401503203050602c0414041020506400203600380b00c014403020280d07440d00a0340c11 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 333701843 1250 333700593 333700603
    0x60b13060f140304300e042307030b010e0a031104050a0e07060512070305062803060513060c03060803090409020d0c061e0906050702131e0911040e150405 68
    0x1964420306000000e201c1004100024001c038078544444003845c4024005c11240c00b818503000f071078001062040718003010b10b4603501c501c030581d0003c00d488200d1020f030300700d2402c40078088440b03501003582c4001007191560449102e0390701c1881110f101d52402c2c00d6030b5608281c00c000144880c02140c4d600700043e02c003007a644c00304c080c3c11803100032903100d55a603650080041e4029000861942e4111011a14450003030042a0207102c008040c603902e2908160088135030104041118810361210700000046401441240c0c080c01d408030405180e41021304000d015212031400321010507252150170050942d000c41590b0001c2011200400d035081d5a0001881c2481c400074040c220180d14203000401907040005519000740440103840190740d10790059501e1900f900c100408240104098401843d110b01e20b0030402c0e61030700c0005581100c06420700610303800340000c20010b990381c070912020b0041d200c400100d0200202c80602c07021106080807500d401002135690346441c41e66012600700203007485 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 333703093 1250 333701843 333701867
    0xb04060f1206171b190b03190c03050901140108060c070204020d06240e0603010e0c0d110414030703020d08071e031d0f01080c03061302070503090103060b13060f 71
    0xd1400f1003441120910341c41d4460072040d00111855244140302c80d06100030710344140004524000e1190340340c42c168a041d988000c0080300c1001047d41000300c446030300d10418800360083e580010f150b260000c0040e085508a001c000c005005000040140140c0014640d503c50304181c0c116480c3d0300c02c1d101080190203001103001d4114100300d1f0209004094250307403520078002a0485108448945098518060091030075400280c10001070007089603181015403c005984442c520308061600c04c40304540b00002c1001204500140402c1a08503002c0c0c5030031001c40403805010410310b03641c001020030301e40c4240200801c40110f641c0c0180206c5844900c4006190100310400e9602407030000d00c445030400e8403141030b24074030550201c582040940d00d00a031406845100709516500e805500d290401807580b42c1c0081c1884811a0f16941c50000d4014107200704011500c508038000003405980b12a000ae0300451020b0104819000b911041101207825a0410306e0340311038482c100b01c0700c4c040040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 333704343 1250 333703093 333703109
    0x121a041e05090d0e12070308132105010f0c0518010903080301030b0103051c02060f09070506160b01050105130308070303200310060806010c2d12090b04060f1206 71
    0x901000600d0b000403940c0e4601200990307130010340c04044400c0110414158103c9034107540403003002d000151078480240450b01d00b088084807031a6440305114407100107191007000c1c1c10603980c116400c0081c01d018400340c04949038024080030440d010018944d000d40c0c10403401c1001000300460041c1d0150710294040c5811203041a80c0e0740e16030410700540d400a2008440c0e03841410450044060b22000150540300143d01912480d25201003003810400701915481040c01060400186592204000e0400c096031210060310351006003800f01200005901c954148103040141c00000d0b01c200c1007010541c0e5012419544413012410100e000300f00c00500209140114021040d051200c100554800ca00003048290303425181c06080741c658400f51105804030f11102e60030000220b554443c1000161441b01c00f40040c030100400003c5282814415142c4414065142145561140c620307005080841c0340345141c1b0741f0701803004055460f015180345c20400b8020390a203803005c0941000f00205061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 333705593 1250 333704343 333704351
    0xd06020c0706051c02070305030402060903010624091205070b0d0e03031003050d0306031e080f030f1e011d09030c0f1c090b0702040e0f01021603121a041e 68
    0x402d005006603100d07403a00c203100318502c0ca58861340103603402103c40c15941584d9183c20b5442e0395080c096240c12981c0d10700d80c113541303a0401042d2991041080007030400500d1110159040c820005489a2400e40290310801c03d40091100401d1000941100b240c250140b040e80d91021009814014140c3c601c23400c100b400000305100401041820b00c4050324020401c0c1c44084074404401d408640f21171100504007100c440c60b069508100800752409a405603409914090b045400745002d64000c81d903a0000341c420b6401e21080c0507400c1042c0d4140c0da5041000c404035410305110320348000704541c0b24070100c00c1071800556030711818406d890300c0c2c81004d401c4407841e50300c0300d0441c1c0d1100302c1d210190807503030780c0b600618019038880e110348401c9544035441a49403880580078440605140d03c25a4903070b100302c400c135403c411400d02c010403070400c42c610742d1b2210301c1503480c2c003e040c0c01c0a0181c4059107400d00c40d9843c01c0350400038080d45824811074001503580c90300e02040c00c400050403c90341d031032807130 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 333706843 1250 333705593 333705599
    0x708060c160c031109160c1506030f060501091506021504030905030f06010311030d0e0f04020417060a110909070305100b0705010e0609120a0f1205180d0504060e0d06020c07 76
    0x401c0303c0c034944420b8100c4501030243d44180007080c9854648003d1000180c030280c0c7c13040031510015030304c00c0815001e00040350064503a1034207040c10166540440e14203079140d004020b00e000030312078903124003403000c946e4200c80d2920100a594050032584900c480c92044017040c101030003030129100408002d03090318080000e2642c490b4945000748000d481d0414140b0010550345000314919403c0c0c091a02d034501c400010340c0901c480b03205c203207507100d8100c0d90800c00400c041c0d40601e04a1201d21500c0000c0015180c5400b8000c1500e501500d00d5000501c2400f846072aaa00d0020050307020300c0d13500d00010f8a9949400d41001100a544011009400004c8401c14810b042d082203198028100031103c00340c490540b0030350340300c04550070b02e103007050184030050318244600c0c5000c0c000c01d024541a15402d140030303031441c102c03942070703460214450341e003a000c2402460a0201d41c0d0340d21482c0c2002820180360610141042c155114070a2156440303801b402c00700700c000e034151044228042c3c1110000c0351 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 333708093 1250 333706843 333706853
    0x6020601032303250507060201050115080c25050115050603040b04020406090c1d030f0303041502070c0e06040c0806030303071b050d0f080a020403031b03020f011401090e0708060c160c03 82
    0x4030a1300291400c6c003480300003094080c0140980c81c1201c10800004628141d0840111140710000c0e00c490340c08802044100c4a441207000e450032455410031a04424a20038a0451300b15003180b0103545003c40140c2c0c08021940e40c86003620b9202c5d8000e50341007103039551840014001d2216070412100107162504020a83d980310568214660180010100f000c5003081010341c0c0d20340c03804007561590300070400280002c1c400c100c225022080740d80c0c098180503082e52000c4031591544c001c00c2c00190305a04224040c60103001d940012406420156a941000f602098a81c40010500001d01c01c400400c940b8403500d0804e000041ea8000050794600d10041000511021041414100044802e008030b0303441c3c038140c0700b29411280d0540f01c017081481010800c42032204c0d01c1070294151f0150500e007200c00030080c002c007240140340c038410562540c1825034031402c40d240308084030510ba200030001c0c03110303620004146402c010801030302ca40f81e0fa0340a21443c210380d2010b50051400c600501c001003001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 333709343 1250 333708093 333708157
    0x102070b07090503070b0408250e250c11010e150706050f01051903060903050c1e0106060509030606040207060207080f1804050411010804020102011d0a0c06020601032303 75
    0x15022000e0345c1c0c0e2259500e8030300455000300c1c0112180c1d0f4001a401c555a0b910100840d11540d07030306842030001130358540c01a80c0c40d800407100c080124034002010b8980241c208110b110300f944505003c02d074283e003900e541e82e100e02c800605d50f0521080520700c0e5510354640c1101e8501980c1d07806905d90b03842d45813600802404042e205c5204030f4151100208052805034103220196821300400c1d03094916580340c0318080c0c9003181042d81840020805c005018605222144240d11155034034001002d10228150031125140d01900400c20b06002001060340d000c00c034150410804c0310051384484c11030030907070020301ca42c01005004107000a000c00b4035100f40009405142d80c0c0203684421001060300344803d0700c40460b80240401c81c1250080d0322980600c0040703801c1030041c07000080c2103004c240580181c100c0c02c0002c20b03480c6d0209800100f004040d402d1007010300198030180c0031079499641d81038440c903002d44540c180000d890484800350007040094640707000e12031100d01d40d81c0f06c01e060241111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 333710593 1250 333709343 333709349
    0xc07090608010e0316080f09040c0c14030301060903030302090f0301060e0702070b0f0421150b030618060c0705030d11250503180d0501050711150c0712020102070b0709 74
    0x95401d03c02440c1000c000841a42c044107410314480c00c2000c0c003651500e440f03601c4041c219408140c01d0018002a4969200d0141d00c0e003c107868280f2407250310f041c25070a816455142d4a107030751040005000d13040c1d016101070b0072aa0706027000343c3c40d0460b03c000074800c2c928040101d9010340ca00080005c00007001031a82c4c0c02628250281d540da0340e140e40703100005203d8150340f05008102080300b08012641c0000403800384901e4240303444c2c44401c5968107100311008e04a2001415101c02404410b4039040c01240d40000503071205008400000c5102030301d55000920040e10044080b03241d4041c4801403003201c08140d028072003003240e042044940e05070b50b0484152525050303025a06840307116012180841c0e86d507000f000542c01d1501c140b404400e42e07c8010400e5130001d5010030841c001035000d006403030040f0f01c240c031160180755252461524003000c8121089101c1811402e00c44c500c00c03902c04407030510742c001c441c00c2e41911b00484281e001e4829684000e004a80605c10450b2103a4000300c00c1c810303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 333711843 1250 333710593 333710609
    0xe010605090f0f10080d0c030201200a0212071e03050403060c1d030114040206090a0905042001170c07020409080a08040201030605061c0506030120190906170405030c070906 76
    0x1030784e240c50200c8220000c0c01e02580da41c66000030b20202c200c5014003000e240991191002044482c4003501d21101c004041920b0b400085012500d40801c58062040300022514243c015040410544421210282c0c100c40194558182403c11050620580444018580000c8240080640100d004004444a0311440040d0b64000956290361034103004141e14028580049102a103640c2c081201e07170f80c0f05100c0316900118130304000401141501645200300d0044503011034240c030401c4070920054201c4611410004403000f515040301420141d2500091820402511101c41d840810010542c040d000b500e4040c0c00306100701e08030360003084144a0fa2007a64240251a5180223111241c081d5145071004e4012802503c0e034a2152503102640c001802800811001c5000880811145240d1841007182c5000203954080b002041c1c00980c0302082c0749011204a458240b0081c484807002d80c0080200ca565000300e81804010000d41b0014540c1d0000e480c800ba0351159070500034500b07445051030b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 333713093 1250 333711843 333711871
    0x303100302100e010206280f05010e100b070f110a090b130501140906150c06041a0c030c1809070504091113050d030c120804060b04090302100e010605090f 68
    0x1c0e000d0b2061451040e0200107800501c00e907200c80250740d025008504240c100c4420900c4058012081f03401801400c050038440011a94105114400e203d00c0050861900e9100d034141044060840000c8032100d64010402050440a502e001c5182c9000b011225a0014400c4c50210340584030354845079000f80210303180d03810801c40b0141d680680d2400d10a600c02c404040b408903211341828109580d0080c0e00a00401c8801200f81019000d500008580c00c010380c0880100b20030080c0d00c4820300c00450f00e180c10041c0620304a080003509110042880b5510b820100f994283c0320000d4180f030300300c0c031401843d40d01c00d480c00c610300405c0380e04148607403210107003030032083c552038581c200132200707504000320682ca001828a418480450314603681101040064609540415503882880b00244c0d007a954201302802e1600b0b0420550f1440840d0520071490300c415a00081d03000101210801d0700741d2004990305070345500c218010032550348183c0c4c10580910421185400c820300c4907104222a8040302 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 333714343 1250 333713093 333713119
    0x81c0f050a0e0405160813051b0a0510020303010509150f04020f0d09050f012304080304020105040f08100f0e0d030506030f06010311100206040f0206180613030b07050703080f06060c0303100302 85
    0x48851f5100da0800b4009401441807003004030241c1d00440d01700c0ca40542000d031515621004180c02041140e655401604048018880c034600f000b00280c000220158000c04005c5030000079102d03541180e40d19204550025002010154030015105e1054503107804008519007400c00a48801105a50751401d5180410094031102ca6450890035200004080c001039500c0343d90304812584083c1c0103038188442800001070003803440c00658081e1000310050014092a21107007019611a60100c40c5100d040242006c98042c001070b0345040c0c110145004103142d15440013003424241d801c0011113450146a0010040c404541507801041c030041d0b03299140b4200c4030800b00d84501090f9001490705d00700c040220050719044c2c01801c0c00e10200342041c00080e4042d400034000303602902c0c3c51140d4002c80d00040007072204258069a20001508025140c0b041c9540c0040260784020100c40842e1907030b07400300d07049032902000e540300c0d8000c550880b0394a0a055002d004141c1851200307c2c401c040c100108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 333715593 1250 333714343 333714361
    0x2a1d1207030b1315051509090a02010e01110d030c110f01061d070504032d0308041401020f0d0e0c040c110c0406060f0804110303030a06081c0f050a0e04051608 70
    0xb110040b5040800e603c05600113601c40400f070140070b0000c2980c0c40510003000f071950385281800d401020070f64002c1c01d840b0051301c00501070b1641400001c2c14024114a49500f86034042081e2071410042c7c0740c0041c0c0043c01e1181611140c00721940c41d091071150b8045030045880542c00700c03045d40d000e0300d01100d10340c0c815011011180c80032101c1100280c004d00007040000c2c900703410504c1500803030030440d545250300250203007070081c0042c0660000c0c03000320510007448800c40c200c940c40c0c0362000c020b502c1c0c40d10410001250b40704068404000c29a0740c2c7c0102c03a0b00354103000500c0362500052081c00b04401a007401403260514a4600030903000303400d84038815103002c0c0300754812111941c440544c181c060440640301901c0007801590610054200c550850350248015841807100701e81c001103043c20020210303e4010090b01d225010b003104423121140742d4211a59060714111417a02c17540d1141c4018040b14500c041d046019081800d003001d00c400300d414407000c020080160b540c0c44c006a0750700004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 333716843 1250 333715593 333715621
    0x1b0406050a05210a06060303182d0b030f01030203100605030a0308090c120616090803070803040c08010504050a0b1501090e0705090603040b09012a1d1207030b 70
    0xa040c0e84032180400030442400e200540c914810060f0b0f18240e8490b940308001414240008002c5950350740d981000c0c0105504000003000005080c01507400141c10f107007206948074503202400042d41546c9541085107002c40c5280c0000c0c041300c1402c5c9803641802c00881e4508402130104034480c0c0500311314001165154440d5104907400280101503c2c40300c0c0c0c4040e2100040640700c0b540c6401800701e00300030707603c031250440c0d5800004e00041c6031a00c1c042070070482c0100b42d61005001c004402004201e18100001620006904180802c1d075036212498401d0364001c07941e02104140d428032041006210020640300c0206000d810410116a5640806010a01644c1003d03010846806091040640400d41241c3c01040e40c10300310302d041041c8000640030b030003c075412218400a5003c000c54000700380103e412591800c12454070b10b40d8014101100c0320700a20b00b000800254600c441c40846000c603070022500700c082e1000c4041101404d810b83c5a04c0540820b8910b5090240816189051810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 333718093 1250 333716843 333716849
    0xf37050105180702030406050d09021008040309290c030c1203010302041d0d0e03010f0603060905070515030406020309011b0c030906050a050a0509030c04061203030e011a0d020d080c1b0406 83
    0x2011754503041c00c0810580700340d0052070380c480a81e07076150040d03001616040ea0162200351701e500d65152920f0680347c0100640103540201035500f0200000039000d2a00000185501e04011003840e02e8085030030301c0a00c1d602600d040c040c0c2c9885000b00315107086048100071816a17000f6201489000c01301c00c0b10780e01e401c2507902300342c20a90010404040c81803043d801140d2120b8002c001040f07603400d0460ba1010340f512500103440183e69084d900341040420807421b40180304c01d482115024460811000542c0001000548581e400100140400000390b01070103000c000a0030803030084204960040880d03807002021008501d480c5404900c0340d002c1c50a0300c4e204007140d80e0715803a103d818802207030a40c2084c04d516415101d2102c40b6005581c450103400050718144840301c40070749107420014190303000301b60f144102d80d1404030390107003011b25550419400101540c085d5040744251001c01d43d814604040601400c0c0007050507a032070704011818200900d01e2003c0c0e40710301e05011081104443e4944 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 333719343 1250 333718093 333718097
    0x1030b090f042f031605060906031806040b0a0b040501030519030e0402210708040c050f221a01050903030406030e10020d02120a02030f370501051807 66
    0x38a28200c40c0308950348144504940028107001d4805801111851400c0142082e90f691099072141410040042500000d02915840301d150201242c0c151044032a418011940040001c6480d500d110b070481100c0c4082048810a203424101103013059810b58580c011f80b410100880000e140a02819060b00e03007000180500e00034041884190200c9240c0880600101001d2039005aa0f5440130304000200711020910600240c0320001c031010b8001c05980500c40d82c41c0038031001c038200010260940700709513641040060060300041d00c40d01c10301e840001d04060604240d00000440e00040b1081d091421107400743c2d584103006407250701811220039007590050108004181c4a90081034444e00c201c000c0c1d805000b05000440160b030f104003c0d43d251950000740401001348140303803261b1301482d485421811820601d10000040f50060b101c50070f043c01c18482c03082c02c0705034180c1c029202c02004002e2640081407102c01d2020780424800c50b8810500c100b81641c02d588145032041c03041081d5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 333720593 1250 333719343 333719359
    0xa050a062904020c0109060e0a02013b0109030f0f020f011103071e0b011e050901030819050f04030b09060c07080417160303171617061f0c1101030b 65
    0x41424840290440302403c130300d941d2111902c1011070300078401d0380c03c40050038015043c90041400007401c41c0f0301010048900c0020748410303002a02220924040780d910b01c40c240c4080c0c0b01540c0041310002000d03003024280d502c5410651041041680d8040040c0d13100b0340b81c0c12489108a001503c0d80c9282504ea5582508200b00f0440011011034800010251020700ca8218400039200c4a80d0108242c0040880c1c44441505081450141051a00802d0b00302d4054139190b045d0741d1100c803580202040c180f030000704004d134600002d0240003035481c140110030100d61030f20340d01e0610000c801000c0d1003011141c003a040c0401c111a01500407280d0094000180c245068644240c0140b0f000714003240203514000c0c1d1060806400e03e240a843c000c60003941c0395401038049820340250307004090802c2211504078200c1c1c0805603080b4444140c00e90515003503029594804020880c0350b08103c650314166405002075030740e80340e003003608100d01d40d0040c0c8884645900c50801502202d00030702c401a481584 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 333721843 1250 333720593 333720671
    0x9031509060f150608040f080301170105010504150501081e073b10030605030109060617060108100b0d170a091406030a1107020a06030b10080408040e0403020307050a050a06 76
    0x25005d1581140c890010a40c43c00308a4464404a80080e00a07612201c001c841054189409002d0340d80580403c40301045541032142400807a007659201d01030600c00340c42d00041e030151407040c503c0d0704080d05814040141c5806240180003001810450005840d60090b0307250004100000350400e2403034036038020340c280d102c074104112200d50343c0c140001c150302e07068041201d880038014003500501c100c102141c841e080ca14130503501400c0607441003590384400010402c4102c0012020360b820044c03500081c4002c00400424034034100d4440240c2220300000c51942442c00740e10060901c0460f980e566437240e9102c0841d80700c100302d1002042e40c0518140013040310312000d0b5210405104071602050304c1c0005c075a010070840b401d00c2c2d000401090303580e0149062801e003107442200010140c54111010f01e820380d02d10206009901804188849a20018003018000c008503451641c100040ba00385c484117250490b560300350184125131442c2004181c004003d070452920a54094130401c10303041d509 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 333723093 1250 333721843 333721847
    0xf0409031809051909021516020a050301050613050901180c080106080615010305061c0606050a05010e0a140102032a070f051f1e02010609141608060109031509060f1506 74
    0x30351701c40c0590f444403c5088160103031101c1e42c010064400110502e5110a0700c6004100400d001c81e4042c1d80264140b0b03007003140300c0c0d40c1c10881e121006582c640010345500c50901d2140100704440c800001d501c541100d40090180d803000ca00700b01d80f50a4024400d40d84c03134902d0651a6401941e480c010701d604900240d081d9802034008544c003501c00342c040e00c00d5040849044121041041055035015950308080c020b50400040c02d00290400382040100719556902089800ca1503100700c40402d4090804962203a20910403100320544e016503184071002c10903c00c2c0380d4600108003141c030a110709d64000034290704902c0700c2411142e000b404000b541c20880c91200454100040c00c1c0104002300c03143c030f0715001c549090860b10000a50002603002e050030780190442c2d00600303c451200b00319404008424060038004008011340b40b8001a80e03498842c0181c0c3c50f00440e800050100e05822205ca200698031390100764094003403c3d0078405500100e20000c104d0740c03000d402d8213200c00c00700c0e41400414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 333724343 1250 333723093 333723101
    0x6070306060f050f090a140306160c11040207081308070602210903070b0a02071806260f03070f0b060a0f06031505090c0307140a0206150f04090318090519 68
    0x8044c01d003028902406170000039178048090700184000500c01006030f119040400180d81d100310a0041500c840d5001c40c0c01400003480c003480105540c08100500c205034503150182c0d00c519500c038043d540c46900f51021083c0c100d0090046001c02d1068050000301a4400101182c02c1e60340c54210429084000054800300d90000d0321650309442130b035000041d14880140208418038042d405018018101641040014485901260450b041c0502030107e80302021180c030101d44a00d5044008201030360615007000e20540340c040e02c901001c120b1405000d00440d010340c500d482501d2400c005e0b1340302c0007000b503444214010740c002c41c00f20503418803045009074440c00c40d403450310342e0000500e9a1030001032001201110307507041c110310201c00c0c482950740080ba04007001c01780342030050901d845104001c0d0780303510007040b888010901403214961621810000f01003500040c000340001c6a082c1805424144082d42203010741d1056240000c0a5407244a4a4018032940e14bc0c522a45180c84a44c0d02030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 333725593 1250 333724343 333724357
    0xf10051804031107090e0c190e09070f12110616020114040807091416020c0915030102070f03110c010801150201140f0403090b090d0b100801180506070306060f05 71
    0x10152100c4a583d208404012542c001d018032440401c3c45e003068000d560401c5c400072a454020100d08100c0c507060b050031110b1100b62143c50403640c3c0300f0782d0381011003032420030390794030042c10f01c00440307400700e02000907000109406010b01c50149900c00c1d0502031240034462a01801d240316415100e250041d803088a5032031800050444050819032100b880c5410031901380e02c07420a917543d4108440d1040502210241e1226015034040034641400b48041d45521b040118140b14240000001d91101c503407149401c5001c101800071501c55159241c8824200c0c8a900c0a030080392041e1502200751400207682040d612045c0d4690810343d01e8009204c030f0880113544140250354840548110018642000d103110b8501b0100000d59802d0034100949400b5844e0800040d00e501044812000e0302e842480c0e4001d50381c44803000e2401e03918620582c00c8200c0c0c07500552155424601c40c840502c9051158280903400380080d42d95a4881d0041503048031003d10944020802207013001c480a805180a0004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 333726843 1250 333725593 333725597
    0x601121a0403020c060a02030c0c010206090604060507030f020a08070306091112041a130b010e0c19030e0f010c030e06040209070f110105070c03080a0b01021903030b180f1005180403 80
    0x5544d20003c0080c0080c0c00103134031400103a01c0440c01c064040c0d030820884c2e006100a0014095030b0410701c0c20310381c0b9144014000b50a4544410200300d07010301c41c1d071084c6100910400c04549500c015003006003114016549038001906212012903000d82c81e11a50002080c44c401452904292205503081100020415120900c50000541181681910f070b0341c8111812080080e141c00340f450f00340c44005040e004550115101c208104c165002e1000b11002c0d070590b02e010071b4900700004022000f40c031710b0300001e88a900030b1114501c1200070540011800241948040c0072003e092480f00f99508401c4038045d501003061000300e84000e02800110200d2046460074442504803546021309403001a5a03440000d40d00074008814035a000e01050307040001c01d44203110783d03280b440000b5600d0703001c42071040c00e886030346440800b014005d0380070743d407800c501408015080d00c3c01640c840c400b0804031405044c200114001610300b81d9000004d100b9101d00510180741c55071425142c60a102c002002141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 333728093 1250 333726843 333726853
    0x4140402070206130810180b0c19030501060e1905060304020d0c0303021b0303090a0b0306040e01060b09012003030f0a0e1f180b04410601121a040302 66
    0x10150300c43c10024101d81c100c2d10700c050001481d0030521460320000074030191080d441c2800c100c3d40c1c8054a5551085150880488000e5480b0540d500701c031481076441c20b260f5038044072541c1c0801c41d01600624100d801c1600c82021000c050783c00c0c04003606080c0f0321117040e00117011013030080e441c00d44003035600f00d80051300d51140f64103030b82c4d504050940c50780c0007a00940e1114070340601c654038071070f040100c1c5007059000c1c5041c00d101e400450302e001c009014036080801c0200c00a600d07602c4036489171006030f40007030090022550f68102e401a41c1e116500e03050001d9280340700000080140744000c0840e88200f00254510b54920219000103980500141d844540b540300c6c1c0301e030542c4204140ca148a00800c1002e0031000b2070070002c01141c003400903111100160b81035410210f000d150900ba4440d4114600410020b0741c4c3c901c40c0b03035041e1581004100b8040c00c2b4155020403403540601c101500e1710f4000c035800b0340d03203980d0039228580400c50000c01408948403625042c0311400c0b0700035006031103801150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 333729343 1250 333728093 333728107
    0x503190e030c0c130e100f27020307060503010605034204050a0515060714060408040825051009050406060507051e0607111f02030a15060504140402 65
    0x3411540001c4000b01c1962081c8201001483e0016080520844484007048417000440c40e580e110072203203002c2c0c4061070b95099050854129034004220b038050910300300d441c00b80812040c1050144124040e802880303240300c0445c220340200200d0341610502d45466082d542e03100f1030b040340400310380c91000d64040d0705a4000000f0007416030f00d000540d0795101003d1b61403105018001240c01c0181242891418901408201800c10703c034042150402d660345a5100c0030b900348860280198080711625204800800080c010014003900a0320680c074103450807048210103020200018203008481d41301c90f141d04020b5440c2c081441d052000c05420507000700c5503900c000034104c90980c0d12441c04a00b000a041080020070301c10404144590712200c00400380300e030481075031800b00500711818440983c2817001c00c50340402070b10a40c0401a10000c001c1080d03066007502035002034460000c1c0c80c0c2403502650400700710314020000d0703a030140d03101420305190802c4025220346130100550495030801c201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 333730593 1250 333729343 333729371
    0xe1e1e010303030c02010e0d05270303030106050309151b0a2303060a081b0402070804030606060e100c03020a030315081212010807182c0a0308070f050319 68
    0x41030003140240c4000451940a400280c00e40341d031344904001d96002894040a03050f08041528640c0158450703550340d1a04002007501400f0340300480070350510000c000010fa080e400402141b065494106451204481c40074440c01900d042d510446500c0c3d903054800303080c4521070050b003014501031170304c144032440e62844010b90401804400328209000000c0290394100f0b07000050040c0029001010b2608050b01122120030104038135a10640d00000c280302800790110030b03034014540000c0708105456a681001d00208070520360700740140101380c10004654000d1400d4920607404d50081d0100703410b00c2da4220b0007080c8041507403440c000da4a030b01064803407040010003c00100265180e55800091811100e03001c1c0c142e100c1481179103c881d00707122200080030071442c90b405149002c1641540c5540c1c00020010105c0d02204800c1c038041b12611003580040e0b40954507010307866049854403807580c111403040c0045502408100c0c2000820580d02071021980010b170181c010004400c4c008580f1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 333731843 1250 333730593 333730651
    0x7051207061d06120906060303070312090201020a0203150a0506180604052203020a05011104051507062003060411042d03050a0503041d010302010903060b01021f0212010e1e 76
    0x1440c40c0e82c04e0030700108104114100020b40d0040c074210011400c2c1401d955004000541a80060315480d80f42d480500859000f0400e401500713900a05072a1030700f401440300d001d50304040341c803003001905010110700641405d407503407903003100000c0c14000142c1e0386205010140c036000d01a891031031042513031056881e00d00004020014804d82c081c03e106402824240d0a4139034002405441582c00c010401c010727035800a1807200400e640e000d60f034481080341810002040194400300e4840e007a055002a42d01844006501c1064100d41c10400c5502120500025000d203000301005030040d032282c08282010311a000c00a00c030708080600c0d1054030f070750f5160b00b400800c00c42210a0350001c5020320141052141d0031841803803450a50455600d9500001c2c00400a84000f0303040d00e50350150058680d10078403284504003184106600c890b5040f0009000035440722242c40c2d08030011078000b040e8125010311490049010b01c0050108101441031041101000f5102c0911044200d2100d89102002c82d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 333733093 1250 333731843 333731857
    0x309021306080f0f030909061210050a06150809030a1404050d050a050d081b0304030302121501030b01031a060c1908041a21070e04020409050907051207061d06 70
    0x760540e0100910aa4903000a500340c4c82d00c55001841101c5484e15035a0009078425012203810140107000c108480c203000b015924611018108020000c6610141d045041140c01d40710700c01202254840c402c0710507003002d4600c4230031030b0010818050421b2181900008000741031158520f07066171100012040300c0d10303180c212019000030b0701c24418003a0501081c0c0340320308142400c84d880e01e0240700084142c51510300c858803002e40800440c081c90f1180d41610118401280d084a103800d22081c100d0105000071324490000b400c0a0046c125940702e4090042012510b1311032002820b0000104042e035008030880305628402c0c062441c00100c0c0d80210042e08501074500241d90303908141e6020410f0004100110170b100b800c10410511200040001c1ca00300d401035290203032034907007110495481c1d408a03040c60340036002007030100300c20801d5800240520140d00841e5009941c520030f0005c60101c0c822900c840741c01c01c01007000b00a01640005411885051191420f0030000d0002862070300800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 333734343 1250 333733093 333733109
    0x103090c0e100509040f06110412020103020703030b04050403020619110304080d150608190603020924030a05160801060501090b0a120504140601060e0d03180302030102072607020604060309021306 86
    0x200703001c05200d0203100d00382c03001c20088c0100e4506410078040900800c101c180c02410154005210b505140c800d50010503034030001041403001e0b00741424000d5581030180d4050391990b000790f0b44640340021600c2002d4140c03c507510114110b42d903a80b12202290841d80089046544030401c1003225205041c007070002d0483da4498120301c0c141440e1011200d528181d0311200d90303180c441c1c1800983e81d003150250f402001c85400c00300d11901a0804104e02c42149803d03501803240c1040031003042000701d0588032120f800ea18000480d0b40d02c1102c2426038400344900382c08583e0b0100f040c000320b90324034020a030851950903e04001c4122110603022144100c5050741d1100c002c00c807904402da8280001401020145040481c0e00c0044001034284c1000e0100241401520301d1115500b0a40021500003160024021900e400a5040100010720340707540c18005060240078044d10b6000341026104242e80103841c86040c1420500c6c00d40041441000907a0700021461080400c1e003200e016134809444a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 333735593 1250 333734343 333734363
    0x9010203101e0e010b03040c051c020d050c0307080d0e030c060912011b050c10110d0c020f0a0f050607050a08010e091e0c10050909062803200103090c0e10050904 71
    0xc1c1455012002315401461291509024520040501c50400c0207415011100452200c28515002d4070300500c90007040e0701340c042c0c07a85c00144060046680f88010700240c80e24501034140508060f182d22000b034000d544090213112900041c00c10004423040d8411413800080c10031074507035100f042030700000d04550008500084c01e8800500c24002c1c2811088408402d000c4010500480a500e0103403202c200943d0356503200300340c0394070310800100e40c81008680588051828a05002110b40d40ea082c094900784503c41c081600c05104100310b6003001d07d03540c1d55140c26401c203d1081c440301009050b18842d8440c10050b814000ca0807503402001390010390003448106100300c04d0244494000c0e428906208052000c1031071526403409035603014804881d114440000d403000c601c91520038051191003442815408402c21041c000d10000c800c0d1060050301c0e59201c0300b4011004e43d00880e04c014a000d2010310200510928080c500c0e40040780c206281d0032098a800115440c040e0031141583d400c0c01c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 333736843 1250 333735593 333735601
    0x405030304120f09030311010908030c121b0d0f060b0a020105070e01230c01060b070516090c021b0a050607051506010e0109031b090203010312030509010203101e0e010b03 75
    0x10b0801040c12001042c10403c0302100d019801400350100c512000d000d2103624861190549001c0d880010f40c035900c0090301d6224100302c0301d22400c5812060341800061500310200d4900e009801c40072018406c1401c0d401c4c03401010302100000b07448030b918440079454a64a011641907400c0c8042d02c000ca0843c0e00000303941c90000ba00034058210040701074140440d02a5506210320441e50172007a0b004c080041c165101c2d66825113900401881e03224125210000c14103008011002c100c00040440007400c08280607101e0404804903402d41c00c50802507400744000d80e422000d0542c1c60088000c0c000c0080c0038255861010910940c810310007219681c2240102c030010890101e4805c2e000a002c1c64003020b8401d0000010b002110300d80000380484d002e512540f40c1c03101001c0b84031405421600703030964403540d6070300d80a4181004040c449001c20308050010b01d1905051080d24410b03840d01c0c00808a840c9882400c80308111033840d40d406028044402081d220010401d49008141034480c4a507a0b00d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 333738093 1250 333736843 333736853
    0x3150108011b030b010f030504140303090a0c090c0c0615030b0a020c0105102d080d0509091509060f010e03160602100504030e13090b16030f05090d1b0b0405030304 72
    0x5024050809052404c060f02d512644d0120040741150f145080000745c5441d2402c00444000c0c00e41c1442c5064031000040242d03590713000c540c0300c64481c4900d94000f2026107500030b0b503003070382c004800000008001e400894082500764212120b40c035850241100b51035229100c0c140040803c135594141542c001491450310b043c00d104056008540d0042104484e04006010f41156008144090034000601343c4409440f07490709410700424946086568212040c400502186c2160403260f1140c0300d00c1000412625a50742a903040301c0b00100b41016555603002000032032540c8a510904003e0320a07410200ba8070200714010b00c440400c0c9020441c14544080245080ca0001191480078140005d020020b50802c01e040700301d0742d040f80c001468481d00e180b00381c010203040d803004d815003040001f0300c0103240f500050159103079203e43c2d060100115062081040c1c460a41c1c10301e80a51020131900107a501c0b901c21500300154507094460300036115210103840307003410395059800e40c00003c24081000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 333739343 1250 333738093 333738131
    0x3001050a0b032205120703020601140603070e040f110c06090127170702030a0c060201060503070e1501090509010b18090603060f1902040b180303270315010801 70
    0x10011984441c80d43c0741c84024942d600c031024501118900038804420301300702c0305202c0292451020103402d51240f8080c01c00035a6080207104030681d03540500322040c0207041c818100c901c2441e1548988203003043c40c0061000505050b40074050541e907401082051482050040025400c03010040049086c02007040c1d08440451020f07070760401c6500000d400b001400e62012000741c0d0440102d00c001c0009000c0c801ca00e2040301c2c1c00030b525002e021000d100f00070f0500c0c0e110040d20080d50003001810340300c10a05503503844074016080e1071212940000c55814100c80d0110007107070f041c58080003480d55080810b5116000303802c01414200007185007114031604000c0c20352018801c692048881c100700d00405c3e00c8840190417035025141080c00034400c0941e850188001028600d003c43d03030b69070f50311682021134004600700703aa6042400c0001c1c2c0385190000596128107540000f1110480e01c0901045201012801c016054050040d40e00300c0a1003007140ba038000c02080c0004228ac020038000900d042c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 333740593 1250 333739343 333739349
    0x20c060a051c0504021509030a060e0a061406130e0a1704031104140720100b0a0f14120a05010204060e010e180106030b120d110f03031303053001050a 66
    0x80c0d01c3e0008000150f6a100b03030741e00d10b2180340031406558001c60b0380031a080c0716980001601c0b1034100708845624400000d95500802d018480400505000070360035010000e0030341d003560713101c01640d1108a803100e0a03449820003800d020211225030301c0c1a52040d0810b9a444840040064081810802e1001060344d0341041c0340125002c102000191a01442c3c084004e485d0380c041110340010903071041003418039515189164411590406905211100034011070310078240111081a4002900c5146504003015504003107241c9030400030020078884410710000b03100c2e0b042d11840e440d103000f00742d0a200400c05041503a840503402c8000350009006c0142c06504d05000300510301a0907082d10074082d00b00d064940d685000324116040300e00251600140444030b003402e0141c40c4801d580d041d001030070f0700c0e00130b070050054500041a5180a40c0c480c0012549210381c941c141802900182c81a401480128000c08142d141110320701000034002c40d6482d0a01c5060401d100103220300c0c58000c50326001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 333741843 1250 333740593 333740647
    0xf060a020f040b030703090609051e0f030313031b05010212010b070b01270f1409030301030f02010503060d06021b01060b090a0302090402040b03060c0d0b0a0b1603020c060a05 77
    0x9004686078a400d482d210b94400d4040000780480460700e014401d13004072694035080241800949110700b803164442c600004900c0000c005000506152070303001c10246001c0a004020314203640e181010b00030000781d0300600701d080100402d01301030780d0b212600c80164024040e17000113032140fa04000d800c04001d0b040c1c1008442400a10041001030000e10a0b1810340d80f888010040d415011a000e00504281d42c041c80c82c42820314a10850103802070744050960208801c010300c250700d0b404103080e01da01c001c7c0405004052400303080c10165024100039a000b071406450075820084984844049030402000c44d81559000510b0340082c590034000c0c81c02602e4016012881e141e02c20300003d1207400c8500c0000e02440e8514009429552240d012144262018081c0c81051805030b022003e2a4032103510f0082e120b2404007003000500340320300c1c0c4000b524854a0701d50301c1c010403020448030220280c0300440c11803040403050030080e1686005000f010503191102c603154165800449401d07814450304003e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 333743093 1250 333741843 333741847
    0x606120210030e01060f031a0c0f0f03060f04061401080906240301020c0d0f090e0c04140f03011e0e010203090d0513080105010321030506030303150d0b0103050f060a02 74
    0x5691100000c1d105024641400110008280740d014050042039105140c0019000000018441213040c1c40542064420080f0b005a603281e580c000300740640c006c2410414014821005070794110320046410903001450703030400300036100018050f256a500300c038600f084040583c50841d60031880d65900210198083c04061601c2420401c00c01d83c1284003003001c0c1e0040603140e1164074298120344502d800c000c1516160049010064490400720301c041c00040c0d031050f8009003030311114a205000300000c05684e4a400c6c980811600119201a1507991000c06002400080d680910400074140ba88500c00c046003c0e15604610480340e075001104a541d004004005c03c400f802b2800d1019070b905800c1891725a185441c00310701c05134258006a10713031b602e0000040306200004143c080d075003095009045141c500c80008900755602074503610b4040d8000c0c008510802080f1403510b40742d040c060701203440c0c00d40d00e0702c504425460a0b8800c0c0d449411051750a13004035802e1100b90791040b00030f00154 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 333744343 1250 333743093 333743129
    0x60609050a0c031b0509272509210602130905160519050a021006090f1a030c090901090602070f1202061b07030909020a0e040c0e01140307020a020306040309030606 72
    0x6050707485401e80361031140e102e840113001c155001b00c6206008082c7e0320740d101401d2a0000980064428400120203001240a987c6103510300c94008001a64900c860329841c400c0d4642100c0020300c0b03691001c489140e028001c041030007140c0550079008020890300814181000010120b00000e14802502040740801003800c50a04070b1010001d5800d15140166541e04030190403030601e46040d80113844a8288a40043d0f182c410340c0100c96604045141041060800d10200d040010f55081942e05030300401c1c5004140d280185905512040e102c001194004041d61141c00301d0f130007040c1c1203c0a80b002d040311410300512401150b04a1401e00003000c41d410490540754454001e1090700d00913400c002561810540f0a00c1100001c0c14000c03000e545403c015240645040600c0d00d045008500d4200d90061180c4601060440d5080603181c031691244940341e00844d581c4028140701c198441d003040600181c40400409202c0d500a684045110b8154030b0480c06481040e8816003803103000040e40c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 333745593 1250 333744343 333744347
    0x110a0b041515120206071a1b12070305060a09020a09140904020603360f01111602121c080109060b030c03072f010f06080a051504060609050a0c031b 65
    0x1000990712001a0a42c2e0754107644002003851081280c02840d11034618240045000d002c11100c1c00342007c0c0c2d15918423000c01240715500e80c0a0105d440c80301101807404100c1060181d4083d98001d000588001c1105880703000303405c242e9000191442c00106180c1040080d00c11070560082c0c0b42c03a044819046e036050940002c0c0702c60101600301d00c9008854600452040745003c1c2d10407035501100d41680c8104459494562501203910b0384503995400d0103524280c03400c000e401c40382403036924488003060022039028405c5811007078000001c81e125029440140382400d40e41c2c105000541d9403207514660522520750181e6445e54442074495500b40140301c0320f07062170b8064075030041c0c062070101c04810000c0c100a4100d041a030310f1401c60000d89046c4078445106400642c1c88010300c00c824800e40365186401913440a100c60b0150503604410510000f08500318043c0360064050f800110b10140c80d01908001c44405940c61510a42c0d50440009415018012801c3c1d4104a00108102c00010100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 333746843 1250 333745593 333745631
    0xf080c0a050f0307180e071b170a020a08031503120306010c0807050309210c0d05070303050f130f06270323010e0d02010608191101110a0b0415 63
    0x2a42080c0b140100005002521600c60030010442582d4080d880540d1030189860b640001d803080d00004500000348200c001c0404100014070f83e02207542543e500c2030300c0d104607040d08a841b090086008602c2081c1c0415581c0b4051401400302e141ea4159480c21001050f00d0301c1c0c06414208034422041c0100205680c024541c1c060107030300051110340e25a144e02c1c0c254194441c0034003150384540340e10051072851840307041148040082c10100d0307a560920a081000d82403942000034019881050240002071050014001c140e103038202c03003070604540041008540d134041d0000780340084000d01c10440701d0750182c04070350803503034410f0850100a00007000f101e180c1315600007d801a00011907000d03030b00000001880c0560208402003104401a4290079100d80081966600540c02c00c0741c003183d24003005c111540440f5941c100d81010050640d03d4000c02c01c40d50040c0c505100c540c0c046103500302014014400300a120b140c84581d02e1629141000f0301006030034101074202c0c50112154004068961 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 333748093 1250 333746843 333746857
    0x30b0d052805062a030405061504060b040b0d0204080d1211030c09040b0a120f060c021f0e12030106030c02160f090b03100213030b0703090c0302040b03070905070f080c0a05 76
    0x140c4d0852016150701155034040000b02041442200104100c103101c0d001c10000c1c041c1c03146029822400071000b00304000e0b03071b0081c0100000d0303107000c0104103c50802200102807040000d000942410350342c02c10ba604001c502080304c1c011a03070380222038403040304510514001400b0442031505500b486c0c1198200390080c541c03214065a580d04001590356034a81c1c103440240b643d07d510002d102044c0c80c014101c414080070484100b41460f800004141c0013050b10380f070449000f007600c01d02d8034141c181040030306000b01d560203490180c108841d684502c064029800381c0100d0300d000c40e40c9464a0002840c084040050120b1861002414082d076601c4000c1c0c0c04c04c0f503d040c8408030300100b00000007030801a810004242140c40001e03090a520800340700417084a004600000725960303810001e82c25600800030041c5000c1405005100525290340b044840d100068100c070740d00c5031541c140e43c084540a860800124001c80c074211ba407076501480c0d10340d20549c03018061341031129041c0d010341580074030a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 333749343 1250 333748093 333748111
    0x31e03021203040f1209080105010b0408150105030a08130e04030c0201110c06090103200301120209011a12040807121206120f140f2e0905120307030b0d05280506 71
    0x5d002081d80388900b0042c00a4250322000b080256540d0681800a078018441d40303105014180071400d00752003242609040f5000540136181c00c00c002c1e5540d04042c8d0018520b2121b101c0e140d08042200c000d00d26550784240c0c4a5200d941c01509180009880c80b42d07030182a040a90150071031991903195002980d0899601f802d012500d600d80054401802d40d900d1800b542c101d802000000e84100b501c051a000130f4000d6401800a980b42e81d28546a06007004101d41840350822180d181100c0d170104140d40640100c00003424038002c0e0780c5034141e000d60422035a0010700051060010340030644a8003005151400d803000443d40640d48500c00e4003a9141d0141ca0180f100800d403420480500c400024100b9000582e044010101804002c07040da0383c511107225204203c1500160185200e24900c0c0c9401400401800c035603800074151300d9000900d003078101a2529022100c60f1502c12800100d41d116001500006c00c1000d2110441010780c184143c41c0e0001c40d1014011600102e00150421100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 333750593 1250 333749343 333749363
    0x150b0a0b07050d080709050d0c03061506052a06151e0904061a09010308070c0902070f020f0a0515091203090117061c080309010e07150c020a031e03021203040f 70
    0x3841a181b0422030303440a81c1014003007025804004805180c0b01c01d03a48034034003c21104085500c0360140d5020ba00410001ca1010094000e0403040c0c0d2000c0100900e407078141c60303100450803140c5410f0020541e603503040000038440060241c0b603d11000808030b000b0a4045021214001c00101094000342c40600300725524000420b1001c0c0300181c0326500749021705403902e956541d03d050b01c85680821401e458403600411f01054480441c021950722036040744c0c0d1255140542e8003000070700d40d0003010705540224500000034842e02d5480c0d04081b1011941d071a940c4075006a424428410850040d10340705810400c0309190036a0003c500344200e848610700f14009695480200d141002c203005100620401040b03c10100404180111322800220000f84200424020500c2e0384040398003d098080b040d00f00480d40781441801d0010050f80014107003401c1c50350b03c2d100d13074250128218014442e0101010683d041c0350301044629011040002e0f01c41c40d40c0f4268869184540800200602202032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 333751843 1250 333750593 333750601
    0x203091c02030106080f01050a0501060e041a10020f07050a0308042108070c05040b01020f03030c091c05031e071104020f0d06170d02060919020d150b0a0b07050d08 72
    0x40c840010010950142c0200320340c40e116604039607280e10888980400c0d6080c98002003040803a0301a490484541c0d8442208044880c800c0002901c980e07440012845400b05151200d5580c40080b080c14416035005041c0884903500700900b001e0554019a01613100c40c1c0e402c100042c3c810088900703c44421041e0f0140c081140c0183c91050405903006d000950007040d62418841c400262303100715501100d042019214a9006a0301c81000c0b203150341c09a0801d00004140e6000032004041c80e00c0020300c55800d5210400b00d080890800000c15126940082100400945840701c031071880740741c040d909406d15041e6a1280503040303150b01c5003402650041101000c60450100f60b0780b2a4004600501080c1d40700d01c24001003680d5580c3c2a0039a11403000541c45007070001c00c8840c020410380024285001003030011100c8451030002c200c1c0c00c090700821001c00b066407070b000c905c0151003030380d800310700000b0300801c10486a0030f03604034110704c0d102040244002200000c242c80d0381340c8a411324032401d0340c1e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 333753093 1250 333751843 333751879
    0x4090206040b0a0e04050a18230a0b0403140f090105160f060b27010312050708040f050f01110a020f0402040f06080105040c051204110310060b0c0d020c01020309 71
    0x41c03a401404028000300d900185103401ca000220030140660b0200003c0c0d030307010f01750002e843d1203072105290011805015408159031f1140c401400c060b261060413100d52419007240b50a0f004c15060b143c035a841c405210406a0020440304030180c1c0100b05800c042032000b101d6902e124501c003481c11302600054030b8020194102d28543c00039001b0300f8240d0158028140030b009080c19043c1240b00b45014001811611500c00d1903111141e40400c12540e207178250b81d02c11070a98410036907201405010701c42c3d1000110594020409050061032540303e80703291400f44030130142c0e00102c070350500c10380d0003220030340f2480061105241601298213500c5a4810804980203200b04c1d0010030040045410120700560000d40460480d4001d45040008245001c03045441d4058038140e81404a890700228022804042c21b0140038100101500d030200d03c01010754003141c00603071010b405240d0201e0101c09196040c400e000d4200c40390b0000d010032010b0035000039164030402c103016203e040c240103005c02c400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 333754343 1250 333753093 333753097
    0x50901060806072a030c1a011206110409021c060605031e101e03020319020f06071103031207121104150509040501030308040c140109030f020f191d0609010504090206 73
    0x341380d0b0009003802c00141c0c103000342492080c4d60180c0715000f42800030340c030800880003032038105d644401455121034003a0b5203110180182890404a07944140800b0904000f0f51000f03140ea1196190701d000e0800305880d140c03040e55190703880a42401018020000000c0801003840800300b140f4040408541d2101c40d90b200310040d1750070081001c041022a604c044918034007900c2664001c0f4115140001036141c0314a040072805002508414041c003648042d04140f070140154134820b42c0c0481142c3d21038400700b4650742100302c3c4c10081c0005241403008580c0c0060050034903c3c12650140320300c0005401c4443d862085224982c0e00308546000341c96000e200300c0c10791303540c000000e0042c005940d4070304000700980740c00d440035100c80040e420001071544042500b0031601d04183c441000451171074491001c5140842000c0e60032048686900b1002d070344403a0308881040d244900301803810f0900e45400014988000c4084411040d50b050110b41d0703846080c92411108100c40101340c02c002031000c0f500e18 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 333755593 1250 333754343 333754397
    0xc020319030f03110c0c09060109170318100903110a03020306090102130b18060d0608011401080d09081e010e070f1409041e050c03070e040605090106080607 69
    0x6009001015440500300114180303503641030010344107440c001501e9214481010145d98816034200b40c150801007426503011405040820590755540310900c1d840503100402e8402da000040e0080d0141e1380f0400c540e440030002c0d55202020441c0c000081e241d06030364013000d0402a807040e500301d44c50391400121801780d5030207002c0c3c480b02d0030006009030103900008010158410160700105803204903c013074034803002e440c003004407240c001c1c0800c0c04519405501c455082988030040440c0124090040600014844550b550250316203611541000080ca1498007041070024042218007400110b601c071040ba40c0c603c070007980e0f445016035801400064200d000502850343c0000d00300003102241001c0701c44881c14543d000400d403080001904c0e0460f0700425038080c0b02c1c86004000201c4e40449201440744d0211059210fa03140060714010007603100d860075103840020442040003038040c45030440004c40007401a075003081c210f80d481d202c0c010958020030030009200500d6003031000d000080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 333756843 1250 333755593 333755623
    0x50c21090c1302030f0112020904060c02010213180c1d041802040507020a030e04141810060902071103010c020703140a0f1406090c01050f0a0210021201150e100c0203 73
    0x812900d018103030b0040d400c115000d0000c014030300000640c100c0c400706442d54455005101c6281c41e901c0366130b000003d010361811001159424005000042841001c46002e011340b082602c202807109903614043c0c0b10103002e03000c00c02c0b42c50003d4200154020515002e411803c0720045003e003541a001c801c80c2c484110080d48c014101801d00c00c0135134000c00e0708800c843c000c0d5a03d0000a5042d030510041e100c0a26213107002841400c00511320424000c80d49060504820684408885888202c0e081c2d5201d0342190020943c00140c1c5000c110024007004100b440a40003072155940c00755001e5150a5540b001400d240790080481d01813400901045c3c0401e0360009850f210780005041a0300726440340b8403d03040e54450000481e28180002030032848842050b529a45071200c5031960034540d81201005a09511840b0b50314104401107001404031041ca0000c203d486614208418418100d039003240c4003888514100032400c2c1d140d030010810707030100e941440c42280c10b0328400300f0f20340716011181d070b95 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 333758093 1250 333756843 333756859
    0xc030201110f0a090e130609020607050d0905240405060901110f010c0e040e07060e0103060e190b0d1109040f080a08190e0312040804170c0301050c21090c 68
    0x24550b010203002d009090b400b80e64219940c0d864405031016940103640120515075009120300015503160001b1810a20280400e810072010b40d4680380f51030168841d503004207480007810b020362305004000c0c88208100c03000c02c180c10265611034000c5031181d409024001d840014450440364061103400c0c1a004c049e07400c48044100c00500c4034001e0010402d24000986244185034140c40d1a001b5001418070361405440500d19240050304c001203143c003840c4c189500c401e400610004a0f20505108085410040a03840080c4202c5000c8440e0310354514468004280440040f948060301100c140e00300b52038502094607541000088585050b000403d02040003580b000c08540c41602980511030803c0c0940c08086d8000c0b401c4280e902c400d0308130381ca5034410301810b00318003061032007039800900804041d0316094890b0f8140c1251600840c4643e4660311605074840c40c1e04091082c3c60b444503c038414142005501c06131030880b10020691694141d00c145e012501c0c0d02070610000d4101400140145 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 333759343 1250 333758093 333758107
    0x206040905040203160503060a0e011b0323040b07050a1b1a09030301060e041d07170f071802130503010204060e0906030d08070804050a1a04060506040606050a0c03020111 75
    0x110191100b210101e0281c0119400102c0400c0c1c102400b03015140001d02031708003035070b4004c2010010b000e88400e4040541d00e94120f40aa1640304103101c3d40c800190750007003070062000b102644280c1801c81003088000c004810040840d503401c1205410250b50b1610598903c0002400c03600301c081c221600c820300c0058584101040802d8407902d809030000a110362a6a85451f48151680400d1051001154034903417200458986680902240c0c0c665a081e40e0b04040f1940c0c15505e005c0d1036810080c401d41414400c0881504108007807008080030341d0042c06082d04044100c0b0900000c8204080e2281d004900ea0007840e0000d89403c1c060309000d0000c54071103954000091014209442460040d0b8208000c1002414040b800034200e181a40341c0c0451510740340f004036a0928001c10a40e054051020300e4400590140d4443c8486001410303060400d04140c1010000c9030000703030086200714070f041d50400009801005840c03142c881414044030306812404d06078090302250514980c2014005466 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 333760593 1250 333759343 333759359
    0x12090506180102010b010c3f09030515011508040201120e071401020109082505010911100804050c120102120103060615140301031502040801051303081e150102030403020604 76
    0x186101c0c1500340d0003400f602c01e45100643d2070780c0c000d070740141c01074a00341080b030000c680c24461200355a0003141004104040030001c0010303d2448164940003460b0304004109020080054088005941d040300155503d030440e20340d05c2c2d401100309001882110300019055a0181c500c150800038111810701204820744c52680d21602c0354000c2da81c0c210300e50002c402c8a5441489015104c0d580110300510300342940c2545800c01103407031300e02e001210a81c0010030010b1000e004011482e031140b410038032034075500000c00c1502110800c00030100646e0310100400300384005940d142c42403080d1105101d003103408149501a118002d100742d10101c1c808000400c05c115540100304175004102c0c05402c0302141d50f01114107194000c451004440300b40f0060012a00700c41d00d403401803400140041c030382a030300e00c940c81c2554002c0704e1301c01e4040094143d0806054018525a910441c01048250400c0030800c010202c0034002d003004540203106446d51042d0b034002c008070740c00786400400190311584c0d83c0d400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 333761843 1250 333760593 333760627
    0x2118060d050a090c09021804021614011a040c0e09040309050d0311010507030b060406030c020102130320060910030209040603021f020f010c1d030a1502040317070c0312090506 77
    0x700701d640785041c1400040ca20400c2c03003503a1510443d407c0b00756a8203881c00c1000065000104e00d202c03000082401a0001103004c0e100559050740c80e000410f00c40c65800000d80101d030b20300c80703450090303042c03a41e00d1051590041490b81e00c0d0303104941000031504c0d2414122204d0445401290b0001640d02c01b0505140d0030800c845800308400e002403026559000c000c50540b03181d44d00046cac01903800d010a201141c0250400d59101029200040c246407900028070560740d0540d006645c42e880c42907032003900703000c00b100559904005aa40c1e1b0b00e80304107400440d03002c0c0941c5215800700b6501288840031661243c212800460b0000c11403501c00a100700b05141192115214201611402d005007c09803810f00400d806d241083d00c0300409083c0924903082456080a03019505008074020750000918103030705c5c816404100c0708010f0f180c508510300540310505104101d05e00002c03d000e070390700060082052000b0349502580c080845405448103a0f0a6022904100d50020703011540f100d4141109030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 333763093 1250 333761843 333761861
    0xc050115031b060c080f0708040b0304060b04050c03010504090807021002030913060305070512210a1115041e08030f101401090b1804090f03022118060d050a 69
    0xca805422141c00071400d1042602d0b21621001c210b0400341400452002c034060510303030019081c45071404400d552064255400768110628400b004001d1205004280c4150490285d01f0348080003217040030403030182c843c0414411244170b140c42c1c1d0082c00c20804a503080c0c0740e0311a40034151251459503400080e4694002101e8140291f42c40c0108004002050040c1021030b40c2100291007030504113003e0202c5070300041144c1c0c00a00c00c10580120310290340980f901045401051030362105e918400c01040c81e00040511405680308002d492040440720600c290015409010031400c00720031581401c01061440016240850210800140a52451103544a00694004001d030346860300700c214441480c260010380002c2102000780025080b00b801015170300402c0d0148001f03208180c00090940e0701840f0100d451174288840403040540400601103104061a2001c0113088110482000f90043c4c5000712041c8814103410740054803641c0454000e2104e689042c00140740c150b900d00f0107022500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 333764343 1250 333763093 333763103
    0x1030b1302211504050c1204050a030206011d0105060d1e05090114010b0909100f080109110904121404030b091e12270d030f03150b0306040c0c05011503 67
    0x841d4281100528542d1a224007440c800121258560301c041c40000c3c00300420780d0100703503810468036004c81205104240314520410080810b102645002414039506a00c000c03480010312480304102c101140310141510320a8680d503855800100e0b12030050000d030b40e00c4007520701c0d000c00314014042c03051308403070721503050803000f80b025070504000b504490909100b144038071481884565064a4032000c0c8503040310b1400c4122041075143d443c0b140d41c882c8140c0c4040ca440e991b0300c1d503007410085801e0280b510003008a402c6440b51070240c07070722407140c44200103607010000001680080058940266005180c00620501350761508540c0740d030780d4801d01c81040410320749001d02c00c200c500000844101c0303990a103054509100c0c0f16030f41c007500204000e01e480c0844020031030800300c54440800d00d00b69507000303030f5440104507615000a030407038122411417460590810030a00041c180d00702105d400074010707100001d411041c000101c0304000c00820081503542494140345266000e003401e1030941e8054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 333765593 1250 333764343 333764377
    0xb0f0a11070b091e09010b0702040e060f04020d030314010609080f0703150b060f1306080709030b01060e041506020d03060b041d070513032303030415020901030b1302 73
    0x640d41d410703441c4107842000c2020080b108141c180701110040c83c2c0b1501c5201100440c01a000070b00c207600c240c002250000010440905502e0b20340220a49c07002071310b01400407820240c944803004440204040e0040071003540b1181094460f40c412402411143c24070a020750711820020260b0301103104401403803080c40220281d00c400402d21100301ca03849045c0c2540000104030076806040c081002c19803100b0700b4401b03024600c5055006010540000e410040810300701a40a000010046e1601c001c000b290b110502c0010801194181500e0050400f100407503030304000603016000e51428000d08010300d05e000520103400042900702808981c50610907240c07641c0381d544036800346200302001c1155500d02840e41c0d24500400070381000c001e282681ca0405200011708013000f690380200e42c0d0740d2100d076000342c09141407840c1102d110341c0400554a9410140c41c0c540303480119070000ca0210f0f9000030680d007640e020b5400031a00401c00780120b0104215607241d20001d40041d034078400c541242d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 333766843 1250 333765593 333765617
    0x317030103020a210210020a0c0e0907060c0b070509150a0801180207020a0306050403020a02090103050601090f050f240301060612060b070816030302090604090e12030610080901060b0f0a 82
    0x205595902c14441c6410001c134400050703001c02ca02c8a10611100d8194011b0300b41917000f00d004400204060620030182410381d0406c0e58900d4039100d201e0f407003c02001141441c0358005002c12041c1c42c0c019003640381c41a280c09000c4001100f140e82c16401c3d804003440003814007151a0442c2d07000d4102ca1400b00c16404134000b80c802d0303005a02c620480254008808041400058101e0b4803132600a40684100c0701404569400704403202d80a82050759654000b00041290107058000e0b110620300414081c40300c0c0c20070110f64250480301601c0441c0c04020504030446507030700710035668445040100244000ca9039000090722003283d40c0d00035003041d4280080440c60415500441d50342650102c0d20900c0d0103000d001c584000103480c402101055002c00a645959440fa80a00081d240d50200050f091740c3c0180810314003c0c0e40441d00305103030014000c00040b030345c3d1086043c0521030340d4101800d00b07954041d4400e00601c029007280c0101600411413031040710b1076a0280c005107000d41c4078034125802c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 333768093 1250 333766843 333766859
    0x160e0609061c020d0501020d051806010803040b07121e0c0201171e0c0702150406020c0a030206031303020a05070e10090e06012606070e18010506030a150317030103020a 74
    0x4110903034902c50a038060002d006080901848040030700600005040c44860708011080e1503066804003402450342590300032151042c8122801418040019840c261601048038885d000f0300e41b01401114208552140c247e015524440d12212024004804119407540140601b44c1c040420f80c00118142d44000701e00300e0105507907000f01c0f5000802080307500001d06c01d10f02c07850024190407401d07105000c0d4500503101e020014100100007110369032202c0c1000b4000b0301d00ba4000501ba4801c1100840410140e102c2c0d40c100c940102c0d0701a0a8182880d031401c00307a1070016070a9000303009100301d0a00103480b00201030300383d00400081400313520a641d109400c3c0281c0b0b4001d214001140c01030401045107130f03015604040d00c0e04600c9141c111842c1c0c00c0315502e080610490350b072804521030001020591800c4c50111103640c660050003c03030341d410680403a041e400020420807041d6a01c680d0f0010b01e82a4a0f1413200940d484242060809a0600c15401c05c0e0404c0c442240543e4030001c020034125 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 333769343 1250 333768093 333768109
    0x20d090203010c110f03090622240e0f0f01050c07180c08070507110d0f0803090607110a0308010909061d0a05010506040603022202040f0609180615080603160e060906 73
    0x220000c042c4c6040c407102c2c00c0305000c2901a00700c10742d0162205a07000070030188583c3d45001d44c12100340400ac2078031300110090300341c03041815001d01c20a030141512070b0603915103400c0b00510f107081c0b03420b03038440904d00c27030443c40c14180c1c0c0c0000000d08010b8096045400d03040d0444070b00c1420790b5803036006984400109449a0203441002001481e0801001005007400301d00c000220380a200440206a010b0312296429070048c0e481404a4225104004915401c00d01500303440d842d08004010b407034982d4074028625141805040042d5403181c204200f07008040d0024004e400390100e925141c0740c2100310003965086081c40450303895003410000f66440c41c0602c904021a0b40141c101c0661400c2c41020403200030302003140c201d0b4035500b4000444d40c600620124005044a602c40b080207030304118000401d003034603089a00341141440300901007486010303c004c6010003581021822512504000ba0074085900701701010848509000074540c51003140709400b50754159201081502c0c0c1c402446404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 333770593 1250 333769343 333769357
    0x50708010b0d2f1e01020c030c0d0803091c0c0302060a0603083106090f0e0c250203060408040512010902031b010315080606030d02010c0e04020d090203010c110f03 72
    0x81d00500b42e0201ca103025038001c03c0305143c0b181401074400700c040009825062006407003102242185001300655804200001e680c100442c000c108144214000510403000e05c074008041d500040701046c120801080200c070464090308101c514400540e00081c110405504154010300c10240400c040354468170030701080e0780e0800c50b2545000041e0b95000400b0011903036604450440c100c00c0c1a28101c0e200d80c09c00075084690300d22403540e182ca040e040b81d0180540122122046003c00d0211440c3d4007001c8a08041c0e4411a0f1a0a20401c09440c1c020308180c44029405000f00001c000030803002c500280b06407101112410703a920300003104e0500302c0e02101c400035003603031000041014000c40c0030081d80d41840149808681c140300c0e11014401400107070b024400640c0640300340100c9180030f00102d020900e1a10081054600e01600103140c2000d421a65005940c00a045110251650401c0300300c81c2c1c000e0020b10048603001401030032480400003003e5107002d007156181c3c4c480c4000c4200c81c81 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 333771843 1250 333770593 333770603
    0x1c0e0703060c051201030b190506100e060705061023030c0405060f060d020d0b031507080402040e01140910090c05120106120b0702010501062f0f0a050708010b0d 71
    0x490304640e100d40051001c400801c0500c40e090100c0007002500c1d2100a01840c0304035101c125504060310420000c0407502c2d81e5440b2241002d080205c0c548a440508014481901e420b124101850010440e03d00c10894003034100e005103007c0080990403491a441214000004582c98600c0e010303a0010007034410401c194184c100000300310581c681600420f40010001f00040031803003404002440300e502c201c213580c1005030080344800140b50544500070419000b0780c0600621210001e880c040000c0c01401c80d000e1210030400f1030705540700d661019400d500c4c40c0c4000c00081c582c42c4100000c1c00310445001440780700302d031848000d941303c0c4d0040d001210b902056803051706007400100030074a4284004202e44d0340da2a400000c546507c841d07405410ba00482c4405d02a092004000b400d450058000c4418050425090a0448030700c88419201e0512407a520407420b850300b850f0750070225003002c0140c07280705112401043c080c011401c0e5080385c80c8100200300d030341a030300c0902034212184c10002e81 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 333773093 1250 333771843 333771853
    0x50702090a05190903020705130b33120f06041e02160f0b010e0609060609061c1b110609060414070b070602180d0819090f03081c0e 58
    0x11107a0041e080079822410121054490302c1060000c4811642da054040e401a03119680c02c1055061400e072401048029120600003030100c6004607143d5a40680d2380910350700b5a00050140d4903071180074000340100340d100e1990340c05d2901c06003440004c003912800300751804440030900c645003501c200390128080c1c00070141c0c103c64440600000f50000202407800e04480c03618040000c007030542400c041445815014403650601541d010b000340000c0c145801624008240412035499500b601c40c070799000c03600706940303040640143ca00c0040400501d07086034180451502d44030303120303080c1c18501c80559540d11801d26030b00d07540c0c1d81d9a0b1029558a070407500200041404035a08401c0000c00c0c1c0c45e96030403512141d903902c60510460b480b00405540d81d60740852150b0391000b0040c2d01c400109011a1003074800403d684815406205e1030343c110000b03032480220b00306900c0c024203942c80203106110708801e039150780e4146006a45c1c08018565411120911600d51100c01072150310000c40741500208 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 333774343 1250 333773093 333773101
    0x3010c0f0f1b0506070302040806090f071202061207050409111315051e0403021f0e190515090405070906020303010504050a0216030e090a3b03071202060705070209 72
    0xe540ca165500c1c100344151a40c0b114540410410401140200300c156801070780c071441c0949240c10100050020300f240d030098905250701920000d04001501c10309a2000941203d40c4005012445003a015000d050294010071200f0741e0800c0282003102c5504a083c8004000041e003003900c2e02c9071003d501c5c20300310b140c05d084c424858401410403040025043c61460590301444100c2c8240b02905694046800080c0500c118103142111203aa0000500360641070030320000050480f07078410042c280031f001540100c00404030404040e84c01810081e000508260210300100c0166000a0f0780502a41c204404604407620844202003101d04c0d627405182180d00701820030000d880b002d000304040e00c0d000d11002d60f180c0100c07503c180c46a4841d44a10403c0c401010a008101d8070040c00c100741149004521042180071800c103010712003020300c101c0880089014082449810303110141400d20003c110032042002e070030301040c1041617907022695959200c040850703061241441c02500180050042 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 333775593 1250 333774343 333774347
    0x60a0302090c1e0d0c0f050a1704020316120c0806131b030b07122405060705010f0c050403050106080a2d080f0a0801120c0b070c050d06060503010c0f0f 67
    0x64040700c3c941003111002c1490701c001501d016048051561203da564450a8181d940c2119107010420450304119003484444c0310081c1403000907680c485107120b510800602190340611007074007841805c4611101ca10b485094904420072051012520080d6403200404c1c4541d000030300b10b2040c04039108003044500380d0764480442c000c0ea48602c0014940402d03001c000108035a40d290711601c143c0d940c4d0342d41e0289120200060364010321110184401b55120390a034050a072206400750342c030039205160b07100c0341c3d450050300520398074448000862800c42c2035038003254042d00820841f4005e00c000d115041c1c60340b85d00d0b915144022030080041000801e508490045050302d180e0300d4030043c640309200103458607100c0103035008410300100c42c24001003281c01c041d00101154050181100d00f012454455a141080c140c1c0d5070141e242c915034045000c50810030f415403450f02070103015011105662042c500a0041e06480c02800d02c20f50174900b109a0741445800e0b00c5031042c545070303640e1390400c401d1030701 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 333776843 1250 333775593 333775597
    0x702010c06090203030f0909070314132603090f03030613091103010c020d090f0b0f0f04090603060213050103090314132d05031204030b060607050a030e0108060a0302090c 75
    0x441d080d40e166030a940141e94240003604408003505605a61900b0300d00410000c00c0006040f00240351030a954081807100003552a035000e00715100c0b604400605040450000078003080c200c0304420254910780420305080082e5000704030941c2115110000040110340b0381c0012a5081c1d0440d122050380000402c1e20f404c0800c5641c002c0704031174030a620800210782501d0032502400096400003403d06034036070340188101f008002e03014480f0101410300b21181c0341c2d0303c5035641071110420702248600249841c1c90440d4000c280203075042100341d60320728280003c0d4101c82080c403140340c0c0e0f090380010343e54000e00031002c940d5816603034641200c1c8070f0400c0610700d401c211801401c105c3c0c030410204008034007904901c01c2c0080308002c800703c0c001c0e002c41c08400500a40159000b5003007680c501510070003420039078007966400001c84c5441d9607041c001c29418082e800f009400391084101c0c1c0801d16401000034903601d002030b6907031078813076035140140042e080c01ba01c4001c0d0003128040000c1c0c1c6181301000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 333778093 1250 333776843 333776867
    0x3022e050703050c011802090c07110d08041706070215010e06010c062408010c0504081209190902030405060108061e0406020417060f010e0f0109090c0801020301090c020f030906070201 81
    0x3c0c140e0900c403007142c1d02800c403180088401e2800212003511003d40c80e01c81d00d440e50007004807904034039024055607000b400d80010b40a060040100c1c3c0483c808008010099901170000d62407584248120380031900e90340c0c4425120240980154000d06141400d6641c0b02c41c10b031040e814000d0b00070748814004590f0403c1c00c4400340e900a56603031404001200c55035075882003101d0b40141404c800e04001c001b0b400c69040c80199410302074204010030981601060405056458425054032480441d005c038182010700c6100c4c61400d002c101020800c19201e03405940601d000b42c040b00c459a0700e843c03000340e45410a68590304042640f62125000301da10f22291944142300b120007505142d600e04098109801ca05100c400d1038001a0411006880c41d0302068010b050198191515041c05140b20302c580301d060082c5c0056035220078601051207800401c0e10000c20142008654035a07480a003034000b000561544001400f610140504007071002007511903100e40108610b00e06802940152500c20982e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 333779343 1250 333778093 333778097
    0x9120c0305061302040605030304050306070815040c120f050601020715031107030f140a090e250f0912122304030804031703040f2003030c010603022e050703 69
    0x288080002001030240d640150181240030950380482c1c810031055404503007083e4000e0340113100c1001749075000200c0603005070302e40c00d190744551154002002980b1454000540003401c0034a65810240d00000e0800c1510700c28104202d040c004d629680b098030b0301034031110b0040c1e008100610090740e00007410401003440d42000204801d00d0012034015030000c0c901540440c4003803e0b244522134000c1c282d04c2e600124416100e2814020882c06484150703703000390b01c12031045800049100307144010404135602004030400605030301c440002c00100900c050340c00064020100001e109143c4002001695406028683e0300c81c03011a007120610700c2c5004a4052070200e030510070f0305144e10001000030318002d27030949541d582141442c0d070300c0d09640d107000f04124604004010118400c81150110503501410300c40c40d00103403030a0f40c0b000c4409080e250f80d05000004940c41e456a0543c0848110b80c42918441e5003100c0c0001250030008a543c0c50102207403900c0c0401c40003e104000a00f01680300b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 333780593 1250 333779343 333779363
    0x1050c01231006051e093c0a03020303030f04020a030c06081614091003230411010e031005190509011406040b0312090409050d0801090e07060912 64
    0x11420703981094464480e590049140070900c0500300e54200c20201515a50030520b00d4a03020807007203003642d5581800f0490122000c06d00c022180e4032041078841c0c0000f400010041c080c1c0b0807003400c0d40c0e1002d103072400d40340414144a000c42420904a00000c403900107003e14255581c50750703412080000100103d0788258480404030008224030310603070103419907507503400c890300e4800c54611004000e414071009000244c1c240b0940c2010490844010100684030070302244500f101c290094070f804000180000c4008058400c1241e074281110302c910f00503a802c030300c1c3d91009001502e62030303e41c0d0445900b640104403450741504290308290380000e42c1304400000c102160840c1400c482054600f021180d4464103690407054144251542002c01183e04100140f09180041c1d52140a205036001600b00880d404020b0358542e0b00c03400e01d81e034000c01624034000040600a0100c6400d004070042c6510384584068003c000084c004159450380d1950101941000003015608454810444e018080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 333781843 1250 333780593 333780611
    0x3060d020904030807080a051b130b0d0207060b040c0801050d150f050405012003070e0d06020708090901061e1b0606080c0a060215060103051906032d020d0201050c01 73
    0x1d0340441842980030741e8800e00c032402c02c0d1000800450b4007800c481182410314090210f007030b007200c4410f4454010080b0680d81c0c1c0c04032807100d01108401d5032014402c0c0350b01149044140c10641c00402c0214420041003103c80044020042205c0280d40c9560004403000014401c0341002e44841000f14050b0141004a21110050400352205004c010910f59201c001707003c2001001d000701d1000089031035807201c07103400d0842a95150300000300300c4010408016544a1a82c0f1019101081a9000038065546242505107009603a000b5054540a400d4440c0002000c5208010001502c2d009900d86100089190811901c3c00d420354240c000c0c038403890b4240b900049481c0b184138014011803001d480310144000c10441c0e4119154000001e64100303c910340c240d0308445c1402a44108242000101500c4070321104480e0081143c0120545180010100501040d41c1044102c090f1040910704071841e04401000c90281080b4000c0d00401040406401580207001030725200c5c010f43c00011309201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 333783093 1250 333781843 333781849
    0xa02280b03271c09030618110405270601081e0a0206030c09130c3011070807060e06070f0c061a030a08040302090c0412150f0509010e1c021203060d02 66
    0x30f810b10300c007280c1420320420400081d40203440f5030071405140384d92840c1c03d503101e16212500b03001e00c2c10700c00c6980d800014042401d22485400c010003400005940b1260590707802d944010170700810340b4a105194410808100d140030f001044d542100203031441c7e1055034240011600040c02c41d030640401844044095154a10301704610310b03900c0300104116144041c00b8002084449603030901c0748180c0120b400303542000340211300c442c0c2d124600180c16981071400000c2400341036001001d031400050a10103000442c1c0180c0c0034000500191a01910358100940c0c400032034170080c40c0460001304c88a00801e109600c094200e03085032503481d00e1a180000080d062120114044a15580209050080d404c0c5071144030380c070580344c000303940c60b013410500064082d4151501c010001c01104562540d080c4860f000401080711940c0c00380400c2c100b85a41c580a44004100b9400714440e5601040094940700c0107000d10080fa0303009070100385840c210043d6941d1008007a0741c1c2080e51180c002006032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 333784343 1250 333783093 333783133
    0x151e0506030702032706091219050607091d0403080703090507120b01050616080a0309051009120305010614071b060f0908031c0902030a02280b0327 65
    0x120b06507001d1550380784440d80c504101050702c840041030108886008070103490383c1040359680c0e0411603a80144481c44401c4510302142503c405000d0303821500c1e564104a400a2014092441a10307010441600d4500506c40d003420103000c141441400004180801c0c054108180c00121900c2c0200300420303151500d51a08003980c1c0202200c40c944080c040501030b40d00403250241904849681c9031110648002407455240c0c14081c001040001c3c208007414042e45c030600050f944002600c40c0c5070415086100181002e24007030790325010002418100611a100f814142c40c1c0b031b0703100d19105240c0d415140c0f0040c0c0140604650144104d4414101d40c03020002c40c3c0300400b020380d031303041480c0c45640c0c00810302810350b4089101a40140619110304c62424001d807904d0010210000d0508820b000292500c40fa1a0020390803d00f0100601802116901d0301c0444251006c0341804042c0d0b5031482100341d2104480d0792044035074850f00c925080340c80c4508200d901c0007241c121011100c010054144003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 333785593 1250 333784343 333784351
    0x402030f0708100608030403020a0e2703031905040b0126030c0303012103090303140702040f0603060c17040f1b060207060f0c03080601030e0102041505071401151e050603 75
    0x141d480080c1100c0c1ea042940a2134000c0c0040e4400795044c10714590104003090064011030241440400c006a0300d0891000440d410320481007402032101c0c201e136403d946a50040e110312100150203001e00e40001c20320300409015070380c4540803000036846c6c848400c440c440b2080035036941c08042d10307010300c01d12403c00107010101441000745949501d400da0245031721440c011540c4006d001c4078520070100b0341180c5841c085a0300360500e1107800d400800c2c62078013441200302c025440380c81c11613410109034a0758004030580b4860041000003062a042c00e4500011150410751000c0344c800c001000610200c10710348100344a500c001c00e00f802c00705c0b002da80140c9a9004100186e0100c2403c101c403e903c5a085400401541003a44a80600b62001080481d008080d02e040c19190350140131001d0007541100c0042c0100000c881090f048444000c0403031f0300c075907015a01c1c1c0e50b00b01400c9208a0707040c4250174504812181e038600c0c1510703002d208041c440c40c00e0050510902c06160010382612400021841 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 333786843 1250 333785593 333785609
    0xd0201200c0f030f060c0a030b100512010f1202040905030705010203131205211905070e010305092e150e0603060708070212130f030c05090702010e03070305030402030f07 75
    0x800c440c03401404541da0816003128480c0d805404104c01c01400841c0070394000c3c0c91a000c031903076495030700001d4026004d80454a074200341032904840d0281d6120014118005503010902a0380e41d84460050400401e80580e20500308000e03c05001458558440d0f011180300c2c009407802d1180e136888603422a00104c80481d1007806441c61001001041a404070a00b0f0709824100d00304100c1040f000b00b401c41d00c1076401c402c101a40c000c9511041c90711092403000e00c103080140201e203080300c401404401890080c50119040038082031207101c010607541c402e11281040c60402c41940d414001200c0d82c120319100314259902c1000e00308001150300c0c1000b406201c100c82895092040034076140100041c100c034100840201031001d242e0f40800d04214900500c002a070300d071400e10312019052410f80d40035048800d2040000001c1204201c100c0c41103980450f441074103a1f40b440380c2a82a03c00c202c040c9082c50300100002c0000a001c0c801541d00f06001501b00e1b41c03240a2050014500022a000601 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 333788093 1250 333786843 333786853
    0x31b24040501120c02030a08070e09070e0418050d080c04080d030501180203040f0201200f0f010b18130602070213090507051210050403030e06070f0201050a0603020603060d020120 79
    0x4241d580103180d4110003c04800c003000791942d002c9000391640904802d1030304000c8024003141806110f01414481010010021603c0c3c0c2070862000d0200b0142481c91b50103641041c10100941050201e410921a00400a070026049003101207d40304030040c502540144c2c00c0c403001c01c101c0300c10029180c140190740c60000e8039506040001108144030800072001c070380100108030009030f080d001082d03600e0342820010102410500800340807045810754219510800ca58115031200003e00716104104207002040200084401d0121100301e885034a4a100480c2c030200d41443c190610698405000301001401c200c15a400030310020002c4c42c154421680300c081303500c144201803058600078a41164042c6450883c40042038a560800000d20780c8e440c3e4590000b024540039030000c2a800800d4000e0741e055203840704000c2e1840343c9030079110005619090010b1101002403044805a90b00200041d0440c1d590302c1c10400801c0807100105e0401100002c2d08a800d075180c0c500000720710b8054040c107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 333789343 1250 333788093 333788099
    0x1707021908120a09020f01030902041b080117070312050309030702120a0209010905070e0d1b0806180316080703020c1512090303040b040201260a0606020c01020705031b2404 76
    0x20510b001d003826071094a060f02e04c0005a641d0100e0701c10224003800c02149113002c1c0d00004001302014204e0f81e40c40030060170b5204030294084e01c4c0b42c0c1a160041c209440c2080034500040d07a8104502008007800c00e021003103568580104d01039a403150b440c80840b031a11009a020a0013400d00301080341d0282c0c4802648070852400b004828050941070b4410040c5192041c00105140390302d00425005054a00c0603000f40580c0352007841884402c50001200305170f682d0a1140d5554003160f02e07080442c148109140e105101004071207283c1d50858800c40090442c0d10b4130103996101c07903022025449540e03040e075032646402406584034441031218a45441c00ca40c100300c03030310700b0080240003560800c00410002950101000f03400540a1070080c000c40c55000ba407800b0540d00150b03480300d81040a08100220324a17030440b009039501e5500b81c49030250031400690380c2e28201d0090f0b40d89900004950501b4440c40c040c0c3d140001c1004010000031030000250064152681d40141aaa00001800c2c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 333790593 1250 333789343 333789367
    0xb070b09010f0b0907030c03060803070b01031202060601021b0303070c0b03090c0f1c020a0e091c031505060d020d0f020a030c180e0703022106010806101707021908 72
    0x444800d01142c1010b004501d444000100c610034001d0803401072603681c9016084451180e808a000340108008481e601c003041c1c20240081182440700f00d500c4800c100d2500c50703961000c140c00b4003500061b0000c0c5249585014500201455060482e40521041c08070344080303006514484020804840c003599a0b0511590b900c0c281a081c3c200c21740903054114240e0070584540e03561501c1882c548100120035121840014680000c0398090341400021100b8040300b1440881c3c82c446003484000d2007011000511820740c01d5030310700c4e0310f04542e8240c1c0c0300d010096402c0c038800507c82c981141000605d094028130b40310080b115840004000d06034081103180440f50036228003660140e4a060082c01c00c01c5071100001700311098000c03404040014008940c3c110b0094040d507040c1d50068404000070a40d130000c1c03412a080860b4040d00250000c0041001418980d0503000452603c1d5901401809454256a00b14070094003183c2180324218945180e40031205d0800c00c418432035058141d03151000608 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 333791843 1250 333790593 333790601
    0x20a110f01060b090418081801080f060f040905032208060f011a07080405060304030809100c0e0105070c0506070b040c050625060908033603120408040b070b0901 71
    0x516685403010500c03200e08504252621080101c901160f00c01c09044d01032241d08550600410640b40401c102070b410750002183c98580f1400c2e80d405415075142f120103402028180c8506401070f00b80f00b00d0840f01e08098201418440c068000c9a191103d0307600c0b0403030241280441e50231508407491040c8281c5c10203104140c1c11500b04243c0300000e5041c003510524840c08074450001c2d4000010b519001c00c040d840644005041c010b016503204d1803c1d0030b000d00071407070866002106000e4100318280c03401e02840707103d0040c001c1d65030f811007507002e21006441c65030055a05907090308404200040d1559542d004160040c4200007a4074581801d1501c0951088a40c0125201d8001440294400301d821554034a980090b1130401c6900301c0582016001000c4840015050640010410500c008081002c1e5100045400d00c0001d440700418040d0114030310801202c1075400400c26070052441c0100d0560b0070a00510642c2e10b00340c0d031441003000540c030252040b141800480e0800600510a04c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 333793093 1250 333791843 333791863
    0x9040b1e09151806220602040909060b0a030302070501120e010504030f1106090c2b03050406141e07150c03090201171e1f030b0105040c0c12050715020a11 68
    0x1061aa04211089403640801000307a40c211043c4161a4007082003800b417000d4503500030780e0440d41d56480e5000c0d10050050302a0560b040c0d030814240c0000b03418030442d0701080720b401d80d000d03080e03030360a010045651a100322500301d5015160640c4616860003031060382d008501c0b0b13031920304640c4d500e1040505070308070980c480c0c1c029800100070840b051001161084a5540403210300c05400c400341210f640c05c6843c0c40c150060200302c084141d0405070070070020000c5c0d40a50b15640d00c840e41d4210514034620803540040c8031090042d51800a581c0f0380700207002d64600c1034410901c3c062541000c2c1e0120b81c1c0d030301d0721800001e48400d0341c5815943c01054507042401c11649040192170841c03201980c080100003940c03a070080c60b20000e80300000310003204100d6040f404240755250395905001c841c030031003800313414825407038900300c10000d500501403501724035072000c001050101403100c1502d01e4ec01990301a2038102421081c540d032500e086c401055070306090f48071982d2a5036012440ba10b44001c0a07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 333794343 1250 333793093 333793111
    0xa060b0301030312151d01241d0420030105090705030903220b0f190f0c2004050a05092a0d1b031412040509040b1e0915 53
    0x10060020a07032000c1604184c2540003800711311082d182d00c00c0d0300a81c5480e806a14003139200010050110301e906103950481d80c41d4008422030a180e0010320303001902c1414080b01181003020030541040244541e2002d40303100600000d455504a48103001d41c10804800b01b18151700000141f1951070070745001500300b40c0c613203415410340c501070030040d6aa100c2c02c40e00c40f4402e5005055010086001003002c070150000c8240340303072540c0560540102ca60890aa51404624588c0d0b6010b09940b040900003400645640c8030382264100d41c440803c07001c0075040700c0e0420080c01c0c0c4030000a0302d5902481d4060f0380001c10000720b40c0740141200d810440c3c044950301c890044040c00720300031a0a03103102104003900b111a8403944240380343c1407008076014044840c014840c0c3d0340c00414001c43c090040c1c0c0080c1309806035510003417400b03e2100c042c455405060740c0100e800001c140400e5030040c00c00e51022070312a11107003000c4580384130300c2407a008584440c250b6000360000b00000d805900041d81041c0c0790 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 333795593 1250 333794343 333794347
    0x6080406140402010c080c01090602160302070503150105060307170c04080c03210c10090c0f1203140a031d030406090e0103050705101e030b0a08060f010e060a05090f0a060b 76
    0x9540000c1849039501c002406200c00407c20080c01c813402c2d48041140c0703901c01c10840d51400248a4007100e018105d4003030b23001d40a0810300203022705001c54402c030700c4d40c02e0050640f100d80c2400d00b00140b030707040600740ca000c00c003074001d206d00105242c0039090300454455960545442c60104c030f0310700e4600c4401c9014000d402909442c1c20700640c02ea20021548907251485454403a01160b40c1e145c88a109491044503081100020600c20f80600d008280c881080e044018661075107095020048400f84c010300140c1c0e0250368000140e10711340a000c03100c000b4030b0003140c48a03c3c81d601a00d0b0000c14180006150000902002410707000030b01800201039100a50030690b1454803401c1d00c030000382c03003114080c103d281c000307003006807148040c0514407510a000c00102c0c85030300320090084c49266080f6014a1030440045400e2900044085c8a8001d24100c0f0708942e00b4040c680044050190140343c000c03110a402080580da581515403240d07000074802851441c00025030400e0b1066540214400802 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 333796843 1250 333795593 333795601
    0x709090615020d0e01020a0b040b010e070203030903120711030a080a05100b12070201060509100801050618041103030d0903030506090109020406051801090f03080c060f07020a0201140c070608040614 87
    0x329260f1803104060030400d003149401001030341007004280c40140754010700750070001086052110760f8169603075034001101075600c104040e6628031040d105030000d03070310501440701c0c0b2140b2800794650040a5142842180c07001c01c0003186075802c00700e07002000c149840100300071001107100c3c165000e509102c540c400c003898140b1000c210f02c5807410031981c00001c240040c070224001d401500040101510307416445c50010001c40c400c02a900404000d0b50800c8041582443d001c2049800c0e881201c040c140c21b503e07190703218480d280340103c006800d07000620030301c4a0a440761058200050007524085064a48001006a0128141c01440205205200030301c2100d6201d826501049600f03405800c01e10217840050b00c010714680d003d44900ea8001c000401040780035005031a00c4819501110300b0364580120301000080100c4410b00117074808040c0030050741c402da4003102c5103904089401c0c58001e02c01c0d02c69040c401c86400200c08200504148020090144612015800000d4100c216410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 333798093 1250 333796843 333796847
    0x360e0f060111010605130f0e0601030c0314120d090f1e02010315030b040b130f08180f030c010c08090307090e06010b0a08070e010302090301151a030108330709090615 73
    0x20503074071440700072603903400300b004640303c6580400304001c23541d0308603100e40d0b0f5030340741ca18400000b501040f5903a0003113429007412203800190035140242000c2120703040620605810005000d12031007520381840c40116800030813201d0000000203c0e11107801c0000403403c3c000174040d00c944c039402c4140d5920510082012402584800360401d901005688154540441d8014050390415000d80a1110011a201044a620300a05844c10381c401c85c0c80e02181d41004200044141c001d6442d05508a003196212a600ca6050ac640c02841851014201202c80000c22b16081242d00300c208072650314030401510ed00704124003030052882d0801d8078a004200c05008100440103066201400000516800d4580c0260140c50041101a000300411400c8082d28a0001c4c041d00c1201203090031804003541000c034600459042c0d847d00300090540e07408501c02c0d28841480e00000b4401c1743c0c0507021100210904c540040e0040d03c045d5103040a880c02c100701201107a0060384410a00c0d03181510400c51a6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 333799343 1250 333798093 333798109
    0x90b1c0b0405150f011403010c090302040216170702010219050a060507050403050a2001090b09060a180e1605070b040b040201140406110d360e0f060111010605 70
    0x250340900300050301d4445262407460148030542002102c5407660400284000b800d002e541202c1c1074144214000080200f030600300c1c1c8034001c0940000740014001d10150030160000c040c1500721007010070030710281d034440340c4202822040b1511442000601401903690411030b45210340d0311801c0050200d8004d5a405a86e038588403401020962680c00007450203000c2c03815a0001d40c1c0190a4644803600381c940802c40c0c03404111100d1280803100e1500040354414890141510400141146014100780400c540741d0803043d01e8204100d9a007010400384002501950001d00c00350022000c541090344090008003e07064101d003c0180900c040380c0480c079000c02d000e40158200f402c800c0300b40c0300c0740012900e107110825208502d80700090001409a840824603000e5903154085c3d9001c07003000382007201c2290f0b010250a09800c440010405a90360098440c106440c04d101250343c0155200c4010002c280116030318400002054108142d658104524402c002280002000f00d00c1c00e0800041e040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 333800593 1250 333799343 333799399
    0x5060906120423010207030201060b031006080a0603020604170106050f09070503090a021e030c0312040e07020114070305011d01030c140d140607020f0309010e010e030c040606030501090b 82
    0x5009039801103402e100d03850016010541e0b044506002c1d04030140f200601039408090220015807a1500003e1322510b042c1c181c03801000d2440c00060607074a4000200d60b0810080c1c6020b9446550300350010040c1d80f0403004100a040310204480203108201001e400c464040c2d01c518001c1305440c1c0c89001960381c0c0e011040e440119400c0084c0c41c1d448504545140102c04070000303400c18490034a0300a0001c0e0032080c040031010440c122079402e003d40040c1516180389440340300d60b61009101c14044007280754102c0360305c101d203880001a42030a608803500711100944800001c69503d1005010380e4104518890984030303001a01c0b10503514503520391054a8051041c0e8264404458070411960ba540c103001c41c490340c0007200700710703180e500061050f00c0710820740e0844050700c240d882452409101000392002e540c4140c40706124540d180005407035012440c6145981401900b10040c110340c0c0d14426400540941d0750001350541c1480d03401400c854025804074030a4038030061084003c0c900c1c140c40310312 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 333801843 1250 333800593 333800617
    0x712110c03030909041b09050a06080307050c10050d0603061505010509030601050621180d08070e0d0201090b03101401020304081209060c030307030207030806150a21020d0605090105060906 83
    0x319a640d0410006c509510415218500300175440016a82d100c0d4100d18001c07201141e04104095803070198964a1061400c01400e9810144030903c03141703070041c0c01e140c4c0203181e824030b14070b80313080b80088004840160b00226646613490f410300c041504542152405810b007824030500e0450200000707903442d0707414459284030f003000058164a0010081d42d0b0301d04050050034043d207505040207404285580c0c040389564512071800481d4140748a103040d01d004440303d072980502c0c9821401800422000c00d541a070511220000001e40442002c00452145a000030b0b1002c5050800460192080b0110711b110f04550090200788044030001c6071060004124641280c0c4c0d40280e0300202d44503014170070000d1024080401000a042d42540090581c0c03446a95980201c0d03544038100a41c500c40ca0400c41c038002014040d00d8001d50251074140d01446810a0303100e0381c059650540b0040c0d90000f80c03c03182c0140c646c40c00304000c1c10f00f00401800341c50225072060074400d030302e4086083c40c00f4103d5040c403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 333803093 1250 333801843 333801859
    0x60507020c03030a0c020310200c1c020d020c03010509120309070b04030b0f0907060e06090d1b06080901140403140705060408030910090209060d060b060712110c030309 74
    0xa005000700808610028003600792900e40080034005812800081d4040c0c0c003d014040549036219068441d00c03842072207040164101d410354625101c00c60300045140001481003441602d40811900c034604504603460b4010141034405101c020b045c16000803045019a0522040c480c0305900030640d0f0bc0b41c140304410943c0c4035500d000d10585095882d600c80402410300107004400e018948003014400d1340b00394a5241a81c803010200c0f991050584220400110cc030a0090080d1820000030900e2200040c055080380400d80c0355504003040c180f08407500548254020400d450b0000c02859001c0000340007088404801600c00720351210040000381002030f6100121210701502040d290f000384c00c00c04a03116440c0900e884803441c0d0044e030321401603106164281d0f051105c5030081d0b1106a50140c0b1160136a1240310922000745402882168500c0e1140c44001480d258003010742030b5240901440300421805050141000c041007900e65400e8010345441041c0342c4000044804000083d03961078 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 333804343 1250 333803093 333803101
    0x30d030c0e09070305220f0204110d0c0e2b03050a0903050619060e04020a0b0c03070501090b0a05060a0f06080a020f160605070c0f020409060b1008240108040605 71
    0x100d4001604080940c0b211944091002aa0303069102521600d090008030100102d03030040c4050300601000000c00c851000030072400142040e4000380c011312954070250b8149628800111b0036144610071100009403581c010340d0162521850a50100c074049903600025600480310610503403500201805001d00050350400c107034800c10100d402545c1000544201b4142034144503a04401b8418140e041414070340c000c00ca00186072040d50103998001c0044410f03c1c84c00f468012947c02070040c9441e02c4c0014440315011500038001d0a030741c148507504550b03880ca08171514a0841c1c0d0041c0c10b150280300c00107001c0c40140c0d401c0e46036600756495130a0094240e03503071240303140180c0320301408040301c054041000c0c05803000800d5060a00780c070840041c4042d681d900421920010142c0c00604010655015500503040c00da0040d83c0c105d024080205003600300c04041044500300203412000640c005007045500080c42941038009240c9603002c42620f030342c1400080009401400180c2495035400100f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 333805593 1250 333804343 333804347
    0xf07030b030604021e130b030d090e190b0a0e060405130f08030408190c1511040b130b0a050705012019170a06090501170a08160813090b040b030d030c 66
    0x100c0c0b1340c42002094445901186d00c2c4540c040c0c030b449044a8000d2042c0500d6a198601a4040005981503260690701036030716860681503a00001d504104080d90301c070b4284a40d521051050000790011903020700d03031800e05109000407210000d00300c0d240160050400c0000a507045007654045030403031001c40e00c90320b03507042028843c4165101010a0496001440e8040d60031003300030186021325a00003403c10810624025120000400fa01c210301c1000140702240c001000742c420801c045040054050301c601c038900c0301d070b0f02c00071a8202190011418901f000400d0080c00417076182d40302c2030802069404d1000703940c1c1c043c409020070100285410750b10200e201d41c0100120624002c030041041c00e141030a030000f07105902554134128200340020514880001d41c81c2e1811400c40001e11300100f0356182c440d5a5088101034202c107040908400c80401e80720700c00307440512102041d011a9601e484040c82c21034801c800824020f40c28031003628a0341e03030301160005214959090129442d0495901 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 333806843 1250 333805593 333805639
    0x903120f12040f03033b01020d0608010203220302210705010606110f0105010503250e011409130201081803160f020319050a06020f0c030a0201050f07030b03060402 72
    0x100c51101c00d40080205214071220000d04684c06070b01c00b0010194640c89281108000321400703503040620106011061107003484104da0245900d0005041c9084118010140c8403244d20048003a900807060000c9852211140d20302c4454612003007400000c55034020b500c0340e00d484111507680d0341009400302014441000c0ba49e18a030b002c1c000708103054407410f010304007500904041075684911580c04003804814030400341038890041c014402d15000050345170b00c1c81c0803800b103020703a500c10100c0003c021023034040c5e01d80640b038494540c21542d41d41801b0300c820003100800c1041c0b11042040d400700540d8020308000d422a03101c000c85080c6a010102440c03452141c4c0c400d0310302901408000d030017031000c1c0c2c1d03000d84d04903031080381034030710403040e0031030842d103010340041d024100b9003001010b0300000701140d00030a010550400c00c1820524a8070340c1038155049029060090303519841000320400d01040c03095849291820101b0005001d0382c042665020020030080c0502d1540b0b428442220b09448 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 333808093 1250 333806843 333806857
    0xe0f0a0306050f330904020315070203190e0f01031a13060302100809060a0e12071401050105030d0504060c0507030602040f0810020a0509012d031a060903120f 70
    0x1c002c0c0a00c0c20320708406181c1110446108184400c441410f44040c5101005220203500d001c82040c02c0550003010098645030180c422603140c4640000704024010b800c01c0c8520882c03640c4c0141d9129443d014030194000c54000c0b45400700110700e2401c0c4ea080e80d0ba010b80c40c0c8a07510a01c1d0024000f01c0c40e008110101042c009203a81c80618a00c1c1d546103171001d50061802c0ea4801e03030307501a4105c100070b0b0640d070000064510042603086071340024114010b95012a5003080f0074803c0f034182003041640c200d031650100320280c1e2114460445e000c03086809000d51b500626040d001030011105048000f0700303078002c40c0580344c100101d080c10301003400000c200c803401a50304120119500d82c0d9030698040000c2d10391040d89941d02030356442e49040d601d01d10946404040c00e4075441d2601c1071281c01100d82c80610440c03400382c00400c14960400e48108144840845044d8400141ca0311808044415a5091444281c4980c2e410840c02c001910041980300000c9524880c031a00c92280f91050b941d035001d02d070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 333809343 1250 333808093 333808103
    0x40b06041b2f0109020310020304020108011206060b0703260403050a23040603140f040b01090b210c150316031508150601120b030a02010807050c031207090f060e0f0a03 74
    0x40020100ca4019030180404910846c125640300902c500c407030059000880e0080d011407549030042000c406a10030121815215000000c0c50302c1d187c0a00b00d0701341c0c204039000c1d00040c4458100b45454106403e001c00070401c00540d0180d41c3c038095600418500c102d90010080098090703d891019120362410b20020942c400c25540b01c7c1e803140401001440c4040c402e00e414001c20b40403079041d1001d42602e42c080c5800821080003603003000f01c1e1101030501e4425040e00700848083e00d070350402c845100d071041941b5040c042c15100d4419420407801d11503680d890038a1000c100107109507001e1644290034520720300c3c10085008202400c0e00301847c0c0d45a8001d000f10300070b100b100a44070030340c003d140d07109210980300c15a00c1d0241017030b8a02142d4203070b1185038159029010f030b00b01544c0281e503802c3d400300403850807919001e441700d84242183c001e030708030441c80b0b1224414440b06581000c4450003507c8104060f124040ca0441d00500c60188085050300603000540c203003807203480d00c0b8441c801843e041 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 333810593 1250 333809343 333809417
    0x13020d060b03090706170601050711130e010f060501120509070f060207030303201e130f050906060306010c110d020a080d03060602030f18040609060e040b06041b 71
    0x5500509282d0340203c070168414041c081000c500f036409403807165024084030801045c2590740d0340040d2202c3d81b150000b901c528400e24000d0300c0507540e030824000d12000010010442216040c54142580d0802900e00e04a90800406000e00d0b41d000c05c041d0020300c2144004107a03a15080d02d42414012755400084422409070008183c468000072484201c911994040010601c846294800780703c1078441d904032a4410000180e908228080c0e40f0f03100662403030058542000e0a0324040c1145555208225606c41800200320f58079169504079400042a00c1c003920f1807400a0008207107102c10340e0000d00105403c1890411500c41e010140310b030550140c051f00300b80c1c0e22401100d641d4111010007500181c10200c01049a0784040107a895601c50468070341d040c9079008180080d4610003115841c1c1150783c442000807a01d1050180000030024030446c501c007402c084c10701c0301d6000b02c010040d0b4080c504100d9041d29850068406845d100e04074902a01502180b401c200301c0d2818520b20401c441aa07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 333811843 1250 333810593 333810599
    0x6030c09060c1605100e01121121090610030f060e0d09080c0f0619030207080708130b0415050313021e100305040506011a04030f0f0b0105030604020f13020d06 70
    0x400241d02c2d80401e4000a20f00d03140c1d980d801001100001103581320b0000701c582d44000000d500908202214481d500000702c0c00048904125240350400701c00b01c020110b0702110706c9007143e1071614094201501c8005002103241181c28240c04000703620004111201c1c0001c00800c0c4004ea502520188103044103071030072207014140c01800c15400e4040c03401c843c007a100d14441303203140c203010030b2480020280256040602c0326006420480c80001500c05041d000c2142c580041c10388001486150322404140751100c032802401c00c50100b180e0403034012104208824040107408a095041c449174078508641d03259980264180390105014000b508039030624005003149914a0090140c0f840c2074660a04081d1440703004ca040c1c403010368000d811034021500600400c91341d034141c0840303510a48500c510301030b60303543d540340402c031f480000303aa04200e0200806d04002001302c246004010480050545013019000241c811703041c416614404c1089450348494502c2036015240c064030302c05010000169 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 333812949 1106 333811843 333811867
    0x1306020105060f04240f080c0108040c150c02181b160b13050706050913230402040e070f0510020a0317070c06020f0a090614070206030c0906 62
    0x169031400151708081085200d0041c203500002444851419456a003403011030624541084087c03000d00010400304080300e0306440350518080d40907100b0f00f03000d0300c801c076480070025000000110162202e0301000000c1e8400c41e0402c11090103d9542d48201250f072241c01d00c50500f141c8031410407000b15200600c040e070f2022140c0864802c031003180e210286484c1d8140d01550010300c00186101c5181031a03042001449070600e800d018131500040c40c200346051981020000d0071001e00090250b5175150005848041950140c4040c1520303400c40199166213406101e006d11000c03120000703d039200055a04074a6010fa46152801403201c505503860340313019148100300007002c0c80b6400410313084c0c801803c4000c0c0100c400e41c1d0301c00c04214003401c080c3c026480a41413190313400300344810115403012105d10507070403503003035580340d441445d01c807024040e2600198000e0b901080f0810040 = true := by decide +kernel

theorem cover : BRFrame.Cov 333633093 333812949 := by
  have h0 := BRFrame.cov_init 333633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 333633093 ≤ n) (h2 : n < 333812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
