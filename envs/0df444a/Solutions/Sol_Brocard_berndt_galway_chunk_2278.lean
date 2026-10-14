-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2278
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:13:37.078035+00:00
-- url     : https://prove2.me/submissions/cb5513e4-daa1-44dd-99df-57e81d345ed5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 409532374 ≤ n < 409712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 409533624 1250 409532374 409532401
    0x2040f03030314010509010e07021c020c01020f030a090b0c0a021003061401080f01050609180403020715111f02160302010c120b030c0405090a0b1e0a02090d110612 72
    0x40e8025942400b00b54082e121071908000d007030080700d40000664006000230000c0f81c40b91071304000c0920469a280e03082c0d0820310b418011b4602c9480c016041003115802c1c07980d042002c10b250b050914080c601d0890984405440c0c01d515100387c030803100002c102412624814081c6803d89074024241c41151079407060018011b0035180600b204490844840c1c0c20254811030506208420005541003241d09001c10841e031a0030070526564040507101c0400c09801c0c1e134004080c01280b00b500140441814070407120445800035980c2c00400c950499554071003000011842c0200c12808807150000307042c0142c400192203070b101040300e003c00f00c81991082590550210115100d207130f4851000722002c60245041c1c0703444101c0b007a0f156001075100c80017860294003007074201300310380202e8202d0841c50342c0c1c0d0780c544c4204468900390894101c0021550b140b8800f1500e60010101c2821842c10f2032a4001403122a9180c1000d8840284885554200d44038101100c0f2000404404441d0307524002403102c0c00d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 409534874 1250 409533624 409533629
    0x1080d1b0819110109050706080c0f0c03030403030b1f03090c030506100f0f08120a05090a12050c0619080a0f1d010c03050c040b090303040b07060e010506030601050a030803041502040f 81
    0xd0f0300b14000310910b01d010b129028101e684000603200c040e160034012a55900042c103480500a000c100c0d42c01e500d04a0401002e4150348800599142d2810f820041c04072a1802c038824021003020701b000074003a448101d00f0320349000d40d06000407121a141013500b84811150001405c512400042c8842d00c0c10807040c00c41150600f00384030380000d40760181c455200010b84940364066120b461042101091400034113445461031400c54284281800010038140d01a403141080e42c0c2e8001c1c550090140a000e0341c00e0181064680354545001126001500c0d140c550107030303007040000f00105034250b03e42d4024000c01c02e40c041052000c00c4a049a000600c0e0030141451b000b0341c60000a03a02060003401443d01c0713110b525188a050078a080c02c60b0030b01d5485080b45580c1804100300100d06100c4400140218074051031001840725200540c250864202400340392007907000d02e004000c103940350703490b08007544d90001002d41c890f01e031498009140c01e054905050824008180440c421812403400000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 409536124 1250 409534874 409534877
    0x50a090b07050c030d050c090604030c06090909080a1b02120c12072919030506040e0705090c0a170903120106050306030303070311090d110a0603020301080d1b0819 72
    0x215500d401200352003500c01c00c0f1148100da001030000c0342c55100350360300c199031200144001d1407510250100250440d409504203c13009440e500d000d000c8568058400d001400d0440000c00128009440c3c480060107000b035000c0801900c0041e00b4070104103451741521441d03000d844507048901c4904000e44406200c1070480c0a94941010540d13542d40020b0400b00b100c0d09923001411001444070001d64a00f621011151803090800c0041c01c220f12402105400b8402c035680002e00b81815001c0000b900c5003a1084d0b001035000c02c0007400543c1d25900c40e170742c111100e82016035450103101d1055400c4c1682c103000042c80c2c481c00c000c0244c4940c021000300819112500841100ea803a618103880074081980d611303406901c18000202c14500950042c44803142145850742456840c0000030b100c5101c0d00002c4a5183c216030800c042d6042600d0b1100103460300b0304007941198102240541e4949038214080100007421207543c0c07548001403420317041c00b500b10321000d40c0c6060800d50790080a1603940c02c0350 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 409537374 1250 409536124 409536143
    0x4050a0501140612010311010c08070602251104020d061a07170a08041b150f120c141608040303030504020109050a030b0414070803181c0f0609060f050a09 68
    0x7120b5160030021034206150f4408016000c2c0d0035070310799004071005818000d0520180310b9194000c18110f1002c2e00718207202313040c0580d80380a41100f00b25403510180d0010b40480300074020394005201500c0070500c1c400c0070303100161202c0304108480c010b80590b6214011900c4000481c00c0800c407428024180c0301e0007010b41480d0301020109036940c600c1804541000540044089000100b040c1d07003100f11044640442c204164031900c6246148203124075980c04120403012282505801101401100d007260008000c02c000140000d44085500c01e04607490304800211400509100ba10246040d500115039640750f64030391070060001e14098906038040f0700310010004091030324180c00426681c0c011110040c41d11503580d0710f0011170403060802010b004549001c14035500400103020319140028040f258400024280310f181c101c051840094500323420400d101040e00c1107807000e15907600c11000542140503050510040245504c10b01000d41410144010703214940c10103c5070034056620003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 409538624 1250 409537374 409537409
    0x50102031b191118090613080702060a03150501020729041a030a0b0d08040b13030512130b04060906050c010209031006030210081b13030219360f0b04050a0501 70
    0xd0144c3c400031150307403072035138040b6000800c030b000f100610040c000c2c4036280150070300f505640000c4d082c1e00002103080001303503038286110030804585003280c010301083c00030b03009841c10301440010206079504440392100189041c440c03182c10072021a0000c000318000e042e19101c40f900009020b901c1950040d00c414109105c80c0d1680c6020303018201c16640c051071030b915151a0800f00b4070a81c09c11252074003000424500000810303002d00517a01e0062006070100da846248400c20740020166410000b6040018841440000c3d081840c1d80701b500d145007400e039250105600c00d240640300d480300d030740c1e0107004280c2c0234214202c0c2e940010058900c00c89144981c500b8603181180c809004682118032008031130030740d003010f00b40c10008010b0582180b101c200500d03125004138100950702c2d00000c80c040e5002800700401100a9116100d002c1858680184c0c1400b101c0c451443c81326018a803030360302d6920b0742e071035120340c0240d03001c400750240c003a006008526220031f520000341000d00c0f030080110400d04d8031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 409539874 1250 409538624 409538659
    0x302090901061b020d0f0506040b0a150f06050319060603020306040c030c0f0e030708070b0a260103150e100903030b030c132c03091504050102031b1911 67
    0x15a849020403005400403a820f507020403042d81c0c0c2c0403509076105502c030850b2002090050000d64401c038019004107210341001d0486200716131101c50f051200780030111040c040034072600701610880c0c84602d0141e45944524080c403440880403182050f1a80c81c02000041480e0580c0103580300c2e031800c03502002200d444800990036180403900d6140040c2c25210000040c40c02040d00d0070003181c0203421580d55a071103200280c90041c00f0b401081011174041902401a588031a1414400c940741d4a240d00c02100b8540c1000c80440c1800010110038846004080108035540122000d00350a0220341e2a844d40d044040001e21641a00350000b03800d00c9400ba4903824001645002c4d44009003c1031202d080c10300d03001c8020140d1805031a4400c00031b000942321004a45101101d080300c11010b5035031400c14000300301840c113846013040e003000414041000540c0e00030042d502c00c0c0007158081d50320713058103061030381c1000b03040424904c0c1c00300d400c401007052000003550220f520030241c66860711046400708 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 409541124 1250 409539874 409539887
    0x2041e050712020a021903020304120c0317090d0b04031b121716110304051801080706031e0903020c130f0509010e0c130209091306180c1e0801020307030209090106 72
    0x20781c4c1c2c007590080b80e107189a003030180c5c91800c05030b000f84140c0381016140d0119a8054245200c00e469050511000f4418460740e51503800c0c0c03001c0d07030030381ea685040c10440100d42c01119010000c0d100300340c03100000c1e007814003400d80b4221560800c030000000c41da10f8075004401d05e50300c40b4070000007240c103820306401c0c10303042a0300340c015441e4030300301480703401200c038200c03401c040d444012100d6000502c800a4030380c0f58074039405031100194242210540c1860342c03403450b110407940544201400d00c03003401140c04229141c185000d0101c44042254000f6080c2a4a0702d90380c00c0e403082c0c012640d2091580d50300785691007540b14502410007840346441d56040b140c00e035420b00c06480d400c2c1e00802080b0902c0e2611001e20103000c00908000340c20041c8500004001d81012a00100c400d171801c010301c1e0400455100b01140340d070948545285041013074032040a030a040e40610000358038400e480110720000c041000c0c0041c100d0b5002959030345400e04004000c0d4004815050141c0b6141c0e0005c11194003071740 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 409542374 1250 409541124 409541137
    0x82e060e09010b01020d1b23030927010302010c1a07110709091a071b0609141603060c09172d1c09120501200f0304060902041e05071202 60
    0x251600a001035446580040051032070040b07805060008c1d801548024200440b81c0c1110b450000e580c03945111400c2c402801c003a0080f81030321b042c40411002d20141c0e50f52803181980e4080c0b80c10040e4a080d40b400420135040b00900021007142c0204005290707520001580d030801d00350060f1810695504094000e40e142c00e44020800700c4c1e02985000d040d016640f1466101c1d94a180440c102d403420098034030290320809003580c9858850408000303201106d101980c16a91880042c07005105001580c1500c4609001c01800c650311444030521651154803064080c01d040b40d0f02c010101d40315650a40e441c101804041c4000d0f9440d03142101e51244403035030500f9000c1002c003502c60351008402804011140d030284400f0302498050210b0221001c3e40c2300b01d03240b44035800024424a12207901d0b0300015041d00c521400e000b040014003802c40280c000e60307070030590268011418003d0f41c8001005081c03e46104070000410804101c20480f158004a0183c0d5581e00d0b9145a110010740410591040c003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 409543624 1250 409542374 409542377
    0xa06090213050a0f0320011803050a030807080105010c060b0f03071e090c1704020411030702031b0304050307060e030c0402070f060e0a0b0628080124082e060e09010b01020d 76
    0x1072030400341b011400800007045d444140360446828025060724100e05050f9001a14a544078800c0c41080603000034240790030075084e0404600039031419000030601d8540100040803a5203400f200c165640303a00c1032040c00020000d050320758440e1124128a4102244140d0040110402c20002485445849000e02c4c612003641c0304503040d150619510355509000d04100d0f00550b407203200950f0850008007541c0076410740c2d8050340d5202d40304520b2802646c800c40c060701460300200b0007048603642c0000c1080840304c20f41014030600c054040042e0a0001b5048196003050002030300404210321550303e03000d280d1007400704000594603698040d503109040200103000319518000b040c010b107000b448910508000c840c8010240034903688442c01c02000340e21565403030303455401060942c0111100c1c080c9103002204071011091502016551b1740300d220300c0c0140032500b1003031041030340941c80003000c0546a00000034046c1a41e40c441c44c0311010b0782240c200c07856501e00180ba400c650b00c007107103c0311440400d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 409544874 1250 409543624 409543643
    0x1101110a0e01024804021c0507020105191508010c091d040b0c0c031e040518040b0103111207030309031e050d03051801050a05060111150f0a06090213050a0f03 70
    0x902104c03e181010b800602095002c854004500c0e035844c002000c0d11200042c019500d80d81f4103070300760700384c8002424400659040c01d0400c0320f022000c085207099516260700100d01004100c24082c0010815081601c1319400d244d0058903580d0031800180c00c40780360b0501d0f5102107031404414031744290705803401094a05200c010a004040b06005404500b011718160b80c909407142d082e20150108205002400000205040009243c5211702030002000c1500f000d0700c51516a0720401950014040284882c1e10501080440d803164520955a00c5444d01103a04854882c2009400400144000c0f01d0000781c0c0203d184021a903d215078003169480703001400b183c0d02881b01517001d81401444ac00b049440000900d00050003401031034020190b540000a0900b84a000104141c145d000c006825070300103c0100b5a1205202e41e581d8401d049014100041c1c803140180c2c005440300b0f038407150445001040030806503000c02030300000c035181120b20340402591003d14540b81d03806440050044c125 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 409546124 1250 409544874 409544953
    0x6051519141509030a0b1006030603020d1401090c0305061b04050d03030915060905090105090307030504030308090a02060f03060a0f080a1b03051614090f01061101110a0e0102 77
    0x10800c200c0802219201e40340c90803e0f28200100e8030f045001c440035a40489400107200c80e80b400094a0b1024000c580b0f0306111450954000c9061130380c402c2d900400440c0b200f9400d0380042003c1d4400e00c1999480354200760496030b030b1705115950f0181528034072615104c08094a11008500044a0403614054550181002c2c1510241c0081503840b0f81510744501c080c00312110b961280c4140006000f01d600000f4480c10710568090850f48003c105414030740c020004500429008000e880840358540b9110142d0303070310f46001c82d00349011200002e40101012801100581d00e12008e14454042078510900c81036031210514091103840c4101c01c0950016011003012591162580480c60805096407107500d40e40d64815107071014468422000410100c0140240d00074110160540001180d28117101d04007107400c080081d0040c030408090001c8849900185a001c0d00300e4210807442c504025181d1002450182124007441c0040f4014045c1000028141c650808d2440408100403400c60051382c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 409547374 1250 409546124 409546129
    0x30303050405100f0c02070506130e0a09060c0903031106071e1404030501240308040504090302010902030d030b011115070e0112020a020a060b0d030804020405130605151914 76
    0x80d0241c02914140a4090a40440d00c0e15000b2821000c03e02d050000b00e00300100c0d002424040345401c201d01c05e20b003c010914502c480000c0384030507103808150030041034a8a85500c4028a8403610007012581000d407440403082d0488501c104803402911445c81c02040f20407110785600085590a01003880d100d07210200c00107801448030015164141080720400da1000001349030050b0740300b1607850707442c2c1045440401c0040050050041c14034108007105084d56599081401507004443c002c940d1605560b0a151003504610009134011742990300d400c3c2d40314801070241c1003451005000c00c0208901e04040200014010030060f003a12018000d501d810004441618801000904000e03598408684070f440b01d00c0109040c1aa940091009410300d00d404801d40b0b04160314607103d80d2580041001003074220720079951160b8100d40008169550300d041551081d00318002510441ca0300f41000100032901604080b01441101d2540e07240300da84850403e8201a409030007000081140060260f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 409548624 1250 409547374 409547381
    0x9040b01052b090203030403151d1908040b0d1505031209270c0c0d0e030a0b0703021308010501050405090703210c1524081b1804030f080609060a030303 67
    0x350302d04000031812641075000603185400c00d07002a42e41c04189610b0240d601101e1040341381e8102d0408000142034014481c6681740e2140d00c00c4058807132400d1200c07600300045107003124080c000e080440d40d121660313110100000e00b2120781c180c0c80c0030110b041c00300312071500080e00d02443d64010240b5107007040c074000340007090038a50303028a800342c050030000350002010300c09039215507100b035011500c030783d0b02c210140e2400070b00081040a00c40d200504600580b00851060078a0303412480d41c180c25111000118001c2c4a00f0b140780c0c51a05080350301040c0d1402c10b42009048400c11603003485541ca682d11025110111403100425403440303005000c03c50007003806400141c80140c1031151800201307848142c1a81d070f50703000311000130340d555a140700040030f0b09420000e21964444500840342c10686c485586290366140400d0581015440d4040b40d1b80700002448030381c00e100500340d00c0d81000c0c9001791030205c0701d00c880b40114041030300140b800d0a00155152203036070014500301c41285140c42c154000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 409549874 1250 409548624 409548697
    0x1a0f040e01020a0c411612050c0609060910020a0206120403120623120d080103150e060604050402011b03020c01020d03050907030204021b01060b09040b0105 69
    0x29446035610340300480c00388094084081151214002c000b030600d04011030302070000f01080508941c007010f8003a8a1082e0b1800c42d09111030f41070f00300f00000510250324010424000f00448400a000802c0409901114541d00c6209404441c007103241030041107683c0c0142030149402410500152800e4a400d40701024280524019a0b02c0850142c02107001640000301c2240c82c0d40058080c002050b03440040a2030500040d0000c00c07045041103a24951340c80b4801414030615402c84d044101c079542e04840c02c2d04044c8100854400e40250345005c3c0100038244030944041210401820481d445405004e10288500d005011150b980d0302c100070003000040c100741d040200142000a082006680500582e4040d400505480305454002490f0a0107059101c04140c208014806469000980380b42626412503002d0380f154004000780d084030340d07801502e288543c00d00a00040380094a8001c000b49103094070203108050b550b0005503928440c81e482c62150070540c60030700074800e5011907030080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 409551124 1250 409549874 409549879
    0x15090206160503041a030402090f1e0114121506131d0f0607020118143d0902090403120f0603060f0c02150403081005060c1f1a0f 57
    0x10405507240c141d045929107442110540e000240a0004000295002014140e070b076080d1403840c40c0035404250b49190203000301003410f9604010546200d0003056074040a80e09210034503266940e0010001b4489030a501c45000d1262550410784012010038900540d070f141030301e045501d8613010140403001c24580b040035162585d070391440d034111204010bc050711070001001407044200e2104d58500301540a0401c005580c94440003188100d50a41454000c54200078041d8000e02c400690b1070420760425051511001501e01150929003081001e8908030307a82041c80c07603403140100640381280c03040f100c0a0b40c060103050001d000240b203403c107000d0307821149401180b54462041c861046d141140c00880c0c4098540d41c804069240398812031aa042c010301c002c2a80421000103c2d117980301c090006001c22400c50b0000719a4007520640c90000c00001c1e0032603503a50714a940c8107841d000c61300003140f28440c5001140400c04841c1c001c90380404401d44082218407101401c01050f8007040d5507068 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 409552374 1250 409551124 409551127
    0xc170901050d020d0b090f01051c050c03060f04151401051c0c0f0e0a0203010b09130b031203010303021b0f130e010c030207020901081b040509011b0201020a09050a0315090206 77
    0x78450014006013603207010190011800b491124100700075070100a00300b0148888940040009039140c0340c080c07401405941c41900d25001d03506183e810102c0103640140c0501c200414080102c801070b81891086d0300036140440103280b10728a80b0305803040310707039180f0320701c91039100600c25882c1550440d80c841980c0380003250240b05554607010b0680c1a540701c2102c40041510410a1204980c0d85035030004e0011021403a642c14032080f28818000ea495450042e08000036029408840354801116480003c2c00c9884024421076032401c250b209000440040c0038402264080c204030343c0c2c20000d02000182115075021015051021001001000c0d8441580364100d00c0b0013a6000e10450100c445160703030242e91141749005110601d00d060303001d0109940000c81940400d07080e00d00d10810268112008102a10360b60744d040c3c00340040c02609288405081d8118524540550040001000903260048200c2c0d45004001c240c41e000d110141c084c0c40c4501c0311441d02d1120f6800112254802000f15 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 409553624 1250 409552374 409552387
    0x301141309060509160509270a050109061b0f050c10051302010f090b1c11030f06040b010311040312091a0a080a0603110d03030b0310090c05010c17090105 68
    0x50a4910028081e68a02e544200f80212038030248480e170f80200c107984641c2201443c00c0085001c0b43d20080c095890010114440316907041c4080190102d041c04d4030403940d03c40d03914101603000340148981101c4591800d5820b1700c0340d036420440891949086d88805484901c42c1c4401d03107403030340030614445070740c003c6d100c0c403500e00c003140d2141ca4001e40103e040c050040c80303180f00140c0000e000c28074500502030202d40c10004c803031680c4108d07580d6498030b91303d0394001c100c85c18030032010349032604a0703d024180101c01c1080300403160806605c81c40c41128280180303e02d0700010f50898103d00c9046008a80402c424800728203d48082100181c80d880c22170101c941e2204031180d83d080c0c102448600303000000d40d201c40143c1c0312105a400040030b01d410000fa40ca580ea032041d5a0070848010f0707014282c484480c0c010b06000340d1000d0519500a01611220303d07a414100d0000c0c4804002202c210030910700100d59544942004035149900111101050a03180c8100006400c601d40301410003100300b208 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 409554874 1250 409553624 409553659
    0x31c0506100f260f0624070309030c030308151f0804050c0406060804060501150c0213091704031a040305160f15020705060a0b10031505040501031109150105030114 72
    0x4401007550f022100f0724142c1010088410ba0120262400d03200d541031003c2e40001d046002100c0d0302c0384007403c1c00c040e95400c3c0c5203001e03035580c1c02c01c6e400030f821950f8580000041c150401031003131049021301c072141c0da081c0e40d030300422050b507060000d280130020750014616030540c000d038062508580180201c4c1d0140c400e1b40000b030b054948580120001850500601c01040f00c1c5000711800340061005240310210304002c000c0c848228194040d01c11144004007070701e061003a0744410f840c80d03001103400181d032401d9611148217034030902c800c4500c605c3c1c00208140d189207104616010701ea041e5030711031408003031141c1141d5440c5103583c10341b01500000302020004501c400c50340440b41c3c0640d030158555259091650801c0001480c0d07401590a104070603011390fa41c0d04100641e01e0b0780781800554042120a050b60520740f50b00f0583d0480d20b000d0010092100c60580910401c07400c607080c48a540d610104400480c140c21080760200e0020b1005000351060707000c0b00312500102500140108600804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 409556124 1250 409554874 409554917
    0x406030b030d120b04141612020309150612010c030b010207090b0303030f0919060506010807020a0b0a0509100f091205041404051b120403080903120103080306030a020303040305031c0506100f 84
    0xe0701103040e13031f0302e005c1409140d420400c0510281c45d41d0f04c0460440c82c21000d543c2d25251400d00d14036800d825079000503c20350b907880c030f045224912207000304088001030380c002e802054218000c0d4003502c103e080004481c0b015002d044028400a40030b5420354490b100100c1810030090b0440e440c900541c4142a0460140c0c44c6032135125000e08000b25890501500140c440b01c400380050045401c01c0c0d1242000c9500f0740c5040350040004440060142d858504813410201c410310501c481d5808c080900a0b1403016400004200d80a03082911003212020415152071040c3d01c10301d48000e1007464010340302c0c0b919038003080d8001380d41511034400741907595035081d4a912826082281007100c0c410301050503884003105074440710f100000c610f045554004070f400030307805100c01802d0031000000600c1c0c41c0c40c20f00c08900d0700b40d409401c03a41c0380ca403a460450303200d400000007800640112038005040234094040e05002c0c0c10007521040c060314558030220741940308a184041070000124004030700e98041700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 409557374 1250 409556124 409556131
    0x140a0302040e040b27251505090310020306090c0f070b010303080405070504020306060f0c0106030804081015050f04020706090813051c0309060c05150a020406030b030d120b0414 78
    0x90359101440d06594620482c0d05c461405d8450401e02180780c1280c036000200410320820521110b140c200c058070382ea40046007245c010f07000e6030200c100310aa0407900280034022940d021030581e04528102d03800c01c0128001103d20591113200da0000c511242d03c08401007130310030036109120b0320f1f000168a0301c8518900c01c1e4411800151907004000920105020b11005000215420352540c00c004000807101d001d031808081c03045100040501c007030130b0254814002035905c840c0e040d03112541d541c8100d44a2100c9102203550b42d0400c44941c0083d01660074800a0f158014809988a0080000d02000b904000c404440c2c843e9601c40d1300b808105104050802d280d15031840780b020505000511844103041c1c401a0245400e000700400000e0b00081c0800c15101175160a550b6401c103400c003540341903040400d80c00d80302c5140c000d00c06000c03c04c2d0000c20070340d2210740702444a0f0140c9030174550b40f16141080700b0006014104990350b100c251b50400f8480110003000459982544600900450800d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 409558624 1250 409557374 409557383
    0x10e01080a0e0d0e010e03070b0d0b130c08100603050c191704240204030b2206050c04030605070e01020d050d0e010f140601090f05010c08070f30140a0302040e04 71
    0x44c0c40c040980e41e032207803e00d01148400d4010307006070b500e0701c05500202d000d4800c0c071801c0c150700c0364500019a220360401006001503a8070610040c0b01150340070f46404015980b10303d044101080c049140ca000e40141409501c0e4580250f00c5c11061074080d00d0311210144401040101031203600f1003025201c0d00d4503000340e000c0c502a0120444101c480c9405858109074044094018030040020900300c81607285d100301c41d28101105484c42c800300061105060600810241c582002d101c2d1042c4904081c00c160b030700c9000100103644552a040d43c1100800840342d005038880e1501400d454403c502804281c0d0a924003c60044500180c841c00e450000c03400c0205559500510500318820190b8030303030041420f080c210445070a00d104108500424010641484215003000c0104002c40381180d00103030700b182d002c454501e170a2500c410204030280b504411203500c040004500030520202c0a00d0084c0343d255020440c0d000307404000541c111101040c01e142d030900002904002026086120740e205 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 409559874 1250 409558624 409558637
    0x30d02060906150306011202031213080c010507050318040b030f2109010f03090219090b01020d030c091403070b0a110d030b181b0a05120f06010e01080a0e0d 69
    0x86070086282920080500303000d5401400c41c42400d0b2004514181524507898003408000e9050000ca031506036102c90030801c4450006924208900589092044d503682c0810354500b50408401114107010310074019000ea082041014420684010070b0740c100c403001381c8040341c038002c040002405e200d03403444241c032281c2183e4100c40e040c0080190124884040203021400c2200140c0002e1102d03d50a1040050542e903e10100a40d0390714824000307016800703011500255184c886a20191104548181c0544140c000c0e000a040c084e0042103455a0590b48400360245041c01403120b00b200201200e8041c0a110400700340b1803141030003051440304c9600c61180031a0300c500b6491418440d50400700070140380150781026a03940040105050821007803071603d9880711100140c0c20030703030252600c031050070005900b00c1690300900a405142903460b894811a40c0c1e1049118141d0403c641ca00d0016a104a4400c090760013075080c5178210020380070006110382c074030072441d1801242c0400140031420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 409561124 1250 409559874 409559881
    0x2030a1e051005040c050603192307140306060702040b180f090d080c0f0c1c020c060705030301060804031106010f0e010512060a1a091906080a0302060a0b010e030d0206 74
    0x4003040b140004421446081000780f4060b16519405142c50040c50300c29180040480c00328060319102902c0e461510b030f0100080a00400080f14622141d4010192501c280c8000340340035024042640c0107030640703000035203582d40b8002003081552160108a074400d0746c840e04000e880c1c40b40340000c201d800b031401c2480c039070b030404c940703480b0750294014094503040d0b000d00441c1c81c05540c04200b19401003502d010316034a800041410310114003a80e06103203401e12841c1c0d440844001760003e07055042a16809440c1d4065500083c00b0241c8500d410180555000b0801088054403451200741c4c064081d06c0c1440b1071316442c0c24200e0800c2300070f0344455104050010f050061522060707240d4010700c4100e03050114192885403540c0c1303641c4010080718040b541c40c10000204194a403400306242c8009100329100c1c5031200030704803c0c0c1c03a0021650707072082c50640041162100000c0c010340c0560560028099036441c00074000c043d016203510281041800000030078144c50402010840c40940d40140c900d0f8039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 409562374 1250 409561124 409561133
    0x3160618031205070e090a05010632030406060b1b070506031501030b01050d0e1b0a05010c1e060f02120c0414190803040e01030c0905010e0a02030402030a1e 69
    0x35040415065120601114140000d410028140084040c0b2002150503a5200d10958004010114480c2c100c2c041404010800c001940214140c80743ca807144c44401502c0301d45091400c0c503850403500188041c2c800b4800c0c4500c0f1001640d841889140085001503c4459248542d04080e8200d8100c00c7c41c00d0100980b043c092258101070441500c0361400c503d48064600d005580c2c00b094281030585e00e041c1060164800c03c212003850140310810701c80c0c0d600c0a201650745102186850b012000f0fa5403241440f85003d42c90b401c100c03201656800d42101d06501d440001d80c0e0079a40c1c9403e4800c0b4600c03010f0014480b8054141c151710008001038a03a8a2041c1150b86980300418104c8100e100308001c5c0007507501c0d142c40e00b1102105a48420b20810140203441003000c080e041811248404900095401036402865050700d06c510780c8118030581d180c4030b81064034828040c50020410450000c1c101c02000d5001d554000c3c00101155694101038a601c900d1995442c10f00c001c400c03484041d5401e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 409563624 1250 409562374 409562381
    0x1f080106030c0912030c140d08060a0501050417030412030804021c05072309090f0d080c0307030c03090c030507260706080705071a01090c0516060f020c031606 70
    0x6156608040c0286500804014500c403854002c1303d011500d54140c4030289481244021411a0312881c88aa034000d200c0f404d42e0388a075906075a1f4001080640012014100781c03054104862041e1115030034181044024805203504070f030300c1d040078030051100061545028041010f054003036215102d00c0d080070300510104000301d21402010720520861280042c0f4001f07244e6003107850740c8410300c1c1c0c007540c10210007805042178072840d035000440b102032252814001c01e07400c61407500242219001c1c420f042c01543c018404503035480c5800418070005a096009821020070074489103400581c3c4050780d550100d42c60381c25081540c296200c0c0105104a00001c2646080401c1c003400540ba0310000341040d9a50300c1c0140200c4040100840101d406580540c094a2029501244c802c00310002068211446a424170680c03802c582043c0410b19418091000c851150701c1164090107280e4158441c240504810505214026401c0140b00343d80d80303092020b00004000c01c5040c04604544ac10800140c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 409564874 1250 409563624 409563629
    0x25051201050d0f1202010b150309010501061b121101020a09180b06030c071a040b0405010b18060d140d05041d090619020706050c21070e15091f0801 65
    0x41c482012494003c501841e40020103103502210004801c0c00b44142203014025103408103400081d1703481d0391807400d42244003445c0f10b20482c030002c02441e030f6513803800c0790300d102030070340c08082c03080310300400e001065003030180740d000302000e0614905104001209508981c0a00c0b00d11000401c101c406011180a07100c6030701061002c00700034080d06904600007030052001402c540103130140011070320100142003205000880e0b02c0c0c59120401e141c00e082201c0345a4040700c00300c82c0b55282c14648483c41c684002003080b2154050040600366840360705003d10002e00c2201620907111402d00100d460004002007148110b103642d6258507079144c00e05048130503483e812a060318005da6020019119000103d065010b100e0080140c110b00f0001500b100034400d0040162806081c070041058013034141d801420f16034180398603a800a0140040c1c800e09079420749100c000103d00302a406110b151015903640c40d602c2d4440018901041c28000808403015240c11402543c01214495100b980240e03c0e40d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 409566124 1250 409564874 409564879
    0x906020610060e0f041118091b0c0f030406091701140609070309020613061704031d0a08010501060206180c0105040b0c0c09070e1e030a0b2505120105 66
    0x5a0418008111048500b80540000c203c4481007200321039488280448620030098030800c041c06c200d1040000c0c0d039111100410013078090385d04010f41d600f41007017510312585c0c245442800002c11044c0081180c0c2c801240c004d014031411f001428010001e00003040100016107502850314a0040c482410000b800d15200d940c0e4540070440da0442c0f1860384042d0700400440ea0030840d6911020b080e0010071364860061740100000c15210740b448034036804082a2503280c1c0361441a0300143d1300c0c00c04031660444005001032900d03038200c100024511034103103120030000c0c210400540c03a034503e0381c00c4507400da001d800144e0110040c403504403508405003c0200300358002e080c0c00c011181c00a032162280d0311440d100900002a100c0c0301410a02c01e001986c00c004200703403a14141070400402c025018250075120b034100381030103a200031403506890648207024001c1c0000c0f00c0a40ca4509400c200248544100b8107800003400f09283c070f8400d401040c034415100c46844460031140d00d84003584c143c10190 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 409567374 1250 409566124 409566133
    0x140f0610050f031b040b2106033d020c030706181109070c0602030a0506040e0f0a1407050a060f020d090b0714011b0e1c0305160503071502030601090602 67
    0x241d001d071581040740d52043d40700c0d00e510034100755a2034001da11310450b44020000c01b0081061500170782d944100a070120070031141e00005484181c1090780310070001210624040e410110388071106400400703a0107941070a004910f0f9040e118101030140d078041000400035400018007502000424442c03203804012074016201c0c6051203644120707403101903d103d0341c03107072203244002141a44100d0340342c1485980140706549034200f071415100600420b031759030740c4141d041041c501c2e6031810000b8412526142d1000600703045400341c80701045042d0311030b13a0001b0ba006004001c683ca850355007a040007009076030b0300c442c1d0816800c3d10007401c001885c0d402c40d0400c0300d81d81c010082403c12400b0b46289907002406250007010075520740d401803c28000640034562501101100b00e500302c020a07080b1013050700c1194014848040e0140d600c6d4a038000180460401e01c503900c201501ea1006422003031007074041308e2038169280ca0321901c0a40c21101d405144d83c0020400c4180e5038440f40403c02024140000c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 409568624 1250 409567374 409567387
    0x60b030304090c0e092824170c040c051803030405040204031505060901050607321006080d02030421020a032103060b0904020a0311030406020304200a0b0706140f061005 74
    0x1807203101411450b44280913190251802c11f0034030b4a2402c100070502d1b103400b400c003d80d944c034003107180c1c80c032905218000d000f81d4034013003c07a0400c0d0080d00d003181000c1d03aa0518088602d89000166201882400e405100c01d10022810752a54402403029500450041407040006040f02c0c0660303a00070641405030007071000402c01900c901c0240c1d07000d240c0c4002c03000100e504403608a0740c00103100d8002c00000f4021001c44540c044003180c0241101a0002c040c0855034a440d2013940d03d01a01c0d018000583c010402049441d242203002c0b28606600c41510061011720307000103034540d48941094605444c004040e00290106a26030340540d0210f0805219445c5008924410381c061010400e0240c0c3c1c0002d28050082c1c1f2991013804210075080a95440e81810b0400800a4208035000c40d50940481d02c10010943d480000042c056402048001001c1c24000c2440054128290848045450f500103d441c1c40491030207034411265406504110b2800600300300011010288100611004101a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 409569874 1250 409568624 409568671
    0xf010207020d060c030906090c090f0e071a1308032808010612090203010501083409021b0f0f0c010f1d030f0604122a060b030304090c0e09 61
    0x7a082643c0c001c44000741500c3d0004050f8040c1407034100c0241303a94544440c0704104203800000800341d603a090800c0280769000f28608048440800d5661465480b540c0d041100d101381201c028509010014094107110884003140200c0c03905411401964101098240d4050041c001c1110f19031b40e031110910400c1e012031740140c000401030007401d080200031802c050008000e500655071103903010f80204503540c0d41c0e0480a8854241030010416080319603410542d10702240d416459000f2009095240c8920300245a0b00035401072454100212040e002000c030040280320b02042c1400c003402401a890f00b001070a401d011038404504d040c01644800c030302c08554050045003820020701102c40380c402d03121000a24003842000e80000c1c40c49802d0400082103c03c805855503681991216a144515184448010141030392801d8843d0750000c24000416500e030070440014101609491401e07860301d04d100d0035900103540340404101260780920241c14541d00160f407022240c400c181050402148 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 409571124 1250 409569874 409569889
    0x30d03050f06012a0302100515010503131e120306093809010b12070516020108060a08060a140a0b06071401061223010c050a0f05070c0807080f01020702 67
    0x8200d04010358981301c44003100d10410090582000031307a61102c20880c070702c0c00030b607110079240c21183d81a0501d40403030b1200d022104083e40c420310503108d05040d030750b030309d00c2c003030003e40402009480540241180b0411740001c0c903074250346140542e86d00e40002e800c00c1000740a4503000d900100c1c40524008030800342c0c0a0b4010241003251203469000c0d070b0041c1041c820b41a2034001d2181c1c561007252140006000c0c00024000c00e0306840b048a10002c50f59031f06000d490600580d20f18140800305481c207907005620400003140c2c002c1e4004c001c0651182c80d0140d031440c01100320b4150554039a90f050301444880e0428681d40d00c101d80b6002404030881040100d0414041c5000c01811003614100303071780000ca800c0d00204060300070020904c0308614035003402c4840a48020340c0c500020b90094948204100c18014080950080d0300c54500c0c210010800b2205001289244010040b0901c5050300251081c41c60000030049070b4020301c00ca44c10702d5031090030aa50310310354a4440c0c0c4104000001a243c900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 409572374 1250 409571124 409571131
    0x103050603060f151810031506060903060f021c020a020f0a02030d08100b030c040f090b0d020f0a1e081e070b03130f050d0206150a05090402011709060402030d03050f 73
    0x150404500c0842d0b0041030726039004c91545d0070030850080c20401648004200001107a000d901324110801c2c000c1d0f4424101c400e2802604009160303507505002042c919000250703a11128a401403070b2003030726201c448000035000d050a405940000341c00c24803a40c10020044410488801b610320507649500007540c1d2086240c034076042c04644000504001d0496560030001d015460b8030665a150804a40319194000e00a2414248a01101146000b400d10825030200406031101103e81c159800300015404420520f60388429090804540c00e00c04118810480e5400e00308070a2441c1480e44060422071124020504002c0266a0381c0e03401000150020480e050a0100303a40c1c1d864084150540b00705812002e4100307a008000303e001c000c000030300e0350381c500200c0e401e891582d183c4120303041480c02c0d114001e07648900307805420b100d00c0c640381c400590023620504160b548800c039421440c000210403100d02c402d90700300070104425070505000b10061441d59103410400ca1901c220900e0080354081e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 409573624 1250 409572374 409572391
    0x41d030d0c03061e0806220f0c120803060328110120150c04050a1703070b09100b1c060b01122d0212130f02040f06050103050603060f 59
    0x1907003141241400b960120014001c2ca04200a818624000c6411455138500c101202481a000028040340e801081b806900844070b605460f45603003900c0314000040c900e8402d4481d50402d460005811040510244c2140e201d0782d5000c1d1a072900000301800c0020302c00044510101118410440c1071100c2e426405040c0d10070500d00640100c02c1c0101c4403021100b6500c8401005401704402d801d00c00030740100c60036071210b1348107004d03614034400220601032803140680000c10ba16062017054805014000403121080c1100d0800381e0640b036840703c90006403034120442d00241250011200c00d406104170a15042e240e0080c45c0c80381d100c1103405540c0e15080600030300da40d0654004940c1c40350400c0c070380c450faa11b5414400349a520900402455084041700111040c440750514001d03040e00a032032400d55404036800042e5582a0318044040c400c0e03c044075140b1100301c00000681c0d0b584601c054401403240005191403c090025080328009030100c0c2c82039014004008002c0b404000159021401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 409574874 1250 409573624 409573631
    0x201090302210a0308160309120507050c090c0c07091e020a020c1201020405120c03030304060b060f0409020a030b0108090a0212010e03030f041b03200d02030a11041d030d 75
    0x40d0503002460905002001c4514000e540c01c10f000d056224540394000c043c0101100d1807043c049400b03408483c14600d008101d034420b1441d200c2c0c242d01030405440002c0c0607406480101c1400c00c00183e00c140c04554100355030001003010898518100041000b41100c1402049400d1b0402c14000c180c5c0b07103020091600c03903000240f8060040c800d0100c0e0143c590007a0034518107407002400f00b0f010350440d026041c000c0007540041184440d000968075680030028010318616296901e039040940459140305e0340080303041080c0c0803011040d5005000801c090b0800588600c2040c41c020705036030141400d5410000d040061240f101008140717144155070454070240030b243e4902c9841e01405280c2000f01d00c0b0b000200400c41c070300c1011008a8411441810340c0b00b02201c21454002da01c2d40a400040d101d14080d1820311500003401c100182d462400504560604015900103890402d401000b100e0032640e402d00600c482c10f01e03004884402001d50900212104104d10550b40c031701414402c00c1c4203030745 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 409576124 1250 409574874 409574899
    0x8150a14101202011b110f030c1309021507030207030b01151706190815061008012711090901090204060e1e190612021201060c1b090c020106120201090302 68
    0x2d1740c1103c0013100d186651441c1800d850a04040002c0030035030503402804408080b88445c42e012030546840300c0024088910007000c0c9042800418028104981041400d41e184550004000c05048043d1203540101515400d519181080b280306a01401820210424040545801c55a00181641d41031004080d03607889500050054041c854126609005003030042607400b404903511079904148410720520707480714070900189090351460070000444100050201c2c41c0302a0034400841c4801680f0f02159a5034035614084075049240507c444000150994803810950503843c014081d40204604191405c24080c0c9025141303a51184500104048181c4003a0315182e0519004000341549000328648803154082000a02038500450200c0145102e9074a450080f9518035444100e03190460f4a003440a403225048504211021000c60340d91001000c03900102800516480f000410704130321906000e802c56882d40c11015400000c02a0800580d800050400c01c03298143c035850301c0c810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 409577374 1250 409576124 409576127
    0x105190c02060408041e0f182f0714030d14060904051b0103020409020703080702060a0b0a140402090409050c0f061801050f13092007020a090209010908150a1410120201 74
    0xc4e4100740c40303841c07d0750404100017042c0040d03202e41094801c0100242040010030804c0c20f0504150549102d900c0280d009170400200d0141c40388610402d044203807122001015421074001281d00fa18080d59000d040040b041c42c0385d6030710b400c51010345903540541080d488094035510002c01140782021400e248a020341d1095040724000c2c0050202191580e0041c5002041e559080d0340c5d8500611489000c0b0724103400a100d50000c8640007480540614680605000d2100100b05250b500550901c0700d5801c9031118003c2200d00da05c12005000803542e00010010800802010701d4082d100a1040f0150848000d100500c0c40d002400c016480e00085444040c6030b2140c1106400600d00080001a00700c18a41120a440b0400c12311058000302c1813080f101e0500945602a40c001e07540d0070700700501d40c9a64010304941c001132409182c0f03da103c41c0014900009101440705852201c0200828481c592143c04050040c0d07007a10041401c0c0350b000d04084d00c031540124030303031600042401021a03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 409578624 1250 409577374 409577429
    0x80702151509251d090604020904050a090201020d0f0512150d080a080105040207080a0c0c0f030c1502010b0d110409140d121b11010603050105190c0206040804 70
    0x6801032107542a0f1829406485040ba842e00100d40752070450b50207042d0b42030281420040c9a01000d0482228440441c200825041c01920050700b00782d00f004086040c0e2520300600c2d118a0141c000418007110520009141500d000084001c00454442d1000c441d640607048440400400c101c006064a820b0b43d0308007801000200305610108520540d000c12600744050040001e950b22200350070303aa180f0501040c0d100e01800241a0041004800d101a018501509c44240034442003c8096180e03c004080422136400c103903008280d003a001c1000343c6200440c00000c0030544000e000150a01e00070400f1071884200003010a420681d540380240c403198003c1c6441c680115920404036420201c680d103807070b42c80d00090009506500d070101800550f002d080c903140c0810488501e20341c015007084038010b000003280402d07035481da080040440c01c04d00400740520030341c2070b41ca0254010040144202c6451008100954000c2c00c1040017091100e4240c8003255907a0010203014408c00a41c888032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 409579874 1250 409578624 409578661
    0x31e060a050d0b040b07080c0a201902090a0b0907080910060303111006060519020a053a0203030109090609050a0c1503140a0e0a05060f0604060608070215 68
    0x40282c10311003080c01040c4003058080d43c0586400240d0340c5400d0004c40702c9180803229040c2030102040b45c401272502c1210210341100c0c402891200d0940e80c9905241020740341180070340703104080c00d94802503290443d005900005030302010803a45500360702150800d0300051410050060380c500103411044c09000c651030070314070400100002a00c902d001b0f0404c1b00740755040780c003501c103079a11007240344190b104030001d6a00f25140e090402940c2080c1c441003041120040381140906550307140095010403802d4800500f04071400502d1058802c0e500f4074a9510704c03594100421341034802c0b042500441100d0560300e0119000c0741c91844c0f400c0104c00740042c40e2004226214401a400c02c1c03090580100c0143c4521a0351140c102d046024210103840e01b403c2040a43c0d4841d9010508050782076100311520014102603400c184995181c4ca410300900311084240d144004040010302d05d0544a9080902098240703840f00f4100950000d50310051a0707032501c1d211030800c0c0440d01040301c02d510783c01e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 409581124 1250 409579874 409579879
    0x5180111150408120135030c0703080405032103010e06040603080a1106060102010917030a11040f030c0f06020a030c080c030403030c1a0106020d120b06030405010e0c0303031e060a05 80
    0x450801c3d00c0e041800743d001c3e84810307050201c124000310b2404400c90103c3c16851084c42081c800130181c131082c400b01c0c2403c0c505070321a44400c000348001d42d01c0a00c0240011402a80710503100c3e49000103240c108402c00300d000c1c0c004e681c05401d49040380c08480c140c03410345a0000c0c08400e96900c05011400508058202a00081c0701140c01c0c0ca40640c4816500480f61b50f600580d81c2c035440309401a03013a14025400180304420b8901d030004c20a101d0740245a20440c00c5002054241003542c80c01c3c00b0b548a60044115100450028400c1c4540070100c0c00082810703a80542043c0c1c540700b0025210180ca0800804101c1d0091142c1e0600c4000c109403240b5800301016a999190b0300c0c50f001d0428041c11318200e41c01071400311a85914010510258129201d0750083e000340f804441c4211485500311b004000282e645a40300f440b10b844403400b8501c118400c0000007003030f0841c032a080e03241150300d91941c0c0c401c1e84100100040b01000b01d584c88000100c0008180d25621030b0400075502200a0700100e4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 409582374 1250 409581124 409581163
    0xe0604060902120a060e090c010c021c0b150d1713080601090605130b0102030417012a080f0108030a05090a05040906091b0506030c07060914100c05180111 68
    0x80311a900c04010300520302c1c1c140421640d40c0d20b9000f5103800404070755128040d00310081a10300d5501910ae0120501d1004082c05da16040c5024070100307111000406884c100f0400081041421512255125050086642d514903500c42c0c1c3c0c889a42c21800d0005088410700419070a985030458000c3c00090034600c81920002c2d03031203080507030080140748101d92249101e0300e0740313140051040c42048040388069000d1031400f4102b001244c4280d50341035801480b907580300b400c880b11740310503810410788030100302c40801e540c156100700030b02820740501940340356607500004004842c4000211201054141005a101d1014a00251104905a05c1980c00600b001807043c2003100b203034444018548582d0614240e00c8544a41010039500c5000b0740c0d0304007801300089484c1d0580c2d20043e0400030310810010840400e15682d600c07118001c1e030707a05103080d400340c1590707490001e00e0700401880742e1142c60080c2c140014010010349030140362040c40e041c81500706044642074010f010000c0340b020104600c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 409583624 1250 409582374 409582387
    0x61b0b0a09020f04062d03080a0507150e06040308070302190809030d050c0403050d080702030304110604030204020a03090c050103090507170f06010b071118062e090f050a0e010e0604060902 83
    0x8020300a03205108001c0c100e0000172074080542500c1002c0141e036044102c4509242e0380307140650301da2344000019581781ca01c0ba4058094cc0c02e16001d0507110340b081034060411410316180140c00c07448040d046038140360050004180a03c1c842e100a201c208051420100381d40303510059a085219803102826420704007401c0010b02032a0300c005100306d0b0710540c01c0350215400c0c07000448071040195440c40c0140c10401c0442c001c5160320240c0032002c400140081e01d081d9482d03000804913442164110b01081d2a15440c009004c9481c07070b036000801080c01c042c425020b00380e8034992140e03203501407129003003911100b40c51601d034100200d5600d05078210032140c507540c48034424030b0250000300302111007900d00e621502440c01e05450880300300341c903500c5c0c901072521401e041211140b181c480d050703ea014aa05104449400761107807401c1a420381c0c5419441905055111142031344940104c0e001e0840710741c00300890800390011504407502c00c0000b07807094940d14002342c05081c00394400b01200340081881d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 409584874 1250 409583624 409583639
    0x40e030c1606050301060818030f0c1b0415030b0903040e010f030b0a02040e04031b20040e060609131a07110f1609020f09060304050304061b0b0a09020f0406 69
    0x209040c0064524000001640c2c514040340e680c0310074010040064888000b003040c100300c524803c0320711101070041d203050030801030303c20324207401c0040e0440b02944a40c02508010b450342490007120f9070192030612041b100900340103900c00c040e100050101418100048002d00d090044c1c0300601400d0302d4600055a4a80d80907003140440e00091321400181008100e10181c1c9100300c07802c1300d002e410703c6a070581c1d550310306a0340c04031380702e0300900c00110119981000540c021403804c1c242140030a1001800c00303002c103000480b06a0300c0c811070503a02907414044140e40300110241c0c0010100e40d0154000401d00e07108a65415200000b03858940c0c40040c0700d1140d4107e4800a0070716042c4d0112001309018081341d0350340d0514081490400c8500903014402d1400c82d4009180c0c4450800d081c520307102c1c02c84d0110702d1552007101c080d11643c001140501ca03484d0b010a0a0700002c802c14000b283c8454980c442140c00d01014090400080d5940103440031501c0300348403000c04d284000e108101e5555101c54 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 409586124 1250 409584874 409584883
    0x12090601030b0a020301030309060e0d05070801020d061a071b090203010905070e01020606240c0708070603060602160504090f02030313080c010221090409080705030702042315040e030c 81
    0x8503a96030b4488005201c00c0c20380c0c400e507030407a5010f0307880c004110b00d003000540307070b0700620380c103440d0450081c0c406040818010090903004001c500d00050f92211242100002c60743c89030000c589a207124601920b841d00410142d590f103c0c4c2054030141e09500c440403280e20b00c0c0341540490b5107103001000001c0c0d000310036484103100e00456180c400d091000381c001240c4a100c12104503030b22002a200c0842c18110340b199000000000000c080d2a10701c04414030b6280ca6625485121280d1203182c0600400341e160041d903000703100500007404004804528400c00203d5400307410b000310303540d000300c0d403e01c101e0074a1042100d80103001d07250343d81e03050000c0e06190b03c06406544014402c410902956520001e408110145004102509505440041d40341644800a000d034099141e40c0079001040c0454020030149105100642d0345882520501c403d07030f540c1e0041c21030340001aa504682e4810312501096118038007000030180e610441c40050f0003404103480030082072101080c1292074403c00039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 409587374 1250 409586124 409586129
    0x7030503030403170708070e0402160507081005071b0503070f080705010501170a020405091606020703060b0a06120f06030803100609050402070f12020703061104051f08060d0812090601 81
    0x180d038040504040c07501d001c800007040c1e4a0100040d81003002501f010311030750ba01e2203041d50081000d403400d103205003103000075000018281d0301c54200400c100304101041220700c4103002100410310561070080d0f006040400c90520b07020517041c0d0300c100e000401000384101c42c5020791247e41c0c0c560041716420412465089088111803c0d07280c50b00101da059014007071524041c2158004180403000c0b030742484090071002d02806200e00c40d100c040b80350340c0786008090024000a038000c00d80140b1310700703100d400e5801c50380c5010b000d840b4020003881500d5100e000409101200c5001007011704c1a4038000300182201d0344050000600801400140305c660308420003183c103145c1d5601501030700c039002c1100300e04c592a401442c85166544031000540303c0c00d200e01e410b041c14016a030f4195600e890707104c260380d456078049610400c0010140064a4485080601600c17007003112828000c41840142c22060050f00b0a0311509d1030202000c100100c80f4100d6841a500c258902d5040c01c002c000c1d25034800007130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 409588624 1250 409587374 409587377
    0xd260306100315090e01020d02030109090b07090f0e040302030d0c120e0705060403060e0f060a091a0601170c0f0d06030204290915031b100c030512100807030503030403 74
    0x5440e2028602d220b405000d200300c0902e0792003442c943c5070840000c01400110428000355409210074004c082e907903c00385000b001306030004145c80301c45240c824040c02006111800b404a03440041c4185c0d401c2d041401d080c1d031448009107410b0741b55400d040c0e1031801080030b010560f07030a2110402d000b0342e000c081d25041001c4410f003070054043d144000b5071502254050103411210512003080841c256401800c0090403120643d1145820400f08609184084846192460b204e110b95400c202e400d03400c480d11540c02101d0034226040039400288112081c11030f040c4100d400d24041410101d600f03084840c011308900d00966075001104400019000521060348920316107070700d06007015800c000f089129101c1e07086480c401c54240b410030109010240c102210702d4119401300a864400300580c0006102985580c0d120b41d05074800c000a101c42c0c00c0c40082003020f08001200000c2d040015611060307152654079a09540740c10440c0c0314024954084903061049802c000203000d00800294000c071301030b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 409589874 1250 409588624 409588639
    0x307060306050d060b060f0403031112070f020d02010e10090905130503160f0602040e0a241211030303042004020a0e0405040c0305010c0e12060103030e0d260306 71
    0x45000950459405200b441d400c000846818000107002d50701c1210818402415682002c4484000c4091604103400490128040fa580710409050802c100728196895000c280d16002c91951030001400c0080c1c8002e000b05503c0d0f03101340c1103a000d0441d16001000252100c0544c501c003910080c405611407161248040c5020046082203400c860000300f0580c00c80001e61418441524103090111210401e0b1a0400c0007480c190018180340001c10042c18800c01d040450b0803c2d52743c0200b1900403800b090160a484603c2e20920341840003004119030340740220035100c54450420400142d2111000c9525000000402c800c08c28101c10300d1071410240c030b2104018005030001c0c40200e1288102c000c2c08140d0420b03004000b07140580126078001d2095a40c955415943e9030f03180d0035202c0314003400c0c01090060120700001c1c14043c40c582080524000200351551540e1009095112682c20b0b650050031409410320078009182809007074030710043c401d500c18080121051006030000e5a140d071180c400b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 409591124 1250 409589874 409589879
    0xb102109030f1d04051509070806010912020f03030a020a031803020a0b0c0a0f1212020717210702012a0210020d0f150f170a02010f120510050307 64
    0x9032241201055050700c0d5110107031045101900d210030840d5603035200c0248442c10050b01e88813030180500410b44608469040e080440c01c012154100a00035400c00c82070100300041b60380d000650100b1520000c0c103201040c20310f03001140784000c0c80c03204140c0504c8009520012990700060742c01c0031900a5558102440854150400b103174040c1c48041d610140c402810301c02c0c1e44100c8010443e080c115812181e1240541d9210101a40a00c2c415100c0a01640e0303589a0b003501b280e410b02c011541c82e98214940340140d03541c0c000da04000d00000690b0300003c41d840e0100c00803521004a00308141442200c03915144e003009028014040d400016801001000c119011207100d110080d000aa0007a0142800000e101c00080d0018610303440000d031a201080c07030b00000d61080e080c55074100b514442d080e42c14040d100728000c00b2a03019080d0302c00f4500062601c0070b401b25554030081c0d4240307010b01040e01145011102c2d0481c45004622452a1005212050780e02c00791000c200c0b035087e0103440d00c1d03c7c1d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 409592374 1250 409591124 409591187
    0x1e20070b0d180b0f06181f050607030504090902010302040b040b0a0201060b070209070c2909010501080a2112020c100b01091a1b06070c050c0319080903010b10 70
    0x100c101500800141400f00424404003c03036241e40d900480c05005c054071710445040d40c0034a4401501c6405000c0528003520718260900313500721000e0142a14001d16260950764002c1041c401c6100d007840c02e658614400003107a01c02d03011600148000100c3c00e40352b60703c4882c401403907400a10701d00099880d014001620603101410f0f5407034280c0086c102131450b80c42c02410740703202179490411101040c442218800100100700c0c00d010380c1d426101c2031a824502a00d4040c01c64406030008080703a07020680d42c000040070580842184000d0503100342c143d20380307003105503a0203500e40d291001741d900106040990385c4002419030002e400000042c0101104c090040d11441800c2c01054250202d5068078a5a480b2402c020200030034217500c409841c1c9032075030300c242c105503050750700c0f100099035131441c1d509003c4100903900612404074054204881ca0f07a0150340d80c25007410b801000d8400205180007256400e501c4003440e544082c0000482d05c200d2803000f0031072049014030300c224002c0e5582031480320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 409593624 1250 409592374 409592411
    0xd0809010903080a0209130c09141c1203060312110c01080123010212192003040e040f062408070302030309040203250513061e20070b0d 60
    0x650540c40f004590380300c41448001960015841c140c1003990544982081d0350b0b0f0b8480c6426959a80d40c88070340d0281060840e801207a6a40c40e134522502c2e0703903928800000312540e50345140f240e210b0401c10801035914415030140007203a00240802060010a1a085801207042c0184050100030b46d406101080d0041d202e20200380100c1001e1105048020346103441e40d0a0180081e0050044413043e044c6000302c41815030041c0412895030b00030f003405150054108000c0c1911f00742001807800d244500f9480f5580d82d0185204005503c2c001c98085428005224074950034140c002c8814840001c00103007121602c40020400c606000c03002c0c100148125000c1410030a81c1d41c000c000c0c0d8542402c0740c040002940018004d004445410400c3d400c9800302e008010750801800e4813181e48815542d03c10301c540f40030070f40c00f88044c00000720000c881c17480d40000207002d044040c10420034612005410440c0c0e100016491151032150800c0814185190b10290182140700c900c140880105002a11404d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 409594874 1250 409593624 409593641
    0x507060c150c0c02040c020a020904080a0801231009080307050105180f0705040506040e03180301051003120c03230d0b010212070f050a021e041406031e01021b0d080901 74
    0x1034041c0303c18600510340360f085890980720500c120b070760940c8182c0005060f08412f1354203c51243d0002603403c801c68000071080c3c014a0300c2c541c4540400705e1082d505402c00d144400c068440c0f44d0300302400c071049000307444100c0601004000c490312002680343c610f000307200c1030300c000039402c4d080108072071441c50014501c41d02c8541030015107400c52900c014480680000340019500c55160b2189114649082000c1c043c8404850110701024600400781421204081c0c00c5c80344018100e102130011415881e0034030800c0045c0e103001c80750700c5001e007000c4400c00c181e10f070f14912400b4448854000800350780c01400508080440401040705410010fa80e10f40307071880801c1c0642802d110b11000b00e1140203a220906001314207541c0703000816400a600c0078180700384c10403041c1e503404054040741024403902c550102000c0760f09403582483c1e000207070341d003800310034154800c001c2c48e20705039505400f07406940c500356207401c1110183e42101189a12585403414280029540c400001c6064405000d03074001c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 409596124 1250 409594874 409594877
    0xa050c0c03031e0c010e0313090f090b070c0609060203150909071413140f0a23061201061203050a020d05130603020d092a06170708060a030507060c150c 67
    0xa04103e140300c1c00040e00580304c400900d541e10901c058002c20706200501015100d1a892034032641071140300c904969201c110154054a450844000a045102031540161041c145151115a280783c0b1402801241c10001c010034000b0090040e8098000c9488409200c11541900640d07035480032143d03a400ba0340f06a4035000804040891641400c100214484152402c082000039103d440c61400c2c6006803041a01c00c0c41c2802000a071002603c00c101c070041a00b0219040c0e480d0542030701079060800b81501f4420000b840c58000c2da40e030254404001016a60281d550704186801c0250464004440c010b003d07000c3c4824010400340308000700c0d41c018410000c00c0d010706041050071002074000342d4000142035650081c0708042083c0310000049080312042c0080d080c1c096607511002ca1490f0391007074091140b0394036000034403c4400e1440d984042c0d00e15003080d4036510030f4002480e440c3d107544054003c0c0030324180441c1c0c0940c48072840ca0350b01e020310444182078890300700c55012591072100040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 409597374 1250 409596124 409596157
    0x10503130c09020c28060504051509030d06060f02070501300c0806011e080a240312030c0c08130f0602160f06020a1b0f3803010306021606020a050c0c0303 68
    0x5e002859540c4902d030814010030032190502d14a140703180d8140700698035400300743e1010501c01c02c03081c841e00404000e40103501d4441c00c0030a078848003940d1080780c0d02403141030166910554841d02d0101c0c1030ac0c1082d0750795a10020444003100d00c0003000f0a1020309840000d2910720006d0f42550041e443c42c0c44281808010020460007000200d6220304003901d40140b1540f20030400516458105e19030041c4110044140441851494a0044c481003003000c00241820f00c00a0039003190001ea404034015040100d8a0752104c8100c5483c1584109811003109050035010100700310742d00003100300b90b1000c40c8072190041611481c031201d216800384a0140140d11030303d541000101c0308a0000d41d01d00100d400c0d00b0005481d420320300d0a2007029040340f00d0000324042c41c402e80d41e014920440800401d0705c15011450a209100582480140800742100c0c5c0c0004500101c0140c58030141c1c80583c00000c119102da50380d40d0700406030b42c40a00182c20301d00c1000107141d00c42c80c006c0100c3c0c611031030071004d91 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 409598624 1250 409597374 409597453
    0x50903061303021603050c09240409050304090516081b0a0509040f110c011d0616110d05090f031c0f21061a0408030405010503130c09020c 61
    0x5005928a03814118218001d41e0300c1c4c002240c12038011100514465006407107a909010140b00072200d00400700c003000c259035201500ca088994408a807075900640d0081440200c0c0d0402c98550711843d0701400304a4500001c200c81101500302d41c0100321029940c8810300c1d1a8207e0200d000100010b83d801c024904114514041e80a44020401401c0140000ca030041c05000307601d045504a505440180302c0c00202100b11000030301c1415100c20f000d000d000300351450114000c1d65198003c01500d1261042c0b40844209402003911016040101c0100e1b01c030071800d000018a590424000d06000394400441051203140115000300445d404880707826008044080480c0d1426110140c03400307101f51410882201002d19040c0040c00c0100c281c046003c80c5070030a02d4106502190018070300b2007082c4801e1060f01004001c5408851003460f0680c0c883d1901600b8091017100f4200040001c000904001108400d03900a043c1010000050380c0305103520b0f4030341e40c480d83c04000c051881100c903241c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 409599874 1250 409598624 409598641
    0x20303010e0a0905070314120403051c050f030c1b010209030c060d0b0d060c080f10091d010e0718060f030212030702030609030705010501140303030a0e030d020a03091205090306 78
    0x60b44820410004100001c098640381e0511010307400030380342d48000d031000499140c0100b104080e10240028500d290a00d10307104c11380c40302c0000208803651810298041c0d0050310540c20b9404180d50041c6950f60b909107640420160791141c030750f046441608070800b5a00640610950f4940b5030090040e248044101d03040042030f502000d008035002d41c0d58a088500303a10f030600804141c9110303c00014904480030703030182280c1801024020080440410814075440700541d001c111030b06000082024070040010303080800030b118000303402d07620b0700d0002120090300140c41c40c11101d10a01c0d040c509280b9803001e005031601401403113a02c031401c407020001824400d400700400da01000580f42440d51560000c1e0a00c0001c2e04c9500d030315440031a640c001d0100c03c0c0308103801484c500d010f6450108440020a440380002484000c00c25580d85100d01d0400c0280700712015841010000c5503282100c160240041c4003141040c0c2d0649100040c6900403401501110700280f0700400504d5682c0d182200b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 409601124 1250 409599874 409599899
    0x2012f030a0519150e0604020301060f11190b04061104050f190833010e06060a0908190618381009050f04020a170c130506010f02010b0102030301 64
    0xb0501c00119031001c501e55501a40705003940700340c41031390348102c0900d00034112408100103001070303109510400c010411070350081d0b440c0008002d141003c680400c848c58805080903144c49070345542050080c00d020800614109551040d031081d042042011403507500b0300034034060360150a40040d2820302d01c03003880c035007010407580e25030030f0420a103000b984076101c0a081c00003135204200f40c150013820410201c8a4030030001f6401c00700d1095100f032903141c052034000c141d401601541c05030341c0000d40c03407404030301c6014981c0181c00200e00719860b03402a0080e0511080007143d09860701480c0c50034112458110b07852500b0510380081d4541e00b42184a514001e100034101505101d2580d000c80c81101480940c1203c0d206480001070040110714008481d0240e590040c1601083e01220007000010781d5000418001d94694951400100002194083c600100c4c1c40d03415500c01780c0545034100b1160250447c51141e50281d070b03405016104000207a00345c3d00c54007141800340e0428001881000201c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 409602374 1250 409601124 409601131
    0x6010605070f170c1b150306041409060a06050418021207090603060902100206281107050706020f061006080c07020d0501050919020604030803060102030c0d02012f030a05 75
    0x219101e0100859035600502104450f03d40345594a0209554801c0082885000b035004152501d075990340d401d05000560311211490303201070148001c0041740b141c5d04c03680d02c1041c4101041203001c0041c2011540e555030303a00221080311442d818403901181a0801e40208c0b4803840b141043e2403003001c5d4a508105c071080700c90f880020395200d1290001803d901e070740141001140240320024540007180140070404002861389001c1d0b5120b075003401584203030180003842045040181d211000710304000d18028040c5030242e50001a004100002413101c0803862a08a851603000c490764000c400000588a2408407981044001c1d503020802c05280500d61440e88240d500313202c0e0346072403045c0c1d0020360346107042101650580c0d0f44008210405208004009079101da0300c4458210307005070740c0003900f84d11640c00014812003001c0b0120b42d10764001c0081d1034490700e100041d51296400f0f0300009000b81340118181c00b01c007074641712240f9201c0405100001074100345100d00d18555032000000060030015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 409603624 1250 409602374 409602383
    0x30403140f0a0b0a05010605180d060b28050108011512060e070203181c02010c05150421140315031e0106090609020c030913060812070515090601060507 67
    0x300071481d010a0a000340c10142c0d100340c151801904020a81804648050304070380d090010402004000701100201d02031845010ae5400c1c580349240d18008010f445820350950300703c0880c103045d0a044a24085452203744045220340711140d54000444110300280f0851852000440754004098851054080c041da410500412040da0300e0404150315601100c1c82e000581021513840d84401c0c081d00c40780c19a210440d03010048140304c0450404d10a0040e100905014101400504000082c00340d003183d054010301c103620f50b24060520f0f2010050200c03220b8413410320f84c40100385a0f4013031003101c0ca51008081c039071801c5950300b448031209141c03c0c01b10176905120f54045c1c0e103408003807500007010b0914400008580940f400c40d6070019542d99030000b07003080c0c0c01449a13804000c4004162181741c5421a08130303c5042c001d0020100030b02442c0c01040345806500c80c103690381d00480d0700902070b5910030300444004240200c2a01050281928076486079003103c40100700251089000d00b1800c2e004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 409604874 1250 409603624 409603633
    0x1b050a200307140c0103090312090516080d021501060806041a09101401050f07110a031a06090a090506160e0603011205120a08070f0e0303120f090304050303040314 72
    0x900c55590314641200708102d90b951114102c3c2d031040d40c0c0130302070300403c01802e08092000380103642d800303004141d00c0b5032088040b1355560785c03d5041c40030400217440c004003041184916292120f2180740c41e40e514504074805440341c542c442004829201105049aa072960b444641b40c844008010241801c50050800703215007407401e0010b6500c0f0b00015010b0380d0034000d94000b071031525003d0b00d2040b0036a6080c030f05110040c1300b041c4505400c6022142400c0e40102d006100b0325128002681c070000641010f40001c9900340303001400b40003240614010380c41100d410119030345d440710f501c0c1901e0841200400300d4100e080032070140d4104484105003c04142841d00c118045140071610b00d41090b4050b0060085508843c01803000a124886e80e4008600d1164680340300d9040252081401500013820042c0f602030142100744900b084010f2010014180c964407244c09880d070b1480038040c0c424403507403d00381021a000c1440081140c0c00c46101a02942c1007600d940c0f0740c040a8015101124501d004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 409606124 1250 409604874 409604927
    0x103090b0a150501090e040b090a15060801060f08030a030b03240a1a010903030c020a051f020d020d020d1d0a060503010801110306090c03040201230c011b050a 70
    0x340181514490700d00c1e80d038000742c40c0c2109031002400414592001e4144a08245c041c4800341003c880b180e48960448550522616150142890205a8070014001240c03d4110038400c21040e0811012114644001d01c680c60b211904031880d448a4482c030a120b6004000090440e03001b5001400040802401c0d2005d000300060114020150142c1c904003170042d550801c0b60450300b500c10b041d0041d8403200f11032000451a03001901c8100755000203420f010301f0315403031021541d640004034003402010708039402e603810301031341851800d400041c20005402076000c01841144000b541000300e00c1d00794020458202030070025181e071844204d10b69020f10f06d0700410b10403030302d0f0b40250f41d0081120b03a6550f80c0e40e41c944890789007111862107001c0c0c0ca05900300b0600003036070b80c3c403040c00d501311012807403003a41e0351520b10041c1c0301c0c03284030350024804101003000c282d40b051400c001b030881d010664009001407180c005402c0d10b40f507446440c101c081130082c001c1c0f2010601c1101040c81080c1c40b15072013060f181 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 409607374 1250 409606124 409606133
    0x3070c11030d050904180804050909120a030b010e09040206042702070c031b0e0115020a0b15010e04050f1314120306011d030a15020405040e03041e0e06010e010309 72
    0x54124072042d011800c00189650700307042034440c0440c0100c2c203842c010381c400b209544203202407007240304092203a405000840d038889800c1c41900580c1307000c50f2800740e440e0070540025019020580640340400d046507208070030740c104043c4091269130300412140ca0181002c0003c402c5c1e04580d900201c0241c51001c111034418440d100030107509008540852081d0302d5843c080f031049164004600d400c03520002c00f0001803040a88040c10345800742c10b440c0021000c0042240307448409074000d41280e0903101480310b400350525440400603801c0c1c0e5000c9404010405010030b41d4800d403040175100307050000051125042c0305c24655520721448007284101885103402d450036244081d03440382c1c2c0c071002080c00f409682200000920f251000c2c602d0810045610000f03480d40300255000c0e01131540221302142d5900e00d58101c6000e050014010418502c0c40400340703950360082e000d542d008507404400d1071000791070001204111601d00c0b007001d0050b5901401159031040b140141c5040c55250002c1a0005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 409608624 1250 409607374 409607383
    0x1120c0903111e1003090f150b0303070c1404020f070b0601020d02010c050d090807050a061e0b03250b0a021005070e090114040906050a0237050f040b041e150503070c1103 75
    0x2e0740a00703044065030f0450708c85002114800085035210754010055480054412000342d0102c494003550740407540f0390340011401921030852040310740b0000044500c108030498104900485080e030803540c141c505032034185e00321703410900040c02044040c01000382561040c3c00c0150640e05c920f0505090094960342d01d803402401d20400c9035056200d040c0362a00c1e95030200318040c60111104140000c01b660b4001c82e80350b4242b0003107642440e20b10307a0700c2900d100781050054020b189000440e030340c031417408500940300c0241e481c000540e98100310114926034491442c61032494402009140282d280040003100c8001c09039000c0d4005072200391980100d03190307100715881146c4190380503a0b01c08005520080c50f1010905002c114661100280c412041c110728a40c44000c150804680c5c640320354200f48100e004580c8007120501c000140840c08070486440500350301140c494003c00c05460301114032144120000c1180000d0050001808207441000c20304031090080450020814111000c0703400e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 409609874 1250 409608624 409608653
    0x5040320150717133309060201110304080307050703030b03010221100f140a030203061303090918060f090b0c0a1d030304090b01120c0903111e100309 66
    0x64400440e000060011500841060544201c1030504d0318164211550040c8480d00400000342c416040090b41c040b901103100c0312895014650002c0500f43d520700034001e0155000e0030005500b001103001c7c81950035025a4000d030b4bc042e000750706542e54880202e41070340103000154201911041c40d03945a8508cc8002c2140e45040c1e0705440b50013402154020030200042c10b403980700d16903d03104010548003692030500b6100b0040201010306510703400603400078080c3c3c00180d8140100020b000b04450000d212550241c803907160401016903c91034030085030400c00300049200406a9070200040159102000c440645000005c8494140c0c4550f0182c110403600d01c000c20303000041c9000c409800a06400042d14070194035036985a6400100e07031240201c1c81010a17558882e0007030011030b03024601c07010010312851000c114802c0d80240080c004000c611003a01c0360301c031101c9100c50500704480c0002140700c28a8100001d4235004041c00602052a03a8a000700360b541e8801100081c0e0074010f0741070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 409611124 1250 409609874 409609909
    0xf060f0603110f030a030305062806091a030712110d0506040e2b090b1201030215121305010f02040e0a0e0601060f03020c01020d110a030507030c05040320 68
    0x115103007545030042040c0040b080c458424403d000788031601e65000a030420000e541460040381ca0f46685c1c0c00704440000c1051406210a0340498010704034040710380311002c403207541da111900700355204290303541454240405010400108005150f00e4000c03691081d0060001d0320000e80d40c52040101c180540003142440c95140d1114180400c5280034002c00c621812070101600c0790003001104070003440c0c0d440311840070240c03045041504450151840c0300040504501e2182d69070210314070326800040900040f480740c0c0d05106c7c4506450003110a0302e40100b0215004040f50301d43d102e07485c0155000d024110381942d2a92010300c0c0c0c14003d40090001030103403191155240c18180c1026044c1c80c11614002d806a01c12001040110340c0880104c0d542c04c514100140e6600580010b24068800c0c1d049907508141080d01c10200c42003408002c010301000c1c0d0782d0402081e111080201c0569a41c80015000900144010301c04900b440b101c2c0320a0303034100328120401000080c0468240081c0c17034000d14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 409612374 1250 409611124 409611131
    0xf030b090601060806030a0b040f0506070215131101030e0c1003020703090b0a0212030c2101030312050712020904180602041e03150b0d0c030506090c0904080a0c0f060f 74
    0x2846a00c100601030140c4000c0c1406485490104003299559100f400064141904000031405201c01003140000f45904641070710b10500e070241c0081d40d0b544441a90b902d82c04070100004000104801c2ca1220325940040c211365100c895000450140c84801a20b6185000b9484003003619a076888412107500341c2030300d0150f1641398508001c0c291030034a034080c0c07402c1c09080204004655010440ca94007858640c4659102e0311050400c4946014502c0c0c4200c811100760585c0307042002021036a070490348250341e05250b0800210001c41541d60a994040100700150364505103146141c02501031114041c00005000750b400341c144104008286040d01c1d62940000c062009a180015040f0055016140080c5c0646907030745500002808034450748046175244e40c6008103644403100c0c00c42e42074125103410b2401ea240c0c00c04548031402595602d4040c0314407120480f050810700d400390710031a044001d0b113040125110007039038100c0032540101c1c0c81201420100e4001402403040d2001c00b500302c00000b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 409613624 1250 409612374 409612381
    0x18061d070305011a0a0b0a0302070f08030f1b0702100e06120f0a0b06190309020d020603041208010f050105120a2705011a0f1509060f0c0c060304020310150f030b 71
    0xc03c264901c0c02c0100d4005d2110080c10320201081e24119002602d140c500181d46107804d041005c02903090380e0000304000c500209001280204540e014066180354803107455203049414a10041d1003410f2000390803803440c011607504c040c060000e02048040c00703000c4a01d045c0c0910b0150701104d001b02c80c5502e50300c041909001c81031030f8070300c5000c0c200364083c0c4026181c252020003640c101c0c3e692072002ca0801d0b84a240c80030441d20340c0d18a165556901600792900e90401e4545102d5150f2004080000208030000005001100300c00c80c008680043c0c44191501c0c04619194510f91b200400740e00085884881240100021280946008400b00004040995103103007190030f44000711201c601c1c1082c8004029150b96400640e00303002002140c02c0b450b4100600c03003850030381c0103c95035943c1c004004035203000c00004000c01003540001e01c1c01961500c103940f40811100d40030944e00139401d035010043c1c003a283c0c00b00b60310111199501e4411103440e161b843d0707000d10300b0b44103075002140d04206c5807060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 409614874 1250 409613624 409613651
    0x3130305010e060a150e04030c020901062c10120603050a080307090f0506040b0c0a02040227040e060f040c050603072106081f0b0604080307050d020118061d07030501 73
    0x503650131540046061042209402d21610340342d03c14025040075071040c0011508042c011070308010001d134040d10344d590669544102409007903001140d80342c0046218000d9030401203811511104460041c54405034080c10346007100c0c4115401a10315085542e000040301140f0b0802032054000c0c4a50901513680c0760a0000600414259109102e0f0400c0c00320b041c80720340d0b11281558142c13070100c044261220300078404107180a02c8441d029410520015860720110050294059100d1a00d85c9801404c00584203110458008c080720310401c4e0400030215500518101015030030038003407020001c00c0e589039800110315610a44d01640030550b44010740b000020764521132105071080070000c2044601c0c0080302c5844000300070702882c404105880ba01c0d4165400da022201440000c4d252a84841d100c1c1d04d459030b01d51101000361450f2055003c8003142d148140101001d140c0c034131004411803d501d60b81c2c6009400111384202550342d203120140c210100402500c80110b0044001040701501e0107107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 409616124 1250 409614874 409614883
    0x30b0702150105100c0203030d15050a0605070b0a4a060f04021002030409060b04030b0c2104150e01051503030703080408030a0b1c052b080903130305010e 68
    0x128215012480c0c001000180d5828036003a0134190541030a000c4d074900e43c80000d0851099508003a0b04500e004442e02c5910303205606d0405503181a0b801c44803a5032106015a0140500c2c00e006005c0f2122030f0000340c202da9540c20030441240542031030a13042d001d0030301a00d1401000b240c1c08070f00c002d040100e0318403040070320007501034035044002928141c01e041c1f845440e482402880070b80240003044d034107540a03100f0003c4800401440b04100f100c0f613100d6020306150740c01840150b8a00e0a0200842c125070f0b42d4104a44442840004480340040c1189920303c40d01c80041060741c42d83c0c80c036000001c2c9403440307004508000041c400002594503011044018a105400391140250701c01d11103040001d800580c09904150080c1c10b4588035030365241c45c0400751204601c0c0c8d940100c10310101801c0314240c0030201c43d03414460350545156164241c0d81050002142d803098400c8490760035100c0c0018021b40040780c100030b20030141ca2800003050b00200c2c1301c5100703034011242a03540c0d200e00d036001d900c00e10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 409617374 1250 409616124 409616143
    0x90b0604150302062110050f040c02030c01090b011a03060d030f090302090711070b0306010507030c060e0a0c0609080a02060403260c070501080609070c120207050d0c06030f0917090f060301030b0702 87
    0x102c0701c000d0701f02808180c0b00c0c580d6240150186940300903c821460081059900076400c860003800700f00c450b0b240c1404044400e1003440f0080d80c0d1581d05503040381511080e00d00c604005800c62001c16000d441c106d40c3c0f8281200c2c40d2043c065020404800350f2a2100c001d4464402522a81d500343c200c8132000d07161441d0355109414003102481407080903030307000c421a54000d405103804c0e01d0000c183c0c200f80b00100241a40440b0611a4038907140410104000b0641203030100c0d11040c2d8202d50300d032581600c460084200075031000c4104000d0000a1000e081c494290503a004e400f50151641c0c0400031280d40a04102c0342c650303200c48400c012075030303000d0109a0711010560f144841414114400f5000c0300100e41e009042544c00c0550700520340c0308020001c01090006c261001c15121800d081056141d5805040000f030704242031812a00e540f405041050742c0c4c030144202840d0140b555a11460f003000c0210355001d1075504201c030241e500c0d0070181d406580102c03003c0120341000132005c0d01d410100c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 409618624 1250 409617374 409617391
    0x3260c1c060303050d020d0e0a0b04030801080c030607030903181e0906030807060203040f060207080405100807090b0310030203070e060405180c040f020708070308160201090b06041503020621 84
    0x16000e00002c2d9004d000c2d146458403444015840d0004d4203c040068200204410311920030a64000103101d0404103071401180240c41745040e59803030300b8004d9120140001b40307a4060340000c0110340300d1f52282e0300840781e581c06860301304160304140c0081c1d180c000c5a9030113904640c0b000e00d0b4000c09005005800002425440c00c03c01c00c4901c0e680e02c00a06001c1c0d042c0240410754003200060510128041a1105076484042155500c1652601000c20780090003598002c0e01a850340c0004c01d405055141c2c020300b0903480d4980700d03a24080c01030540342c4c0000c294410001c2a44000001a10100a00c2c00034102441c80c00c520380c505901440211480286410001c0c0e0342554260586800450000c41551060750042520144403050501a2007070040091428100140c02c2c002e245d40510014000c0d43c0e099402007a22240443c200e00740e440b41c1002410b503940b20000f0441511301540007144080951001c6024247e681d000617010350000e10540306003480600c1f81d1058000703519102030344070200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 409619874 1250 409618624 409618631
    0x1d0706030606030b2407020603010e0130060b01021609050a050c190807260912031905100801021308060a11090409021305070e0102150603060403260c1c 67
    0xc650000350f00b0a6407003001d191009080148011884407175044030315054019105036980e5030368100c000c070450b00901c1124210800355441580f20602c11b940e47d800c4d0031512660380824442c1c0c1e121080280305104c41d081c10b6109680d00a0042141c0112080091418000002d0b00d450001413050941d003000b8002254940c007001030785222420300c0f03504010303c0310620300750b003013a0788400301a5480c922000c03070780400c03c58010300e0f848200590403d0510a00c0d07401c0558034820389400c240c40c4a4001628101070004c00c01d14a0a00410158881a03008aa945034488103035540c07031016089078402c41c0d44284a4550000520070103200b00070041d005000b0b11010061036106031840e0f5040d000f811782c3c4900c61501c8103035084c15903481d030002c03494104908008000034100329a010742041d501e0f80015001d4010b51030f040328159003545001d4130135400607016210030f66540d641100d00c50325051700e443c441d036203414032264083c803003034003e0340724a1022034a9981c4409c4040341d031244002440103030081506 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 409621124 1250 409619874 409619891
    0x50d0203180d022b020d11010e060c07020103150e06060901270f080a0804090b040f14090c0a0e01050d030c0f0f021315060f0207120c0603140f0106050a031d070603060603 75
    0xb400141260700060f030346002000d40e5147e10090740580304240748540305114501c00c0c40301a040070002002124801d80f01000008624211807408280510511a103d04905e0001d202800e1a90041c000804140340c65050211500414650032000701000640c0c02031696003030220041c1e90785c00001501142c0c00400d0215090b617178000e0907102c1c9002e0000469142d802d10181d07a2129009042c0300c2c6010001840888000c0c0d1059046040407901c8000ca8415211190a1390070211940b205507904d200302549680c0c20802030001c0380b244003108a04201c07645082c10302050012201d04100784c80b4030060180807155004010015101045a00c1c0a524202502600ca0003910a40c4229001418070040e07540c0001410ba080000b968010700c074080800c00a030f4200101c01e81d10740145c9010351070802c1880c0889000710700a5030102ca00c0c1801e484003030010302205000b503001e800d55a00d586400308510114013010b007101805600b144d5610340c0010028030407540c0501581000e030480345401c000902 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 409622374 1250 409621124 409621127
    0x6020d1521060b090a090b011401120509120d0b010f03140f1902040815150a0306020d06051809120a020c0f043306020d050d0203180d022b 61
    0xc40e495120a00a02545000c604000b1250404050118001c1614150b840d01c140100058258a042200c8a40391800003003088a5185244c1c4118201070703684a0705080303000d100e00b0041c040640b2030345250bc5200d44a28a4009842c010101c18030b0001020a807420103100141100340c40d00d44040130b05040450419002c1c1c00400815400440c0c485840b909440310f003104040b099038400581a403500014000c5500d40380002c122a40d03400c515041c0c5096540c2e10140d03111b90b059a80303107a600c481a09800c002003142900505070004801e200040c445130307201c0004243d182400350100b5504000e41c200514504144091a000401c2070000c034600945040002d4071424031108251051603607a180c6c01040c0c45980c0010f0018902c2001c2c1001c00d4440148071481e040d03201c80020340c20b03404400c04500c2d907102150025224a0a4856604083d1106680c4010b500010891181204007104800e000c0e00104003d0407860203580141c04520250342000b140182c51480d1f01c03c3d81050f540d6804800ca = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 409623624 1250 409622374 409622399
    0x10c110106140d15062612070203030406180f030f0b060901030c090f020910110d05041a0306031005070f0e03030f160f06060f0e1e0106050a0207050d06020d15 70
    0x5030f40030743c0381244d4a550b00d09110043c00c60f42c02007500a19000b4120040c0724030700e900048052100d108444001901b01c595401520660310020342582017071104000c05801103c0000850516080920782140c944c1c02d031107140b21a80c0c1c815144004c1e00381d8544c00340300c03000b07032044e400580c15103032008158115201c1d41c09a070003d100d061911991801b03103081d080100e5059445170b01c801003451030240701c4104007c2080d41c034941c0720038450082d200800000da00840441c0d0807141662804240c048031040c01208603000280100d405001b01e0221100c40d820910596100b00819150002014041d82d4001c141110707404500b0300a90003045410007003a011780030b454112014a40e011840109031520700c808000340d003401071016051010100315220385031451819200402e0140c10030b642e071082510403040070745e0030405000c7d11010060010920810041400030001c1c011160702d03aa8410203c0e2000111020a43c3d030168041644108000c0601502c030110380101803039014181452004402c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 409624874 1250 409623624 409623649
    0x1f02031e070c24140402120d09120c08010e060a0605031b10090e0a0501031a161103040f12050f060c1c18030206040605090610090f020c010c11010614 66
    0x25240d0114211440300c941d40c21880f032100304444248400b1a05403440585142d06440483c0702e4600781100714401d00c40000c01003d540c450b81d440c88040f030310341096540c1d081c682e01e6059580310300c00364002c1032a039800d0048416880d0204018503032403500c0001d0700101d9466402c460300c40c0e00000c0481f8196000d45403201c0004104440f42c1008010500c820780c0e402e00d80da8012807070001c01004200e170908099000e607049a01807101c0001441e01030040c81d0052004035030701490282448983d40151340b14401d05000a205c131000c4a103032603243d07141d001130a480c80c5e100500702040301160204001042c00020a1031850900034a550309004e1908001da010f581320940004840d611340303030070203a46a013080d04090404001110790002e5810b0007910b4510071501034620a0074500402c603070703050003e9080d108002400c05124100d0070282c1d4003002d03004043d00001c5640e002c1c451051040028030620027081240d84401190248040034203017075444507484403d5041968140c0360180d11b42c407041441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 409626124 1250 409624874 409624883
    0x140a0209012103180312020307171201031401110d061701110405060307030207080a03141003050c060a12111314010804020d1401090c05030f19141f02031e070c 70
    0xf41080003c50005040c206071707001501e6001070940d0680c0064000c00240451802400070b403055045a146035035452207020745802c0401829030040000c900d00d400c01c008a2305a96002040ba220710f03202141d001d03080b510340308490070394521080080802c00340b11090300c2c03040e00c8028081102070b998050f915005a1060900a190001c0020055442075040302e0005034401d20060325400ea420008000b005862600d01548212401207980d00c10907150100469500900802828101009008035500201401401d014132281c040169040c540202c40c14815200c18482d1103240c940c01d04880c190f040e80c08010441d00405000700d1a076031010200d0340c05901600c000711354100c10b1901007102d6518160a40c995441c2c05001003c0000c0a660b420854208030b0480d581c003e002e551041d1910351502d0040d0344660080c030036200085180b03009180740350000043c0e034000c004100e001c4250b046d0b00e1002429460b1b000040103181c0c43d540250400c10a901c030300400c854075041d0b00252004100705000b51 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 409627374 1250 409626124 409626137
    0x515032a040c18060e040e03090a210f1202060c03090601050d081903060315020906040e0402120f010b1e0102150a020903030708070c090203040c03060209010309140a0209012103 78
    0xca005000d52510040045009002d02c2e0b0182d1354580103000300649880315100707900f001d40000c0c408000105941035504020401c00480385001c1400724050744400710282c01642402c0c8050106210080a404030750141641400240c00024000d06008006088401d40c06040c810b106e568000082c059054407c00c0c0d07a1551508017034149801140070b944440c1c3c1c1c607140c000600381d80903617168001c407040328030a2101c290b00301019032035003040c0c1c02100f0000350070040130700040007621582d82c0c8260300701e400500303440042c0036002d440a044c401c40740c110502d0b1303070344824040c1e00724141821204600060340b041403003403034100c3c80000c0d00d4890340300c0100c840300451004a51a240294110b44030700400600b1a0764851513403034002c40a4000c0386050702c0d14070940710300280b41411802240e00c101e03400001c1c0d280e407e00b10b80d261b01c000d411000c010b504141e900c89110340000c0040c0020103608813054010700b090703143c40c81000b90454050b0807002c06070601d03c1112100c204d07031050b40090b0561604250 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 409628624 1250 409627374 409627391
    0x91e07080607080f0c22171e1036110607020627120d03150503060402010f1103040b03010302040e0a021309020f030d1e02030c0c130b040515032a04 65
    0x1c0c4403c1001010b038aa00c2105000c0001f904807082100b8482401c1810958003141c81c51154a034002520400c00d0360700d60004080c50b0f0600c6415807240c1e0b01c4603038656895003401900e107004030101d401202900b803081d11910030101804101d490011036080f0848030709140c20203541c08118940200c2d064840c0000b402402042080241801c2100600780589640c001c1c0304c2c08251181d580c0da40c50007000c0400c1c505000c202e1402d004201d0b41066a0010b0028845510f465004465546007121860100181d0b59420a1050300902c018002003107001f00d043c3d00d17541980100401c4034240388000300703160b0209452a0043c0c4454131800c000c0940e0440000e40d01030789001203002d11808103e0301d07038140503546c900501c0c41d0b00000d5030700003068150242c11140c0b807182e0040c0d07a05d00c118124182541d0025075904801d140ca007040903240b40c080c2d140858948103400108058604c1510381070002030342c400d400c20050800304088031800380200c0b13011600c00405007940710481d011001d503c0c040c030f0300c50b4100d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 409629874 1250 409628624 409628647
    0x20703140922061d091b0105040905090a030e0103020313110301060504020403050604050c0109080628020a02010902030c040c050906070c03020303030c0c06010501080601021005091e07080607080f0c 87
    0x2d582589003814a5003198014000700d10005124500501e1402d203d90603d41122000052805100d0070b03540d00201040b00b0342d0301001403201c60540b0501c1c104038040201003640255805401d00602d000401046482c206203800b426030626030398138904242c07040c8200403441c0400354202d41a0742d0400c040304407a840f00c20129000d0f02c402c0c1c11850300140000303000020000006900c62242d8010f006a8007a50321040044800608078400ca08141d0700010100301c912905048002807000c80301002c80c0040b065034400801e130303041a107003080541d661341d05803c10341c14180003c01c141c0314100c0c0d007000100c103c00c4001d0701502403904198095070002c20814100000c1c44103000246400030101c940b00d00d030113161041316a00c8100c1d10800740c024900002803650007415014060b01050700135203056021a039a42e0700510006000402e80e110f80c110500300480c5841381c0c1c814012001014007506030900708140c1c94180d0180c035a4040100c1c41c000c01c80c2c0390340c0805800b6003041c104440681d40e180507909 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 409631124 1250 409629874 409629889
    0x170604020d0908070c0b0906031803040302090112120810140d0b012301080408070b0403030902060a0914060405031207080409110a080f06030613080d060906080708010207031409 78
    0x4166100d03107045030b007006004a04014060880c40341c00d201c0d031403c3d1900c0e402032081c0241e4403003d40010051001c541c5c10000501c044011940d6102200d05240d5a50000f0389220320a034400e01341c03000c0c076444c00c0e010b002900d952031b10303141003d050511040c02c0648401ca8189000d100d903081108010402c0859661220080421300307410150301e900750b58440d01100c400b5003880d0283c680da05400c000140e03440d400b501d00c0300c0c4143e411071071050410f441c1303031101140600300800441c04c00d940da49207000141e451002915480c0c41c5c0d551000e10b924204410310302841e0580201600c00c2000380000c000700d640015918400c142c3c80d624003515072144c5d14209045001e26000383d00214140542d00c0440c00c601c5c0058503c40e545560f41c04056103070560000380b024419a9001c1d0550040d070700050756486284107003488a40300300300d0b0900d00030250ac072070f80807030b6415048240d41c2c0380c9030941006080380410a1f0000350041d03000031803402c0040ea4001d031011100018201460002044c17482c090750740d281 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 409632374 1250 409631124 409631137
    0xc0c0a050a0b09060f041512060602030307081e01090f06080a0b0a0903050c071e05060306130c0909090807060510080d08060105041d2406030109021b1507090605030717060402 77
    0x2c245ea07880300d4466060311a400300c2d9a8400d400208400c4101d9440401c5015000072190150080c52854540390350407115400010b04128840c040060805684410004c1646c001c144500e000034030642040000010344115078005440c40d0b004400c2d000129048130800c581000d825480002c48910614054944d13000e0181044c0c40c500401c840040d02c10003507080525040c1c0350860130b0b189a0b84450400049004c141c440603000540300e42d45d5048120b4941c400e090740203883c103007090125078800440c801c0d603440a81c1103511150110f009410085075016154101c0d1802d421103a03003d0400d94082d5807541c1d503a41304020032001c1030128803a82d000b5021100508a002c25000140540000c2a08240030940d00c0d0045880a030100f1030344100014040030100100a01851441c2d18004400e0040d400107401d1292413840707000d26100000c800c11448201140902541c01c070341c5031141c1d01800da0083c9601c88000d003c0301b041040101070740b21005007440c0c40740746602c08140c0c5409002c03078000d0040c070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 409633624 1250 409632374 409632397
    0xe0a050316092a020c0916120b1c030302220315022206081603050601270b03040b1b0901120c110304061701140a030b0a1e020c0c0a050a0b0906 63
    0x1050f4032488a5070200e0171650f415010f0300d608a8a4640341070b00e1440c0c42c0340c41c1018001491100144144100c26004002a110010943c44418220301c00e070041003525403030210042540021403001800d6a218403124a68000115100c20703403450310307803404030b07801c004048040c2503001841203001d5800003036104d14820007407001075006480c1d810180248009403947c20103107846121034480a40f0a0040d14400c990603501c941c002c240011803403540080d61060383d85908110300c004112007a091002e14451409030854010b141804500c1400b1595002c0710411400380c00c01141c41c00da60040c0d074a002e5141c848600007000c05050200301c44c9050000c00084450000150000340c4540c0208110160308000810000c10f99032180851042c0e01d941c04116080800d0440c200081600c4a00c01544003d0046000c1001000d0031038891070710800b0b4038418450f5501040200d00c0900800c9084502d945c00e0301c4d0010454140700c0015031b1362aa5114070001c5e0100010354150a07118103003603d00f0500780 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 409634874 1250 409633624 409633691
    0x30307111903120507050c1e0112021e0405090703060e0105100e12010b040c090f03380114010e03100b011205040c170a1106030a06080307030e0a05031609 68
    0x14800f00038900d521114003954688200220b0503441d1071700380e4558069034411060910b8010b034030340040d0761140d402c80000301e0482d4240401d44884004075400302414883c001115503d42c14042006079412029184004241c6815810300103240c0c5d0403046419a0342c11218940100c0c2c19500850751401c546d0300070b5030070440704036130744a19640541015400c054215000c0c4033700e03403080030704440790100d81c81500d1040148030303001c00c0070605042411580b4a210010721400340c1d00314121403103014021290200a100368401004581415090403416907400d21b0540340d01103184000954850381d80c4075813071121740d55010700801a03004d6802d59a142861603028080c40c03415042001c00241c90340b01c1c80c2e5007401c503e0300d203824604012446620365580904d00e00304c816004014803070150030003070151500c01c3d17540001160240c003c2014044c0148240d4441c440641c0030000e000b81c513001e940c861401396001840464443e030744688004151022030100059103180032000c0c0d81d15809001030300ac0d08441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 409636124 1250 409634874 409634903
    0x30406030915150e160804120e060f0c0601060302181e0d150507050708160c0b0c06070e0102010e0d031e09030f0e1008040f0609080301081b030307111903 68
    0x4000c03c903141214003146014109a81d80100500c1400c02a0200c07000260684009030010741c00c00e407808000d101c2c501d08041104140c130082003043d80301c00d0409819007000701e0350721b10b0b1030400c1082d10b0141442c0e260550900180030101e04001500080b40c1d807044125000c030980601042c1c0c0080a0031600810001000d00c00f42000382c1e21101d1400100c2105c0e00f010001400d0f02d010743e0484200540c8410b0440c504000c1e80000315480040e40d00858403194140710001d16140007102405140800001600903410480d0b0301407e00741480c02180c0c15039040070f440600051000ca69a60480791b1810046126041e010340402e54094403915961f09a241041210626502450000141e00c0b00e484e22200f00b01400100700001800d082400006529000041c001a5207442a507160510a11000c6161607480e0380380103040c0c200b41c0001d14641d00c800b00d08800d41754054100c00302e640081c1c0185107000e41648442200181580e2b03050f0260018212101401c002c0383c1c4024021500a4259a1100b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 409637374 1250 409636124 409636151
    0x31b03010b0c010605090708010b03090109080d0b040b1f1803060f090201080a0203010f031e050d0e18040c0b030637080319030b0409170415090602030406030915 71
    0x1041000c44001e59864001301051303d050109105000700c0003601c84500c1c5a19294009142c8c1d400200700342059500c8159900c00240c041d8080d10118103000004a8140b10807070034030040711800301c0c50500c56000f0b6140d035052010390054800c90718106103041019411100017811140c1c0c0198030040500d07242c44c3c5a10b109106683c4546c0d00c0501c00d98810394662682c80320041680800c0c0641c0e0300c1711a80c05020000600c10883e14440d03042640070701107140740c1e079446d02810901e040d007242c80401c01c0b01c0010714140c90310a20240e180c40a00701854481d0420ba22103800c07030109400798000c1c07103d0000100d03034280e5807803000345480131b103c1d072040a5a0031a001400354150201446001d2142c1c0780c40040799044011003075074081130b0900302103800e445c1030102c08c4018080c14080580c005035200c0c944402316802a0084032100083d02c04503a94510b480741c0c0036144607501001d1020450300001c1030082c164080701321000c485540ca408a070b06500c80c101805c184100d2100112480c1c500000030301c0e2503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 409638624 1250 409637374 409637377
    0xe0d0609030906050304050705060d2a0e0105070803010e1015050a02010b0f030312101715070f08040b0601051c0b040b0324090a020a0303120b0d03050708031b03010b 73
    0x280310303680300240340766528400c4d80c0501003590020056001042c05006034202280500006500010301092800c5010f01c0340f40030401104482000d20410b821101c0041e070000c1103400c0d03e031020b280252030600325445240e154001800b80f040303450b0300840840d500031000c14071800a0300000951510495174017070042c1c91035110803a00c2001d0350038404540c51a140850300c4140384403014010354603000c10740307140e0700030500020121100080141c00104804004083c201ca40360400170041c066000d010881d00240c2100500d01000c10000882d00030003590b0101c003540d0490390080042c0d100b600e5a00068400d0300807a009a500c0d00b141544207200e80380c2c03d801142c800502583d0030428100000145510b80d81c4404010f400c9004c00500022071403a504c211580c01b40140003590000c108580c0040d220000e1a0b00603270004101c02c021040207407581c0714010000e079046441801d680c0031030b5405025801441401f43c0190008000100310302040716241c1d103e079490721141d030303529138490311100002d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 409639874 1250 409638624 409638641
    0xb0711060c0d020f0c0d0309030b18030a02030c010f06030203070b0304110d060b12010911010f020705030a03180803070201080a050705070b0103080c21042d03080415030903080f070e0d06 82
    0x102d120702c1c01d4045d6103080c1680080b80301d540581d5a145402e0031a00e801c203070b81c040545100a03a4100b440c0701c1314024001d0018042082d125400b540c0d503111100e030300e079007591504541e5800041c5040810401640d00041072011a088000b0312030703ca5656061210070b00703c01c81509074001010071008420010158810758440908036000440108544d02c0c45080350502a002060040004009075080d030003521800403010b103620445020944800c0402e00b0125101e0048020a1180d0b88030390791195a4108000500f6503800254185002034000074840000544400394150b91032010a01c140d20480855403c1038000f50f4807401c65940345840085980180c180070550b0160b4050407820200b4410b0344101580ba925040d810075081c99000310402152114506054090000411041070150088401140034102681e03c4506d09440340190207546101d0404242c03400d0300140000707800c03800d010307004004003510f030b82e46903114001034486448001c11254040d4007041d22004204554008001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 409641124 1250 409639874 409639903
    0x10c200406061803060b1534031439061e0c0307020321071704030c140709141911030103080c070504050702010c1103040b0711060c0d02 60
    0x7026035221021150354507022a5003040710004441000800c3c05d0303400044560000403d401e032540400d02d04420340380e004e81150010043c1500764413103d82d498401141d0325000510314000304400ca0740d4000c02d000c050103140c1c0364510000c500381d410b211000790342600c601c1150307203c05e4500945102c40000c40c0b902100344062031081c0c1001642c000b032540d040707050b1812910fa0340c40994991400051554000800c00c0301144814420b0f01c0c00410164514241102c2c1205c401146041501009000c0d0b001141503451000030075017480006039118100b56446600030310941ea4a8007110015800c015450380300c3d094103030801b44070f900e2212400c03049602035080080c909910100d80c2e200d00003a11507030a03c4007a955002c0c00100042000040102906041402600d41180d20b420004040352401d40f00000141e5480c030407069281d4102e40129a80c070150380045003080c3c40e04903110f98030301c42c8900c02041105480e66075401610343e013081c0d40d944e54081c41901d50b0400010002507450340b54050245 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 409642374 1250 409641124 409641131
    0x1d04050706031e0b0d020405100e06040c0e13090606260607021e0106030209040807060c140f0c0115030303200405010c06050603150106110d140901030b010c2004 71
    0x80d029010744a2800c01000c0f00da54003244501e80c000036401028200800f40d0400d16032007005005903903910030b081c810352070a402c4071002400c2078070328049248010855409945000e109482664001003c0580150126101200742050801560242100c0140101002c1c182240410255040308074410101000c15041502e0100300d02015a511410f4880401581060b46960b40b1142d505020340e10700510b000000c0380383c580d00c2d8081041c0b26000c4030f06507212000402c00c001009460300402941c50300500e490602d44000180096945c800c0c0c161f420010703d0000b655500070f1800f90005800405e500007070402041c0e4a0502030050302e925a4508011109400b41e045500d850800b6641901c006940e00f0070090050390350700c402071030084c1040d0792501c50400c00200a103021403410340680407990395440801443d114a034509032004c0c2c03c81e41440765142c21040b000b02ea00d0103071202c0e48024a0082a0000d8400069551140c10354000d86403001c4400c03071240c4a462642c9141c0714150544041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 409643624 1250 409642374 409642379
    0x414010e03070b06060a1106161e140d06030b0a1a0603012d050405070e10090506070803041109011d0a09082a0d0914090601080708101d040507 63
    0x1d4491141c4003005040e50100404900c41d820010080d0000362194107180b41c0344029001c01516000d02290a46d01004860248800d25640100c102402c140902500114410002c801030022070340d8186c940d034282c0010400180003851604240007c1da00704900c50081d0030401c1802c070103000554030100a000d04220280d482e400c1c14021241210b040b00c2000e4441030048600f10600103540a0504160782400008141c5984c5c40c407415000e0079407625640d144c09008018050600c0b40306004a05201d00b0360000c10507034813044210f4815660004403107907a0395942c940110003d90440d44560840c00c54400825120300d00c05903540804000161140b455403801811001c0c0c40400600a01411052095a032090381d1039540000444140d030f141d4a04c240215102c6181070154003000740010010541086101c030121100d010ba180c0550b040c00711440c0920001e0302182c4068140803c1180c41c1e000a048606000003203c00342c4035805135030285003030301000242010310a84050b5991b00400000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 409644874 1250 409643624 409643651
    0xf14070308091c20030409140411060a02031204060e01061e140a0b0c010b130207060f02070b0f0702160303080103030216030c0b09012609190209130f0209041401 71
    0x809810070282e903078480c1c2c102500e101d1a201556080d200c084d144000d10000c21940020302689400e2400050104054a0941480114045102d00044c0210340400c211b00656501104680060444442401840c0c0342e62524200600018004821652a140c00807171000000202106c03a01d410140280302240c45006110000c10850191503102e150070604000749500000500042b001c01800003e000c600707070000c04c8485504a802ca00c8d110745c00241c03201005003500c00e40b0072741141ca03a021405e019650340c92400d1020003401c201c05c11800c010006410500c200b20322103e1840740c40c40506169a80d14001c1c00004082c0030407000b500940180d544401442071801080307a070030040d2a00510f15205400f0303001da200c440c40c1c5041140500c02800965042003511041c41d0200701d06000360300d0080134035802d14000c500c80b404103007058200d00f000740c5c3d9182c0760305800140c180c800c0305600d5074615000c01c480c3c10b2507030003d42002a0308100002e0245610940b15000f90142c020722004526090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 409646124 1250 409644874 409644913
    0x110301081e060f091005010b2a0d08040c170a120305070e01030f02091f0e010203070b0604050c0702100903060c05041a0d060b0706020c120306060a0f1407030809 71
    0x3501d0a075405100020420a180d04980c0d800025400036141413032003102084042d140c09030050742c0040d1000825281051180898030140c020104c0340003010100e880744961a40e9601c000a0104018000803c1c24400b503000590002c01c00086c40e65804044601141c0c0ca4801600c02940c04030500c2c119400c440d4001c0c00398a114242c56038800d11880c0803d0010760003804c00000281031580d0900403c1842d45031803444120440300490b104803004046000204006509502c01e811500203120305400030340405071041e0460b000312404181a0382d0072001c032840740110700300a0342c0402400c0c09036060641000c0c01c1000d0300d014040c140b0a0308590803055403288104d121f132141700c214800300d030070206100901411300401001c0d80458900c4c0e030f940c42c0d80240d070490601903d141d80d0000f40886000f00030400d11000c10690520b0504500c0d288000a0380750250440003014444051007148215206048071020b022242ca405c58403109503003002058190100c50440452040340c40c00140b0111445 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 409647374 1250 409646124 409646173
    0x904150b0406180932060903090109090e0102070f140601060f050723070803040906090c0e040903021608070501030f090f03110c061b0c12060109020703110111030108 73
    0x2000d803aa8025420014000c0c5844d680982d0700d03028400030004004d010000901200506812800a4000d48583c03103082071006440b09603036a10030051440244d82110101c4211810280c0001e803020490250310b001e40b10322000240b003980d049001c0790030442619007400d2071026000841e903840e85c03503840650304c87c0004851000816001e001c80703000070380b15280f0b070f2401101c0f0810000c0c11021502006151040e540c004070301c980c10100b02482211243d1061500411030030b8814007080e100712001410380c1c0c1400100314003d60303c030080d10051500030400982080880c450800d01503607130b01d00e840d4441e0801d019243c0040c0c2031042d40b16070344941c0c2c007816210b55008100014040300325601600c01d052440c500000601405103620f010b6518840074100380080100c1e012410315190440c207061507022034089225030090250075143c0d000c0010307142d05603407035480d0069503018107050580e1704000030f81d0030740c20540c2080c8911002d09121806141290510301c2190f00e03038000c05c0c103400346010054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 409648624 1250 409647374 409647389
    0x2d0206010b0f040527070305071b061401060518010305190902011209060203040c050607030914060c0a05070806010e041e02011e080106020f0a0b06100e0904150b0406 73
    0x50201944100040203100350740b840c103624069580c40070800d10401c1d501c8028603400c600201a02d007000c22944aa4000d90a00d0204003e01d031100000d40310f0703011260035003100109003800104000855001c0000c0403072070b000030340b210b6944810080c0254803a03c0340200d18aa8000e076648294000d02809002d6030004606a01e0b101c00101d0701c0b8010803825000740c0c1000401600012170862500c0b80c02d405901444000d81d4914090510181c808207035407125000d06003c101480102e03921a850400b074036441141c50824009d55000111580034140c107a0410340650385c0c403081007003000140581101c4c04081940d01d180c1e6142d044514003c012200500020400120480c18000c410707601215548141011100700c40804c3e400c401c03000340d207a0001c002c070741e189005201c55901001700d03445842294000345030103410340d99001c0440303a0261031140103030303546000140307d01c0c0140c4900745649005040c02105142c9400d040c0703140740150009014043c80d224155506040c54041e00080e550354 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 409649874 1250 409648624 409648633
    0x3030e030c0606060f070f0b0604060509040203030a3914070503150703060b070516080606061b0f010507020d14090d03080a06090c030605040b091b0c01020f04062d02 73
    0x14181481602da01000301000d005c80204002000907003584042c52002c0d02400d51032a2030310b0040c3c00d010480e50b558000310711030380d030000c10000144d40000498031004000e00d00050980d035000d00250350740e004140744071980d8044854002c9107002c4c1000c04a01140503020076030700c08404420403600c4140034000c180e0503422030307900d01145040f00f031600380d080074a9103000030303035141e4455025415801403042201d41e6001140610f0480e046180d901001d00620300140200e81000f5001983c148507082403841d01e0aa01004001c25200a200c511103501c00c05000344090302e01081c0003510b850f80100d080780420302e0003089200d02c584510079540720b08800742c52408000c02c0c1d81c60544841c1d800034803102c0026181e001c041640d0199000e078090b1000c007030301c001c900d003410901000280c5034066000350142c011030041000c003c40d2480783e031b40c004425689035a9104842a0904d019225281015a0b21360340001d000940a52080680c055565a01c0c1228000c44482c18a101344103503007058a401a0701 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 409651124 1250 409649874 409649881
    0x709060528030209030616051b01060306020c160803040303120f1d010b0f0d0c0e040807120206040b010504140711070905090303060415080a030807092103030e030c06 73
    0x110000c150311078400003403652001c03038094101111207030301c0d41000002c3d40200e07448006050070001c0369044000c410501380d2003200550001d020b806a1450000104008604940003880a40c800405141c02c590299030f160812002195070313140500b1402e500800103640011102c2001c010b1710256035055a40c01d1455030190007460250004258040641d0382ea001c02c48040c15200d41b4505540149400100b8030080319410840d200d001d29441c0390080f09650101000245654070704025a000400c101c902500c460900d000f450241c464001c2101803500a0140071540005105110340e01c203186c0c44199a272504240002e0340e0781c1c4020b03011060040b0b030200701024041e0701c5000c0395024060031103407280e07030b26064881624001d40e68025240c00000070b03c002c0c1d081a02441d04c40030880b00340c0205c0307a0714128101c0c0d51080111809000c0010340c40106017602d206406032402031010000600d40441490492015284034007000c0340843d01d0061040c200c0c64000c415504000050805010a5135 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 409652374 1250 409651124 409651127
    0x209030d0824041404030309030305012106020a2001050603070504110a0c0201110d050903060a02131503110a1e09050f010c02060706140103030306081209040f0617011a0405070906 79
    0x10410284141d20903184e522410042c1c0103c0c440c18495802a5000701d0031010504001d012030b00d042c6c1182003c9500022408019001c0384c1420142e41d9004400603919511824211034581484200c0035600143d0994661054415000b41d070281c4012400d03a002d1560324000c000469100b049501e00c002d2048c006100c9003400752082144090060400e107071440c215000c1207040118410191010803004101c400040c201003114a0344400030719003c40c43c20405861207071070040c4a11446c040030500145e01030354103100e81c01291105080a0040d40c480f08100405022840584451052060456080744980c2c4c1b081c074024003240c8020b020442c0002c405401140c24074416042030b80c220f401002080000303451071254840440711009440420350552400805985140d80844e92561200c1c0c1c00854481c0e070030f4100c0c0e02980040301e00044d039000d52000ca0b07002d8846580302203c6808030204031505c001c4103400900c00c0000038103d91141c0f00811b01000700b21042a81d0754400540b44110500c41c05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 409653624 1250 409652374 409652431
    0x207051e01110303191a013c03020301060f0e0a050d03110f0c03070e0705160501090609050106290702040e0f0d05040f08030a02101104080109060209030d08 69
    0x4981890071910002d80c5002c031915607030040d901008600c01072600003a41600c0d83c400c070302130b01645d000b03031401620300100000c0081907203114841e40c6445030403a223060b42c000140000841010b01c0303040304c50700311f2149000d00250024031800000c00c16103000d0203055442459014040f42009100741c501508200030302c2246806d200d011018880040031000c038400042241850440030b81d0000c0500709800814541884042d900903004110400e0034013152a4100c010385042c060b0381001c3c60415149401c016024018511014054a00d072034852000d0040c103420260a0b144440c0c59102015402c1c24081d01c569a40b507130622182c0410703c603090052801c0d40160306c0d10240c41e0100c40c0c1c1108400080da00b82012581d540010460000d000c00c400f0a4141001004051000196040c040798900103500d855801c4a0071a0840d99018884480340300e40050310060000c0100030081d80780c035854068000d42c06411010300c2031203004c240b200c0d200d00c070303640e2144141c002c80403d405c00c03c10058110b00702c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 409654874 1250 409653624 409653679
    0xf0b06030a15020903010603080d2c0a1e0b04050d08070e0108010519030c090209041811011202041a031503060105030d0c0204060506070f0c0905100b1c02040303120c020705 76
    0x11b5403501d1000000c101900d000e00314038442d607a40041d02034907071041179098500707030316440d03641501420008101d0003002c1490180140c010070100b546c0803602444c101840b403003c800400b0715442c42c05000901400152034a1036180075101d0200c1500c8801081c2c0c0c1c4c40c81e01640c03d41c0001c071310500510035400c000700b0001640c2403840c000303041c01d51a503403044c100f556240c005803041540402d5007100c0c1e140900072200803400000e46030810311110348862181422060a03a0705000c8102d4075020320714443e070b044800600050039400130320000142c0da424654001e4400b040a19544010b86c00f480c030b00416500d0407200c0080c0201031041e000340c1c1c15600c05130010f0302070360700c85d5446030300013402c0c8c440c00000d0284520401030200c40c48034078900710b12484410342000314840d150804200c2c14080c0d10355035009903510fa102903078a803500d214210f00740c0d004600c2a1800c0e9400400e00008164000c18426000c0c030491006004100f01c40d441281d589a0600c2039a620004240c036650780340c0200b0302c10040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 409656124 1250 409654874 409654879
    0x30911030c2b0f030f080a0207021005360111060c0301210807240c050412050f12090102060106051801050d0e06010b450d0f0f0b06030a150209 63
    0x1011080341c3c071400c1d901e2410b118243d0100b004419205601c0780d1005400b90300640401c5d0450a149164000c1140a5224100f400034484000740507618140314401c0d44007616480d030401c109030700c411840078980305000d17002c15005c00d6010030948101d000c0443c0003403240380254044c1d415070b86810b01ca9103401c800d400ca041e80c3d00288081d60400301e4813100060000b01d00840044002c02d25010950724000c410001e801c6a0501e80302c42d08948550010444084a00d50380f0003200101d035906117141003c036100d40b2510a44900900d15034101c51540160500c003200b40c091310001e81c3e8900301950701d44030721164284824110b132403290403036009030050303ca120410722000036104042403040d4905082030704100c5110b00d020135800c500509a218442d001c602c42181306006c800040c0b011000300005a01c0c2c00c03020b0b41409034100960701e031013004410303d68110700400090541030074550400b8240c21826203001d5020783c0010000c0c1400146102103c0c0d00c00034010314141102504802500080c12095 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 409657374 1250 409656124 409656199
    0x108060105130b130b0909040b07030e031c0e0303010f1203090b0d05060a0f0e130512070f0201020c0406050102061902040b0f041517010314070504020a030911030c 72
    0xb1010b94001c2502c601402441c40803d5440d64003a18424580c40700c2d44c000090300b0f104204003000340d02c402d05000d0700b00d81c0c00782148070651510b21007500074105291903028248004103488400d6500a410524101105c0d1010041005240030340c4c1d48038802402416400320481d44200a030200760120b1050031402450000e1070140c40d014103031103981c050402c1c2148583c5441c00e00c035407440c3c03d411203801480380c0c03910082c0c4d1918040b080c070750019004003540031100c4811241414080b007484206010310900e442107582d4110303440c0c00d405400401130113a0052256180e001460701b0188101d40c10313514160000d10040d91a441c5200030004503604504401e602030000180c0780c24490040c080f5003440b4090381c0e0301c8a09148003640004240c804a0040142e4141d40001c04045558440d0549801040b104480044100d041c1d00d0095564003603a0014030020701c0c0c105213a03060703100b8030b401072241d60402100d82d66502090f64032a0142c0400f84d04c4811164134212121408041c101d00c002e0001024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 409658624 1250 409657374 409657387
    0x2101140609062d0d0303050f1f0501050c011b020a03031401030b011401120c12150b030718030804060806030606010908030906090315091c0807021507031404061a010e0303090108060105 81
    0x10018004d50340100d004c070361240244107a846a0f010055800313800c0da0040001242240000142c1e1100d51041905205000601d429010000e40140f801c000681410002e01502e290009680d0018a54146c00207842c0000703c1d842007440405230740c100c0e80c10411b20b11250342018008400302c002448072905000600340301a01c1c1d41510f01038107a034100301d5200c0002c902c641008010035141c9404512107201c000400501c40c0f407440b1025203400880f5850408800c01803813038100c1e17200030250000341090b04085000a40d07940d0201c100c0c0c3c03160a0a8003a914540c80e82e0005440260180c0201d400c0e0350024812014981000310141454103401021100f40090b05c410316003d0352000d881100403030704140d540903e4020105c41d0060004150314049001e40782c000b000a4807501c0301d54030b84181d004203802140196110fa0010900070044d0b96980c0d540d4141460018010a20b4521407103600340310300007010543d8001c24940d0010000039018510780307005c920044034003180043c1a54140102840403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 409659874 1250 409658624 409658629
    0x3020601090b04020c010507081e0609160903050f160e090a02090c0d09060c201c03060806090f07080a0f02120a150605011b0f0b062101140609062d 65
    0x2c40c3e008050644032004a400d0002b400c014411100811000410121042c090681c88071580942e200000400000d15041d52040803140c80346a0b82c00500300703202d0006004004500400e0501d020034071902c0600e8517950710035002e0042d0310216409003540d00418030040c0903050901005600143e52111035282c035280d54039540460303820300001d5440c039994050000a842c0c01c000013066000740e10900f044d43c2542002195542d0802c2040c40c0403140700d00c108034040d1b50094101c040541114070503120385242c004001759032000f00500e218039510540000264034000414030386842500501da4408801498090043d000780c102d05180251060071a6500410040c504841c42da4100d0f00b400300d1300b90b00e041e0004000b05400090300d140101700c400c40800140d600100e5004441e40b1021074081641d0b1440010140321400302e58118610020902828200c0d040d407000280c0e055500841d00240c8410007440134031030003281e045400101e005014101251310840c100150402500400c40b04c1301014003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 409661124 1250 409659874 409659881
    0x1606060902161a0105060a0f020a1709090c0a020703032d11100c1d010903050f0f100905070b0c010209041806180b070e01020a0209041b1203020601090b04020c01 71
    0x1507002c103007002c0c41d903404000082241c00454410307101d00282a50402c40010342c140b10700111182800980c1403107946c16030090010301001508500d80012041d807060b4450802d50111800030321500d0080300051801068900382c50105410760b0040c20303a5829580d0136198900c1100503048440c0c0025000d10664401e2102149a1342082d503482c2030f810216020a4600030b40516413183d028201452943d26503802094115a00384902c22130b128200c0410050711000c03a10740000d0000d0143c00c01a200c010000034000c6030034000342e0200c030440c07090142e01d04100e5804d400000d010780c02c819010002c0004d03860150080440a42c00145003074000d0000500321440c10b0480d1541048660144061200f18421070000c441b911442e00d140305600e0f0703126074680c04014298000c1c041050580038441e44208101200503034013a005c6800c40c103150030300c140e030001c118a00c4180f01ca52810042038501c1108000707201f0035419001408140d007013041d1031018100044505400c00d5080c4110100d45e0000d00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 409662374 1250 409661124 409661137
    0x209101e05210c1e090d06110d050705090f03070302060a181e050f0603070801030b19090f050613050a0b0c0d020a09081b03070b03060d08071202060f0403051606060902 74
    0x7141075a42e072040d49003001c100c01d071500d03013050480310a0000074001e4684084189103150f00640000d03005045000d030911901070420b41043c0145000d08221070141c1103c0100b03079a210840c4c511901c0c103c00f1003010780d10100c03030000940003001400b148a9180c050542c6035030114100c94a01360307041c0c0300e01d00710304c805841e8516101e034601855420040d609210680c10020001a03d1407491481c080038064000342c2d0602c0010200100301c400182c0d01e81100ca42403000343c0c0014418803140b091400e09481c1c44964203410f8401d8010900407882200c041840710250540c008040c00b607030740142c1c40e480070103803000f002007072003071420041030400c1140c0d84000c00c0040160307254030f03e01741d041003000c5161045000d01130782c45403071012268125940000340a0111414201c100d5640c4c1e9500011800700400c0d0360004101110206e011410082405402e5195120603401c940096880800c048102c000603100640481c004100c800c40014170400c20301d543c03d0241602160359561818034400301d0344a070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 409663624 1250 409662374 409662391
    0xf0503030103030f030522020109050a0b0d0506040c0813030c0b07020d03200d020705010209040e0307050f0102090a03030e0d0c06031e02070b060d03170a0209101e0521 74
    0x4014001c00d50400213140086241d490b04000624103144801883c0c016609403200c0441054a080210381c46580308a01500019140800c0d00350b81d410b80035401e4010007464443c803800d250010303420b402d02e84544865010b40d652000c905480380a4281580018041c00f035041143c400c1c100004100b564042c240107449a60040054140302100101154029120002641030b10880c40020f500e16509030341f40100300c4c2500598941c410f1405600a126900416800074100050781a0480010020303102c807500440c2900e0000905007905800c0303104107160340d0362080c8011020310100384100c00d00308182c5d1006c0d00d408441d05298403401b42050182d440440004d4a07100310141d4135159003004010368000d00c01c01c0d0300300a807a581b403821011009242600070040350248005041c8501c1a03840b103120300c1074188059042c081c501e170b800707940414400c5000c1c2c00240c103e282a03034880d81c410075003440c20b182c5030b1500710a02d840885255101d0f10074203140200d9001c41d03900340b9006c51a40d07401610103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 409664874 1250 409663624 409663627
    0x32a1703130918032006070c02030c0901050f060a110106061e0305011d04030c020414060a0602070e01030b090a0c030807023102031509131a040b0604110c0f0c090a0c140a030204030f0503 82
    0x7a88101072412f0110803e40e0b00420521004000981300c0e000d10701618030003110303056194003801c48204d4030304c0c500010008103582003000019040d070700011b0511000c81c21646015040080ca4010303001e44170284228030b081c0359003102100d200151002d510742c0041c0300345401c08111039039400040c1030360f28003089101d03645c9103003080c0516850244040801405140054089286003510004080c0310520019203110f40c41c0c80001c8900030305101041d003045c2c0c40708010010030b03140d007003840441c1c1204100301c0c09021105880540d003002c00d21400240c10310102030103e8140b00004080107500058185045012811a070f1003299480d140341034070420150a0000c00c402007420001411610740c440070f008520110b05100100b0803104860754041c1d41601e020075605e18400004505101d910410840c0b40200400140000e20100e4128410042110124040d4039450041c9040324480400750000c11a80c1608040c401211005040e0a04080c10f005080503070fa80c88081517043d4520080f5440d400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 409666124 1250 409664874 409664897
    0x20612010e0a0605010c020d0201020c1903060506061602011d130e0c0607151109120c150c0a02090c070b090a0302060907032a170313091803200607 65
    0x1d50341e40b11120000c140f03c0039240c41c0000e0000100c501c00a400b0307030004142142564020080b00544d0840038041c6003200300c000501c250410481c1c0800c852840c1008041131031841e00c5010b47d80c41c0c912422408042800039401034400044c14110030001d402c1c65094103615555603041480c01d00c07801c08001c144401e041451034242103400f00c0c1305200d82410700030b100205d0200b50b00071191141e143e00c00900200c2c0080028247d01138089074650001c002034010350000d001181c0d0895031141134450244c0c0c1c40700814461041d000b617554011540d400200100054581a06160f40001c0700028061914541c2d1703c400d07100f82030403500c900f81c60344413000381820550304105880c2d2001855000d071450500b150341d900c810100c43c5040000b07080c2c030175401802020390160402d0003049510301c100e2800002d142d0300c070b0300c0e508401d840c82d030b00c940d000300f002500b03c145026581613801c84448070010100e043e5025289410020b82c0c41001009500042410660411081c0c1c0180704c40c1d191020002c0c1d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 409667374 1250 409666124 409666139
    0x140313020312040b090910030b130b0702121806090315010f0603050105060702090c0d0f0606020f0109050312070c05030301092a09090c110a0c051005280c02061201 72
    0x428025005020b9208200401c0303034005000c1558a085000c8511000f141c407088406008840141c001030a409000000d1042e168400d0044200303035442901d0a542d10ba50340312041c0e03211740350211030340d007082000c1000036401c4244040d02100000c0c000d110030709041d000c8021070300c1d054a451802001d2040760740140072100c21400c0c074100600051400303000560600000c5a070b00c3c090420000c0c06070484601240001003411306031602c442c803200040000d00119124140038240c02e01c1400058020310310300b20f0103c3c40601801441d543c00000441c90484942d60346030000d11300030000c000f0807200c24954800a0f00a100441c0240440000482d405c1c1e5200707030141e846c3d80c444040d0101041d02c0401550f000e5005104a03040ba00d0312100040d51a550340e40c01d44807119000d6425041e801070015000800403002c109006079003080d61001004130075160151601d1107441101000c0c10410700b019410800c00c80c00c44c422419042c50038101c4641135030b022a2540d00314813080d14250303107039000500c1481c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 409668624 1250 409667374 409667383
    0x90a2607080a080702220906061503090302150c0408030a0305060a061e140405040609020408100509070b070c240e030303130803103302010b0a0608071403130203 71
    0x204004405030011006030355910f5494490100002e0090003014017a8400f80380b00906203107015124402803003510a0381ca0107070004e00950141d040c81103003240a446025119200707500840f41d06400400d15040c10603c1454810b1005000702d544190400020400d03100601c040c144140c0caa0300c000c111070038200c0412038042520f8000e0401c01c0011180760307a90725900880c0007c583e004d81001e054a8082502640741c82c452604415005400c0020001e030b0700e52194020003c803080901501c81c001800c40d000000c0d105e007512110010ba0004600b4080010440010003003c0c0c40f580031903154950f2440001030f0450340700c500d10540101a44400d08054002101520105c001c4025515600c2c040e10071034114061488007621a8102000107100c0340c207000c00c980041d0490510828a0216040d29882407611024589882018624103100c1d4240140100d04407000020b014003e070500b0180c0441c2d00c644005d14050820060307010041c507044280008602690035044031071616080c0d40141443d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 409669874 1250 409668624 409668629
    0x603190507080c03160e090106090c0e18060d0b0a02090301090b090c090f0c07020f03010906021e070803010605070501020712091a040807120f1a06040506060307080705090a2607 78
    0x20307000304149885e0314141864282c00d980c0882c0c1d401e41d140e1110b00047e0b00621a030b4010b07690301c2d4644071005804541280b40b0b0214410111022450400e1001040181c58001c0c3e4016420445000350140090200d80003a98450007044005081400007000030742506d043c64400d44030307540e800007030003040c0c4800c3c00320341104102500e00711241c0c200003903030490100b0014104070300240e0100c0c99a0840d0340710848a116090000d00901c048915801e01a009501c001c0070900200d086030b00080d0840c002da420b0b1030700b182e04045080d0940e8a480000c0d56190b110040884595500304822030000701103684068202c0c220b656051119030410308009810f19100d001c0c409110b20a1108006802c0009000c10a42d001c007540112544001d2030000c848018403070004010030075000440c2c1c011240646000c0c41020700700c40a100c0c1e911801c0600c1603500c003e880000011720210300041c41d9500400040c141110040c0805885507903070750070344110140b604628000c0209507180c6905103282041840301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 409671124 1250 409669874 409669879
    0xb19020102070b070f05040e01170706090b0913090203010e100b0102070828080c0102070606060f020613050309120307021008010803041502010f0203070e040f0c050f030603190507080c 81
    0x10b4000b0035124040700801c01403064041200200c00421428801c1d02907500030104440d00060958407a8401d6001070310784111207919100d010b20020f055842080b004040302d411458031031808412006020348448200c064903126520b0740c84190042c1c900344141c070144040340d00034050807100d007100794080d01c000507030b8241190f0040c0c1050042440100341d400808121020b14401c3c0b040c4860880350200c02d50b013014115000200340440c0d100419001041c2192050104000d55a00c0703c6042c0d8400000701c1c2e20070010303800b840005041d010340c40517264420340205d0440341404959000903104a0007000340032000d4201065850440c2440c61002242100074102102207605000b64580e59000c6c500c65211401400800d401d00c25000390700060702c030005402e00b59540e140c4188041d1072101040042c40c00b80c4e141901d06010580c2602c40d1401c240c505035a0185800344000e400c10301d680014019542c14090501c16481c0d04028600c101900343c8500040c100803803405030500e0601031444090750 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 409672374 1250 409671124 409671127
    0x3020a08061902031005042013060f031b21020f1209010902030a02060a110a03080115032d1503030806030706020a0809010c0614010806160203040506121e010b19020102 74
    0x44079a01c4035007840c00c0d0f50081d940098030014940c9a292383d00d02020340300203140030010b6051109000354500d60145c6130152111203090705051011421503168400c1008011544150500150303c2400c040d0201400f081c610f03050780480c00d030024200c0e481010507264501e0b000481c08a441c0e86101c1e1141d1043c10840200654a22500401e84a8100b050000e00c6105d0020b04010658002c0c41114001c0c2c10750000c0b40d194640c1840c010f40848400e01540241c568403101519059120703000343c031003506441000e0007003600b400d098541d124056003034561000d42c45da410400c203500c03030104e0031008601a583d94800da0038103030285418035030b4a410407001c42d0010386030301000c101e0f150101c0b0140a030030703e85140c0c8011242007210047c2804035000e120002000f000242503d0000384090080c16116803065180c940c81405990b60300c1140300f02c90b007040091040800d08500c0c4c40300154071000a232804401c0d01c0404c01000030400c0245c211005140f40401c00050481c2050300400c03070a01d0500085 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 409673624 1250 409672374 409672381
    0xc070902090604060e011103120118090c03150e01021603030b0901080d080c120703050a0e0f0601030821040515011a030f09030c0102070b151804080a050403020a0806190203 76
    0x1d62511444c0036641c140002140c00c601c0d2640b01e480c09401415020b07085e82d0300c45071107840d0b241c4410390038816807081243c802402c482100861280e10141940510249952451740e500c100d5007001d40c04c04480003958a222496212074207000400b1010401c4c4004003000a4620f000307402c5031840d4042d28002d08a4900500c01d1880011300c144005459050032001980d8424030403400b440f07007200791230300040140c0c241f0010300e4141c0c00960140c0590b240500001c6c1d2031155903599401d40529098065000c040104042908100104641d4a0140340442501c01b409040032200600395000c031090f0380500b0301480c101b13030441361150243c004c00301900c0300003102c102e004000d804003404440348422401c000c142c4600c020021030701491000002903403074a2460510944001d030449101d03001e8500119004c40d54944640301d489080d019184144568031107845101c8076811010204040c00010000440943d40b81e580311401007014400401c407518005003000d000c40c02c2401809812030051061 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 409674874 1250 409673624 409673629
    0x32d0c03030c0d110d0b3a0609020907080103060c0e150c0106180b0a0b0c060403110c0306010e070f030501030809040b22060305190803040b04020d170c07090209 71
    0xc0300e401100921046441d0540c0070b42880040c985101c1d40e1306a91000601c0c220000410341100e01d00d00400c96104000c002400e0a0010408149400195211000c02c1c5e8446030990f020040003218003505000440621560100384200c100f5940c0c480411050001001084607a00035420b00c0703a01413420040c0b032000100415042c6500080000242e207001c0743d02c000041095000d44d00030310320f008031140c0b83c0089181c1e0038024081d500010307010705400c440226542e0300c100f0803115000084c1c0014034803030352592011541580e000c903214100340203018040545070350400c8094042c1016001e5030300e19050500b40680392100883c03200007414281401040072450203010340381702c04410f0b10040303040c060310310001e254030100201307a050780070801c00f01d1900c0750011703030190055034802c00449e400d01560f103454641510074564018240c49007000000d0000b1840d00c40720350894400b0b0440c200881459a4081c110412480d001046900100b0f80c440400401c0060308000d1850b03030300441c80d0131f926802 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 409676124 1250 409674874 409674877
    0x1103070603050603100917031801050a0f0f0e1e0709050c0a082404020307050d020403081b160909020a0b0d05060406050111030414220b030123060f12032d0c03 70
    0xb0080700c41f03000400040c05d03203075480c0da80b004400001c0c0001c00c8103141091440000704440012006d04d1450010300b0901d2a00318880c3c02d1040072180001c0540c0300301071080307848a590700d110048040c081d4660000f0303042e002d07006042c0200030202640c0d468004032400242204801071581d08040c6108a9500102c0c100381010510500196005a41c036500c11200f903403a0706c284801e8144561000400105110b1058040c0039080ea20b428490600c0b10b0450f0701070341c3e80f03403209542d440c40c01103880308000c0e00b0210b41c001e0a542d84054103000b1003aa45420b618007580040d03502d8455113407038204200d403a15142c03044070003904013401d01c0302070001e025011a0743c034091801050751196030f0490201480d0703140e030003400004c0c180841d0a0000d1802c41c40000140250380d0006000e5820100001c10950040c0c20400d10081e42c480c404500340d03100410448007804011a00b0340000c23130341c202d80c1c0c040c1c0c2d403e0009040f4018500d210340032240800700b4401c4010b081108403070340c5481c00c2c403008800400110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 409677374 1250 409676124 409676153
    0x1903142d04020102031317010e120d020d15060c020f0105030c07080d0e16060801050103060b0a050306041d0d080c0937090b03010b041a010c11030706030506031009 72
    0x8503100c5469490784010307440c0d4400c090b03130b81000100841c5c0018001c1c105034102d400303904100009200703808091403500d507911120380304510890001e20050a0070030056000d03007808042740e0f00100d541070170041000c2c2c0600382608140001285011603030154140070040c1210028203103850707031861134000c0c0404440d00421030020030070f010004141c105003100c0e4003d100213500413030907200c0c0b45e08005020310050400c1d200f840c2c0803665820000800d58048e105140c1221018001c140c6400541101140c035948024199030f8000d9440407041a541002e080440301007003010000c0c85818500780307018100300002448480202c00402c200880f58a80740000b5215140c0030610401d4501049051300000c4a651400907002c06941c02c0000c0861b0141c02411b042d81003a8006c0048040100074002919069844d00c60300407048804001d003540f041041b00d070503a002d0320004d50b4407000c1071b0000c0d0410000b0350111000a80380e40c1441018a4140980d5000c210040d2040100c0d07292640d40301190107030344 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 409678624 1250 409677374 409677451
    0x150708070c050f03030c210403090e04031106150415050a05120307050102030f040606060f081506040308070b04020907050403050c010c060e0609010515030304030503040509060402190314 82
    0x10700070501045820480748480314101d01c16a6101d20344003540840f1608851800022111410300d480c09071802d90813150b009940543c2c50381d000504000f1100b0200f070300a0000c0f8104105001d46001100c0c0500c0894000d028500d11002a13030300810401c070a40d1300503d07200400f8980c2420400c01ca9864120103801c0b1034080e40c4940c054001c1c2e5881d00c0c110700442c03e001e01594000010003000e02c0d40210f486102e6840b4140410104d6111b620444101036907000301c00c08242d211001c11100d40d1211030b44001258018076542c0741a071070f541c0e04103007604102d42c11030310103009806000452500a205941c40310380380c90320504048c55900c4107a03882c10707601d280905009088a2020034070040303800c41420000140d0480e416801e00d540c0c0c1030300801302260f85502441d1036002c0d11803185008000c880407250040019410309080004010264001034885503101ea820000c0240c20039403c00510001c8401d40c60025a803a001600b500c1000d10080c80f104004040c007003180403103031940c403000b070420440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 409679874 1250 409678624 409678637
    0x70f150621120201020f04030303021911030d1d0f030331060b040216050c010305070f02070905060a15080f070915081f090e1203060109050d0f0b010605090315070807 73
    0xc1c04061340240301b12001c28a51140014002c02416056002490300c1990100c0300c0c4818000c2c640704642054001c1d055103a03c0d0801c100045e1040301603000601020011414880130030303042507009140c42024800b88004e0340012003009000b50004102c48482118031000410001900ca50651b4240c20340100910070340d5105109615601c55a05480c0c2c0a03034072071411a503001c6a41802940e9100ca808064000b070309060016010b41d00c0740701074600a00441d00201612802c0c49044c1000d04030082045804c620741000c0000d80300354208408489040640703c40300c1e50700313258009141480008041d14140183c0d0802003200301d0681d080100e03100160701d481d900d542c030f4a0b4001d102c01220900f0448141028640106c0e02280030340c0590310700d981020403203002c9070141081420901007201d80341e0104826000822403030502d5010002c203d272003031441e9051100d5035070303550b4041070080e0040ca00141010401590030700701080b1a803034000000540c40701520380701000400031003004101c030041060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 409681124 1250 409679874 409679903
    0x30403080a020d1515092102030111130312050c1018051501150305042d0501060e1915090b13060b030402040516020a1106070f150621 59
    0x40d541680d211080c06101408080b8800c500f00f60650154003e400d0141d14044500503140d004042800072030358000036514408625940038030910640c0301f0241d0309952030340180c2007400300c008000d08100494160181c4014110309100c4241200304065000344141080324554400001031782c00f084d034202d000d0104140c03040c140c4c00400d444040200818a1042595640010b043e0300c2d0402c1c165543e0001c40345032a4810102102038070310030f980c00340074080c1d0f00c4c99842c092007040840c01d0641e06403403421207040d21155111821500315030320035504080b20b402800045032020300c0841900d0b1100380103010070b560a603909004580c440c8640520303035542d001061007079140d00545e81c2c4107010b0301e4400c024050340c3d07513042c0d0b40a50088404034444d45c540000a81c180c800c0c1d48a07042800013690050207950b000b5521414001d000c41c1d5030550014041c80303084001a11281c4411310240700e020381150289d10400790074140c0e526904100501c001d0030490045019500d4600e9030310301c0d04406509001d02 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 409682374 1250 409681124 409681141
    0x32607060f0603080d0c120b0d0f050115150207060e1c0318170c0a03170f09040911040b060c0a0809040e1c110a0b010b0c010e010203090d030b0a0b03040308 69
    0x2040f540001c01440c40031607041003d038510391120001c40340c00d0702c070b0059449101c45100c04980c03804001e20761050402c02040c022030f42c02600c030940c070752098000254012610f0602280340c440c0e5884110700007404a400780200764140200f800a14140c144a106986075500088802c20941d102240c2c0f0743c0d141681f041414842d0f991800e9401180e4040d0303450607280c2280042c0b0b2100544031450314445d031034004250f410080103860882c1d4001c005590002103c44200c0419170040840c002d2000d81441522036070340c1d9a220340f5000a1003100a41d29820900060005071803080050794030070881030004c94660304002c10180a40b603032108a4a1341d9a000c81d002a009011000c541c2c0c0a91207202138618112401504a01018100d0340310722005240d908c0b5140d0756000c1025006101100c0c800c0100701800200c0068103d43c07141d54004600e2200e07508040d03089800031140c1242d9644540c01e8030f036030281c1500c41e0f02003200082d10251031050800f82c0400781e61002401c000c0030400c2c102d00040441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 409683624 1250 409682374 409682381
    0x70f0f060902060d0209010206010b0a0f081914040302010f1b030921080402032a0402030405030918150d11060c0f12041d090d0e03030706020d0501032607060f 70
    0x742e500409480d1a003018000f980000e4002c0400d00d03001d0b115600000c51850380e4002903401c02d41c46a40d8040107492100c2007100d81500c09801c601c10f4102c00103130985001864015800032500742110400782c1e15040c1002425103191040e01c03030419103420605840250000c802ca00400c0761070401044078031151078550603668000526606440d1121000580190302c5840240102e000300e08556000302804c8107460240490102500e46600c0d240140086082c150061503101e0f000d135090768101000b440c085030354481c5060224441010080405c96001252024000c000c002509c0000c2090904da9800e20040402504103204403000b150726035160b9000c00180515480440503200c05a29001d03c002c1c1c41d820034040c0403101d07035090034103124100030740103e40d22809282004148901d10711800343c81c81141084580d415010030042c102c0840c015000902d08003595440000d45985181000c5a28201e082082c0258000080b13110800d18015070640d80030640018000aa03d090388400c1d4004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 409684874 1250 409683624 409683641
    0x61413020c0c0603090a0b010509130303150b070506010e18070e040609170a0e09090615030f070e010305070801020c07060509030304091d0105010f120807060b120a0c0b070f0f06 78
    0x100f0001c2005580c1c180440c98502440c441c59002201340d880300200311302c85104454100403054950340d25000b10340709810900a01c0b24100b0341800040d01d0758102d04207980310b007109540550000004012000030010311680c003441e00011452a182c500408a46602c2070b07110b03072421100900302050a0041136800b030041d01e503100c2041c41e0360031210305007078546800100d4a030010900780310700004581410745000c1e01c03440300c0002402c1543c0d285080404800b020303561861301032180105c10382c1403000c1045410003a19030a070020300c0561461801354075003100d503040001e05174014480c0000406c0009001019156103080450b1101f0001022a20390b0040350321000c0c0980c1414410700b501018103000105c5002c0070b90080c4083d030303255000202c07011030303e2103543e009106480400012454007805860340324410440865460106000100803416800305044160801520f00082021010009000f048a01c0409080c500d60751107586102c108608007400d0382c2500c280f004200304099211080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 409686124 1250 409684874 409684879
    0x90708071503200412150b060f07050109150605090c0f0313030215070e1929071a01052106160c050d091508090d0302130810020d061413020c0c 63
    0x1310381d56070f800e80d211501e06403842074800511b01b00ca400c0200c070043c00b901c03603011405803441e403078090001150030450340851415561556510400400218642e00e0480030600a110110354542444100084010041c1503031402c01c4040054004801051042e81d03408420051007006c8201d40d0700f03060b41000d41005d03014004410302e0080111403074110103240c00c4690295841c51501c00000c0c8070150321072003801b40281c024a0038800d610f03007070204e100c5025441034103852a4100b01726562142c030600c4414940140c030304040343c014000f074104058a9022101d8000d0800300300c440c0085007a03115400900010f12003143c00100340300c014054a982814503503c207040311484040b2031070003019500107005241039101424000c4c0c0d038684c400d48440340501c002034040c04c02c242c00c4203010380082d03001443c0d1004010780600c00158500052261348403e40c0324090159403010b0045201c0125105600044000200003004c14403030f84952000c0821a9a03402c2c0050b600d041d075902051811150810a56 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 409687374 1250 409686124 409686127
    0x201140c1006080a020112110d050a0e0c0306130803040602071401090c0512060109150503070b071b1206091b1d060d0314161a09070807150320 63
    0x2911400006140007840500300303010052252250b0455803138101503400071b8009100802c4039403c0800d07550204450034001509140b601200580c00c0c02030305c00c111802902265200003204181109008400c8003040407009000603150004a20302060075605001e0f0100401100040400c025681202da07003941007220860f0f0b241a001c1360394007810000c01d0440e81048441e800140d1400c02107240e055051542001d04841da090071441001041d00d80301d0052019078105002402d0748080c003c00000e0301139401c285980300a01d0921001d0854182c801040b04d604001b8108500a0a0980314080c06c1d8044c001003246519401d001c1803020b1000b0500d104030a024400055980c1c05105079000305c0300070b00d070912840d50b40c0000c012840902c05070213408a130407000c1d00b5400034120002801c0044200c207041303000e848151500505100d10f40c1c610b144008203c003d00542440401c20315000304000d400038140541015000307059080224070140c00d00d51662100c85901040500500c24182515200f5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 409688624 1250 409687374 409687387
    0x1020d0501032114090609030106030c0e180c0907030902010c12050a02010f050c03180f0a03030b240d0902040b1008040308010e09030a0e0414010902030a0f02031302040504020114 79
    0x301440e682d1543d00c83c001d458000510340400c0c0c00307000702c4000c14044040340360410358002d00b408110ba002ca0303d03440d4195641d4102200050041e03903404054501d540907c0b0203460601c850340c210600c040c2c0104215440944c51040c5903407142c50f07140c0e0081c1c1390300e80410008070910060b100340030000c800510024920400030f207a558014094105a14264001d1040340355070404182215000c0c4e952a0702e100040000a10403a403011164100003d050111203611016182003400c080305800101c00182d04c0d55a1400940381c1300222101038241c120417a880c013419459030403200d10800b40121171042d00d034025402599607a03031060300d00c5100900a0030100d085080024801002240c1c00c40c085552480080341b82130140700b24512604080340194903100700c41d20250740d25540580c400c0e42c00342d03e400054036a000483c43c102e00800d6a00e101589034280043c018060794000b115501c0d03207070700c14401c00141d01b0325240390800860f015200003806841c0c500040b1882c00e101d05a4228001001980 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 409689874 1250 409688624 409688633
    0x240307260903090f0d0c0e060a03050102030f0114100c03031802060c0c0102151509250c050705030c0f0d020a1e09060e0105060324100903020a1d0703050901020d050103 74
    0x38080301400701c448071300689a400401003032610014020741403285110091040f0102c03850000c3c0c00075002070580820a6072543c030142a80d10440d051407100343c110303004001c88040d504040041b0801200c030103440703230322081008108a08001e005020117860305000740134694480300d18003d079a005492245e550801990f501c0d92001c0c0400440c0c0144510148950021210000640100f02206444044030060340410140a1300079010001070303c0d202c201d030840c40c600038903090008106900c0b61000080305090440c01d040c00ca80c00503029401001740b0306115503480c020100d60340400c07103121078a00d095002040d00000540c2040031a95118551141c14100c640101412a02c140d08141725080d01ca45503031030301400038802c01f60030100510208a17001d07100b012a0721004010500800c40d40404000074000c69511100c81d0302080c581e031020320541c24441400030161141490510f416255000f1511000c5001041007040544c0c0b0000708621440030340403100002e038010803d000700d585a092 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 409691124 1250 409689874 409689877
    0x1c09060b1512060d0c0b03040c090c0206070f081012050c0303070327140907031b0f1b0f0f0804051801090b010e060d11040f14240307260903 62
    0x414548412003000050320f42d1030400403000015a11a40e022100c91405d4001130142d04041c1c02241d600800020101300703070005100e900d003c1e0810f035000380036078108140c024040042e8521600c003000787c04010006071400d028050b10441d0035401e00d08081a00380d082040c1042d03106503291b60b040c040003da44052503804020486403680090340d0b030002e003480014840545000d440741c0c554405c020030b0f0341841d03840c000e42c80b02d0384450341b401c002ca581282060940c01401101310403a0200707140154024045900008201c00d00c042d40b0030700c01c081401c90700c2e84040c0c0c85003010300802081c0306008120400826a0a4800602019102e41160641c80c9446030a1031802d0040400252900505000b0396200d8001e214607640c0241c101c0d803a124188458001130502d20700008003010342000b0000c1d541402c0c4010f0801041c5010b51842e80c5800030b010400d855a004000401c0b2003084203405000c0305915080f40c0d0081401e0400a4524813003080e1414151079060000300303948558010000482030100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 409692374 1250 409691124 409691137
    0x1b1b070f0806010e04020402070503090901090f0b0108010305251703040608151e031e010501060842040f090b180a11040b0a150909021c09060b15 64
    0x51001818a8907a41507569950b400d116420608100501041c05800c26600800c1746d1030141055070f103449214004548449003e074865040030790b603044031035041800c0348074000b00003c00f4608040305502d1501e465950741c18802840320402601d00749ea440b80860201c5100c0200004004141102d0340d8940090f1603401620039640400e10070800500d400700c8080c08070b40308010003020305225041c006028840324050144542d0944103502d01e10600c00742c40c81c9401a449240c500119042d030400398018444200606904084806090340c140c1800035040258840c01c51074520034059101c52403280c000c0100501c66540240c03034410b200b44201015004083c0b07841c0540249402510b034404624407088580d00010065004000341c04000390700c40c01c0300b00500700003c201140307401c6060300180200b410355001600341348824946106164000c0d0220b001000d01c140d045003420f402d00c20352411031903502030f00c8003102c0c0c2d42d0f214002040025405040c0607140039090306140080f4160091413648002d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 409693624 1250 409692374 409692389
    0xa06030c06210209010f0f110114060f01020105060102030f0a170415141e06030703080f0d0c051602090403120c1809020a022104150c0318030b1b1b07 66
    0xc01800c2e01448050080762050603041e511140c9501140800312085024007510744104400c0c2030308902e0130182406507121a00c050346507204142025401c105400b0245c01205055904100030040140e8010040d26000110700a03616510208102c08449404c0325002c420300121a07030040c80103101501c0403907c0d01070a0581c0800120580343c505035490b250480340032502501a00384442c02c0a0b90f000d90542044002d022220348039141d80d0b460b84150440a10301082200100f49032150390414020160b0081a6081c01440d016050455906000e10040040e0080b010400402d0406114826481046900c030030f0801140c02c58950081c400710f80c00314154007698150402090040103442254000c000540041508a09a0711b540c40d517a000448400e0400c2800c0c00700290101100041100080703082e551541d030302e61503240c040c101060200400114004008050000074803082e00941c1069400c400f205022104030002400e0384a140725a01d83c01d42490040303c44d07501d0000d00402580c010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 409694874 1250 409693624 409693667
    0xe0a14060912160c0803030c09090714070b0402030c03060907050f01020f0a0303051b0a03090c0b090904080d020d14073002180915040e0a08120a06030c06 68
    0x6041030550b50300d40000300000c810404002d6041ea07500c0a1000940c1c03a07205081076a03500c1e64499030030f410f6070411200d000c11a50300051402d46850b08c909e0142d80102c2508080c00000002400e05451380658400200724940316000715055540800c03010355001401800c41e195894081282031711014503104040c000c05440d600ca03103131580080358a00e090f29806005180f00c00e40c90b14210050100541079801724251000c551420200c10030003018445410b49010908004c6032504c07185010003588040c42d005428031035001d5550b964005240c1082e086641e040d155001c0c80340c032400070320901c3c4511580e1850003041d0300100840156592080200e9250901914020814180c58030071031040f400c0084014040030302c1100300ca5014055410025545542802c00c00d80400c14610040d12103400c84c010030110700c105460140a809006030700c6038040e080c40461507271030030b44c0f0f406020001c0007501801350010b0701038842e03584401c0046802401c5401016030701d0001a280c0307403003514401c800c100c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 409696124 1250 409694874 409694881
    0x406050301020421030c02060720040501140d020f1207150503070503070311040e0f0a05010f08030406030b0621040b1302090601080403091503020901020f06010f180e0a1406 76
    0x301072007560119410001188070140e8138140310302c0d4034601c102007242805414101c000240c1c4581c40a04200d52060b9102c5018001d81d9100442c01c90b480c050f40d51050341003100621403070b41803440c5011600e20503242003031150503910005107801d1380c900a0f10340200c142400c0304200003002800d02e0845409241c0c184150040c92030454652008440081c0800c10420104800038440e90041100440701004c550034542c4400414240500036100103000085040c18048160810b01c1032600510601c065006010700d002c08813500c074080d900c100c1c014180c0d80c0d14445115142d010031075034076600c091961078100d0001a43c200024205590030b440000314031001804004100941d000003903002403074200710f950303030740c0044039080e800074411810441d11090008100500c0d10316502014410b440143e101c0c091003000a141010044156240c0e500a00041104003c2580080c050b2801061a20f04809081d032000002c0c010182c0304100a10682e80b1000501011020443d0b00402800c25106e1588 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 409697374 1250 409696124 409696129
    0x1509010204031a09010902060d02030108190203100b01020a0c152003071101020109020909071d10151814150a0918090606181104121709130902040605 66
    0x180d01006011402d00a8500c240350b01031840f8a034018040400895008400d0780421016088071080354615500032006001141c020300454410000d221a8203800007010f800003980c58a244400c000607a90b107005466091348284840344d02c540c0c11904903821640e8480e9000c040c40c652020f5000001c840c0c0e0a84459801c2070303240060820f070540b0040d410001c0039180c40c0c02c400d81c202a400d0544d0760b110000d90058540d420f4662041c0c0360003014000ca946842d519081055011500a81c0507180d182005403074404007440c04140e50400d440b040200442c1c55003035600c0d00700c1c00c000140850b21260009000101c440c0506010034050b40c00e08040205d0300d01d28280c40c00f0b1094108040b500c0114103104c4080500707010b00320581441000304050103551100011551079070012011105452105e5000650724021010450030035000315150038542355081140c440b1007900100340d6002c03140a0a10065900305a496140e002014542c0e40d40c8105504802031a40090490280341090000250b92 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 409698624 1250 409697374 409697377
    0x31407081207151d06010303081303020a062007121407050a02040c030f020c100b09060117040501020f040b090114340c1d010504110904050907051215090102 69
    0x4500d07014815040050380c2e50f503111500100c80d41a142c1c44d94a00b0080c00209035411080e149450b01405011a541141001007240000404070703a02c119506101500103680014002d1000d03400201c00500a00d0720740340302482003401c504284480c2070105904051104e0140c81c01050b100c186c070745103e440381c4001c409100303010b552f50281c400c1e00071b0740049001d13003801c6c0c20003480341c2d405d031070002410072090700d80ca422a0859104803a407540b041a03042c005242900c1019400c03401110002814a00311000901c80c034185011001e90707000403800b080410200350140d6003d80281181540c60b02e880381107046207030300b04200745030028424032001141140300008032205900c0b0485200809074403a0045140d54840c4c2c0f089a0659000e22150000701301100c10384c202030050030120b034aa1001c1801103103090201a08076522842c80d1600c681c00142580c006c81e400d01c0c90607200401d107980c0f43c4061500740b049542c401038210307052080c4102a2040420b603200d1160706021000da030350310f503c50340c14201d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 409699874 1250 409698624 409698643
    0xe091b0d0206180111010e03040911090a050d1a072604080f071a0a050105120c030303070e060d06080334060905030c0a031701080a02030606040f0b060403140708 71
    0x610100300c160540c06000d40e0307031250a0f1040c1002030204c0318150030503084400c1c03245c110501d604085801e03c00c00070140100d8038803202c80101075003091f0441000800d03444192203628480d9221307070400020032000c40100d6940c803811500d08201880c100b400548280b50404820840310440c015003071200381e1440784203000d03d402c04019800d100c4508100e084135842101d003aa0747e06590340c95000c0b245003429005206681011003c111545001c0601c000c44d03d0624a901e01c88d045440c4500040e103000095a85c86011440c03c001c252807078201088c07044c03069450440a25080250110b090140003005100c891071050b00c0d481200c045804440b5160300341d003003104103c0c480e43c06840c0401e079150031148a9078045c0041d41d10300400340346001e11344400c107501140840e0203092040301e2010300c04095401041244098202c01c20b09a001a0b15524014403061250f80c1d0703505600c1d449060303075110010240c00545100d07038031038481c00c008010078020040800e46205001000c00d030b105010807410744 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 409701124 1250 409699874 409699879
    0x40804060516081c0e1b041d0106030c080120070602090d060e0106030b0c1e031008070f0302010f030b010e1509060714010506040b030d030c020c0d060c080705030c040b090a0e091b0d02 81
    0x20740403150f804200c048d20501c0f10707100343c014200d0b03001480c01500703100da03c00441c480c00290b14010701d0b1000b52801e41e410701011a5030382c0300040c0c01400100c0d1010442e0036042d44002e00507618407582d00054818103119402074400c07854918080500001540034100743d9014260144041d59104010646440b40212460459031a0511940c0c440300b00e40c0596000103032803060074159078032046124504a8254407050b5105110300c4100305658000c2e06050800140f07280500c500d100480000e464145004105da00403103c803c45008005000c000b41c0b01031302d0000b046a581e0b03494a050104c54034402482e44410b42d413824001c036405181c03610883c41d9240c400742c09051581c00c2c035082a0f00070700c1184014019801410035244040e41c1e01d10280240b03a20550000500380c40c00d4500030080200105100c090000030001e100446400c1c0003518100d034042ca90156503145a0310114259400d903600c5072030780c0300d011000d100801902046426000b018400c0d0364500141b1082082810302082a004c0d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 409702374 1250 409701124 409701163
    0x50105040b030d0518030a050d0e0411180f03070f050f030105090c09040302010f060b2d04050f01030212010b0c0d08040f06050603150f011706040804060516081c0e 72
    0x5540ca4028809002d9030121110045c00d6140d5880c042402c12032502000c454a42140600c5000240c0046001c5408402642c04100500b500788224007180316400b00a40c03000072a070311107502541c1c0c0100107240085d002e02a04c0f0320035500c104060f545200303405850310641c20800c0d01e49107410144070303443c89112101d00034407a0034031751820b212144001920540c21552034042001681204c1c0c010b2200400c1e1031640f103640e0320b011304c0100a0800301a42892200c140144001c824044214280d50680c1c00c00c0f69511010342c25040141c00901c270720003104590f0200e1384000207082c0100c0e8090600d0211510030768560341a004021501524110350040490b52088815804212127030310007644050050100d484402c0e207010b44c94520042150550440e889040060014142401e030032022035625000800450500d030780c991150740a140500400c0000200c0c8280700582900c0c18000129001814260f444c0303031440b188480b00c141881c6003c81c02d4117241000190400028807000004008003401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 409703624 1250 409702374 409702393
    0x1e06090f0a020f2106070c0215070b0c0f0c010509060a06080f07061209020d051006090b0105090d080909012301050403020915040f020a020f07060e010c0620120a050105040b03 77
    0xc0700c01000003159981c801001102c4038007004c10814580690b60b04e8440207a00d0f88284100440c6d9908003070061001603042c0003e00000e40d001c071549410003059090140c0b2000500e480384103900070201990070035800d16040c4400c00d800450100e024034410142409000c0c0c56680943e50f8240880c0c6021035580446c2c0100401403042812100c030386503164000c100e2061540010789140c48040301520b642d044100040b6040c2e540b0710a51009180ca11018415a0305200019201e40154080d03103010300040e5030b0341802c0000a000302d1f91401d4005003201150750311410703a0342c0300c41480a110754066034007000d070f0803241d030050080d1000c480d401800310805598004c030300341040d40750b1640d19410940714034540c40041e00d503001034144801d0030350042021203d0342070b4071480c000243d403024040c0b152440ca82c0000e80d034002d0556030b980d030308884c0c046071001140300384080042841403070150f543c40215554680b4110706941500a1214040070301443c1d8a8030104811501c000c07401c154990b0020001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 409704874 1250 409703624 409703629
    0x6070906030203060d0f030e010305010512030909100e0f01080d02070f09020c07050a17061501080f07090e0c0c0c040e07060c0807060e0a15020304020f01030e1e06090f0a020f 77
    0x3c40d0b0018020741228801201e40c3d9079204040065042200800d8075100390504559141c483c1e50700404086440c803003080d0703000346196100e105103c0c3c0c1a0040032120005110b40b401c80c0003480042c24000d02d144154a00f8072000050301034280101090350007844808540c0c248006003c10954040065000c102494808060000d41c40140340140d6405402d170b000070742e135036603602103801850006004200d1741c020301d4501e0b05008008003a05100e070a4108504840d0340d12a10140c9e0198004100e0707001601c07400b50a03078001c08503601142503440b0389810031403040300c11000750403d103c1c1202281c0d80403241c0703800c02c02610010394412a2560000e034081080740d1041c2d50304040d1301d01a024903880c10321581c0790b0300b00365070b5a03603085600d50748104406001c2000c48851004184031f5000214114201075001035072092150240504142c3c882428840080040c040200b070944503c0607001d078607083c07001c06611104110307040011801581d55080c0070000104c2c0f503542c2c00c1d83c010440644010803804 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 409706124 1250 409704874 409704877
    0x206180c0a0608040311100b010e030708031b03070b09031803010c0f12020906030406060f082109041b0f0e01090f030b070302040f03030c17120609041b060c0212060709060302 77
    0x45d0100060004c0300758641c0382c00c1c09902550781d46001c0101c6c0c0d05609038009082d107021204554003a5200c54810000100084259040c0c180c0b5a0260b52008180c3c5070300c0c0349580078043d170207030904440c3d505111104000000030400700750000100f4010310380050405080350207074014900400c4a2a4066810502c28038000741d0340401e02d50014180400072000c5500c64108640440d0343c10b58841060000181102c036813401082441d0003072080c0e80c400200101d2006000140f80501100450f090b6100c0c0c0d141c3e08148a07501c40700d6281a4102c0c504c00004004041c079200460102c1d200d81461030665114200c901d05a61044801203040ca1a6070354480b030652000300340c00b04141d070a11000c58200260461180110300a64030102c01c0300b010700380701c491108a5103000c856150104078600d03080e0300c508440760f40648110350344070851340c1d1401c0c0300d81055901c480c40408d0035980c1201090950b0840d811301c4d401d6000b5509000350503e00711205d030b59402c082d2013010118440d0502001418400c0c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 409707374 1250 409706124 409706131
    0xc190806030106090e0f01050c0c0706050901021f0203040605070e0d0816080c0f0f010510090231180b03060612120d140702010902010e010f0309120206180c0a0608 72
    0x740001031940ea56804d40302191034003455040381e41c2040c15007140d460702c02d0068035049102c40200f580707820444a001344c1d80b0900b61046000744600030401e0b944a0707000748071441c00d4021000b00e102c500d0211403860300083d41304850440e8014902000718840601c1814610607020300a80360401403405901d9000c0b207504000f410241d07103010361a01c0800616070f10050500030b0b07103100003021040d40302581e650a00143e00c030510016850103041100440d0084000300458405040040e030f540058020f00c4803000c18000000504e801142880e000b02509111031401c480c040d0a070614680c1c1c518481406668484031041d138941d0081c000300d0414604042e034900c0108200d4200e5511b45108211843d040d04620070703228400d641e4a0440304150128002e20780e10814620081010f00d00990018080fa8502180305040040c0020a0b6040303d00951100c095190008840300c4010300c1d00600941e607a6007151900100310f903000f4900d004800001c2c82c4665804001c100c0050b040c02c0542c00c440900008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 409708624 1250 409707374 409707379
    0x60a0905030f19022424030a0c06110102120a05330f0108061008060a090e0303011a040e010b0d020d0e010501061e0e06070303020c07060201050a050c190806 69
    0x4005000c01002c820b00101071860b007420030725242c0c001000f0081e050105880050352076000d942030200c00c0b25440c48000d07903c01c90740011140510a000583e0803c030015070b98071a05031143d103192909215a4004000440b60f42d40e45242084180480311801d0b80078650220700002115008582d680600d41c000550110303c55074a0308200e80d0b0414804010034445403043e1071154800141350702820880fa00443c2001c0c00c0c03d003042c0e1824000e02080300222210003002c1003100c2c00010481e03540d01c031072106000700240030302072010361058000e080d101c0e8022302c200c4240509a003102e4180240842c2a10200c5000d40110351071686070401c815420f601c942c0044c2c494590801812000d40e045108002c107070b4000000010f85981081e02c003401107689882103c007086640580804020f521440f41c00e2141380c10b0340c0f0280c4500e014641a00030b402400030450b5a8040c118000c1580c44e415030080b07200d88203041c01480305448101060100b44101d02294000ca10f5408101c1401c3d8026088140c2100b000f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 409709874 1250 409708624 409708627
    0x204090206070b0708010f0501030905060403080406110a1205060405040c090b06040506031920160804031a09010606050f030a02071b0909021e030a030c0501061e0302180405060a090503 81
    0x60f40e40c0c0b0040788411101007011801c5040103200803c0300d8010f442c0645801e080c10031000312a920760655580005000030708101805d00000c08100e0316800c100050315041c00398544400d0744440c040c00c182d10030006008180e1138440092100c0c07a0a0007058016030b000f1068001307150270240410301600e00000400d030414420480003a00b81c81e5032000f0751148221070710507442001c2540c00102500c0c8140302c52012100c2000c400079083c14a0320481d80d038610f1139003000d21410003e00d0103c441d80120790020b400074104040300421541e0100c02c81d0300c12482400204050364666070709071640e005100000b80110400e02c00114480300743d80c02000d0407802444500d540c4c81c0c1c000b0301c23010b0819030303a04020001a01d030f061045c11414840600030000400c039045a507904156004030380d85030251040a01003148042c05801405020760009028144080011450740c4142203003c078050f8203031104070b0080e424280880c812940d060039440c01a03a1000c013514241e15100100b4000e060540c2d000c1d01e10f0b000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 409711124 1250 409709874 409709887
    0x1c120b030a06020c15040c091512032015010b09031606030e10020403020906150f13141002150703020c0303011e050a080a061d1501030615050303070204090206 70
    0x30100422811644580c1c40581d688000c00b003142d007044542c020480300c0221550512000644450320901503420301100000d02d491101e110f0201303140d40740d00c10003100364041025410700d40c3c41a4803900503404c3d0003e400d04020421986941c1d543c2c0300d01c2480d102d5840354018448a005040200324019008003126030908210a1000d1682c40c264010b0000c04d036100d00248100406010785000e034545580210304042c5142c0101c3c6601030002c1c40705200d2400d010f1074070484d0504c141916260340c86a204140c58040104901e100041c4c00d0203010040740c81d0340d0610401d890318070a5500c510b0b100d54050f05440306600c1c0792810110000e4140d10a054003030241a10707281d010000b840c002c00041c503640303c0c0140d40c041e030480a10003d4000034040e488601c1c0034005070400241540c00075900c40070003c1c8c0404620f4207131005500c080c2c14046030b4007030b518085040c0071001d140d19050303c0c003030b60341001014440390600031401c40d40c0c03141e01e0701070300280b054402503e41030340401c02c01030000d84410324000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 409712230 1106 409711124 409711129
    0x10c02010507022a04020f0301090b0112020306060d0c0905030a06060509091204030f08092d030d0c020603060d0804120303110f12061305090c09091c120b 68
    0x101c10107204545486e8121264180315102240d1a035840f401380c040a081041112030029007103018130b43c2807901501c210f034080c040c0103114628040051000d00040c048009215040c811070f802c00203029141808880c9926101e9203000418604050800072100c43c0500411810f0b071052440030b4110f0485d9044505680d0008420300b081c1c0c2c0e0030b10308041144151419076801c0811190100246000a0b10506502030040740c3c03d00c8503090001410f651b10400401c1000207400c044555015090410085400500180160b41508100d490b2000d940d03102e54065038000c061340c0ea040342030542c9480740046e40401c0b003001510f024800b00d04488e031303801059247d860051350b52000c60842e60303a803d210940780382601414000c0b0b00c0d09006590b11248600c1e4200c0c000c11000000400c914408100c06543e060125603075144110100411a04440600d11100595036940350051095 = true := by decide +kernel

theorem cover : BRFrame.Cov 409532374 409712230 := by
  have h0 := BRFrame.cov_init 409532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 409532374 ≤ n) (h2 : n < 409712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
