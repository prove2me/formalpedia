-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3118
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:43:03.216995+00:00
-- url     : https://prove2.me/submissions/34c6c0d2-db6d-4898-a410-ecfb64b806d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 560611510 ≤ n < 560791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 560612760 1250 560611510 560611529
    0xf0b101410180b04030309081c090311060f03010902090108090c0f0f040f0e06040618030824090705071103120403080f0909010b07050d020c01080c0a02010f05090601051801060504 79
    0x48010106071007020b00e6691000c0c1d0800390016001c000c05500050f01c0c02100c80e070300100c0b4042d403d01049000d10140c601950300000c2d4803150100082503021380808071070030b80513042600e005021145503140c1d500903046007840540009941010b56802007040703a02078540310107409941c0b481d4002400b031740040300c00c1510504601c60340d030707100b40e65542c403507051038169080c00c00c2248814511031f0745541040710700340c44040c50b0041403048074000c401c0801e919039041c2d40c5c110f00d42e920950358200c2011041d60f1001354075425804003044c2c0e00ca681c40c2d90300541040d201c00303403140500d140405904d2a803144440c0070390444c031032401040c4003090a80c0c041d240d1042c00252030300d0004612960902910307500b2076001c604a0000a40e0b02407202c020b00c2c81e41c2c051019104075441c3c0070130a0360b60f044425149800621100c3c0010604017100020f000c0c002014400441c070318542c1d40c0c6450a452042e0346440e900c1d0820070042001307180441d540c2200802d400380460300c0750715140024240f80524403030454007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 560614010 1250 560612760 560612777
    0x100510030209013e01110f07030e12070f08010b03070501140d09030e0405090606090705090409020a090b10021f0911060304150e0109050705060a0c0f0b101410 70
    0x5a01603c4040d21644101c41c903441c0c603244c056641e28202c1980030480b0304550f030107290310341c600034180921000303000081c110038a1b064024014802d0307540314883c19030800020340c9803c12a03030b030354040c4005405043e00082c400c0c40d0030021407511058240e40b203400140e1418206800513280819000c040300c1007403e20603e64290002e6a5a40344560454003000500e0301100d1010140c00166101e5035003c140e9081200d03584003003a00740e9403142682d14507440680d4500040d10580f049000748500f42c0e0140001c1441496540410300030f2420b07420120a0b140c964420814074103002c0c00040307203140b5031f00c000c0441c1c0074150111032014401c5844131003d681c454209a00f80042511035a52121717028094650b01c0c43c0604120300f5822000d6103200d54030b42800c18a07121410705001e0500003540042c00b60000c00d16290400c440781d070048033214107002e084680f18000c1052240c2e44040c0703500031050756609150070701046442c9000c5030815550280315440007440c07074175a26050120310115083c074403003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 560615260 1250 560614010 560614027
    0x19020a1505040e070906020c01032c100c08091902010c14070e09010f0c0201050105060412111507030807030612060f1122050303030106050f1c091a1005100302 70
    0x1028842e0390014583c0c00d524909010816074420f40c080c3c100d4005a0941d810400c0c1e020045056075103e40104004c081c1d11452010715900040c1050030700d40f0500708a9880d08402e40581c0c0c203465481417514081003143c010090401001e02504040c401c0d2803e848001d900c60347d0000c1c2c69080741520140c501e00001e80b003044620000c003e080c0c081c011800e1045a58039000c4004c034068034002e44801e28650074104414162401402051f069401c010419030910b07040c0202140e500036000c409562158060021103001c0d02e81410b109200c001d4401200e42e161700604000d441503801a2885040511700f0310304200550340a13030307500042a03000300d002c0380341d010083ca944050100c2d10315540d484036002030b4541004011944005107502c44015411041d6610020547c0301d000900c40c0402040041001e0f60710104410b0042a074622a1207000c241c00140c60140d50440382007550486848407060407a0003680307200304c0d40541c0801c0340305030100d0705800c01011500c40000c901c45202030540205400700b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 560616510 1250 560615260 560615267
    0x1603020f0d03080c031f030c03110409020a05101707260f0403120b090a020301090b0a0518040c17070f0e1306020903100504120f050703300906050919020a15 69
    0x410b03286c0c06050f1101610744a0901302c00030412880101c50300103020324103054a01b450300512241d40c0d001070a541c0e10380d14010a02125220041d140c504210700d00806165408007a42c0041c094251940c80000681045080164042d840da00103d03c1c5440c402c10030800244051040d0b41c40355242c50030300c1e001702c04000d038800600000c2c225a0340c814601801c20804542c0c41c0c3c040d604a422000040c400116072000707208650a580c0152600a80030040703444c94000490450754020340b049419100d0301c1c0c1d4403504060041c944020003440b0b6000b03a40200041c5941020040c00741020000b43c0070319043c800308894041d410b01c00300400540d00860ba02c0410341e4180441c001c03030705420005010703c2c5000c1c500b0040782c001013048400401c00c100d04082c901032184040e11001030b810380300d050b0410842c0c40c1e611181640d00071450000040c510060003030300360714000c8020151283c04041801d0402a401c14180341c9000040002001c2d0341d500c0002507075038000040100e480364401c20154a06494046 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 560617760 1250 560616510 560616541
    0x3150108190c080d0f021903080a0209030f0714042730030f321909211110020d021b030a02060f010b07030807030e1603020f0d03080c03 60
    0xb80300f103001d00142035184640100307454450060b5642a20030b0001200800c070702d001d80050002d4005034404e0000703094210309078014680da2100908865030300260031881c038902040c0b50003e401d508100d510041c8a400c184c01550b0030340315a001214010481c0c034810440201c50f0000103040403280c1c000300e0b10072052004070b102c1c16a1100c0e902d0540714142842c0680a407050311494440340745024840d01c200c104040d00301c901300d207150115183c000050b03031282d100c441d0003400060f1b0320452641c43c24183e030384c284100d120740c501c504c1944d0b07400fa40c03042072001502186c8082c80140a0142121618074101240c142c00c14030031000700585a15000d5500002800741c10080c03400c6c02b001000c5c85040303120005c09004402c400358200c1d005983c480882c209403d40c02c3c4181050900c0030b00800300020301074104c10758405040d140004a0303d64803081240f9084200d40c004020310b12203641841035040c2081c0748002041c054030b1170416132049031b0b0000d000d40c1d801020744000071804030200c0c1051603081135a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 560619010 1250 560617760 560617769
    0xb0a050a1b050a08010b090303031b041d04120206010b0307051e070b0f01060507050307020108040204020d09081b030c0601050d05100608031c1503021311040306050603150108190c 79
    0x1440602941d2103018005611030042d8102007101070000003645c420500850720414400390155085484050329219100762000d14031030a50702c1403001280c01c0001280c07214803603821a02e8004a814941401d0320000b03c0d0300c00c2242150803020061107000072140450340c00c480c0e14600b403550741e0345140b4072210a680d0040988035900c00014000280314140e000c8900a5080003c00e10243c0d0781c07141c01b9580c1e4850b01c080180301d5002803000d040998040c0011691060000d40054034240d5804a00010dc5d4440f16040b1109103005c12400c0208000d099111145103101d0b00441c1740c4000c15440035075408051280c188958078190703003074040050500c0308040c0c2401c080d41c2070014585402d4807545a0301301880e498032140e50b440b43c1d092a00214040c9041108501030840300c1c860031502802207003805c03810360300074203a121110310a2102c201c074000c2c00114015000090b580c00c10300304060810071990b90040b814447c040050092810204a41801e0030ba0108100400000c615040401041c0b0b03901 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 560620260 1250 560619010 560619041
    0xf11031303200a09090218070e13140415050a1503150209060a020a020f090f1b1b010e010b090c190c150510150e011b1209090b0402070b0a050a 63
    0x14000b6004c00301d41c00000d850342c4200d40c4407010104207080140403040072610790700002c0c0c41b0082d402190070604002e00040c0700800c0040383d03001180c4050300300600180c5048510008403001412211098420550020142a030920001c542442807425000c001d0001030600c01000c10000034401319a812a0602c520103800b0326290310382d00387c0c041c0d21243c1014099004039825240ca0480e0301e42510600d00c0759407800800301154452480000072098110b002d002024810040102400c50107411280c000580b44004524000c003440e802c0d095982a0411701d001b852500107000c1c4581e0230b031040d199040418603480042d01200001210a80c1c1c1011010301032a0851010408580d00c503041284680e080c803080440d1103580d45500001502ea00007403070001441d0040303074030342588190956000402441c0b0501c0c1401030946400c1c1c800d4905001840106102260802101c00280613031485074004950850034169103488141d0705000003000461810f548000041c520a215485040d03a03554640 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 560621510 1250 560620260 560620279
    0x2122203030908070905041203051803040f0305100c020d0c060f02120421050301141f051902010c0c060c111614030703050a020f06070803070f1103130320 68
    0x100901808042d0168100743d01030140301041d4640b281c0a071b28091544800840904080384604800400e00548500102510300c04201c3d141c51081010308081e0a09402c42daa0341d51651510781d06e007000e013210300e0046505000000b80c805130089031040300888182890400d001035440e15800410810030000c1c422480403408400349441c03010f00c7c0b40304600c9492030054941c03285c00d454001d03094921544000400410040c402c80c142c6d00207207501ea55002d8590003990f0050340000751380102408521000410115095a9604c105181442407078940d000800c80308aa280d0000c02102c0d0342c10018140644845040c54502e110300401800b0440150540d140000040021745a40380c140c45070300140c2d214480400704625002c00d50354100c81d440001058000000d60034005800e03292138800f41d0203002442200301042d42d100040d07114802c19521a085c2003200000546070300d0440c150035000382c1c4140545d6040d00e600042050589421200c10003001d004404a08441000b65010541050201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 560622760 1250 560621510 560621513
    0x60c0a1b050a02040b01051c022b1506050a1215080a05070e0a0e0615030c120106080607050a020c1e04090c180207030203030103030c02030c0a14120d02122203 70
    0x4600c440d002407084070184070071703034003000119003600840480e08a080c45aa844190380d0901d640104149542d0440081c1c2c02e684644440000a9140780b8801c080c03516a8800400a55190406005404641012420096003030301c018400b040900410904503074810403c21540440d110100003000842d0446444428600c0c00a80f11561841741c9403080340d2210200d0f031107101602401d907040010740010040c0341e0340c0402c2181080c02c10f44229805004591188000d03844e0a8500107207124480d001155003480c0c4101e01e898440000c040717100b0041c00b404582a00d90703010540c4500418102d6080c0c240100d0000c1c0081c10348240d0611585c0035140c05580f508014500c0d5074a422120f40c400717000d040c800c0301754131802688900070000300160000c000500000303000b2240c18076028009402c8416441d4001c020400d548502d40028038075242d007104102c92403400000d01c0705861403010190040c0030400330082d5031100c514003242859103001c950f10300d503c0e030340035030305210901c0740c04402c00059580e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 560624010 1250 560622760 560622763
    0x7030f090b0d020a12060b0f2208070311150702040b0a180f0e0a0302030f0a030608070314010507020706021b12010507270e04020f0301090c0b0c0706090305060c0a1b05 74
    0x190003030002148018224140058076031140108a031440c7c44c4161501d804c601025100d13900c070074107000b902102540e01d41e0b2080c000c59200000760004800030060035040d4200140404516940603210f00110100101ca0f0104101a10142c680c103503004200d800c031840000d4030152064008a543c41070701e80020440d18001d0300039092004000c801000710110741d00f942515003140ea5406405030f8810000c500d442042c0030014813420b4442d250004082d80c030341e40d0143c102503250f8030a0712071446015108412020a12aa0b500705005000418880d8a0084065141c0c21440074028048000c000b41e001c007a100d52200d0008100c000f0000c003e00d18140700089c2812111019005a200100910b8a80c0710580c00108c03094404040410904d41d9031a402c00c19007101815805805540b19803400d0000b50080c021140501012401036403244410591a86484a81e9000f42c040002449003000402c2e00800c450b600056940e8a480c0d8458030f0354016254039519100c8034100c05948410b000078082c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 560625260 1250 560624010 560624017
    0x80724110d060b040533120403092c180a12020606180c03060a17280305030a0b03070f270509191103100212011a07030f090b0d02 57
    0x1081e8908008641c1c50395680001405580a9940c0000c030b801d0350b50b403602800d10614400d00240319454a11080390340c010f041e1942000003924140315003241070004140d0069040405001c4046031581400c0344900c1c40c00c9d04201400d001540e41640d400410900d0806801245007101c852048444900c51440c10017540301e03000c0203240050080c2c40105d05240303131a4070501c0014034070a01400712511074004290041d400036090552003183d2040000c0c03062080305e1400c0800701c0010103807106050b85880ca42120f5013211707400848411190310100040d4200041d20f0304641c4100c00050000c0862020900d01815034000c8110340d02d92400008000086004641564140d44041ca2064400c240712205a8100381e0300340b44580c010404501801002039058100c0300c4c0035080071400e0b501141e000c241001000040244002e40000c2d0444070183d805c0111401080c410306071001009850008200074091402c008007085059400000028071810a480107081e1050103290303514a90b207800e600951 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 560626510 1250 560625260 560625277
    0x904051e07030c061e1803061a04050601110a17070c0e07030c020d090e091515120a0804060c080c060f1905090c01050a0314070e12030708072411 64
    0x240c943d40220b0720504c6425411492051103070070381c4224401c0c01040e2903041e0b001e403030484071011031080007000c5115809000f0000c188924001c0040c40c0c074206001c280c80d00203050318180303d0080606a0089400034000e03034072940002d950241807040b443d030700700184915040070341120190603000c980758204944c480c5c000c1d05182c400b08501110030a0030798480c00b501411101003200007808001440400d42d845500400503015241c0e080d10480f4100e08840381525a401c0940d1940c543d6072290808042e4040ca01480c00c00030030040c40310740da07002d00601c102c2c020002000000200503040010034402d82d0003140d0302c2425601c2d04c2c501843c201a81c0030088607d100755081c0e0400c0c01145101c1403184034011400c03d00070340991441003005444540c03041a00004042d5240c101b00c2c01071001d00e00d001d00820b500d0340d80c11086020b0f103040103001c02c5014003100d40f54208001c03800014128908590790740c0d5100440301c2034210054030f42c8401411704004a2101c40c2000c61301910202c1c16802043d158 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 560627760 1250 560626510 560626523
    0x10608011d0d0905061e3603010608060112080c0f0c090105040b0109060311210a0e0304080c040b0604150c1e03200a0c271a0904051e0703 61
    0x40028102c2100c0d500020301c100340d0080002c00205803c44089040d80d5464070140c60180e1915a080c81c1c40441c40201c0711500800c08010715810800683c0d5134036002c0403a0f42140244001d5080540154a40c40107100d012440507a03850070404002c940002d0b0380c490003142c0c0130f0b1601c40103010340c0180c41e102e503d00145d01c81c4c150710b400400c45203441d216010140d041a901c0d6000703503007401019070003880b03000214400b01c1d20a0101005020044515200c090b82022098010b402c0258800c001d0300c480d01c001105503041032005100710200011fa840441c40115000f26000024038081401c5106076084030300c01c800209290040190804181700c071051203020003840100b14a103150141202d9400020700082c02c1d81040c44a00d00203041010440c0745038030548054480560361070b0555451644440c07884101c2400320f658803400401980440d1988200034410480c0b070041c0360403040c03821112144241104c1002c40d0034003104100010030f501c4000011800c0710103a00e4102d643d42014801195070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 560629010 1250 560627760 560627773
    0x24091006030507052803291302030708040f0c18090201141914040e1e0a060501050304121106010f050f03120708070303020c060c0a0f180611010608011d 67
    0x1524071500860340c240c100f0001031108181690306100d801d0390f180300c0110030580c540259006031500407d200b50210b0b0030f51143d442c2120800d0501c110b0760a05120f12207054814001c01c17140c00d0f0400301c0343e07602a6002d809038000b00f00e146001300d609000f075081022280f954541c1d0a0a0101035400010914001d8031400540c400c1824504140d03c640119403c0c03811451100c0031095015503001801600c0403400f00741003e448601f0004189801c070350101d4610b0805e8800701070b6185242c4607035000001c0c00d509120f45405c280c0040d21500c00948000e0030812074001d02c40e64140300d5103100c507613140c0345026150305583d5001d10303c02c6076881d40a20340c40744005000d200031f0391400090860040180125035800d2100c140c03a21000d603000424140d05040d001c101c0000c0c0f0800910200e07200303074400c100064464181d607800401c0c1d144606403031801d201c1d4600a40820035007400303428044420030315000d0f655029113507407140904650ba1020030703e503007031075012100b941203004c0303c082c41c5030301c3d40480380e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 560630260 1250 560629010 560629021
    0x130f05030c06100806241903080c061902281b12030f05060a1202030703080d140109020a1d0301140901050103030f08130206030604061d0604061d240910060305 70
    0x34908011191806c0610300c80190310b241d041c05007416001a600220000303030b042d96a15105025401441e0071001c6402000070044a280040c0840d0030310031080340308500b0034068685c03402c07181d140f0106080740036500b00d810501c0c05105002c90b800800740c1d809e001d20784610360324040c0c1c40c0e8400340d103884001c00d0414000b01d08800b550300c121442414003c003e00180c03440c122400c2021440b6440503a011b00903120702002141c0d80700d00420001c216404001609800030350301d1103461206800000100d03004118003a296540940c441440da4510300f1002500340000e000a8010684081c2c00354031000588204285070106610240c103c3e40262034030310020003071101c1164900f00032a801c0365040c20400f4020054102200a0341c0d008401600c002002d5440306480e241e80d4607002980402074842000308651401c0a00031800102070b02e507a400c03555407541c280d1060003480141500101500609840300c03614103401d020082e40d2020740160294100301080855000d070303e00900000c40e052501064 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 560631510 1250 560630260 560630281
    0x2060103140a110d2a050316031505090102090a180b120d030c02070b030108240709090f06150503090f0c100305060301110a090503010b0603130f05030c06100806 71
    0x1280303240d00c420081c0b0740c00000000c00c0110b102808055600701800419400c0c251a0040d85c6028107004031800d03507006161108041c070f003604110b0b9a00074070707102540070030008141c070444010001c0c003e01e0100749036941206107802406040103455000b0301c843c40002c1e03030040301d01c12a14050410070781882401a40c0d0180320200b503120140c404150300c5004011881c030311907401280c25640c41c1c41680d400940e240c0c50403500350000e03004200b05c0d802840e02800c3c041e40c8003100b05148110070508000500e403c440140820130540308241106d600c1c0c482e00080d194190740705201900800001c0b08074080d080b030008060b508100c560000901c1618003100502e6400900d580107004001d200b101140d03814581240513107005001e0300d8041d900d40150441042072075010300665a8607079034042e952071900041609503000000b00b140206410403d101a0307031448820020740c6a0000400748200034945000c918612490b00041c80343e008440501820605002500c82191a408220303915505c8444020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 560632760 1250 560631510 560631523
    0x90f06030f040b09100504030e180c0f071a0103061b03050c070f11120607030606090f0603020a0516050d03050108010b03060615090325120302030a0507021f0206010314 74
    0x20400c081c9a00c0000d030006506999440d0701107038810554030684404003545040e40c0c1d060301d0490100b60300c901a51228204038980301c0703103021500b1f00d00c26a4100500e010b5861700c01d0362441c030740041002074441c06125060012882d40c4401c024404c0c2d441d07a49090075030003400c103006180ca0f0f03a0000390406209500c640034440c018844072400620300000c991740e002918103d00310484440c4416085102c040e0764048003410080c1958019000c00e24003060000e0845885812107010301445c0d030000e00031240c56882c810151070b070070306006036901e403078000989680c000c01070346041910b801c0341c1c10020004081441105c81410340c5091096981750030807142a1841440ca03580c00d030740728800180b40c1d80f404126002c4034440c3c440c10945032030402d2010908000034032900a2560151031641071034824a50b103140020070318002911200516035070001d460780b06006405003042400718140055541e003400c131507031114005d0020501c100c0d800e403000e51146424403054489a00070b00200300c0b80880071954 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 560634010 1250 560632760 560632771
    0xe06010807090e0c0f13050102010b10020d20010903031a0301200a0219080903070e010308070230070321020a061119020a0c0b0405030705060c0a0803040c14010c081b100f02090f0603 80
    0x3c2c060480c4490801c1340d50b0fe403a004c4140070851141d0380c11314800070038810300c83d40c28049c0d80c01054003010034526a410b0340380062510f000b0b03850804440510790064000d600c848180e0074805540351a900812460072151700c0c21190f0960304016640e080080501c0100183c900c2503051341d80c135696a820301000380c00c00340b1006d4900c0c4810050b10b001881c02802407004002d081c0e0352402030070701c82421080072100b40c00c0c1058161340080341c01e200b0f10620740141116a2400c201211010360203c400945034828030310010407141e150710000050140c400e05851520302540d034000c0303c940602000035030b90500c180d42a50400203c44011895903207540485040d10720203030041800c02d260105022543c0d02c4409031846034050b040700800060589030082d4041d0340a85c1041602c1e50511002c01c509100c2c000b4070b2810301c4082c407401c0c40007134503160030742d43c1501e820003140b60880044100b42d0300340b801c1c8013803020703240f4a8400707480c06101d55680600032101c8140d442800c0d600f400d5003440200c1c4820b075803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 560635260 1250 560634010 560634013
    0x3140111071e06050a060911030408070f1103060709060e0a080c010e0301150b040515030906010905060d12021627051902030c040e06010807090e0c0f13050102010b1002 74
    0x44202050100c0d110400d103000980342000d00302c0841d00e0301c80c100c50054600d0f04003203888400c104044002030041a00b5400040f2003546181030a5a5681241c450703031034010050b0b403c1c02c0000007030004d080010002e48202405541d000d02d0800c034003c2003101d59004a46c0484d1001c1501300d15410303c5644c520544009400500608031844c00646003000380da140709525640301c0c078500000820314151000109102161281c03140d0600c01007107403200d1054103000490000303204200c01c0d40c0c0e0000d14241110501e1400056545568011070b0803040c41c0c4c503000d85105402001c1d00c03102680041c012500055180c0d80e14280e9032105407101002c81d10700804003002040200202ca21034881c3e00c50b0741c01c5071407409504020b4100c403071608140e0b0003ca4821403803903030101381002450b44100d0b80d90340c40042441c1c404a01e10301410301500c3c0c01c40034001c03900d00300b4855000070000340328101103c030030300d0610503115143e900c40040311a019400e0b0158500550070301030655114144000c450038807420f03e40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 560636510 1250 560635260 560635267
    0x7030b101706120f01020d0b030d1407060c1413090e0307021503071b0807020a050103090b04150b1305090d1419020106031202100615140309030405031603140111 71
    0xc03c0100c000d0400c43c4082c6000c1e40f103452500d284248002c046409094001160440c4078404150074504907141132010710200b1a44428148000f508507030002d82d02c00d0300007404203403803181241d1810100d1054003030039400003082e0044100c508240000c54480702010300c607000c1803503100c07500c0340642c100081d00000750700785500d1020481c4e4041e580c045441d20701500c00300e40c0001101d440454183d4280c44500c800181d28081d401c02c0c11101d8080e0a080c20148403400e400d6844142000c00280054100030b44507c0302490f054080d0030114101200a2110200d0103a8910302801040161103201c5288544920103142c00d004545001144000130049410100146210b240303400440792030f03404555a594001c80042e02105481105001d03c0d0300038407942d80e0b10400c040c1181c0130380d003044484203c041400e181181d07110b40702c00d00486c038408043d51252541061305182d801176403c030311f43c140270349421042a460701745a280112070240302d4003201940d01c49981401c0ba094000e025680b03e9081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 560637760 1250 560636510 560636521
    0x506060321070219170705030d142a010c17060d02010815041d01050a14160509030f0325023708010c09050114070b090703080307030b1017 61
    0x1400903008050015050b90b2024100c144007254248842d080b142c05c0748030300200420f007280100040f80240109400038100c0490440c009052540c9102d07464881c1c0700001034601800c0080d400350300e41580140350b1403448481c4081c08034041d0840c446101e00007402900c031034801900d254031590207071304042c00710f864600c00c84c2c00444090400030805510051451a549074035241c030b1050300080740b0a08440c407041c3d04103a80726425684058200ca4425044ca852158507020035424290006020744104001e0030031214207507054090352b011180c1c036000354050344034008000300042182c8905041d504c100141039401ca50722000300040003035040b110b0b12840000880d1034200c8000d0034000109485da464500302d0300c603440d8820640024905035141c0b0b41e40c1d24420b4002481c840a00001d08000980d1080d544c0c0712440b901034468090080c8800c074010a000040c148007610140da049818542d807841c24403c007402500e103d503040350140010441e1415154031900c010344080360304040110464070341 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 560639010 1250 560637760 560637823
    0x3010b04061409040f050a06020307080705071502092101050a0b0105030f2202060a0309110402040810050a061502150a0605011e03021324030212040f05010605040c03020705060603 79
    0x1c0c400c45d01070803c0303071515004c031308204801680b0034070408000d0303624900403000400d84500540b1b982c4c00d01000740025000507004000001e403c404002c401a220404240003490078240d610704a42e0503818125a004816019004284240c00c0784030103116034042600111540c0c44211071301000340500c0c0010810301c00c8640a40c103a407000c04175010b401000160001a0540c0c001004070f408643d03162260f108000c010105108003220071202103007494940741b2041e84400c81210b100d00001e98810010340f00d008a40d01510103440b07840710500205414010280d654680500c0403140c0c0f0041c10005500e112003405001e05440040e5200300170588043d080003090342080402006060b001c0c800c000c0c802840c10032003002410740003210320b80c50b044a0800d0b0030078001040018100b41c01041a100d000120b58880c5801940c031000e44064003100e8180701c0d0040c14260401c1e68800c1c10300c454184c0c00d681c142c003d4445240070f48165211134407840c1c109640ca401d03120a000c1c00c4040c010380c070642c200c1c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 560640260 1250 560639010 560639029
    0x30408150901020708190e04110a030e030c060108070806010b0405060906130905100905090105060d02010f1701060305060f121f020708040603020712030e0304091d0a050c03010b040614 81
    0x403070015042030030603926000d95070010700c005003a15107440c1035142661360001c681d05000300290b03002c0185040d400c2c4001040e02c2022010030506440742102070206200304101c440000404041d1201d5517115590241c5481e8148100f0a0620900c40040352040c9880125000c039007005100340e1400030f603107040c80302a402a034009007540580500004000e000c901070350303100b080098411003007107050041d020201e0b003000d001c00c6010b030b14240030020a62100c142c2d444440d47c0900f02241c0b04200c03800200d401c040b04140f00c080c20840f144c000103074940c04d9086a0300031031041b20302051507443c1d94140310818150559420721540f042c105641001200c106044402041000240c070f041c03030b580c461400c20b60040c0d0052001950000c1e5400c18083c0c01007049203900224070381840303040d03003d00d03055540c0c1c0a80c0c0030349050713166034900401c0d40c3c54141050056900f07032041a20200c0c16103080c000d456209510281d07000e07509001030b91406203884d00c00e5600366282082c02501190054051180100313 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 560641510 1250 560640260 560640271
    0x50304030e01050d061e270b2d090c0703020c040506040f111e0f0307080a06090c0215070203040f03110a0f030c031502190809010618020c010e03040815 67
    0x4020020604c01c42454090800540012188483c0c0715180052505511040d540204070020942c452101e004032504e0342284001d880c900f002c1008001c1c480001d81c0e40983d4200c0c1e4621641029120401405c54107800000c844201c070558426a40c600009081e8800c0180080068100c0186c1d04034905c1d01d0350000da040300018000042000e060b03c2890b044507058040020241d03400314040c03200800d1550a400411118003c1c142081e0511740d520070035004c081c081d001072082d1000043c18104450b84694000c2200e85010b10041101150280d161616a408032007403100010014848a0000044504507082094010b40442c65071f03e8503071200c03030810603007944402c00300e0b00080c044400402c104065409030110100d024598600350409580c0710300703100002030040c0202c25010304840c500e1024615542130800442c0d4030400c00754014111a00440d4070041c0c0d48601403c07002d41c6034080c098101c2c06000802007108075100301942da0003140308070385030307079011000800c0c0200a80c2d00458012 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 560642760 1250 560641510 560641517
    0xc09090a052d072a03111b100807030933020313110406030c0e0106030c030501180902030f01020c0f010608191202010608011e0c0f082409040501050f16050304030e01 73
    0x24044d031000c041c10300b83e20b07070001c1d00010030101c01c03440160f60601a00d00c0c0951001050504000d100e404910362540e01d2991a0520401c0300c0050f00050103600140c90850b030000c1d009081d4091055134444c06003058540740081e0304190301d001403039580c80c42201e0041403a80d450421076070301980da00ca00034440381113094109132a90070000001d038940054101416004221040540c14800010200e0b10f403011050201820000100a41820307182c0141001468290114030040540040f910340701e21005440c07007562000903001c10098000c1513500f40e880702c2034002c0c00182d03600c0040d19901c440168105071000720715032000b00040c408140384450000c1074000421440c1d070f504803d0b42102c2e030625151901005e00c91b882000c200b0b01e4826246844024281180308040100700104180001083c980e508040f02c00000591039041e5400207980800a01e00c2a0794501481e10f1030180000340c0d01410f144100101148102100f150790550044260350307014110b40e03907a01d04981ea6134150f4000c6060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 560644010 1250 560642760 560642807
    0x2090105150f0c0a021903111513080303100e0c03161803030905130c0906050a02030906041d0709060c11010903080c0d020c04090503120c09090a052d07 67
    0xe82902c901504141d9034039009004105041e0052100101000c100080b00740803000c03042c0001103801c0751080c076403101502c407408005041c0000c0c402c039116120083c0b110150681000601c2440040214410000340102206040e03a4482d10030650005803142c05c142c500510000e00c401031040e001007889585d61800003850440d80945d000c540301d01e038109500203581c25900340458184540010050103552000b044900d40041c802000d030240b5000e01010044002240e405581c401c00c10390340c0c0c0f0f003001040c031642d543d41d4003080b00c00c804101050702d0b818403000e000611b01c1070041d1500320444446031954894420b080c0c0c0c0b07080400189203404d03418810f00d260041b011651090140468482a4004200880441d0f1000c0e1518180190362442941082400c400007400401900c05825110400c07004988803041c9100300e501a10b0000c5070440a56001c0000f481c92941090380148204900c2c000030b00011807000403001c120442c480c5004045401040c0c0c0c20303100d4020310361100044103800780d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 560645260 1250 560644010 560644027
    0x605041413060b060c060615030402030c0f0a180603050d0504030201020709240e060a0807150309050c030f031206040b0607020d020a03021306090b2715030703060204061b0209010515 80
    0xe10340c100c5d941880b59035110b0300c2002107608001c0c080c0345145520203106421890a070b07002130340c2c070341210803914020404010340d0003241d20343d61105d50107000014002c2607840742d00403030346c00107000610060b10144038200803002001d000e0401c640c1602e0b0103901034601e00f802d01c03075140081c02e01900594186000d8000040c080245454124007404c40c1081e5110281014010130007180d4103600017021980003004200126542442003040482150902141802c903a050050801e80329401040e0140911014000c01a4000c07000384018540c150f400307101ea07200c01007030204590196144641201041012101510300500781c100e50b11310050180030480d4680e40411070031901c070b006442c48652141014170404e60180261503104d8000d5451b50340d01020030325015051642c4a40ca81c80131050b01c808944014641c001d41d4216580280403507003226920700e005002176003d48580d9000a1340300d1721004201140301d00c03030590345400034082280fa900701002c2004c3d40c0344040c062032440d40101716000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 560646510 1250 560645260 560645269
    0x170705060a1403073f050f011a040e070504031704061d040905012906090d030f09240807020109050d0f1209060507110a15150b0714010605041413060b 66
    0x1042020300c030b050b400c5c1d0318000386405503000c4445c00802c0701250926003000416140b021075241110315458900c4401404d0750103402940c444c58002080c994068400c028046e50000e000317108491154101c45c2601d20000c018800394061801540300003070080108400724080101d0196035040000c00c0041c540e145580c805003107c00e9a5800728400071034000d031300c500300c41420b4940206034059981a00d45008080001d40344000c030302004043c88481c10005030000c0c820030b12480604103c4c4003036600c80300154070056000e03107100b00440000350b040e030004450031701c18090755004641c41401000701b0818000103680012007000b000080141e19190001d43c80900c0c01040200e038000c81002500f4100004002c00b144c0310392000c590310758000c03900720000070400c0d10200c1090010710400243c85002400d82c1810036000da01c103180306440400c03c4000c0c4102441c43c1109441e055000b000380a60302c50500040c0da407641d41d8132401c041c8a0300090580300e0158071912400340b1070080022195487d00005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 560647760 1250 560646510 560646557
    0x142103100e0a09120c050c06070602071401050910090f030807020f12070209010e040201050f0d020906032e05030d080604020904060b0a0206010b04150e011404170705060a140307 78
    0x9403498407014140d00f0f00201125104ea0441c0d80e24028071844015180c0590320401050401d0243c00000f4088003441429070555040d00d0340464440342c440d0811680a001e0501610304a01c0703400b60401005000070380380304104440d0350000c00018a001305460070f0326011001070062055004880f02404c03d0310083c401d00c1c03030344200303031040da61280c2c050300501c00e049805801582046944d1818880982e82100035a0ba86125481c5031603a40c3c461406a10080d025262075039421820100610245014007400c0c00594101c02e560300040c1c420b801a4086004c14520880780c15030001d03205036444901c200841030780160098000751030001d04d440402c048910582c0b203050b200c00040343c180c00046c0d0621001e4010b001181c082e03414181000c10302c0040c0341c43c244800b81484600801c0d1600c0b030f4010013401200c0c00d82e00d030461741c07640d41d900c15100c1038060341c00611405014800f00840c040c6006c1d026980d1815281d0b41e0851080c07142420b030200ea5101610000c00e009807000524040150034120b0f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 560649010 1250 560647760 560647771
    0x303030f062d0f05060f0a0306030b01060c060c0c030e0f010c080a0f080108030a210f05010f050a1d130212010501030302100b060717130302030304030b0103142103100e 74
    0x14022580b00704a81c24050031640e4111240702c0c98042e01c00c01080e520f00050715150172104102a9a502c00200141e00620041d80010030241c801d40001400d15044800014510701605d41032151082103034045407480310046004000c141c151030420214100070388001c0703902406042448114060b07498041c0181c210300e10081c0003604042004407080e034020200c6005090110003141026041e40005e80039245940004582080c200c103141c00808560b00004204000314504000d2961181240181c003e054054075008509880000800c0300c080c02400c2c900110704030055040342ca41b45020032280301c800740181e0b03001c02d00d0b04003042d10075428464a4020340c481e030000c00300401c2143c1144103031030401d000c0921411060200c440400c0c51680c010b403a4451000c1d1a954401e60301d40514075580703a076000a500f500c4003141c0403041112085181c5c0c10b8034003e000c0a1f81d102103e80b1042d03500c0d80d00002c2802007441005c804001090060003468020070f940640b12510742e1540641019034400b100e5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 560650260 1250 560649010 560649059
    0x11340318030c180b010807171510030e120918091c0c02010905010f0c06110c01020f030103150b03101a27010e0c180406030b0c0403140601030b010303030f06 69
    0x81820f11100034400c00200b0982820004114940382402500c1c40d480764090807041451100022030340e00450061030460b180091001c040c0c20303030304130303004000b80030a0203084030034842c030803c00301c4010a10b0142c07042e07517200401042040801100d1080c078407401411000c1103200c0c02c2102920040f00c81440405651070f41d450116aa9090000410a001c2940024107000840079001a050b07400109008150340100b4003240d582c4108101362082d100b4008141c016520101e608a40003588900440c1285d01032000300c1c07041c81110740510204c403401885154161300101400494540300e410104007080c0d0204020840c2014030003007051440024079043c0b000c4e405814490b52031042c3e0a01a024060b081142c800034600034405400c40c1c49400c00c1b140002010110113401544d0b40e070030140203903a000610b4101c2d403e03c004c0e0300906e50000d001c2199900ca601840302d070040c41c00101c95040702d03006400e00b18684d285890070740080a883e2004840380b902c1d0100403c80500084c400b5052807d40003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 560651510 1250 560650260 560650289
    0x721050304050d0f0c0b040507050306010815090706020c150403060609090302010c170105150f1b3901050c01090507090c030506150306031011340318030c 68
    0x42d145082c8014000345805200221020150082d40700b9504080d40e9400011081d080e2034038240380313250208551102e5030500c5210004600901d011032a182c00080001120a254448041d40d6440388000d02440b40180d04c260510019854410380100408021061240c0703000d4480e01c40d0819140706401000b0b1158945498900b01a42481039401e29443c1d490704401c0200090800c0c00f2030345040c0b00b1507110f40c01c81102103105d06500f41c226611807080c0d06c0b4280d6282c48041c8100b04046d010600413006004e01e00c1407406035400940b002540c526448400c0c59010065105103074058400d5500c40e04008090180d44401c000912a601084c0d000b1801003140520f00f20818050721b11440012013014106420b20400d9140c4810007402388000390846900c03070342c1d00c9003c2480d221611494060050801e4581c80842c0c1d840c01c011b0900c40409100600c111402e100d0305060b00700d0781c50070203201d61026070030a0046481404001c1c1c0082c1d0300011400c41658a40381e81100489039000301c0c0310341b000c06 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 560652760 1250 560651510 560651513
    0x6181e0c09101a0a0e0d0f0b090102160c060e0603102112020a0203010b04091104051312080f07030c1b0503160602040905090609070303080a090b0f040219140103020721050304 77
    0x21841e17004008216819620403410355102e1a002c07d26100050206002c180803d0040000790144c1e491000b071070003241000812420900e4281d1503030700c50000800e17080f141c0c8220302d0a2010842e845401401c0d080c0d1780280c5000c004100c026402200c01c1c4050040c0c12944001440c5134150103080303225a030040c504140035004040c21518003440c0244203a250600c686e0000d0003c403024001d07035008a90020300d40d61078006004882e4510b13040101905100f0b00c01042c0e1542215800340240700103410084286c4e0381000c1a000c44907101c0f40750020600c43c40c6804040d81003012074841c072a00c181d050f282803003030718811110844004842250101e802080600900303086100d65544a0134000060000741001c8141c0783d104c281600018040240d4000014029070745a00032001a0b5845030f00c1a01d00d10b03040f140343c0c0c142d0784d068404903c80d502d10200040c0c0b501a04030080251703408090241141400c07540154001e521548044556215501d05d0900001c6850a69817409083e501d64503038a241c00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 560654010 1250 560652760 560652767
    0x7080d0614030706050304060f050c12070c0f0f0f06020c071403030a2102040f0f030201030b0103093201111b01060b04030204020c01090506181e0c09101a0a 69
    0xd908003034201c480c4000262100e580c00940e1800700c0b000703410510359a1b02d850420102800d041b0801d5040c44c2c0c20700d401c2c000c1514a0400501c0141c1020000e02040d458000d800c40b41e180300f41c44050454040000140c010940304604190322910130ba103483d83c42c04456880c007042e40c014820907606034002d4081001400c0030100305503843c12045001c1e515122020b10060091120120050800800c0c03240321961034a1a504646c00f03031080c18000001c82e0b580e564090323401401c1d80412800a420b00e01c0700f03c41540a400f071b09600c2544034201c11402c1c54803408007841070141c0000c006032038400d2415540c1a010078407850440a803844045655107000911b0041c1040603007041210680c9003032802c0055032800c00c15942500da04603000f51b520700d485541d05000d07103040c0c0009000d500810342481541c2c4040c0b0b034800c5402d480750b41074889141044d20040e251941d481104a0360ba0800a2028070318613204541661011644a00c0e07100140c48030030085d601c00c4100300d550381b50b01000500d103c00701d41 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 560655260 1250 560654010 560654021
    0x1c0602030a27140703060e060403170906060609030313030b010e090d020705010c0204060e070c030e0a12020f0103090b09030c1509100b0307210209060103090b130c030807080d 77
    0xd038940d00c041450030502d600008000c40b180c0142c0010303c0c43c91000b5100d42c06002c1c0000454001005000541c040a00e00703864550589045020468107010803401d580751062031803040724054064211980c0b0101401581d07440428095490f0008101d048a0035080d01c510001070b501803d0b4080e404e60401c0d58050414401070b04001803940440b0b080c2c03208690000f090000c0d00d50a107000c0e040d9400034408100503000903000038802d42401810052000c1c0d0100d81010020300076901c60081e8881c1034140030711001140207428242c0046120000541005540507202c1401898001114039140d00d9a5846120984036200280c000041144181a003005440d0940c2c200c601c8442250910510032585d848101d00c40500e80c0d51600700212481c0d50903c4243c00410401c140c4440102600d401c07800d909000074030480c80b4a2661001c55840d5200c3c1c4900c0324000d90144180010341c5984120700640e011380c0300d040310f400c0e01e107450102c0020341c521b0140030036a01c01c2024503102d0360550100019100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 560656510 1250 560655260 560655281
    0x110c1207030b01050103180314120702030d050105120a030c0f02090408190806090f1b0a020d090e13030507110604090207050606040c020c01030906060e010b0c0d080f01141c0602030a 80
    0x50030080c200409503112980c103200741c1d88c1820100c00d01011040c0c0e148003400351030500035083c03801c00100048290084010880300411440401542ea03d4808101d010a1841c4000105501c0f13040d092000078000c80d40703230850358080d00c01442d4034043caa00150044008031421200d45502044000301246240c540204190090409862500d413040100d0100310340200702441c440e05010114904000c207048048401c52485442d6654881c81040a5600e0341c1003403c110001d211340100113031909107003c41e240168828001c0895044240d201115a80c010540507035090415a0400e08a559500c00500c018001c0600158a4000b5420640e060000060000380038505080c2214485a03002c078018142d2442400d0024815003182040310041c9038035009040d00418200021512881240140190042c01800c0710b8080d2602881290300d104240c0c0d030740006050f8200180114400b254042c03400c46005080e552002c00a0f01c0002550701c0700362800d445c8681e00009001405d4030ba0f026544421 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 560657760 1250 560656510 560656517
    0xf0308070b0708090d031d0f061909120c1a240d030207031712040f0204060602070b190507060911040e010c020c0f043801030516110c1207030b010501 66
    0x9207013001080d40c031010380f0448403040541d42ca030030100c1340c0020f13100403101c108020212000300e0500e031404c943c1c2d80720645071030740e12000c2c0f80c030b881c410003129000300101607601c61105401c1340c0d98050b0558403444661800c60708800700c81035000d04196032032011449644901000603032018a9443d01505510000030b40e0b003e008510f20030801f0940000b100d0003103a0340603039401d001c2801d12070220300c0c50103030304d140810b038085800c240310900c040e14070740307442e0b0600840f01000616910301007680d40f22594802c156000f00d0a2141c403004c1000d40d8110151042d0a00f007642c41d04003c1d955000031a10510b80c01c6840ca0166400061035040c140b14180051810300000c0100d0310f5100c81c080c0d43da907082410107100e03030f60300d0004a402c0e45994201d000500d0b480c008000c8030950b40e01e210702800d444d5513110f8000452690b012000d1f0340c402c3c041c440c00bc1a10b03641080d01084109011100b4980c02a0400701c51301c250000d40c1d60a484e0400152010301480e00503186075411454000140c00e010ba21a0307041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 560659010 1250 560657760 560657777
    0x1605070201021902011b080c010506030c01090b0a03021b0f15010605040b0c0705090405030315100503040602031e0123040c170a090609061407020f0d0302130f0308070b07 75
    0x1030b40c001030701c41d86a5040d00400c1c0ca040d10300e44012604007118180284198500c1000d03030781004a240c01410b00301e42510001c1c0710917603c1a05155850700d0b820750450000e00b03d2401001307405895002445008080d20300545045000c03e0343c9001d45001ca945415560301204507440185410321112596421038480c5a0341545029802032980c0954004c0303903c0085c0004030003140c3d200400c800b80c01000c000d0245210f615040c101583c80350000c86502c42c2139540a030202c8524501032105030709007401601e07814110f44454072100002e40009010140180d1000e00c41e1041403040070000340202118070740100144808e66a03e0b14000159407804c0c0514101103072541d215402030781204c0e00040e10601007034a0f58540030601301804035498040d0031903280405180502074681c01c0840740507030000a03009280c07214030080303039140d03040c1540c404103030000a65014000e10a400400480b141107072070612042d11844140b80c2038480d81d1044034400400507804081052141ca82c1d0303842001c50912025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 560660260 1250 560659010 560659013
    0x1314031203061c0501060605070c0e090d030c0e032d070506160f0605011e0e090607050904110c0d030c2c04180c170a081801051c05160507 61
    0x424040074001e02c1c03042440d10f103900c1d42e011400303002c0258150450002e10480d40d8410015281d54800c9000341c41c1130841920100d1200420030215000d596550010141c00701c46e00f801328002c0004914032000c010302001d204016580401c0040c900c2c03107004844045140001010200090b4060301000c1c40c3d40280b0b4040009503030300c2c0c0545044804000d00103812110700e18010407004d001b81801804181390000229080c10411403966001010324a011005512070a181c09407510072038003d034403603101c000000d000501c02e4020f00f2603403401a0002c10441c000d80148070558200400c04080d80d449002140303412a032600860401502d58182950311811828508055814805070583d001c44810114405c940f21580610b6401e06545c40c500320340145454250510a41032082e910701c52610388200300000c0d0b000c1644221290710403c21468010410151501a180640014103201080c81514941c403840307041744003054142d03000008c05150880c4616120200a00c0a80800409200317100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 560661510 1250 560660260 560660293
    0x60a060303020a1205130b071e0b06041e020705010e06070806030d111203090f0607030606090519080a030c0c0e0f0a020315120a05150402150c030f131403 68
    0x11030650007002400000b980d0002c103580130b11410704110007071b41c142c0400195203503181010704007242c820720110422200501c10f4800740c501824020b4131122401022485901e00380e40310300d00c0440201011141190410441c0c030403a00003180586669448500a6090f1207043c4802640071140c0d04001441d401d000002ca80d6a101d540064400e01c030342141e00c0c41441c402000001c1c508070081d000950741c0d240800c0840e845205161091480e44a4400401d01060090040c601034511941d181107410745030004000000e03805804c0b80000c198000c101080554046c0000412980039071902c1d01050f80a241c01d5a10403c15070214440903044010300280a0301e1054850300260480000340e100d85132500d03400b05400461210950010015142824800e004690885038500070025200040140140c0704c02400c411034000f50712408810031407000c8000716000d0f0410000b0241102d06242c400641d2104941c424005194890440c2004002e0314540007019400b42c081580a081400002c48a50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 560662760 1250 560661510 560661523
    0x804060c030203090a06050901030e0c2209020d0f020a0e0c03040209180d210e0709050405030d0609140a2915071407050a1503021312030908060a06030302 68
    0x500410500c0100402454420000d039a070700c40c1c0040070103e031a991000090b01c10340c0810f0030399010134280102000030000116840150040c06004810721404202c440c0384403020060440351096070350071030480943c403252101c51045211301404034800c2c0309401040311205d001d030b0045078490040810130665000950030340c0d13001039041c3c2d520003164542c141043d6102c040c41345c000f8028400c503003042c1c1c8002c0d407040300b640c00c103060320329100007400c0c5804090b07080c2c0d0190703072550443d5400f04400b0803032603440e41c0c0080d034494003540a80303041000d03503462041552420f500881d000c0761100c081240c485881d00303a26410035402d20040182e2031204001451079180c01c002d6103801412001520344036103c041c0d5260000310582a65641d41c419450001d05d20a60700c80700100c1c40c80f40000c0801d003820b08001d01402d9515000d50203e00da4a0710600320042c0d03016035582505052810710006000009000702c0000521945501c03c04500b0109545e280c000028440a6078034200300042020035008503d9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 560664010 1250 560662760 560662769
    0x14010f17030f031509041a180601031502040e1303020105060109030f11030705060a08040c08070b0f0c03040b0d140a20031f06020d0206060102010c0e09130213020d05060d0804 77
    0x2c41d1030f0366414495441d40000420a1030b0415842d204020030003022103403c0e00c0f03030f200d4000b4415141e110341160034060341030103003804060386c031810050000c11407070241c5492004d6680703000740c606030700c4480c4144080030944510300074104c1030340c10f135080540a0045990124003860309448092568448001105416402030240c050344914011152030a01c14030340a0280509160b648050412005003144412501655140303036128002c550460080f4410381205c040340401410300d075140d01d802400b03500c110080112031208000004241280b4000340034080f00000c1c00180c4091114500003000380c0050002c040c00b40741c09184119603000b00302000c04046221105504c0b9540c491311100f40044007121444044005a000101650300040328040000d255082d144c1ca52203000040e03003a0344020f14000301207000304440c1c54042c101400082d90100d10032110780c0703080007940c01207004031621890100005400080c2d1502c040c90502555400c1a020740740700101c2407654580d10080d0107103006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 560665260 1250 560664010 560664037
    0x1050a03020a1211090a080106080d12090b01030b09011a01050406111603050f0f0a030c12021504120f090e0109090c08060a0c0e0f180901090614010f1703 68
    0x5610782d1140c419019070003075400c0e10104009007020115006030076006020400d11524040c80e02040054041c0200412519414000c1071b002203041c2c0103803203081c031451a03018880e84d030340c443d400412400e0810600950044016242904020846500355100444100d2100d81c00a58a03031a45e44d100e0112030485030b552620890f800d904242c000d0424a4aa480c0d490320080e43d0f50100900c20b010504c19520500c5204450302c010134483d00986440740407001402040685804030b0200740c9150286181251620543c0c40c0e00c0f14000054442000541e405e80c0c10003c120041c503d0705030041542d1200320128204010070916100031308003050014085c110560344c4550300c80342080200d400e1b42001d03100c44000d41d070344c1d4542110744400a010321122440040c000b021000b195040c581c0f001100b0300d1025042c0d03280d01c59041c0100c241207002401280f00d540d41c810045010407828411079100e405a0710040e00c1310752504980f41034080480c0c201582c14510491132800580e4000200c0704039940446 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 560666510 1250 560665260 560665267
    0x8100303081504020d0204050901120305070f03050c030a021005070924020a0c03030e180411040b01020f01020a08011d07050406080603070302090108010903110d050417101107050f030901050a0302 86
    0x1840318a460303000c148560f0304280049a101c080e41c50580103072060355000d03507030310840742c0e43c0da00e100581e11400d07a0040c0102d9010000a400303d40703038405554400d40a810564a06000d03820a285194440c00e03400c40140c100301521601c02c5510b000f115040600d42c80c1c2a026079040003040012031140b40002240340c00049d800001c0b4074000c0c4444040e00e50801a2640701c2584c90402800d071201110f90316110709e10b41c1001600b0b00b100300e0104c1d40034a03009002c6002201003101030000901c86614214158481c860707000d40b941d002400100162142581d8400065140000320f00c10314007418204e510154414042000d1184d200c0180c80869840f0300c7d0001140e00c80303402007810300e521034201940103900e04002180c20f2505400c010041407103943c408000d10480041140c99015004c1c01000144040008026819140000300d102101c80380503504140c0c1198407503000c070307030f08160745044100c00420003d091240500044400c1030700c84000d189480d09240c0001c0a900c907000100c0181980030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 560667760 1250 560666510 560666521
    0x141c05070512040611070504110a0807090515070b010b12163c030b030d0f09050303030a1b02010b09010302090c070501152903271902100810030308 65
    0x2c104140d402000801c120b03558a4898100a0402c4121011100c40d445410000286400c140c0b040b4161440c0d0841c0050502040140490702482c000d40390030102b1103808030100b02e80e030359403400540c10021500701c3c40e42d80c1018a02141010300580c46580382c1c00f418000e44500044083c40c0a51244400b00340144503010380328180c90205290821070b429413401143c0480010250031545160340e0ba4001850030354001240481c2500e0b40d0784a055055042034013031209080c0109038101629002d070510140c0d1030703262800b107859034004030303010040d80b503c0d4100e00081d8600050f00c0c14044540384000d221070300e00307040414100101844024060006100002d251045000513151b1440c0c1c80002441034050348611000030181600500d00c0020309040306007003e4110300326282c08281a064494159642d0480c4805c070191704041c61511448030040c10300109500b4070001c550004d040907561041c6111340180013a0600a007840c0702817050480034840001203014041e422a42e0601d010041039454 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 560669010 1250 560667760 560667763
    0x6080f0c1311071505010e250509240306090105180402010c060b090a0b1507050c0415050d05070618060e120127150209060319020f04030f141c050705 66
    0x403520041c000040090003400000d07200e8001504803034007e192000039032030b1802000f0441c164284103582c2e600c18250403500b800e0089004d00f030b840c00d00900402011390040c454050340c188114900380714143c000104441e070300c2c086940c0f60144c04151f4201d038a102001464000402e40500043d05100411000c2e40c104071545d0801c43e040100a0407102d128245a45a01c0152a0f0702e849030b40301d00d0030550072403401c004070070544600307940200c0105032606000d070600005140158030a02d004030726000100e81a1a000d100c030f0082c5d03110320002c050781481c1240c01031001200c4802490300300c0d908e420420602d87d10941c0e910809504950403190b030700e0700f00707603560041c44d603040c084400101c030061090416009810158072240035084c900c111000344c1c1903110882c4549001c0561114061020039001901c0c0c45140c0034070710030150300618149032603600c1c4035940c2059004640e00c8010010010400151221024079544090b008000000a000c1d0240b01b45d0011000313c020020301044d2001031000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 560670260 1250 560669010 560669017
    0x12030402031e0d080a02030c07170403080a27060c20041e0b060702030d050a18090203060f0f09011e120602090111060702030409020a2106080f0c1311 66
    0xb282d00030581240c1150000c079484010240d10000070a84031400580c540c510750080301d10980d15403224503e002000c1c0d07205038009070380c5036182003810707000d100100c002094040245020b044030b4460811032a50002d0480942d481c480300298280200740c020080350b900010103480c1d10350b1000c114860aa40034000f901d00000d40b020881c3d01c02e0a08151241d5614445111010040000c000340121600b03070042c4041841001c2c0003d41561242d00c0305840320744124080d0244140c1032a1400c113900301074400d100b044101c0c0e0000c102092740081030000380d1814102d54200841f00391040c0c030102c81d800002480e44281441080b034002115014044a001d40006610140002410114182ca0941460002500004101e5000c5030700a003141485910001b85107214480342c1d4021440d0505202c13021019401c00d408c1502400400b5243c0318804406032802203081c9107078100083c54601e080400385c07414281016030741c41c60b0024402e180d000e84807001440302200740424045030120324032007180520f20 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 560671510 1250 560670260 560670283
    0x9030f1504060222030c140402040b0f1b060f160c170904020c0601030606091d1c090504050906090d1701050d26041a03150906041e0609060f081203040203 68
    0x5503032071000300800030a9140300065907005440f081d4102107010234003040344114041e00d01c07502d01c14008030980742c01041c0248000d80096504035180d51019085900e050b074103441c80c40c0c40c000034a0070000484490041050642807900c1c007101042c00a4443c3c2800c45401e42e141d1492000c0010b220206454a404641c9007100c8203086030007540e901e04050005028600078200700c5400c01360034020480b05a04d44401504025018082030070941740300c130000050750780e40380062101c0002e00044640c1e882c442d484c0f04d0241a4050120303071400c8980039050080008009046c820180300c110b17200d90550481c6410740f0001d44d20095181c000781803a4911600c2440e40072104a411200c1110740344001d0040c100715211166401a020f29800305505079010440e104106d07000c145010102e80d02e072001a03950001c2c0701620021f000b544903c40b200718034031403664101225172100010801101c840c8a070400400030161440340e4030b801c25540315201e400b440310701036850002202007001c3d95401e10a0f03200c0f89 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 560672760 1250 560671510 560671567
    0x7030f0521060f031f051e010608060a090228050c0a0206090a1a130501260411090a15050909030306091012150c0903080f070309150509030f15040602 66
    0x30042031110204601c4003050300c5c102c446c240400302e58030030900e0201a039007a00034035000c00702e03a00340a0104c0341c091004000c9548a500780f800040c82501e0b603c0244801e42140d20000300c0340d582c1d5100b04182c2c921160304082044000c200301024034401040031058198100c2c0c54a036a0840e40c0c000a1000080f90041101000181907440310b0300b1510009114074506520500303907182c1d5410054440c08498600e10b0486d401d04081c0c1d61886001c0c0071401d0b4064803c09030103105400040c045401c0040c121003c56070a5510028a8901000c0342120741c02401c080381c0203070141c5070481100d030700c0c0c2c040a002c0c580200d10140200b00c0c0203690403040e40152a0a403d4003420f01c401d42001030010100d4ad035018070251134640d018400b5441400000c1c260707600048074a1a02900200d807000507406030809608028440d400032500c021907507001090380055a81c0d1589820015040609200b20404440180e0348000001081c1c5000007101d55486600f014006880d0040e00c0010003640301c290603494500d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 560674010 1250 560672760 560672773
    0x306060901120f0b13021905090301090c151b150203090f060408070b01090507020706140c031c050c1603120e2d0304030c03020d020d0f050307030f0521060f03 70
    0x11010503400301c0005a130407079114a07012002200c0c00d00320710540d4080a0000e03254164079072443d00070030092141c1c40d405000040c1e5402c1f240c03662440c815207130b0040c40080c1072034005ca00150707034894114006845040d60040c00141e81d5a00c110900c41407001040c4407607004030008080c1c5805012400400c0d9201050314424030f860f19010300c496000a0080302d021135010008669808248100e5205407296001041c203141021403e03216100c18115030500054200b188942d41d4000b0f00150648100d0440c4040e064001a0f400e581074450040054180c3c0b90144901611403151580819003a5010b0412008541c0072804e154003804d503103110903c0314811602c40070001c03280d0f505c80303012190303686c0302c5000203c02030000c0c1500e80c4a00e101c0034140280c10f2209001502d809640b80b00c1562000b44042c2d5124450750f9214001313051288151029000810140c1c140740e001640c50718080c2e181d00e411807030003c04080481c0e42d803004000e042488480c500000d48181c8403629003c822441c020211841d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 560675260 1250 560674010 560674031
    0x1302040e120306090a02030105010e1302040906090603020f0102060c0f03040c03020409030c140f032a0a1506091116060f020310030303180c38030a050f0903030606090112 75
    0x1440d842030f20301c0f502407400b610005400500d60302c20740741a070700c3c16916511480c9884040011081c012030f2402c150030740c00c0000150f40e05113803003801c008011141c004154a032071801000b040b484400c0090341907422000400400411040c1112038241901d0f0456489445a08182c2c100e040c0341c0e00020740080c6450707103110905070012a81c0040b0b80c0b1800305651a49440c4030b8250f15503c2240d8042c1f031070340c07090140600c90103c08160010404c600002141d506041e4210306190043c8028290765511000c119154505010b0184001620450000703204981881c008018540310301d56180e0600008a00c2d9202001056004010f100070403500035912410021000b0b8584141e521049002c240b030190703501d042ca45188094003c46811120501400d442e040400c05504441440f51a11445c280700c00368280e805003450402c1225518181134480ca007130342440c003c841002d001c1040b8241410300304014a02d0004c202c940c840d02c241c4049840b8030038140180c1e19080402e6003540c51505155507080c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 560676510 1250 560675260 560675293
    0xa0f06030b0f0a060311010e030309040c0519030b0303030a090f0209010905150d210216090c0801080a050a06022a0f151311010903020d060c0207090c081302040e 71
    0x90044a00c9100c0b1201c0d80c80d05048030046035200d110003030500c600c0c031100c0c5002c1d6009582e011084040a410f583c5412040d03000030b01110b64a0704503401013100071500c20040324908440040042040c18100306809421001903502d000c0181f6005030123440d4070b520401c10505425504075940d0240c14811071f543c6444509025110131204034604114440d02c2c80300c907103001f280102c20960041211050b00c0c8118501ca01c1d84429681307010b0542c0b058100c0c3c940e8944154108200078010f0180014141d503148400410103101079004002a07413116203007001081c2e000c200d8401c0c10758032000c016514114040c04a442082d98803985209940907a40030f240c0c1800800c0d80c404161560095521441c54604644000700c0309072004c000803031034050400005901c08181a100c00814100080041d91342d41c0050f48082100c141259016180d40401588603010444100a0039001802b48601021202d00501e0201c0c010106454809048080b8056440d81d45c002c0c00180d000c0b50030340302d94403049120304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 560677760 1250 560676510 560676533
    0xa030603110307030f141c02010209010201060f0e180708071211060f030f0403050409090609050111191d0d08191806030507030f0c03091505040b0106080a0f0603 71
    0x955400c0c4054002601d0780c68042026800c3e00d074030810a648414454841e010703440004154000c0314440c000400081800071200c001040d0701c80d03400960f0343c0700024002402e646d40b0358800703125042005010b002c3c20032031880721544124210003100c0090015448149800700760380c8441401c0c080c0000100d104846082000e42c01c0e0700800300d0301c080c0511301003071202c0751080320807044241c441440410600484400751540150003440c00c1802d05888614400c22100720715022541c25644017071590400000b030058401030701b41c080c6104e0070300c1021500032149091400c0d150040107003140365104810b011020780d00b0000d0000d008040c44105510f030560341540a80d141441d50411005402c940500c1081440341500c22501900ca0b02c9150000a6020b020003500e440306142e140c0f500700140d03509622030044858669030340400c0d00d040e01d0514405004102201200c4903007403808110200f12041c0803a0b044415a250264143d96400701c1d4100412145400c0c00040c0d003080000006d024941411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 560679010 1250 560677760 560677763
    0xc020d0206091506100c02060d020d0c02070b0f0904271b140603090a0212030d0b06160b060a09050f01090606020307020901180b13050a1116020f0d05030a030603 71
    0x1c81e04161104904240d403028880306043c900c0310084001043d600f0000556480318009040050310244560b0002c2c07060b030004054071003490f40c0418410f10403e003601a03611290300b2030001d0000541405c28145c51307449032007a91548103400180700c01c22074503141e1111801219120140514950b041c10f107400b0358454480071b850130300d038000140e1100b4503240040402c0307440107070400a0613200034080c044a03070001440038480340182208100561207002001103040084e4011f155641b05030980030080341c140c0221240101304c24000c13568180c89518440d0f61941c0c00100040e0542e5540001614140d415000720f1000c03401d00c03040c451000c40804c0741c541030302c04d054003d2064030b84405040341e803401001e9019601802d464010085032400c1403428502d104040f0002c01d0034480007012804403801d80c0c074045a16541d8001b040b6445100e88039480d0f20124100c5071901d4040190800e08000118076400307031090b02006503111603a6940d41880b0403c0741d100c000c2c0c946400e080c00700940100704a200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 560680260 1250 560679010 560679013
    0xa060608150103150f020d0902090702010204030c03020d050304150c02090c072a09020c03030906070c0807030e03010920030c010f200309060309030d0f02031006030f0f0c020d02 78
    0xc280110003150190141c00020880809a0b00c0d5403514030595000b4007204e0129581e80d480148403d000b40018942c1400600010441c0c034160b05c10301c0607200d4010450421640b042c4400d000142c05511085c1c101c030780481e401504981c41c1d0a00e40d05512481e030050382a410720300b50181038150010002c101640c02101c03400303129926141103401d2445a0f0340018200d5624001c400340716051040141c0344603008401240107561100419000c0380d01ca04444800d03648040208840c801042040c00e0340240d80d45000000a0b955035100c0401d801100d50080500107100390300155501d00758003503110325400c40300d02c0008401a00d000140c1000042c1075a00a010310304540d4460f50107424083c10007402c2d66503a014042c000d00d1070031001031520140345d0319408100241c9240f551100d01950058048030091070b501c61405203007008a03401480085a60343c0144100308842c252070043d0800c0b1101360801240a0b4189405a0000e2054842d007450051600e0149101d81e0340c005a1104e16840030340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 560681510 1250 560680260 560680271
    0x6040e15060304080910031d07080601080c031f020708071103010507020d02250f0f050a1a030a09020d020a06080714090a06140c01060b03040c140102060c030c09030307050a06 77
    0x5000c1180720481d80030380003884c100321580c00ea09141000344181c0d40107250000e135500b80280030304c0d440104041e11b038015034054030703091010260a00c85035004095440013014204050004a91a0900c1105402b07403186410b0721310000401c583c0441e000c072680440040d654446d980703400c0d15280c9441d042da6001358a40000541114000208400350f0b02e020740040c1403144046003003100c0c8254107142280b0b060301841d40001c03241035054110000d40780340d03496001003504080c2402140b170416440385440d645083d0644541151600c1200d1300a1503840d80842c20850340d002050030029060710081d00084450000182154016031160103080c10759100d1041440900f4051124007500e0f00446d400708281508004c4a4040d0210065001c0071003049401c02c2c0001c0131a40c2180d100d5482507100080000070041081131036145a400b03006043c2e00d50480b680403800007580c1b20360042c017034980d1b440008042f4401a090310103403095041c000f800c50780d0b10720351480c00544541c4070504c101e51082c00d01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 560682760 1250 560681510 560681551
    0x711060703080c0a0e03030304120201140f0f1005130b0a1403100207171303030e01030614090a1508031b0c100c08160b0708090102030c04140f06040e 66
    0x18021603400e03641565441c0216150f101186903554042144201800007448071100a07442c107001442c4628000c20190702403400707850019083d02c5460001d0340c10340021001700894141c190900541125814107413800550f03402c4000d144108141e0005607124480c176502c8403200b815074000001000f000d8440f01c211940d40c06440c00869070348080a941600400704102c2c0d000000e501403c00c05010b55115540d0000c21034040d0066440303060564504800c01070280185a004441c200591f0801e180820410b07103015030b8108400c80903000355100e01910800704034182c1294005100861765900182e062590750b8a00711b50f60b0b4025090081e12417034103465481c45100100388000880400740080518803604074085407500c024100460b070b0b0b8001400341c488881c0440f4038155840e881100c25582d24109050b01038880c2c00001c2904405078010020460200202c1d01a1403c072402c0383d101d00e01c0b5403618800180c0036885440855006200031a00107000c02c201034600f80500c950482264049200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 560684010 1250 560682760 560682769
    0x24140901200c0a0602030405010b0a15020c030313230a0f060e0406030b070c0c090513020108060910050f04140906040c09180b090102070b0403020105180f0604030c081e0711 76
    0x2d410060640e0341081e504080411081e4008660061061000080100e00300c0001805e5400360341000301100c0c903007410300c8070b030f00e404100c0410204d40032402581002d8000e640b210000c18a8040c400b000c0c901c1c0a00000461192013041440c200d00030036800c501522018001c0402c02c0700e228250020f1281d40c0d42c0d00b02400c00c0d115460a40740c002c5500c0145548016083d200440c15040486101c0b1102030300141c2c0414611605005074100c80c0c986030b01c0b043c030303000040c440100a054540f0400341441404140140601040110741d02610f07070540c04412180000e005060705040c1d034045441481c2082000301010030218070951045410b0050140c9420908048a400c1d200b000c240c0c00b4500a0480803030030103000c80d54818070079000540303407400c140e54449080a0503038045015179100c1c02072103d0300c0020094a030b05000000c00820b41150203210340c994402018002034244400e840920f8140204e0004807146030740c02c042000000c0c1e05003210300500d81d20504040d00c03010032802034100300780350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 560685260 1250 560684010 560684017
    0xa0b060309030a2708010501150302180f01030f0e06070f02030408070b13171609021e03090f0703051606050c06240a14030d08042414090120 62
    0x8107402541081c000100c1512548001075180d0b19002c00e08120b070380c034101a0162200640f0191001254a502d840c2c0c62200103403090400c04141030045c0940304000100c2814040081000c848048c0a00d0305200140c00400303101900840146c00d00742a4008118001a100d0050540c0e55034150740c00b10256007203032039001340c1c0a50b0343c8035004420300704203244203e8081d014254000000b084101d039120350303540794400000041c04203030b008103401c0741c10002d114200d070009181c1d4010661400c60300032010049140458800300307403e0401300119243c2d000400c1070a00507050302c0210780303815859007413142d602d010142809207594250480811032500c5402917074900454140145255100d10030180903c283d91031012480700c005940701c5103180e4034101510b00629015061108440c540b41c180760030540380d4001ca90500000b4000d200c002217a0042d2940c600043d102111900d55043e0040d4010b8411030300c0300b0040b510348038140442d8007010350040400d107082d422082000c3c072248000008500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 560686510 1250 560685260 560685271
    0xf02090f03061e1e04052d0309061e030907090f2d09051e0106050d110618060d020309010e0d0f0f02070503010e0a170702130b010203210a0b0603 64
    0xf03c644025486449a091506810800100521032110036404100140f480100c80c01c0e903e66215901031801003080020750039400c0782c5003203107101d00e08a542c0c18a80da8800c40040500400f4006210380c222a8440c00c8a01707041010b0103110f0380ca0070014031032130381c5161a0162507420782c905810303000c1c1d55000d881029105040f8103100e0043c050300742d15048a4a2254604039501c80e03c40c03034014000356090100b5400d003c44e0400c504c0840400d04241400c4407040c0e00702d14020520010100040f8042c220200410f03603080b200c10740c0d545400011481c1344460b140d00705030040b10200e4410030b40d02594014600c038000c804020410503840311009959820b11240c0600416600d03031071480b109100c1c0c205503d06a2107401294529607403040841d00b120791040119100f600040143d00801c602d0410f94003801d4030b00b030750f444e04194591b00002c03100d5583c00d29a00400743d0b5240300790940e90007030065503081c1d03190243c00200d000d080700079000c002c1c000326103101c48145480c090004626143e02541c1c0140c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 560687760 1250 560686510 560686531
    0x308010918020d0201110607030c02070807030b0c030402011b060533060f040515090301110a020c0105180d0f050f0111030c0c071502070e01050609060901030b0a090f02090f0306 78
    0x1034185400348030fa0f01d442c0440c16410000c40518903060240e0400130140100165500020080441c0c00700a0402c00f02c3e42004056811000d0100702081c0d103040e24640120281e11090354170303100c61005a40b044912111010800c40c512802c5040c020307142d01071031196041e8030b01007c0c02040c1d41240240c91003040414203403e00c00c000d82e45007a08151001d01410050264a10315150311040025a801084025400315400015a1452500b801e0241036041810098032a00340942610040e40f101c3d100c0c1c400c98108100440c1d85c0f426490a80c040745c240c000c024062000046850400c4002c00b0784405007030307826100307450801825038030500c1440d50068021780324a0850312900800322007136008c040748c9096849004000300c0d140349002020031107420240c0080541e5441d200301c1c400b41c010141e00030b034403980e0188880c81240c0c4992044030a0300c0e009103400514212440000b455404d03003a009080c180d440e00041c041c50500c6640200301545040364044800d0b142801007603580c00e000c80e03604020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 560689010 1250 560687760 560687801
    0x1a1801050a091803180801090506040210030c08130206071e12080c090d0501020403120203070c050312040302061b07080d080f060109171207030e120d21061505040303080109 76
    0x1003441840d0345c4017080341c0018052420b070f0703a4004190a507040c0007402d66081d00100140400c6142400d104a031b085102e040902803126401000703052004024030400111700030b00760450071551880708071808581e200c2c00b8070f420042c0149550034101002002143c00411074004080018007600300c0910070404843c940345040f10390000c2c40109541104100d58070740d000c2c130020002846103810b00b800989a94011516417031541001c0099004580c40700d40241c0004400040c80a400011a03041d603030107481003a070b201c2010700546040307080c0043c1010940252003011800010104a002000d1042d5a500b000c6481b084c0c00905203e00070b852460214200d07020400c9036210603000710f044001520183e035030107004110004c0c50340c0c0c40403c0071400101e040600303505910700b42c0d129040c00c0c20b40000415400c40385003070207400d20b07440c6034507440440c9070161041d00665641e040a00030300b1106103560102c8522000241c0141c1190108070049a0102c0001c51120b90f81e104111076942c40c0e0f9190441d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 560690260 1250 560689010 560689013
    0xd0c0b01140a0806010303170a15090c0507060c0915080112030e0d0f08040e0108010203060d140a0c080303070801050904031d13020c0604051e030d1a1801050a0918 72
    0x1c003180c44a60305a00596520350016096006001075802180207490710030b01e000310a46114503002d002040c20103803500e001c2d520070004039203145260130b55403110000a4003840380c1901396403d009194004210600b081002c408213540045d0050071201c1003c000c8020110215040c0c817800800d02540c01c821907500c200c0d101103481504890801c441c040e198191124032a21160001e055803581514004000a0108070215100e07003c1401895120002c5046040640000721100c00104010707000c0e100c0c1c00c40303070b81e00711001b41b00b50b12185a12071480c103e001d031f40e0510642c0ba40c2080b15030314003081d00280005294208880711922507070b850b940741c814400994400740c41e031036148229103070014400b285180d030000c2c89100500346545d00100409640c5000e140c511314028020401075501303680880403207421030000055032081c41804002240e105024641c41c002204510f69155102800052039290f074654400c1d0a41a0340003034034058001c585a0103000f058521406070b00c0e85000c008001c100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 560691510 1250 560690260 560690279
    0xa03021507270303021c0c030809011e051005010206040c06111612060f0209130f0b15070b09060f07052209020a030f0e0a260a0c050d0c0b01 62
    0x2580701e201418010015881d40c8100c410400c040400210305001841060042c56010490501c0c203140e07106a8001c8140c4841d4024103501030280c0081c24000380c04003240203000d007900412020312105c50701d45010b602d80c2c20107001406084d103800011915448000c5030310751012035100d11a90300400740300d040a1502d41c0488002c051a140c00c21607000e10345000d100c0302c181803001c00041000d40c003520100245420aa000c940303030501c440b42c41510410031050544c8404408000700b00f0401c0000805024080c180c1000d440c10b074120550017204103c1050001100c0e00181003c02c1c058054448030b5a50044155aa5582030300d80c600e00c4411080007910262207240107144050781d0300c900c0320080d1800c0c08040c0d403100c1140c220b40c1009401149680150350f052254150301180c030501031004860703100715661542c42c880c0c405030040e110b60003000820320b8842d1040208401c484580340d0b44d04003841000340101308804044600c3d000c4c640c0b80c80b900502c03e1950139100c1d500004208226403824950740e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 560692760 1250 560691510 560691553
    0xf040c050d030c03122901022103040b0f07120e01140108010e0d03050621150906060901090203040c051e3312041209050907030606020607020a0302 65
    0x229004164440042101c0c1c0300c44001c00d840501c603840e03d104035411458050100c146960a08141c24900105001d440c0ca9070404400750340d109841940c16410500300403810305101e0a903040c1c40c103d03a5821405491200313402948103034010710000b00c0079218072084510307900040d51124002400060000d950840c42d40c4212001144040000740c83c42d140108461361400990103080240d40d108001d043c284010300c0032020450541ca401c22aa03e031403800100c00a00d01001342c0c200c604010102804600b00700b0000d415030200c0d55007607889143c8450010b55401d0300b1682710303008000b0080001001c40990082c1e81c0990303070000e9412485402d0009214040d024059914000c084004c0c03075000c3c0d40c40e03c1d0004501040e6803803d0b0440710440680807542d13004559108925004204103007248170b0484400286c016038412880c000d45500410200c07920805070704102e82c42020300082c03089041e05a800300b000c480e055000e0340c60320340e505802683c071203400e240c0227000b682060550140300507010615 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 560694010 1250 560692760 560692763
    0x10207121104020d1b02011d070b031008070f0519030f0b0603120705030d0b150409110405060414040507031503020d02042705150705160303110c03040f09020403030203030f04 77
    0x142010104c00d411029545594002c3c1a01903844900c6030031943e082c0500003130740030050980c444000d8a4208540e44000a1040c00140d0b0408000700740f2f04940c00403101c000b031900c00c08482c1c109031a1050354051031100e12440f4801e949501000c80c1019112680344101c0360002d20b258003801c50f41d202c454040d0402080d46900d40101c0030705000c040c15050240c409140514002d607115070b000240e06040791070103c0f0751445103001e610f40400c9020042c003210191292a4004901d0104500c85c2c1496401590082030780030901250214101c062148000d0f107041d42201c0034056903c6600058044401c013982c00d440ca0a8141003d00160510403600c41860780302038000114003501080344540e400c00c0e01f08181c3c9800780c0c101280300f0700c07108002101c1d40d8141c003403e2800d03504160502500314411091600308042c90082c10030b040c140254407810300780c180b503502d803562041c07102411500d9a006006182d00c80301300b01e001049001e290701c20348094036410380055144d40c958040031200a14010b20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 560695260 1250 560694010 560694019
    0x131202010e0d11070b03090c010f1403040609200f10020309091305120c071208070b0c0c07140a0603051305010c021005060d0b01170a060509060601030b0102071211 72
    0x1400c9100801c01c00114200c40441e0361802c03140e000785444142824030399804052400014424080718080101b01c02c00040024200000c0703854482e4800d4541034075946c02e5401c108404000c000900c82947c200c00081407041121405c0005520004200da880e62003001c0c3e008590140f04c20303841c0c2007158045041c06082d0040303c0c140031420f0002800b40e00111350700b8000000070354480d02045004c00c03403030740d00603441c802c0e8508200441c907035590b03111240c4c03188007001c0d00700364040018441903004a03a03601d40c1050603000e0b5440c00404008140d031106a64104038400c001000034402216440c0c08030280d401050200243d02d031032411006007030090301d40385140b52140b20440000d0400d11650307200c240d0503000b501c01c00c1c0bc544550000c41d40000c0690307004181c07088000d000200c803003440c1415101c241d0300b0a0350416040c0400c40c64507081c1c000003400300d441c000511658a000080f10707889024240e8090058141d520012a1180d11b5403180d0718130b01c2060380c4c1e41d4001407070440d10045003031006032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 560696510 1250 560695260 560695271
    0x60c18410301021801110318190302120a11270c0f180415150309061104081509010603050607260a0c031a0d020f130510060305090613120201 62
    0x1002900720781c40006013a001004600c0301d4481540c00564001020300103002441c2810480c5410b10780c1070480b4402d0340c0c400d0340980c11072050b017191140c40a010f9500070f002c5840d940742c0c82c115560380c0c041c65070040c2e40080210b1098005031a020401300317843c5040c84078031000885224510407103400d014003103c042101c2401000c440b000306101401745000421288100c0c0e020701c6003440100c424620014004a00030441800b403102100d1485c80482024900040c0300300d01400c1071402803945100c08a00c4840c00100007900440009001c1d4040a0400d5003a00c95103d422425003240c0e0148401815038001c82c0000e034038203000300310441e8922a030000301041215000d14100c6031020032520070702c420307548203030940c07051307905100700c01416440e0b6680140f107041c000002501c05107441002442402ea4840c44042c2e61201c1600c04203800551205101c0e505107000d65841c80c0e041400f4070000686420002407640e030000a0440c0140208012040c1103400d603180e2807404015419094250b64890 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 560697760 1250 560696510 560696639
    0x14040e181906151e140108130b1306180b0a1a010f02030f030a02031603140a090f050307060b090a180f080c150109060603111b0703060c18 61
    0xb1030082e240704003043e00340070149040903105c0909404011045041080c241c082004c01c01a140c405100d40342c0100b0181895a240706001500c61441c070001841141000c03460100000c212405050355440744812020542e240300a402c122070000140c10200391108141c409554020304100c0d949115920682c1c0c40c00c0400b80e1404019403003529410a110360010800c001611240c080b001d0f2045286000d01583c00313100d06048580c04050441c9002c155150b00d4030040088810501c008241e001c010780e0744031000c90402c100280186040395005200200004e08490750520442c10900c0703101c445610042c0c9503031940210400020000c0b90080420000a40542000c000c01d01c4810a9040c4101466041009060a981c096071005041c58208002003e80301d4018054400c08440048489580c0a480c0c900902e0300780140c1c800b5000f1441c2819030304609500249c045100d266440100c0c030013550380e40c203000c0c041f0924407140701c44812411208038914050140c5203107103000d82644c402d054150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 560699010 1250 560697760 560697779
    0x50604030e040e030a0f030b04021303050d0201050705030903030a0f0e010510060f020f070902070606120c06031a09040b040201030213060e18010506160314040e18190615 75
    0x16181503001c580030038004459460b0901032100700042d100e0145007098050140039100da20511603e40504d42c845810383c1c12526942e064512003100004901d20b190b03908e041c0344d9150034414460b0401942418000703400a80100110382c02019100025461aa5440003100c000c000c1446c00350949502e07a503c1c10000d00b030901905029070f400c1c00c1c20810762450003c01504036515150000c003950015007581c400c030580415a8400c0302c88421000d40e07203100c47e15122002f4245500803030300390350140080009110140344041e05032801501c040068554109006180c000c0011005910602000019001a090740c51107600648181005400d0a06003d41107040a4940c1c0002c1c00241d6001142d49030f45c0b8100006003000201d4100d01c4010303504040200700c4604c61303081d4000884100b07827049001c0510a04051316003420650040c2e0b01c6603110a50708030139030003d940251604842c080304885c01503011440078580110ba0750703003410080c2259104009040d4411910001c410000d4000481c413c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 560700260 1250 560699010 560699023
    0xc0a02120309040b0f01020304052116060906030b0a05040207030c020a06111911091003060f06140a0b0306040f0609020c0109050607024905040f0e100314070305 71
    0x10034006142c56008032402d2000700d5441d01e075490b2261001c2004083d560b40c0100c12030b401c0da07400b6035550600203a080c42c1075105400601134105e5500ca440711824500791602c100c0720545270640e440400c3c050340c90104a00741e03400e0f01c1d01c0b00e40c003074a0324200b00a02c0c40d05500504c6041e1007800c1c0300484c0c9515070001800311280343c1c005004600119040c0c0900d40d014000b92030740070810094015015a50703140d11604041802505000d0070801006c202c002c900940300c5002507070b100784240044850400b0030009810144602c07800c00182050303000c030314903148807804c0548404828403400c6503145001c00020b4240b42c0000c040985c0d44807170215181813140014640003c1144c00800e0007006850a1454014000c017150304540150300214a01d145011844508001003401c00075248486c01c002e2030310126402c0201600c41d240c88401640b1600903000d081181e00c201d01d92050250740d04141001044101ca11040c8d603000c1c0602400011800c0e862600005680030031543c14585030390741c9614000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 560701510 1250 560700260 560700289
    0x201306140123030c07080c0d02010b13050403020c0103150e0405030703110304080d030c031d072405090d050a0b0c07021e060307030e12070311100c0906050c0a02 71
    0x145850580e129940c1203018403401d4050701c5000b04112035440007041c1d5900001d07010704404000000c0c008140103448040d80c0900324584140e50f06a07111100c00f90003051010205402003200c04404801c079126131050f02d20882c1c1540240640ca192080110300504417030300f0300c55607420207440c00300d503402c20b80c0040ca101314450001103035585010700b009041240249004c900030380c4200828011040d010840141d050294100410550b00201040d0064403105c43e20008a0561040185929130002458070440b0081100c440c051f042c0d10030061920001001d01d500418410048a0b0b140d0400d0301000860714000c8050320180c242942d5403600702881519446d01d180c00116a60040d454400c182044000c0003003003181000c000c64000c070b945030000038584001d042e521401080c14250611017030b43c110301114812940d642d05450082e105a00100d952a0544152200e5078015291762003002109071990b02c900000d00c1c1341031011502d90741b044c00c6150705130180b0180000140c0303076603d0100420307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 560702760 1250 560701510 560701529
    0x30615041a0c0618030a0c02010c0f0302030703031401050d0305130305030a0815040221090f0601150318210513180509420709031a04201306 62
    0x358a0044071514140000d03161610364414009400c500da1000002c0f80d0b10300c1b00741d08083c180310100e400141c0c0d03000d42403c005010380440901400c1015408002001040e00c00d44040004001600201c0c100320350074080c841c1c2141c441c07030b60000881d0191b00a4100612100c60b10240c0c0d03070312035468600310780203648600041003501c030074411240303000d5203501500c002c01d5508605003204500710178002028201c0080c11b000c440008544441d00601602c80c0c140320040171904103594070b00d0032880d01d4040d0138401c00080e1400069800c4056840d056600464002c4080e8018600503103405103d003810614100500c0020400d0440640ca03810b03d1100420010801c12446288200f601068030002018094540c00c40a4000488002c40190400008618401248282c55207070310016141301c2c2c103020341618607800100036290f03138440c2040302500d1207461000e010890100c00180c5c4d05034142c0d0700401400b07800560405600d000c40400c41c0c50040104003600d00c0010121030801c07151160011a0031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 560704010 1250 560702760 560702767
    0x914010c060e01060f1a0a080105010815150a09050306090a02150706050f0a0606170712020706020f040515040b0306010f0306030f05060a15050f10210c03050c0c03030615041a 77
    0x103038001100442c45c0d510700d40043c28078052450100400c8c1020500411341480001000b240c030310b42000300b1920030080054254808080310120120382e40d001014460000385078040003040508001c07408602454207000100444d0443d58208244100e80300010481c9003001d100c11ba000c41d03182c0c001c0034098000c9600e080d8141c204030384200c083d6002c60300110709004100e161046c801180d26602c0d980440305182c884041021352000300007074031809a01620031070001c0380018000024200510454100301c8001040d00d1464501402901480c468646100e605200160391540589400f844040d403c0c03400040c0707941c5907554220080b00148042e55142e02000412004a01d14412074072a480040341c03c1c03034080e1520000401c0c40b1561145280690010a0070ba803169020b00d03c003a20380b91000c20403490002c048011000105010f10028001a0807e404202d0303410f13003001103400b049086005149580c0d41c440900180c02e0780034040d411440350410000900c0c040c00d51107080000d2000689030354 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 560705260 1250 560704010 560704019
    0x10303090302130513030807050c070b030109060618030602090d020d0f0b0604060b040b2104030f080c07020619020f0d0f08060901050d0b0c07020301020a05040e070914010c060e01060f 81
    0x1c615407110038140c3c1d40c030310f401c052085003801000e040c06840c2c4d062814000076502c1d00000c5546000b602401d40c0c00e80300d1500b0100e40300c42d0b0300010314141c840402e401c01056540c1c500c1100c0e0409880c0b0140030755041c18805102040d420740050415500c007610060f40700270942d01203020303885001e03c141d40b440e16404a01d020809802c07606500164211818032019040803807800c5d10380302e41e1040d00c101c0c00700040c5200400b00500c003c00040a001c0001903401d2030a400c0281615800c00007010010316010001002d40203881d05070341040d900500b0060034440d81118002102005001c00025849070340240007084004120b40005104c4564861400300a040c030003914201004e8190791181c4003010040c80071361581d0401101d00e5800050f011000e4503050104030003407041311006074155000241894a594102c0000c3c000c840001e405a109a521440211644401402548809219451000c25641c480e000c82d44240d4040c41c00003802c40b070029400760840749554010626040c21050420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 560706510 1250 560705260 560705269
    0x1015140d060303031a010509040c0e03060702150c0c0c150d1e1103090a0f140a031e0f0210150b18032e1d1515030c01090308180603010303090302 64
    0x204004a61010206030f4001c420010b0610300441c030035640912b2369100c003141c100e4441c1451002d40f1030050140d4130366081080b4002c1d181e400411046042c80d06085c045034815185a00b00d943c5514440042c0c0036805110040080c0310b1121100b9401c0400180241c0f00c41140b207100d1181000e10f0506100018560b500d10b240c01d41e030b20000044031410f002d004221f40554080345113a1820f038003000007012060503180c00b90101901c2c0c1e8030342c125031040551901c1051381001d450a00901c802d02d05d940a8070b00b221003101d00c0000818140c0041e0403084555000c003429400c030351000d03260014202900d42d11910030301c0c4540c00802882c503051038242c03020b84807400d041c442c09800071500d03c401c810034543c44d5002d80b403c0c5042070500c1c3c00c069071040c124420310b000180002c6900710303030010f8030700041c04549551500c40040d2098201040901c10001041c9030004021443c1b54042c0c441d090050710303648503a440b54100c00c06003001c8840c4c82c0d40c00601795468500548c06140b01ea1a03071003c9505500620 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 560707760 1250 560706510 560706521
    0x4030515101208070f0f0c06050a0801090501120b04060b0409050c090a020a08012702030f09010c0801050a0911040f030b070210022505011d011a091015140d06030303 73
    0x30b6030412000d1114001264030b580484000d182c01c00c0d05c41030300302c02500c3e151043c0f1590380d90150a000700034201280c81a0304c80d00400c0c2c143e04640e604692a6203840303c540440f402880b510880e003c00005c1100055000c20145500600811000aaa01d1043c000c03400f03403201013100311890b820140b8278a50358641040740a400a040c8101142407454492000e0002030f0180221501c1c2c00c1e0020b1228110584c421002070004024070040d900da040c200c0d5000404070082e103030201d095003812040120a0b12544000d8100c81c0c2c01400d0700503c92404d01d80900030114280000d01600c02000049420078451291000131445404000f11034601840001e08020303c80c5000c0d02d04600400401d00100101e21040d08ac824a480001c103401c07601d0b00c0c007a401006415010000392501c207910040c41081940300184030001c009984070314050010422808a01c11140c140f421100c0301c0050044403c4a107034100b0048541c103051480d4080f000d00c0036410b410160500301d0f01074550100340b04059060088 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 560709010 1250 560707760 560707769
    0xf0e15062a1c031104080712060f020d0f05090c15090109170312090a0309060807020a140c0f12070905040f1401022a060402012f010b090723070303020403051510 71
    0x806040c91b04100116880d4800c0d0701c201c1d20454060460401400003d034480440da070107001085660b00e200c60700d004c001e081040c0d807400c1c40d585880b000a40088002c40c07207541c0154010517644130218420042016500a00344030303030401603d00008111014442020034485504a00450303c80781e0b00b0300310000d8808010400a0260817180301000000c2c0c10000103000d84a050501076442d55a181e012480c003a107942c0d01801e40c000158000602d0000800c400004801c01c2e00c0784c101d10030300c0c04140079080ca40c00030b0100207540000402c200c4401c060340200d81141c4206801400d0000584440019070011b04804c10980d50002d104c0c1940ca100010b505405400300c44400025400801e4850300c41500400107414081042609002d02c4040924242480200d0400200e040b10b16500d1500070b00d0304190b02802400740d1004590498024280c2c0300f2a801500e440700e440500758084e6815680051304100c051640901c40840003803804e02c440c21007409490300108040c030b043c0005030560fa0003680b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 560710260 1250 560709010 560709041
    0x20a0609080703122d03060f032001030204081606182405090a0303170709081c02030906031302030705151b030d060f0e15062a1c03 58
    0x14104071040021032400e080381d030065003d4040500c408402d4031541400120318006030400c50515149900c01400d950341d041070303039808001d03207910703812014403403501e40c040540504100305aa12420800c0103174201001d1042c0350150400f940c502d0300d140f4003c1d810310040421042503609000155118210104400003103290540780351405a0300c240388020448200300c0c4920108040320000d000340102c0d0085075018126004440c0d07607090040c40c059005200c104505010404216201d110b122200161621200901582505c500c041c10002d5a01124441940010300c1017084543c0c0700360145219003048000000818014810541808410f070400c6115100078072074507050943d000c0540e030aa81092505118020035440d5061071801100107940d0160b04045c0081803944c1140c01d140211050160360781002c0e150381e070740c0c854107500080560750400300900000e9511203480d8010264200250724580b00c89c10442d001c40c0c2814011119002c0850301f0003800540705034140714a04200c00042c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 560711510 1250 560710260 560710277
    0x9060e181b090a0b060a17013017030421020a03021e0c0a090b15250317091e0a05070512071e0f08010c08060103150509090307020a06 59
    0x30001c400340741680760024000c14014001601c141000d0380b022454400c02402d00d03403102041074005007000e80e040c14840f00c203120300c0000181e44690a007481c1d0790b502c4500a403480301e043c042c14038140da42e40c0802590b40c000302005da00100c02203840258040c0740200d4914080c000010701c0c085001030441015001c560110760310348003196001c201259011001c281c90503903c02c03011542440d19813405402035200c09299000968845039610010030b90720f0030f455440000101c070f0481d04003402401504d4403000300c0303070304501c1c6455941c184141200380305c0d040080c40070201c0841c1c442d8180742120700303801581c800000502c000f546810003403411084038000300003001d0f5a540e1240c494443c0e101702030080246000400d003d40007440503801034680b50480600448517803104843c1801544181100900908400b0403c00c2060240400010444c0c86803034068644500450040c103101000c000c80e40201440450716a032210141030103080c1c40c000550b256107041c0100002c454280d44490700348810078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 560712760 1250 560711510 560711533
    0xc050a0506280201021209030a030b010801060f080612010c030b09100b0403110607022809020a020d0f02030c01060f170307170c0a0b330a03060f0609060e18 69
    0x31424040000381ca40d8082c8030300104840c1070340640100450703441c90303078200410003a0503e40000940f40002190b40d040c007c003c0e201c0c0056414503800c2c02104005103610107040211400b44a03256004407011f482c4036810101600d085007156191562400003a844030150b650351b140c1088069000042884817025007403403c1e000760410b104620004016492a07510783c0d00903034881701903603030640d0013a02c81c090007000701c00c5804103103072141c0d121040343c3e021140c041592038240c402e0300c0c428400c07600202224240b9800030b686038800a01103900f1480200551604480b0a02401c40105038080110103028103002122440c0482071091480980c02400088007240855064200001150303907130668900c04141000d052540e0000c025011645020500c001da0740ac2c0102001d0040155008007a5034a0858040e1314014918800943c00b018400701440858121781c4854413002c0d004000145140c4c0d02d25000040d02d01590004001e03440407010441c10700d541201408500a17010003600113513400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 560714010 1250 560712760 560712787
    0x60c0c0509130b0a0902040e0d080a0504030c021905030d12110702010203070b1e0403050306030105090f070611031b01060f0e0702030406050d02090901090e0106080a0503072d0c050a0506 82
    0x141d400a0b007030407050740c041130000503103510584000360050024046001c8845c003c55560500640180004040e940040c10720036042c45268001c0f07905a40c0c0c50205d51301c6808010b22003941c14036010312842035101c0020107640400c5940219130064541740394402801209130704031190001c080500c00401c108400050382e01100702c496090f03002c89225070940f10b51b805500b000c43d0038502c140c59607024078140414150030401a40c0301e15030840083c85956218490036440d03088480c5180016031219070140301c001c1c0903500040c0b05010f00021203041030300001c03140082902e50070000201c0d941d500700900092a40684d500042d00340f030b500031110340c14070410095481c0f10714443c0340708001c000300303540015904a030102c900018001f410001c00c1e584075040e000081c5148080b2100035881c0420000300902e000c21240c7e45940c005024500f402c80584844503900300404074589003ca10000300006112000d40d05d000030360003194500e1020f81841c0600180784074640090744a41c1c0144062000c50b0f01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 560715260 1250 560714010 560714041
    0x3040222050901201b1e06190b10080c1c06051008040b06010309030306121b080703020913030c050703030c0203070b030c07240f090510050603030f0c120301060c0c0509 74
    0x5c003c0b02811400c401d0710429003010080d00161180c441840c0000d039040d1030010303809008aa075001519100340042180f90304a404082000d43c00c2213401020342540e0707018034206540641d01002e21854288210260b00241c851461600141c82d81c2d03c4c424425401e0241c2803650106482c1000c200508154440b01c80b441e0006100c0d0741056144d048582c1010702c41d4012000600001400000d50b10b024903284400c600f200100c80714850f609040000d6814000698404990700a401c5819645407103450040c01c01c0c241000360305010800e600c450002c0c1007040160019070181d581e00361a061a481018248506540714544409080c03041c0030a14240c04221a00365074894000c5510301c03d0750082805401d691a01420100c0c43e00e0714510469401d030701709540c4031f03200740e0a036005252000c2d51502240d90035507402d9019482801401b038464404c00c000c0812109201c12103100003e4891010444d41c000d810085c00141412400010410104800c501a041c00c5441c4500b5190000d480c2c0c640300e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 560716510 1250 560715260 560715277
    0x40903121a09070806011805010f05030a021201030f0b090303061e0103090501051003030e06190c0c030c0b090103050a0e0c0d080409110a120606050306060304022205090120 76
    0x207a40c0c10a01d00d9804510001e94107026000d80070750810320b07080e4000380603c801102c10902080103035407900c405182c090150300c00e41e10140c481c4410310602440c103d40d242c10041040e01850313400c108a20079041315100c000c2c0258411041c0c100052010700d0034034051580903120a101d03500c280140145c1d590390100f440c4484010401d840540c00010340100c000d05106000503149510b46014040c5a245c154840b109907802921010038041800f01401028030910400c08090300d041d850b542c00b4580304180031020217000d400780040be10307243c0d140c004e504045d40e0710403344041c0c0040d4001595030140629640056800c20800c0b9003510041c1494881ea8100c0145208220030361030744080119075000c0c1d501802c00650100030101d409150004160b11a40700400810b500142c00e50250b900c1d070040505807000d969407141540c07604011310900741c102600c226400305c80211088020810001e20608003075000f4001b298600f0446a41404c607014165000c951110018181b803101c080001182c40a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 560717760 1250 560716510 560716547
    0x5010e0105012a0b010501020c010804080d1d100f0b040b030c0f0a0806010b04091d07050103091103031309060b09091906030f0507080616021f150801050f06040903 72
    0x240c030039683e00b001010121401d0380022020707241c10018410007219007416a80e0a070210b628100c1500700540c2d056204481c01440c1c01c03800c0000082e9185603400c8211078000704800c034843d05211007c61803c0c01c1c0120b10341020f60b9901c4010400070150b40c029441c503e1400d8a08219200300003001ca070710703005409d400501505002c08069140c2c0c8070941908000d060700b1007541c0003540c480c51041890350181c42440900b60400004210468900da840e0010400000c01480914070b07040064000e0072000c101601e501459078424900b646042c00200090003802803284e0400d418260746804444144d000007000c42c005010690060b1102d4415542004240c10404900303000725550002600d21500010070340a42a251b2404000f000608501600d402e4002d540302a81c80038508400381000c034444100580c01003d080340c0e4500318070b0902840d000b2400c40802d0320080080d80034506210350740b0006050395107108000c0f030030b5001ca12150f00702c0740441e4180036034420307600c2c000e203103424602001420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 560719010 1250 560717760 560717777
    0x140105060f150702151c06030b0705210c0714030307020d0207120204110d020c03130510050d021803060c0901090902070b010e13120e03061003050304090c0903210f0305010e010501 79
    0x71210580030341d050004520100f01e801b4480c06221406420644001c40e407480072040071a039170300d005000341c582d54025040c0e603525105403019650180c480207480341001ca0b9003007182402190f40d0603140c2e10030044002c000c40e501e00303216500914210300030700d00d0011500400c50604c01c06d130001841103401c0350100e4011400d04140c14039104107100f81611104140c0c13000540a04140e000300160090b800102d4182140707030f94800c203211445c5140d5190100044007040b5040721429681d020784003803852a40c00744524041c0301c0110345894002e50381c8a010910219142e2840c1da40a40e140f00940b90724036056040001698403004890700c18010b0b036424031041030000d4001304c0e52814038480c0d5a003103081e00550401e075000c050070080c40c1c0342c5c04600901540c00012100314000c00ca0004480d8807900461609140c18172400003003c01e211260204803ca607800008100102d810740c41c2804483e074454003100c00148090002c0c600750340b21a05141c1001e004100400501140c2c0c1d0440303000703080c040710 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 560720260 1250 560719010 560719039
    0xf10090f0b0310090201090803030408030112030203190905040e01060f05010c210e0a120b15010e090f010609050d0f030c0206040b07060b0f0616020d02030a140105060f150702 77
    0x24100c1c050074036805204a000340010000b890700552101c4c3d0003030701c900d601141c031500301940f684012140a0b04102c000c10040211108081c015010704d03010788103076030424861080e10810325620b95001000a200740c042880070340b03001d104075611414010004c20681b494660110315030400f41c8601418131121044c61000d1084030080c136601c103103062170103001c200341c0d41c2c00c040c1c5400041014103028030842d4401240c0002c0c1030015603d8030341c21001300080da58170549568150302c490720711103041080074900d065050711184501c50141110346640d0003958107262008280030500e911041c0302d56035642e103003c08901143c0b6004200754041c0341000351076505002081207032180d03030701030003001000081101c02d1000562200c000e5000840e12207240d040c01e58100043e034000e010601c000302d031050070003200610701a004860024170103420f40700c201c0003139182d4148903521a103103140d41c1d945034010406945051a941110980300b103902e0124503081e45002d0130b160150880081c000d01d100b02c034044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 560721510 1250 560720260 560720291
    0x11407081b01020304051605060313050102040803040305060a0c0c0f0303020d11071506060206060a0b09030a020312030421090608060d02100203070510180803130c09060302090f1009 80
    0x3101001a4030707070300074520031280d0014001d41c412142a2818050041040828080e82820344102c8078024006411504e40e1803a0503254102e1300c00803203641d9400c12000500e05000c3c0090001540180061310301c3d850a0303481c813000c2c0c0d5600027848041001d6419080005255840008646a01403a0041c0c40b40c03e40300005006010040603102c82410120703050701042142030000c501c106503440d09110ba140c0d50041aa6140d10555281da40407012880030302c00500c050f4040e0040c2e40b0001c04a642d40d0003580c003c03900f012601d010580800c0c0c0700108000c1800311491f08022001018250b114400710b00180c0102071342c0e5030b40243c40410a0300c4021580c299079091301c107103590340c008103410765103010f510000c0d40e2607000c900e00311100d020b130302d081d003034182080d00c00c0340100348040c10040000d42aa40c0c03801c0d041d510041040c0300003010100e40801240c403111072a8040d1844601c000341d00303415801000742d11100109a02807000000d010010011000294002103440310b0381c0204660f09402c5075034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 560722760 1250 560721510 560721517
    0x3310060c08070606030807120206010509152403040c0b0408060a0203250503011e0305030d0c02030f030f06040f1e05100503010f0501050103240e2d07080a020901140708 74
    0x103440c50381055008800c2c04040c2c8002c06203c0e10512311095081d40350281680c03030b01c90134440c669200810700d002601a99510b4120414400020445a5a0100680c3c0212140e021200481c2c150001004010800801c220300801a02c5490700190825291292859807224000c003074140e520340100104407070883c00542d8a409030010701c614118075001e108000c0c415002441101920229a58104020242801490242ea422001662030155000f00d01d201801200215108612041000c80c92082a01c0003460245c50520b0034010300381010342c10003081c0c031004144e0328003031854050010850181d01c2a0310081407030362040407401e0b0790764407440d0f030840010b51310517501542480b5440c41d056903540c2c452816900262010040442c02c21503640082c50440024940b85205c0b02d028806040d140a505a100c100c1c15110b446065400c44104891312450910541e150f618500b404034940d003003c1e8660348007501380c4c801c42c10500f03080002410546440d40510030500c002425400303005600084 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 560724010 1250 560722760 560722763
    0xc110705131b0c030e041509050702070b13060e0f0d020d081c0209030114070c140c060d0209101d0607140102131e06050901030f0b033310060c0807 65
    0xc18041c8109a00141c1a0002d070f0100f1400030b0b0810814140750701d024070402112003038103801c40e800b6a0402100d9001090003505042c2548a5a04000750042c040301c014120080c11400344207506282160180c621860b007140c4601c01c26100d181c141e016141c0c000c9110681d82c0444614194443c00e045c009604d00c603915061030043c05c41102a201602550000c01c1c0c0c2c5e03201034000b000600c0009040c0c10400708281d40f90030001d40010002400b00701d08a80c00700d10080c0b504255a0107560003400900f1030b520203450301c103440b500462902524a0200002c5111200ea42011700c854440715550704805031602c600c09100c3c440200760101403103103507007039035980760501402150703560241e04001320030000a00c00c001910405260581c070068402c0b202400311200e94031030390300307000f0f20300e005402402c03055407103485107503840014001c10b030b408108261548030580c9140d0403200c074580300b0365290001d0b21004100030182009008406103008a020100d4500340351030503d400451801403a0351040c41d60 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 560725260 1250 560724010 560724041
    0xc090d1104023006061c0b0904030c1208040c0524031509090a020108180c03010f1b0c0f11010c0b0f0f06090f040201140c0319030c11070513 62
    0x8400403198001c0103690309241e80b849044078034101000007000d004008079881a04100c4c01d010041003028480c42c011406d4044000c00714006540001240c19035004807402e400092102c50030320107000004080700a15015032402e00b0544c60305484002e4161002e100b10ba00a104550740d000c0d0210180d049a0809240c2000059482c18a40040341d65030000b100941e00c0303000c1010106150300d1740080e40c0c003202641138460049a13507440f04070a81d00d64041300c40c01510f00810304000550b603020301c11803d41c80d0003e000061281c09018404013030b54045070b4094280319100b01c942010441d0160300c41980d5901c1006040c400c080000101c8007460b032054010701c04001f4100b84a042c03c0110841481030320311a1801e0000e540b00010012044002c0c2d400c3e4585e910090301060143d44508988446402c43c05490340c604aa0100000d1441c0d200f07a026040030100303448040b26955050268810f944400c3c07601e00c550518500c2103035103c405a11a02d07200d41700d40c010380d0380000516000450303989803864 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 560726510 1250 560725260 560725267
    0x306070917010209031606020c09011a0711030604030f030b1002281a190b0d0605071b03090806091f0509070506030106170105060f0d0e2e0e01050c090d110402 70
    0x320002c034030501d007c0c100c0540180324820895007000c5c548039049174055840310341c214440749203c51143d4003951040c2c99041310005038407940d4504100a5000318030070782d11940c20a15100c0c00808a41d101607419104200100c110032403541c0c009600e80c2c8100c000d09120007000c0c1610482040080d0a4100a150b160410001c0c01a0f0300c0e0f07002c03243c2c8204800c6c0a030b101c03502080e0b9030440854102c00000340d07200c00d142030315001080007980301c0366015000d4100500c03200e01000e282e68540d84901800ca0002c0d455002c01c3c0a284002c0c030404d500034500c08010500000100362030940c501e020b000310700300c566607600012000141003080000924001d441c2503520358403404000c0840b019a04107501d019420000056107003070180803900311412200e140d80c03c00320301c9a68a005081741ca1079540041c46002c07105200b2501c4c85004081079100a0164060465141608001d4880c00240805144d2610381040004d0300040115044250100d1b10150f441d8070a1a11501541c19844c04980151011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 560727760 1250 560726510 560726533
    0xd05091e0615090c1209070302060f13080c03061803040e01060801060206130c0b0a1812021002010606020a0305091306090b040e0a020f3003070b06030607091701020903 74
    0x120701c0d580540d030300701d11291481100c081400b20741e040070340e00d60701c204a0070401044031141c11891242c0085081080c1c8150340c2d0380b0380004602d03421602d103554607400000744c0d0580354040585a06c1c0184800409000d03c1180d16000075103500d80207000a04030940c1c802d002c1500101030084402a0290341104da0095850341001400e502c030901604000d882018007142c4220300d880080041c407544084400c2100d400d0400004c500d030071244840c07042c0303c0b00304040c004441078825100050a0890f00310f001d001071500400280e00312a6504809591420000b03000c1d1607404104c444500380c05090456403995440b0104520620301c42038038012a04c1e044000c95240041d0700700725224901181d050290540b401c02c0140c696548400c0250301228550002d00d960500700204204401c41c44100b240c80709012400c4c4800e824940603a0045400001d0310350100a0103080c0b19400c442c6c254014130f85807901b6030000d080c41000380207550300905a0080803070811000d40484100d030034003030161801070380d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 560729010 1250 560727760 560727763
    0xa0902070602030109051312110705220c0908100c1209050a030f030c080a09050a02190f0902030c03151908101a011e021501060c06140603030d05091e 66
    0x83c0105c10003039090030003241010281100d2180980d0708000e90400c0c030044c0910940f0f00c44044c6815000900a0030000961603a81400d03d0b143c407c44c41c0704504520310700130054001c4822541c0d0b00014007001500034052100005000105880840c40000301104ea4001c00d889100d9000b052042490521802000704000402c00c4840e15109407161180c0450300c0c070041d000c0d0340c0d440d0304030030009030410700085601126030010600103004109035081c00c2c80030780200d00344a040b1580751800a010390401c01598900300915001003801c00e2085085080190001c0c0300c612018044084001d00c0d0480741c101943c3d214074002e0720300c91341c01d81c81c2c4199940c0c540050b02c03100461000448940b81031006091040c05840d5040101c83c160764248810205031405001141c5e028440300440c810500c0a2000700040c14007280a400146c80360306c540300780c0b454504161070464070104500711b080810312595880c004151b0740001c4030301c10085090303581c48981c14904400030106001005c0403d1990303041810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 560730260 1250 560729010 560729017
    0x204021b061b120c041a0406090602030406050904050709180e010b030105010503070b07170409022a0d0302091807030b090108010b03060604111902030c21180a0902070602 75
    0x520388180c42981e07541c0e4980d8409615640032040203014104491039820008944542d4049440d1a0071400c2c180c690140340f4100b00791841c0003980d0071300010107002041e0041c820310010001440154901824518018030b5800341d006079038003aa2700c0e9000b180324180510024005000c0d508040c10106140103091009400e404803240225460300c11800300346d0906004060684001400400c0140e15054006035aa40003100c1a0b900108020340d40031654410002400240312021025843e0407111154907102403404180e41c00c01803889504540464010a100c210050707182030050b25040d00001294544002c40032009149440710200140c10740c05910400c0e00c14406c1d11680342c242e032070342079841c200ca10b004021031703043c0d01450006405190070f4105a91642107104442d051642442c944d1003040c07600440c0801680011815000b480b108000440303c85401b010030369086144070380c3c801d200b0300c220020200c20900c64814081d990b1122030514000303014080c0115035032400c81c20b1510083d003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 560731510 1250 560730260 560730307
    0x1171c0302070611030115110307030e030a0b09071d1501080703060e010305011508120f0a0c0f030206010e0a020f071403070b0f040c060906021902040b0613170f0a030c0f020402 78
    0x2050001101f045601c940e00c1030b0006110580210314001407500e040c0e80b412841d0031111342c144280f6826800080081844500815806004103806e074240319064441911201c60b21010700c450078100000c038120b48403c1c105502c4203080021094071280310446c0904401e8103c080914052070000003000380542c4614106c040344242500b03c0c1c2e0301c0c0c1108588440f00b03442ca0390942c0009100c40040320070302c03000034080c0185600313005030258410750381c500c0048460401600503810030b40042003021500105598040250320085103801200d00000c0301d036002e0014040c0c42c01100f004a141c50190400403504d40c583c120511800c0c6240c01020100700c014101c408135600e07540d07168006070b0309000d503400300103a42890300030f0100304400702002e1382c60604400e4280d03805601e078220903010b030b110385004052400c00c41c1c83c003002007420480c001c050b4044065945080d03610a000003601100d01050b4140c1c143e82c10324007020400e159003030500c40b241c48450040d5200c0e1001907103551882c1104422903a00307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 560732760 1250 560731510 560731529
    0x303010e06010906140319060602030a03240308030414031605071d0408090d1202030903010b0901051804081e1206030a150903050c1b0901171c03020706110301 70
    0x1941c90800455260145102d0704010030200c40700301c034105080b0342c041d65002e07242110000b40240c00c040348209583c46540803d0158000264010701e155050142c82e0503a0450a8002e1041c1216600800150194070002c1c001040c0072002c1020480500b284c100604071301812a6150b01c190f101d8032070800d2100100f19403911940c030f000654149502c40c1503204100250640d000c668941c0c58860310b992010101d294012540542100029030401000c4552031442d4021501e500c0501c0901d130031a12054002407240315400c00400c0f00d50f0341c41c0300e603a100b5066014051016125490300001500510601800704401264080d16204c001d00160a40002c04010301c02c2684520b820706448070090300300544217038012160406030311080e40203411600e120f40350030791034881280442410000c4405129194903075400180c066071511034155805090101840c00c120311100100c4c695400e802182a901d13313142c002c90150450095056600d820f403c01000d0008860030780b440c181c1079109002e0240304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 560734010 1250 560732760 560732789
    0x1f09080708070e0a1805010609020a09140d080901052701090b1201140a0906030f0b061806450a110d0f11160309240e12030408030301 59
    0x4060340007030b034a07040300c03030044201d81541c50700f690319030140010706401702c01000800041d00000d102407040034014000b0400040c0c8912240c4402448094182d0144001c1542f05800d180c9690780c0c1d070781142c070540e4042c5510743e54020010040e1014001c101e01810491440c2110054000d1240d10000441900366900004241c0740c20f10005d2030b00074070080e880019502401031044651000b00c030000c07810002c020b03a03015071b40e03902103405861981e0812100341e00003031300d00402c0000c040304240c0c01401c21258030480c0810301400300989000145110b1240321125a80300010b03100c1c482c3c0c2640c07400002000c0d40b07240000600c0d4a5500f040c0c080920703800610500141c074569003849450380c00d4080c1c091249c5821109a81e1001a021000c0e201c00a284d861041158425000d0700410380110b8501300346520200c1400d02404180f02503021805541c2641b01507210001e94101c4044070144a090100ca1009194049004101c001000c0f21052200050220303100b400040518100e50255841c080b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 560735260 1250 560734010 560734019
    0x10906030218160c1401021b07060507050325081603080612121c0603150501151e0c1407080c18010e15130207061d0309010309021f090807 61
    0x80c10342040f02c0341e030b0088454059440195104d280c400d50540e0140c540200307000001d0b00c1090882c4c0c40700308540c2c0d021092640c44e0380c140a05004590051446040141c10070109483d03464491080c03011401041803e588555404406107410b2800b494202860310f480e01040c11004030030b8a440102940450548000500285018041c80c07002d00324680140505414038070412100340c0140c00500f1204128003590008060144180d10055008210207031001c44020310b500110b80068110846000e04203105401c0c0c11342020846c0c04144410100fa607504161950890300c0c0040380302d000340420201e00d10044000302c0005e804040e13481c8541a00e21b0080d205040010341c40b00c04041045c4000914010400500c540c0b0f00305a01004407843d0400703180411000903006000d80901110555000c038410091100070711501c00310680002d03004044201144d081e81d0f1301e0094110584c10140c81c0c031189804c544a41008883e04042001500d1048003c580d002d00503803e203004110161284000000e03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 560736510 1250 560735260 560735299
    0x1107031707140a091d010509010b03092d010504030e0307080304050d2303030103200405041a100b0304050f0f150a09030e09190506010c0201170a0b090109060302 71
    0x5008000e035489400b54030280b20b58400060b000f90030b020050051480c80040c401c0009084400a01c0c943d94024443d907040804204007650181c20400b4980028003c000300f443d4005005a21560904c03042c80103941d41050038082c040b40300c8801101c1d0350908050000b0143c121603d0b64100f58228140c500c016103c94440d950f9000d180300b4243c1c4410442040d80107d6110842813030302d09100c1c144560b100b1189403106145900aa0003101d41a8a1001c150300d400f07800200285240c42c1207800340200e0906440c0d00143c030303060440708403207024060b01040b40f4004d030700b02d0300006041e8140d441da10391800c0c2c28101d842e1000301046048a0061045441200c58080307681172403140c80c2541c8004070b0711000750340d0300100388040048003440f0a07503400d469159640b002d850301c900c1041c01c80803c3c60b1742d0700e100c0e1802e40d040500080d0500c0190b1121000507a04600d06070750507148000140210790383c0d02c0804018000c1c0b4040c003504102100000705040348103410840a03030b03000f0b9803014443c070603074214407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 560737760 1250 560736510 560736557
    0x210906020d0903020f060405090403110d0806011e21060e09070b070f03020327240d02032203050304050d0c02090a0b0409060f14101412030c01110703 66
    0x70400500a110144014038240b035500d40c00040180070542800d072100c01291010f041520190007159000c0b1628550031804c00c824030300009a03140c2071403079007013140c00039100c0480e00300300307001c1e0402c1c0c19000ca030350358420914600b0648002c0780043c82c0c0f0480c0c2d0300d500300801c154000c40385c20308592400121800b03c0040c1c0d10b4200c4402e0213003289808216103031a80913000089044045001c1000454070200c001d031000c0b0f0383c1a5403110310070168101f050400a110400d848030340036007060311114002c0c41800c10245c800d4100061005a40e980d280d0140d51242074840805d6480c0301029a614410300d6845009184070b43d00c00e20440300c1e540580e000580d40c0402c407010007540944507000281c2d0349851900140e84581000d0008076280314241c0d0750b070041e51400d40c2850b1519a0b10b81c0c0d01010341140032240d030740044111604400311400d048906001e0580a406180164148464040d6600b81001180c90f410003140003001a40da82d5802c41c0c40c43c1c4d001040550014045500e00c5440c0002407464 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 560739010 1250 560737760 560737783
    0x5100515041401050f040902030411090906090d030b0d05060903040806070905030a11130504061b030209030703110d1b06081602073b0915071403040f21090602 70
    0x1042d00c48544900455159000d4080c1d19a116004c0c000011062072500107913015512076904008200380400c18031080000007040103440360700450600000010100e20306055103139602e0041240301483d000b080d10441c050300d0003000c9118a10400051100c04005002030720b101e8004c0e075000c0d0f110424111407800e410b0056641c150442004100040e42201022900c02c40107450541142d828a000e001103c0b01100d0585840b030b212040107072540e05010044000480da42411414000a00c0100f6074400040c000100050010602c2e00c03a035075509440440070350341c0000b0a040715883c1d005c0c1660112714620a210100308030700c0c0855520840d10f500c2a09400440d4020300040b403402160303900520b4180c10a8400d4030045800c403010090380812048882d0308d4405031000c07414141920f504d8030b61090741d02c401d4134124034140308141d9440080d001503644001c3c865a226100e43c03e0130729400c5103003031000b0038251b0190407009540c0212940f050a8140c60745490841582e00c0e1026038684140020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 560740260 1250 560739010 560739029
    0x9050a0b030601390b0105041e0506010c02030f0c0a054f02030907120f080a0e0603070c03120608150a02040b07031809060311100e040510051504 64
    0x190095214490542226402d200040e1a0307001c0c552070640c11051300d06925070400c0c96511414144250301c0b09242c0144001e880c00c1107a0301e8100c004c50840c04040340b24100f0292518040f1310703ea071150f140c010035179400030103071842c10500340400d40e518203440070503d0080c0e45044000400340740038480701c2c416103540b00c52040340100d1500c0c1038003d2448101d865900010104070111102d004940d806500c07a55100016900c0c00c0c400c0b009841c002e480c3d80b041c5400700d45000c0c000b0004100c10a01e5030740ca907100e489291560754a42d01603e0154031485402d0f0080808410002801c1d0302a032a1104280a81c44aa0104038003030703c201c0640e603040c0a9141e10b580310055400d00c0c0c501d903480c0164400c80c62a00142041c0d1948842c0c50309510004c010340000e40c1050403440c8045800d0302c140e0080120074410015945181d071942e43c2d68030281c29103840341c40700010030f5a1040c010300c40020542c500034020081807408080b0500c5080441c09401d004622a40d81024100c1001040b507054a01110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 560741510 1250 560740260 560740267
    0x5030f0403030209150a0906030f11040b07050102090402030a02030a0c0f1b030c0c030503030106020f071505030a09020d120201360203100e0d0f050306091504020f071209050a0b 78
    0x1c40c190042d50180e0110390308511100001c09195007400d02902c0b601056a0310301c004c02c1d00e0821f0080030340761640403208880d032420480e0910708922000700e034102ca50b04025503842d403140741000340c020301030101821781060001041200300b040b035174001d40c070600301e40004000880420000700c802089840a80021820100081a00840d04954400700c0ca00c28506880648001c0c0d0303a40312808015070049440b58008001445900c2e01404400b554001410081c5040303480c02480c0180100c0940c02c0d4000e002c000804114070700c01a4109050842e0040c0c00403100300c4841c03511030b1910280605c007100551811400c8203015103005002c1c40c5554500b46035008518140c0c103504e04001079508120390502c0b41c080714440c851454028859803440d410060580140300d0b0134050181007070813500004001040041245659900740707102c1d00248441a81c06040c420b40c2c000c10001d204001c020301c24808040b80040401081090301800c810803035035829542030f505c0301072101c0007042d8062201044402d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 560742760 1250 560741510 560741513
    0x2010207020f060d020d24060f02101503050a0f110f0303040b161a01080709020f12041e0b01090b19030803060406030c03030e0306161211040506030106120c05030f04 73
    0x40b800b911311644482e40c0103192520121491003200c0e100c110340081200b01c20a842103c22140c10240b0040c04030782400e02820300343c0880251200303401d003444600c050ba1161684807603003481c02c600c07000e150711104413a050f00c3c2da81015404020704400803202c42184080099403801e2010300c0e25501c0c90301400131410182030036500031654006050f1403110000e80300c000404110140742c001a01c0311012400d4480c1c1d4101a245406c1002e035803c58101e84e4010400100c04140c103004a6810401801444049807202d1030100052400801c41d03040754694030361042c0a10620b8a021412030b4561201000720307181030000d00c02048440d60603052508251035040001c0745031754000b1544504000c000154154482d52081c9103030f003440e0019400184c1900c83c2d203141e414100b001540261501181e0240c26007401c1e40244180c6890710400603894544410703540740d400c3d25098902500008012640740c8da12010000c1034092042480c940f072a0414400c190b0817030003003080783c0c041d400340c1c80b0215541e034a9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 560744010 1250 560742760 560742769
    0x105160917031303080a1b020904060507020f030a0207060e0312040e07030207061a101106070f050d0203010608071704080702010c050f010e0c030d03150e100803031302040c02010207020f 82
    0x1248004480d9002c00c010240540c4451003000000d5071064940355110507420310020f0549400c503500180307a00c4500440c3c800340c0d98824041d83e01980c44840411103075030b0294220708002644800c240700703100104401a0bc180c020a030300007980c0d040e588030308076407032003800301555000f4500d01c0c1501d4400c2044144641c0d4200c400555210b041400c1c05440e0103101c0c0e49000845040710340024100c05c40c0395440c40a80f610141900c15154545002c0c003643e110b030460540c03204006448907051140919003c40c107640600140c5003c2101214119142d6948882c0039001410031105940000c8181210000c1c00d5a85030086014541203841c060501301554019560001c0075041035402d0722400714100780205d0240070b80c10310360030b002d400340101008a5041c9450081408100c00501d400d1020102e000c0886088440c100c0354404050b034000c2d240d48500c0342c0c1100c10354200100e40c2c0000020040882a40114000c030f4510980c3d041000c0201001d0072401c07030242c032000030350103800002c010115140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 560745260 1250 560744010 560744039
    0x30c030313031202120d09020f060309150a1509050433050a06051e0a120203061302060903070303022505010f03240306060e010e0f070302210108030c01051609 70
    0x42401110241e21a0012061264120401809421f074403402d440085050071a80c0104110003508d226080d4108854100d0f201d0345524514030008030082c000a12100700743d000300400750202e048540341c840c3c079080d018000c1c00c81140c0c01e440041c1d00600b110b0400c1408400050444160310703014141d114070700340304030280101138000c00c8481e0300c402d00807900e0703510b102c44041c1040b181ca20303240540c01880c040c44aa40d02c250711600030006406906809a2000305007503a000210002004404440d84005582401880041d0780c251294047c08010940c002594480408442280d02142d0100b40e80d150154601030003654005421024003020607402500403060483c502c0c183c01036000c01d459014042c8180c41d510955801c1e88030702007042000171003410540504440d00b140b031481d140030142c0d5001c005014101e403040580c006141442a07648000b603e01400481104840c00d50391081444d82e01e4001c450380607069480c102c080f5103070151055a10001d00015298041c0051402800c86d00700b40c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 560746510 1250 560745260 560745293
    0x4020307091503060204080c0f0102010c02030a0c0c03080310180612030c0c090203150f18061306090f0f1503020916051608120108030310150c14010605030c03031303 73
    0x1220b82d10044005072481c00648054a001001454031007100c008221001c5c03c1c00305038506591400501104681e80841150703a01c0d0351909115400034000e00d05140c0922256002030140314000c070a000ca146030000907101101c8410a000d00c40321125111030003200d0840c440c08440d91481c14540e00082e0040c00644003003406a034220080e903594600b02000d03a44221419480c10480081c1c0c40040e1401c00c1c00805980700603103c104a0240a0751803a410850150840740700e1003848140d031441040704d07009000030702004e034003d01080003030584a030041c0060f8a0303030014607802c040d460000c3c545844003070011681c0040004501707403201c2c03c0303401068584a80f10420000d08102401c0380f4514500001c107410b1046a00e01e540342401e544502d21602c040c0c0010075190410401e12404000d0020601d05031102d6851150301408106815501c2403090314008080403e25490091001c406520000488405030146c03180a030012081640b2032003940400004600000710034004501241c1c5203a0001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 560747760 1250 560746510 560746541
    0x5130618020307060e011107152106080a02091e060906190b0705070819080a09080a0b04111c120201090f120201110a0f080714070f11010203030402030709 68
    0x41589801003424004182c1126020580c4a00e140d203155074000d660072213030440311f009031280794180203001d09000700030026403040290f4000c002055451685142c1c89004007003408000304c0d50b130341410907141d000190f401c2c1d07c2090f03810006003d0014030400145100d012801c0012103666000422115840250000760010841c0d0b1148683d0407003900d60360701416480d94003d456402c02d103070040c50044150414507443d08403030b1040c01048071040180b100d0561001d42c198482412030b600311001d0350316a002660301e2048501110030f10021001c90381c0964082c001850103640c40340148039226200c002e070705640828510390107001c104100c0500f4004501440003250442d500d1f1903040c0e22501503041921480007618228410b03980900c28416822034444010b801d1170680d581c05825003148481480503c41903100007200a071141440704403800a80d00c50342c2c0c60781d11a040c20084d00c460305c0c03c121307542d10071842c125207298000010341e8421940203004110180c1440341ea500502001d035030040781d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 560749010 1250 560747760 560747801
    0x8040c050301020a02010905010c091a070203011401120302070503160902030408040527060108010b16060f0501060e09010506030112020607050f0a08280906030e0a02060a0806090703051306 83
    0x1141d400780010314079040da55002181b40c8a09040c0b0b2821601e02c844035a0500405820070000d040b0306804041d0221000660b2640752840c44c00880d005d89856100102d684003032000200e02c010914480043ea18066821100140e80365401d259403040849100c5180710803801c0204484403842c0c0082d40d00910484c00a030525607200040788120400c042c2144502e007800054003000902100348c1c9600210034a0144001c0d450030a000c0000d03c074030f0f40038104070302081d0360400a00c1041c2e00021131050203000b04110540c1e407084000c03d0140444211407188003c03200010711442c1c40c1c0240ca041c2e88204402d04100542d55007004216808144219440d00440010342c800c410203200003000741e40100c007040d642c1c0c142c00c401c1c1151080106540b03006441d803401c144600c154850343c00003d03520642030005200d054101410301d00b03100c0400007503000c000040c12001955110704803501a44090f01c0003c0107490701d110139800e907030046074091044541509081d001c150280c111944075240012003240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 560750260 1250 560749010 560749019
    0x200d0e131b081b0406120b0613080c03010c21020a0210140610170412090305070f0314030408030f0928060206010b070b13081611090105010302070209040308040c 71
    0x9501c000319000c50101d20a2010001d01c401d0001c440d851030b80400b000149028140780c8007500401c20100000714142d600c107621801611640110351520000c1d007540108165101002941c60401c0c0001074000e5003001c00c2c00400c28002c500c0b0311f14145088002000d00c40310038014074029044100250114851658940c0d4620399520076a10a004500c2090009180c14001c0c0000b00e0310902e010000c11804200030140b91440d8042540c1041d405550138004061152007111040c12642002c2d085020b448c1c00010b0304801000701c0303c2102c3c4076000c0e0041c0103105100d52501d03405140706003096034204011140030081344000034158100004c03d80803000b10391103540c000051300c0501210340303034141e00802c0c00203c0c1c0400002d401003240105691804896a40d0240e503503034050080c00300340407101c280d50100403030f80040c0c51080c12006d4059221100508041010350995a1007a001e03114803400402c0302e502c01e00841f0708264024152000648031607a0803a0442401003042d40d25a014003000304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 560751510 1250 560750260 560750291
    0x30a0912020106090b090103112814030c010807050307080426070501060503120711120f0d08090604020d1e12091d0f010b0313020a06200d0e13 63
    0x41040c4200d600008030f607400d04041204843c0c0c0308a0031403141c2c01d11001000000c44641400f5000041034540080d4a002d890b004440703100c0940704606644581840818564411f01c501c07811110300310102c406945407040103490000c4180d40a130006a000c100017011107026160487e00117214a0f451960134510180c03038010040e42012800d84a40c0000c0c5010074414240035a1000e04811405060008110f161041203441061001003540a0000d000c0d49a0382d55a81c00300e001d40c008405070380580b4641d8141030348409440484a01061941001c11103500c1c00181c90f0b03124640c003408803e0401c60315100c94020120b03004158402c003520080790030000d12410803c1e819200691200d41c0038034100044141036119800e4940780100c02c42c400c00c0a128100b01c0f030141104c3e10316901d65582e07210180012001c1031007090280d0000e89106002882e281c3c0401601d05c0c405802c2815641c00d1065560f03152600700617410b401c00141c0000101801d464415944100c80a0490340060940703507611105 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 560752760 1250 560751510 560751533
    0xa03081303020a0311030705011e0509011e0e07080a08070203070b041a1819060f05031302121501030c140910090c02030c0703080904061e030f08090603090d0318020d08030a09 77
    0x200030ad000c0d8111440601070a8000d240d04502503c000f4007204041c04004d10b000c001042700d441c0d00c80d403140ea004c90405030900c0444003512640096541c800007505114545501c612412402071158000c006002a0b152094130261900104442c0d42a02c1d0001d50742c07155000751a000c0c003924030f0f0103d0705c42b1941d2a00c1c2840096854410804040c528002010f00005004201c140500c0000c004200c4a1110140003214403541154a100650554a2101e29100b541e038508004290400004018071101c1545881200c1c08400f10100c1d050942c0203108a0180640c0e0f842556400d10205000c0540e280e0010250a07045104a81c2080e44084840385440b204e07520036201c005000524102d10304082c0a8000036005554800c0c0c280c849115030603184807034a1001601e180150004041005299170444001e844014140740d140d040c07207085140c680c19243e801c071780864585071030035480d0040b020050741e049400420b050400e04258480d0040342e44014519100c83c0c3c1d80e21880400a610120740 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 560754010 1250 560752760 560752781
    0x5131412010c0807021905060105090406060b04140f270c0f0d0501080705090702150705040b04030b0906010512100e010b0a08060f09031207050a03090507080a03081303020a031103070501 82
    0x820f441070a08900c040e0030a00d600e0380312000040c003407103e800821030005032681112030070760344a186a91345040240050030503070003040c0864000200024480d8404028100034181101d981e20360a40c500100141c001000c507842102c901e880d60610300303a2000400082e40300781c1e0149410300d0b0008582424031158081d00120748501d6035600181301ca86020082d4a000d880251400f20742410040000781d5548000100c4995000d02400000c04051086d016500180b003111a0b19441d03035160f1804500e1040304682c40c02991145400008017450f09516560380346603940080c00102150119035006481d00d54219602507480740540c0c1d4080e2150400c1d00c0042c5074210180000d4103006c10001c1c4500409400d0140d03075481030010b5a138811140c1c1411340c03c0010b070b003003080d0350300b46604080d4007408203500c1c0500746000c0c0321800160140c0210300301d652170b44070756500751f440e81d60708a9083d00540341c0140034006910507a005030019014296161060703945104036030801c500d03942c51609640c00503a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 560755260 1250 560754010 560754017
    0xf0d03120204170f1207081303022101050907060509040209010512090106150f05180f041b0e030729040902030a060302121c0503070306171b0105131412010c 69
    0x9065400000900c1455812189400600f174024154045c01c140e5001c1d418010381240c400103042d8200190343c04640004590140c40c000710b191002d0b04a1140c012003413080310255080c440050032000c8003240c1d640a940c02d64480a040403800c50034030002390050f062150502c87e0810280194a00c0c1c0100e09105640d000700209041c0c5c1800f1060004200c5003040d0414044180103458045400c80141c030b411001000440001000ca034000500196110b554681c01601c0c000030340110a0002e4110410041661559081040060705159541e012842880d0354084100390200c2c1e59481d0b030304220348102d800d240f206d080030b40f204004000c80e8002d80d0304103441075640004004504001401000e02c0e000d0001820340f0183c10703003960244442038100c201c10045c002000855060103507010001802e42e803514201424101d1803465510140000140c101103982400040e5540c80781d022164117040702d80c20b600c940b500d030a0f04080515041c01c0607a50007010812030340c100410921070f010072913a060f42d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 560756510 1250 560755260 560755289
    0x9070315082a09150d0606090509160506070507030803090115080d03050f010b07120302160309170a05150c0f0d0b1318020f040f110a08070e0f0d03120204 68
    0x1280d0b40402000d50150901a50402c802c120443c40d010000c0c041108050341e80320004a460300d0850018a40c3e80c210b0b9441e2840d0a080c0303c0c401800048002c403001c1507040c400d030300b00c0e00c80341003000307a000300e80d00242543d010500c2030001508800256030002c140d1000802e07080c00b0910500800012a0880541980100041c0304415454060207401025103c104000da50406040001d944140d0034007030400001c107605006054425030468051082c102000b10b070018813494000c1c0008001c0c403e032140c411403000c0041032030902003801c03500c8950100061902445656524040c04801000d0420807001403202d00c00e4041c03484020103400c0c60050000460190020070441e41d910700c0203102e41042d1134101184140c080505000403040c0d011100d1108400e1a0070002e40170305006000b58842c0745c184a918402114110060008000700b0344810032250b44e1884115000d240404449510070018405800b090400b008900900b500a2078032041d4440442d1248003660300580c08040100d400c2d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 560757760 1250 560756510 560756563
    0x3101d0f0f0606060a170907030c091e050601200a06020301060e011d0906040b0a0510033e030a020c010515010908010b030a020f030a0b0a0f0c0309020907031508 71
    0x601442d80c0c8450101d40360340c01d02d00840360090841d0600d1240c044400490300200e04039420400c400c500665001c01007001c41915200b00c500078103095190142041c0740c8450301c41c03002c802030142074030404060751030081c0984c08d044403070440030305103060359410b018840f802030100341c65000550280031030b600d80c04002d10f40080010640720b51014520004188649800c0666581894041d0080003c481c00b260f0030800780c1c0017841d130360380315407140354400c05c61500000c1880e0140c103c40b990311090781360b0761458920342d03a0100e9562f0440125003c02d135040b03982c0c4c6811443c1c03440038582140c1042c0c001414455200d601508503101601c05401c03100c00e0710040409581d0080062000c1d101c04002800110065030100707503030700e20144000741f04186586010142b61803c2144070308894004a82c00c82c5030401e031407444024072103022420701da1402c0404001e0300d00d0203405508035072076014082e2007460b82c0b0311804a00800d803800300d00301a40c1c5d4001d000034150303d003080b0f0300003a0300c070b1150002d01c0084003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 560759010 1250 560757760 560757763
    0x51905070b0609190e0309040207060c141204170c0d0206040b0610080606070812040c1406092826060a06060c14010213031a1503101d0f0f 61
    0xc0026202d20f501d00d08101c28021401c809002610041d540031421301c0c600300d807a074194010041e0fa81d81107480820785600f44050303608003903c00c0ca0309880342c101391110300032a24124462180d00400020811010400042d60340f05403156221546080d10705003008c103019141082c0262200c940183c4c4040c0901c01800155000b154100e282214a0000d4074050507020b011410005c0c8030078850240800c18006200c1c018040301c072030303041c41d01c000d0400b4038041c640a540d042040c00b6803d1030b0b520329203640780181403110444030303020002401203030010303a100b5058075500003130752018290802074040001c0f44035110070f00f40d5580c0405440750303658140c2442c2451070110300411121030542030040403c01c141d00080d1904d0055001003080c00c190668040b040c0c06441440b600d03d402400b00d10001081c04018a021006a64000c904080c0e0fa280d9510400046504524581d03061b00316041c0c0010b011384a0f031004011641c401c2e0360240000100303100b5801c140e0b000c61585142d2f08900c5c01480321120 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 560760260 1250 560759010 560759033
    0x5070b1e090a170c0c0409050c090709081b011b020121020403110a051503090115060519080f0106030911030d030504050d020a120c0312090804060212031b03060105190507 75
    0x1030a0405402e204198544070340e01c40f03a120f809401b070750391540b40806100041c0110210360001422114545c2800f1600400c070054a00c107411282c0130f40c0e400c00042103000e50b0b020b005a04141d48214081d03a200303543c540c141100d004200d040c07000d80c4400c1c481c0036100016103a20310448010045c0c5451a40c00e103002900543c4c08c000b4843c4158050611080d520010449403159850441303d03266611001400e00502c1c0d5045a2054408400c60002c0c000ba4403000034440740c03000e407241c500d481143d844152003941c0d082d01c0c4404003080c064010f100782c5100342c0c4810300ca540141c0b00340f03a0300726060340480d00b03000c0070b0140c0c007000948078401c100c10320500300704a00c240c0000d48028040f410b402d4070f469000c4000c6030340c04810045046c8071001810f109102242d440c80e0005d10070080c0e0401450b1400140c0d0040c89200007600683c1c0e40400b000300d0910a4038496140c3e031030080e010152091105880b90300050041d030500400307100201c0808025020310303559441c16140c00e81c0c2d8802038100305512a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 560761510 1250 560760260 560760293
    0x31f0320090c0f0f070c120c0b1305040b01030b1e04050108120a051c1407090602030405030303130309080303010b0c011503031b0c081f0c03050705070b1e090a 70
    0x9803072000d02100080c507504888100c2c0c1c0701e210290b19034030b4144031050f240c4120400640303803100940001c5000140c01c00c400704414403d8010b01403065480510741c03050b0140c4050060303806080c900c10016070805070016200c1c580d0514000944501e4000050840083c490700710202d00741205c05029642400d204140c09040780400030301400180d40613100180c4200f001c9101088004150700050110317542010018500792041800300025071540484618811504400081c095680005409001108440603548041c1c050b5145030303529200ba0300c00600e9061b0403410401c498000240c1a8020300207140601200103c60341d0301d13407944a00310b007569140d80c411080549401001c00000e604201c07412040200041402c06450150407c48040ca80640c09011240518007401c07a420f80c2c58000c1c1c82c80e440e0401c82c2000031403c031104c120308890040b03c848011a41c104441c402052010f220b15510001c10045003501c000942580203030001c0903120302c00148d03c10110441085100700341c000100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 560762760 1250 560761510 560761519
    0x60e0603010209030d050d02040504050a05040b10060219080c0303180f0706090611010b04020f0d1b0f050c100c0e01020c0d03121802100f1b020a0b031f0320 69
    0x400000003903c0e215117955900074403030005407a807050003440e0140d80003442c00074010451450403183c07080203020125001c40700d43c08501700040103043c408180405841555009041d011842c203030303103182403d0003a4107944408090000c91a00f820400045202c1c02d0400406408966162040c42c68100c0e000a03180003500011030070b0080c60340c8541c09008a5030706181c502d4901d40884041801403000141302c5800c01d0000402c602e040d0034140090690b8480090300304a1144d401e41808215001c0e0901e010000d0303c000c040c10f140301e12600c00750a034001107000f940d11141786010b0346011078461080150100781c406920400c250380500522500d008250340d1075545043c590790042400002d401440c80701c5507924001030900124484441c461a0701130240e5154910b9100081c0c071180644203102d002070a041003540c42d2420141003080300550291400e11300c9070070811518100d801c0100140000141c0c5140f10307201002c2c010b01c5100a50284659070a5100f07090300d851110502a644640503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 560764010 1250 560762760 560762767
    0x90b060d080d060f050a060f05120a0b0a0e1906050a06031517070306050117071710020d060906060215060d110607030c1403132d0f05031b060a08091c03060e06030102 73
    0xf0309d4008007203030b2505201500b0704000b9529030141c000202500130300c10340c003c0107030030b000f0445503024940180100c140b20440d400c8034500c064502c007554560302425801a02c4400200885802604811500100c007040000903503214000c41e02500e035082039484040d40b014100b003007408154400c1d07034050881210011030058210f5247c0740d642120348a500030580d00317004014404901445041f40040f00c000c1c0943d5581460042040030b0092406a003c3d00d41c03130034400103942c2d03000040c2a80555000040110a9aa80801c01c800014030240940e04024013545840c040d80d80c60004080070342c460344424005050b207003412040c0480a04503461036510400007100b41410305215201100c07050030945000b84030068007a01c0d10540d030301c00c02c03c40144911300480c0f0446081086030a541041d42103490b080303c40300c019021450460585a0444400c0004440c80c2e03200c1c6aa1380d81c802c088008071000e5610342c000c0508000140b0a280d0006031b81c0707440901400380c000784880c1d000701049000350304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 560765260 1250 560764010 560764037
    0xe04060b04050a022a0304230f100906051606020a17010e0c0403080f0f13060201051b0306060903150901020c0f0304421110090b060d080d060f050a06 66
    0x4003101d076012582240903500b170304404107480400c11240908012060100c0d500001d0f0851010801c812a10f40d108030400e4200b0251070501d0390384048400e9280d0b4904003094680705003555140d00c0001c442c4443c0507481c80040109580b40010500c2c001a5910307a02202070402d80b0f042080c2060704101c2c3c0c41c038442c00c107101c8441d4007001610290b90708800915602d00900c940302110344102d6401910a1401082a00d42d4080c00450b4a08641944d0003d002940d2200e00a800405d035020503410800340c1400424407a0410740040d241e903110150403034202c145100001a14408121540304840c0e40008030051342c01401e101c2c44096210000c021418141000040c8548842101c646000b0341911800e00c0d105013000d9082d01d240c0da0a100520003d00d501c0c080046c80038100a4100720544600004840715499a101d00c0f00d80c075812141c0300170780da1500b40800014a0020b1400d03a8511414040d840060312340d0321400c0014108130b0b07280302c0134600d803105210004140c1e6001c8400c0c0b1130340218100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 560766510 1250 560765260 560765287
    0x60f0907030c02030c1e15090a030c060f05040819080633040602060a0506031f0b130e0c09010503161a1204060609050603012007020a0e04060b04050a02 67
    0x190844003908002c1a07010b42520b003203245008480e5850b140340702d010380400c8004413079207888500764403200903281035542c9120a04881001a2204180c0f64031041c0b003400440d204210000c02ca51040d500440c81305540c01b0705100303861082d0b505030342072a00042e107542c8014241c03100e0301c2520494205440c4e075140034000100318914003441408000f0395010021342d084410031200c05c000c8282c226254a079611504020f5680d40b00315800c800c4540f902c40441c006190028511400e481802c0b00c91441c0c4078014080d0014004111a141d0401c902018541910030207000b6600303c400304a00038003015111504014200806910850094109100510900040124440a803807028903075540e00303140211807800500c14400d80e007d030301d41c14000b48020046d0710780000c000c490f42e2200500640d00c542040500300d44583d0b1246400d41c802212100d600340310740c00030300341d031600080891140603680c0c815290307000740440b011030b101a5a91803030b6006d46014822250410a120f20441c00d04031719183c00c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 560767760 1250 560766510 560766529
    0x607050d120c180b1303020a03030503070305070801030809130b060d140f190908040504140412092306070203030a02030c100b0607021e0418171e070503070f0f0605060f 74
    0x210201d40080e1703440c01e10744481007090081d40d02428002d06075a407410010100e070001d40d04240003c0c00c00d0007181c5854412806035050702c2d0071126451501302c03200200304584900c010020100d680b40d0440d40c04603610301e0081d1000720001e44001c038910012a040c0c95180703500800c101e42b10003101040c41100707a02551151005561040b00148403d55810700c10218003650740203e900c80d00344205580810640101d082c000c1e881030094012613900c1020507240c1156a01503510140000c010181410750440d01502c44c007a009041e0700c5c6032100d260042030855010814547c0940e00c0010481c1c2c0080082101c80d010403040d6204001d540e01900c0054154807850310702904c168101100100c041d250b80843e0101520001c100304a8200c005258a420200d03030041540c001c081d2008060603052a44201d8040c1c1000309403121586107070061038090350300051819241d6110900c400710005021007a284034480c081c0d040c10b84104450702d0404e05680c00100002d00071525101c001d40740b51070b4000e15 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 560769010 1250 560767760 560767769
    0x1609091803030e1207020d1119051c030806100c050a060516030605060904020d0213032d0b010905040503040b0a0302032202090712090f060903030c02030a0801140607050d120c18 78
    0x80c0c01e91f51030141001d24000540310407556010116106000b8000c0401c0c41850403200b0075a10260800408641200500c50201e0040c020075400000201c0c1c0340341c000b00d14110074490b418000380c1d408080d12105c1ca01601c0b1401140c099543d5400e0200341c0c01c6a40900260b022503160074400325040c5404a82c480c080c10500600035500414a405c8a40c0b182c0c068645001154014841d500d96a082064a941140c03990b4481d01d081c0e1550404890840d030f1446244a41007201040306900c0c28010700d0091000504c191507a0005000c04241e1341500d400601c0134408564000d40c0700e09115280001e012006000040c2e5480405041f2005841d840492540690542025a4444420500b90000e001241c500038034445100454108010313035940060b80181c025941080340081240c02a070f600d20400d201000400c04803001003005896910300c1d80f80000c005840c0ca820150b075644c910345030440304003005d404146c07062442d140c00e03802442000030341c00d060710780300c0201e030400220b01c3c5268086010707 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 560770260 1250 560769010 560769019
    0x50705100f0f270f090902150c010e0d0806040c09080a0605070212040f140904050703060e0a0606090b010e0901150525030512130305031609091803030e120702 70
    0x80b000c01040c003581e240104041107aa00410580c82007001e2080320b4054007590304544d240d034070007103034004142c450070f00c1d06c3d94040c1c880d0300841010300310804143c04c00d00d00c803191503403202c1d950356000e4401c1c4104e820003201c940792404142040403c100c142c641c484814070411002c10401c01c800c00000404449294000a000403552118075049040000c2d0710014280076500240c0081c24149210b214400c803641420840e03246094a01080400c11058030094560b41c058407003400030500b00c0e4040840b03010a1002c482529040e80d4440b001d07690039511a8081c00d0b0b0310180220103507080165054205011148443e1940c18028104200749441100c83d080010100f620541094014468005580a10105140a100c0380383c003c20715403100071071206014040c03000c9240540000c2003800c649a140d20344609556501130748050020014803040b0410020480c006010015440342c0c02c9800c0035420310440707401c02030030041d0540d0390b140d50b080b01c81d500440d900c455a020141c265410141d040341d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 560771510 1250 560770260 560770277
    0x31b05060313021e09090a050c040911060f04050a0f05090703050906070f090b12100909030e010e060d060f061103210402150a020615031f0506030f0303090307050705100f 75
    0x3c02c00134140c0f050003c183d82041c0220180100302034001030402540c2c0c8a0f404840c2c0403100201403000350b5198410003000d142e4420b0b00c0150528000024200c50051a020f540c1040e540d0000250051031560103070103501e20350385040c003584c100a504660b0004d6542400e000c0b60030508101542e4150040c55601001862944d902c0940d00c00d140c99030003080d0407001c268880320900110385c0e8404e01500c00c2102c004000000080304080c0d4001c0038200d641544036200c2a4290f6801913403030144404505a000350b04008010383c2e03111500c41c3e10f02820058446005460500c45c010704188030040340d04240d64010b000e000d801c00c802c141c98400d00e041ca030004080740d446a2022484080c0f869142348154400800c168031615800503480340700e501c020507508941d00700c44040c59200c50080d0010b15141114140d030f400300e140307540c0007a074211001404480c5070210525000381107800070b81e0f0b06966600002440300600c441004260081c1104580480043c0100e11000c0e0003024124401402d2001d0f01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 560772760 1250 560771510 560771539
    0x80d0c02040e25082401090b041d0c0f15040b0c1e010912110c04090c0b04030c09050a0e0601170a0b0403020309011806020316050c0307031b0506031302 67
    0x1d205800f81c2c1002110019003003c20080d09074009421801450341904ca500a00142000c0c0255811014807158102029903400e002208026104000d44281c0080c0c803120701c501b01410b19403500071100208070240610390201c40410140c8004054154072038202c0090280340740500c2022501103802004045940d0301a40c08014104044006ca003084000d0b001119a0b4400041d0450410b544c0305000048080042e01c0050b98444a1030380d283d900346d80810340344c16140c209644001119030050120001495a0f40c80c1a20f9030341c0143c00442d0103814040c020080d50710140505904052140700910001e8002400140e0340d10051045144011580803407121040d0280702540c1001d40090100b0b0782880d0030300303002e03642c0c1d030154051600040701e1041c1190b50342c030002d048800766800c40d800f035450080c2415400c200c00d200b048064030a401001d030f61030030304da5080020703e0056228000194034007010500500703989410307600c00c5004110400401c5103034101d204444035140e5040faa114000c8012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 560774010 1250 560772760 560772763
    0x60406030b0907030c060203031e04030e10030e0601080a0b040321020301030c050f030a02240d02030108010c1b050d0507080d110d1a10050a1107030318080d0c02040e 73
    0x2a80d00c06015005840c0a01612100204080742920b02403100242c0c969070f601e000b02c0c0d481c4821900c00741940c4807080b0000d55103905000f91500640645810340c11881c0c038a00055600c81c1001c54400444d030f4a1040d140301a8090204a0051001c04080c105030340300390b01d80030b03280c0070014801410040c445940840c0001c961103000203503807508d1b1046407030350384074a0150821a8903000b418403030348040c03c000035640b030300081129440d5030180c002c0d80c0090303611b8034401c1524258508411140c1052000d8440c41109202a50090034904000b103868420004080d00581000403251310100b120701501002c61000611001c40020703d150480d13860105060070945801101d50144840f8105000501109401341c013030f11403500200800c1000c6212640c504106d0000c10340015007115a80d020f10384078038040c4014044280301b1341810310b0107225110034a42402e40540007103000c82c00c0c045401d0070300c50301048110040c1c04014002e240803a52104081d09006484000a20031a2107170400b01d0001e40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 560775260 1250 560774010 560774021
    0x80f0a0b060d080406020105060112201804020d0b12071a0a031d0d0e060412020613030209040b0109050f010b0313050c03070f1a090d0b07090515030703060902040f06080604 76
    0x304000c2c0151120340303070103001f40039000030781e54a030029040d00c15504640f0464800d80404240440458181d002100200481a081070100000000c05203d04042c141c07102d0004048680300800000b82d010141ca0400900e40a2041001c09030380c0000d60034002030350420743c01e040e107e040d08003494440300c110800320003802c91613081d50544030f0350115000003083c0018012990409540318030340e02e20009000d01401d80030f144580303c0074152802c841c2d0050b041200040c2810403007401c1d06403100e07031650081030f500c0c88280c0703044a81360000340041000072070521565400080742c084010181d4500f4907070f01c201703002c00b400d8042e51513040d4141030b0802ca002c0001341c0c51034002400342e84013156180703041408180544101e220040c03800c1d540b4440d40403c2e000f200d88651000b003441d0300c884696200e007140900018070140c02e0048442011820b9694140050401c1604a105541c2e0f841d2400d402820784078207070322291100340180400c0c800303140d184911000f40c03841c40c40d04542681e01d00c03001402925 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 560776510 1250 560775260 560775263
    0x2c0f0a02060d1e23010501050a05090603060a0f0e0103120e090133050a030b030111120903070c0e0711010506060409020705070b070602041d061503040302030c060a060807080f0a0b060d 81
    0x910300003080c0c14221196580c065a10b240c4d0030351102d02da03070721001034074a4803840c0c01d068002141008040b8040c07400794041c580101c009840110015148c0040b142d901206401c600b4800d030b4050010020000301020030a4222410b01c0e100010390602000710311086c4c07040c040c400c00048081040040759820000c82c603080e140440c00b8104410140750090210b40c82100020700107030812028029500f414003c4c4400040d51051a43c90030103212011035648001514811b061f0004012400100d8200c07001c4402611007010184580c4c1094100540019085c01c0e4140b00759040c50100250b81c0e454906540884002c0440540c1c1c1d581180350642c02c3c1582e80d0006007209402181c103034203202c01a400340c01074032981c902800a8840c10302071905080d808440c0968045808a45402904e4410b400f95801c28440e004507824507150065181c1080821150002d4603a81c0f01810404000d04110307240060030700c00c015100448000707603d1f546800d2a01d03006815007542c20042403070390b107424505030501c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 560777760 1250 560776510 560776571
    0x1c0c0f030807090509160309050a0b01030303020d14070f0806121507081f060c0c090f1a010309020d0209150a0602060406110405010c02040506042c0f0a02060d 70
    0x1084a850041e15180c010340d4018005035140d4404186804c1010f900390165400383c18548040c256044214013508038000119601e0052180f8480068507030f008640c0070f140300341c9016031151241102c240840340404c3c480c8400c00c0840c0180914242c1060345000501414640203c5590b9002c0201e07160740368401221480d445a140001c60355040b0a0402e03008001c20b0b9140481511130241800e0058050f5481e0400d0001c0468204038290040303001c4132071640300e2200c51103941d40c0c2d8648007080b600b10000d03149426858584480e20000d0f42c1c1c500350400d2009007420000d055058006c034a17a202a210001d002d0500880451000300340144581011513000b8803048009840311002500c645094030202c600d1418000c6480c54800403405890580300107075121004079456401704009440f0141082360010b035241c3c02c094644082030008205454481100407130418000120307490b140b0994040c5c6900d41041d96503000503561007089541d02502440086a2910740d944c00043e189440044d28800c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 560779010 1250 560777760 560777783
    0x1819020f0711150f03010e0c0304200d12030c020c10020c04090606050904050d1704030509061e130303090905011d090c03031602011701030b01062304080304261c0c 72
    0x411300c1070065040c2c5665a45001d12903c52809482c0240400e481c000d1503402d000641c007400200a00800d00701c00c4c0300400e11455000c00da01c40c640c140c480d000401000030b8a5030740f0340000507010031141c4140d120545050090182140e8000d40768491054268869900c4803440c10a100450708000050302000b014400700d4105480c15603a140000074252010076000e08100c40d0240280781005d118a406894040c0307841e03001010003061360310042002012a41c005800d031903d00e602e0707002e800002602e641980810f404c605016250443c1c5500c00c144041c01c100060112500849003100107201302c550302d80b01501c1c1c1000107801c22114503441c030740600c40030403a0301032070f617820060b803130031078001c0e21250740c401c1d0800c041c031106240c01d00000d8222902c003401000000d01c66002030791024800007900c10203011944513692507078820b500c19072030303980041000d000ea44403001d408641c0b60b128000c2001401c2ca00c011240e2200142403500e81c210301440d800341100f50042d003980074240d031301940c010355 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 560780260 1250 560779010 560779027
    0x20702130c090b1201030b130c0314012004060f270515090306060910050909010203013003350906060d0f020f0a03021819020f071115 59
    0x40c074411280340001401c107034001908030005021290b1104a25900d600161309640f60109051006841c8281c40e951641d030200102c0c0d11038144074060351040302c07146e1003031070040c03661825145828040049a501c0404480407185203004176800c84840d030520311400341c00356106407000c04140f94021a42c1404076821364801000901e0303402a03980844444901000d0403109c0441e40c064a81031541592184001c941036107000d00c80c02d80d2001d241c000007041c190300c80e4041340c503003401510112400e80d0084010300c82404070010703403541a031071140c402c408121004000845011400b001506018a6281800140d82004500e4000b0051010a14114148211140184c1500b05d406060764050407011848904c5c008007500c454617044010314050905603000c014200000891841c0c0c45040c00800000507290a100665418403181103082145080f580c003142840d2411113030b42d1424410800d07031003a034180d24246c030b8042d038000c0601d1051502d1403001c030321400102d0424154008000c0399041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 560781510 1250 560780260 560780299
    0x60c10020705120712110f1002030406061d010306090303140c07030801050102060c0f181207030606060203160305030622020c16030c0e0702031215030d170703020c01020702 76
    0x100e214030a40407a004002c0031a95480b850090b99001084018081c0c0c58080041c404d50b000c2c0700d4aa070316020b0707554440644400501e85823031350081e2050903802008010030700c0309621812000300413401641c540701440c11010745c006031050100521281d5a4004c4406152080c0d014a01400e040e1308145818240368480c0d0800390010030741100000c403003100100b100e510215515008002d00c00d00d43e81000011aa45100c90300031109115408055050001c0c040d500c8002c10a0450040300c05030034014158100201660f04580001c0295401046141001d002c00a200038143d60189801074a9445510003e000390085850303a1a001c1c10a140400d161a243d50041046a4401c0200d8001072545005e000d481d50183c130001d446500c0000003001501a010304559000c12070f841074a10707003940c010707003445640002e0302d001102c0c0b5483c0708042d117a410100841100c850460400602000f400c124444450200a029900300340c0c020544118800c000d4060b127001641c0289031100c4040c0700a10380c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 560782760 1250 560781510 560781517
    0x10050c0109152406030b0402090d0602030f09190312180605190510030f03120e0607030605040504050c012708030a030b0a21020a120b010501030c0e01080411060c1002 73
    0x1a0351075854103e29004004030078260040301c0300e61000600e03034075107403180c10340040c0707100c44a041d0060380030807000c145c030394580c103c95540510982c80142c032400d10080e05007030424024420030700c03076008000005920052180480009034140f50a00840381381d400140b02400103580c11098400704001100100032254200d20311425801c0c2c880011410580c1d5a581910001c0c4d40728031800d0901402030010600c0c00742c05e084114003c0c10031640500c9030200240032625024581d0707601d034000400744140580d00d07000340c0f00107200480b0300f8800b604054031100d0f21004a541e125041c01180c8000000c000c0a0380c400e4540c4588140c0c80000940d039130440f080e2654442c095210000346001c00b0500145004070000c8142c402000302066200c80d02c9040c0d0030038400c0c00b04140d034005101c1d480012851107003400c17800d0b25881644e0745012949490000b40584420707210100c02d102c0c05030352034000d83e648030f40f01a900540003aa018208100c2c0004561148108440901ea50080019200102c2d0041c4c004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 560784010 1250 560782760 560782793
    0x2210109150b01090501121d121309050411040f23060a05030a17030705190e01030507110a11040b0a061121030c0c120301060207050a0503010603030e10050c0109 71
    0x1e00c4980003040044132592602d0041502140e2104590701d600300450348902c01040c403140c80718224096100640d483c0000c020b000320707480c030000070b0807191011050303640000400c502c190601c01810165100590707a000400c1c4c0034041d5507646428440d0051503080700203407a080a5030412914240d40b00700e1000003084507440d0140b510480300065a00300040c000b1404ca401179898031030300d08024001c111550000c2c00c01810480140804c3c5c0f40c01d124801114504d010689400120200a80c0098241d4a004001d141400195405e01464a03400308010800300e078007540c10720000d55410001001003140d0341c9103503000504c120780850342c47c3d00890803044405510701119174010940c8500581d25601c0c11190020880500114401841e088043c0003410040c0040d00e40e070550014007030300c464000341e2007000180c0c4800401c010034109080c08401803c410f078024801035043d41c40c042d20220702101c1381d50241c1040021100000d100f401a110a030040748001e101070b823850304105125141c0c0307015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 560785260 1250 560784010 560784053
    0x1050f0a14030a02131a030c1e03070c03021c09090f06030b0a1e050606040e040302030d0e010c03110408120a170103150b0306060109030b0703060b0d0903180b0702210109 75
    0x3000c185440b0650031400c203c800710040c0f602d1070f9a04036003104160449d00950190b84481441c2c124081e01402c051886142a0740d41e0043c81e0502d41070080c68810301d1140c04d0441c0da8290420041640e01200340c1058840003840844c48140c0d8a00d028020502a403000d003201c4034007000d010120b5072942140081444411800c9883c42c10f12401e0350496034140ca1072a4007010820003000420814101103611034002e0045c0ea0800305607148190694900d0903000d4074503599403218000b183e4042c030940c0a00d10141003110304203420440c00d82c1e81c90f081041c64007440395010411519880c810b007001da030710055035145101d50756582d2600303071601c2010241c0a00313044d00f80000d1240234100010741314451032050b035030500310614603181c189000b50040c102104140c3c49802c0800e400451000410b12141e01e001d0000d6094024100207011086c004652065203d00708010400c651010050311600b5804075039075030300030481400c090801001c80485020550809840005011950b444024500380c4c004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 560786510 1250 560785260 560785297
    0x20310090516090501081e0403090e040f05160b07060e0106080d030b04050106110d21091b05030307050303310b07090e06010f0305040f021f02070b0901050f0a14030a02 74
    0x6540c003440032507500047e01240364006280d24011031a1a800038040e00700217901c2a01c4076900700300900c0031a0300b5500340d01d070081480100401040101180520743d160154002c0c00c01e020b40c2d08900c1444000350089445041c8124420030079400580101a00030484201044054018000d4020550114400c1c2d10340800044c0c018020160342039042c00d0f08001d0100c0c8851210280c81ca81d4a01c00d80012809010600f10380d5101c1c14442c0ba619280a503080315442000c0500590444103940c1003031303009030030600c00c40c40040e40000613641c0240001844101c506c040c0348032020100e651f40b2400b205032018400f060140000d4170006030244515541f034680980e114440300d800c015007a00c0050000344820350200b07420b40f003070b48800d4009104409038105201c1035000a172003c1c1d010403000031040c0c00300315030702d2400b50100203c00c014100c40321102d06003400c25001800900403051582c0c820b0300e0014480d20304c2482145141d80560300c4080003916030800180b4000250840340540d8012004c06 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 560787760 1250 560786510 560786519
    0x30f120e060708130506041202040b120c0915030607030203060f040c0503070c110d0302011b080907060516050601060522031203110d050a0b090a0c080a02031009051609 74
    0x50a00044888000c0c1c607251405410f9642c41c0615030180300705540903001003c001c00c141c4c1c1e0741c200500040645541d500110191401000b04861500c0c0440e841021130003c46040801c0c081a8100020030403210740d40c5c01d03607540c4076800407602281203490303240c015282000351140d0598060740c01903c0a445000e4100c041c042400308684402c005800810014000501180c0c80384500d0104948120008180301000b03801041a40003068000c0380980d440c3c010095003446005490410390340710780b400e07a980f410f0081086840d04d0142c0907107000c01500084501d0007540603c0210751803035000c070840f14a90380d603000c014060381002c114200314004450303483c17a1864a8220400990350450450400c1da1050402a0001c008402080708400000e1160381c03070441d201e10072a03128030200000455919143d0040080c804070040c4845481032403c0d817200103907030780720300703030380e50100f56001c0051b501c0d25043e5180e08260090760003020002c2c100001c203d1941c600c03076a00504518540c83d218501501c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 560789010 1250 560787760 560787767
    0xf0a0f061802010816030e010f020415080c04030618020925050403030813020d1a2d06090402121209030d1106070309020406030c033509010806040e07030f12 69
    0x7001c081d00042c02c800200d001c404010602c0322800c2c025040004401580d070f44038a09480b001c2d0b041500d40ca6000c1000c00c130400f01c2242080c4503031510f14004031185401e556000c41d034005c1c1d000c080c0119952310600c19803000019540148590001d090354064940a20b4001140e0f0003003100c150200515240a00711a010b002650240ea5040c1c989042d070b9512404244019800c20005036801034900d440c0c0c01c0440c0c1080d104405050342c92942504518140c1d0000291000701c034004010181c0321400001c0b40345840380b005401c0382081f504a40700c0d4a8500010701d44945440104c001406a500751a0003081c520004088401c000d03426600303429040c160645941103c02c0d694040d40d00b2640002d15154482d60098145600c010000170315182c482d100c504ca588495002120b592003c00d208125510641d000d0000280d0081000b07202941c40b000340309402d01541c0040c605100e502004030704240d07699080300902d0b41150084a040556905020100b10305200701506e80120300364034100201e21 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 560790260 1250 560789010 560789051
    0x2010209101124010f0f050a06050706141e0c03070801051002010e01140118090c120c030203060c0304150b0d1205090a2c01050a170f0a0f06 62
    0xc010061100c04500c00d1094448064215602c1064000d44185890800181000700c1034103584a4145500d0340c10209500911034043d000400c07040c18668040119544885a5909a8405191294442c000e6281803006040785d1800300c04c2102c1c2d03032010003441c480801500c4880c0003022200314102c0d100e0064041d114071054071000002600400148041e013845071000d200c06d045880000f440c1d2144880c820700311038140e0700f0b090300c80206900405c9600065a50b03695840200c00082010100e2556981c0030f80403144961403110929007000003e01071140c1000008640143c19181c8628055403110a02d40c070894040b642038003000d1461843d007182e403007103143c0558050040f111140c0c1c01c0c0c403181c154004100044040000400101c03a02d600c40841c420700a110007a4028900382c0358000d8032010030208500e0140c64415800100302c2941d1b0445481c04462480b0560407403040c030080c02e0f82c02d001018100c1c1400d0f01c1421807a004020300c0100395000c9600035001003001c4c04949550407a00320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 560791366 1106 560790260 560790277
    0x50325061401031110022104120b041e05060c07080c0a110928020f04030804060e030c0406060c0b07021e03030411030703030903030e0d02090903030a0606020102 71
    0x101c41c0c00315209026040b9034407501100b180f10001d542e4030741240c00c031f00703042c1c5010040001c03602c0302c078202d0300030340359951441e48030322081d080089128900b52004c60f0800300d40010303a000024a01544259581d025029101e0741e10b4207400000c55400c9a001079070001d104103c51001c08074104000007049206640e07494100c104103041003080c40d0000e0410015140701c400d10303180341030390f44001c00c0007088040d00180c50321038500d03005c0400d00130340d080104138010004001c62103076006908600244411401c540c0c003881c4c5002404242da50f14480d09010812108040d40007440b4110001e0b441000c610403a100c0886810300208003500500d000402030b00004148070500018074221952800d003900241903203481e503030b4000c00a90740c1d81300140400c0203410010030705a032603488200c901900102031811508000792826141e070700549004801c90b113814000644c6c0382c0180203590a0a = true := by decide +kernel

theorem cover : BRFrame.Cov 560611510 560791366 := by
  have h0 := BRFrame.cov_init 560611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 560611510 ≤ n) (h2 : n < 560791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
