-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1033
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:55:57.559669+00:00
-- url     : https://prove2.me/submissions/caeeb0b6-4be0-410f-92c6-ab1b83994f75

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 185611510 ≤ n < 185791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 185612760 1250 185611510 185611549
    0x5121009030c02040b09041104050a09050106031a0915130f02040207060902090108010c020a11120d020619050402010c020103110405060706060f1e0311030a0b010e0601081005030c010806 82
    0x250040d0070000d01c11400030302c050b40038070700d80072116095082220100d0f10450300200c4d4048007480203424480204002000012401da41e040d01000040080c06610011130090140191491008816018988010700f1280342584062082064031a800d481c1c0703684048400d01d8100d07200340794203248108810715070000f5441880000c60504000d502d80c0031700881802580c105040c1c1e80c0f0f44514600300c40c0828006405a0b010280f03c000040160100d404464405800745006409034103405140508103030b4501d0241e04140100252628251300d002c280503000403091090b41001e0f00046d0a10601c0d520103410941c95000140c10628120200e5000700806001d003552101607040070001400e0900840718000c420040024108004090f10007441e04200d01c6c059140b40355640c0c440f04c940c0b8035040d0507050f0048440600118140b207521038000c0000181d00b144624100b000141007040081503a01140e0410700c0c240495140058a01000402820003413480d465040018058800c50583c00ca0700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 185614010 1250 185612760 185612771
    0x20102120c16080d0c030c300b04020a05070b07020114010e090708120403020103050a2705070b130608071809021b10150e04050d0503070c0221190804051210 69
    0x40d82c855000c2c241c10101640d0070002d44000180c01c49503180101a1b07603c1c1382c00a04e140b80c860b44000e21003d23112002c007000000748280d8500116090740c000c58130460200c0e01c04140ca100744059008400d07845109480208106801c8240311094424103001c4e085000414000141c1c0b100c504020640107000c1c1901203c2e100301000c944401c0c281d1150200700e00007404e06021544030350050040711048104004041400d604101e03083d000d260311350a094605114411001405552060081c612400417245145101c1c0c10403c0c06051140701401c05000c2004403180d421139814143c0090007550000e00f00941e58142405508425240041c024440b502414111322403500b030f5075101804200b1000000d003101307595245000c5004038125800f410035003100c101011658880c03001160b0164813800d10b503c4142e441e8001ca1200d40030300f100146030445003170440d078440400b0011090440c4811a10100c0c12800d0b0b41c81c6034490155100b15401020048020341c00500d0501a41a10702c83e4503500300070b07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 185615260 1250 185614010 185614027
    0x20a051e0c120301170712120207030605010e15010c0209040201051e0408160b0301080307020105090a0b030910111c051314071401050c0d0c0606120b04020f01020102120c1608 77
    0x4a90080c1718101d4031783c0c001d0040c04000038011410004858400940c00c1620010362101c01c0724003003148913101140a01c01010000074164800e41d40a40440c1c4030501062415440701d011400901d2080d41c14031841a20701c400580d203491006604c0340d8217107001364481c1446407000030368801c40c117a10383c513140c0f02040224039240001844001a0828a00c004080342d030356039541c40c1440280911911900b041103c00c0c05940110010b107009100604010102552601c0d075001c3e0782c01c00d80d0110240d81103054400760400086c090300840390f0200d01c0e018030303080001800160340d0f0036076461004c40e181c980f00004d042c1101d10788104080360f0021f541a40d400c904201c455240c40c00c602034001c41c58282452950070754461001ea42c9140c40a01c0206404e150414040e25203800c016022214540c440e030001c51103c04450a410229103c6c418130021404e16104219401c20a04800ca0441e131043c821a000d2910061a01d80c00181d008142995080c84142c2d01d00d080e40c070850040c00c800070000f07131080c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 185616510 1250 185615260 185615293
    0x80d09031701090618020c030405042f0301060c0b060609040509030307180e07031d0709020901030b0618011b1e0203102903010b040f020307080901020a051e0c 70
    0x10407a4802030300e030010740e0b01c0e81c0c41107049890038050311080030250801c1d0465500b095005200c0d20324018122410190b5400000e8281d4090702c04138189413200c0080074001c0c1601c1e0111159242c00480d02038219030420301c0090400c203030b1400c05000300c0307503c0340811410746641d0202c6031202c0c0e0150090096103011240301390381c2e610a881e60750000d8400110500d403040c24400c1d01065810820b01c100150b11140d0084015111a25000c0b200309c55511801200d4641040303000300401c201c42000d41c031400164005002c95007400403440c00307200104041805035502c0c030400c40b2401001d00300344840d01381d01c10351284500b221040090540c1050b01002031941c2901c070790b02103028402c600710380707040011107000001d403150011895081c509520251604904a0018022405c809800002d040700c03e140018160340d0450040216207500000f803200c150b81c0420344030f902102c000029807805c5414a4001c0c0503116007484401c92061481407407442c181005e0840704605050011a514001000900c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 185617760 1250 185616510 185616527
    0x61c1208090d02010603171809040c060e040204080705061e040905010311010f09051c24111801140403050f0c011115130305121303021212060409080d0903 68
    0x281d00e203201c0c00e20003281c4544140510801e807035002c00c846225030544818200941c004040c0f87c0c901c42c00c03140b11040191100014903210354051320f1902d165500e800e1000d441c040e07900c1d4076140698010002446007200c00581e500448200b83d50342d07035491f1a610380f1648015002c02a440b160b110009000405a6a40d04003a0590703000308401d9040c030100c2001500da61841c03456240101d01a03a070104102d1600203294095442051809c0d1008955a0ba81d02c0710160070b1148601100b0340c044908010a05034440c170480c8800d80c2c100b00345000403401042146000c0d042d0501c0c1045614801104039020002c03e440080d50b1000c02c072000c1244210b060ba403500f9a0650040c0000c0c0c2d00000c40307105040000e91400898810407403008241c64070208038601c14580b080c1917081c403508001207000c0030001c5c22000e12070408041c0c04100f5040a140003418001c0240003002c00708000d00904604460058440d42c01000449000401001c0d51031718030614001d40700d9100c1280c0c41c0c10400030034581c100d41007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 185619010 1250 185617760 185617771
    0x703081809100e0601050414120102160f050d0c020a09020c011509020c160506090618030d0f02060c1315030f050c1c090507120c0909030e0111070509061c1208 70
    0x3280f00c0350b488100440741402144035060048400b00803440c4242440404001c04031150b070005440c1041e200b0548001c01d4509004440d141ca07041428400c3c0700c400c0c480d04000011a107400d2134455002c2c2c000908111840c004c0b400d2060340010b1540c03849100b5481001504807c0444171640d0b41e5510040009421580d41441c0380d010398003210440a0044100e0026150700400c01810708a2520901c400782d0400c2080840070f00704649840300568040140810740101e0340c0c5e81303c295000d4404001d040c004090310780310898609100091079060312404080036154000c0011000c0c0010090403005080005c88500415140509010705803949000134080e1420018510f0031610302d00100b00200d580442002e03080c1d4008483c248070b120028500c9640c42401460060411621503075620b041311b124840440c04616005291401ca50b0441e034001e01d01040207018000702880c000101c0e43d078035002032146205105543d00b80180b00a4112003440058100c550080b80064004000e813441030162071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 185620260 1250 185619010 185619029
    0x20322240807210e122b020a020c2808010c020106080705150a110d0c020112050f0f06210709140103080403110a03120e0405090f070308180910 63
    0x580481c0580440910700800090008160485141030b100411185581d010a8003840c1d5004071401105c90241c100d201d50328007902c095000448100c0241c50398000c25030300c8640140302c80c3d4010341d0080b91031181510f0030307200e15507943c0c0312002e185e8204448090740d24003400305034004142c4100544c00030740407080d41c1e0000c104813a212048565205014820641d01c001100b00704101ca0013140060030400358079003012803540d159140e0b500c1c1840e25000d240030008414180d0344003507682c81031401600e142101c80c01c01c4582003402d00c9110040c801007010301000e1205010070300503240c100301c0d1103003007000808480c1032842c4c61460780d44440840c866102e040e03080000440c4076041394400b0360b0483c0e81c401c07030240c5003030b10b180c0d244203118a0b41d40b15a0390026000d400080810640c0908030f03880c01c40380d511500c2480d41d2900704012944050048041d55100b810289001c900021b401400d0302e0300030718070944603498444c00442c101c2c14024659040b161a40034401c1c032851080c4030302c094406070310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 185621510 1250 185620260 185620277
    0x19050106080a022107080a120305060103180b0402060d23100f060c06060306020c06040b24090901090609081e160f02010207080111180f0102032224 65
    0x880a40d40c070b4820740041d6021821100019030259488102c01c00c1410103c103031201c41c0d68400341141032a142c0c0a050340d003003100c404860002a418890345600100034201045516100215180c1c0c015100e0002001203041ca00440c1c155078482d0140c510040d0700350000d1080100e05509090641646102ca9000035840e1010034804d42030400c5800680c1c201d04841d00704140341c01401c81e90001004030a8500380da6400021010601d940001d0098200004c01001346003010b10b4000d0704c8140c000c110f018002e99541c00701c14002800c0c1e02c06500024200e4800440341ca401039010700400c0c0c80743c130040c5424902082ca004000050b0b01500300c44d028844401300d41501d07900c0f008030720300c50303102c0c2c010802c0551104100003c400d1110340102c14010320440d503000c2d4881b01881e085505849100e8451107010400e8509500e41c24032165040d142920202401031030440045d41d43d0080c1d007901000c0100003899050300c8244000c003140241080d160320341c2d10030050308801610041e8040700100040e42203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 185622760 1250 185621510 185621519
    0xc03022b02120304020f09040f062a0212040b0901030f090506041e0c05010f030f0e07080c0f0306010905040503070c0605030a060806060901060521010306020c150705030c030c0c19050106 82
    0x18019079201342d80103004008030304c03105010000c0081d0010000c0343c0c20240040304070081104c91040c8000c032950f211039103041c6980d103c0c00c60f02c00700c04d80361805c04550000000b0b1b65040010800c0d14100c0700034402103521800c2c02c10058018211035001005a14036001400040c804002421b80c047c0d03010301052001e0500f8102d0705009140c201001501d42040400e0402181d48a80c40c001603440003464005052800182d110041d5040c2c2103000e207066000000503c500481803150b6240544201d64039061820500d01117030702c5d84014403032062030301e50f82c800050034400140115000700307900002501c04240c13030302805401900b068903050340107403a00c500030541075400280309024000051100c0f41e11781c6010000c0710360340e1003104811403030242c03891034100324208407001901035441200c01685035020054618a07004421a03400c4041c0da4407014050f495810900b105e40180a40410542d0395803100d02c0340750359200b07220105e0300c940300d82c0c1d0006141d200d85110042c0160f00c41c0c070080c003443e9942c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 185624010 1250 185622760 185622793
    0xd02071110180b0a0507020d0501060810230903070215130504050402031e0c040606020705041b09060c080f070305030406062309090106080d0f020105070212040302010c03022b02 78
    0x1484001e007280c040302032007405030030008400740c1300043c01842c0c030b02d150184c6503001c2591001071010895884c1c0d11654103010014061101100346103442c6010008109842102c40200000380144240c4414400100341034550a0044400d80d540140c400603004001c2003684c481c687c4a1420307124802c4010102003501c1c68140509401035400a004040803541ca5581c00e50b1009607155042151042c89001032031500d46006210041103e50050301005290a0034401500c1690449a443e00a412104c2c0c0800340c01241c1001074031111f2a0020020082c0d280144540c842c06a10317058081010401c0420154468001e5100c4d9104a40c10b201003a030b0b03800d00c0c0c1c011210b600300c1006c0e0600c001409682ea41040900e49511410b424000b18103241d41d81c28150400c80312940c400001010400701e1000940c09000d1141c00c0100341c40100102d000c2c00003141ca150040c2e0200904016481c0d011105151082207a00c941c104202d4143c09440c80d15265640d10b40c2c5d4101249015005050013000607118 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 185625260 1250 185624010 185624027
    0x518070501141206012304030515040201090b03180105131202010903050d0f021b060412020d090b0f09090108010618060b0d1e09030203040509060906130e01020d02071110 75
    0x1c2c025401c9040c4544114001e036010002800300b4100058240440a170113620688401d01d01c0d045042d0756510f80c10760078183d0429000c640c41d14104585882031000503607109800034100e940340e0354925184d4903048000a1807001c064400082e40d0700704410b02211840b0405280c100904c03891070780c42c1c4500443d0040c0c2c20b0b41c003c4140540071030b01c240000c11900c00b01d600042d81c41d00310290014034284090342440041c4580b59280140307030b44158100400c10140003d100514420b90006126451401800500780e82d2103000d89078285002045229040fa180d2040e604440001010003c0b1136844a55181c000c200c640301d400a02c0d810440202100c44041c0724041c00d49024400e41c0e454190105080e0000d4041c4e080300c0030307c681e510700e64608442c4040c807a050440d8801e0340038590325850002040380c081d0014000720710486c03500b014044a81c4d183ca030480001040410046000001004014028003503101d248a0003400041d003001040680307840c510002504492564004080c41d1084a6620 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 185626510 1250 185625260 185625287
    0x20d0527060f070c06091214040f03020d020d061a0109060e0d020f031f0605100306120b060a1503021314100e0d0609260c0d18090518070501 62
    0x20000004148500ca42c0c82c81c03070750700241c181040008001c5a41d1307510212002d40b001035603000420a0805445d6602071102000d542c0760303180c11401c081c2000007540705105a480024407444c400c2c4400001c549500554890058104508000801d160381021141c603c044210a0008070b9200f00481d00b1802142036454200d000b5240030845100366007480b803021801d40f00d0300d503d440781c9056210200080301450741131031401f03007001ca000342c549000d1084071441905034009042c00c0003024410018280142681141c200005403007030f44480380401c04406050b00114201103078034008150054060b0001d19410400081d00301c0394a9543d0190f05103416540c1920b6840032075200319000340b51050815100f4008000c0c55800e6030069680c1c0c04c4c0407141c0415007110304500d0340c10f604a80c4150725803511803151103944020720700751a0200d40b5498040034203000083c0200340007500401c024604000d030207044401010011814560900868022040858100d6204412020407554450490000d010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 185627760 1250 185626510 185626513
    0x1107120f08150603040602070b010b0706061d04060b0a051e01081f03080a030e070f08010c0c020a18110c070317090109030303020a030b0d06050703060b030c030604020319020d0527 79
    0x50182c10846641c0c0060030944d40c5d903800b0702088000c11240c005060080000d110740c940d542c0c0c000d08d800c105035510341d402011350341d96103a51021941031103003e142d0b1043c0d20100c009100e030200c90010303078007a0384c80d00440d40205001030044100c54114440200c0340500740c0300c403915076139821b08001c0c0d00e00b203400c03858410781c0300d80b041080001c1603000030b00713003440d401d04000c115901c041c50005c0c0b400034103034008594031242c281e04000920742071081c01040001c51500103203c14564001c1000ca400341d1003224084513084802101241495000080c8208180e52280d5107403410340c0020354400c07a6002c103448000c84042c013400201c030808103e4000b1201a1030701c01c40d0619548041c3d0081d0800000c0d2410305403250041c801c2983c0b08a08400d06600c02c0c0400035540c109504018221829500b1195042c1020428408918003c40076682c0c08541120050307070341c0d40d0ba81c0264003428401007a1483c4c1f9030001c40c0c4008140240c2e04010322448041742a2500f800041c0014000305901581c1c14055 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 185629010 1250 185627760 185627791
    0x212102705030702100c0501050f0f010b0c060621010f0218180a15170d120b06090d050a0b0a0207111503060409030509120303010f050402070b13061107120f08 70
    0x609045c005e120100760a420010350115035615a40d0035950100c1d20700340742148030810003440c5000301843c14003508c8189034040c20103078551805a6a210013034009413203161480401e540f06818410710560402044009016500140c510705000e5042500071551207119a45408154203160b22142040c42300d5588081503030302c03054021402481c5118201c20402002c2c0804550311000c2d4808010b0300b100140206030a0f240c0000c0113105804000391100d04038207043c5e1040c1e145e900c9a05582a000003220340042c440d00340d1034402d25092555400604070f1443c10b040081e1224640d0242802c0e9000322124080100442d0401203813030b01c607000c11382c1512810710104400c6c0c02c140c1c1c805808a4400d00f00103162580541c002070b5904c00d000000809030340000300600500c050b00030307240010142960194148111903840c041c40003401481102c003400c0e41c0b84000c0500406030410454a00034810300b9a0f03070f00180c00c000d91807a20b602c10341c0300802c50103540c4102c9140304242e40d91080f0165210101c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 185630260 1250 185629010 185629013
    0x2030c04030807020301060b0a0c050f0601060903140313030507080d03020405090103140c041b020708030c06181207030801081b09011203020f010606030912110705010c02121027050307 81
    0xb9550801c0d40d0a0303806642e140c40100e41c00030850014414040542c80301480c900851a01624001200c6801803c9800c26801002074a170891101425a0b501c0000f00d81c0341c4000c1190289140100460703180701e200d200100100703100c00441d200d400e41d6019000d680880c1c4090000790164400c41c41803a03040600c0c0c1b0010008214000b8600c0111191030703040d0b13180004660001350550f2030580d10145a40d034142901c0e104560100a004000c2250740050360400c071407c2c05040c5c6441009100c80f0b4159400302c1d01c103082c0201400300101c040c0c59150b90310784900007810000c106003402d00502c1182c1c41184c04010840c0c04c4030f0b010522821004003940d4a980c241101c5560720307a038040b8101d0075841402e41c5116030312020301802000c0c02060b900080c18540504152140c0c10740341026005010803249448081030010030340030300741c7d1020300b01406c0001452020501080c424002c030a903500411003240d01400840d0400c6240c0b60058000c030f003100b0303503400c2d042c0c0c21210a844024010b500030050b01c1c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 185631510 1250 185630260 185630273
    0x207060f0f05120705030108010c020a050c061605060106090906080606151e0c010903080615040509190c03051f061b0204020c0a0803250c0f2306061302030c0403 71
    0x5400038140e1508a00b000b580c0f1004001a000949106000c82d0001c801845030013401d01c614994904903100800242c40300d501c460f929901050146402880001a840c01440c40800000ba0031548481190003560790384030001c1c000c00c218021303400c15500700440040d2010000844a00035000280758460040c18600301c40c01d581d2100c51204140c101c41007840380d6022031440900905907030007001080b4001c42e464020101500100740c241301d4540b80030341d40c27004100181502c0c107951096686502c6c5032a4861010401c2c07100030880260207040000240c400c45e0b041e046540210350481190001e0b07405015982452401e502500c0700040d183c60f022212014079007840d000260026100603d00f6591552440c10401c10b8201600e00940001c2400050700010002c1c8070440711440d240805103456200050251086c0c52016041c620000c00040500c0fa185008018110b8010000100c407201002000d803510003c40340c00744210701003200610310b90418002c581c440d88007180250716150641ea60745 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 185632760 1250 185631510 185631527
    0x5030f10090c05120a0504032a020d11010e030304180b0a09091b120c0501120f02030907030b0906090c09090703020319060e0c0a0b0c0a020301060e01060f0207060f 72
    0x1026921848080010405034910401107850110707a140c5660740113000e449030a80c00041c03c0282d006140c0301c20031001c658408040040d041090400400340103403454070440e08074803100f001c5c1d03105142c42c0d941c0b01000b03d482c0f10b5102c41f100031b03250b8081090350501055124061361245c1000200c80a4004074a40050f03841356000300c01c000c21000c500c644419014045400b203c02c101c1d04400310b40c103100420380c05208e81c800181994891001303c42031075501c101000e001c40c450b10b4140885003a8018440445030014101401301358070441d00c924003904955550704c0284000d8411030205004281018000300d16144500700310401492a9140c00d400c0c0700d41840d009180c1d031001c0c054078101100581d002d02608420341000042040e00c1546420527404941e2110b260910380e5001c7c590300c641c1c1e030b103c900683c0e0840f262808095101c01541d09558184460683c00a41c103510384140841c80006611415050307459696401200f4030504500faa940c02850184201081032401581a43c0d446600d84 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 185634010 1250 185632760 185632771
    0x5060a031b0503180727110a02010e06010b07020f010e030a0204090b0703111201030f0507030f050106051c0507180f06030506041110170a020403050105100320090402060c01060b070b09070603060605030f 89
    0x3151f200602030f050482d00060807440060751103c440003160300381001101c0c0540402c540c500d1920318241c1c00104160200e6803540d040c060b0314048415590f50611011604980290061015603502e26103040c04010440d480c00c082482d00c68403410045d000001c0c1c0300440e14880104400e6400c58031080c0a64684001c11034a510a4507008000902c1509503642900d11030703000420b010b03041c10b041100150079030390603c645034a890544000315000164403012110500040e60f200ca4005001002810050001110709410b1460000030800c0c000703801441070f80103426980110032288100b000000c26585000300041000c1c1c90001918101071882e41c020100c0800103152a075030b42d440e1802d541e4121004203055032581010000d1010003208941480c2d00b41c0303040704502e80c4000000361403c50150004e03010b000041505d040d0070900350312420251045458050300c03101d4600e800c020070241154a07400e04d0013409000140c02c0d010b409068140c44031a2140d5003959529100205000d100911 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 185635260 1250 185634010 185634089
    0x207060f0f2028020102030907050d0f0b181905010b04090803010306050601020307060c02010e0609060702100902150327210313021005041e050a05060a031b05031807 73
    0x201c40c0f1440407290902c0001c0300e43c0000d6107a180c105e0350107042c58100e60115005060b100e03a800001070501c2d5018030890350000e5130445a844144500310340342075204441100d80b09004180400314158031a00c0c19140c4214000c0c002c2d06110030a03c01034072501c00005060f0302c02800103200249181e00710b50351000b010320440e41005510b840c1c19050740c00d0440540c015035940d2040d000004001d0013100d5012500368002c04850400f07410080d9200100c4101005a5540b24010411940c408a00d201c0c508040f01d104d6450741800b0480300060180803942c0c8450a0b4040406102c8000124400800703440507000c070400d00009030f0300303030070180e100419840c0c8090b0b4601c8420016030b40c1703d0540c8c03c000c10564626032143d081000c40700c03130588420741c060341000020b001004180d4400d0004005d807401541c5039a201c4140c8542940a000e1842c0d081009a02c500360f407c070360a074420051840b40880380705031111000d20407030154540600c0d024039100c401c212040704400b05054812141294030320031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 185636510 1250 185635260 185635297
    0xe0403020c0a230409080a20010c0302090a09060617041103060405100c030b03060103170712050d06050d050c01031508060108060405210316120207060f0f20 69
    0x400180c01c221040c1c1202115805071501d807000e4070b2075801200f00d0001c043d00c0c01c101060254540210500914a04504100c01c0c882c0c014441c810060f0712a0111247d140288400c0c8120540a0065040070103d107002d905411000580b0010a0083c4401c903100ea40b208400a400c0400000c0c444000400541d004021000140303d03640702000410301ca58010380151070201c43c3c070713408281503e400d0040f90007014100341140146035000300b01c49044071b512004404480020148940303660007041c2000d4247d1419000b41113045411200419042140080c2040b00315101d02c100446407510340c90180c190b501c04101c11003c2d500030b40c0428001040c09201d0003c45a0702d180c2da0785072800c242c1141015800020601081080400c03603c0e520031201c1c1d40c001920441710681c0210390000074601d0140340f8441003410455805402d01021004990f40c05640d640c00504114000d400c1001994000c1c034903010b141c41c0340380400d10070060101440003104043c0b00702c81c051254607800c001e4010554601c0e54 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 185637760 1250 185636510 185636533
    0x9090f1003080901140d15121a04050a0210031a0a2105010608030c1e060f070c080702090414060c0a02033112060c030b0f040c110f01090b010801150e040302 69
    0x5e034060510030b4200d441c0451003051140c18a05007030001c0d031000002d41d41140a110005120039104138600b5094540529556202d040c110716100740850082c3d04070101d1031030140420341c182c020400341030010000c80d2140207403030280800c46d4410711400e410310024001c6042d032401c214400d5000d2a02071000841d000741c44654142c1154888040000b20364170000d00a018545030303000040864001c3b03009000e15180000c015014068010186010000d240d604541008035440c2507514058020301403001515241c41e20100d1815500c00341c0aaa20400000540f00c034101011909440c4055014505013041c002c0024565416100310114011124162807a00c42c101c010440c000c01c408003062526150600300002201c01c5041d1b408201800c00042c40d9154440e21140c851112041d140061503030601403045500d1a4a003850800500440c0c0310b03480d0f1003c05401060620f03003d132051285999840c031040d42280c011032520b03914030500c1002005002c0c0389034265a4054042c2c0103846510012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 185639010 1250 185637760 185637797
    0x190e071b020f120f01060603271b09110301092405010c0206040e070801170105010b030103030e03010e0a110301061403120a05190c060b0306040f080307020109060f0209090f1003080901 81
    0x1408800c0f801a99071300c1e8204601f944c103000e02e07201d1010552200100c49500c0700c0700004c580707141c4000f500d601c15407140303071484281c100c0c0204001c10547c03004100710000016000c509034020f20032403851030f0601c00031003184c807855640143d07007910600c416500c180c41d110040d10003910070581a40e01103000d0000051544c280d800c03442c030581076a0703124482c960401d0000d1100908846800540c0c0e0714140061048100400c201c23415a50141084058480814002805002a0300c0e201c0ca0502501e002a0100031655500b0004120f0880081c40039a0b103c240c0318206005042c2880d5155000c4004114110756000007881c88800618001317240414140e80fa80c1c2801c20300215100160940c0306420074003900788140d105074041100503201b541002c1e2200300015514030409000600000003188055000750b012118a0342e014905000d004040c4220b440217420400720369006400d03060010300301111094446201d100e00c2d4188a0402d070a6843d803800fa901b1040940b07050061469090504aa5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 185640260 1250 185639010 185639023
    0x60e0f09071b0804080715020703030206060d020411070308040606090b030309060c0705030a0503030708180a11030c1302070204061712090a0b120405010b0103021312060209190e071b020f12 83
    0x5c2000900081e845c10b01f070360ba00b003c0c3e4800350608540000b501840001d50100b01140c0000080719402c9900c000390001a00401040a03404d01941000848104050300400d07043d1041c2c0c010700c0104110380d541c408403000d54007400c198940c15002003140c0c00c06442c2c07510103050030002a40032907680c0b41d1a503022038500065100c1c1541c1541c0044200455a680500b4643d403100302c80e80d08048100d10010955900c0b40100401050241c02501c01c2c2282e403810803101d840200b00030302030700015030307800c1000d8000d40c000c084c20380c011800d00300c0c08180442490b002c03402c401c22020050072500288180d0103102d40101e10069400010000001407991650020b000f000e059109002d0300d5041c00d00c1c00d142142d00101010f814140144904d43d100100b140026003100d8003403a5260100d9660301e80071000f0300c40c49030829403040d01510071400904185201c813003034540341e143e126450307212250191540250704803040b655407006401e1900604212445500c90354016040300c3c2c0000460340c0c000d0500301c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 185641510 1250 185640260 185640269
    0x31f060503150609010c03210204090204091b0c0b04110907030e100b010509060c011509060608090312180a02030d03020d0b06070804030308060a0b07050106060e0f09071b0804 77
    0x32804402d10081031842034104100d58002c5074042e180684140001c3c1052000c1500174090200000d2032909600503402a5040c040035407000319a0355881e0307a60030000750802d0180d80041c0780f40401c2403070241074201c05014051030b82d8403260400b00c0c0c91341c0d4000c10f9080c000e1088840140180c01182644c44d0840402d01605040e18041441c8040b92074040c81e100c0f00e030f11385001c001d0038000c0150003a42c00c1402c641078901c06a030920b6507444025100d5016140c204071403010a01090320001d0404235541c04401624842da8542070a1345446143d141d6a008005000c400c010f0790401190100710100507510b2000590400c0d10f1002c0c0407500001e040a14001600300841c4c0c000564001e4051180b0800001d0b8404950160802c05a07468078152401140401418407141a003c11280d580d07030900c007001410021100b940d00c102902e40180a841c0c284500004251800d90035001490b02c03c181040d119000741003110076503100f2608403027002d0303103a80c000e104d489e1111846010070141c038001d1000c0c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 185642760 1250 185641510 185641517
    0x9020708070803010b120c07020108161b0506070f02070b0a0302092b050c01050403030203161a1602060c030103050c0d031814030708010509060103060c051315021b0a0902031f06 78
    0x110401940000c0300c0c84003c20b10040c1f81020080d104c0140e82011341c0729007080c0c0903000c81c80c48010000c0190758070848441c005d0340700c4c1402c2010108100c0700042d000c0c45014140d0b00e40745102b290391fa0030f80e036500482c010f034070b6107940500840c00c00d0340c880d9024100441000b0861000540e04c00844400c000c6007840000c02403001188503000d0040070485c40c000c08400f1301c1d1061030a031440c0c500030f450b4000c040040c0c041c00c0744441c42c0c1060116000c001403110f550702c080048203042c551314583d0301c60480c2c0d81c6034003d40204000106a020704d842607030b0403a908280a00504411b05081101c0794001d040d0450910000445a501c04091a00400c002d01840c0c240e40c1440350740c07c0e04044c5050815841001c40e0380c1428104480d029000c10b45a0460f0380c0080041a040d914400030b03181409a060204800d0803411400228004c41c0c000c45016041e0503000d980c40e0f13010050a0b20f0705121099482074104400c54010820105176500455000d802d81c5440c4800c801d02000214040b8040e038003c0000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 185644010 1250 185642760 185642767
    0xf010e04151404021002370c12050c011707030203091c030212010f0b120405101e0c021501210203030a05070c0f05130f0b0907030e0c0111060109020708070803010b 72
    0x4c5050164076104142d881c0d00040c052000d0300070601a95443c201d8100b44280602c0d1000d003d2003601c4a40c0707010704d550040c11001c0051700c41c105881040b620b1401a80c84d48102440d641855002d4060fa10a014041c3c01901459980c1c1c0801e81c003a41c00030f000340e02584180152040482c001c004802e6003402c43c1d80d03000d039031110b5040701420030143c1030b00030600038000400100300e0700105104603464000010040000c40e901e0f410078900304160030b0468812181001d03501c00c89940f04c52044c00006212520802003c45e0501003240d403010303012170502041c2c01003401030024101c14880c448000010203640d8207108507650201c1e007107030095010140401d10228400040140410018010303025140c4140740740c81c40c25001501c03140038080031403d6181e40300038900845003140c100c50310300c80e00584036482c2401c00c41001402042d040f0320315012401800c154101c1507200e0100315100c01e04841c0248010390030b00e48070a0095001c480c040b04c0c1a40b041201c48005000c00f0091802041c060030029103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 185645260 1250 185644010 185644013
    0x40b0a17040311010f050c0711060d11040306051602101d0a08040f060c030f08060f0d111c0b010306150515031b04060c1121010906140f010e04151404 66
    0x82d508684c0105e19040d04000c10892000041300544500503000400e00000e03000c1000807c0d428418095040002410000078400b900c4d00d00000740204c9200314000c101c1651807214480d90440c40550180041c3c0048240321303055101c5401407000b002c45c44407144042c03a00390b0507103460314400340c0b0b086480c000042800c03c161400164100010000c60070003100c0d4a0003554010202d6080c898480c2c20b124441000c43d00c40d80303640340011041d410107450819102818100313540e12168411206100342d0070284036040480e6402801242c00d6030000d4064502d0b400d6a0720240904148511780d000d00d000b00c240000c3e141e0310f03400c152008015528081f030303890801d64807002c0c0594840c0406c03e14400100f008102182d80311141c88026a08040c049003060441000900e4200c1d400490440b81c46103d0440c5401034010360101d14103a02c941d400704402c0f00110034040480408580d03280401440c040100200324440c41c500750301620820400280003100b0781a54104e9400c0e042080005c00c0b82400c120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 185646510 1250 185645260 185645263
    0x32212050105040212241e0910050a061409060d060203131a010302011d040608010c12051302030706120222030b060108040b0c0705030c06090a0201090b040803040b0a17040311 77
    0x82012851000386c461101140c02c80e006103030000000010301c00d25800002c28011001072030351841200004c03101c541d801e1504009568603a1110301c4003c0c945400e0128520101621444044404001040482808000400200480c01040d0781c1d00300c00309107203c40000390035100661080e0a1030701c20b076140f0709003401c2c6401040701c81030b8000c0c0e072800314034010b00150382c0100030402410350741c084208030395501102290140c82903500c041429806c028000500c1c2d60012210140180044000c0145684d10380c045c680180c1303100800394040e0403020003480324511030150417031041190b00e400340c5403901d00b40da002c20365220034010903002000c00303a0a0041010b2442c480e6004a000d18200c24103040c07549501d54410406869860042000500d03a810400103100390f4040c050144141c80312450030300f09058645000002c1240044d1b6101c0020624540c21070030707070f401e98290f0001141806d06012400d071496024030105414802c0c005c81c01c40e114184503120521561282c4d0701c4041e0030725004d8059 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 185647760 1250 185646510 185646529
    0x509060702010603020f040b190b0a020d0e060703180b13030b090123090a0503040e0105030c06041422050a0608060a020405010e09040f050d02060405160501020322120501050402 78
    0x16401c42e41030401c00c0001d0b82d82d1683c003815690f400c440c001400585000000c0d1114401048040b5025000b540095074000c00d20180c405514982c00b0303996a000c0f0b29004946500070320088550000341070002d18086840b8034000f00310f41d80f405641700e0002d40c41e183c40e0301c0550406020b04510f07540c809002d01c200900302e100150019071400082c05880c040104d18156125040b2140300148044400107050500410041070b2181d0000207681c0d845403a804500c241c0942405998000c0c400c0c8d06488480341414070840e811a41b030011102e441d440104c003000380140001144001c041d00d803500f042810341d00fa12540e801941c8000c40000d0040c0352a0089042000c0100401211403042c00100f0690740c0021300880000350403991080305945a01c2e14031110002c60002030018810312645c84e01d05034001a40600850245044134010342c604041c0c0080c03a85c036802414010f820500c40c6051480c1e80c01001094401010301c3c28481d56121300c00301c0905070308144d007030301c0030fa444009000a50500d0b5111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 185649010 1250 185647760 185647771
    0x14130c1701060812090612060402362d0402071a061801051011030d0518070803130603050405010905030a030c08060409020105031303020307020d03050703030f1a04021602090406050906 81
    0x60b6070070f21071700d54001400c50280c100c0e101070b0100f482000400655a960446031340c0201150003468050b51080c0c8803e104038801c112006400b135400708070f60b9500c1c000307a5650031540e21040407030b13081121450012084c00e041d07200e00d4210b502440700300c0000c1c80c103071013448030814110140c0d041843c1030010481803010a1180c103030b6103070003040113005680b01d80d0101c10700f00c00681014526070039910340301480d42c1708125a210b1024500010f1100f42c030100001d0080b401c3d401c0c001c07503920640781d0300595101e03c142e0b0782c84107020001d54401c00200d8080c4d00b24540c082c0c002d20000420645589445045600000c1c8000000b6a107508401095810540141d000101502d08000d9035a030b6a002802510000d014040d11160700a01102003600c02c01c00c8500166002d4a406029a41490301902a4000d000c044010900746158407509030b059218024640c80034507101c03005030b040c000c00d0000951200d1842c0c111003100303100250140c0c071030f03000030303405030348036210006551410340384c1c0070b00700800580b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 185650260 1250 185649010 185649043
    0xf0f01060905040b0d06020403080a0f0201020306010206280e0c030d0905030604020607020a080703060615030203040320070f120314040b27130b0102010b0414130c17010608 76
    0x103012195025080d001070b00c00a440000e0070a01400002c0c00340c880d104002032040b80001008004c1100b4100904040c5039191180e5010700c050070000c0c0e00382e00040350501e0059202000081069903c58101e400e040240c4d000e02455034080880041507620a88103290140e01a40800c00c0c9070270100700503607181603079182c004246030404001a864010207040a4481c032001310b040e81c11b560b9441c2e0003100620080048540090b92441c1c0341317014100c14490700c11540c401c81d00e18003d25020740201c91045606a4902019a02c00000a010425040078540251103031507030100341e00c140300181d00701400201d4a10300d0860b0300381c030b00180282c8010b00500420341061004000314400031060301c1c0f002d0044921820b90a5032a47c109a844107a03060440c2c0c019104a0018020400c0e41d00c420703400042a4000d01c0100134031018001511005100603405240c4540000d0009a28000380026240708a842c820002da0300c4802c40240b001d0405d00c1400c9075581c070780c10880c0c50010407524003600f2044d507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 185651510 1250 185650260 185650291
    0x31122120308151f0908010c11150910020a080405060106051914070c15080a15170102120f010f06080601050d020702030c0604090b03120301080c130b13050f 69
    0x59000b001c0c1d0384058118202c588455401074125903d4148800f22403030071001c0c02000003120f00380141211010b1007004025440c00980301e003058400c0303da00d0320310846038000341004a1a40d101d019800c3c80100100035a0041242c2c80d0702804190004000c4110f80740d82d00b11480c20a410524240101a442101071100030401c913001c9503040c14491822105c142002c803902c04c08254900c005100d02c0700000c0030141c03090008a800012604440100c01259448200b2035440c0c84026044030b003500d01284040343e02c0d0700100641e20642c100f02040030405d81c00135041000b869008c2a2008065a03080404421500180007103403a00901c207004112a1404e100c0d98149040003030076502c1880d41d540403441e000101030302551010802c82404100181006640d507650304296402442404a500d2080c041d140003401400d500500352410307201000041c10758100010104840701502844100000303848000b286925600c0d446a10f800600b42400400c0514125648514000000700200920a04034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 185652760 1250 185651510 185651513
    0xb06040b12010c1419141606020a030b15030c07020a1509030308130f0308040615091b0c150b180403030c0305061f030c03021c0204080c1c021003112212 67
    0x805e40040c8644140c14107541400025400c01803500c031f00c9101804401c0c01e41c4969040010990080040c4421030342c0c104400e1002c0c00400110b40700f42d0013421860402030001c03403107000200005004440c4014009103000782d4540d0b00c00300c1000c9501624010410395441002407503001403405502031003030381d16000301402c150b035411f41c80340c0c1500c8054100b011810010701007201c55846900c01c21280d030141400d60750340d1032241c0c1c00f8054a40700c00f890b036480740c2e80e64074a6a005162082c0c5d4194060304500d1a641c2602d003502c0203046c403003020703544004c040c0904800e040d90640308602442c002e030303000301d0705034090100607064590150469000e2a001c20038000800910400050111003c1c070740030a10090900e4102d0103802251700400410103070b4040003007140e000354020412240c0c95000c0d84c030621088003c018610030980d118024000d007442d11b038401803030b144008000e00c000500300040e1440e1003811004030364001e031403e103c00310080c00c80c2d080742c2c1050340c8400004120b082d4440e003d10405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 185654010 1250 185652760 185652787
    0x3180f0b3f1503011406030c0612010e071b030513050d0302100c050904060f1703040b0a0302070c0909060f06090e03090f040912020d090816030b06040b12010c14 71
    0x1c45801210000352010814039001e46201800380000140240250913a6440403000300406898482c464031505038000900d0611500761004a00079482c0410aa8604105015050401022101001482d454003070000c0c0e4406c3d0302071907441c001d9030790310703154940c21405001d001026000103101da0390819809001aa00190312040340b0380d034050200303c110045030305449500441c101581e01600b00840171403104030754403d503c21108000010b4828030b51a0310702c1616407040c1d00514035003400820000d441c8502940080007401e2084198044d107503903a8042108540e01441b0480c0c41603120085001480309a0042030b01800d8810300400c021103070910781036501d03c16011002e0089103824000003482c2e4407540050100c40d04625038012001d4081d4000352140f00003401000840d0b100400401d135000e0025940030100106801d02c4800b9003591034014000800902c0543e015849400542041d20350000003071049001030001b042091500c0c01c041c188403103580b9520854407090204490b0340e202c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 185655260 1250 185654010 185654107
    0x606050a090f0b190c0c121502031302091f0e240a090e030f120f010f0308040902030c0d11130603202104050a0b15010c03180f0b 57
    0x5201c28035018403000c9801c10b5a0400586101a040382c400003400140100903242000c400e40c800c450075623800456140d220100e0106560103050603c12040a5005080101c580790300710300d20b00c00361101d15180d58910040c131380040d0410000b44070803500f404402240540105509410001f41c000384643d4034011540940e0544100b04d582500c8000f015442d410030b104036005500753780c2111b40d64014800d00140d1145007a070f912454403042c5400080c2001011031004150381d401706881d85090314002c07003013000c3d40003d003c51281d800d04004120040806200b03550a5143d00950141c4409504820304c145504d00d602c00300c1414140800c2041e5520000c1c101c418030062440e000d0b8440c08080e001050000c524100c4100c0ca18190003400140403000a02e0070b1340381d2089103034110b41d80e1600c201e03e46c2e503126900c030240071030f540c030210b000000d018400f445000b21501505000d519912150034a20040c503a200003958800014460300c40d05001c110fa403044c8201000581030390b00c590160540118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 185656510 1250 185655260 185655277
    0xc0f030c0f080a0b09091e19030c02040605100c030306092d0e0304030b01230609040f0b060f04080c0901081009050c06041e0839040606050a090f0b 65
    0x84020002400540c841c3d01944d10304002038141079041c80c140324840c1d81c400141c042c0000201d00c4c11400072905000040c492a405540001e500800700b0698041c0e45400b007003807040340d0207a11900c000c5680e0f110031144400788407103580c4017604a03609040c00f0381142c1107a001043c0d4070b4145220034810400350316200c0e85040400810403c84000c0ca040c410007440c541801d41a6030000080c00802e00182c8a181c5058a944050043d0075a502090203560110407080d0300f5048513060064612078032b0203504c00e45503100f086001180400c1c13410700003072655101000180d2440b20200c0c051000f81d8040054400100c41621144119414035108580d11202c004449181a450b41e080604000d000e100000341d0b601c01424868841e42c4600e07001c0716041507200007248401c3e02d41d2000800420004050344a0750001044251030384000300311010400395010003512031101200b84004503204c500c1008004c0c0000d03503503240c80f4481600000d210001c0f80d4860000c880c1600d00c14800a440e1074100c86405 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 185657760 1250 185656510 185656517
    0xc09101203050c0a06060b0408070f050109030b090a0203010c050c060f09061f0b03010b07140a02060904020a03020f071101020d0509010512090a1b050114040e06010c0f0c090c0f030c0f 81
    0x10000d80404904e0201c082d0402010f05083c100300107500507070302d17024000f41c80b0130200b0f81d80b403117440d80360703001d04000540b14103400100c4c07180341003002ca480080215040100c86007541c00079078050b00420f094414070014000061000508041000c6060240c0c41d044883c0c1101c40c0341d42d040000d205075458074041d01d140c800f6010351b45030603034030540560100010701101c0c02c4251a0742c2c0d68083d6001c66002044143ca12541c00d11340c520301d078100862b030003c1c4150b00500c01d40c10011804140002500f00c103c4400c00e2503820441840c0103000c3c0005890494070810b00703055550008000241015202600c4005000d01400000b0361a0707044410f4400e0300400740c40c05012981c0e04c0d000c40e49049034450740907000c142c14401902540d1280650305e030981d20281c03101c2c004041c002c0300100c024400d0344107481040180e6404541d80b9032041c0e4480300c078035003d840c91001542c1c154075401c41c100140e40c459002c50790307601c442c11100c9800440840401d0b403141400c220f0051000b41c042d207038002c440ca880080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 185659010 1250 185657760 185657767
    0x30a1103030d0501030f0213201b0106090207050d020a03080c0a0e130501061103251a090a060f09020303030f10150206010e01051002030415200c0910120305 69
    0x1151001c100741e80c4402c03802c0c9414481540d49003060b105181c0c10042c160700401c5459610100e00d0f0f5240180042800b023110300910b0140000d2210030250003c1900a80e0724040e5003801002910900943c0e010b4842c01c030340160b4680c400d25020303103004040045141503402105001c40802d410141ca16441054154541d5840031b02410072240c07110700746992544411007454500500410f648617034143d40312601d0300300e105510395031619030320300034110200a04008540040d40c3e03191325481032400c292169903065070600d49846030380c18a0104a503070b03c803c0e034000340006060000b10b0040da00800700003942040403418940210f40c99200c014a50044d078841c0e50081203201c0d1000b0600d4000782540301140c800c0020007000291a030a0a0bc00c0ca07281c01905000401d2030b1a026104404040d11900250710f01450b000f10b034150701c1c900c0041c400c01d0188641e1a003049000a02c440800850200d029003003000b80d0404100c04a0341c0502a0560815040c0f024081000a01c040c0705200d60142081e070744 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 185660260 1250 185659010 185659043
    0x120503040b03130501150f12060209040905210405060f1b030307030c091707062d080403020d0305041e110a0e01030b070c05030f091903050304050f0609030a 69
    0x1561140e64040004514000100400c0f2a070501204203060711920080c0f10441000600d640320750350501600841d8003c2c814104100a4481881d00007548215009400d001c99140020701700c0c0e03020401911203400c00d03089018079414401e1000440054ac0d0100d904007810b00001c030384580990041c42260b0900081d00502280348140002080303007a400803170381d891030540002805800c42010711307000b003a00108040ba600500218044503014464001c1921916080e07007152440c031031504040381c81c0249039030b4500d60388400309c036000d042146485404203400d0905d402441c020b6035081010805103000c0c1072000007014112100712f508041071000410085a080c00ca5100e04455003940d44814082c0c0001111071020f800380d81220300588140e4800ea450140594082e120090018829001007000c1003040d0482c034050b1081110243c100c0d4411501c0f180008210741e031070b03003098480d50700114040050340342900001a0710801959414108080000070980d0780c1007000300102034000f01c030b92060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 185661510 1250 185660260 185660263
    0x209010c020904082508030406090c080f01060e07020616120f05041a01080a0c150507050615040b030f03030604050c1e030402010212040302090414030c03040e250203041205 76
    0x1411540040600100303040610b408456a80800403480c158405180517002810a0136240c40c0c1c2a078110b1764141c075550f00c9980703c1000b0254070388111800383d150500405e0b0b0f403004221650503501614000614079050011054440314001c040600315030020040141c185403286050300400301d0350904001084080b07074030078042c159000700019020b1030702041205203e0307160315000540d0b00e09400d1900c583d880700445500e4001c2c400d809444c600c003032001008021540000705200078a14603082d81000456982c0750700b0043c00b50303480300c0e100104100301d28061070203100b0b140301000203e00134040e20000c210760395128003000344101c1c4a6980c5500280e007891850341180c00c0885002c46000c030000178404070030001d8009550690040c4142c3c0e4507041160700c040c08440940360010f004540660311039807510000c0c0e9528030150b203203000600802c04d1904007040508003628402d000e00e0140e14069002c0c400366090f411083c040101c041c003a040c3e01517004001c84054a80c4002c866000c14202e0800c00d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 185662760 1250 185661510 185661527
    0x12090506070c0e090606090c030a0f0515040605061306050310030f030903050706051c02070302100606021e070e0f090109080d050f090a050601060f02070e01060e0a0e07050706020901 80
    0xd0300680002554810448040d001400b6511011100e122540f195480f4076130780d10040303807590f070004004004103824641c14805103034032050844d00403d00c0e120983e0030005441d8103030742400d01c01c540c0302c1c007144031485c10780a03401c050038050311f0190030050101e141c03851000c2d01d84612414004000f002c150150707805090100550381020341c0e90031001c0c0c81d29000305074805038030050b00d140c05840340110300d0300c0c030640455541404040b4200e620b90540c1114070000d51200d03a08400f5803040015041e603070100ca004803401456150080d00c240040c0c0e00410044030f0741c21080b0225500404d00a00001c503d00b0b90140e002007040c3d40700402c076075503001c1942c014504480050700d40341000c83c00540160258200707500c14410040018580d8480600581d0b492035011402804c0e0f1300090010310460344a80d8030060034401d1441103079001a0780d4052480702040a8000700c0c0000d0400260501c14182140460010903002980d401189401900100700307005081e401440c007900064108816881a10300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 185664010 1250 185662760 185662769
    0x8060310200301030803040b070305010302010c0204181a0a060b1908090703080d1506020a0b06130f0204030c080610080613020d05060f10140121020403150c0206130206071209 77
    0x10302d95a584038240031102d82c01c00c403001c4a91110b104005a00300b0700c00c2c01139a048a6041c0c4034000c3e00810350b03003000080c00300d011680440904881d030080203d520400360420083c10411041001e042001440c000d5503a650803011026008100820f004c8407034001080c83c43c00705250544054583e48442800d140003a80060725125012030007600800300b550080e4403c102c00c196421082d40e980d0320581e103031188018098401c1c0410800601075040281c08540c0c0d48070003000015071038504c44e1030310b0100e030007a170000e2702c0d8800d07141400c0c05900c80800403140c20051104d005d02e119403074051a10350328000100490001441c0040500440d114005510340c0f51f9400420386a10303162048213103070b00304070444500401840c03885d000a070300c03500030001074000c0c403044c1d40300e002010368807114803150241c01186c44c034490350800c03000001c503850500842e05811100000300d140388068030024603240001d0061801d00e207418100d03000695441040b1030b45203038425280400e00740c88200070707521810503520 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 185665260 1250 185664010 185664071
    0xf04090c090b211605010806280503030403031707030b0d0f0609290a0c02071e0f080610050f0604090515030d02030702030f010209032d0d0c0506060108060310 70
    0x112002d518801241341d000103545440601226982d84004444c0074105940168101d21107c0d410024000049000c0800d200e03102c203040509542c84000c2891a44160701c261f00080340c003400e0501c40590343d60001d4100019113030034826009074000203a10420444402001150b00c1000702081055940081a050b0307000000042d8015900c0390802e12040007130920610704042c01e0005084881ca0710408880c99080d46c003d010481c00c1076000e6a0304039864241c130b4a0211aa03a001038188486035041d40039164000180c1250b050841c12041300718521742000d0300c12820341c20584002d4a52405540c21074403581c101162a4881c620403c462814101a10303030180a00b45101070940d4000004100083c0f0a800310b40c004030084202030f080303000709684980e1607044101554031883d015a980e0003400700c03440d00d102d40c541803900300340e191001e1b0030002c03808201d0701c1406d0002c0c40024001154802400e0800001d00d14081c40040d0303c070400c50040c001016034550f80c0e122401000e56501403840c00022 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 185666510 1250 185665260 185665309
    0x1050c19061a100207120201140307050a0f05040302030d030c030216030509010e0409110609060c0d030f0b031906020c0c130e0c1504030821070c020f04090c090b 71
    0x10024003401070103004440c4019258014a054140500310f49281070722940604602418042c0002264200200a1341040501c0e404080708020280083d402405070f615402c2e0707142c15492010706142c040340300d60720038042e052100f04003585000c183c1d490f21035040c1ca000039a100d800c02050f002800f41107103181683c5143c841ca242059084801041502c4098843d51100c0143c0c808000079240c4100300200340307002d41c1c9020346260078100c001c1c1001c4c80c4020040e1b410005840ea1003403030002542d01c0d100000341c68042c041e000c41050710421011f100103a000e0064010030504004604422100042041d903000480201c2140e06000545410b00020100070202c048081410068260000c1c52021030080a20030038041c40c15a03d4060046600740b1500e091170f01e545c0343c0c2d90260300505115203421407905a15440304450100d520312480b026102d80c1d07407180c0c1130300605c0344104100311100e000314581103190020480b6081c103141103d40d2024081140b00500000c6000005070b9555060044a502c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 185667760 1250 185666510 185666513
    0x2130902040b0a0305150a0221091905030d0b040209030f070509070f052704060e01031a04030207060c060605100206240312130902030717060f09070c050109050d0306090e1b01050c19 80
    0x4112740c0e40500103100484449840d1041c6000c02140d01a40042155200300059010303000030b0b0300950410f45008100504181c01da202003410542d0030100540c0d203400a001c240102e1402e500c2c40780c0c102c0c030b491900a013a456803020180551041d0200180409101444500030695020b15680e40950281040c040c1c2d507912602d000360307420207000c2103030114030720006803c01034070841d4801c0c07045805a0007461410300d010b1080d070b10001e00510588940d81c4800002c030b110f460b100906003414903664002c20b006c0c80c0140d412840b1780b00801d50144c2e00e10b14401e00b00e26a60b00040c1d046000c5141c1005036946140d0740f07021032819101580501c403520700100c1013144194022824540440e00b280716002d441c2c0d280740802611456900c04e0551104400010800480c0314040e114034031403050000042c65049503d07118a0540400c007140006512032030240071002c2c42d030141e440c072500c1c080000c0640e409007a02c00f0501c840850030460406c0008210621092010400d510401d0254491b0f1440315505 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 185669010 1250 185667760 185667817
    0xa030210091a090a03020603070309050102040e011e051e01020304090606030219080402090406020706020c0a0825020303091207150e09010e0f06040b060702130902040b0a0305150a02 80
    0x503200340400c0030b503040242a02030070003004803003090b50b00501c6040c1040c00c6500f000580c1d0801b80920b810599100034407000240700340f0040016211694a000d12503141c03d4441000c02c0e01e4070100c5001e05a024020003098603540c6a4210920049080c112801c1d003900040385103014540c4a121101e0611000103280c030b415600519040307109804800010b580d5000070b4071645006e50300290840c40c2000058080341c0a540039020340c45c8500c7d805480c01d9601c0c0d0310140b07400d42025043d1141e4600242c1040025540000e41d5030841c200308107140c8201c1283c0000707403a80141161527001c1d0560b01ca911200c10406c0c042d03100640000c005091040c40c001800610702c1603101c448900034559240081921907081c46078a215149520340300129035203050900024103014101c10b608010103001d802e0050f80c51001d201e200d402c0031a80007410b218980100000c1d243c0f240091070041004510030b0012850200751052002e1341800080f000e51100f209845c020f108100b10147c55401451408105254 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 185670260 1250 185669010 185669027
    0x90b0d15060f0510090902070804080102030f07090512070e06120d020705040c09080d030905010e030f030a051003120f09050604290301211109040b040303050906240a030210 76
    0xb050031040c031070345840e60107208054441d00700a102240ba02c4000300048411600100071b024820a2081d0515588100c2c550a903041940c401c424031065070100000c20f944452000c0040100700d40d84482618500c2d910307501c400840c02800b11f0346100e038000035801d07200c01400d1240d60f403c80003125801c5c00075800094680c0e20500401d8800c90503d001c501810340302e0040141914003038000351880705100381d000d0b001415500411502c41d501d40541a170040414400b800c00840880c42c0e02d41d07a0714001041d04c00301c800c020030444440d0011681400440c140080e1031200100600f05802411001c280c00c0d251081c40c0c2c1c0c81552711040004003c1031500c540300c1c180c0c0c800380000c200b501d0403003004131510003c0d001c00d000c0d8403142c0c000c02940d000e0010030110071250090040c2181c0e00521410400b181c0d00041c102c0b401d07a00701c144070302807100b01541441125071186000e409440f4034100b003144510300300b4807038240c606440090107031108143d40e41d441e50300080d81d000740401050360420340080c04014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 185671510 1250 185670260 185670269
    0xa0312050a0f0e011e0201060b0307050c160b0304020910080a08120a380405090f0f06011202130b0909010c030b01090f0b0c0a06090c150e0901090b0d1506 68
    0xe00c401032610450f0f000c1c2070480e9034003070141c6551401078000050800001c000c4c140002c00c541d2a010006002011000114050206561455640c024051f001d91620068a00e03c0440389103101003001048011000d60340c200381d04030340791b0340113455902113502c0303406098000d11141d0280c80d40c541d0070010984024400380700840848680f9543d0400c03140c046031000002c02e04482424981e0510a00e403100e45070450000c0001e50041c00407010010404880c412150407042e50312000b5524078100081140c1c2001c113180320028400c030760600c00c0c0a030203080801e10090194108094200b04060550807416000c203000d403038203903503140038807016001c7c0c640f40c0d0034403012034a4405801029489483c144040c1c03036082ea10030107058070741005551130f5800a0301071002809002d0043c40050300311f000304150103026840ca040b015083c1401e101d03640188424010500902206c01d0f005070311740c1207506044540c60f60000034103504050124647c0445501d0042001540ec4651400b0fa04c40307a1210040c2c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 185672760 1250 185671510 185671517
    0x2030103030e04021801030b0406031e050105100f0308090a0b0703210e191b06020f06010603050105010f0f210f06060302130e04050a0f060b100203090f0f0a0312050a 73
    0xc80856040c08220b10841c2400e0171081040103241e41554002e8000e0591548081c0000401790303501d0b150369600b50444124101825020308010041c0701c130900071103030015046031031030b000940b804403c0c0860400510000b44440e030003181149840d80c0711048440203020060101c1d0303684409150041540910840b08408800100c4458079221214498151400303400702c01011540d142c0c880b02c08020341c00c40307000c458202c40c200c0402d5140341c54041760b030001c10540d002080f08034503084644d403c004050700580101407400004000580e0301c64190003a50007242090704032801c0c498400c540e0843c000010101d04011081600110003403984100c4003a568000d0810245450341c600301c003a07110300d6181011a11615006002540040c605290014801c000f290301481040c3d941c4d5031441900403054039065681c1080b4502c40c10300c1020698401802e2018500d030100160005030680380045100303016003a822100e000e1074460300610800b664110182c1e4030042c60b810b4004100760700c51000d00001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 185674010 1250 185672760 185672777
    0xd08090709020a1e0833032506170f0405011103071206090527071a04080609060601080106030c11030711010909020f0301090f0f060608011703071509020a17010203010303 75
    0x1840c403070030217607004080058502c261242080803070402400003128600019400183c2151560b900b040b981c0b500400c08442e423807110070150183c1d0001040c0f540a43d0074081030b565132a011080d0710f00f0003903201c130194140402503119801d0642c0100070002c10001e03941d0340002409462030300711000000c4c40e00c140609008190b1502001800d490003640e814800200c1040907040a600d1590114040314902c011585801c4d5a01c048410801071101c0c01c200022001901344080d6209102c2e003644410341200a100c0e50802c600000c5ca8a801441a10101541c4101400c84517104800b40e02d0340100250417641c03039100900f001c44102000d1219240030030403851002075407441d10700907103210ba2640c804490a40e0310b070841c480c01419100029545944c0e88400c3d80c0340744265841402c028184640d03a80e099581007260760840355401e08406001c0e948140087c0001a0044520b010074956240010075444140e10100b0141100d80c1c00070804014a44045d50305524150302070341c100ca0095851140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 185675260 1250 185674010 185674067
    0xe091c0503190c110d0513140117071e020c0f090702010b0d0b091e030703080c04090e060f010b070503040512030c03190207050a060f0804020f10050903060708090d08090709020a 78
    0x46c14410050810b014110b8070308204104445110441d250301010304242c0c1c06000441d01d10700c18030504680d914003107003c955000c04841004035215540e200c01d400180b00e5941c1d5140000c0c100020b810006125251100004041714030070f42200701c0100028040707080c2c1c0340c56880d007007034088000c8070500c01921400918043c416041c6801200e00546003004d14034240781c036142150340c003000801803d24898200b00002d0113821500c01c0104c600e802c40058203171402d0546202d404040180d01591074030609006d04404901c01008444c1160310407602110707183c1107852483e042d4001d0001640c801d000210b07184040612103c4180348400195003981c1c80ca5480d0005c20884540c0382c0280c400180031214000d01d003a019040c0c0c183c1207800106202e444804010026030109010309c580000918041803422b2241020002c0766000f101c5814a16260701d40a0f85156440742018040c0041180354004520040d2090045002404040106542d00c0c81203040281c2050003142d50a03254040c0b0440548 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 185676510 1250 185675260 185675267
    0x5070810090204050603121b07050d060c020c0405070509060d060b071406090a0c03030819060b0702010e09040816030e060304030908061305101d06010801060e091c0503190c110d 78
    0x40b01d4118404410305200c1200a180c580401c60f500070002340c07051500110b0b05554512460070a107100f9880030074018051607000342080c007400034841c0210f0924080c02445600307d801c1d101080b6064030341985441d12018964040c110360340c0311011008002803c4400e000e80000d0f400c0d00701c40c02400f02c520640300c204500e42d9400340c604001d000a90b00d0601400064481c40c01303103820080d03174410f094050b0792281301c00d412905154081074000300005007800440d60410440c1e00b421004850301905480c00e84c9400090b80f0500b1656031000c4040342494007098010070718443c1d41c23003020308400d85900d4189409030000380c003809040303001d1003443d0007d02e0160300300e907071180803541c07201c050580070a0744a84480900b0811240d00300d006495410104c088c102004201e00920001c0001700701d25140001d086403841d401342c050352203030f04100703001046080d81c0010360f01c2800b800e00d4030075580da59562041080d00c0c0b04121003204a41061540c0110310f030b05c4110071410302800c20688204240088098 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 185677760 1250 185676510 185676523
    0x60f0105030a061802030607091502070b04090b010512100e06030d0914011101051e07020a030e10031803020a020301050907031106030a020f0d02070c05041e050405070810090204050603 81
    0x11a41940441280c50001e0700e250091013a4441e074130f0368490300d003d02d503000900b031090440d034140016541e0402004100c444078040810403115001406a15050905200c103c1c45117020b01031a072522001103400b9a4410f80c00c540e10310389441845051414881002101110f00d88251800e0001c0da00218a080c0b5001c42d241045450076110300324864542021300304030842c8008028140642d010b2511310201c400c1c000c2e42e200300000c04091001d424200d4100c4012030b40a000a0210b40c424005000000c0d00a0f0b0408803035401200e0135a10b9a104540c111b014020343c51460041c83c100140c41020142c0005454040d81e00c214024807965686e240d19079030342d1003039100217454120383c98071600300b0741048001150070022081016241c0b80b948290350143d0350113a0310150449500140c3d02d81800440d050440150000700c0d4180035100c071221003040030307010f044846011aa525400b041c20414100140070052040e1403d0745e00120b40b655024005100340031050b03000314149000646c0e40d16001c90790 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 185679010 1250 185677760 185677769
    0x5010e090a180303052a0d1e140717060f12031b0604050d020102030c0a1808160f0b0909070f030212010b22050609040c140a030e060f01 60
    0x28009481510000c0041048001d40011a181c0c0c1d505002100c2c1205034140e0080745010703480c08905070500a044003c102124003400301051040e5031074200124a003012125540c60382e850100d01c1c1c40b020207411004401241c05140042c3c41d00107000300c0309084180781440390a031034a54190001404d004c0144400c2c08070392540c0d0100514101a20500e051480310071842d110904882c01c2c10380c404420300007a80c5901ea51545580f052040004020342084241090507882c030083d410b508003100584581c0c001c1964803005c0c403031090704400c1040d00c0c101071070004001440441d440a80c03941e406240d030031005d00440542055000010030710041c0d11003100c0c0c89201c0a00459200d0784d520030111a019a00c0c984001010303000c014211074550603040c8030740a4504201020368640000490b42859224003031101500f04140e03a04010369030310f000940b02c121801340d8001c07a44440c0c03e0f800b100c101d001c179120b125000130041000300800d640355204c03051018401c02111100c3c1c40300031003404039000900c134 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 185680260 1250 185679010 185679017
    0x5071106191104030c0305010b0a080118030309051501061e020c0d06110f040602100515030c060306030304180c180308030601030b0a0504090f110a26030423040f060501 74
    0x20710540140980d202c80c000d2090401c0070b908254907942c0b03807103481600c1d40c81902c2a0703448654617030161400c4850070004082d2130b4000c010154001c0709201e54104880c074041d050507954040300f01402420b00007030400310750407080f000b00d03036071141d80c05400c9000700042c1100c11203080004d0024a03000150440407040300500a0302e14000a6880c40050200c901c0c102c41219070601054850001440190001d404035401402c04145140d02d80c40840e48000c10a90320b9901c09070394800c40d501d01244041744100152201c40d640d60f68840820320710f116039070001c0c1100c402c041d2903108103000740d808070b080d02025a80c1c1800d40340c001c1c0c1c040c06c64007002d40005000c1c01c0040000c904250700950040c00050030140c1803010059a81000408449040f5010744010809006c0c5004101c1c0351500044103c1003181c802141a0038940c0d1240c4429200d18244490380c6600d034038000d00702041094800800000358559a120310500313046680364410103400340540d040c002c0300e50b00b04041d40604020380c0c1042c1d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 185681510 1250 185680260 185680291
    0x40b03030313140c21070315020405040506060f0a030e160f0f05033702060c150108030a050f0711090c04180605100c02010e150705070e13030518060d05071106 70
    0x5c010310304900c5850040e070588a00a00000018103c182c802107031444060010384980c5480240010340e20b0082c001c5129850400001c001042c80c20165903454607a0310b8001101050b03401712030303e480c6a0720b4802640c0403808000107003141650140304107441c0e1940003803800c590b881c4140740c1d64a10000c020001807051040522041e00414850006d8500c0d08a049101c1070568010813081d520080880901d41c01010080201c3c0318407210301030050140600a5180030807403107004120b40204509003003103000024840c0b041c0030071400c024056500c0101050360b135003441500c035412640035220750003442e254105a03000c900c7d1240309840072580044e016603184560341d40111005c0d00d9000040307043c0040f540c41100203884000c05101410045c140c241c1c0e0b2071078181005803401405a20081d5030580300001c02c2880c01131074410300240d41c1d250800d292a40c0210920304500801030100c1d640040011503640e244000c240c00c0113004407652727200c1c51075000c50240c81030344991089426402000840 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 185682760 1250 185681510 185681539
    0x603090303061c020604060306090510060203090d14010e010516020318061605100c02010b040204080712080705030f031021121206080d030e031206040b040b03030313140c 75
    0x103500c1c3d51000c2c29404400008190b0f41e81c005281a086038020000003079695a0602c4100c1c16441415005600401e07104d00f66803400000031364910407a40030741e0050386504141c204001a141c90710070403441c100c009104090348003c00f6070003081c00700d5121022041103182d00060600110860b07488007001d9418407000c107041414001642d01030203000840000c10400040800c8041c004600c8030081c41c24041840c0300100002400c2d249407484c09445a881003100f01b01c8244000b0760f0008840710044054a069101d00300740040f4080c0080107460350000281002c81e90a0f44001984240340c0000600103080c1c0318290380c0444001c05010707003140c60842d842200030a045500c0c0600c60a01031030a1210b0b21420140d007000d640941d80400749560144240f96201601070007010b85440c0540001e40c1050054008102880030241599002c0c0340d6038017400c0e0054486401c904011080a402c0300ea0b20306044002d800c460340c4980c030030384500c1081040569081404108480918002420000c229030070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 185684010 1250 185682760 185682769
    0x5030a020111071505040809100305011e140907020a0210050a030f1a09061207080705040509060919050a021005180402160201080a140106090e250813080c010911060309030306 77
    0xc6c000741e510700d01c148a444000c0e641c0e800200300880f0b8643e0042802c1d4134040c43d4800e8030640c4076840c110081480c0b0140300600c0c00302120007020004866030b50b6161581e44099040501050001c1d4106007050f800c10140d603002002000760718088d50341003000503090b40c0108201d03669141300740c102481c08440d50b0490700c1c00109854011a0040042ca0008459012513103011129401128180c00102040060b86050f1240d240e0064100c0f0160801f0301c7e0048070360351240c041030782c2c00340000044000d01050007000c12014620344c3d03014084244c100040d581c003404a400c0140482103500c0c1d00c0b1010300003070515000361541c020000300742448211441e801920040310007010682441d65074a000d0301800c44441c4546c0c000d02c44c549466080e0b608041040548140c018205d103001507400101d1010f54155a01c20b01c1c0c02010b40c507007082c140e00c032410800c0000c030608038050306590010507000c11486e8194401c1c02c5a82c03040903000c03030303000d00c00d4184078150000701e4982c2804d4000340005401c5060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 185685260 1250 185684010 185684021
    0x2109120403240c03060e0c13050d0c080d081f030203030307120e0601150f180605070305120403021f11160302030d11030105101e050d060503070305030a0201110715 72
    0xb41142d0b240c04405180502d4048400c100041000030b0707101da400308105070034800820780248104554620b81407803841c00803004c0f0003e00c1142d0080845810320024006201041c90103450410709917050f441102000924a280076500304101c1c000c902024090035005001c00405c90703030702401550555841c0d01040c0d4280d880ca10807140040e4513070000005e07000081c4020b40c083d1100e417000c01442511440002d290310403840d9080140186d0740380d03900001010041c51401c80f0b94a14100d03a40d485146000c0b40c0d00d002d1804c1e00c2d5803a40501090004054010420030116a05114505209600c8064000689000380c0e0011003820b4100702c0070b0205ca682644500800d4020b0040301d2030b003c0401543c01c01c48a900500120b00200030006000d03620381036003a140403424a1810a40c0030807080c4200c00b10006d0140325a003403003400500d114101500340c200c00c00030200141a9a1120390301d0611549943c42040310800551a0901c0ea005541054065510103a0072130301d50401e045c03003149040010072 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 185686510 1250 185685260 185685293
    0x411100c0203010204030501020301031a0705030105060d06080d020f060a140c09010c0b070503060312030105060306210a050733140d09120905090c07060902060d022109120403 77
    0x941060038000740e00c0034001080158421800107a032903246061201148002c190100c2030340c4000c005200b0816406801c3d01d041d01c400326106a0b507010b01190040041106a200310302d64001d00c90010562a004124a185001e100302510029541e5410010898035440c00d06901110202c01003a103002664020b0b003019207040c103008402a05540321180501812508900051700000420016043c12302522a0106080c0311290565040c00b001402038000100224060304085c1c5146040ca800809007070b10005c504019600c0e0000c580c200243c03105110b000d6140541c1110031550300d806030710328400304040b26002043c412107a84150880e400e100300c84611100d080240141c8044481903c580030602d8415014500c1090388010701600244072948600c1c810070755102045000c40c0b00208690740c0960100c00061180c001c0c3c40080c0a5005600984401c1d901c007048050040c404a404011403004503280400c10317554484610350b071804103001402c01e81d80148000c00001e05410b0f070200061 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 185687760 1250 185686510 185686517
    0x603070b0c0102211501080f0403050d09141e060c0a2106060c020f040504031b030c0515040b0c040510052809050f0d081902031c150608041110 63
    0x101d4030a040160032155000e000a51640006006072807585c0559543c00c2c082c00e00f044400351400c48913000009600500c0a0180300000404244540b800c0d480380e80b585502640d0b0f41410002c20300c445a65610102601c1808040708514003046400014841d1058608064035481c0c400000c104075040340340650b0391803010029001107485010300e030007600098401030341c88015008190040ac22503000600380c0901803031401c410f00000c0b030b5001c0c030b074200420031002001c5c51f20204c42c902203601c20348a10000c3c02902450b40b0809a0380303230841c0d27040c0c015030187e20b04001c4c64480c0318251003d0f10a07032148960043c10344143c041024000c4c0d0140052504501d44d40410900303003050001c5802a000c0b0000001d541d1102c180700d20b11700098030a003122401c0d1184010200d40740d46004603403188030904030440c1141ca0203680d04a20030000c4421080e2000d403000429080802c91802400c441050341d00108850800070a921344640083c6101c1c035008044001c283d0409814004950f1080d021103040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 185689010 1250 185687760 185687767
    0xc05070506091f02031605130f0b0d05090f100b0103060302031005070206010b1e161401020c070e0906070e0604050d0c14010302070b071b1502031b030603070b0c0102 73
    0x455024894a84a200314070701070700300884000082003c0d0704101d4030b042d1101c2c2c4148240140029000c0303104008060606003d5038a100e02ca1440303018000940c800c101e45eaa003100081024810400a8031014132401c4042c0f101e40c503020031f510b81350b58413004030800c5a40084008540e21a1325041a11440010f05000540c0c94494020034107104c003080328041859261024403848503410840d05005150f520041b5040050348214120301c8400d88420b0309446401140011803c842000d03000c0711690310150030080d03400f0405959000c0c0d00001e0031b410031805010300000b5045120740e00144141070311005026195900d00041d58003a100c1c2c8000354001c082030ac400b1030750f030312003803100c0404500545038000900e140243d440048009118014100f40c01440303030500140e110380d50690085198201036860315000c907403001c01035078004070140c020007040030070700c0c0d0381c51075075000b103000e003c0300003480d85103008000d2501c406110556002d0b81541c000c074010040c00c3c0c4d003031018001a120305c2002628 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 185690260 1250 185689010 185689013
    0x501033e07060203090c0103060501020a140102250c0608010b0409090f0512040f0803091f12230703050906010909080c0a0507081501080c0103020a0201020c0a0318050d080a030c0507 80
    0x303a04141021210a9400028451508401c021000d010507003440c09009403401c10b00000e440c0c4a280740e00600410107041400003240302901600c901c1072282e528489a030102c00390804c980e000003817098402c03058201c8003040091052407810706a8400990061405141034545001030219231402e5803001080e00c031120003e0400d01550340c1c100031140142d6103450810f640075000303108a500484240e07108005031155070715038103003945208110f0780c2e003d0001122003038195842400701110032910b61902040c00b294515210340c403810034046501001d003640e2089415011100e0030359008140741d0040c401007000450701e42002009500c10b1400a081c002e0b200d000340d14151561300704403a59001b540c801c1c84514810080111a100c0c2100c80c401d4a51400c0340070f640b541b070303918121810036400003800c070305081c001d404560040d0815401c451492469080042080041d801c001c3c5140b10711540c00551454001303040340f8101d42252941d494008010400d800038028910741d50213100040c4107800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 185691510 1250 185690260 185690381
    0xb0702060c010507030501090e0c030d05030403170a0c091e14040b0d0f060b060a0f0e060412030305220317041e08191b030c0501021306020313050103 66
    0x140135404a440102e09541000c4d07450b0250f802e2040010100d03800300b0007507600d581c0d0000315101d4038915030801c0c036580e07100c034102140e08034903038000c00124810a0090041003251b40d8040c411b03403030807652840201a15030101007010006041340e85c00e04d03800c501003032210040c0c0c06c4414246c0c450003000003400305042c20120f40611185001603c06070749041001041c0081c5008006915608071b071402d02d013840044026008005c40100364082003003d281c1c4a50315124002160081d1108061080320b542c8607280c010302404044400c0007a21490140c03040c6a0b000d08181c1400766a8035403547c070050030000d100340b004000020b00c1a1490700b240d0b4144a56407450480ca60303451030040c201a90749111000344c40c4800d02d4180d1148041103503400f0040014400d901443c1d0b05141c1c1484d015a000f0000d04289029000e56181181d050303000d010700040082c4c002004017140d500d0007900c0822117580710015070440c0c8442c205403500b0101000100407910400f280c1c5040143d4030103018030300c0548424000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 185692760 1250 185691510 185691521
    0x130203100516140409180c050a3212010b0a05010905010c03030b030a0c0f03050705010503010f210501020a020f1006080613031209030903030e0907050f0c03190c0209180303010b0702060c01 83
    0xf00d2070401028070100c144005014594041d0a00baa42050704518110412b401c09580c002401c0054410b81745440080f09015207401ea45ea40c01403915041c03488640c0f5060003400c41800b114894001681c0024003075009081d90b100b2a00141c58160004180e40c8068029020300095a031b8140140c0e00d001c0e0000c1c01440101003c3c00c00840d008009a00354030f4520310b040010b0b048581030103000c0c401009801c031107a02241c20b549042e90321a41c2015812805007800101102c02012540049241d20303295034001113550444000300304403013046a400910f10200c0e49035004a40194010200059030310f01c5c2c880202140038880e25280360611440c480407401c58034070240c100d0010b02811001c001703140e8010541e80c4034913000c40c0d5602e00c5041c17599000c2c16502c14030f41d2040c000b15002c110802240c10a200fa41e02005042c1220001c0d05842d09000b800240f000c60201c4c4510070010109008200302d201a16059201000542c9142d0921095410035002400101d80c031407000c21000511440038000c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 185694010 1250 185692760 185692781
    0x230409080304050a050d02010905120a05070606080c0a0501031812050c0d120b1009030b1302030102030c1b15040f060e0f01090309060f02031206040b030303130203100516140409 78
    0x142a1080d454504942454500d1b84001c086a04000f0300d840807070008120402c0c07403000d4001c070369554000c5036000d9815010782c18014025a140820004807000007103030902c020242115880c4000e82c03640015000c4601c0006110703542d01840050b0800030300f000000d000303100c1603420403c0c00c201d4484c203803c0c6006481d50f121800201c41c141e1141c030700c00b010300900d10300a5040f41d01084603215800014100300d030a2002405420034400424017514610702e1035001f0326000b500a6689240c003c03866422588515400000026107100d8003160080204105030070103910041303000c3d2038a480c0c66203040c01a8044082da8403d1381c5169811a0040811103038140ca40c244002103030b0b050041c1009000b4006547c04002031100390b401c1001959404403c07604640480c8002c0c200c240c0744d40c40810000e03c24040b2840e0107101c00030030302240c0400080d0090541d0300c04ca040b40d0005405c00c140100365101690440b40b05002c10074058200382c040c1980c2c0c0c2c45000300410a50400d40d81d5074444051b00e13900340c3c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 185695260 1250 185694010 185694013
    0x3020702091302010807081e070302090612010e06040e030708030a111801140a0e0111100204080303040c08030f04090209030a120507060e0607090b131208041d0123040908030405 78
    0x54003011560801c017180e920180d1400c040007a490544400602005403034031a04554442100040706a40698107580c5080700140c562a100c034841000d968407268207000308100340c0118000160a03103071501624000b0317548140614100091540c6080303198001a01c41074001e5250b503000355591a44030044c050000c00e080030302c611b405c40140094120741030005800706e018810019240307265040039080902007000c2ca0444c00070380c40055010300300100d5883c004006400002d000481ca8000005140a240641881c1c20350f82d03940c400b40c60b81e81c424031800006030b800078001000216195800791030200009010f4074242082070381c80c4903400079450900c1020402c04078050701448028440c521201c4060301c01042c0500b00341202900c1504e0b44e01c1100c5464200140c00d00450011510f844000d0549c610404007682480c0341002551300180604426051080d00500c2e044c800401d07105c0c12240700141ca0740319500032400354400c0030689050303a038225032140b081c900002c5200300114800e501400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 185696510 1250 185695260 185695291
    0x2040e04080a030e060705091014030405160602190201051b060103050d110604021e01122d050402180a1808030907050a1401050703120518010509070b0711010302070209 74
    0xc10280c111040301c0c5111000c2d81c01707401003042e0213800c4004c50714004000c80f249034190201c02021501a040020071102859001c81880b08002c0002000341d40744140030201040ca50b11042c0480c0c1d01c00060758201c5140e001c02c15288095401100144640d1100940045600758490788a9180c910281d0080b04c50f6400210044002c4d648214a40d03a41400b100c00781885041c180c00242141d0304013010f01202012080d010b03603150380284400001580c0b40c060a02080001c08094600001c1260380c1c0c0c01203204e085222102c0080c030780f0842e4070882d030007421080c0e0302166005403410b401c0020009102caca42c0c0e914005a51180184179410903c0c400e0348805d64a1074903084107414003440740e0181e030207090b502100703024080086c64138080f112820310b010790b1551101c2c1411110705c0707100f1041c401740324900b80c144101a003074a100c061001074002c0007400262507580e50603a075480623109007203903800180080000181000d0741107049010500d40582080015000500c01403400d6441219511640 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 185697760 1250 185696510 185696527
    0x1908180f100e030c06070f06180c031208161707021603061d0703080301090f0204120b060a0b0f07060914150a06080a030c0201050a1403011203080c0705150a02040e0408 74
    0x10480880640402e5402a0800180347e80300e0860100711316008000b03d44943c1c0000408402151000003030740c00a0044245543e242000302d0903054179446d05000541200000320840084241c0c440a10070560b00e1213400d1000a04c10f2a420f200039101c4000c501486005004203520000928059801a40002150740141101428040306014058001d8000030030030004280d4000a40b411900030001c085107052840d80110300a01c9541c2045886080040c00402070107000282c00b03104000507111140c8980d1202c51540540c0110060500018000c0020300000744a5801c050000b0b03214103200524180c022084904122512140070b52404100040104454480c0a50001407400c00d010341001080c5480041c410600b20324081d0600c40c2c00641c01494030b204601c0d04400140300102a07403039586030a48410020113200c0c040d00001c0050020520344c00010301120505507000e001407020a4a0184031540d0035001006a43d00c43d80c01d120028540d032226011900c5180b00d080c2090340d54028 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 185699010 1250 185697760 185697763
    0xb03060603011503230706030c020c040902030c01111f020c15060a051210060308090f0117010302091b0f13091802060c0f12040303021908180f100e03 66
    0x102441d1203a81852503003d0120400001c079010740c0d40101e000f440b401280a500100259030664400c00b510843c100080e101e80d15070302c15041ca242d1503083c0c07810041c1c000c0400003516205600a541604044503e04a42d0700517808141c0410450054942d03074549441d070402c540300c4649004c43c041d9000241a02403240501030050500601150600355084c2180070442c4078519028090040e03915002410b0080001c06c541c003814a41c41405104960f2a8607203450550021030711680101e0724000245199800741c0c83c0000d920160300c0184000e41c1c6140c00f008450b01001d01060031001814080f210030700c4000c030003403040040c0c217100c490b51911a81100984c40c91603a0107600e41c2c07403805603496146c610241c0904203003501124902c2d115003146010500308042102d030100c0b544200620004414013240280c02200d02030740a0324180100465101905011040001c005210400c00042c2c00030350f602d1850000107000e45628080c84c070b0000403402110071100b10201280d5a4888141540340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 185700260 1250 185699010 185699023
    0x6010c052406180127020703090f0b07031e0c0506010605031611031e1c1e020304020303031f17010203041b0b07060b04021e07050105090a080301051002070510030b03 73
    0x10035036054412055007101c24111030818003404880417180a9541000f00c00c0302c9030007826440d00c0404542d00c508a01c1d0140c81e2052a100d000702e045d404000000740c80581d035064916040d00350b1609900ea164040b1820070301720322146480107000750040244041a0100800b5018056549800d5581e05000710208004248440706108010f0a036016841020000c0300391070980040c456014040035800604651034002e05d9801c40d40d07419540400c00545500350801c0d010060b2038919608100900130741c540c10303440b0445019400d64020400f0685045000d1140030255030b02010020140740c81e80390b4500000300c20020718000ba0340101c144001c0c042c4084200840e2070041c081c40c1062454410040098098807074080c02d07440d5503518500441d02e1760b40480740011990715000941e208c40300c0040100e41c01c815002e496540c608000210300540000710640e01c507410005040c11030b8a42010000103e100004501c11401000300004003501e83c0001e002544203151800304000d00c2d40400e041c60040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 185701510 1250 185700260 185700271
    0x20a0f0b181c0308180f01020702010e03010506060901050d021903020a030506010c0c092a09150206010e0105040b040209040f06090c2102090105280909091a06010c0524 74
    0x1400545100b5681c003a203940100c1c0c0a070700d410410a00c0e030b02c1004030107011070105584502c030302403592a8421088103600511a5910036200ca0b2149142d80c0c0c01c4c10300f21441122a1034000e08204040c003201c0d800365000d0485081c0302c0e032000d442c02507130944000c2e0340105450300b000449d0300410002803554040c010160320990a20300f03e10f03103900f15150003400c910507101c2d411034165118046210b00c07a008240c0f402c041e0f01005059501001102c00810035070302e078801d5281100c81000703041070b1544003080e40ca04880607440f108103564240020040181403103520ba56109600304680f400c20745079405400194100114005201d42c90f114004c0280d032032101118041010750b114495441c0541d41c034003101e1400700040141c80d5400302006865621802d40b4100443e00000d0f0a400c5602c101c8188a81800459603900e16940d0f40b907810b0000e4849604004100040c0c520300034080c114019106640208140f4042c000ad4807240c80d400d050a0341803200d05000d420804072001c94940700722010740c022 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 185702760 1250 185701510 185701519
    0x3030e0109110418020406030c0303030e070b0a031109130504062708030901060b07060501060201060e0c070611040902070b010f12020a09200a020c01090801020a0906030207020a0f0b18 81
    0x1003050b964a196030550407112601c150365404800b41c0c01c000d0861160b440755406002002041d86a0814141c400120321040340062305100c00209002c0c000f240000844074040301140c2020300c2c0590540c0034244c0060141c0c1215414408602641e50741003201e803013030103e60000201403c2500f800b105607612080e21303903142011006084082d040080c01268814cc01000c40c0f0b407030f40c071900101805032450740d103d0403100e1000f04480003030008540c09141203c140e40c00800a03a07a440340b828503015012140d04281280500c80e12010400036000304102000d00c48c0410310701510703400094201d0300007200c1603945640d03000052042200c3c44ad500c6000d0060100e82031402c800076070000e035003c0700b24065070000c0307511201c003640e03038800c2c0d80300c02d0030040f034a003030b280340c440352443da0080d6920b030300302460ba0007e0003a0900040104040c07084889071500c59a80c89001c0741880c80c10b030702a5104460484e00314191250020f49030a001030882c02421941c01d0956441e0b01030002019058804030b84107114 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 185704010 1250 185702760 185702771
    0x30f06090c15111c0e0301090506010303080f06040504080403080a0e0a080304031511041a0f0f0a021606050d1a0d0b04020a0b030f070e0f09010620030c03221e0303030e01 75
    0x5085942c2c685268030045c907001c1051215040402c0c050440c6d400b008150b481380e40700220030150070030b040c140b20b03050584c0180d007903541d031000300010343c1d00c00d44024107218003c0100b8800300321540020401a64035043c200410500d0501181c43c101856000c01a15017004c28240200503045850780c9000784111401c0c8a1040e586a5420300f0303205611440d4a80010f070300c003241d1442d00200a82e0208050042c1454542c07107800c2410306150300564054005006841003e00c140041441700c000340c035010780c0d5103402c20b050582d03038800501c224a2010164080c02c083d0a40d00c0d5111281c02c0b0072903115a08454035800d0600c1800442081500107960a55040c800c10402d8040ca46034258826040d02c0c0c42d850303013242000420034943d00b10a2843e0428207400011a072583c00102e00c440c103505603000c200c0c2d1121080e0300b40c0d45074080c200f00b008880e041000a184026260580140da02001050001083c0d503681c80c1c80c020503070341d040084120784801074100f062581501c034204014070201e0080c0700 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 185705260 1250 185704010 185704033
    0x10201060902190e032517191b1701020c0105090a03020a110d0b091b010c020a1401170114090115080609040c0504020a05040e0601030b0a030f06090c1511 68
    0x444600c0801e00400c485014031600d950b600700030a0821120304511880c5658503501e001246d10814000c1d0768400006080f40809804005401c1c0c034059007406103c2d0b142116903598140400c140503264012609030b440c04900d05881401700c0010402903400103960b00042e04666084d100004e0114200341c02c0461130300701180c1c0209280700040d92001c821000401440c00250303c2030700003040544085007843c10822108000101e40505582c2e10029000d02548840111040f2540303c00c029002200c020040110341002d0b0002051164141030049414401030f6034509200026031001010f11000d40c0d11400d00c1c1450b002c05405010203c400d00381803649200b000d00342243c0238000303a00442010000506014002c1d40b03003800b80c80010010340d0340e021402d07030080454102d40034000000d1500000300c4d00541c0a4401e40f4403c04018104d05a410306e1601c0d01c4101d090003040a503580c0d0b44800f400c0c1c00241030a0441c1c0054840c180251540054505000303240c012114080ca895903c01008800d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 185706510 1250 185705260 185705287
    0x181a03071206050403050d0207030c110f060d05090705040c021c05041a03060d080a0903030905091302060f0702030109242706060504090602040302090c070b010303080402010c02030a0c05010201060902 88
    0x4030458002c0404201912645000c840e10310826408030001440400d03040300701a44001ea60880170301581516581c4000c0004002c0c81d4240d40107503030f9100310200300341c08690b42542c018a07405100b08056a10b042c3da43e40208065800d2a010040141c11900003007954035a0038400d030404160a180c05401d045c10114040f003c1742c011250108208404070005003d96102544146620b40c070050003512030400c104003400426a500089000c214070744004a0241031008105100302600000d44026054a03000e01c00d2503403003c940103407030020410140380940c600340030701c90400303106113011a0b116004495210000c46d6040210011034200002c09400d0100022401d8848192142120000e01c080c60020000e00305540a950000c0c144800002800011b42c05042140e0084e20f040c600ca81e1082c00f050124422040002d0001007000c0051000c40e10034402c0550061041c1448074200c0704070740020b0700d0b142d00500200d81600440c0d80500640d642801440b004020f600302c150300b0301c2106148031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 185707760 1250 185706510 185706539
    0x30608061306150305030a27030206030702071d070e031b040c0513030503030109150609061202070803130203010e01020903120a03060b0d1b050705030304060e07181a0307 75
    0x1201c0c9400e07000161024819107510480800d8000115401c02c03030760b00d10301151a038100c1e80703520b03010030620f001c82c0e072091145c014501c9248860503a41200c3c1030541c0c0c208078550300041d00203030840c49401d8000c91900380745181014244400b11203c48a81351074180280002a00341c0014002c1d041248880382801c0d080c5c4000464810172074001c20318005208045541e4020207003100d06290724442c2c0042400408001507040e09c00c00d80e014003859240600c040d110649910410b0002070700c00404012840c400d18101481e003201003405841c0001607280d12034a0341080d60321300d450030014201321045140034412541c2218200c0001d5040c010041d00003600e81c0c031030107017187d2100c500007400c1803071600c00d0344128082e141c0703015505d40ba152880c8041c8020f01840c6540c408281319050000d6070385006505440b4599440300c01946035950383d031744000141009400500c0f061141a002203500b611451190402c00500c07100001c120802950041240c061248030a0090b080618240800b81a07072400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 185709010 1250 185707760 185707771
    0x7030c02090403050d02070803010302180f160207050a080d030b041112180105010e0714040e071b021507020a0b070201020a0206031008011a010206100f050f01030e0304030303060509010603060806 86
    0x18010310b0380d4908041e981403081042031019a032000421030100a4034202540c1620700035141c8845022103012490301c0d141003520440400c0c0c80b1031001401c400503044d040460785590f403064a08640d91800810751640d00c6400580b0542c01102c401040036501d48101e40b8007030300c1198140912403202d0302c010a1885410242c4111800c8400000c0c41e142c040f010f0041a00000c01c0204410341c2c1d10510345c0c210364030640d0200c00040040071000715910001c41902c0c10f4070021100100c00c0e4580310001d4030341580510415581c0001c8503818005030b510f904e800c1413007415094989998207000d02c100007840d0f070b458003c01c0013603c09006030000740c2d0340015032803900c030344c10794240c0d980741c0710905200c8500300185c0c08982e032582460350f40c2c1d504808004520b89009070030307000c03900c070b82d11843d404030101c6582d80034001c40344a210401308903514000d400140050010b050014500491105175402c582c0950019030100303480c4c44d0100490304226086900510303483c6004c002103800c0c22507060b141c0001420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 185710260 1250 185709010 185709019
    0x1801060612020a1728091e031101090503041703041409180a110f030f1c0c0b0a0e0d020d02060a0b060d020703030b01120b0f041d061f0b07030c02 64
    0x4081038214025088800c2c003425590607100d051800c0c00c10001c41e2000d00c00c9070170708a8104040d03102e07150050300481c03500c507031311100c00e00d0b000b8540c070081c1d9810440d03010240c0c2089005008074881c4c060a1150300400c6020307030091a600c03801c00c1e03618014101d001440a4140d40204800c02844454500606440c8002c0760280e0040c0c580d400082100c00440c20700169500544000e002080008554004801419a002808501240105074940212074100c4409811650024101f0401c080400406440702c2c20f0024001001d0340b1126000070302201e030718545a550b00030b8400382200820855074904018401403180c0e842d40341001752030703080c044c124900303007034a9086c07040e00c1b96114402d0703d01c105049402191a41c41c6030400401400d91158400e020480a480c5444a0343c07550251800c40d050140100340c00100e540d080c04000d00c8140301d181101e80784145540c0001c181840101e000e012000241c0c3c0018929545424014000e5806024581410042400000c1d0000003039a1801d4044030b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 185711510 1250 185710260 185710267
    0xf0a08030103061a0a0902091003111b1f06050a09090c0b03090109080711040f0b0d0b060a05040c0c030215150607050a02150d062114010e060a05180106061202 70
    0x103401c030003030f0301e500c1303500c00d5002c141c8050226031010300c0d03401f400030f04008a584820350040c1d5041030701111025031140c3e04858041082c1c610007020300c2c507001482000c10b01101d00780000d40070919040c406158455403400d480310002c110510700618401c01030514030b4020401480c82d6519001c0d903001a10603800e2607074000c00000c690b01420342c0004582c03a0041c0d84130350b46514070f2520300f090001c098991442103207004202c0070f64000e07511032900303122009031100c0035070616911000b0300d806c00240a140e22000d030309404134458946000d11240201340d901d4a02e1180070900c0c000e8103000e205e001e002d04140106040000b070302145600300071a10010f0b02d03580c0e07690329141040c2e41000d0412101035040982d030305269510481401c010081204641c1080000640700d11003d5100100e400d0700142e109458100b440100b0302019403c541c8404071400098402c50381008642000011190744043d260b442d010030400c0710b550840b80c41b10843d00c000070000d07d820700c031014102072074040c018602c135540030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 185712760 1250 185711510 185711531
    0x7060c050f06010306050916080d0309060e0a1a0f070c0305090310060e090c0402030103110103150e0a1b030b030d120f02041e05031605101707110f0a0803010306 71
    0x3449015031603404801556202d40c0c40f400d006006e0001515020080c1c800d0801c0e82c1d0180e800d034904101690401d034060b101a551110040300035100380c0e1415140035994684903a8020340400440c40582d11a402c007d807804090150200d1183c001400c0c001160a60070030403e807070307a0040c20000d032180e16050040d1110f80c2c00380864606003898a0020340d040c40c2000108000040e40358407071081401708211401c0c0255001480305a010a101c000c140240c4803407a6072856000750040b420400321100e0180241c3e60340c07988050403440664860409659403480a1800d107030310015440810400c0c203003804854114004295655903441590040041126132550181c1143d008070040c2d2002c84000d540722031700caa11030201d11a03d1545400c0b074145c6d007607000460f030502040c400301c104401704080302850302d8201848085c540000c80e140030040c240001c854502071004240340601c01c50754401007025181360071140307003c164407042a00b03a4060400140080c201d101180c0c1903a03400719000c180b42202c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 185714010 1250 185712760 185712763
    0x50f0103050606210303040c140102070f05060c030712050315040203090d0305220b160e090103030e0a1503021b01110a11070b03090a050114060a1509090513030305160207060c05 78
    0x413070a50340c0da80c0400014007090260344414441624075245101c03d041c0c1c4040016030b59000c03603200700744a04000f96010010340c604103001e0800d1038061020349203026529036800a5481440e03081e1008a0000700c113014103841d803c007078500001800e0340d0452071814040310052303960f01e140403500100368490340010b0748603003145891030110503281841c103c01d211924018509000444040039104510340a00488910419000000b4940544049091f0f42951401c40306180b10701081038000790015030014040c1000000d449035005107650058490240009400c0115407031240550582e041044000303105032510115031a0004a06100403641841c0310628102072646e0300075043d1080110030007140700d0740401c0b0701d08541e100700000c00c100007010030b05900d00b00d03043e2801c0b6001401e03c54148045010105407101c840400e0070480c071600e60b51140081603071001c41c5c0703070b1030850103c0d203d640405405021341c0b50805c0040b80f4a5208040d6524020b50760120b5100708401c0100e10280c841c1413140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 185715260 1250 185714010 185714059
    0xa0203100312110c100903021c0b3102060d0216150b01080906070905090405100905030a021b06180a0b031014120d08100506070f0501050f0103050606 66
    0x18000315004456109000c007038111030405003400e0480c09061044805450240e09281c1700d40850789507501602c1c1103400f40070802000c1c0d5420510700c95003140c04008960314554003445405400c1c644d42806a2a041018040440030800302016001c40360710001030f640c42c0e05885580007070040040e103422485400d5008804494005003088003200301e2040041000e401c00c9841c3e603c2070b2103000d09611166181c507601c1c0c030225200000961000c0051204d480c041415580003400340c822140011030031172540d02200c0c42c58800702d42c0e9a00010300d2042098046c00544031450003016120b8000b414180418071074410f80c0d00303c1a00202e2a203660981d0380e10400c43c42c02525105081507261301e03207400001c142c84050300030b00905148070308140d2003626048004041c2051810301509003040307011019552000d0240c81e03069030311885203001c038482c1c5801c0068040107010302c03c40310750681242001c608540c8042c028400d42c90b0688014404540000341481c2c000c0401d80f0100c95031070365148150004031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 185716510 1250 185715260 185715263
    0x30204031a04030311040303050d0504030e1e030d02030405090613150b09090a0207021c03030b030a1505010902040f030f030504030b0a1a030c0315090715020d0210060b030a02031003 80
    0x60305214201a41101c44401c10302c00d0b4401e880400203101556803550030780c01244801000240200304403c0c800003a6000690820b00c41e04090300342041e4500001ca0007800d0fa040200e05101200050050781340810241e03401044500140d89404e0905001c0340c2d81e808001c3c0840d024440000c60131101e10a581e200189014076114050710080c0c076501800c0340c942c082c1005d1032040c103481010820740703c4c251007200d660550040c819002c058060b480704070000da0241c000e4007416584c5200d0205910107026600140f485602d01481c41070040090808441040e001101e01c1032041c0b09c2405800081c000010a03644c1102568448025a140c101ca02e4480c030380000b80b004030250b040c82050b01e020307084465110420380180d401c0c240305000341a540e490501c0c50a074107901510a00d1004103442e0b103004e420460403c2a540d8458965141c1003105001d000d0340d200581c008000041002e506005185521146402c180071492801c01c61010318003014041080036940000415243d01070180620000c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 185717760 1250 185716510 185716523
    0xd05032707080706020d0f0306140d0515151c0305030403050c03040f0b0a030506030d08162307021c02060f0a0c050d020304081b060d050c13030f14030c0d0e0103020403 74
    0x944c890000948800c020398440000c94101003841000340d00901640d02610708040a000551900104120680d07209800564481c0502030402049031801860319201d2019403002c9401d0700c440800703020340d83e1104000b00645040180d10100000d0740038085903001901880e04540301c110308140b240c214403807135009100519030b621001800300c0140e0302030035072507075292410015590b441080c03684501c00c00c0c582e40001182c00c0700154660a0346400000c2c021060f141603000320750704000e090f0603855903181c0300402c040085001e50451500e210140c4030102d0000020b442100940e0200e00c540c01a0160081c21060104d100e02126208411a565094101c001c640003d021107002944a5100c0e020703651181c09913544080400701c0204603e005001c0151800749050601a0781d0001040302912210225004021000b4511104201c2c40055406031004580f00d085078a00107848038403d1030700071165041400341c001e048170041090900b400090401c10320101002004800a11075500000c0c00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 185719010 1250 185717760 185717773
    0x10b03060105280903021f02120a0c060513020910030b0402040c030902090421140f0a0e09010e1e0601080402010e0a05030a110405010f03050307060915050c0702030d0503270708 78
    0x3c03070b42c42501101224000c2d100c03a603601c1c00d405045a515110052034602503031101b840b41000581d02c0000740400403092030304007190341c003517660350050310f00a440701a8124080f24540b41545802d400540e0084dc010000030308075032840c2c1e100190008000e002034800c554070079240070140e00075040341d244283d00402c5c418103450b040c86c00d8002e15051182c03140104205454800e9041e0150b1a54412444200303020350401102140d4208180d01c42c125440030000d010b6906801c0340c807480c2089004c0c1800d842c0c452a41c0c50104400da00300040081d02a034460740540030701045981003a0481e400c250280303030044207050702501240c4249100c1d40510740600c5610140030a02084e21800e4000c20710454040c8602e0340d0391120034044200c0c902010301540c00030030070700c800078a465010b103004c144900707040322080760040049001c9a80c111340c0c480c1c00c6440000c0c07840c110718043c001c0c1c00c080040c9090003802d50903d0720200503c0788070303080740c2051090404c26030003150700104aa40f00800d42030045803403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 185720260 1250 185719010 185719087
    0x70b04060504030e0306060a03020d060204080601030f14010203011412120d0209090c19050a020a0503040e09101b0f0e0307060e01232b2c06010b03060105 68
    0x81070101c0e0181c0003d100c601c00c0c4011340c40c001c1500ca000b540d006104009442c1180c007000710803050110201c41d025401c100005000364144205070003180964652165010380d42840e10094842c1a01901d59074810801801080749440b000f0103090303030558401702803030780700b00e041890a00c240b280400000c0c0e0120b14441414440c3d0014040400f044c0c9804c240754440e0b03030302422075020307011006601203104500e00418620580c0980000031003403044030b4406142d41c4510341542e12640002650301840c1c400c01041c1c2400704800030301c3c203400d44010007114a1150494003014820414171040000c41c00d205503a0358406c5d018050090030080984407142e41c0c1d0440985a00c412504607404190000305540c4110b5000c13050030a00860f0039041868000922105181c2d0742c1354410340e0440c8080c09070045401c002a05c55050791541c1124450014140e85001400e0800108a5020160300400060190300100c0060740c0d044882820601c3c1ca8490410508107031444038504036190400500c107110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 185721510 1250 185720260 185720273
    0x6080c0f12040c050307050d08030703090c030c03030f030b0f01140f0f0d0605040c0215060103090f0b0a0501180b01120b0a21060b040b100c0c080706180f0f0e060303070b04 76
    0xf81154022401c0340c3c1c000c1c1c3d07540184042817203600405400790740d060002800c51030181d00a44442482500d115031056220790701c5060f441003540042e40081c0246414404031a010710801c2c0c0c01510840e04800c0d21450078000a00c581140001c441c0c0004001c20514511804202034513181c400000803280c441a0b0300281c4001402c2601c2428450b90910104484080c000300b039a40001100e0100b407249030f0780f41c00c019400b41c1803070442118144211610003003c0707842203407420301800a4500c08200c07035241c50841003407007410055040d4540c0c60f01d40f00c5803041e80c002060031a142d6042e41d010440050902c001100101da50780920900000014522100b02e4039406030b400c0f442c0320340f1003008a20b4544007400200d07001248035a4104942c50000d05600703000350503100340700784610184281303680c89058050505049a0105001c11440a280c203001071194140c100034240390390040c0213044c9403903440a108d0089114600c1c2505003400452180e803801e008a400380342e000903650f0601e04007407400c00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 185722760 1250 185721510 185721533
    0xe030f010906050c0a05070809180703020d0509191502070c0303050403030f0305060901030b1302030f010621050c06160501090c05011e02030f0a031805030a020f01020406080c0f1204 80
    0x1103030302c14078003030014489044100542d101c502c03040d540e2a090a006507500c02255001d41c1400d035000044200111001159a546900c200c107541d41c05030300c90a80e8130301e2070242c80b4060001c0c1075a07008203403c46121000c401c0506401e03030700130001091801c40c102c074000007441104c4025280960030140403051580040041044a20076500c1703a8444510410071400c4502c10740313203141e100b0340300307070040000c0780c1c0010540b0380000c21618840c03540003003640007030b01c2e150183c6040c410a03511078404001c0c012602c1400c1141c0080c04210f07040559060f0f4800c0d440da07240c82c40e590720a10300480e07040720f03c4d051140181011507000b0001c025024141c144540c00b008a03100d501c0c001898200034282c040420040c60900c1c0089030000c50418030014103607592b036009000401d0401d5918840c0082c8401050a0300c400d160240d0090340d0740d202c00d420028209a20b4510001c03a0340e00410040000760b9010020560001103030480c2602d80d6803200d003011461103172035a207000703409101d41800140b01a03000314 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 185724010 1250 185722760 185722763
    0x10f06020d09080304061d0d1b0b030f0f040f0f0b0a0c110a11040e03180405060d0506041101140c07060921023c0405010608040f120e030f0109 63
    0x2110240c446081c02240c1c880d42601a59440e90028001040302900509100b80d100043c0620030440d0f9850b0800304601d000100415034110b00000360400c104605094024050400c0d0f07040146540717800c03480c05044420117004581c0000c2d46100207002d0050886180341410385c86a00052858060704024442541c25074118207414544525800002c1c02400001d5480c0a1803000d000d000015884201598a5282d8180c3e0002d8a629800c40041c5080c001841441c02c2140495000000c100c1800100d400080c02a80501100c1c0175000c0801e4001828543c0650b0054401880d4000c5200484481d0448500d1680343c0d580410307000c051090205000c01510919a101c100b2155a41d0110502c904828150308903c0c1d482e003250809410034465000c92a0403050310381d0104290481e00041c1c0002201024000c041206400c141c81c0c41c0c14011a8018610b604d0310f0b0120341019101d00d85041c2e0503400003070480b205014104011401200a0f45041000605446410b07203600e04c0700f4081c0c502c0c40d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 185725260 1250 185724010 185724013
    0xb040605071b02011d060f0f04080706031116030c020d1109070305070f0509040902031c0305060607031e2d1e0801170a020312070b0736030b010f0602 66
    0x201001005064002070300c401c0e016960317180302c59401038034880f8001c5424010b642008041180901d007183c8000200406c000c2146070540d1189008500c41c03c01c00d242d0050340405050091012110141500761928000751405005491402d40f0f0151502c40000e08025004001d045040c03090144002a05904490a58150280d41d441600031012a00222406408a002c049803c451940b166001c0c00e80d400025100040e1000283c00091030066044154050b41d07140300c500326901c65040c000d084d08180192030341c60402070a0342d0080c4c88490041c4011481c076503807440280741148240000310700e03030702e5400d40c8204c40c2c60780c0030010000c81130b403010090128a034115081204240c1680d0b2186004665852002903403e101300c0010020b600c404071900d92186098010150b0750038407400002e440a1a4100e944003202e18080c070710058001c280f8000e01074110707180d0140c54001155420429035441041c0a00110f685c0316800c45000c54201511a00e0054000310703e011603140301e001568120380 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 185726510 1250 185725260 185725277
    0x109020418050d0c051911092701060602060a02031e0411100e0a0303080907030b0f040213091a0a0e0106080c0a0f081005070e061909060905091f030b04060507 70
    0x75110401010b10007841a03000d00c5034000c0c42c04043c486c20a10030300c201d20540b040d001d00780010b032004030140c1e070580c4241030060003000550f00214050881c454940028410030345130540c087d444220041460040c90340001c00200a0f000c01040709c0d0003221458103658880c1024180702c84608034000780c281c00391054000c1da20303030140200d151012004004050b10301480c10b59900700c0d549a006841c450140c0f05a03080030000680c3e510348907102c0ca0842d0842200c0f07151900420141e01c520010710340c2c000c1e242c21610408140d045400d45000580728100f1451038a038903150000030205440440959468802d01080c404004142042502c1c004c840e000030003911003580701040310541c444d0282a0b8081d0100c02c10001054010641c804154181442d4032600840401c051b580f1001c0d030400080f8007201001c0100783c006d80102c1c080c042c01d04c2c1100410f8106000f042d0801000740005614101c01c040008450540112600c0615444030020324281041e241c05005072105440b104003250140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 185727760 1250 185726510 185726533
    0xd05160906210f08090607050a0c0527060f1008060901050916080402041503080a02151618090903050304110603070c11010e0307120501050606090607021002010902041805 75
    0x2c0489500366950040d19010a02c210780d02c0e20f0300e042074224102c0b0010b0061101142994404c4050071400340620050040303500340d45000b540c020003a400c084d00c1080c662004e040200e01c0d2190481034010100c1c10302900c1d807640400505e422508080301c96018641e000401e91940e84204068042c03201500e08070300d642d0300ca000304186442c0460b40c0d4280d003c1540d4a5002461162408035000b03400030380000f90002d01440f04880100032a04117580c503140014000c54415030410520710207139620040000c1a043c03900c5002c58802d08588507100300442c21805110303003a4400050401000c0b4a00300f00301030300b0f2925000d0800d0f00b084805031291841183d020b41c10341020000c903403050380d0540c1d81010100c03840e41c0e00c60850f51900f01450402c455144841e002d07032030800159001e0f0103031543d1414420054540755003076030001080d1500400d030612103180c0e41d840d060140e440f81c5038100c0750001c0410201000724014a50580080d62080c00c0910250124002418440c8d8050046080d13410300b01c1e28 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 185729010 1250 185727760 185727779
    0x16090212091b1905040c05070b070c0b010b130801050a09020a0603090312050901022b0b0102070308072a090c08060603041718030f0106061709100b0d05160906 70
    0x402220411812802551030140d251200640d0714840303c40e0031441c1c1c2c3c00e0b101c80c0410102d594602d0302c0800b041001810320240320a4518641e4400d80c10700d01142080313041c0d80c0e15000001c06205032070a1107004102810300c103101d0300e118409404480003c001c0c600e84040400d010b042c40000c1a4060a107400e004640d580c0f29010f4181515003503240c5860140c420707641480280750040c0000140e550034000d820300c5405502c01d98030070002104011000f82101814601110b00c04403940e4155800081c013000050100400d0b9002d558100700000014040503071071410001003007134000c000d8006048040740d116150b600901003c103442d03071500280e60759041070007410710041d00c000c0d050104200b00e4011041055000701000c0c00824082c90f20450820302080c601104811450426510741c1e0b82801442c0e44010140340490002d00150100e052000b40c1c1502e030f5101c0c2411841c441d44942c80818280c4681c9403080020798080102c40c182400ea0b5005000b04685004a0750010f0400d503000500252 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 185730260 1250 185729010 185729023
    0x4020d060501140a08070509040905010207030c0605010b04080a0210091d040506070f08240d08120901020901080a0e15070305090606030105010501050a0c020325090b0d0804050f031609021209 84
    0x2145d2200812034489a9007034540b134002901c403903807058079040001d000403420f00180503110310944500b11500350178507005003602c40503041584910310901c02041816030002e00c200c056a0107450b03414003a50f10203002c0b0340f00308a540155445e500114181e040006100854900c070f00e00400c240d50154031190412120420b01c015443c00040c80030022940c2d0708507215007203440030009403003030000031b182d0404185a80c0c01385400340c034018400300f10101120030f080b0240354840c440100031440d0110460010706031201c05071030000801e95420300403130740c07081c100000a4010440c1d10201c0f10f501d0315800080240204903a0405140074100115425040c14016a0b05035441616014248083d41c541140c40f41d402e001c2c184d07414401c03942c082131503400d1040c0201c1e50b0780c6c1c1021012881c9007020611419201d10003109030003402d1341d2507001c004c1070551099900b91a8100e4070112241500400a071804c154a02c402c00854102c1c0c0c000176040304154001c007004121180032050594032131003216201d48 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 185731510 1250 185730260 185730277
    0x110301021204033b0f090c1615050a020d0c080705160c0f0303030b0907020a110f040b180601170108031803030f0a0909060b13030611070204020d06050114 68
    0x11900c8001c50b00190181c092a01c0707625070b110800c44924404419410680302c1e1302450000c010002c0711184072414001c1641c80152000d40300c15210b03040643d242d800c148580c0e80b01013654001064400204050765858210b4a02003680074455030410070014002540100ca000016a283c41040243c007401200194032501d01500ca01d402c00c10340280c215503001101404546c110302040c000b08002507080c507000007846c000d07540043e00f8038801c07050025072140038001c681503510440c56240050910034081c020304034282c6850103074800300d10200e0050000345120070380c405182c040320200e40c4a21903040d0300c500802d03a60b800b65100282d0f0f010803417070021f0044400c0c0d50010410720b17540c15403c07080b080d080c500c00303000c0f60310f0402c100c2602c1c5081d400c0004001c000800301642082200010300610020780b254080c1e075031030070b40d402d0b1114801a070a07100c001e0400d602e403241e00b06403032049416a8007094000d80306566845510807940000c1c000f5014040c00701d000041014165507051003070f1032100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 185732760 1250 185731510 185731537
    0x52512020904080306060405030f060610180b0a0c1208040b070c0312020310030f080717032a0412052103090a030e030c041e0b0f0a030204112511030102 67
    0xa490b642c449088a80c0300400c840d03080b0b04200300c0052141c6080100d030010303c09a40203000c4070305043c81081022020707614507200300540c41450b80d8202c40e85c034025a04484040e040103641e10a0684280e608859254020340380f41403041e210700c8642d41005889100724442c14040c41c0790799179210191810032111201500040508009034503c0a25500564110f0214000702400542c1ea41e40c0c0d0032503070340650040f03801d42000710703100c0100300c2c12000d43e18a40b0f00b40402241035240c04841c42103502044e03011000d80020a456030380b001c8108604550241c60502c241a21610403400c00325980d40084d10191b80b8082c08114698103c4681d005482c015828035003d451210b80c2504d04a8150030310070100c9505004070442917000b41e58501c56003c122803034410b445400b03194120101c049514505443c4e001e01c004c400c0c4264a652545084c20550303238111400601410030050f00d014034003e640104800070b80300c1040e003500502d45048140510702c82e003600c00c2801c2000302814203030f020303406801c50031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 185734010 1250 185732760 185732779
    0x4060210050a020c0303090f010506090f0a0f0b0312041a040311060c03040e0709090e07050105030c0f070f030504180905100e01020c010f0c0e031b0906060705251202 73
    0x30415008150081c404260150070900c01100301800c507803040d218445540e1060b030000c69040c400307001c2e06034800310465090800c5e1a1040c02a40150030007050039801c996140e1011500800942c40248126006030071501180b2110660154946c401c1c01182480a040d1080d9002a0b450070100e4099039484040018000444018055550020034249103280001e11010610401030010381d803180000d81e68921003a03280c82899070460307249030082a4107401200c2c042c06541d1300281280d4004550900050f5140c120042c400d0280c05040c40003000350b40c401682d003042c5a80719001d07009403060b045241c0c0303240c01d244080004542d20414020446e03042100e101c4042c22982c1e101d00c00240701c0070300152810090549d607034210398041c00e05140b80caa03030703070807500001d503121204950783c040503801003d01d40c80d00a50038021346440b03c0030620810a44000a40645070030003500c00381c0d5441003c40d101d45001c1070040c1d40d042c41c403490f0302000000001c40000c03041440001c40e109190040d210820 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 185735260 1250 185734010 185734033
    0x180f03090406140f042d150506071a06010c170c0f0a120503060f06031905060f0d0b0414030c0106140d120c060b150c0c010509100c0303060914041106040602 69
    0x9807151050814040c134245144034400261141d40944504a10b800040c0194420b1402e083c01d14060300441c9c01088148100400100c207801030002801c01e031a40c1400301d1b600d020048034050002080105000445001da920f02e140141c05080e260303903084103480c407030381c401e1032010f580e401c4014010b8054103081804101240c045d200071a0480300c05071110044000c0200800c00940c0150391400b04040740c5145612581c40521030305401c500301703d07050b030060728a900c00590a400116005401c20380000046000c10520210382c07640300d03207104240ca88400b511002c882c0200b0261040d0402c42c11041d1400c2403a2501248040201d031784044294822485030b00b040b10b1b10301c51000f0445e8402c1d40e800507120f80d60b40b98500302c00c1500c450f00c02c10703696000448049080101c0700c040b450500005116103132140e59108808041c00b151442d1104032495076040480240440d5441840c0c613a14002401c03e100c464101d900b031144d03020351140a4070100200c28000940b01d2403241400603000100380e1070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 185736510 1250 185735260 185735269
    0x90c02031c0f06140a060e1e12060c030718050a0608180709020a0e040203100e15060304120f1707180e15090a0207020612180f03090406140f 62
    0x884440194005020301c4214041e03000c0718504d400186080c035010035000058640504c60101400e079a207044101070b405a40410f42200c012142c0e07440040c48070400307101944903604003c06a101c0042220090305000b052149558030503508440016207800016902e6414009043e04488024081c110440c0c0342900454190f10f02800001040b0501c218000314035a007002002e000d4480c903800140e41c0c20340507402034410403064600a01450040c010044e03044c09a410220481e50303840d500400e661b9550303c8000015040b0540140d218101005000a01c03503040d940b40c0c0d004140da1a002c56800ba02c05080e520100c0340b6200304800c0c07072038800199196110708550000d242c888a003440700a5181e81c07040c00b00010850f50403502504008220300300346440c10300290400c00d802c60440c5040750680200b0311070320820100400c440c40344070104a1850042c09408911403859050f01d20343c5150780441a1a60320581c2c2480c400c1d170074140d02142440b41c102829001c2c00000b0188420f03c0d10050601 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 185737760 1250 185736510 185736547
    0x3030702040e1905011a09152413031103161a130b03090601051002070506180d0501322d0108070302011b0312050901020c070b070c090c0203 62
    0x1100c80c014643d035001c0001d0f02540da2401140318900104500100c000d55484800e0708030b0b0440c0c401c80b4001e003030000d0300f84080080554050190707115881c42105030901841980d50001c694141140010040700c01042d402d050f50989110341081d90802d8811340405942d005003c100f0802c0241b24134081101005440718040181c5840080600307001d040791011030031401c141c2c0492a0740c4800000c202d0000d030144103141c0540001c030340640d120f15001000a542e081d8502a44c1e02480e40018105190481d045031071544a80041c0f039451940103500c0d240313010300b500e84a215100366038000788041b00e00d0f032592414402c0400008441150781d90348240058554101c1c0102c03c802d007444600074107005091100d5000e06a56002800d005240d0310006003885400a44002c40c000c01a5158000992003103103d0204054480080790310b4407525103480c02445500d80382e144e00e10072100000740ca000307440083c0084500401c503c08150360b0740c110700ca00b95040089442c005806c100004482c0d1310044140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 185739010 1250 185737760 185737781
    0x60105250507120807060e070f060302090310180501110c1b2709071e120c0f06090512030a1b0f0f030905100e0a090902011106010605070203060112020303070204 71
    0x115100c403a9150410401c030342200106130f500f5040000c00d00f0a0107224080c103d5201c1c0070b20018201d103031502c601100f107100790380070b008109900025458055a001c214940c29804000c42c10400101585491203403000311807000c8441c2c0d402c1466150203542050141c42d141005240540352030b40900035034422090003c1c5c00a80d00200c43c1c0c1e01610208070749114144a1040d01c680141d10b402c1441c0324600d0603815a0003442200c050056803440a5800d00380c3d981101c01076204442c0071400f928100c800107869070001101e014a84100081c02a408008081114425900c2807407060702c05440c546c40b0311031065002e0108001e410341c0c0c0002d0504a0803907006601036038031044200074035038450f01c1d1034040c1c0100380c001500b034420030b01c410725000b501e562240105007004c00c10011a800400c5001c980740c460030307100a0707581001200b90790190624503400e410b13806c15038141c1e684814025144e5001040c081c0d001e880340b1030000c20034045c0380101c5d86421350005d00840c1015002d034204000703400310b00d04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 185740260 1250 185739010 185739013
    0x3090809010f140309010e060901050412080606192a0b0f04021c05030306040e0c0906100212031306060602030304170d0212090604060b0301141603110309030c01050601052505 77
    0x150b850602e50900007850003000c801e4004203214220347d084a2800074050400b4001b640340209000000321000c1d074010000019040100c802c2d3b80752000a0910b0140c40040780201c5001c1c1e40f05884554031a01d15840e0094482201b0a8102012181c0c10341151741034005103c1401d840200e00140780c200441135100303100a100b010710758180ea070751003031070b0614420489040e0710200c2401b07050700d424084d0400c00c000c0d1400600c41651032000042030000041d14060140c0c1041070040d52442c800d11240b041062034001c0c0913603d082c6140f00000c00d02c0c21a801341e0b0000d00e0100085030252000c4102ea005a400031003065201c090b07200211b08960042491b00801c550801031210003a5500c0c07086442604000050610b515013404c154040d142a101c003140309034907001d00d6410900705552540c0e0080c01c45095000c6003038411501703070b000b02003121010000240200401c50034100c0000181103041c4424002c0c0100e0b11080019140b6004030080144804261004c11011a03502641c40300194098030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 185741510 1250 185740260 185740277
    0xd08030901020712030501030b070e1c030e0301020a090815100b0a0e04050a020d0501080d0504031b030203121903060f0302010f120614040510030b06010804050a0b010b180103090809010f 82
    0x44d42c2000741070003076024602003034990b0010020701541b01c680541c06089820300100c08600c03000058040c150b00790a00c5000015801003606061098192444221019000b15a1038100700c0d40509299002d21620009204100c5803552044810380c4481c06032a200c440700f00c01c6810002400200d400c00c40341e40003080101102d0400c241d44a01540780101180b441c01650b841b08581c900081d01c105800441541c1c2c45803003018080c551003400c49080760b80103499050702d08062001c0c1c80300400e05904c02780d80742c4900c2525501c1d55030060011301408400c004a0011084010403d40617200b551149014441c01010f040003d54010400c40104034854504104116914a0b1850450710640c000310344035405110b0031050b81c04e1501c207207a00700304145801c1a07120302c1d50390b0f00301e05604002e100e5410443c0240c08a010081c0400049040310390101b1650281d41c0c450200280f1a0048214907803d035200800985065000e0f00c5041c15498201000603e4030205030019207440503000c0c512400c002c02c0c403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 185742760 1250 185741510 185741513
    0x303121807170d09080c04150308030a05330d02030a1202070810020c060103030e030a0803070201050429010504021c0203040c05100801061b080408030d0e06150d080309010207 77
    0x511044010b042d1551072241509090641d80e807820102d07480c010140052501d081c40400c20006030800c0000d0200c601007000d02240743c000a11000540c0020031a50005c03081c01302119894200310b1150300200d401010b0324111260002c010400c41d000084c0a42c0500c14000301401d1005903011143c1c009822107141e6491540e40c5440e400d04100340400680000c1e0b401c2c400203030244030b1008a140e5203001941000c031202051511800d0611000701403100880300400280c806000740c040d829008004561039242040c0041d0282030200c804440c0d000058004031802a0081907044240c0c440c111040d5060b030078081844002e61041481030000030350026049125055030000318810b504c240140c030b02d9a031414040c000c0a0898421410621036810f005000060f800b182951074407071a0f90311149900034604040c4041e1049401c85081c038040040e00b481803840c1a00800385c101d071a002100c01c150390700c2068400d042400c60800c3d51015668240e81e0101d8500c030080c640194125000501e4002c01d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 185744010 1250 185742760 185742763
    0xb060703030c08060a060518030f070303030204061806051e04080a05030c0d0503010b0d020703030209090c090a06031a01110c060403030c05010c030207030c02060d061a1e070203031218 81
    0x85004800098070760081c01d20840d80480388580008050340d913007a496060401c00b50a0340921409404414a058400d040664003046038518400c9804203550304652607040040c0654410b020708030224141072031600d0316041700b04a4500702c2d8201e030307143c1d0706103050450b11001200082d4407042e60180c0901003c02d9884003405001d0f402d074424001140da52110701c0c5175500307001c050404401800000d20040111400714801c80d26002036504005a880030305190907070090140701100d903088009070040003058056140107080b41d80e03040342e00c16a40e940d100800c80585009000708d200001055001030825405a481161351030b540e1010344401024040c0841d0040d0015402540041c060380d034902d00740b180a11903451076101c20f2400354030340103c684000c0c01c030041041d4001d0003520300144034241c0c0820b550080c0082d0400c04c43c042c014000e07120100015400000510002d4144030002c03101e10040c902c111219194054055401c00c2002200031049820040c41014102c07080301c04141400300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 185745260 1250 185744010 185744017
    0xb0a2f0a02031506010206180102040b04090e0c040c140d020c010e03120f0601020a080a02030d06031113090b0109090f1208070305070807080c0c030912030c060f010f0306050a0b06 79
    0x4000142124540c5004052800100d100e001008040c4202409040e0368003061942d0300c0f0580069402c011818080007030300910032507020450026001ca40400c000400d034000c4000c010940080b82c400c4403111041008981c86940944049103200010281113403100016100700c1060316801400c00300b242d801c0320f081da040382c01c1a21060304002011101003030400e201a4020944141c00540743c604040040e584038401030000d403900d0400300780841a58400c00444a000d41404403d0084991b01d1a140300c070305400b108034a104045460b40707018003000300c2c41100201178214800d0883d59181141020003085500c80079076840300c4110380303000428043c1564004030b50440d65402c441e440d000c0001030440e00050300d140700700080344d07003070010300d59101412540200c90084055074490031941c4180c0703148200109150480c14038003001c0000c080100281a5444040069490070380d90300c0f90000807040b090041600c0c2080d006400d0000c81e403545d0005921204181c3c4c0080c007070544600080321b540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 185746510 1250 185745260 185745347
    0x110301050f0109050703140c03100807060203030109020f1603120e0f0a060f06031a0609010b0403080d0f061508041103010908040e07020a081801020c040b0a03030804020f0402030718050a0b0a 84
    0x94000090012b04c200580c2080300506009000c2d10100d818010000c3d201d1006200d00c00005030049048001803154004075048628051016412040342c3e150140c0b500a02c58510492a40744c00c125114621010403142c80d14050080a0902420b1954800c0c004084030700c0446480d0b81e641c000480001d00040000c01805115140110b50b85044c0c82006058041600401000e082c207020820019041e03005442c1c1d03182e40000003142560701240000300903c015400303241100e4514500907010b9400854180c000d5014a040e01001200c44003414240d1318441801446082e003004200314210703142042c140c00160700e04c10f40d143c0d001103803070300d981a40150390454142000b820307809547d5a010010400180c200f681e0612014000c10000741c2d551480b84806030034002d005000500310b55664043e22090100140b00b107450b410402c038000c025100945d4400c44815a49401044514000c101c400072591075001c00c5203002c44a1b10200e42900c0740350021031150043c40345005c0a0317000c0b210001e03000c0c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 185747760 1250 185746510 185746531
    0x6020a02221415040c0f08040609022d0a030f030f0311030c040509060d11100306120807351b100b030d080103050309010e0111010e0a110301050f010905070314 70
    0x182016419410300422040e03140340b04519021a030f017215600030908405003451410300c011b072652a81003520142100501c001d40c000d01e902045480205030341c14074002544c0030240c4280892204080c0811500240400f402c40a1404221b00000348120680c003c071a2840c9408140e881c0a10740396042c80e0429180e0800110005c82e00780040c0c1440c00c00c0562042d8101c4000541148946540b6400d004040080c1c0c0101194452a42214060b0700003100604c514100320320580045d00382214140c00c001011201d622840011070070743d9941c0c03e41d015942d00041c0107411601d5015000d040c0a91040030384000c02203c2e040001210030090207990203800c007110012400f545010201401d10038540c88150901c00c8103c0180302180700001610107140d401c2c01d042203a4001c280050300c803d00010300d900203175800d01300d010002800218445600511508400341c410644404250a07243d044803a0100c1d0304002004210072104d036006103410240340e080000750550714a020404440b030444e90104407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 185749010 1250 185747760 185747801
    0x30503040302150a1e030b030703060f050112050d030b0a1d04050706020109050c060309031201080c1804020d02010f110a050c15040b0a030506130e0d020d020706020a0222 75
    0x80d07050880c2848581c1c4400701c2031625000c50380304045c19550f22216407281d00003e1400085403540039501580c003403900101121813055407440c104000c0c00606000501107410003000091410b4450002c858050f440005020030764410642140103103201222254041d03c0d00d000010502d14840b0144034085910407040414605400d00500d0308985034000b108686c07400404c1c00110b240461950a009806c6403095901d4035007074501031660103280000010307082d462000040110300020081c5041e0020f40702c1c0010768a006100702c00854003118040d410040a1034807000641c807030400030310b0b43d131040e084c80841e0b40c1120f00128682000c2030002c5070198080180120785140181a011a9400182c01c2c0b901d001c0c00d03c2048455405041d613208145500d4001140090782e500003810340000105400300000c2d8602c2d07000982c3c865080f075481c00540600c82d030480c099840860704400f51182c980041c003400c4500d0b030030b0003030301184604c070070034010a86c20b0910700001050184103444003604446a40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 185750260 1250 185749010 185749013
    0x806070314010815191b09050d020a0b0d0623123904090b15010905030c0f0103020c070e010f0603050708070c0201050d0903020325110f0102160305030403 68
    0x100c0d121012801a4500352400400c10040005002e00024444040032011a11080c03c804c00c44c000302103d0821786420030000307a001840c0351154242c8000c5503601ca401c01a0380d1400d00040c030310a80300103500305105010600a19500c40c4c000d20100c1410200042c410b651160000c0710951003582d011f50403061251000c1c03c0e4a02990151410b45580c1c01520750108448918090b120304c2050046540c007103220700c03503035034004000c140c04c007141d014200388180c3d10705150904480c82c00b201d184d0802c40b2038225040507540700311807243c1503450280040c18148100300400119660718090b40741015000c01437420110340611048e001000c02c004130b00d01355410000c0c0081e0184240c1c010404043c40c0c20204203046506c07182c05500154079081105110340e80d800101c6552180200e880d801c00d00381821402059400001090790801e12480e11000034581c00c5003c405680e112400f0f1310082011107a01107034903201d50b41000080050040b135201e00301c030003000b00c060703103050b0700c1901da41c0c00100b010070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 185751510 1250 185750260 185750267
    0x2a0f1b030308100b03010e071b051203072a031103070212010b0f01020f0d0f0c0506091e0f030904020a090e040606050306100e041115040f080d021216020a030804080607 74
    0x2c0184c51084445421507041c043c0c02894003000a05940402c0030031a80d0014050f0030100741035803581c11105039000005120060350407a0301c160760840008020720602e403600941208070f984035003145c03424150303401c0355038034101c0e048880d42d182442140400c03c1000d0041e80c90008130303624440680c0000c9140e031000020050320380a00700e00c0314159081141701742424440424068070400403802c000c00190811803044500005000000340740344621414401c9003440098900a001130a01c8841184260048103039200c846241a4840039402030290030b09619054019181a05191400000d00c41e581d1580c50b0801005440603915295540024489410b050000d079911a6860150800030381c5810520882503500502c0a4000c0f000c0040d01c19440d0350303d05520700101d080c84145078650341c4414031030344441070b20322442d5450310070b00c602862074600200741e112503da9104921400c1584242c0b68000428965000301d03840341c44902d000c40080c0000c40a400030704800380003805689400d10024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 185752760 1250 185751510 185751541
    0x90801050f0105060f130302040e0a0203010b061903020325120506060702060304030806030c09180c101709070509040305181801050f0414070806012a0f1b030308 71
    0x20030120741250010320080d00d504040741c01400444100036038a40080030901c2c8410043e41000354014242010407505080000d044640303a40210000c120f081c1d500d104011091040e84214030700030406074030090b8542e00a0303015650052003030f020200c80a80300d45003a0303a4401c4031000080818000c1c0c800d100d20984511665510800c1550003501e00203c6400064090200178001005c0012400010302251800d2000d400624400381550041d8144644000d1071541c0a40c0350307903ca449031803200c16080c608103031030780340715034081d01c4442e011030618100c1c900809000b0241111403042c5a0b000445440f10f000740b600c141e02075078980d602c400200304c05415641404000600c035030307424000e40401403601d1290504492003210a00e040c0402c0e032001c5070240413100d07440106522260208a411504118810300c690070987c2c641e200f0180b0220034600b4602c07a060309a168040d01d40c078040c00102c0c030424610050b4042d01180ca03800840314010b0f8a64203480d0004c600051000c410310028003500d8604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 185754010 1250 185752760 185752771
    0x9010c170103020303090907031401080d0e0603130605070918050a0606050a020c04180501113705031305030c07140301060e040807020406051302071e02220b040c09080105 75
    0x214406075242d5000a40c0c1d90143e805a5031040d494040810344042c06a130048408902c5e5680c030b075050350b03503500045444410b8802120081684111441c1c814500082220f01c6074800181010882d4140c0e00c4080090000812071001d1184000001c00c1c03c0852547c9a652401142c201082c0c601d00704030141c09440d2664410810b00100340020203100b074001c02c0050707456105030307000106140c03a405440c44040242a01400c154138040d1340b01802c01c841d0004210401d8491340103503600f11080d01844042690302d80c11866070140d0041a15107903c00d00065422001c05120340303490711a5500c1e0a0b042d175001c03296aa815500100c802c0001401e00ca0740b940500804030020007900e03152006000700b0701c1c1c00400040c510440029190215a155071241000d007102400580c840308a801c2080000c2d8401e920070f82d6201e103449000d501c00010f40151100c030b142c0c050465841707094800342c3c40840e4129903c2035500c4a0310b960744092030340c07990f10880071a021660f0311402d49905c1c01c180700c0c0c00c45401509 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 185755260 1250 185754010 185754047
    0x80c010905031b0c0a12060b060d020c061f080715050d0606200601141c06020301081e0a081207030f0c02250501022104031209080c0a21061409010c 65
    0x24108104006c0400110513282c201030003264540800e00001c07400e00ca14031010300c0252011500711003803d80050028480c04500b000d85816074070300d41603404c01452509c00d42c03083d940001010701100c1c900030000a185506400d180342008125590501602c1040e08802c00062440b4080003401c1491900d11442040c3d4501421f81035040c4070941c04046406081c0b10302441c2140c0001e00304542e15030700d41401743c0c3c03c07000854403541c44001c41c030780345c00300d24102c10f05160b1988502d052031440460400c1c800769000c4686460004504d00ca003521540082c1118240740d071b10070420030152958020100c602a50b94040c26591100c0100c00100b01d03140070b0301c85070a03480c01c8818003659070001244c4089080c0c0c404103c4481c00c0c0481046103602c50f41d00010301103604c0d5031410117000d13081102d03030080c1c425501c10342d840d45140e0000d000c680e60007881400900c80004050011300307503a41c815031280600560340030403800004d010b0800c615009483d1029941e40d41c104ca1458aa44956a40000f03001c450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 185756510 1250 185755260 185755279
    0x3040306140a0c030e060a150504050a0b01020f0c0607021c020901060917071a0903031912110a080429011d010512150c0c06071d01020c0d080c010905031b0c 69
    0x22460b555200001d280441e112358642076a0300c0614140c6c081d9000b803c00078414040c503e020101c91028107d80914680984140300c5d005003c188081200400302c0300c05880c80342030029980801400b07400042081d01200c400030301120158448030180742c0680f0b502d4440301845480c2c0200c003c00b203420542203070403a42001d4414400d45100d03040c40107c04842c0d000150b02e5808540c00a03040d8401c40c0089001495030640345851160408115009102c5004040040004041e07060060307100340c981b0000014103001c0082c00154a000ba81500e07813480b284503203484510b040c02c41c00110020782040d20345440381e0000e0b030304c0c00d541d105625000d000160346d02e08070702c548000c00c13558031580341c5201a2181070100c0000c4a0491200680c1c60344016401140c0d1b4905080c81c0c007800603590050401c140c01c0821490741019400000c880b1000b0f500940620050400d81d15441581d030801810752805540390100c220100c0c0040029000c00510600300708d8410f550341c15204c4c60541304c0120f00c0e00440d000c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 185757760 1250 185756510 185756531
    0x902090c070201020309060a02010507080109020c06131506030f0b09030405030a1e200a17030901050c07080a0c090e0d0e0d14030d06092004120503040306140a0c03 72
    0x1100820303002000031851075150300042c40180d00314005e0500844c2c000034046401500150b0540015003d030113140c883e002a030340c84995400c1a0300c10007005140390f174440c8c1c0104d1641d202c1c04414101650081c04205c000740c40c0c40303050030103981190b80249c8051480b4032014050241c000f900907081101030004604d85031500c80443e8075003607a1180548900c031842e04518001c000b000304401101e070700c21003041640701c001d00c081d01d1010403516850300940241802040681003038006000d07080c03100e0019810071508100442e85a44500c080c101180104e2500240ca01020418803008070b10840304803080e1030400703400b5021a100301890002d148c0c0519000c210300d5804c0f42844050b5031064038000e6420005e030a00441d0109000b41d180c90034840015079440142043d03001400f0707500030a0701405019018902c0341040c900f03050041e401e8039401c2100b080700c030011070b0082c4003803446501541e05040c2d40780c441c80c044036a0b01c038003c4007002c2c42d070080245850440c480c0d040105181d007402c01402115 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 185759010 1250 185757760 185757769
    0x30c1204060903030f03021201170f06280905010c081602010603030507020925020d020f150a090c1502031b010212150406120f05150c03040803100801020a110601090902 74
    0xb6440b015083c44114100525424801d40440b03c002d4407000d0003406950f52011030780d02e0b0b0900c100d080d15080c003400e850012440000b1408500404542d1000c0103035280224450251f103104c100103814207a9908603000009001303000b803148225054850707079090b01d0401c2d1035480d80004aa100c004592502e48107200103074200c1e082d107484d150191340c0c1885954849140e2904520716104103501c1d030540c19501c3e4461540021140405103160b401e80312201c882c5e00e042603071001c2240c1e02020800c02140011082e0450303910892485000d480e0011300c940c1d5411030406402408042c01d0b00680000805859851160144900030b05104000f1032500e1481d0140440006000d0300152080c4ac500c41480c0003039072250011170151034140c066245203402c0c1d26096201070f0384080122802e002c0e07100c9001e6a071000400340c5106203045945240b56a0b100d07500c4a0700c9034401018000b041004400100c3d186a00744041c0c0b5010802e515039000e00b0f004042c034149401070590002c00c1140c2081401c40044e2107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 185760260 1250 185759010 185759027
    0x50d0915080a1802060c0d12020901021b04021b0c0907080906130203030c070b180103021603030f150e0403080c090a0302040207062304060501080105150118090e030c120406 76
    0x10800d0001081d07107203034103482070003d81c03554003035030259020496101c808404a000304100105840300e000c0d2504005008060340a041c1c41c1c1400b5820000031f04010b14800c911101640c80020001440d01d60741c51158490108544082c10303259100214200b49820028000c0c1d411001a0902c00d55920305036920701d664103070007402c40c2083c032032000400b01151003c2041c0c0d03c0e040c07650743c00d03501c1c01d50300d49004400b950401c0c1c50b401d00c20555101c6030303034440d40244200c0d950200012114100b00703080d074905078080c010102880d41c80c11317618042c082ca84400082030380302501c9814070203075603410541002440308a015011143c0080c1c00c10803580c06030b4406c0302010841c1e60568003d600d0301414146000100080500032400020b1142245032062124005600c51407241d0f070104030a90301c0301c00a030300f00c0e5000c50344482020080c1081d1075096006680c501c1d0002c48010400d0605501c1d405084d00752070360307512060b079103074804102d07a000d40006108040328180b03140c00d40b5040c40d1510200800600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 185761510 1250 185760260 185760271
    0xf030b0915061f23070606090203070c0311030403050d0e2103042601060801020a020f0303040f0803252a050312070c080705060f01060e0f010e06070f050d091508 71
    0x383c041402807841030080d0300c01241c4504031141d03101119004504034601d94001942210305902e070620200e060001813080d01d025605079655042c0e0301300c0581d0192818041d0f040340a1440c801440000300043d02003000d12148202d6079141d144031001e020600845517030b0b040190032542c4c00414100b6501d00b002050714111040130507103000700e907290303203140d46460948400c04141c1c0d404c0080115000505400a2128a565a007162140243e60702d1054070f0303010035200148040b0000b1500b0000c41c0d454001345402040d00040c45050240504090042140000d04940412002d0b0706400d10510305000054501d50100c084651a12041e614540c803482803e405c114a4910036000c0f0b0000b46c0318840700810980d0180031650783c0c07400c60030482d50300ca0044510380c0402d04c0c81ca0000c00c05522900c1d82c2104400f01410044040d43c2200042d218880145801d5400c00c2d8180107880c0440c1c0c1c201c00064801f8010000303040c1b00aa1002d0061112038076400c138000380400b102a02c0300c003c0d44090301da540003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 185762760 1250 185761510 185761549
    0x10e0c04050c0d0501150f0801060e0103090602360a060c08070309030827040c0c030e01271505070201120b030a0609050c040506040605030c0f0a0f030b091506 70
    0xd40d1054890301c801e010b184140c081c03091420b80041b448100350385002c28241c1d45501c031005a48200d00044980f0b4100340505000601140101c11040d4085e410851015106242c054240110300c0d0700e40c048401c5c3c6113103044820301a102e030024411482d0104140c030700da0980da0100410b0808001805441d03501d40020500c040000743d01083c94071588110000e56449020030743c0d0f03a03a0749042c0215104455480c03444520b441d110b000150326142c4501006041551190417000c0d8550f00d003950301110740a052414003a0003000000e03c03503010f500e944481c400c10900c455610b07040005003000520904203640c144181042000d0160b078000f0414000022640d001043d400d2110000c6410088085802400c40d4100780b20441001400308200040c0710b4242c5080017295980d404010035034040f480b40c150103820400e401d161608084901d00d4a108014000c0e00c0344554075404201051182d6106591070f28001302071101940c001d021604001086102642040c1401c00000b8144d40945103022041e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 185764010 1250 185762760 185762771
    0x602030906090d0203030301081506030604030804141e070303030f0204030804030f0302010e030307030203040618080d0e03091507050d230a0201090b01060201050106090b0c031905040e0c0d050603010e0c04 90
    0xd03036074030300b50443c25030780038003900d07100c1d40e445200e2076a50360040202805040340308000784241c100060003510803a00f641e500005a155034840c41402d082012100055011315002600400c007500015410301c1c14900c0207100d49031840c2801002c0314043c07007071111061b00401040000c40c41000944054070380240d0f02c04960004d514042e03004007800c0f680d12080b400701004020b0501e4040d400745104030b01500013032080360011051031241d0507100900030820307030003400f0000c4907030041c4d80a140040c14079001c03640b502000900060400310482200d0650750300010311075007000000d0141c6803080e1082d08040e40c0e010702d403940c500205030102c1c1a8060142d00402e43c8103010740300b50064a105a00580e903c40c55584510001740680824002c1e040400d50b400e00c001001c1805000311211654030b00c02450908c41407020401d030400141c20080c042160600022a2250b409001c2d640242e030244941c582d43c1018ac860002030707450040050340f081e450301032405030843e0003268072407a080044600189 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 185765260 1250 185764010 185764027
    0x60602030f0316050403050115051806090a020a1704050f0705190603020f04030212210a0215060a0e0c0a0207090b060d090303180302030c10050103020a060c03030204032a0e010602030906 82
    0xa04d4021a0b001400c00e60900c00502400c24900324554143e0740103032407101ea20402c0f6080c0401d152016180c2c0c07a0485881c0340090040e54480d8043c02e25038020b071070181003500c3c000740b007202044029103064485400140010040c6442001034000a0005441c1c1e460780b49404140c40300c03141c11903c0303543e0615030000b401d020204041d40458010316070041150500324460080c0956072101c01c0040c5140c0e0390901e01009202c10030006130703000c0d4043c960083ca00010340c008071144001001e022140c01c01e140c0c00c0701280c4807030340d200440d2040070948100c58842903414002883c4c5581075015601c0c85240c42c1e0002e0f103030b0325030074122820307002100700100b1010001d02d421002000000614440144043c3d10202003503408002410031241c96400c485684000c121518220307442884020351059500d082000b000340901c1c225120b09020703040043c1401d503a502e8103020320391840c10458208100d401c0d94041050040c19101c060000b40c10300718403c0d810484013a44c1c0b03100d032085a40c4200008a0140d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 185766510 1250 185765260 185765267
    0x3080901060902040b0a02062802070203010f050408030a141b180402130302090609010e2e061e020d050f07050c030106090203060108130507030f11040c0503010504060602030f0316 79
    0x300070001d50b00215511507550003a001e0300c0d0402c541640040c01410b0100d0421828111203000d010716444407078040e0508001810020350002c40121781554949203041100300042c07040612036805011800d66a03c0c0081c1d082c2d0403a00c101142000b03510f52a000d0094180b0041031601007441b0b03d02800c1c0d521545011500c2400104110302a401400000d00d240d000c130b61050264101d0340700356462211070b103a2a00304482c07140240982400e40b10802c000617030005084000d42d841000c0080c444910851004960401c2c8140790002400301e44a001c0e5003c156122401488101d11f0030300c0641001042c8034070040083c414145030803016440400c040040c0301091201c0510321000500030401c0c1030b9034011807006508100c40036800700700800000f40140003c00410113841354890044c0040c00c0c01c0d959019040c0c64000000d8030740b0040c28004484c40d07240d91061014812654481139140c9d03140a00b00001c3c0d44590b0000c800b150400d0041c05801d40350303041500d0304104180e1102105084044046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 185767760 1250 185766510 185766521
    0xa0c0f02090106021b01020307050c04150b0d021c0b0a1415031006090614091504050603091e0a35030c0d06050913060b03030c030c0c0f0d0c0303080901 67
    0x81e502444440000840c140c001a02168600c0e49070380b8840e81ca10143d00591312405903420141c80ca4201a92aa10604d0300c0c3d807102c0404500807803d402c40c192100184001c64001c107202082403580040c0241d8030081250b0580309001282005008003844680442c10781482489101101c0704d0815514001d0303941d054644609040810b003143d02d85c40d189241591480041c45950041002c0b040d000c80d02038801c400052000303802034156807802c00070809014502030081c101142110061101040d282d490b09c0045002d100104000c109800030001002c8040011a91a10050f0b00600101c00069041a208203210160030106003c0e0390700c100301310f040f01707400103400403422400204100002c00a400640340085002c4c83c10001643c90b042400355040d4260b80740728044c188801c80000041c01e41e0460401140c020b0180e0b82400a040c4000b45590000c01d118869034002065041442c1003030b40c10900310500c211880c040300c222948030141072841d1400302400f041a420005800c107202500304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 185769010 1250 185767760 185767763
    0x15021207111210020f0d0501050d081813020a02030304050d03060f050904050c060c07080c0103110f0c01150801020d15050a05060d0b03070e1e09030919030203061f0602030406050a0c0f 81
    0x2e642e201702000300111640d2003da02c0e40c0c0c0f000d29001c000301d000d003030182c0d138043ca05034041400c030700d0602502140d040c00e1010f084129401031080c641d19010344aa030020f098901215001141c0fa800d16280260070290220190803c1501c1c10354104603080c01c05084c481120820380d20354009480700c0c24803134200300038000c840d0341001c1c000411244101e00010940c1c121080384041d0f40180410341c0044064a0a090b48a544542c0a1041c10600204c400c02404c00d00a000b0001038000215443d07800d030400281d1088010fa5400b240c1c240350700341c1500692072100e02401009160f182024001189010315004181c000c1101096020b040241e66006c07070b404030303001012588816560360100846050440d035001d000c005403d49028000e1228078414050001c10380503504124541042c0070000705407034685810003d82d0800000540c4040c440c40b401015281c200200a044022a90140d441241c1c403010071503008000401645034000142c8282094a14105000015504001c40041941c050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 185770260 1250 185769010 185769043
    0xb010309021809070e1501202a0103230c0d060b041406090306160c0c0b0406030e030301031104090c03021c021f02210c07150212071112 60
    0x48200b0400c142000031446203220004031140c5a4441e03e503200109000c2d03400725240607804041c1c00640d0300a0010062030088903071032424000002103a2850403691130b0012401c2c800440c4c2011700c0a41242e1a171401d0082800d003480702302d241081c469404200d044c990955120b00d980469400220903045400c1c007003a5510a111154603401d43d42c800350300c28405c22000f00603034400c3e014903082007010f0301d0201c44010301a10703c5035030300c1032480504ca0601c1400420040311400c2200020480441070003d0501181803940b04c9050900240455900710f01d0a600b5034804c0c001003000544145007244110f07015100860542010b181407903c0e14556040254410011030b00101109444040511028000c46908101d5402c102d101e0344800c0301003d04800681003110320301c200040c0440a084400018960b0b10300d410a00c04595003042181d4001e55021362000700117074140d5904000c020384c41000c0040003894540b00d80d46864403e09080c040d0f60140a241d01c96505191040c400003090044648 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 185771510 1250 185770260 185770279
    0x3050403170708220e190c031b0206040c0501020616050a02100609091505010b071403120c0c0106140a15120f0b130204050303030c0711030304060906030b150d0b01030902 75
    0x3041d01600154510b40d13903e296810318002032183c0e443c1d2400c0340220420684811316000030a030b040050000a00504241515403a09220745000410006145500c0f507025104a052a280401d10102c150344001e045502c06010300c60300c45000b07920070845410707500f40303207640e0100045d00b81e00300b000e0b1084036200103143c8440041c42c0c01240d04007800d1240704040d200720004e900301031401120700a018403140700d14184803150000e0f40c1c00b5406010107007000112400e01d040c200e0360800780314046448503100701020805055080003401224050700300f2070006240d0f054020082041125280f00700c031040100d0365100c031900c601480300c0c0612076281040500030038071f0607901403000e0030720f00043c61300868403014410380000c00c40c400d540c103482c2c0040185d4510f486d011224440341d000320b041a41d201514002c1984030b41c1e03081004200800094840c20030703031413408401504903001007a880d4040c100b8000c0d005412401034040b6036035800e01007400101c803006440100d00805d40c0c0c520003904114500e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 185772760 1250 185771510 185771527
    0xb0c1c11160e09010608030301051302070204090c2301081512060c0901020f0c0a0306091b032d03090509090c0402040801060f1e030b1306140601030b060703050403170708 75
    0x507005200b40d4000c0980ca1580b03443d101115401c07101c80344180c0185800c10310042c091842c1c91010484490201000581400513580015003103d214207011224112002c004000840182e02e05c80e5209080341c200b184280d10724170002c2c05c80e01004059076411214117100d550141d5458160200340f510704c00403210707545015010107078150312503052240036100d5900d02c2c00d20400001114400410701030106040540303941e030751001a0000607802c5800807005820000340588a0510038000c501680b021844ca1003c018000701d014090441f0580c0300d1640c1007800c1c0800d03040000700c4d003100c0701590940110390300c52651717030708068003491003a0380540002130014410505400c54815100c8100124207c00c0d84e4000d0004c10042010107211285076801d400c20201c0d140c0320f44258080c400d811030000000ea03075030314101260a144919402c0340441c4003408070700d50303140c8070361500c0f28002d5503403d24010340e0f07440240c9240507920000b40324510604001440407085019120540d034480e6145480704000e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 185774010 1250 185772760 185772793
    0x5042a05010806190905060303190207050f0d03020a1b1d0603010f020405011e020304050a0303080f150319020d05030705030c06060d0807060b0415080c0a0b0c1c11 72
    0x51281600103260040402c44030b01e416650b1116000c00302d1410a4481d2070017004001412009003a158940020300a1a44045c100718140400e00c0302c1e40e0103048960700f45403c2181d03614a00182d02d0080b084203041c80000b980004080001c10b410244003445072020611300320542c0050341221010b6404082148800301c04620380034003641c4103e00a00c130914025041008034061403003203e0000b001116074100340690a40806002502441031328039154aa10100c0e038001c066500071000100250100140804a250301c00e80000844580765203000c144d0700000e564284004078109440c0100384d4140c21955484112a4840c0e0301c80c003500e07103508460406070349035049441260298003d000018895141101c3c0c41b43d4440d03844503486041c004207031180780040420b0481150416640c50409075009205031003d0000c04d81b8200611541c4080400d103c100b04503988030f140082c405001c1c3c3c60040300c020405140c502c000003581100b40c16030400846840c4a00b03802c4101ea400b03540344a00d1070161 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 185775260 1250 185774010 185774093
    0x30a0b040c020d120b0904022806080a0b03162114031207030605010519020c03010f060501031103010302060412030c080c0102070c0816060f0201110d09060b010801080d030504 77
    0x3e054491024104010003024140e62035034003519848107411000030014a840c0c240341d070009031214507103844804800346040445000c0d82008003c1180c00302017203000007450144070301003101038000d00303501c500d81103034011070f41c400307014141c9000c3c12003041400410545a100c216990007030704401400321945020f54a0354031415400368002354a00000d10303100c0c021301490085405c103a5800d850101110412107090907021328079001c5026001304561266024090a04000740e0780344002842c91074040003504913107004242c040c10001c00d00040001d43d0720482620300325030340036508001507005450103c0c0c5030703909608020004032000c500c014000b00c05501610343c06104843c00c03c2e2446d00c9000982c3d881c140c0440380c40781040f08490074800c5501c10748101012148600000c9404440702074801c01a401c8041d00480c00c0350717901140b2041c80341500480d280c44000b0b090002c05941003480c0c0607166203032440341c0301c00d240d02c5e2808202000203419038801c07060181e240d80c500030b484c1030b0004850840c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 185776510 1250 185775260 185775283
    0x1230606130e010609120809060f0909070f02011a060301050f060405060d050103050c04020f07020f1c08120601030e07030f050a060504050102030a200406230309160b040308070305030a0b040c02 85
    0x81072404041102c01015441c1d06c42103400038002d030b04088800341007068a41c4402900c1d005000c06215204c069100c5a00050080c03075591501d189825401c1c60003400c541c4800264201c10084044141d8240c40e140101c906540060702c0c04411100c624002c0f540c10b2241e68000c9030803110000e070400110b0443d0744800d060720302c00c2040d5240d40f81c04004120980c0189501c006540308100000801440c4c1880150000940604006000d01c107240f101056044540c0c001e07202c4c0c410004007010011180d8000503404902404c0030001075500418003541c8000030f00000b230130006100e03103007805e100d02049540006540042c06224515142c6031880c040c0d0425561800c1150401c150264440100c5060500180041c1c400c07030b04003403410408660641c2c262203508400c00c600f15030315050032120030056125905040080400c000c8800340520502515401940c14007001d000910001c1c41020403150031941503d03250361aa01c80c41e02c41c0009000d42c400443d81b040c85c0084203d43c49030040f41418084 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 185777760 1250 185776510 185776517
    0x70b0c03040915050f0d061d0c030601171c030b090703090302190201051e090607060207021801051011010b0d0b0108190203060a02070305220f0801230606130e0106 72
    0x10019a444a0f50400190080c26440780340c0d9000c2e040503080c82820000505c0c01103078007003128102000019004001c2c2c900d0a10640c01201002e031143c142044030b40d0040904090006090010106144c0c6424560a00d00f101c00380041c103504030740c3d219421400c2c0070f030740042411206061100c00a8014260a04110050301802c1e040e12030991040021101303054060319400d18001000040318502a1306082c1c280d8914810b0004d4001e075100d040c050b00580d8403034540107070b4801e9240100701940c801d41c0c900c114601d0005006000d281c85103015548000181c2c185848480102038103d4050308904040a401c85007614100c8280104140c186048074151400e80e03600020603446030003000001030300a90550710510102d00c2d0310440d540186140c0b4020700e456800e103088058151542c030503503260030f603038014ad000f4207014021903811410300030010780c4000c1080b51650300200d040f94015510f466280d07220480000c0e541d8854a01300d55079050580103500050340c84985540c056038080c003690000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 185779010 1250 185777760 185777771
    0x60e04050108030c0a1209090504140105010e010b1206011e030903180302061b0a08160b15010807080405030c03040305160801060501091512020f070b0601090609030f05070b0c030409 80
    0x1030070000f0007214000d80c403070303c040d01091201c0d8541d0032980110410348010170100c0e400000b4418801d100f064000e07445040c5144029002074101e60131356006800007603400b41c201004100c054030b000200da03105040e41103240035075a90f040043c0c543c1556040c1d55442512640f12400142d54154006003420344262100161a144d101d81c04006602c02c3c04000d41080c01088800301008143d00c0c200e42c070104201c112492200c0c3c13079449840980090300040421284403a11408004560314003603030050b56684404000c86040d00001c0400c580540648184611000410b0501c801441120486a03900046030343c0d5544c0d03445c04640e241013130100e01924200410001c1411081801b400c0d08444050b0345d04a1140d0078500b141c1c5020591a5985040c00741c2c1c0c1c0100d00b1460100e001500d4040700c4003003210340382c04ca1400d1268810030028421410090041c1c028040241c0200c2044141c9170424442e411455080c50400c0c50b101da260403092070341d1004034442c500340000000404c10394500f41001c0c0321 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 185780260 1250 185779010 185779019
    0x31c021e0118050d0801231905061303030f030203070813020f0306070903021203120103171e190e09161407050c0315041208131218050d080304031413060e040501 71
    0x1000305280f81c00100700c6001002c3e000601d488d00251640d0f00035403110403560750303441d070004074960311804c032140400014800400074540c000e004411029085d050035461454040c1c0000c00046006040042c0700700740d0185442991540c224409120030b01070125000b03400c10000151201c070852004074850511148030300040d1001200380d901c1304140b0000e00c40907900303513074803072030410000840820503207400d001125095207081a404030501385100c60315a107000c0240c800d5103140c0000005000e0048100141c0c0d00368a2b54154580d100300281154095403550480c21a501c5140803100700d102d88020410805000021410900d816402c80c215020900700d01c1c107010311101d0803100a8414004042040e034018014512140c4c403600011412851901e2951048108040b2900500003d0200421040c0c0b0402d02e50210010300800c130741e5a54180704035910300d201440018030007801c01c1441e0751030013080412041601e181e1511007d2091003907440c3e540042c084117640c1801441141060000139 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 185781510 1250 185780260 185780279
    0x5120316091805040521030a1d10050c0d11040509010806090a1b0e070306090608010b03030304080f0c0303070e130c0c030804050709060801050402031c021e0118050d0801 75
    0x50840356020182002c5a814200540040c00000d00603207250007086030b8403c43ca0004541e20200f00b2500c001d89849042c486c00100444400d6402c00542c03c480c83d6003041516000550000f401d03680341404187c0e95290350f0300b01d0140c0155103504054509244001c42d50b0709440b00500f090317801c29110322403a0780e030714000075079103074010303900720004d508500107010200303440ca00e00403100804100c00039151503482e00c01490107c4200c2d8030f180060356800307082c00300051601403c00100710081c0240b28140301c0d4800240c6a10001d80010f008040000300b6811010100c4280e40d510020340c4180c940b6840c021101820380301c401e4446d14440c2d05001d01410420849101d0341100116642e6030700611119994250b5040d2800b41c82070b030b070034460701d8000100003440e40110400b52514200115031340c102441458544542460b00319110f204d081a10300d502c2e03600040700690319030101288040c12001c2c0340e1a40c01810700e51035969031100740320b50b000c05004001500500f038500350b076900c80007680e8406406 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 185782760 1250 185781510 185781527
    0x40f0501030c150306180c030c0203130605030a0b060c030d14040f0204020a0c05031305010e041a060d0603061121061507031701030b0f0901060501020c12030705120316 74
    0x400220b0810700c1440300030198218914403603680d0500040440c1c0b80ca02c1070944c005c54080d4244060340381c10031440c1143d4107002e0211a28840c0c00114201141101060061092401a2001c0000200010f0080c1042c0d40040d0007811010300f2041e80c0d0682280426181e038007019081110f141003820000b031040322400080d01c0342d03400c40610126940c1590070480a036201024079010040340f000300a000c1401030008001403d02d501d8044221458640007604c9102012445441285840c1110140e1364440c40000803492085918564440b640f04486000340300340d400180240c2e250612510710610305100901100d034141300c10455201e400b203032201c0a082c0403100302c2d4100714003100b103041006c0044040c08180b4803e040544102d0010300e00a60890401d0744242c1e041422079082c40003c0e903141c0c0b030320754009104d00c0090040c103080030b00203075640c0c24144c10107010340c00d140541401c44c1c9040c010307580000d920200f581d107c0c03290100400075680041e42c602c60480300d09100080042d010b600303807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 185784010 1250 185782760 185782763
    0x50d031e08160e0d02120304050a050612071407060227061306082806050f0109031e021f0c06060602010e100e01230f01060c0f020d0602040503010207050309040f050103 74
    0x1c004069180300c000c480c0d0fa0365008100d600030444281c03d10041e56610703100840303818032800460b180d074900310412062140552100c0c1c040c030401c0141100d03c0d80e80d0344134958050010704144040d1008070325441035074458810060150f601c04070b200c2c0f855180c01c009440c2d5041c100b011350706103044207008101136441043c204220703040041c00200502802000c8855004126041c00701c06110320021508540c508001d2000055030b541805101910740340900540c504420718140081c142181c0c0c1d4003041110604c1940004a44102800c0440d030743c0106403825001c603031b00d4004049005040140050004403822102c003800c0c01c9010414502c148506403040b030400d80182040362035145040e0091030341e03001c4a4600c3d500d4a03103034560141282c820300103420000301420564903082102d0070b01c039030f01a0080d030100000c1d8900200031031000c2031150003654040301e126030b034010140381c0340c40280300e00ea003c0c2e50554004600b22050101c04400f400440034140d030107022052030410b409084a509000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 185785260 1250 185784010 185784031
    0x9060304030f0509030f01090506102304020910020d0f0212041404020c060705040320090406020307180f0f080c03070b1309090803160305071b030207050d031e08 71
    0x200802d1040c1d030580d5400280d810400c0c58440c2441c017207410400102515021a074541c9032070403c002d030030002180d201c040e0b00029103040e030414880c1d40e203641035003050b0241c0543c900700345072040d030300c5504540f5040c100800d264005c508a03000030b502c8595011240010034080210009081d00205070f40c007005001e0039401d4035041c1407018603006d8410181d801500280c1c02c4c007800c48000d00c108003050240c1310a4555a89541c607601c1d0070000041e44110709003500042c08505404e540b03c00d61000d40140c0d1000b400760f165a100d0350f080760524084420200c00d0582d00100241c3c008005074034006840e000034426442907201c05c510b5a444070303140c44194140e40240b404124010b0641c000d0030109001e0108040150b41d40c04690b0151001d90788280c610700e10000034800d82000580c08000010001d042c01c2c0402d20308800701a101d102c0140000c0803c414a1080a0030144244101c0b03010300320003800c8800c02d01312424000c0c1080058030581e4104902c00520b460b001d0f00403120342e44140d10044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 185786510 1250 185785260 185785267
    0x20606010c030f0c170703020601150e010e0405180115230a050d030903140606010f0f09051c0804170c1206061504050301020715050c07020d0605040201020712080a03110906 76
    0x4500311103540d1202005e44141c01000b070501c503141c50507002094441c1c060f030b0040c5607550500c0c1c0c4009440202d900c6141c00c0c0b00480310020310302d0360010304140802008443c0082c030350784c441208003522144440600d50399480c000c520141216207a44150503210206519141209e480300c1d50b8850480890901c3c0d0300c0704000d1410810b034a8400d804000651203403130240c0f5165a41d03900c0416241d44e1511104841d003003101000764559214000c81030050f920314000221400e241c1000e00072900c10b0080e40c0c050141002e02d803001500d450140e640d401c0d0300450143e542c0381c0c0c2da0400c000c0d81803044040031240c0550342d0007000c0b9290540c284010424048068030300e641710341e020060169440c466000c1c080f81e040c00700003180d590a03c00342841d1802000000e060b00301d21103007070048982c000c10030000d4580600409000da103480f940341c4840703684001300180d213031034500050b4503040c0d0685c0a805040003882ea81c004001c0058003038129910701e51802c2c000d020503600c040185000e403043c3d0740d4110b81e061 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 185787760 1250 185786510 185786537
    0x3030e010e06070b060f0306040b0714040303080a0c0e0604030501020d05092406010e041e05010f08100b1306031a0703200d11030901140c070507060f02010f05040b07020606010c03 79
    0x101401904490002c0112801b204a240424103101c07080b00c0a5801600200030000e040f0340083d10070321500050400382e8601411aa000382c0000300c0a000102415038508001481c1c9015000d5450702c800000c229944450b40c07440c142d4080c1d800701c001c11900a0614000c6141d5000000345001c86103a80541c203203080c00850892444100018200c070304108482d0004240f546a5200b20388400003a880b45a48034555810098242c50042c1c1c0256014070b02d0941c200041c41000c102560382c00e49640e0040382001500000940f080091041c4004107468010004104010007015925541503040348020700c0d60307031410950031500c0142404881024001951100420744d10042c1800d140000b400200c48407801c0c1801e2207034100300c0c2c140e00c00c2d83d9265031410104105444260b40307c02104201440c1040300d68640307849820500c503020510114a10030f0003a18000c1d044000c024413804000c00192805050088112106650b4880940104800300c5c605512a4100c1c1850030303015265001000c915 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 185789010 1250 185787760 185787773
    0x21216031211040f03030305060306060102250b0d0e0d030605030604030e03010905060a050a0b041b030c121803090605090d120302090607060b01080106081603020318010f0603030e010e0607 83
    0x103400e0741440103aa90b402c901c0702c55007200c000c3c0c405002440741c800040c60035480c001e0308940000c1c24240c8a98446001c001950703074005485001100d80d0035072001c44841d0104580e44023209900500650640840c065232140200d03404040d441c2c240703c0403103020710980c1800b40c080b40c00780d005071500340d045040004c010130700480e402d20400c00061b00015840c03a15031200c0341045415a2080e0825895030305104c00b0301e00500550004d6101181c0c100007005000e031084105000900c1c3e070b4414507494914460f0818011304003603945211548007801400c84558240c20f000c0e0045908a02207510403a000c070300f407882902074605200780a415850910015100e20000803031034540c6808160302004403110070b45450001e81420b038803e80c40030070f051400c1000507007070000507001901041581010130030130307030401c42c017001c0035a840b802c0c0103949807541100122540c2c401d81e9402c1c5603600b04044080001c10341d90241d41100d0180d41d400c074030412100011070b0303907510b1305c40d070345501c50000d024520103c0c82 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 185790260 1250 185789010 185789027
    0x6011505040b251b050a08030409090c030b151503060906010c080f13050a1203021905120a021c020102041d06042705150402210a170a02121603 63
    0x5400c01c4200382841d2910480407000c903444400c0f04d01e5440f0604000343c420501c00b80b100a0b0101700e07a8210050700340a1402e07521b0280c1e01c51000700c41e40b0b03a0354242c10b001c0202214030185801803075078a50f5160401c04258034401040600b40512040241340d5600485032040e28000e580050110280b52503c00044a40d40c11029081d56104402c00c80d42141c042100020300d9000b000c01d0150900302d01d4003007007041a03441e40c0d00005100c035140814500080e07001c6528840032002c1484041200c020307040c1280b400f980b24803144038240c0d0008540006e2a00002c0f815906818107005078a40042c0131030490a0b800380c0d108806041c1d018640d00e01c2c405907107001442e0720400240c0000386071b0051080f4108000482d01042ea60040008030841c1402428005802d048200d050b110526003466030100301500b95030141c005803a10a41d50503042280b0a002242c9201d800c510500b8840303a246070000c10b141d0000300310340003510175545d142c16000c074003000307850300354410242c6001c02d004641c81c20b446081 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 185791366 1106 185790260 185790277
    0xb2b02070507030b150310020702100c0201120e0c06130f0f06090e04030516060636111b06040204050c09030601090e0c120d0206011505040b 62
    0x80001507508116548480320580650f03521586011030800c17040303443d5040c05100841d1020b9020341c1c0146c48218001c4070382a1307520344a0a0250390b03040304880b00a011404c141c00c0c80c401c1502580c44481482c3e0b220b410340c2d412840040c0080c01c2c9030310480050510700c000401c02c1c040f141200842002810505965401007070420f4070181050b809449813040c030041800006003003610410680300341d56540442183c0040851030a64040c0600b0b01407000301909480700030308032070f91081d564024910034000c03081200f0201c11000029003400c8500c0b1201800c10070040a8a644450740000a9801540a01504e080620400c010f8540c050282e802080d4140445607090342e02054181c111401030400182640f00354185605240e080ca4996074007803602c02a441c4900404528641c014a0b02d07426200c032684c8500011300003152030300c0100c0c005107090006207c2400c07194014102c80 = true := by decide +kernel

theorem cover : BRFrame.Cov 185611510 185791366 := by
  have h0 := BRFrame.cov_init 185611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 185611510 ≤ n) (h2 : n < 185791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
