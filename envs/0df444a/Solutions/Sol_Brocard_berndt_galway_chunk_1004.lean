-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1004
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:46:58.532699+00:00
-- url     : https://prove2.me/submissions/23ef4538-b859-40ba-bc45-5f0dcc0ec9f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 180395683 ≤ n < 180575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 180396933 1250 180395683 180395713
    0x1407050d05030916081c08010f090209033d0c0f031109120f07080312010506071410050901110f070615120501060305061005240c150f060d030504061101020d02030702 73
    0x81b1450020100301d42c810040203080c00c1e40e02584290360b100a409a600c088460001c1c1c504120400003100300014003c0902c03d4400002a100090240c03507403005035580ca040ca00c604a408102025010640082180c0d0020307100307901c544486622604001d050000c0c0001160000c08045207014455210035242c0c1c0c081c00c1c040141c00300918010300118500441c03024420640071041c410140100340108010b810050600c2100c40180400e804036807513180707958505005060182e620700b110354648200c0d621500d4071407049441809604944a05d80119546d17a44010460b044600382282640800400c0030300b44444201c1d140e1b03015000200d00107045040080c2415400b41c020540c8158541e003c002d19201c1c000c42d080d000810b010303542d081552020700410a0f1090040c1d41100d030249910b0502c0000c0c0c000c1e07440f07004481c81c0c1c4815095644513400c0c005401c00065000c1d004c180705010800c034003445881c0640100102400141c14120484010070170390b0000d0f035824016800c000d8124081078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 180398183 1250 180396933 180396973
    0x9170a0b16020d0f03113601020d0c020d0f08070c06020327010e0406090606020606030123181606020105070314160e0603010b09011407050d0503091608 67
    0x7904400103190034200d0107566410524a041c0c180020081c696400b40d000354001042448581455a9111071002058040704200c9404216682c4180f448212882e004040140340c8541038000f4a042e034640101030301d0000505d00102e90103009441100c00140400e10049160362140c40340e103407166460720f4101d6030610650080401c40d401400540303219540103aa03098070010710040e428282814000498140840c1d80903503421604060001800c100350f644031a003190160f81c03d88107140c0303a6908050a036244205090341000340ca9404a85c10200d284001d0742104a204028024503001c040070790070304812030070103034040004240401000782c0a0250079441300180c41d04102100300e0441c0c1c100007450140550714024400030a0f0020301d8042c0044007030108009107400d07103a60b59107a44102962119080d00d0003d00c0c0d00852500081709003080d41c0d0f0090744070020707041c04100200100d072290001071440220348100103048003441c1910f91075501400309440504009100069405084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 180399433 1250 180398183 180398191
    0x2e020303190c0906030203040303020c0a030504050307050d0803011a04080a0614070c021021020d090c0b040b03040b1306050702010c020705060a0806120c10091a0c0c01030c09170a0b 80
    0x3542c20141d00c00b81a907442030007402a10400d080041c0c80744c546080440c002e00490420201d1071007816074040a0541003409002140c004404691003641c541c802e01080c0307010a540204146000d00040c4264207031030030b007210441d5024036803a041560300e440a074507141091205444842c0ea82040003048002405c50307543c80105c0e401d000b404d0f0400b50703011034201022482010104021045420411040307842810f080d204500780a40d201e11407500000c006114032081190105203410000a900c00b00c035050300c04888140309040e046589545400000910080c12890814064551480000c1d254400c06020348003660000481100020010745000c615800182c41003000b07100c10702c0c1d019440700074540d011205031259083c0703031080d6400350728101200e0b00266124055805001d0001c2e40401040101e40304450074144600d401c00f12190f0910548004034110742000d15084070550081d00040c881884070b2034440511982d0748803990002d1131070f5001d900a42c100070320440610030f2a180716900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 180400683 1250 180399433 180399481
    0x151c1e0902030a02010305040620190804030c030f030f0603080309060903160201031503021012050606130e0415050a020703080c040e04020108190f021b0f07052e020303 74
    0x4004401c1e000250f0718854484001d0400d900d0b103000a0400000d50840b19810381b001c0c14140000070700303040c0c0ca1100e8000750f680b4442076265083c801d152030303c21110a03002e26010344071041544119202190002c20308040c01d024580c407044402401c0c5000d105020055003c0c0c1c07017958036800c10020352400c00001070055545c1d03034800d002d00d01e507402940001c0c0e0142a03090800203540101c0100302500c0340303056400603600038030101011003640d8201907803460150010500b0400c80d60f40130200b0500380185151070200c0c1040640c04e114490000011640060144e40700380300203101c884002e8251002190040340c80303900440c03e0020907030420501c0d40c2244a05203c0f5040c02e0500085034075084c00204042e04001c07040010a2142029480303600c40c00442c1d41040c890030b21594600c2010394858000f98203102071041c01060005004200180a064024058040903243c0003c20509402505c0c4040035488078041625580001076009503140210303801071601c0b4541a201800700f06480802400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 180401933 1250 180400683 180400691
    0xf0a08060f1c02030f10050709080601150f050912010e0d080603060a1107120e012c010f030b04020d0b2e050d1409100507020c0a05151c1e 61
    0x2550360098003440d464200d1110303400b09522800064a080419080740303020740a450100102c145031038002e10b10403166a111610341d00d507603815060f602c1200744508480c0420040e80c010315107103c2d450003102e818842c44c0550424080300b0000b40e104000c9a007448040c0c3d034550303108503020303811710400422200e6400c2c505061300c0d104002c04d44580c1e0080c10506107655400c017100854010000781c0e01c0c030b00c1c0c01c03480c060301007092040040c25403140c0250701c6010070b42015407415154202c051040e800f01c5003040401c00040020015215441c643d10640e05154546094104c2900d941c405812160b0304d6140214044070544148200784821649103100007400075040860110307900c944d24619440c40c60860b0362054840381100060005040d045644100c20060010311400021140002c03555090100038980390160140d0303646884481464126005003020804e910309603c940382403074001701d107091a100b0502612403c2c10051000c13071900d1651081442000c1142e0202099041c036544000c00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 180403183 1250 180401933 180401959
    0x6030e010911060307021204080c0102070905091e0c0312030a0501060314040b13080307030c12051506090a09050c03040c0503010b09060d11030d020307060e0106030c0b18060f0a0806 80
    0xb180508204200a026910000c04900d00520800205414002407000342e41c486403100d50703e9454621aa00c028014824101c1c0030600c5034880c403801c2d000d81031400080152040c108412010318401d1803c1d00340320300803450f5a00c12900d091142801a65003010080da89142c0149031004403901030704002c0c101031908a02ca0044140c84600350b03000ae0b04028114001e9940a043c4a002219080000c190b035002009000a494258000429550854031030864215103405004101d40701203580b21030030f00d01c81b030104c0518102240200038180e0080c290008550701c1d6100402a204290350503a01e020001013040240140582140040d182c214000d01c00c1c0c501407000501c5205025045900c01c4020342e0034403007002106070b1201e08000024080d1241081442c01c0651a5000803405a030302d9030401d13040000089042c0303d16426681e00c024405503180c180781c0da00031690461750f801590702c9080a074804140c0d840c0301c00391000441a114065803014a8280280300e00750203400f603400b03401650008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 180404433 1250 180403183 180403193
    0x90602010e030c032b061202181b0901050f0a0c0201082d0a02070219090e0303190b01050705011b110115052b0b06090c1e03060d12020706030e0109 65
    0x1208500300801c1032051100071707401c0801d0480349000d0819141480c0520005100c007030802c515903241d000700c802d03100900d0741303032181c40d040502103580002c803d54601d81200c1c2100036401a05400006240c82030900c520b4040c100200c0d40255241c2010906000c0340d1011581c1c056821a40844c601045080041803d10394003c0d400101c083c4220355a103800004085200075415648550340041c041040380901c0341e110f4900300c0d203500030500c4990405601c81044100002140e0003034000da040c440c521083d00e101e18000780340000c0d21604026040000001050302405992918103403402072004214601d6009800c1c03155802900c0b899074105000c0303903400070048200c40202d034000d131005100300d0390007864100d40481e81401040300c0705884a8076000e10400420407440741b801036900004984510a0303211080c000c08140000f100c201a8000c00d294050f00050754011a020b03010240e00d4903690b480d00215400504044010381c4a94000c02c00f90307905002e14903941400800030440302c001501d175 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 180405683 1250 180404433 180404437
    0x1060b130603050c070203160509070c1106070f0215040504050609040506040f14030409020d0f0902090a0f2a030f11161a010f030c05180f1015090602010e030c03 71
    0x4039820b055440001680191080046400302c990080035103180404501011140041901a03103000d4405980001c0c0d17042e014003143d52205030003030101000d030a040380030000d40d5404004126900a075040c081401a1a841d050704e11004403888825119400c11043c007045400041c21070f071080158000740004624040350b0950031a030010040c60b00b0540380c1c2007101003420001c004111314440014005001481613000c0c20300002104418000450f0b0015044180c6005410107076000080002240101c406948200b48040304503002091090f00000d40c8941500880012040f445520b449000040c1d45440b400340342400f081410841640408680b040b14002c5049060760460114090828424024030320f55007405a00d4600705150b859038240003400d44a880126848042c403640441c0350300d00004d01c682c054809020400060351341142c24840c2501c085c0000b10080e89509010407010307002d000841c6010920385135516401d01e4044001c0c00c507007106441030b0303540d002880290644080801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 180406933 1250 180405683 180405689
    0x3080406030c0306140f041e090c0f0605040b0a270509090a080d0221010602031201060f020307020f18010905100b1608070302070e130308060f01090509071701080f01060b13 76
    0x10311710310425010001f0500501000d0f19002da0a110a8030017a0f03c411113400503008180708880001000f030f503961011a00d48428000d01000c282c003031005100c1c1d8107d450140840c0d040710300c0c040340e04812480a6200001c0383c0c034035aa10b20901040300740f045060500c1d0300c039001a1031100030003440c5c10b503480d1781140d03004900040c11029000650f00d4200007043d000000720692550001d81d41e540d41e448041d680341e200181002100801500000f802801202d400b002008150007440c9086104e50800c201041c1c8002b031580d1111408079044428511101c1d020302a1101070400642400e11110b002c0700810a907105a24002040003849a140d424602808025900c02801ca440709a2071509a0405046030442c540041e4000200300640300321242d0719510900a403246845511000c00f8003920341003008226010514600041180b0b041411170940c0c84019032a000c8000281100c40c1c0a0240007a482035502d47e001441410303da130b10030301c10a4000d000c0001c03158601940c2000000c001d248500c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 180408183 1250 180406933 180406939
    0x1a040b01050a0f0f090509090c04050c0c070b0702040905100504050c060a09050411121501030c0801080618010f0f020c060c04030b0103121b0b0907050a0f09050c090a03080406030c030614 82
    0x1348142d201d07008602e010007404005040606519001c000350b5901c0c68800c001d07502c0355003003074041012440e00d10100c0d8068001180a0440c603800d10708115100c1e403108078102c3c1c001ea99100a8400704809016107009205a5680810241003605091303203410032092039144100c03810040040e00540002d940740c1103c00c144c40100300140c210000075058080d04a0140d0161188401c11130b004079912040e5454402c03d0700c041020b50a201c0080b41c0d08442409900501d0b400700b800710b821403412074900e5580d8030b0202d00110b001500c828009058a80c0f801d08001c140b600400d80c0c012007181446400e274400c6801c10741e04c0c141032660711010070840041c03202070407514048080c1c600a03403003190081510100007855080061180c81c11a0301c1100464540030b65015030344011409141150301c00c001c0300c2001c49662212070601c04890000c01c005440c500d9007490800900c98161a113a403d20001c0d030061401d1900e8034034010003c0d060718600c2e0403140400d841d10b0342c14440c0e1001ca400c03070340300c1040136 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 180409433 1250 180408183 180408197
    0x603020f09130b03071214010c0f2d0f030501080c01140d0e0a082a060606160506010b030f0a0e030d0504020414040b09010605010804110d0309091a040b01050a0f 71
    0x2c0760380c0340d00a14819803d640c15008010300820001d0154100c204030512802d02e10148104c6150b041d422900c44620301000290800701c2c440840c0d100c1d620340b000b42d000c500100c0d140360008821217020383d00c101c40c1e05004580040700743c032089601880344c1401000050050080d150180c4c0c0000c105198400c8000d010140104807074580b20100e91050710880f484070304690027050942443c44907a00a00d601e5800c07911031203000389410801c03500170480c2000020080800d622150b081110b690402c0e003444010522002c0003601080d001c015550003400202c0351207039241030000003c061040300402c1c1c400034a040c1030310a988500008102e400d25480f464000405444070710005002d4110b07041c03003800c201d03006000c1c0010b008154218a01495040380208034659035003005440c1e2103411140a407021581c086115580d0030185d5041103122b210307140c225500342d15a04d44004465105400f103a508044880140c0242064814201900024209182071042c60344000b0003202040301544100514 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 180410683 1250 180409433 180409459
    0xc0302030d06060201060512010b0f13020d0603060209042f031008060411010f020d0503010e0a020714010501030b0606040521030c12030a1401030206030c0c0a060608060906010603020f09 82
    0x10a0080e07410850641ca03003400110b42e50f28000703028082d940901d074464404c00c40e110403e41c80520916081e448054616014503c0c0801000340c00301d1221480c0710159004c012600b14424144241c001441c4240401a124000c0c0300038041250b04034040e1100c0d03541140d260203019890040700080747c40306811810356954403402c140310007031843e6008181758030800c4c1c107000c10414900c5401000d10341c20790322400720b444010f40482c0d4640f0115589404220308100600c4550a1380200950201c04841e02510781065941e8007160701d8211020902681d44d103a0052080040320070fa00343d0802c0085802c81c1c10300b400c00c0006888606158000b03c0e0030503026a4030f06240c03005101341c410302500b4409850842e4080c12810541d5402121142c544914040c1d0b005036140306644210f040e00e0b000b5001c1401e60742c0310361407030b48164004403200500c2c1c4210560080014005e0081034050004030010300400d0800e41240c920f00101030b0840d0f4107160040c08020001d5a0560995000105c101e8000c185099 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 180411933 1250 180410683 180410687
    0xb0c0c0a140c0901150f050a140f12100305010e15060f24040305070e04030c08070c12111008090c0d0206070210020d090807030c0e04060f0f0501060f0201020403120c03 74
    0x42d620560702e070400c0002000291020002000b004898400d4881d40300d10401c0b00d0b0101c0b818032803442c0800104441130102c552105114028080000031240f01901e02601c181d107010180c141203c0c1c4481032880414103100704503080c003e24251204503c000d090700700901c160746804000003082c032801342240b0301c404001ca60b65001103020915121b03085600940780604031003040e81c040c0c0000d844903c14034400103524060041550f10030742d0965a40111490341e541c80060a600070740042d954120340e040049050300f070381c00b4109120b03882801c05c56944403821092016200080300000144481902040203080e400f0880791900300c0c08444915400140d071002800a000304e20317000c1d4220401c0e803903074189540c0008000c0a5042180c484110165a40b02c0d80c40c0c4d80d0b41a4040109884071303800041001440107021541c02610407400800c0803502000d4240454101290b062000340d00c8400401810750000b010b030b914000d0500c001d526140c203680742c1b260b0890508a040c010011061100f200f414 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 180413183 1250 180411933 180411943
    0xa080c101d0a0306020310120b01053a0212010515130e1e010525050d1d0a0308010b070b1305120c011a01080115030509010e010c02010501030b0c0c0a14 67
    0x12600400042c8040d07100d09020f0006d420071944c94400c001c0150000c114103100a00043d06903920010310703071300e50f0b01700030030321940c40400c1002c080c44103020309000c6800c4074038a076101110444070030503101c1800c05004001a64140d00354640d1640d04d0003003445190b001402105004d404107442c0c0d00288109000541d00070170302d44203416203e004050140040c03072450046004110200c0d0001c0c4171316181e0f1442507241103416402c0f82c0300980c030440844405401103000e441500c0d0401d500003015107400d030035071071706c20200341b030203600c0b604002c840d0020190461012400341c012898a9418034016503240301a19501a040307000c420307140709040c010000c040101c90042e01c10b1020281d103030310080100038007801c41580182c28000c02c0c84035402b9507501c5521044c2c103d900a0080a010041d078031070540003050043e20b2031003203540b80c0702c0c0110044800d0051004004055000244c29071640c01c2c94449600054800c02007c03108100c3e520300c0500000324008415000102e0f00d907045203003c4014030305 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 180414433 1250 180413183 180413237
    0xd021f1b0f0e060f18031513020f0901080303070311040b041710020403050a0302010c21050601020f0601080d09050307030b0712021c060312080403020d0e0d060e0106050a080c10 78
    0x590f0005183c40d080b09802c0c0a8440c014034041800b0340c50010408041c3c4405910f60129500940040050042c110000c001c00000b8009002d00524564041c0803901001c8260088031450707100006018915a044c0309484210800744119401d250420b0b10b4580300b8031941c841c81049802e00ea030300030812031051040740e00c0c044a544085540d65501e1900c5511000707007000643c095480e00b1038501070107018003102808449090340d4010b00101c0030780c50400906d4042c0a41d411403050110003094042c3c204a49400303007400400526602105100041a0703e00701e800960180e0403040003000000c0c02c7d295070f00d8101d0b5850410f44150040024158001d014000b00c0f50500c0f45651031038515100180c1c0f00000b964080d95044155a029441c00c0e2070860042e1401401a03010f400d903800c506100d03000d1410304000040803403526264a0f198a0161841c0003d01602e60755241d10802c4a8907241110310001c1c12040081c181800c205000600d01c459815820ba05119104041c050007480c001d80b09000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 180415683 1250 180414433 180414439
    0x612030408060403030c1d1318050a050c031204120305031b040e100905060306011a07051006060f02281a0a0c0801140915010507050d021f1b0f0e 64
    0x5600d040d044c0103010381440743d89480414219480d034070f640020350481c404d0000001c1c0003070b07401114400c005e500801c5890800002030750701d001d41c080014024000043c132180204002c1202c2004141094140480120b0f01c242041c400c120800c00c001020401048840e014280281c680e52010505807100c1c2c003803c00f40700c0c0e080c4000380202d10000c00341b8401d0f000701c0d541040000010340305d01c0380c5070840740b05488040e4158003c40040262115210003592a0002c844107141480c9071507541d20303c0c00c1c0102c40541d0380252152424442d090b07210102c00d41400b494801004901080e03a2906590345d141103440880c000351044001c240700c41c041020219850002c2e210000303140060300c560013071050075050f0700028030040c000514030460710b030780c15070800c8014854003454407640c800d40b06002d6001034940c1408401e00c91140171800900204d1040707502c0d40c01400e800f85400801509076180e5030001203110f890070600c51048016008100d420400d14140801071044820050b0b1b81c160850003c558 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 180416933 1250 180415683 180415693
    0x5090c0a0806070318111306091a04050f041e08120f060a0503030c0c090a0603050304030f0b06031c08060109270b090609040201050f04050301020316020f060601080612030408 77
    0x349050340010030b244510640c2d03404010581800c0024149000325400c040c04203400d0300750120142c07500408a5041048800002903d00ea5880200c4151451078031102d9804584044d051120304180c00740940c4040c401807407e01e589820794840b944291106e441111780c02100058208001595007151150759801c4241d000c82d00d418101304002c1c100c111001401070641403030014036030400005417004803503410050b05130b004e4020280180740c24020105e111030354a4480c004045842480244065402000304440c960481d0501c2488c0c524041c00712030113948601481c054250280540d0f42e0034540038030380188180c5400c1c0040b00c00c10380c5500101c1c914080041c2e2054484042070550f50706200c000400c0c0040c41d40001000150b0728221a100e412110600002d001907205400030002c58074aa00d40b45e04281e00c48000c06e0032a00200e800c0c0c0310764080ca038007545010b82c0411000e0f1101500d80f00514207480c1c030f040004c00010300906124003460b082c420039a8400d5048c4152406420508100c407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 180418183 1250 180416933 180416939
    0x120c07290f0c10061d0403050409020c0c040213031b210206070c0602010b030c0103061503090206040b0408071a0702012001201306020610030f141902040b0a050d0605090c0a 76
    0x40c0003001340c2d100b030345864002c0c0d0421462250720103040c40e03c1960107460700350800c1d1810b04054040d500c1b18420031058084c07100c0c4025980d83d184003038880722101000035905a0304518004403d454600c940c1ea8240d803d81c80104044011024951001003d0000568030a45244082a00307401640070003041c1800050000c1070a940c150710401d403102044084840070350002c00150111002c40c040c03401c1d04215002e520713010710b0180c1c0000443d20303c0540f02500c1e1507510817801005400c00d40200c030440d0082c00c0e042010309410a9041260115007244c24078040095001804010244110312015400c00d45040c2188000394070110700306103c5100c00984c0c2408200b072001c10350146840c200100f1340c00d1000b00e8003610004100303108080c6d40c5401381443e41180c4400030381118034101201c8040d20110900515a421f10024501880c100301c1d160645c0f4840c4108400c0e90594002140107004040080080360380b049031440405801400008040c0ca8a540860400440100d11504003003c81000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 180419433 1250 180418183 180418213
    0x902040b04020318060a110403120207080a1202010507092103090b0f192303100f0909051203090304120c03020603010617160504150908120c07290f0c 66
    0xa882c42280400580758543ea85a080b0360844254444003005600180824030010b40c644903400752b400386900496407050340d02e004003450403624000032504409291f00c01d1404c0c907024059160014080e0426403042d9040901c3d09212031292549850700c12403445010003072500403c41c0c1d9010304074007141c0d5503130f81c00c11401c0c0d1402c0764410306110701101c280854000c8443d204440240c1d4901c84842c5003819103000c00c0320010160006070154581c43d10a520008419120682d4440106100400482e0300c8009045c2941031145641c624162060704008024200d0004001c030303410b80d02d100081c1050301e0444c0c10000030410306500000d403c20400800400d4490300a02c000003221100f00203181c080d0707030b84000444020b40708086280420414001400070800e00001c0f01e01c4003440d0314141c0100c60391a01c0c860b04e8041075503c142c00c102d07400288815524414400307640078207480701da054113800006030340c0306000310b203907400700201c035000308a00b89548528800c07581c2c240c1200045500f101660004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 180420683 1250 180419433 180419461
    0xf070c0204060b1218030304080717040924140d0c0b0708030f1003030c0b060d06060e07170603030a030c020f070f090605100c0201051803060405010c09170d030902040b040203 77
    0x1d40810000d0800080c5c120442e0084200550a000301075420350722140e03030385e0090360441c000843c0c100e0440b06990f88181514006400180510303440071076600030480c079071410f810740315600a4626000e01c909000a482482e01111814025507101e203207410300d820981d005107036035001b0305400080000c1c004140111400610b0040c070300f41010758003a4846070460445d0540c0ca01c001008541880340300004140303c0320000c0e40c0305402804d55881500e140c0d440004441d00c42d08043c548041483c14482603c0c0d01503807515034081c2040354045281003120020b80d4038000c0e00361190426480741d9051100398801d01140c074045400380c1c2120410354031101c04804891460061a0655141c0744001501d8641500441c810100940b81c106c2015800c1d001110745901400d0f40009840d480f00c20030b0071540f07041142500c030360b014400018600018082c000c12583d01d40d8004011480c0c1c10040e0400e1035004900c0c0041c06502d81000900c1d10414030110b00075000000650b81d01610220410685841140c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 180421933 1250 180420683 180420697
    0x260303010306060e090a170f0712020604030210230c0415030509100911010804051f0b03010525030504050c0d060b0112020a0c0212030730020606090f070c0204060b 72
    0x145001441e0341e4031010765506c80d180100504030f800d00b0241b07401203d907030700000d08040f801150303060310f0720700144c5840c0f044c80702290034540140d1045007003000381581442071144a9160740c01c01e020300358020308a0400c040460315007001413070090011600481e42a81150300402c403850300b4035440b03101c030007000d4000c0004a802650a0040e5036410084039075500c1100e01d40c5074000c0307144240100c3c8200468244000501c101d07040e01c22050b46280c10501314009a09035003105401041860000051509450003d00003100c20005414140f04230383c42d0100d441a030903194500004d4070350341c50400c035117081041140180c0005505480c1020722a441d0810b0103207800a0300c46c10a802d00f41d58101040b0300c640c08441c40000c0b14034003080300511380300144140074407918003103034144945c684407041401c840e01210513144601c8400e00c0c1d2507428941c031404c0071802ca070020f0541454184080344003448002e014500011445001a400700e0013031800121042c0c002c0c0081181c242ca880b20a0860f038031201c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 180423183 1250 180421933 180421949
    0x16060906021f020c010603050304092004050102070611010603061503020909070503060106031a0402040605090a0b0313030f021603140106090e0703020d08070803130c060507050726030301030606 85
    0x100810303154000285001c000c031070101c44001001040e5980c40c000c1d000301c1d0340c625035552140c13800008a101040270b030010340410038000a8070101000340102c0e250400c44201411742040c0020401c507030300800c002c07048588609050a0700b14500328000c0c01401b003600000d00c464601407824003102680c4a480c0e05132071003920180c500345c6900d201280d803280c01c1d201d1154154000030050210034841d4120b01ca071541010301d241c6e1003c2080d000502130340c02c2034010b400002c0010444100034502000d6400c0200b564429441c0b071800d0003050005244140c4002030240b125503120004281d00c01c0200260740c0c45121040b1011940b40c2c82c01148c0740485146030b0440c3d40c281072010510310308501c58881c1001d070450003003030b000b403443d0b007807000d40c880828043da2245400d03c00c03c0049180c0034003c500c03403426000c420240700d0b401d00c0d04107100b0005400c20410804148480d01c002900010756605448d00341a1010301c0d100b00351041a203d40c043e0f442405d8900000c0300000801025400c940107a40102e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 180424433 1250 180423183 180423197
    0x61309140412030e060c0a051312060b100903030302092d030607020c0a150306050307060203250201122c06010305071a04060503100302040c0509040507050f0904110c1606 75
    0x410011400c3d11382481400c645a0440f5003c40c081c805080003d1400001c1d6003011804d00d0700d030307603081d160b0b6034a035074401c05010001b100c46608225180c4103403010a001240e05012008c0400001412030b07010740001011305600251501d00c1c0c2d034840d4140d0884800c038800410101e82540c0c80500014008050f40b4024450807002c1510f103800407031420742002c0302a007020000c0f03241541100441c820f1102843c2810368540b808100b5890030301c5100d019201e540c00031a9a80089452413609811a0b40e0703140c1d803102d00c003a4100050b039120301d0a80c1d4410b4511004140c1e0040300da11803030245203000c46401070401e400300d00c090108010030010f048070300071002e80c3c00b02a5964a2613034550701c0700c0602689080200814040c15014001544e040b040020300b003040207440c0c1d40414100c408c469540d1001c00d4012911144a14240c0155684220307941361550410145501c0b012300c0f406a12485072141d038541c0d040c1c110031503800c01500c510161000c1165541c0005210351111401c20f4040c003030015041c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 180425683 1250 180424433 180424463
    0x21828050402043209090a03020f0d09060c060b130e07080102211519030b100b0915070213020403030f02030304080a08060d0b0718050d020d020613091404 68
    0x10920958048a4403071281c1c103015920192201d54000b40b01c401801c4c540c0100420305070980780d20750264858040007004101100490401a02d404203c04102800361f0000740036400c0c581d03010b00e20f00115101803c0ca180c14608502d0110054100480d00542026023180044044001504090140c280110603500c0286c0c681021900703078800c0206c2c9000c414413088001c40f181200e050415130000c18074000c400c500110300d0018178011000101c03a041032001000c10301c20b03c8048100550480b400e68103e4070064a04a10300c4814040c41c5400c510030b00402b160048802d07000002c0700c1400741d0040065505c050302e4890940250858002a8001222018010700c240d0000007100e01481d040040503081440d010b0007101c49989c004d00b0b042d0800d0500541000080243c0c1580d4018451502c1d021a02441c0e505e100044481c40d43c85188120503106104c0e0158a030210682d074600d4040da00695a06c0c0840346640d5124070f2984044203042c9800c00d48030344002501c42c0540200d02c10030745102002c1c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 180426933 1250 180425683 180425689
    0xc1002070e0c0702030f0109111305060d121202030c04030302010608030a080a0c110a0c0602060714071b0308070c0e1008030d0b030111040306050402090a020c0d0302182805 76
    0x901a112030006003001040b44030038a603000d00589803004044036900014000c500b4299162604116008000c0c105100072500e0644a00d010380001c40d0810030040c50070703c001030060103007408060310290400543da50058400e00000c0000d03544460255541d080440c008811648540f00a0300154a402c0c000701d420480801241d005c00895a2041e0b40e070f840b004c103004000c14226500c0d009000d0004601d054129041c440c002e0190700035800e08070420300d0007402900b00301006028904001d048284211501d4492003503800542c1c01c6800001c194845400d08110450990005805c030039000c1402000c20190130140c00030b65440c03110140190b25940480b403801c000900540b0f855030424007000c0e0300c0302c0e49544024201c9400074000f056002140801503c685e001d50001c1d603070b0b81c0d201c408110560400b0044c503500710007a0358085151007411500d01e910b81c115001c1180c10141c00141485045e05030101824848070010720b800e1070751000601c0600c5000ca440a556040c000c5a0f5000450745 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 180428183 1250 180426933 180426943
    0x80901060602030a20030409050421020105011206090204110f07061103060d060504050a02040608030d11160201110f1b03060a090305041a0c0312010513050105012109050f0c1002 78
    0x11303a84444068801c045030340e0110300c0040003032002d58401440009440c2c045409203a009500070300300380405203145031214005081c0b007007003041517a060000400191000c0d0405402443d0080e02c0019003140500c00100074101c103181e11202460f02044004101300c41c08024220688035030000c00c00865104402c0c80940402c4500c0d42d400401082c3d100c0100341c0680010340e00074460000d0342c4046107190700080850340b058110f030010b41c0c40800c040501503c10305c1120080103100411604244038013540115004140000a0400c14260715000ea01c07003042100050300c0c0c82181c19240d000c01d0003003c404545407202201071180c17191401280c080d2003584604d00500d41c01d0368030185854100380c03140303000c0f00c000e03420443c0745182009903007200d190500c003a0020318590350055285506d04010030002c408600c5001c0542c5241c0801004170baa00b14406150358284130300c200c03d4074603095840b0001070520709005885401000703000c0710381040104000710301a104880c00d803961241503004995603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 180429433 1250 180428183 180428197
    0xc060f121404060504060b03010c09050f030721080c0a050c0a0b130317071403030109061a1e2101030308100602281a15041802010e0406050a0608090106060203 70
    0x581c1e6800440c0116045400660f07100780109004901c00b040000468219140303c4945000200581c10612003850007016810140780100e00420090f8103080c02850400080d00c0001e84100340b801c03c0804000308841540c3c550f4144900b601c01c940c4c04c0b41051500e405da4840410710804502001092610b110419130f12244107030061300704207c2c00c50b03440c940a03003000060030700e40c10070501c10304001501112080c0c100c000a80041c0d41c0340d503d4402d8442c1660300581142c9250b1241290034024418000240c5410043e0040e1202198968030890442d40c82500481c00702e4010041200304100e010051075412a446540c503200942e0780c2010100e0260100c3c003803280160020302800300002c6045442d1818040c110403207070180d81c80c03035498a2035855400d01c80c0b03054001c08000c20585c8020318005104000d020780c3c043c42141400118180e00d20340684009040c03056803054000c0e141c40d0741c0c1c0030340c001d00b4000d42220301c070b00d441c1e85016108410407141c641d030135820018040740084c404030540f007071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 180430683 1250 180429433 180429461
    0x403050d0503191a0a0605070c050a0303020d0f090b0f07030e0306090d0c11030d09080d0509010f1209021905090c0705070506070609060c032301150e06070c060f12 72
    0x28001c0e43e6101240a088091003003408074a80a012602c541e65219002009180c5611142c1e61000e030741c40c2900d4001956400a0312401180300c0400203c0c0c1c0200d086001d100d010318000c28030040c01c0105640110550300542e11007800410154487d146400c0100855406900c403440003070303a1641059503c00044074840040d401c000f0131001214000c90702906003034841d8035003800c219a4480440d16101031140000d000810742d100400c15004103100f070350040140d07450445c0c1740442c1d201c0042c01d6101072501d8881040b01c1d202d5001000d000c03e610090706907030300505c0940d41c040e400c5c10340c4482403643d000740c901c183c0c004404141000d026074211011294004080e1590518050401c50541c020080a0f40c01940f100030890002c3c03410720860003850701640b8000342c0e4060060707028010111008601d6444146400180b140075502d40341c403001208e0340e1070028065440302c004220700340121500141400b003546004240ba0303412002240c3c929655075100001d4190760240b003810354220049480f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 180431933 1250 180430683 180430711
    0x140a030816060f0504051e030c0714040219030b011d18070c08030406090b16020c040c050c01020315040e0303041a040606050d051f02040f090207031e050403050d0503 73
    0x4100c6018025110100b0700460000402c2e60400510b1000d0380d1045408464a0b04034200303507140c5811081940d82c3d444603200043d4140340140120369918041ca004d2600c1810084242d05180d50301c94048806c0001c0c580074090104010001c00360180c884048118085481f600280a0001c8104003084048100402c01d005200c06843c1d240c6c41c03800301622a03010441407003514008106c0000c01540541e00c140c000007500551f03420840d480e00c8002c1d00001c0403008544c118007042d0b80c0001e4001e00c0309412100050a40240c1500395064811484610415400813040050500492603500022034056034184104420824860385900c0119401000c525140c081c41003a103c0c0304c400f0a610510580c00068019103800004410f0b0026400440b480c1d800201015541d50101d900d03046110f584010960400c0d04012101c004a0050300542c10000e82c0400c041041c540f02d00c0c0030007485460800915174100e15400028810b82c4540001c1e200c0c2d103d0042200700113407055048a101c2d1030303186410a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 180433183 1250 180431933 180431947
    0x5060f010504030f0f2001030b01050306030d030c1b0803010f061e0c02061215031b010c0f05030706021207140304030f051e0d0f060e090703080f12040309140a0308 72
    0x84c01c07070400704019604041c1d2460320758002004c101011040d07414882d14101e08510f81c6e000101a1280f10342c40504120041c410b0100365240054410f034401881d0402050840301c01b1411284101c09544074650f0100c4100d8200c1400b0303440c402141600e4400c4000326201c1d482d4003040c2e801800101d03a9111440186203296403251041c4041401948010724143c5048170901c1a10040c1c0400c0d02c1c00c40700030504440c0ca171400e1400b003044203800340f2044880b0b6840801007001901c6000ca108001c0d04c0390004c0c15010701080700520840b50813a902200854903400380a2005da10404212000c0d00440d802078244440604c00e40b042c5e0f403041d0340c541e90f40c035040000490101e5180e000764801300882c0808440350700d101c0c1c05d00005802500708801002a070356140d5218002541c15940c011126200d001003805150a00070a804080c0c035080216960354402500d1300c4611032141404a000c84031501c018041010383c8681c3c1c0b07001711402c0d01c0e040c0c182d406c00c03e4104065810180300040c013006003000b0007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 180434433 1250 180433183 180433193
    0x4030209190e030a050415110709020f0919060906050c060a0c1205240f1003020a05070c0b030a050c090a061b02030a06090209010806040b06010305130816030305060f01050403 77
    0x74101c0d0002224020403481c0c0490000c41c51504050100c0e004168049800d2012201800312251070074464941040048030800c4107a48a4401e4080d000d9502d400041c0203902154140885559920251140ca011580350458102001031406036100055440300b0000d05144150145d580300f011000150100e0344038405100c1c0185101c42d600014420507508528001d00c52b80300c1c641c0306246807500940d18900e518807001d072803001c013217100c1d1103541c032854044000d0725608850100307040c0c1800c00590700d9801300020740c1c0500503240000c011045084000c501c45030340328003641c042c0c0c800000904c015280c50074044143d016884000b0707045031a9400811040344191141e00145000901003000d015183c0c005c81d00f0606010070a6513084e0b1106034020071420007140d16401045207502810b09070610381d50780c80192401070407050401d92900c002c541004d0240d910199a00d41c030456042c1c0d0342c60104087e0414041806058001c00d00c0c1c01c1c00a121801c1003d01030504060507501e040c81c01d0300b16070756 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 180435683 1250 180434433 180434461
    0x4150902070b0f0c0a0c0c03060e0f010f060b121b0711041505030a0318080d0207050f0d02030a080706060b0a0305060f0a05030a03080a021201060908010501140a0e090a06022101080304030209 84
    0x3907c2c14544000d00001154140c4582080d80145c080500f1840c00500906403d54501c1004010201e16017481000544007400a481240d00520410310440e103030701c2129040844000668602c00000058400800184810400a851045c0e03401d03c4076841d001d442e0303008103c40b4461582c0641000d060540040d200d01401e1f600e052a8881402035280c0314695140303400c801801d041c026a2002500b4400d51600c1100000180302c1224200200c1c480b9901098407007500e40c02c000c1020034042504000c021094022a0140c41110840c61b12050400d0f0010302800707042e51154081e42e045403480855003407008140301915009001000700c517175250fa0407a50081c00414000d81a5030070710003421414107003280c460081400da500d0300c10150074244400e0850f68103034460065014100381314211a110250b4005c01c03641c181044600c943d03200d4000c0f5052a400c4040106010300c0000e84440c1c4140c0309800781d41c000b1081d49070342c81c142e80710181c00ea80d034421400f01035403210400b00022140c40d0b03412a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 180436933 1250 180435683 180435707
    0xf2104021003091b090b0f030715080403030e030a030b0f0904030e060c0102040306061706010608010f1215060f090b0d051506180906180307020a0306020904150902070b0f0c0a 77
    0x1500044c1c0412100260405007541c2003010f006880350a010094a0201c000180780d2808802130413406152140105090040b00555000e000c250b00000d001d141c001e502003450b4840400a8a5903454201002002440030360348191141c0c55014002c40c8504214001500c900e5040c0c84100703014802004024940d04041d00400c2c456401304004000201c890198070014140f0707a42d408001c25003812058208103058010b0030410100320f00400000700c03842040000c44000e61400e042070a018245070b40744025aa40342ca80e01410f00e0000145100c12174031071811203017080b5042084c4901c1000300300c0b0070b0420f40c2002d05941e00800f90b0020401317440d0005600114020300241c80001e806090008806080706c4c10282078005d00c0c10010141c40300344049030820b0648002e9450035145a000540012640c040904284d40c04640800c40f511142d0040c02aa9030282440881e982d980c0310703a1000c0d6011800813905c0510341404101141580380e50309010b6900451968140801240220b4003010111 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 180438183 1250 180436933 180436943
    0x10e1f030f0203061303170406090501020309060907090b0306010509090106051c02100311120a0b060f04290706020903030418020c0f06010f06080604020d020f210402100309 76
    0x204400162024019414011440798000c0c14404038140100f41c18a40c00030080710801000180c8140040d50000d02c06200c824107207c01111615942030680003851010740c000c000398800420b1000e11040010210b100715500c0048450340f81e2201880415102c3e51748070f641e05648084c006001c0381c030705120b006600a40701e600024440c0d9503400010003c1981060902411001c080d031070081d070a000101102080d00c40c1001c2c07043d000258507481c1c1d0780c81a00c140c0010002c1c264089201114a80c001d40f0580e01d000305003640384c084001103010503600c10702c602c943d0031850008840310290b07600d00b41804049290f03602400c040850311000d005c0d501507012a680f6000801c000b261040c0b8050030f601c1c144078503000050301e1f20356400b103e900d8400b034038901401d5903019600401c8210b0305400d00c881038984929046201e5100c00001c58060301070350400e40001e5001040c0410180c450320042c0482c01681020301400f82400c1c00740c40c100345401d8501940010a0103e130019450081c4c00003030721a03100e9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 180439433 1250 180438183 180438211
    0x305041401061406090d1a0a1b0801090b030708120c1b031207050c0607081209011a0f151b151312020c0d14011a1c080f040303050a09090c08010e 64
    0x5661008419151288410300c44c60141d008e003d0111154426001841c00604002100319032400010700f1804051007000c20064690b05c0c2c41509ea2400d100d01d030014031b20441212842170401d06001942e40005040ca1030b240705484d07900303084441024180c0c1016038050b01a107020007448005100341c0c3d1010509070782602ca0800c80f2451a100c4030010803a00340a6100652200c0d1203011400b0b0381d000150490b08640c0c10310900c0c4a85902402e2008141c803021684840c09017029004909051540d040040307010078041501e0010440a6040d050003c04e084152921800c50f613481c0398114200b41e0304102488071250754007001404c0d016010458150071700403039100c10305460020b04840300318101203440c070560040007010b00c1d809009405403c55030a1214071241140d80200303012106030002120403000d00883c0109101c402004c6904101805038042c0c1d4498603810050110b5200500c2000025442030b8002103840300c51051181000040d521072080342d180500e10030800314040c01800d181050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 180440683 1250 180439433 180439459
    0x6080402010c051009020a080a050d1b140309010917070312050408061f06020a0201050708030a020403051005061e0d140c122404050703080a02031306030504140106140609 75
    0x100301d1140c1000c0c40140c017046a800324070504c04c90901c0c40d0300190303d0354801031500d00000c1c4023145500340d5140516051200e0824407030342e0a1440f0700d8000140c0700c14100715010b520f40308044018000c07004280c0301c6074203240d43d8050b200c40342880c854000c48181c016003411b200080d003100b6045440201454250700701900c80100500701002070354402d0a00841f2010001e55840401c0c0c424002d140500281040d0021500041c00da4880c0940003007100c2d00003c000791386102690b055402640d000000c0780ca1480c04030031050018101a00c410344541e0b00390103031020019842d501e6124030360014000125024055440c4201c240c24011287d4440c05034003514407003a120041d004040d01d0790000144a1035070560082405896100003100710494a0380800011a0000528508803941300c00100d030390f005440004c0f42103000da54910b440307800c001400000d4880d41900300314000c50103040399801031481d00342c22500320b4400c3c0c85400008102280c40300401c5c41c100000d001480302c09800c916072003032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 180441933 1250 180440683 180440693
    0x150406020405150a030f0213060c1b030308090f07030f02090717091b060903030405060c030d0216030807030c1b030c020405010b0a080702010207210509180a0b01020a0b0106080402010c 81
    0x41d1a002400e8400400b040790b095460b454003524240306c5d04c01904616244118001c0b81e0155100c1c0190010301c203009008a0422008440c02070b5522111111146550385a00d0001e084020588282d010341c840c003c2d03100034501d00420007004803503100c144a25600ba507035003444030034500140500e00744072018001c1c1a402e0381d5041202d1181030108054445048807912440303240e60007003a80f0740205804e00c640f0404d82c80c00412a02500d00844050b512503020480807455881902c01044800e8004511074074072842d02c1841c1a0818401d8450450380d50310150b00300c04031582c0b0300b40840007544041e0514540c1125803c0d83e42402d00a00e0302d05101d54064000c6002d4643c2a803246074585000504140b04581c0690010380012183c40254a03000b040d464007946107070703a42004100c0c2545681c060076000d000303000701e945040000c0d00381c2032100e05605038501d41e041300725150b80d4000d0038075260038419840400c0101c21280c0c031158481a03a420b01d00d0464050100400c00c0741807040020306800410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 180443183 1250 180441933 180441949
    0xe1513022e0e04060e060603062b0309090c050a17070207051903060e070f1a0405040e0708070f0f090e01020f070f1a040b0f0705090a03080306190602150406020405 72
    0x422a102c030012840603006000465403680d21451141448001b4042c19a495108594214004442e80003000803280360110250906441d074064a001a904940c2010380260a0b030003101c0365080108040709041d2001d440c1c03803044600c1d075030009403032f03a0134401c807640c0403a00150040058070440f0740203901d807030200d450101082e140e201c064002c880c00700b04001c000e0241102e80070403100504450352502211628016007406500d14400c0700c0c0381440346500c0f03004140c40090000030400d01a1090301c04d204c40c1c44402e50b000701840e07402402ca022518951b10040181240e00c1900d8640c0210324050a8500a00340c0e2100d404044d5020080c200b0350480c201c1c00f178007000380151003c10400d491480c1c81c0c4000c48117a075030749928907024803c02c00840c400d404540d070310036040a1081ea8a60b12188100c80520400160941c010b40d900f1000c0280034241c1c001c0d500c02d40f0213580030008010141c0f01214055413500c00d08006a10030314a041050000e2007045400c544a910094103042c0c850700000c881d6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 180444433 1250 180443183 180443269
    0x120201020d180b0903070b04112b0b07140702090c12041202010515010c030818030c01060e060f09071407021e010216080d11150a0e151302 61
    0x15048800b90402c1c00b6084850701d400c0182000154501081c50b6240141000c0042026012103000016070003140ca076201341004070140f140910600100341c06148400c0d000d60602525943d40c04070006400c04c4c06841181000d18215140c2420002c6590070800c900400400c0d030342009600f80705074014841507961103030090703204100301c15801c04007640c02401c403600146140032410b07516150106690b0081602401d80e6010b00e043e00c0c03d075840c200e02c6060f81501e00c5290710030388800100042d00301419484001951031101160318962200020803400e5124403000355441000a030114500b10b008a14400b681302c0183d805506000881d000100c0444c04681074540c142c5950b1201e020646e07045c403200450301c40801c2c0511556041222155459040070349039814012241203108030a2020000680c0e0b07000700590090700d51800702c070920090100740308441d40c01d1240da03000c820390750100e10082c1e104541c000d5100c94291480d80801004c0c015605000e4081460b1803420224214103103810a11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 180445683 1250 180444433 180444461
    0x100201060f0311030610030201120c0c0f030f0f0905031203060a0b04060c0c060302070b2202030307050a021008040506070c03030b0d0c060e0423040c0503070e0105011713120201020d 80
    0x301c0b0040c0f60a040c14014010000c10f04910021014401030b84c200014881c0f90490000006041040030026075072892a1040a40754590700442d54003056407002081d4051050341c0e6a40f9403d000d111000e888400c40b41c01120340c16000321300108140c07400c02c0003441d80210700501052105584c1c1c420f030800350b801900f1540000300b01851141c140721426212000508442c80c2c21841c0c9006030b02e0b0100d010001822001000940c10a410340d071200304030000d03005a40040c1982c0c2d0711501c0340f510f10b60f01c05031071a040b80039000b0780d090310300124003412110380300319008030150402d551841d00888181128040480505980c2d052441040c2c031005c0c038400c401486038980c1820181803031400303030007400990322180c4220b00f40700900c44580290850100d20761750650740328850b920307685031060002141d0b410103030f014403507a0380c0011060207045c040c82c1295400c0e01c40d407076101080d640903000844202c1d60001f0b8600b02609280001d984cc0c1400030310000288001802e00010582c413005445540c6e0821070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 180446933 1250 180445683 180445703
    0x3031104180b1f0c02060f0d27020127032004050c180103020702060408060705040e06030105060d0f17040b090102100c020607080c0c03030c0307020c0109080705100201060f03 77
    0x14400050712680442c12422540310a40542c10880400c004000038100340030000c1c90b8030750508645441c0e00766450350180400003900e98806500c4680144100310310000c540f0071241501c0210784045611800d42d980680d0b81c900034170300d00c1e40701d441800d858000c084041c3c803020200001080d40000c4040024900541c4941c0ca4155581044242c40c406083c5582c404010003442c000c1e08a86061140420400e083c050b072a68528000035005010320361195100b40182c0c0c04000d01594024010400e13130300e041045c40302685540c0185401c882080301c1c01070304500d055a8140102d00c078a02600c108501c9850f55000e841a500000c0340b06030042c0c1c1c881c420821000c10724000c03940c0c051220604200f06071104018856203030342c0080d80d0302001303460703901400440d401107520741420030304540400d8413950880e40c0e00d00740495555240e50003100d00100500500204014642c800d0100c0c104031000707132004044017030400040040360014110a5015596689070000c2c84d0ba2055105030011401220084 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 180448183 1250 180446933 180446969
    0x1303020c13051e0115141b0706080a110a1238030604080901030e10020c1b06030f07030e010603050a0c03030206180303161704140f0309130903031104 66
    0x20b040350780304036200c0110309843c801407041103203800441a1070711452903d40390360b00c01c512402c401d0348100b051464a10030301c0c007201e040c61a000903c420480312185d441116035030f94683c1c4541100c0d109412034412042c1000219140d0b889051542d14500600304006941c0c113a03e040303800780c0052040c0c2c4102c011080300030300b880c454401840b17071600b090a40241c0700c0d61030244d84440310791150b18001070515a49805005c06078004000b00c002921181d0b104540d80c14805940c036607140c4101a0580d445c155490318080603040030402e0b2070003001d803135481c00030710340b145003055002c0c0c6044510304140703658948000001c2a030800034840c204ac094030a640450b404c41c10024205040100328103150f002804074001060070000440340c0c003104841a01d410000c01c01811240d0b0052140c048542c0c7c0d030460140000e00c044002081c007400c4910048561509480b10101c0e140e0140000c0281d10081c1101ca10054007030680241c0e030828440e2074001545c00e8010000107132500302d90001c840500c810403002d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 180449433 1250 180448183 180448201
    0x1302010206070c1a18030409020904060f030201050d0902011e030b1206010f0e0703110d0e010b0102010e0304030b060406080f100b0102150c3906010e010e1303020c1305 74
    0x1039003104407441c00d8080e00f07480b51110f1602c81410403180f40c4010083e000504807080340b200f1081c1e2200e90906680d47c4a81d19100303070b406500400240e41c840d501d0000c0006440c0300c50b1003113500b241d9040e110142010122041b070380080c078128005034107004088100510b407043c0700c20b404402d210691000184172180d10180078251000340b031026110783c0058018025000701440c00030403924000c0101c1d003240d80b21481180034040a54881c0d584600c08114074000300c0480e0004818860709070020010650024012403e0700d16020204006400402050000c5540204101e60100000e80080303840c681e43c0903038502c0c0ca8034600740b05044d50044100c4184048d4180915100841c00748000e19245000c41c0c40c440d00f040c0090088280140300043c44052403c1d000010710034220018a03040821240b0000c0892208181c05180600c0c0243c60022034000c0c3e4504415044c1e840c4040c0480081d40c80312807480380901c04200c1034003948140800f02100c1d40d81c0a0800c1c00c40356180c400411039081c10250 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 180450683 1250 180449433 180449443
    0x1a100f02010b06070f0807051c031d070f0512031201031115120703020702040f060b030712020f09010c0203150a1a2202031e1e091f020307030f0513020102 68
    0x35503c03c3e54204441408507008a074150101da8112403883da0318640c80ca030081c6408034607400342440759407411906192a4066004420400ca07401c41c001d40c8009846810317880f80500e00410800b89180b41f0140103034203000a40c0d000840610049a03d4405c0260401c0740307804099001711001d070b0301458a5243e609294a901034a6945000d41d2800c20502c01d01558503024010002c004069021510780c0130f540e201c0e0000145000500410031641d80c5800340404a0341c811110800400d81c41000561002400d20844080103e5111401e0905d4194001142c5905c20b1074403e036414410b051600c0790741142036103a070f4018045440c0014580134204400845500c030035241c00e104006c0741e040c40503404050041181c1604484070010ba0342c0d41d139403400810b641c090300341c40c15807501b134181001514a10054014000c140c010a400141d0307035000c1e130155a03803074842c001180c260800e540102e0340c1e0f103807074000d550881100e050200d840403000d03c065080350002c603070f001044400301705e4070425540c040c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 180451933 1250 180450683 180450701
    0x5010e160918021809040606030308071b020f0d080c16060509030c0f030f010e01050402190b0d050c1204081206090709031403070206130905090a03080106031a100f0201 74
    0x6001c0d50051030804448018040c042901d0009a000207140d9103101d01902c0454071100020412641400c040c20103200a2040340421004100c8030404100d00b02d0141d25001c000c00303940d05100321180580d9080c001d0004111300c205820100d0359007031400040452002d860014405801001905040c044d14003205000764400e4083c4541003020002c992804216807031154026115054401c07030003c0401e1401c954125111120752800002810100301904424026402154100840e60b490300011503d0280d500c1410311922042004074915004da400c100d60185038101d6490600402484020b4003100440d0100c6a1400010741481045401d666241d040001a20050150715025501611488a40c0070142c1142d00042c4040480c260400c01c5078600755024107003d8485ca00340f4040b858000b140e00441c18032030301304400110400c60014560303d210760107641e454450b0b4a85030b403d07401401400c40c1422030362a040ea029143da03c0f940d00c01d410316450342d03542009258225900070b0840305011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 180453183 1250 180451933 180451937
    0x70c1203020d09151b06050a0204030309050405070503010303082215051806010611010e0d050c19030507020d051507081b0310030b0c04090f0b0406080309010f14070605010e16 77
    0x1180c00d120307102c0c0d03190540c9030481072800e11010748130001c030b001c0c2c9081a84c0d005c01030042d0306013070400980c820395801030b000b247c0c46900c9104426413540104801d5400494503140056014030042006c68807604000d40c000368840743c11f180d40342c90101006e81c9030302c030071206480701054945d09940348044c0f8880d031a841140c50320038006401c2141a841d0b207540040c8107401c2045070a250002d6105002e50080003c0c0704140100d541180c1d044001030159048190a1107090052000507030308928442144800c2c40e61640c0c0395841c0c03240c60350800190101145c03081e904c910400e80354134103c071008a0094007910058849826074038240f0902c0c0913125400000b051024001c0c021f00610818071040d900030b90741c0c0910700ca440380e070720340c4d014440c24095a404414620306103600c00d5240f08480c2d02c00807449000352810b0180c0380d11070172410364034481c3c00030845c0019113a9099541d0300c0d110301244000354941c1000c0c140740001644501c2c06070707542070b00001110300e072050502950040d003880da801c0f407004078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 180454433 1250 180453183 180453197
    0x8060409020d020f0301021312020a0605030903090405150405180f0a0506010b0307020f03041401030501120b0604090501200c0c0d0f0308070c0606090504020907030218011103070c1203020d 83
    0x254003082074070000002c001d00604400002c8030207580e083d0140d9020280c0c07400c2199007503030389a02c0c0f41c051504e0504140e0050a002c000417608600c10400c4a100e110742030b004518001c41a000c0c80011b0400420701d442c10030307000c21485080d58650098500488000072462510300d043d50619042c00f41013030384911070350700c0001e82c0b40c0019008200241100c0c03081204584079598102c0507400e05003200c42c002030310f0000107400300e000703401e001048101031400e81c0c003003002e40e8980300ca0805440780e101d00a0010300e4450001a0107140c16004031440a100d00008101504100128101c000c0003030445882481e02040300840014104510318000d0011109412405000c0e101c0890000c8d00740c10103001c01100000080c0000d005a0300c1101043c0d01c15030400001d43d40e04103443c0107003400d80d002c81c0f0a6030700301c0200311400d1180c000d980c54420700b81d480000101a40b00103482000c0707a554490309a0100b48488000300303512104041c002d09200f5002d1208080a02c0c0c020b04015102100c10305020b21 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 180455683 1250 180454433 180454451
    0xf06150810050a020c01050708100b0306090c0705010608010f090b0c0306011e0309121101050709060e0409030c021203090a0e041104050403020312010b1305060c10020a050705100c080604 82
    0x70607580324800c2000005140d2034900d1003001901c07a00c1050079082d8205414400ca10303500000e000e00c80c6204441c040245621140c035004144030581c0c00302d902020010200c1c5541e54134400800e4258441e400004009a441d5a000c0c00d40d1030550036005025a02c607140700a1000200099600c2a42e041d02203145180510018001540300d07030520b0055401d0581c02102c9038040d80c404c0d10040d030017488142e0384004401c0b00821000c401820a60954200004601010f00407404a800d4030302c00e407100c40030140610f040c00000c1c6079509058080050301141040584c882c0d18514140035007180c0035640d100408000d2094016080d400305440503038001c108004a0b084544400c05001c080b0f4001c1140d80380c40c18102e287d030240b100c0c00c0c4060459000000358080d0020014805800d0110840b0a0b50340d880d42080024000d01c24109c0c59500004901c100c08081980200b080407a242001400d091964440358a4003240c0c04c1401081030743c031444001e41d04d41000c1040d40c0321304111411301c100d41c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 180456933 1250 180455683 180455699
    0x207080d03020c030f03190f1505060d140c0a0806010c0f0b1504020a030e211b0f030a050c060f01050d20030114040218010e01120813030f0615 63
    0xc20320080d081019804580e1210b1500140101c60450486010081d20707410321245002400e82d071b4100842840c7e00e003554801c250340d52070095000680c48049410328091501040c0306641e4860540c641d2503c0c0d0302d080b0029000300c207102d49801820f410b0781d5103499441188d0080c0c012000685000d05000c0507541c0c400000e080d4406030300c0500d40c001080c807056101d203c807081000c1e110010f42680b05001003490642d03140c0c107620069501c1c290300101c81061641d50030700020040801501340110408100c1e1000c0d60341c50072010036102c2c025500f11070464a0b410201400c41d01b141c41c03880f0020b0400100081240c3d8204100d079000406418140c1c001e500d0007000680741c0c504884010b0400d0b050048601d07290910320464140c16001600a0003241040b842d02580c0b014100d41c03ca1044804910030010005141035441c1a2503020410310036590800e100307001206042c0c0d8049a03d40000c100c0c8442d41e00607059001c00079480b07548006400c0c100c40c581042501e10b0182000c50705c070244641000149 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 180458183 1250 180456933 180456943
    0x3170c09100c0303090f0b090d0503061c11030303011d01060f0e091509090109030314130b0c0706060b090102060a1413020a05030703030504061b0302072106061401030b01020708 78
    0x1c0d586007006201080030f0300d82035010706a43c28029005c001088544001c0c8800303c542d85200d440c14509607401940400780680d194001515255080351800034081c070071522012a001300c11b40034650b6074012011040000e451a4026000940d0300a64a0681c80c0c0c1000310021b101e0242c500c60800840b0540c103001c00401c5544080035061040e58900089013460310002850262810040c02e510654640341070b9143c00381074580004c40c00031340f0300b9041325006a05504502d014803100c000c011089150358507003454250000c0c00340d0010600401100002429501c01ca20042502680e40f54803418010000380c14500d004211810441c00c7ca0001d181400340d6265040d840b000c124100a10f442c200d0001c14126211030308500e41500c10740c04e0100900d1340040c01b0b0700c00c681fa03907680c6845100891600c203030001c80030f034002009030344004400d00003c2c04581031900c018010344041c014541041d1222030a0f1910395010101452a002c100300303165a05010b00f5048000c20300040845034906240513541d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 180459433 1250 180458183 180458209
    0x706170f071205150139080f07030806010f08060114030c0403061e050601110c21030a090f0801020f0301150c02060f04140901051e0a08010903170c09 66
    0x440308100046016018194401e00900e4501d001c0240c1d1505820104184249000507800325090510b10030481c6040405c000407004810310403034504211014040380040e51140403140d1002c00d1103c0d035031340c4201c000988111400303507031091000e080c042c0001d04010f090618000c20819124200485030741c03c130040250040b100e0440769030304d81d00c400042d840c60246405c02484142450000f044a07450110b0940b4a4100310008002c981c45d203030015035001239401024110f64018006505070303450480c0d459803d105108c9008400a04004401c60440e40058001070100e41502018003171103441074164006401518001c40c1361004200c00a8490b020500c140d810740c0740d1011011425034401e40041d1091075000d00103a40f030300c26549005c10a0b810038040c0c1d035248401109907500d1481d082c041c2d6170480c3c8001d4180c00c506110b003007504260020f40f008540c0c019809490004108a00b4802d8120702c40c005c6c1d5980d2810041110421a281c03409001c484600c0028807101d9019600c052500d000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 180460683 1250 180459433 180459451
    0x6070f38010e06010e030f0f150901050910020904021c05090106050111151e040302150610050a1209080c010f0f0209280308030f09010c090b03011701060e010314070617 74
    0x2d05990000070311f05444000105041d00403032444810050f4001000c080d00038002414030400d59410b01702c40d080344c4085650340055440a403e80481c064070b40d008005810002d00b0240c54031140c455084421040895040300b8aa6a030041218905007841707800054038091a041581e0081c0724041c41e640c4000b44040e40c8003000b007c001c04c40b141002d243c506c43c40e0b0002140e41e94245410300700079488015030906104007900340d01c00a80382e490540c8040000350269100c05003441e055201c21242c0144c1155185891a038400c050804210401e020342200000d490012440a4103020700c0400d64190100781d60707103240140241841966121008008407c1c0c01a0080c02c9050004945950714159803001c0c0c81c8080c00024880c02d0f01e4644509881845200000d01031404100411651000c4500c0342d034000e040f0510042c04615141d82038181101c3d5400008030720399403601c401807805031082e402222802c03807602c24181c42507018000704000301441e0508070501d149001424000540042a17128 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 180461933 1250 180460683 180460697
    0x71a1308030c090604090e03041707050102100203090c1816050304020901060804030c080706050103030801060f1d03150108030909100f030b0406020c010e060103060e0d050906070f38010e0601 84
    0x116070703103c02007070720010046e407403007404140c90b40c1c00c020741c0701c0e0320074051044a42840300145a040300001001c0c07013128010b0b801402c4003550130701d01c54000c0d0005000382c5171030b0040114603600c40d501c03840e2007490450310842d490f070a8200041d01b144d0320303203d0070003203024000c05100308001f5070b4455440a04407030017818546196a100d28046800d038003140d000a210040100f107010030300026510140c103907440f940310351070244d07290304e015031340c02c150300d03406000117040d4402c2c441c400c140c11070150411920140882d00d890100f10444042e0000903008100d0a40c800f08410286161040c2c1e004c0c0c0001081c101040050b0502c3d2426100070316a0002030300c88406a030114040001c80d038100d61050350316400811050100720740aa407507810a21007564041d0a01e201501d4164000c14158891501070b100c0c140390003141824092203030081c81040c2c545600b00791800e0082498651044004d0003050841d1040880d02003800008040d900000d02e1140c14010050100d0315410917200d4004409082000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 180463183 1250 180461933 180461947
    0x14091006150233010b0d140f04020d0213020403031805060913090807020d0305180604080a0b06060d02120717010302060304020f0a0801060b07031b120c03030204080102071a1308030c 80
    0xe40303150100f80020f801210b040001121002d8402420307803004c0b520802d010300800c0420000e9042c0307064500c003d10b0617034040428014035041c0e014502e2503202404103442000000110012a00b1030392090700441c1408601143d07602500f02044040c210480e541410072086401140c204015043c3d5540d0b920f996a614909010a610a542a0039401082603625016a141c001c10907000185004c901c001c0303c0c504a0302900e405d809031002e60310130100401301040c0350344904031981000f802642d00410b0810041c01c2108880c0000e190030b0b1204202d61419040020000f000751301032a0700350b0010441c403401400180d468100300c90300540c045a0880c03c001d00d41c80028140c1c00181c0c0602095803030040300080e0344510401501c0214065128038521408400d808030038204034107401041000341c80512500d0600407071b1113402003030181c60300509250b2180c180c03030f013240c1c4010429030701d800f50303020080c41c01c10600e0f003810391150704915500c40650050b51450564000541103000e0b41c4004600c103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 180464433 1250 180463183 180463243
    0x30501140c1e16080408210f16060f0902090a090c17011e05150301060e04060c020703052401080d080105061e120103050d110606040b04140910061502 66
    0x968954001400f06a024890915000304980c1c80740c4245012405a00c5c00c210141c1c0c02c002d48801d2010500490398685a028103d40c0f00b03590040d0711911100c030610316400c001c075007984600c1b045401c00c05000607040781d203401081417802009104180d0141024201c9000850140d0000202c440343d60094800f8201b0f1218280940320550130350600480c6d6003a020706035161170b004140a1500c1500c4411010689c40c1811300342d40e118010588008451004a40010341725401158291079502c1602c0302280c43e69581401d0442084004600c00003400004282400f0381503403500501c6410010301c05ca40c4017480180056005100d658815500480d009075250f600001d900b402070400c02049a840007441c00c1200d8150083c082518030344540c0807151038080c011100700540041041c028038599031030f00300f08400742040e5540300750080d0301e420b054a0364441c10180e00b030048940e60b010341240c16071500880100c9010b075020380107124040211040035a00420760066405c011441c40000c0003c600319 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 180465683 1250 180464433 180464437
    0x100507050604030206070e01090b0304080d061703040302031608190516090e071505040e060411040e070e010207050a17011b0210050c07020f040e120310030501140c1e 73
    0x405019070107000e003007104050703005c140f03070744100500e894020103e45410700443d4101098001c5d0f1820210030008140414058030142240c81c5c1620008130390561104803d07005003241c641d103841903a001007000d00852506000007680090b40d0000b10b400c1ca403401605c035540304800701140340020b080100d003009100080c00b40405083e06844500c0040707035a496010024805811982d2590094a02c013161044034030104c10301840c07680c2e80f080e00b45400c11000b900240380140445a00c203680d01d04101c26070b009503021708001e10031903044c2001442e00c4040a041e9a00c20006141107410240080c016649e03044081b000f0340b030292185400180c1450b450038014038840c0d21103d10070900201391207119a0000c0e2501d80007041030021302c56a19204200069030182c41d030020342c8204a808115005c1c207050b400040c1c03114810303084400300c001541e0321942030f80c02542c1361a22514540e5092041c821b0034002c038080d041c40500140d0803403500300d900a407203024000506d202d000100250710302490400c02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 180466933 1250 180465683 180465697
    0x5100e030318091e0c03070e040603060b33090d050a050f0f01050118020a050d06060e0411070f0303181506060908031602060a090315020304030905120304051005 71
    0x1102e541d10001d5100d400d1412049011601c00d400b400f00103080303140b606032422803c84100075034103016103d61071004541e0300024030010070007013094602c0409035903500503103006500800c00011046a00c8041c00141e0200c4d01c0d0840300c4500e4003400741c4040d40301e85015503580748c0c05400030b5141c1000500081c000100808090024400d424610042c0305020400715038690300d41c0d04079900500e040307900c103013628024070804811424104620600000c550003d0090f42918071348030b49402202407000c0102c0e80ea5400882c00038804080c007000314181807280441d44000401e50b103060920b65981c59500180400d802810941c803640120400a402d00c040039000b41c1c0048030503820000d11a600d0300400c918401e010000d6004e00c400502c20340c000c01110882d420035034200e0f40b040b00c2c43d002d000095210404603c200200b40b000003000c200a08541841c1c41c0c003c000260b52400c05080007032601c8929000280b28078441c069131058517000000f154202c900c2500ca03080c480552801c20f43d03103405610 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 180468183 1250 180466933 180466939
    0x9032106210102040e0f1e0c0c030c0703030f0c08030a1112090109030314010503060619170c04110a0c120207090903020d170702150a090501060b0408010b0103090c05100e 75
    0x106031081141d010b40140c03090754600c1a03d05880d03600d14035115401001500d0a0200201c045d0b14030020340b120b198050762240ca43c40e425441c00a941c1c10491456012000c685540c0c4c0200d54180100760340014040c0b2000806d01c0d2001d0f90340e00c10784a440032440042c0410b030040390743e20780f1510f1071040c1400307580c0300d252000328000c418901001c089000e041000800c0f0002440c11001c02c03620f41610b003030607040c0c0d0750180c010a4075070f4800c0305000710245851034206200300c03d1100042e14020404911031303000c0c502e0000e840b803031007120244000e880d82071011006084c030502c00f01444503403207021004031030341009180c4259441060143d0038003506410003012141443c401d281416000920460f2107504e50380c41c000d40c1034480f1083c0030080010b80d60000181c00980c40c407160098901d401b2500002d62140004c2d403a40380f070f5142821503d00780d0158800c1400400d0400054000b80300780c41041c9000c2c01c041c0510700603507550142c44085070160350301c14038290408800d030760b21580108140340d9020b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 180469433 1250 180468183 180468229
    0x929060a18180b130c0503060c0d0b040f11070203010e03160201120207050303040f0b0f0603120a0e03060f1602030910030f0b04060f080c010309080d0903050d060b0301050909032106 80
    0xa0701c0d10112613648256109070b01010001000e0400103201441005900c040700e0410292000203405006120451a4007645034440e4014071840c621a441444581c500a15612580c0703106150079940851591443c9420a1160f410780da1182c512280a0f203034241b80c00d02110800e541c98200070b016145c0040c0907884048204130400801c0e01700c08844901a080c0c05009586401e072084c80400c0884849802d038210100d14a075009100c000b0304011401401c0068030b601c101030103c0c0c60188200e44003048000700e5801c0c401910161840303a40c800c0b4251000d1450104c1c403030085080280d00004031b80030542d03141c40411001d1070760780c4609a21400100b062080680d136669a9440350700c2409035500350f024051038500c2a40c028071940f50b9840e0b11124407420301642c40c20380801030000302c4003903040c0101000280d075107012034403400300076000c079074030860712541000140441c5650080640d09950f004100b04018160028041545034041001746542503032141d0105102040d03005c0d81d103203e5480 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 180470683 1250 180469433 180469441
    0x1c08030c071707050714032a0909070e01050d0c09020304060f1a18060604030b070c0c0e060603190e0313050f0d0210120929060a18180b 60
    0x15402070101ca40950312045003000101d0b0115814460407000030995401a10204440752000e5451888041c0003401d9800a0003c064030070005080580c10310f45010000000c030000b4a0010070701a00310b4115001489414144800d54030342070018068640b0910360b248001d400c2202403481d420140c200d420080d91207051900d08035021b09181d0b54034605003400c10f1a180326400c3c0000010356008801499003500340d1000240c9444040b002d00030356000441004044003003600e4000706800b070030b45a51101c4614800e410b0000b0790304280e4208201503000c82d000c0c000e459540b5419a40c0102c0d0120040d5201c91072288080001d0142e14059609800b0200e4024800c02c408007105040319015160124100000070800c80d80100c40c00d03001350b002d030001c3c00701c6000d2841759140c0d98090103065400a0860550340f02c1d01c2613034051000c80c3d4401208030302c032070300424800400e42c0e03003000303040d60881d40d85428501c400b00060b5107009128290341e5621070004010000741c1c000d81c540c0c0e80043c940070309828 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 180471933 1250 180470683 180470701
    0x6030309182401020714030a0b13050712120e04150602030a090f08030f0307090e0411041410052403040305030702060c0c0a060209190905061215061c0803 68
    0x942141c00d001c0103590200c00b0589104003410b807040328071059010300152070900940b00e641c10340c4904c07070a406215035842d1304005502d00d41d2050290100024088008002d454840d01d4251640c011043c1c9030907070b00784000010354039032080d45c22a1507400d02c1c500c1058514003144c02082200c5182d02e00030315081000940c1a0040b004045d00306c2141e5403600c2040e19440130303140d042860310031a034003540700f0840d041c541440d03400a144c000005103441d00c0e0716075a90f000550260030944040d03514100c02c000c062082c8c60188941041444d2900d22414140340c21142640c0000903403282034010251081c0c3c001c0c170300490001c2e2035400d40c2004400c41c0c89040900700105141c10485150016115480c00305840400d058107941400ba4442c000f400c5002a5940343c0d17002c0e41242102c0d540105e0071160030001c0080030524070000d0415000001141c3c540a0100620b42c1d0141c0d40314030058102da0b44056051070300f919a0b65100e18107583d03011030034000e00b07440c041c40c44201c9400340071a034002c01031144143d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 180473183 1250 180471933 180471979
    0x3017030c090d1b060306030507052112300103060507020c030f0304090e0610150908190201030b01032a0c08041508011505120a0f0c081803040302130506030309 70
    0x60391803040005600d0f01d40d081a006c0703680a00002d00740750301011040290346040354841000c0780c40600c10101c1c40809540c80340c0b60000040d1070f010800c1021414840c04e40d1b081041c02203400e0166141c03210540e01203024440203030180800751545031070304001010b20f07000700f010342c2c02104082c0032a4808000e15413459225001400380300340090800c00d100f120418009200d50003459a2100140308620302600b00c1c00c0c1e0300c407207222941402096240020041824820302d082003080320348122145100c2e200040444200a003113505152074840014200111442d030060086a004642641e843c006a4182caa01d42c81903801000d02c0000240840c22a03203007810080d042c44561200140741e621020301c456150f52140905c00000e000b440307411819141a00700a400c09580030300041d0ac00640c840c502c095401c045100c202064051040c001501c0d00d1161446c0142d116102441c281360466000030408000c051003070b003100751103102255055800340111101c80e00c3c000c02c0f043e148020f03a0f010b9000c1b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 180474433 1250 180473183 180473213
    0xe070f0b071b03020303031501090b040b030f060619030f090206190206070e1c02120717060a020a1707090801092a1a130f3017030c090d 60
    0xba1108004000c4071110521001500da0040c065410340e5201f01082c040540000e41141c1080100036001400d0344441008101502d007502102d0740e40e00c6e141c1c80e00c001c44003001d440d03030740140c4040180320b90b80504810700003100d1030f0300e14020031b1400c2c0c1220319001400c0a050003030341c0320100007161681c50305110700c8401c42d4510f68007a40c20943d03c0300070541d0003501009103980c20040040041d92041400075103a40152b01c01012000c150320201c5000c0d190070340a400c1201815002c5000d156010400c1100e03940c4216070807815403034810003200040c0310303405508a07442d4074040c140c081418940a02210805010020020403006000cee061a00c40841c0d0240c6072905001040021021800c124080b001601c1c440050540c802004d0004802268080801a400841d41040c041181d03810001000c0c001c110140180d40040049210702c1c43c15401b0036140401d007861406042d0000d4040c151601c0340c2c03044403001b01d480b541d841c1c0100d603841c030070032800c130307612003da02d90706420081c01541f440c8032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 180475683 1250 180474433 180474443
    0x1e0d0e12130e0a020d0504030306050312131401021f0510050d02090601140d0e07030209070c0506060603040c120302070614040302031b0604050907050901140a120e070f0b07 76
    0x10020030000952a184105081c104054000300360034007442c102c080d01c0d1a00070740300c40301c0146030a13014a15841240c409032002c0740040e803110400c0185250800c10312110307412640150380f80506004646040307800c24410468075200c107900040383c90380280401201c02c0e0300e000c2e0114090740c00001c1c144c0241000c9440c040e0510001c0e001094a0409100d8100290307400f40c4002c04c0e98848100650b01d022a00b10500888001008640e09005040c01181ea107011004018107100d810b520404c40143c0b030041c080d204100c0f00121440c042440010b00381e81100c400d4440580d292a1030524080649454204025072100603140303070205a07000900d2000c0741c00a0b83c442c030b07a050800c40da00d003032031003284006545980b10103028041d0013964042c0c0e007140700009201900e026a16004039440960880d1002c0c045080440e43e0200303540c01000401c3c0340210f203040680781454a03180648014406101c048009031303120303100101d4017402c1180c07001405441c1d108500745540e881044106900c5401d044030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 180476933 1250 180475683 180475693
    0x20c210a050a0b07110a02150f07060209100e310516030614060703080a091e05010b03210904060b0408070512010b0109031b0e0f041208100b1e0d0e 65
    0x4020707102d4038170041d408801c1e502a0680c442c0315003c012580b1403c0a414110000810410901c4444d40000780302d842d00c00d1101585464004003004101c0c01c0920504d03091100b650ba040c4590b039900c5a9500340d0000070803400041c007103140685a003500184540f0045030380780000380b03c400700d80034a18ad4034a84003507505210b070a49504020072014001c50720302b50004400e110310702c0000d0180000700d50003c40f0001c00a00c0c81080d48500741040e80c18054280d103480561703491014800c0a0007900e16650f8145c2c01003d180702ca024508900c810800c404041903c0d021440913400d60302c1e500040004c0a01c2e03091580c5881e29080b00c140c45c3c0489206551041c0b240614004139410180a440e8080d80140c440104440c55900c0341c202c028680034294601588801022544061000081c4d004101a4101c81d5091500c0d2a1200400700c0d800a00024040c66800304070508411080d200240c800300d980e1f60383c9628841040c103201e00c0065000e00c14684d00403c00e1505003003250710090f1824031541c1202c1d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 180478183 1250 180476933 180476941
    0x18180b06041803141c020706060312080108060106050307030e011d0705041a0f030a06051e0108030702090c0c0c030f030a0f050309210405100309150606020c210a050a0b 74
    0x80310180c041c000f404241390b446800b28110741c1348003401c041559002e0807402c1024145401040380e00c9402d003190080da48540900a00c094020021080c49090a00800c194100b1025980e80d010501c2403c040000020028110611070f400c00342e00c5181e10002484106551002c40e800404489070341ea8041c071400100003144c0c501f90007481590f0801c0020140304003000003d1041d80d84100a585d50584100005c3c1000240c16110782441654414545240c1c0002c1c1f40000c03074401d0b0103134009941c6510034003070700300560303a035100e402d410025a400c0d103950307000e00710b0380039080c032201403d565454041c422200700c900c0e401000801901b0070542c1c4200382c5d81c0c0581c1701604d1a00054860300c40d0b60703104102840700c1410b900e10320704178802d442c50800d00303061381c4d50006003920b5900513610000a483d0301ca01750070412411035059600c0403501c41402a42c1c20214001d60b10f0400003405489500c0c0100e006042807500c404009500c00440e041d180700c400b0604009039501c8070a03404603602c1c3e15260000e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 180479433 1250 180478183 180478211
    0x506030c01051611180f0a110a02031602190609170a0308040b04030c0c0b0d1416030902040219050309070905010614070c0f140f04021318180b0604 65
    0x181d0101940b038100c412070800d5034580c80444031082000c80d170040c8080042c024402c200c040214402c0c500341c2c42c405807a281017482403080e07548030600741400c00790900449001640103c15079821401505031081e403074a40780000f0f0201d4591414080c0b02c01e4041802203202035100020606a5070b0b0100c66000303592841d2001e995480c4098400340006000801140018680b5002c2a4019010303180a060207485070300c90b510b10000030741c001c003a44140051200b4650865004484c8103060728400c0d0401484c0c105100c62240c85614455802c02d50303a00354840441d80c0e1a4103844407910198411003261600010107881980280c3d0120124490203000140001280c01418140c6c0c0e000e03603801c5c42100c00b0107590640c2d9042103008403002c03020710a01207402e00700460881e0090060b507149401c0b41e0442420302003100a40704505004070300420400107020007218201c01241ca40d501d8000714082801585401800800c0300350300c155032454000c2080c01701e80410203000d01022601000548105480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 180480683 1250 180479433 180479437
    0x703061a0705160302180405030708040f03030206060315071803060501030503120c04060504050f010203071a01150305010b18130207030c02040c020303130204020306040e0a05030c07050a080a12031107060506030c0105 95
    0x10096002d0b104100706c12040140390840b5030403610440c22a4103040341650703015419041074202c0d090800b09518100181a41000010780040d005c0c4c0c05046246c84081b2005000030004201c04207014400c006155414100d51100d402541c004104002c00e5840c1d21307005842c3c2e445144103980202c541008100704e400b4040884d001ca0f0041d4440c0c51401d03207060b003882418000c0e0300045065010070301a041c01f1032440300d030130102c0ca0740b0319130003003269810a8901c400d500c4240c1050400c02d49800f0050150b4800801224a59584a01182400310041c80001d003c091240028140343c0d0001c42d40c0800c058001c0045c584c0c07244202e609101c405030810040740e0381c2c0000c81e60340305401002030780c240150030b00d640110f400101c085d00214500000f000600c0c5005e4001c1012100c40d1706c002841c0b1b401c05014071401002d0082150300380311a0f80741044050351000303100c0d8041c0640341d5801c1107070112406540402d40081c800e0b0402520f603100d6040050003480115007a900078040c62410340065842182 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 180481933 1250 180480683 180480689
    0x140d030e070e0a0f0f0203040606090e01090302060105060d09050f0d091401050d0915020a0c020f090403082d011404050f0c1c110304080a09050f0d0b0703061a070516 73
    0xb4002d905540f03840422000e0b101c210250a0495a02e0400b000c8465440c0025480b903170240c0030101381603241030548001c41d03440710040e2101d6490301d2068000039901140c1c5c0703030440d5000c40c0e00e503441e210007021a0f1700400d8061001480c92103054145020b04101060880f000882612100e580700d503243d0403108a046101036507400100100280c480b0f01d42c490780040360b803e0150540d08006034003000900e040742e10a04510001c14482521001149000f041c0c094400d0815204980035050568002e818484094500000e0040409030500d0390020046404900744401600104c1355a58180b81507045a07440c110318059400c0c48005240d119507041c14a0181d0031891a00e450300d1043d48400b8502d04500020901c40c41e140e1129010b61500d07100594040d03401002175a0342c402ca060405032441109500140c0110022688a002d40c1d8844069207000e40d0040c4408030320b907840c01e204500034030f00390304440415180b01071160b030740201c7e44002d001528811011038018103011103e5501c01c05181c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 180483183 1250 180481933 180481949
    0x1701060320070f1e0b090d0504051005070c0f090c0207060e0402070c0f030b0609011403190201020a05060702010518011a01031e0207050102030f0a0504030f031503140d030e07 77
    0x50480c066440800008100c02d6001c3c60306943c2d004202d603181c0c0c548180400d030035400003a900020390305000c2c0300d101440d0025440d6006164048901c100035042e80a01d105162090440b0300104100c58001d01c22216000d6100003031000060300c0d030142742912850790090220380b41c1360a1199078645e000044040c242d50240d1203000100c0e1b06030702000b0280d444664125514030007a500042c01c6100b8442c0500594441c1b026100c07249052010301600c0041603004860030095100407540c16180404c003000640d41a2002c00e05a519500042c0e00d032050f0514018000e2040318100101d140c1e06600c40f500500130702c01c0321240c20080010981c283c842c86144448034500c9120454a035600991041c15401d24040c03c2c14400ca200d24040300c101d8002080c2911642d40000410013400c07500f00015501a4010700108451304041c3c4008005503500c40410050698907042d28038a10f120181490003103501c04d0741e403030411136004080da456100b0060624086800c03c030a03c420310501140c0c0c401507030451 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 180484433 1250 180483183 180483221
    0x80709090f091e0302062a03010b0a03150f0506070c3501090302100e0114100501030b0406030f020f30160e1609050d0f02030c01080915150301090317010603 69
    0x81c0f2400c41354081e15900e0070800d000d01c480003c0d080a1f9081c0598020704050000c43e88404022202a00340c552000f2060b000c3c01e810f00c020b00207000c40364903150507500243c0f100c9440d1100c0d0316011401d0038841d04012510004400141500a0310154212100c51035040c080003440d1006002c900341c1e0760741c14004000d85c010310504c0b8a401c03160381c00041c940314410000710703d4000301c1e0403010100a040c1e0712441000003440080c4415605409600200c010560342007200e40e1a58451566034a8911402480390500d458039040035560001030441495035002c4d4110021540c0c40341c902000c8081c02061054001d201808800710040d1802d281259150700c2d0a0002e035403020380000780204c8000c2e851003805011400403074292681304820341128030070441102e4011080c0101898103010310a0300d410482d11608010014502080411200140f000c19260b2600d4848050f070524a070001c8194142d841c006c081c0c81807650150008015558482c1d064a999803100000ca0a94403021405298407682c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 180485683 1250 180484433 180484441
    0x3030615170907030b0c0c06150a1205120307050912120f0325200105190f09020d050102040509010b03090303010e040f0209150a090204030b01030201080709090f091e030206 76
    0x460100c45902c80090000c0c0c820140c0c6030354400500c00d07400e03284011521404901c2010f8031200700b160540184000c00c00c140b03980d150314002031607040303d03006416101d41c85000c001c007085010481d00c484030006100403a00c0b0300e4214070003005074100c0b40c61241f0544111480c0c60b4036000100700ba402428501c20ba41c0d00d00701760681d0200c2030303030b10142407508404007900d800f540082031342c0d144800c4a1034655035840d02d03014464022019418120402c0c941d0791411062054821144480803400940b4000102e407d03802201144000d1400440180d0003038004841c00040020660040c0144c40b000c03101c1e001c0c00d07629948403102a010407580403a8a520410052280d25801c00c000d650084c031585036000c4103440c1d54007081c141403041d01e42100322084252040594641483d00c80007502c203a0074114207162031515051401c84040c800641441080700110705650310501e161006446007440a0008104070750100004001c0c003901915030004d001c080344030042d05d0691030b048081c4c15500030105621 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 180486933 1250 180485683 180485717
    0x303090402030c0c010c1805040b031c031439030114151204110607020a09020901020304260105241005090307080606150301030305030a0203070309020402120403030615 74
    0x2002400c04402c000052011810130032090150ba0100162a541d581e01010940c00d00303840381c40c0d03a4005610442c2002c0c0131014648001a40c0e07014008525450301590070b040100368002c0180a1090000300c0718103041010620306000654540050b5006c0880d0004503221805800b03150110301000140e010001005600d10030310440015004c02040e0640304000005804100c1e80700740b94440702d86520100300020b201030103114140700364040e0341181c0ba0070465030002d800c0d40780600071001d18590209050704682d1082098601070f0082801e1500c28510503908001002d41035000b581c1a0742c00c0c00001403060b000c45204480c81c0c030503000103c104040d88410000145d602000480c20007038240058401c0c1da40c20891030004001c440094001f03030501c44184481210413080002c40c02d802000100700103039100040b41e502158a98005840e038440800c22005482440d0300a54068008941c00ca1340b00e44080e50036001d14825101001155a1551036400144140440001096864545002c446 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 180488183 1250 180486933 180486937
    0x106050703180b0406200601080c09150a03211d0d15060b0c2803110304050303180111070501120903090e0906091b10140c06090615010e0303090402 65
    0xa15902c0d0030401903125000310000d5001588080c2c0043c04101c00180760010450085512940080c058000c5605260380299180c84001c0c0c01d0740183c0d0b403100015144544014000001c0c040101b6400c41c0540d2070601c071082c0c43d40c2011480800005440b5008900e00078030340c0030211014001421b00c542145000c0090307003108188243c5401c0c2d08a04d43c581e0080180c440c00000d4101c090303800d5105c2c03a0042c1001d180184c0004403103100c0c03140045080321040f5a080044105505241c850400c0c00c42c001071904600a070b03403002c0e400d444082034121100121034800801080280d881c0148040040402c0307659040500c50070740802d6807521486640300312900480c1d00c5900908080400c039a5640a88510b00c0d0100d41e508214bc01017424041c0c240d0041c0074144444000000641e0b00d030b602140041e51008070031840200303002070300c0c11202c40405601d003683c540b030b60b600c002e843d560f00e0030344081038407800d0817a41d440c11940e0540d140743c160341c0960b80042c016940600154104103040e400d010080d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 180489433 1250 180488183 180488207
    0x405100c080f0406020c010606270b070809060409090503040504110a1d030c0a03080403060b0d051c03090b040b04020a09060b090f01021606051c0b03152205150109050106050703 78
    0x66174081203501c003c40300900820000784070360780d00c0c0d1240c802c1c24405091818440b1603080c003c1c8040c0502001034100c828181c4641e603400a4040c0d80c0c41c0401c00c0001c0d42403186038000e030102c0e230400f501c4100b40700003c40a0001c4480903202446500e2000350340c90703810b00c03a014481d8003083c0c030301e544450b41d07550382804000c0b02c0001908031404044024001303143c800f00d039801201ca010f00020180200080c0c0e0040c10003117207090302c840703910b400d00d90307540382d10380e40c030b01940c140031a02580920f80d0980c82a0054040d481d08142c2400d81420300f030a1202030020120f44c240e001d44040b8a00180c070400c14801c02007103a41910f030b001e061844680800c142d00754102c42813411803003100851070b607400e1888010002042c140d121255240301041c0f100d0100c0e03104071007080300346103040441c003165140858010740d2a1030703400200b01c0c140d440258000d16103415440000c2190b8010000744108503000900c60b10b1104407021200c0e440e80c0e1801c048050798424064040025000e028510000e4001e049803004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 180490683 1250 180489433 180489443
    0x5040203010501210608030d0905010b040203010503030720060304050d031103073e0607090b070206030402061c060f03021305063111040302011b051e1908030405100c080f04 76
    0x10450790340030f049241d60060b52314031503403540c0c0fa40000704102c02440b41100e0010181c03015411507142400080e124020070303401038601c2c07030320318200e4140000541101c100c0a00044c00e80c0c1c1c507420301e82801c0c0e07502c1310b060180320007080c0703010301c400a8000c8240580748200c200340d460400e8407608030000401e072000b01050080351058a64075680b4030b070241114035802c5070090000c210510340070700004d0544405d503014860b142d108200b944090f885000440c1c1c1d0194058505907691110540e5403290101c098407042c05052030081d0204814003420710742c0302205e00031240000144d4809401104a6000fa143d055105010200410383c0c0340b880d14040700c070060342c0c0702d807002a58254107804050b14100400c155041500040c18411984c00103034500d218003880602c00951081551007a40d1000810030141481c40c00981850424004011105c030024420060348041d140c14a08040107820075a400c0301c1c2800b0b51906000160100e210f8100d8215851b07036110815111100307010103d403400350003669 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 180491933 1250 180490683 180490691
    0x307110105180d2c0307170d08070c03021b0d05010c050a1d09040f02120a050c182707080f060604140403020a030e01032712020c060d020d0b03100e070504020301050121 74
    0x804d210719071841f00d030305130303078400030b0040000c0100c40244103e100400c501e0074007054051000c0482d41c009859031802c960800004c0307019200e00001509d03000780f410014025801c203008502c140350301101900211845449ea240c1c40646005242c0400883d041d940d078008121000050210341c039020300203c098009000ca02c000c100303092a00e8288038005805440c903510144812010341403001d07100100e901d05002c4011141440c445940843c4044007404503c8030f84100020b0810400380941402401003070102c80e1800228940e40d600c5640071103001d4461850700724049108210343c120760340b1540e40750740644625401541c00740da0328502d80c04900d040542c0ca041c0482c4038802207500c40c815040d10701c814815610640341c81082c1f03071280310700c00c0115042420700c036640303807280810380d03140d010317180301c056100d82d40402050014818040707103d0341881b480c0c1e410329000d02c659009191006492068800203030310b413014081603220071300c03c44d40000c4980c841c40300500d0146401305000c0c000210b002c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 180493183 1250 180491933 180491939
    0x60c12071e050106061706090a0c02101e0b0604060c03030203070509130b090907051c050a06050f0405070801090b0f190f0c18080307080307110105180d2c0307 70
    0x144510451601100c40d41c0d9511402d000c06604120a01b0710300c2c4407134042c1c1e82c0a15010001c04c2007404007402d2006c800740c0360040c0703945090003805040e2185040384400c001c655120060542e00c0321031450542001490b10b40448154285181110140c8503541c881113114442039508500035030004003048100202440b0303030241c0350b42c0c200c0380d543d0300e103100203000c1030880f41d00303040141e82600641121000d5120250401064458a4000040880f101c442c22aa0410ba0401c0390404c200301c034000341610300d080100440308a41c4129540034600550440c0c40060301c0e982010701b295210040980440c610341c001031425001c1c0c8407026032015418080007048190190004150750300380c8000000305440d00e103881042075102550084420300c2080300c0750018a82240e594492060b00c001030f0800400000040c600e5004191031041260002d000300304610317140020001802c00c00030454850b00680880408a6124110400721046030090718075000c2c0ca8840e0000007440c1c0310040369058010b1030000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 180494433 1250 180493183 180493223
    0x30f0c05031b16050306130206120a05010e010812090d1401090c230603070302070302030c070807030303060b12011701061d04020901050619051b030a0c03020705060c1207 75
    0x20340140c10036151080c180445140080f810014201a80b00341e004941104024554000032082e42110080003000350442c03045c000701c2d43c248504401500c0c401d81c18400d202031f8421b40c0d842a8100c0d407104048800700d9032696a1940c070b54807171426400c0214418003502c07511707181c1642012801e9203e528020500030307000326103030b0a45006000a0305c0c6c0021120081003c407110fa110a0390303a03080300349100006081400010030a000150600701050f9010440c01c003058002c10885060110034000c0b107410950350151196144268082240003c4c20141c0004100d0402d00955210103541e0041403a161309120b250000d41d01a005d80320500e640305d140010700b400800c1c0780220240020180701d0001d24003030041c42031680c3c040e0320040c09540108070140320400c50041003100c00c4c8031454156690600800140c1000d031080010229034000016000c1103213411030303c900c21485c400c2c1c00380e98800795200100010340c090354080100076000074800d1034414070341c0e400a11801c0c0c80b42041c15100b4030743c4401e03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 180495683 1250 180494433 180494437
    0x10302030f16150e1002070e01050d021c02010509090f0603120c150a1b030902030c0a060801090213090c0806010906090501050904050a0219050406030f20030603010902040213060e060403080403030f0c0503 90
    0x22171405600035820501030800d00d12445405820251026800c1e0002980420f00400340700052240407200d06500300c1c11a84902d0445101d1000103110b100b46c3d042440380c0c80b12980d03094400a2003032081d2980595002d00c804113980441c80c0e400080c000c0c07041940d00c18000850020210500c2560721410070704040d9820120350320800700da6800084e45801441410701d801d0820030681c1c401e2100910802100e070303200715401d040d1a84d42d507000d0b8607040d1300d000b80124880d036500064542d508010b01b601540760300c62440c80c801e03942641d80000007a9275000995030301c5090300401b400070300104001000f43c1032541101d070700202c9108005162203c0d40d090440590244080b50000880000e020401c40e903143c02001c42044118000304040301b102d003003814040c031560b00300070700007080030000500c00da8003036000300c0080e5005481555592440307090780c0000900c0e8041c00000c1617000008002c581062003c1d2420341ea442003080b46410b04548007500c5150030000442c08004061112000003042400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 180496933 1250 180495683 180495709
    0x30903020c03060a0c0e19061b0b01090506041401150f020304051503070906030c050313080d0515150309030304030503061c0b01090501050f010e0f010203040e040b010302030f16150e 80
    0xc0300041c110010040180703482e00d9681401d100c0c7e100d04440c0d52066800b204e405003142c0d400c0c1851040080304401c8501110000e803c082d0002c0d20074400040c2c0355203541c01441c4108c104440812840424001e541000142801641159000c0c400e0000d542401060401e01c04403a900442c0c0c14250342d200092100d441000076902c2a44022090120240d00a00143c01503c840e0809100000107500c00034102d002c000d008107183c0010450420a00c44000121000c80d50074090900682c40c00c41c0c00b07141d000c0030040781c0a004462221804024490032004d0700c0c0501e40c0d68000e145980c4031920111102d41010741890707440190f241e9104145407169100300b510901c070361160182ca41c5800300e03001c11141e059000502500c85114404400e03070703000031701c0120340d84c1c12a42e480302c27105000c3c0100d00c0c40c0299046010551a61420b01c020b0298041030541200d108400301c07179800902d01c0d035440d2106000e01000290350100202844141d0b254801c13100e044440786442e0b0312100085000414030a0304c03003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 180498183 1250 180496933 180496951
    0x40f0f0603210f020c13020c150108120a0206010e04020f0d05010b01022109010807021c020a050709020f270603070e010215130809030a0f24150303030903020c0306 72
    0x550000101e0b00729158900d641440390030100c041c800f070550065280c9000d000018483c58110b41044e05000e407543c1a1a5001d131010111945207000718180c6480420a000e940b200b446002e280d030440d5410f180407a040030140754098501c9034030703141c5078002e1400d0203041217074130800c0021040c8240e252001040402c030700513400413030494242c90001e4240010380b1400010f480700a03010240d103a40b441c0403608811000e1a11008550340e2000c100e08003042c5502c850f1403201d01c03043c0c100c41a83c2c00a4107000daa4020400d03a20420380d42c80922040740714100c04080c0d410800d00000100080800280040c06082000c10788042d803018005080c50b03004590350000701e0030320022417286583c1001034044014000290f20001d041c84980c02d2961400400300030202440040e26548039281441550340d0303142d000d07441c4c1c0600c4915141903d1495041a06490208460126070303041c009640039450345021f01185076201d1a0075030328110003030141d0316400e5055214a4007249241c0c1c404000c0c0c0c0344030307035058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 180499433 1250 180498183 180498203
    0x709111314090c0c010f0e150109020306090403051605030703050c0607030c0518030109021f1413030f03032307090b09060301260303102c06040f0f0603 67
    0x100280c0c40341000c480d080103181c940e500c85964002d484000009400c00e0078241c01c603403203a141c81001409401a4180358084c14180000020340b508000b9484552074460083d501c800d0f070322000b106040380070843d11030b544030030684d0116011a010341c000b400320b601c030590042981106901d03080e1444e4080d441c0ac8000550000e0406441103080c04202e070060050301d0248030805440b0001840d038040c40c1c040090000007650540380f142e40950203a48656409403440c11400e18040c40a901209040c0000d0085028400320400d000c0796038089542445c100c03400005004e046448500b0340302c852543c00c40925603148600c0030040e00c500208034074210420301c0785c800c034941980b0040c10740070598411440c200c028080d58074190364410650b0b055440045456041030a4034040c0c140603500c0c1ca582070749600000050189007500010700030103450782d0168100031600004c003000000401c0c030b0001e4401491440101d4420700c0d0a030030401e00510340c030f01d01003490004c0300440300c119402c55004030b52102d00303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 180500683 1250 180499433 180499447
    0x203150607050307050d41030a1401090c02010501080601031214090607060902010306120b01050607020402040308070b060a0609030302150702160609050f01031e0207080f070506090601170d11070911 87
    0x12102120013842e10240c45080f06211400c070b010700c01f02818188490f070b04c0003c0000380c0e1144ca980d0260b1040359902040d8407455039920f15440c010517003044540015401c00001113501d005c00510a4101d82d403050101c4a4101da03c401200c00c0c407442044080c100004010107645542d0f400301410140c0d000300f00004503545207100141c00c0318140c0d07206d02c5e0402c07018400350000c1204030056904464056450640c0d8245a2001500070300c90ba4000500c1c40728042040420b116404110398483c1c4025900b564480d92261410740310450a0320000b00141e02c08440000c0040941241c0c136040032039401119400e6103441c50034800d42d24241c00610020309040c00812031498003081410520201782810080000303080b01201c912089040100c02c8941c002480804000340c040407502407000301640e241d00e9003c145803403a2a00401c0d1800c212a20440001140546080b10714010000c0f0760801018442903081094603000c3e85035001800d0307030041010028030106140603100000c0c0d4801501079603240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 180501933 1250 180500683 180500717
    0xf0a14092406030a030c06020d050c030414031218010902030f0d031a0f0d03050f0f030601080609060a061d04020a030b120c061606020c0a050c10030203150607050307050d 75
    0x39020422001d560210062200c642c401003009035110307405145c0511503503a14184100640724040002d000e140c0340c030040203045509200130f94003a0388100b402c3ca403000c100d031403095030743e02821007000103450182010443c2c600460020207802102200081501d42d5583c0020b4101460056111076542089030441540c036414860010004400940ac44180590b4004180c80800d0101c00d98000d0107142c49000038140604d05440c0b541c40314068803030740d46449403055040e81c0c106907512408100c01e82c010602d14a440e000d194803582c1c0c05840440d00c2440c0c100c080700c0b0403929185000c490140c2e42c10341c1081d9211400206250485510040388003501c0105110303e90400d5003820041d0f030000000f0b002c1035036070325003102c112480c1c1080c2c5c50383c9001103003443c8000348950314031244075106035022801080030104640384103010884502030500242c00080d0140e21040368a0019100c07c25035048480c0740001c0944203060160048038200255607071103907d440c26280200020400b85d5000044400b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 180503183 1250 180501933 180501973
    0x12010c08190b09091006120503070b100801060b0405090a2a0c0212010e1e0703111201020d0e010501120c1221020609070506040602060613020910081015080f0a1409 72
    0x44010700d040511001908c58a07140e01950b640104403140309008110f02003074403103010011f011004001c200c180d580d208000041d40c05441b82500456448000601010312032280802c905044495000f1481c0000303a02d400e0940720050100a006d0446001f07c003589510460300c00c40306144000003600b1070714030840b500d00300d0045004113038060045489411b190010542078100ca41c08400041040c1c1903c000078080301194004008546c804221200100030039000403103070031f0444008108130b07600c0c1c0000003001c00440c100a05155101801080030100300340540d10f6050180051844031f8885c4e0003895013021203a0644801603111505000c40d4400500c0300800802085550324646460001c0107511a030008180358481c400b11071005400d114107030100c580e0580c00030a17124018540c4500a030404c5c600b55620614010442c04c08100c045140c01400c15072905900e483c2002c0c0d030381c48803000000301d00400812505485140030041c000a00864901903020740d00078000c4031042c920b0822000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 180504433 1250 180503183 180503189
    0x3040803120604061403030a0804061407030c030b0a120f05011d070e0903093003031e0907030803010b0a09120602040305010b09010f05060a05040806070e12010c08190b09091006 78
    0x202d0321005031031ba078000003120160107050500303c0c1c01e55614102000209824100b00700d40390f0f0400300704058582c0c56844040c1c06607194070200050031180c802e0041c620701c503000d2854110104602c2c17070040341034000b211095511550000ca00c03003406a84280c010806c0b10b0301414217034000c040900001c401e1642c40c035031020000d001181007280040000340607005a5800203400803001c8030110840f2680380c803a1039003c02c41c8040b6581d0742000800718110121244500e00c0800c019030102c0d50008010074120f0841e900003d0700c5c3d045901307006940902e0341c0040c00380d0040c4150028002804c40b50702580741071807405a000107071a1483d40c01c0580c00c1d202d4501020f4412120980144003900040c1030082c195102902c41a40340d08485d071064440c2e1240740c1001d12540f06e05e80c20882c00f240d018003030000c3c004050b5510010403101040b02d9007a070306a841000c002c40d40c40000035035603a070b24104c140c1240c000080c010032902c28090108070b901c0400e1f5403e0401c5e400c00303841811140681d009900007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 180505683 1250 180504433 180504449
    0x9020111030a0e06030a18030816050313110a090f05040b060612010b0f090303031006140a05030f1302090a0c03060f08190804051906170c0a110304080312060406 71
    0x160401c4040d004003200482c41040b413203010080007084a0080300d0748025001401d0102c0c2d003510f08658240a00450001c840400c01d6080130014000c80031700c11000e50340201b645030b88000501ca1031399940109040c0058442da085000c0c1c1c0b10020b00030300e40b806a600c1c00341040d800083d0500305800c040c00c188200034000c50142a08219000c25000315080c1141161400c2c00003a441e2301e50810081c6042c0f050f4400320354144008003e104141070081d40c45802c8440c0f81d1210400e00758405c07818002e9008141a860100f8030a00004480e0003010603416032081c001a4006054485a030001310048d00648082c0001c1c0c0e6030305981c20304941c042c40740c1c0014101c10030009102500e030942c11640d8000d0121001200b000043c0c2100c104103c44058074040e000003030462404d81e01c02039104092a00070310031440091a140180b04020b00ea4002d924010540300a100d450507103010411b031074180c2c3c0100b00341c1c02d6101c2000b00241e504028005414003403c1e01d0300c104260f040c81c0b020003068403601d80156003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 180506933 1250 180505683 180505687
    0x2010c050301060e040906060b0c03030f15030703030806030a08030a02030f07021f0207290a150f0b1b01050106050a031415090411130b040c08060112020f1303060902011103 76
    0x2040f207402140f907458030b0758110340101e681495440d185020b403001d54427140b412a00410f416408100202c090340c801c0c0c201001c0e41d05030355902c010041000e0143e103019601600500c1050020a05c2912415030142001d41140c4040d4501d98170322680d544115144410b1560100600988013080e00c1e4142e002080c602c003c20722100794003c07076a19000d00084540f94594001829000c01101e803a0125496070003041e002d0a440ca943e106020324203084803520b03081843d00c0a04015011021291800d5850020580c80035608051603050140d00a0b804c41d0000c100c04070400b400c0d40c1007402414064115035942d10345176220040060103590700c0000c1c490103141c00c83c0c2080384090220f01e000c0d1168104403184805038646042031a180391015a001e60400c03020b03440840d4018982e0080c40d41100280c40c01c109030051a5030444444030b007500c59500040b24174006441e50b10f10344c2c000c2c007440780b0110320152070150400b600c01848015607104440154954104409560308105450f4010f00700c1d1003e14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 180508183 1250 180506933 180506939
    0x80105090d0206010605180604030f12031515030902030715120218010305061201061509170a061d162c011203090b07200d0b0a1d06040c0602010c050301 67
    0xe9101c8505010b910100100440c6440d1f0405039000080032000014103c4d603035494807804d1200c06600340c480103540040d1011140f4420f50311911032144d0881c0b802100b6000f5038184901102e50750010b0341c0c500700301600d5110301800b41c1c4e81404040001c05200030031142c60400c4103030181c03aa603515801c9050b41031060240380c02c0d01d2540c0032031000f100070920300000c8035501c09000075882c00303000041404561034000040b403c501e1341101c01c031022070180c90340c90342c0c01d03075540e0700d01c041c0041c510b401c5803540c02c11510280054000d4000115071f64a44030500200e2100c03c884528000385e0400c0c1d8280301100c03a40c01c00504441c00c03a14030195208030700c040030080c00540225003942040c440c3c10a1031020030301c49402e05125039582ca01914680d0443c1e41da650443c10140003000c40c281344081a43c81c000108451407500d58080b10003650b114030000000e96400850100800c1c21115000140c103051840f4410700c02c090101c0303441603208490050019050000090844528409a10034420100014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 180509433 1250 180508183 180508187
    0x712140405283e0a150e13021b0c040c0903211202040902130503010b0d0602070c15020f060703090b01051201110d020a030e060c090904060902060310080105090d 71
    0x1540d82c10b40240610350000042d15070b200c804801d0240c0c0315080d60b002d51001c0100107520301c0d03600741c14204456142a1984991030402041c00090b200c0c0c0c0880c4010304084600d042c2010741d40021071810ba0010309100b4980c00310300d01290340503010700844d0460200c0420624041c412126080b82a00c1c05c40d0a40b82580c1d10f5003078100f5040980e40607500110a03001c2c0c41440742081e903c1d0620200740540d04d41d5030302c2407102c001e500f09840303150400b41141004582405c0500c5402d0081e08001c0140c0840c26864490100a5018940c00d4a900404802c0441d4070881003240381d901803171990040031184503220200c0d00b490000352441e0105801c0c00021004a052490704c1d9042d20021601c451040c80b1072403d05004201c6400081407168000ca81d52031111113a9020b054400341c20307102801010b080b03021282e2203407400c4400441c40c0340244010800c42c01d101c14099406840303100006900200740d00010501d41003100c1c901c2c6c8a0009000900402101703014081c1c0044c070203002480101c4081d000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 180510683 1250 180509433 180509503
    0xb0a081f020304170705030918010303020f010e100b24030106120608070303030c050c150115080f010b09010918150b07050a03030203130c030b01290405090712140405 73
    0x110b08244c038003082e0141071042c14001c43d0300101006143c941078569500791141229402d100c1580580603034800184000e0040c000c400b081404a005411035040072400480105481e500c103a411a88076000880c00380040e1002c5a6540c5016040d41e0320f0798035020006140f5485004120240c500740300c41040881400601e00d02a01c4d85070030045560680f00710119642d0040044908180c810354013011030000e440c05903030741640d10a0505c501d0680c02d07204181c2c0d011100341c07403003d40744903144010030851807140043c06241394145456810341d5920380140510604010706100035541d68414200e250190390b030448010031080380d03890304017909521069220381c0d0003030000d001c1c16000000107011380443d566408080e0760154140d84e031244c60b8104014142000d000e600c09400c08000c2d1522880818421f120250520b4000705140034204000d02201c28401f40c04002406990703c200c1d48542424000c00750710007501131096101e40350500700285050580045e481005800c420115000801030710 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 180511933 1250 180510683 180510713
    0x10f0506030d050715020f0705030d09030f020120030403050705030c070f151d0f030304030b09070602060610030e0c06030a020703020c010f0c06022d0310050307050d11040b0a081f020304 82
    0xe401a141c0b000c51f0b800005c5c0f40710382d0200400c140000141c1c00c1c1e0070092a071020040d5130003031741e07800702d40f03094900260708941501948201180c134082e840341c400725030600110750042c801e00e420381c10107141341d80b0a031640e000741c6030741005a00f11110a00c000c58903495504004c0c83c4428400001103800d840140c1a0101c0224261107011014040c240507128201a04143c0d040503044075540e69480c10601900001507603158038a002c1e200d000550b8a01c0010b14901075480103f40800766200c04a0a90041000101034021405102600d44195036440041c52003010030f0b49004d030b62a081450001d081c003101c2d44003141408160381031211449d0740692103400907541300c2c00059480e00080000d184480881501c4d04090300b6903000001c140d81300c01c0286001714000c0b48141022511801016282d0050b8040d99801880506c184408180d00700e80289203410040c2c00024000720b10303400700b4080d141c141c03c1041c155000039900503005c0801000c506079a5400c24045007982010355170000e008105007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 180513183 1250 180511933 180511973
    0x30b060613080d0c11030705010504180e0601030809040f0e0d030c03090c0f0807141f0c02032a150f071505010905100905090d14040503010f0506030d0507 68
    0x400d011480001e403040a1000d8a1102c048420319101d401c07006242002c0780c0805c40c1d006031034009040c40b5080004103001500d505850700b9042c981090f000c448092468031013202c0031a107030f40d00e0380b4100310207120150196008a821030756900c0c0110a10060b03403401c2000c042040d16101c82c6918411010502e001a02014500030502d19074888044014090f100e0015150121384400080c0c840c825011007403c680310001550301c1c40d41d4503005218048509456182c100407100300c2c41200c05040705591030640043c1c01c049a800b40190007080c90304600942107021026021110118a4162441c046d010b0204844078629541042e4815040c2d010303060740e06420910109120f0304201075900d402e0010089003c0400156958840c6100941001e485c0c00000b14485c1c07038086420725890103140c0c27240305c4a40042c02030440b00b5000715011040000c00c141a1103051102090310740d82030003580180e1040b010302050300d040c000c0030142050f60801000f81800720401c09038001900a00040d122a9000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 180514433 1250 180513183 180513187
    0x304021807020a140d0306080d020604030e0a0e1806090c03030405040f1e0c080a020405180a060801021803160e071101060504060801020c060a0b0d0f020d02061201180501030b0606 79
    0x9210309a03d850b6042d01c008240300e51448004200718000101d1501c441069a003c1c030840b40e036590000c0d1542c00c445a100010381120700000c02090049003002c03880000945241c42d84d43d40d60130040b0314403005960b88054111040203e1942800030041c2e04c0d04600740d4805018510315010010b5030301c0c0300c4d6104007801039889000c404851035042d40400108207002c1e1151900320002003100c00280608940d990109404102144265082d4801d68040c2c442c041c04100d4920042e600040581000900c1d80c00d44a440e113202284404003800607041c069400002000c0c02c9005d20304050911400c0e80c44070000402c0000b04005004e240441c2c9904258182018440200031507002400351200e50010794009050240c0054492415070060081c1c18046082c0c0340715450341d0030310a05880c4905404c51780400c81e0000c1c0c0d03002c1100c2080d1000c0c03161000b0030640080c4144c1d408a031950304003a81004458542000402c8603030b851035414888e04841c01c80401866043d0b90300e864500c64050302c0d4602820f00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 180515683 1250 180514433 180514441
    0xa1d040510050909100e0706140412110d0c09090203211204210c12030e030d0b0a0e040f0c1509030b071b0602030a0e030705070b030c1207050d1103040218 68
    0x30600081e4a00d6401450606c449490046156500d51140c4102000242c2c02451100c07900c225405403810f0b1201400f0681d00000d0755107074041d021100196507684501300f5000413000404c041140c030001c3c4181c6078045106230450042605240991400260759420402c1c0a01513203425021034401e920f0381046c440284d00c07281004413000ca014415080210030720b1200004441d0403290507545240310356203290100d401f454040701592000409010541d01c148441220340850b83c104000342e82001d031110854950760380036910505d0050783c00392104a03140c11031004bc040300c4070501000d8050701c6220440f0305018a0001d00a0380b031071101601450107000402c840a106194140d440d12180411906110345402c00f01c000b0760080e40c43c0512185004454040d480020007a101b10344c1c1c105000c0c0c80c101b4905107017420950b0008255400328181002217640c4180400d103050b00a1400f5038400791179621004ca05012a0748000700040750351024420000140d07601c00000350241b032101d4080c191615 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 180516933 1250 180515683 180515701
    0xd09030b06011b0503071a01140d0210030e03030a141e1303030605060a0908011d1f110c03040303030501050d110d02040e030d150b04030c170307080a1d0405100509 72
    0x2080c00408a02002801b0014071807001d204030030342d070484607203443c182e6650030080c1d59140c1d0440f0780b5508917919441003070141c503044a6940d45140b0a080204001060f0764034142550300854a008056545154182d141c8070018050356001e010000c201010f24030100440303100980082240f62000042022041003520030f80151000b0940a001c0742c0d11441d04020141c1820264012000a0b62800c1754404451644e41141103030200440c0140c1040b02107560411ba54650b24110b81e1481c0d0f0300c800c905108144100001e2600107201c0010b140c54030308502e00102544c0c03040e80071510070400ba14200e404528543e21070300408070126164a481c070041d1003c58040d00d00d401c890301542c000440d07525044409130700984904894450f0041d0752039150001c6030158021030201410100c0440028030080b40444070302001c010414003164100301c81a0b664111990100d0308510024030000241441803d600178480b14010f802c0382c060000745072003451150480c2a40c422248600306c68804520205 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 180518183 1250 180516933 180516977
    0x9030a02100c030212071d150d02070c0302030d0f03060e0114040b010e0a0b0702040f020c210405100519030c0e1c050102070503070b0901050906040b06032a030d09030b0601 76
    0xf242d117001c0c4251a1404410142130000e881003026204c0c1c0c250a01c54641e860030041448151b01211743d240c0c28000c0c0d00b02c5201c02500560790440c0d4003a0200c0b00400540e4080000d0400f00b00746645803031012040003070050950f110756000d840030241c1c110050007412801c100d43e80003103c00f603c00103405c640180048407035104821070ba83d00202580d00201320401c5440c004d002d214000c0c0c805025445000300044200e10550318400300c1d40e007004424143c02400040c0c01465004580344084c102900c2c2c00005081403101d1010b480403600004e03003c4107207111081d4010300c03010207082c20401d1481c100000703003d0b0402914064401d0071401094041c004001d0100c81c2e490750000002c40d1101c010b407401c0c59903940000025200386158100090f200c001c14002c1600c118560005007070103440d29030b01e0f1840192702502d5543c0c94045c81849050010445405884031040000f652499910140c141418518407038840c00800450000500104d4416920103401c85000c0c6440605030070104d20b00900c003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 180519433 1250 180518183 180518197
    0x501031113060302040f050102060f151201020c2a09160210091103160b040308160218060907030e0c060304020d0c030305070c0512100e1606080108010509030a02100c0302 75
    0x41c04919001c40c0c001c2d41580540103a034003080510700d290f922a80166590f85084854201c07284c2d413540001c40407030005180d000980c00281910880105102180303003603810861521106a202045103204103180d489010303061120700b681664003d4001011500403180208120080701c9905030821185108200d501006c811280c400c0081c2086440c0981c2c113540c030410980d10a220343d11840c1d8002240700c000c0c504958007603142c50306d080e1075507941542a07088a00010455522306c0d91810141e100c503100e503a076202030207180c0d0059141c40b031308000c04070300702401c642c042500e003100d00100480d001030300c600e080c8001c8a00540340c2d41d8520000d03603107141c008002000030740406c600108054103c03003d451420311442d00744004c80c0c4c4400070b100e00c0b44240402c0301500d50121200d049818216440980401c02d16800d84261030107214031400881e03900c0d4006030009401e01c0040224141c00e106550304100e182c00a180f4000c92018001e58801c2c201c4e0450702c0040c0e071400e5104455010703034100c82036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 180520683 1250 180519433 180519457
    0x110d03020c061c0606110d0e03010f0204240e01020d0e0d06060b0307030c0201090c0509071403091e010b1f0203070507060c0201020c010c0519050a0b010b1b070f05010311 75
    0xf807450110010b650918554107076418907800d008011a07418040c52030040c0000d54400207000071602c0b80c40c110356045181d07803550b03059542e405241144020721700040000d0b10701140c003000c99070401c200940000c04003920f11002c02503418802215aa0b020031204d0005038546000307076108540d00c0001e444041e0803080240464504030703000034200d41c080003a6201380c41c00e0310200069000c0c020264240c944060004000c0d21901b0014015450b200301c074140c00000b14034029007801480071090707405a005440c2102e842d07100800c00705010b03800321010b03441210701d4002440800141741c081503402c807102c1142c0600f071440c04000c00786940b00300240c074502030b00201280c1d20b20b542c0d13501c09005841e80d03d00903070040c095034410358460b5029003408240c060303110000301640d450130240c005100340d06041c111490300a904656010400c00014075000e010720521156030b03103001c0b400342c00051145240c0034031341340c12500080082d040000c0c9800100c400a08003c0703015040c9a108580c10303c80c4000d4404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 180521933 1250 180520683 180520687
    0x13080a0501060e010b0304030906120e0f0303010f050a1404090201020a0609030e0907020d0e04050c090306010305070e0f070215060604030b04030c03140906180d1502121003110d03020c06 82
    0x1080c400c05400c40c1c01107403c080e0924000e0b0342c0f148090359144c802110003401054183e01d0400030a480b403101645241b440c0c800000c0e116103a0840300f42465191038047d49207a0000c0010710074202c080107960001d010456860307805601d41907440006480b0300f403001e0300c1180e40380740960542e4004d001145150b0b80c825010440b1416501c0c020f498071101c3c24049000d200a4800100c400e4000902c2c141c00b011651541414000d1020400010303110050061121180501070915140c9081040901079072289010300035003410700a0301540807500030303c0c9605181a15007440000b0b60040b032040341c81c03c83c2c0e88154419640b031001061f002d118a610080140e1001d10400c028140c2c000c1c11591000e11960310802c01e00c44101c982031107401000000d951169040003c0d824001000b40c5c03980c1c0c52180640400000e5441da111000d1540142d541080240e0b00010103a2485949101d00380d40040b04c0228040c6c0e00b07045840750450364044042040c081c800403c40801458003c00421907403d10081901d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 180523183 1250 180521933 180521953
    0xc01060b030a020304060612050c0d02030304090c08150a0e0103110f06070809030d030b03120903070f170708030301120f020a0305032a060c0f0d0608060a09050606010e0f061308 78
    0x40080d1300441c0d043d15081d14121010481c8030200079101d84854005004041c1d0491020400c4480001d03c2412a4584010000080c0c900000c1c021901003820b9611640d403d40340c5030384103000000310040c1007031140b00350340010300c0308204030014503064a03000709401c060008000042818102d0003a0980d034407582c0851000b0401017440018103007840203a045c9c0c2c3c000c92030300a0560544180c1e04c5401d0303042e086440c3c5012a00c001d0405070504450040441d0007113682e6100c5d941a6400d00c3d041030309508607507020448040d20411a031001002500c005611307644c50083d410a8101182c0300042503000301c2c68820080d0356801c15044003541d08a41030300da8501c862002002c88410505000200c01140c00c0d14604900000c01c0203807041c4045180c01c1c1c90003010980034242a4403050900343c00d195039050101c0c5c580b201b04045072040000c00400580300c0c2503030601d10314000c8000c046a04000e4500044100c85e1503040710300640003002c1d07a6003601c2d010100280081031403103402c040c404e8480c0006034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 180524433 1250 180523183 180523201
    0xf030412030e090610050d090b0a0905212b050a360b1008060f07080a050907050613031505100501020a050d0810051f0f0905010e04020c01060b03 64
    0x80100c85200c0c0c0c4a041412200701c061102100c01119050b0b48040e003100d52405940c024401001154080c1100190340c114541e07559100c82c4e429030b40d13241169500c40400003040020080362070582c4030000b241c20751090111b6010050300c5000e030305010010720300d034541c590b00080b881c04001000148005200c0c80c40e0001e0b40d0301c01801c0c0c882e00c0d071000b070080301107e00b030210290060207402030580480ca07005e55001e480e0b0f039680e230001610404e0205031842001400c0101030009038010720348448580c4403420081e0b001081200302034580250307d890641801140e130000203842c0c08544083c0d40d80f5440304514003503614507410b180d20140138800550301d501100300c0306a2040d4800d004144180e402e0540301e100480c0e81d4800518000c0043d03000c2c1d400c500845002d4126544c1c0132a0035441e1600554841c0089041d00d080700c1440e140148903640300103c1241c01034a403540208007031800220b81444c1c07000092940d035070100824001d07540000c003025074800079004030380900140b070700c502d50720300b003003414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 180525683 1250 180524433 180524459
    0x8030412080a09050309060304111e03060f0f040b04140706020a05120405060d050408041a07050d020f030702041e0519050604060303080a0218100306031e081b0f0304 73
    0xe103001502041c0012030090b20352040c942d030b82d90890011414800004140310480d403000d041944c0c18121044040780c41e9644c0d600381e40040990210603100000c100301418606400a89a02c0c02c1b0303c180ca0405c46c02004004805074005d80103008a002510f403801e20900c00490001d15600c10b000d503000204240d5000209104054494021640d1520f41c0f4125092540198018940e0006007003207110041500c50f006150440d000d129480e19065480742c0b81d803a42c0080c0f44100303000140c0403e024081c80824020214168104d0010f069050048003a00f88c83c1d00c41d07640001e1040e96101101c1c2d4640450110024020700a001c0070442400e020812011201ca47c403602c44c01c80f810640002c8090400303004150449903da02d800c21140c0301d10120f40040e40201ca60000c5140080c002141d843c0c0c0d07141c00050000c0d03299200000c0c00c1d81541050a0051040d4038505880d0000300c00750700c0000d0086c022600100c6003c51803202184001141c0317414255044804550b511000c90b001c1070001e0006a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 180526933 1250 180525683 180525713
    0x80d0c0c080c070617010e0615160c0501030b0f0907050d09020301050f01031b0f0311030a02090703020d0b040608060a0c140309030a08160210150e01140103060602030f030112020607080304 83
    0x85d000d1800495039569181d8240900a180c0c0055040f4041a1941040c2c120700003a11402d9441a080104050400c180d81110510aa48030040c0300810400fa507010701c02c01110072000d41d04d154240b03000c072000ca07a08000185c220410080005401c50024050b1340c13010654035802002841241084c001c0180c00c42428013042c1d4000c16031100e0a015903008010703400031030b03c80c03402745800c2e5481d503150349401d80754800381c080e00360040c041c4400040e40c68080c018440d01c142d0700d0042c2c0398641628003208980c08002c9560146144c0201403140b8280010341c903901c110300030000300c8e11086110048a541e81c0030071094607100303c08001d01090510100141c010341d100d80d611485c59580d00351101c1c000c080e0040041015800094098400000075048a1a44070440e20410880350741c2e000c902e042090264401c5941c03040003c0320304040c2da41801707079000400462004500300710b502c0740c0541d054070040c442c2400c08480b440780c00c4110340300c1600f034038411500402c400e5120301c1c203800c2407501c07404107070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 180528183 1250 180526933 180526937
    0x10645230f1f0e07090306050f01030c05040c020703061109090a241512020f2802060403090e06010e040513060c0203031306020d09021c031209080d0c0c080c0706 71
    0x14000a20911403616000c031500b4098440000252615071103031a007082c0513220400304151154003201281290242c903020b4248541e000d0560342c55410445054804c1c1c1e00540c0c412130506440c42d8505600060120640f504440700041200002d03c0114042c4140403989801925480c2000508442517206007a04440001c0c0c40000e49016103080b640403034640500700042c03000c000b8056038a0305c50101d5550a100584c401403400543e6040b500460f0040079984202d010001006008880b21800c4950101e0003400204582e04185c1c2d00a000540e8501800d0880300259001582d942c1c80b40c0301840f524140a0030811890500140c001200f2a503501d09607446801c00341b4a0b44a1440041201e1040da241d0303000100360f01c02ea0b6074100203503000c1d00781c00101c691915034140140e038804c4010713500030040c1000405400460718002e03020190b44814090130619001c6128041650002184c40b01020000c3c00106131040c010b0942d2025400344e4003030080103020451122303a51001603440c0603180c0e29 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 180529433 1250 180528183 180528211
    0x1a041706040b060d08030a0902040b041506140f0703111204121a070e010f1403090d080a230901150e011d090c010e012001064523 57
    0x6001030009030407400070010b1030260200002003147c1d40300e0b408084414030080000c81d40200000c0001d09079140c028103070700c1952014400b00b00f055000300c101508c1e98003141c0510b04058600d050308516004591010381070003140100c1e07004a100501020150342070b5950b18944443c0c035034410880e41090f9000c11580350615804403410b940b200701d03c6902c41c0c0300913515000c40b6540d2000441c2e10105030725000b030501040c1550a121040300101851103000300c0401403601808149000b4090000607040707949071441d06182050294549030f5504034225243c422114644030400000d0050040c11041018070040740c0c6d0201d2103007450a010740c100c48400c3c016004000500184109401017a01e60032800d91091070300340000d5000340904210900141840c2002c2c2200d1984400c101f0702148586031140d64540c4240007544014003140d090040d82183c1d800600180ca042c00314095020303505540300300f85400034040b400c010390420002d0740e00d03920040407102980c501c0347c40140002d1700c1c1e4460701848 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 180530683 1250 180529433 180529441
    0x6090c020105091f020702061204020901050109081002030c040e04060605130c350f01060813151a030f0a0c12080a0507020409020409051c050c071a041706040b 70
    0x4140602d07809007800d03202074204074801002021032410908640c2c034845400740305070005070b03940750050309030900d0000c200d80e03413454180b040201c40b84058101038140485402c0030300c003960000450304810400c4400059480d110185c41c1140c50140c0d07805503640000388070410003046901e41092007224070903500780e204000b440e4110f41c10b4a1101e0361038030005401901185c000388c15040d4100c1c1030410080c600740342c405550000241d80c00d00301c400d650381d0080403004120980e4040c8041e0b5002e00c0c3d0120410500701265240c001e92010400080c058a86402071240c000c108005020b10a040c02022540034544000840c2c0c0c507071040c60f005442e003d4011000242c008003100440288940c4407080c41d25224540505aa580e00711010507a0005d958840e0b101c0103880d5480b0701c68400e8028130007402030103213004c00c003c4186260045217040003000e02064808603800184842a111039086814400003600020211406180c0c00560400c0702e000040e41e854001148090059000f250f909109580d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 180531933 1250 180530683 180530687
    0x20405011205010e030f2b0c09180c050304020603061503010915121a040303060b0f030603010f0e1b030c0603070305091002070f030c0212010c020c0418201f020106090c 74
    0x110808000210000c1100148500244403030b0074074090038001f0701401030000c030021021104100c03138000200707105003014004414140c0d4a41e10500d0352070b006201070350340b2201c02049800050f00c028014403010022a030f407941ea0054402e1642150302c0656180e683d03500c24140580981120040810043c02c4003181e40c14042041c8180b10750065500080004244c070842c003a074100070015401c1503541c86c004103014003200028407455080c503005ca612402c02208250860b043c1090500762540703070000741c060058020640030b5888103440c03c01c84010b540080405c2c00d200b489030300c20f81e105000004001a0301c0d00340d808507000380c41010496070348482c7e81800004034030448401620186200d0210030004e8811800b40080d940302402029001012038180f60039524250741d80070160300306c00b00140300ca0800744a074032502d61952145410a000c1074449004e2a0402c196281e00301025181c0c4901c10340f00d282150f00050f0040703181080c1074504420007402020b10703008200700a401c045a50344128 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 180533183 1250 180531933 180531937
    0x1614010c111603080705160f090c05070c03110301021c0c0e1009150e030a030206040506100e04020d050a1505010501080609041110020c0d08030a05010e0f070e030703020405011205010e03 82
    0x441c21074190510103045803101c80380c1e44c02c4080c080300c452047d20240c00c41030000c0955000240040f44503054814100214641981e510100c09800c0000c180400d5003c58414904101201e40002c0d45000062101003c60302900c10f2a2062004420520000c0b003600301035404044085159982d402c03c0083c48000c2002c0014480b0100002400101051007007096910301c10070704c003d42c0e0505800d000c0c030360030200e800d28800034020380140e0013001c04c00041c818240300c1194441d207032240114825041c40861b1100010282000e4092101c881c0100100704042104400c41504885401100003a0340803240191009024680c0000c90030b070701065441c2000c54440d4061a80859500180032640b024400701498190b00003085100744480301101d52a06e0800300c00303407401954141d9891600c04001001d0315410390008225915080403c40040c881000d0340d500244681747c880800d1441c1e5000914280c01908040e6006103417a00019020071a03044607840c0c140700b9002400b44e0301319451466264 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 180534433 1250 180533183 180533203
    0x702030105010807123804060b0f0102120c0102090402040e04061808070609021503090706090f060206060120030d0c0e0a0303091a0409110a110718021614010c11 71
    0x380070803043c0600091503010740341400481c0d122150102840000d04540210181e03c088941b0760180c0060209009003401000300100050f120301d1814682a00001e5490700304e24802d4000f1302c00424020070301c102c2901120416540140190340711616840b454801c0b250580d0b080781c0c4c0c2e1b0f141002d042d08858418002491103600040420304065241e00c03a000506a404c0f022070380440c0c900740380007819800e40065400345050800400c5d269003080710241942c0429000342380d0344031000208100c0345500103a915030041c821b2034085440030210b100042d03883c4000742d03102090700010138034451107003d9a015030601078159032411544152101030203030041c1c0c2d41c0070180000c0c1010b03006010b0403450791000f510300b0545003040352030941c0d82ca112600700c034961080710340c100303c00040b101006a0301070041101c204902c0b0141103100c4c51711256032210120354450b041d01ca500400c51202c0448100141458141c12a07030500d5040c040f40c0786d2500900d00d4407080d10101c1d0070f080d0519102c0038001410300b60307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 180535683 1250 180534433 180534449
    0x30706061d0708010308030c07120302041e030206030c1c0e0d14090315070219050105100608010b04090519020304240603030206040605220311010c0f020c0d050708120702030105010807 81
    0x490b400c58840b0f1b542a44000e00419000d24100103240005611924585110090307550040c0c8030340c20200d041004164003d00144017079207032041800507036103072030450f90004c2d404004640d4421050181982e0380c00f100320a001d81c00d1400c0d00c000d2501001081031001302c04c0941d00e1100c01c040c0000d0712003e1303004008915416070300004c10601d06070501c008494004c1c0c1f44d401100c140740261105084c400591190441c0c0c20394440d018042020180c41c80b4902030481d904016410303604000c80384147d030285110741c031880c03a16000869208010b1f400b1415558032602c03000e43d521714050502d142d940d40c05180a080070761110200d040c40408500c90078064962642c094000c070345580c0c680301c015180103001014050700107244404103045002c611110316209442e1100f412074011140da0845a188503020180501c0b240040c040550211300d141c00c100301140d80c4c0e09511541d0a00d18500031b21038200c2c0c03074984108035201848480c0c0a0151002030300c200c00034019a80c80b174205070303101c20b0030b4450182 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 180536933 1250 180535683 180535697
    0xf081809130f0303020f0d140108061603090f0b0405060910020903030901080411060406120f0902011b0501140903130b0c06010b07140105010311090a05070e150408030706061d07 78
    0x3a142c00040ea0505020b490054200000556280c4c11036200724241c030b01c199500d0401455508020f0b40307841c01404510003801c6d1301c1c80c0c0400080050107904406400700b6548400c1c030420007a4095154031429000400018a460189449607035040203031006103561060b5007049082007070038000c41e0000c1070060061400c14013103400650700820301400c121004000c2100341d000c0ca4403801d0140c8002c1c20070340da800b00040c190b061184100c6c1c65001d04051032608207010700340581d80140d18103103182c401c812039607040715660400d42d0040440d80c004c41080408001449900700e00003000d80b801405110b80c00030940c3d0713500580b00c40c80c81007001560359600b100c0010002d048500703000c0c2500718060b03d00c6551812900c01744c1400c4403c260000c0700d0010b542034191450b4204005001d9000eaa00c5404001d00d042c10080507090320311416407a44100c00321044c0040603450801564014250141141d44030314682ca4800c1c054503141c0100303020310381c1c24142e18107100c010407480f5010b2032054803460 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 180538183 1250 180536933 180536971
    0x10503070b0c100e0c150903061501110d0305060307060206010815090f03030c1305040c0e04022d120919030f0302040506030a0504050f0a02060d090f0f081809 70
    0x1c400b90840000403515000c1e008810807a95014001c070303a5000740f4500640f002c030b08000204031041402c3d11010401a4040c0306a400c00d031000224180c00903d411207500d241c00501c0c4c0120b441814001d4003840b00e01405a0000e0b98580541005000b00d2044068489207a02c0c0e9800700c0c1d40d18405d100c0c01000c1d03401500294030b1003013800182ea41003021281912070b8801030302c50b000d01e198015038440c01d00c00c0c0006540c40b106080501e42201038070003140c0c24403000b0403100c401000b0180c0d11040a01c5994000744150000e13015143c80450304007025442c4031401800c000d2204140c200c400302042c2800d00d440040c2c3c1ca81c0f404911140c00b08015444102d1208250301c0441d10744501080b107206040c0c1c20070004c42c0d160389907c042e41c0300340e08002d030120751441c01d494100c0c144454644404c2140c2e1024600c040140c0d606001d5400c065010080003440301c01509001109910142d8043c000e012500710840620120350000c2000c40040410290301078814020311000c410304581800006131540c10b50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 180539433 1250 180538183 180538199
    0x3040209070903050703030e13060e070e130906020d050610090b07150203090c0103061703090f040f0c0f090602070f031b0509070504030b060904170703120911011701050307 76
    0x5a049000382c030344041e1040d140d9885900e0f0120a0b0026400301d0b09009603460303645840d45d001107580d00d46107001d00101c0e25004aa284101c000707170601040c03001c800324a1000c0d0f12030300c00303a0741c42d100082e03030a00500c4403606060307009503c41d100481541e0b0038807000a1089c00c007802000520b60560341ea0b075481f0f80ca041c0391100c05400132841142c0c84c20f8111a0240000041d001860007000e000c0c0182c00c00810850000d000c0300e5040c1e00240309200d103101500340381040442550103490003550300065580d224000100200b21403051690070720310300605a01803503404010224048030a0f202c4110003503c1e1601070b83d4030340c941e220f0b012018401040601c00034842110032480e00c1e4004010000c0769032100000749032080c044030040c00190700400d042003445502d9500d29001041600c5c81d034540c0c1090380b07a1508601541840b114441f800240c484100f41c89641c411402300591001041145183e01c0c00710340e104c40c00c0721020700080700f46064540c10740c005c05a041c102c0f1001002082342510b06509 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 180540683 1250 180539433 180539449
    0xa020909010501140f0d050106110f100c170702070518061c03050702090723030906041b180603060c0f020c0f0117090d020f061302010309080702120d080606070206030402 75
    0x10140014018455170105030180f0380642002c01c1140c2000c6071759810900024112250300110722503d500000441d01a00e00104901b440111000008200c00c0940a01911219481441101d00021010402c5403866012a0b42410f03540c003203490703a00d0300303452a2000784422010780345641d100c500000b05211425003007082619072031080c14520b0821b11700d500044c0b40c034541211a040414401b02983c00c414090f00c018940003846200341d0740c00c42c105400d446944001c000c1c0000c00d20180c00c503084801e021a001207000520540041c1c00b8035081704000340e40a040c4c1440300b1070b14141005095108280a00100c10040180c0d500914800039841c08010402041c000d0039414000264442e001c03146001a8031480340c80e008004052101c0d103210300919002c1d0034484841d46030450001d0081040e980c80700e00d8012902480c002c1403007009030030f110350a441900f030001d60064642a98041084010546825240391622003e41310f96652050205606c121407000303510801c02c1000400620704690 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 180541933 1250 180540683 180540707
    0x60c1208040303060510030c0f020109030207030b0901111603030c03020702090f0604021b06041101020d120f0b090103030c050708030a170a0204030f230a08071202010f11120a020909010501 83
    0xe0f0100b401661040450b2072040310008903000a42c40f004080c100980010509444080c00d1008000110403500c0084d00c49030f2a000c01802c1e1002c00000c601012000d40280c0a03010840b0400f0b80c0c0c400102d140c44036a00c415100480c0070a00300f0b030071109103600034402c1d10045070f0064454442d99450500c20b8141610007000d1030352156080c02004c0803a40019000602c010704200246400d0515091200c4218035080b1403504651190000d41780b819800400c02800251180c400701d0503004a03403145015250040d0201e400020043c0000305140d0301644219040f4090b805a600941d244d0954680782d2041103201004103511042d6a8841207030110002c1d03014010304001400d180d2030b96684e003070740c5081801c10344014802f0808800c0181075030000e0840d4003a041d00600780030740c40380d07510103690041d07070801b407c0c20070900903840c1c40324001e401ca40000f00707501c6001c200310741d0100c0c03070540c0701d4116450124001c5a001c0c0007035080c480030300c2101c8000900414055490707207440e004552100580c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 180543183 1250 180541933 180541937
    0x2a220f110a090612090c03141c050307080f010b2a010f14070c0b0703020306041401060306182c10091101120b0f120c030f0309030106060c12080403 65
    0x1201080d00503403110080c080d1a002540c0390000700386003880041c0355050a040c1c0982441c50190701c400042c1000c800c05080304d034805c01203400928041d298604158a500c3d41c269000303d00d450500702550701000030340c800e404503240c902140d180c0140d421420700d02401442100081003008940107841031090a9020360091141ca0031482008442030070f645c003005001e50120380f1040c0c594418211001c00c84e600208600d0b00140703210240d100e206502401402d01410f056002001c076000740c44a03008105100f80070300d12281d003541e491200500034010345c0b04d40003149600b03584c82186100d10b07000d1405484028010703200c0b1032170303541898071030050809200c0510748100740360a44000c04a0160803a1203008504126110040e40009402c032604007501c202d0180ca0300c00c140d0f07425558402114600c010948031005182100c0041501c5c00100d80e110036414854540c0521101c2d20000c02403042041c15402404081d944042c291604c06c00c0c55801800309400100945000b8480c0003515800390280c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 180544433 1250 180543183 180543191
    0x22107051c17030106020d0c050607080a02090d050d02070f0e040b0705041e05090a06052404080a0b01090e1f05070c0c090e01050c040b0702060711032a220f 69
    0x16550b0b00701d079511040c03440c0d541010040010841140c0510001c404010181001e0070321092582e41e290301c842008200c501400030241c0800c1d54045140c1c1525940c80c809052060102c4990501070754a01100b04110010300c01d9200c0820011103007a9004200e81e416a4200c8023030b150740e0350301000d06070010f1410080150900000403000d04c0c3c4400c034094400e84030018600c0c0c074100018025007031030003050180f265040500812441d180d24000b040144000384051040210000d41079245120b0b580c01081c00d0700c0f0710380103002845141070246040300c0300d1140401c141d059594200c1e883c0c0244542e00c2c1c810300c0c1c032641030003c150440d4004551220182c40c00b2882c440d00c0f60380d101c0d040e07052a0070005a061707a5650750840003100344500ba80000c5020900740c20149000d0303107c12a40b04840009006400200d0803408110f540d030242c0d03140d510001d0030341e8041c00020480300c1300868080844402c501d03516174800c0e41820712258000a5402003070814043c0102450140050400c1040c013409069036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 180545683 1250 180544433 180544489
    0x130f0807051302070203060408040305010501150503060409240b0307080a170a030b0d060515090402130f06180c0212030705030f070e0a0e01050a05010306051008040309030b0103060902210705 84
    0x5001f002d100718400c10595450381d007941401401c441d4140c004220a82082c210f904100b40c0040c1526842402202e000c24090124544606100c10005a181083c060200c800c03003800c0007500704068412099040b58444c594607030400da0740e0b0000c01c401a201e0402d1945407907444c000c1c00000c0800011504002c03913211940c0010801c06100900f043e52207555400511002041c5604446d82e541c0742150000240d0502d5000100181217040040c92501e03952442d0480c1c0d902c0c2c0d600b00f0070041148220419100b000607808401900004640e200180100c4500c0e8480c0c640e200181e1b80a0b10303003075a5a40c25580c84020724490100c0150001e000c3c0808a051030845944d0045d11001914540001444c654540b00c2440500985a0461030616007040702c14062500d0b0701c0c2c3c10142c0d90034181fa00310250b407a2030070300361641c801580001d890080d150300080103021498012021552094907400100d079000c0c4103d13000700104001c0268140c001c050100998034008c0185909123a64594140c1103031a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 180546933 1250 180545683 180545689
    0xd080c12030f060102060f270106090c03060e0f2703070609030810031a0c090a080c030c0402030108030901031a1801050a080a031e0302130b130f08070513020702 71
    0xc804848085421000041090141d60401581c0c0c20100a00040c20309050186c00c010514100900074024201c00c1d1821440c941c0003464142c0b5000b017804000c01c4000c0d281c2c080c00300039054100025010a0a1600c001040f40c5000c4455120b10010b48884c1e8403a10303050045810b2107090b009044460340f00c410b60f101000f00a10092951510416000a1242c42481c010b04600d400410308410f044002d00c040000c1458026844081c040c001c114a91350b5544482c08500d0340034001c4003d070884490320010902d00c4002420345441c50341201210304440c0d5850410050f072109009281d0310b5001800100c90742e5020380c0020440385420b41d0048403000d103000c041441003803010003600d1040560001005982400d00d40800079003d110040c041d403521640300a48015064000007060000203040ca514041c400e1f8180d03202601301907190342c01d1540d5440c8654554000c07840c1341c1c2c4c2c4035090303460006140203c0d01e100c03000c031206503000d0b040b0710380f034042080a285080441c902d0543d40030080b410040c0c0e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 180548183 1250 180546933 180546943
    0x71101150b031005060f180301110f0408010b090103030e0f04060302062109030c03072003060403050d0506010e0310090305090303070b1e0717060301141008120304020a050d080c 78
    0x1c8694544070314054400b03d0359051160b00c254010300003000b02501d210507400c129900ba15203100c400b5014100b4401090060084626041e001000415000400b07140d4500400407030301040003d000b040c0104080284080007840b005000c1400404200c182e400c251400d0000740d00b00410000d0400d41c0c9401240066000c488486440c6580c02011641104052160b44c2c1007d0b01d00001d504244000c036100317640748551007000e0001d10105984129040b66000c1e00306030401c014060740d555040600d009007043d00a04a00b0b80c050741020005101940f140700e085500000c02401400020301078a00303807000703042e5004181d0802508214102c2d0300e0710100001d001045c410143c0c4001880c00c100c01a40b09580d142c040c14143e40504207202c1c1040c1d000103146c10508482000c219240c03561f4000900525040300e10108095041041108024124a0000854000c0030541380b180c0c00764494181d06200481d802948410703402d13810701550420040c000c25591246045616001040c07100618103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 180549433 1250 180548183 180548189
    0x18100606050c150103150b060409150e01060809100203090102040f030c050405010b0403050d12090203012904090507150507080d060f1205030a1815020f070e060907110115 75
    0x215100152210021030100820b03c03020401d041c488034254150782c5e8440900400803e141c0e10144c9034401c0b81015135480f421240100007a2504101e0610700c401600e41e80d0b0b942d486101d090300c3ca00000000c049005142d0350703100e80205005001124140014480250000341c19051150341c00d01020642d040000c40000245000d1803000ea0114a80020032040e04c00c16080108040d005000c1000019800244510000b0040c18402d0300e50b401c1021240040c400f09001950540c24003558000c02c00b80b0054030b4400708030441d1100c40140e524400d0100ba07412440b0000e0055120799020042902c4c8203c09c00040d404c07034038000b480c004141e102c1099941081c41816105039443d00c0800101020060070070081241861610411010f500e030243c50f40a41400c640c2031000a400804003021903210360009485020310348802e03915481c10095984403401c58030030f6207100b01400800c003600400512032240b10002c0505515aa4100c012500d80c00a183c40030019901e5040203100301e402c0c1a41003010b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 180550683 1250 180549433 180549437
    0x10030507360b0c010c031e020708120103081207111506030c091f05150d0921020106030303050603012a12050106030c17060f06070203120304080304020a06030c0818100606 75
    0x440307291102c05404c403414440b41e002414a004a0125000b002d46000605004847d00050301d40e40b690501480718400c0f05198105504404e00100030450040f000d40148486e92080e10076541c1c94030382c103584c0d0300000b605000969200c25501c0d00a00c40300b800090740500c0203400da652810b841c130b000c510101014ac0c0e40b184141d8455401190b0904020003450080404070ba9610105030541e8041c00103100c0e0903010002c0c0317920740d401c5009000c0611128919900216400040703c81c154000900030080d6000c210700103030600d8041944c40c80c1c140a10300700d1900c001e4032086404441d0512450200c2c224030704c40b05024035441f60045a9905105160003014035450100381c1005441c0020801d1010b1011510400e90a00512816442d410032012102c0b0007600e030f40d0b07a14406070001a141c10003520240c445030700d000080004001c11103001c0e50003188280c030b40841301501d4490583c140c8605000307a000003118074002900b04a15030011384008101e01d401d503055601c1d0404114103640c029084000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 180551933 1250 180550683 180550687
    0x7050c12030c1506100f020a020a230405010806010b0702010c0605070f080906100e0903090d080406030e12070b040c0504090327180b010302040b040e01030210030507360b 75
    0x501d0490502074026441d40020a1054516004c80010f100b1a2400150010072510700d86011425008204116210340c00905225280d0340d1200c07100104001503800007246031010502000301c0c2031a00840f03040c1c441d000040d001c0b603030070009481d48540010000341c1c1009109800c00011034041c1c81403d0003020540d82d01d00100040a1001c0c1c01034002030009060303503000e0f20400241101403010107003034882c1641e038040310b615000525451401511802d46d1301c029041011b1080050090041045a100751018014001c090400075124080341080710903080d0204030080014a0402855074003500c502200310a840d240e2011a040740c46000040300800c2045002d4054004850300c03900300c040988030204102c909060f41555011041c090030003515485420080c40750b806601603601505060b0500c544660340c030341550410785028031060b4080d1781041400c1706024881e005640c4504080c0e103440d0b182460594071856110210001ca520340301070f0b045030ba00c2e01c0b2041c0491000802c6090565a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 180553183 1250 180551933 180551947
    0x10302090112080a030e070f080f0f0d0507060c0507080406031e020408070501180803031f0b1206060304020a03050609010e160e040b0a110f07030210060e0c07050c1203 74
    0x14494030180c010080315001c1803a4000000e44800071640e02d00001c3c07a011840400c41c04005180080700e40010030705030031404011507000800241c0c0c43c1541041800c54811200c40313078690761200000c00303510f000a4000c001c0100411007940041c40050001e00e0068946111b075113400d0360381c2c2c0003a088030300040d441d101c06d00308100c1d200440d03054000100104616152420319850750303c81007071052074180041c125804004404c07403100c45c1c005201c1502600c2c1d42e032410a00c2d1108080200c150418464225075010030b88824003419113883c401500e003411103a844400822066810045c0100c3e07010403625804000141c0034000d1502507150354002045007440d08032018209800b140d0101044c13183317180100b0030f103050b14118039000342c0c100c003c03240386880f80e0583c900501424098110255400103500062070500030007046907600035804d031003032800001c01810580d0b20310b2042052007100c1070b000c20b00312003041c0d0041c500503101d8011a0960040d5201040c401d0010340210601504041122 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 180554433 1250 180553183 180553189
    0xc03130e040b0618010603090206120f070219080a0c061b0201051806040c030206030705070f05060601090b03060d03120204080a0b0609010605250218040609031803030903060513020d0b010302 84
    0xc0e0801c204441804e5810291031360500081814424201010307158162081552100001ca800145083c40c1410591401c481880304650042e03601c00018410f4410b41c040d0307440600c02c400c44c542d501054203460b04c003051078120361420b004201561381903503980181c85402210400418080700a4001050030314001e4141d40382c10094204030f903c2600040c04000019981034100740035070398107d41e400c2e01c0343c440d00800c50309030141c00002013055445030780c0301c41403082c00a4042c1c403d8109994012160b6101c64144403640415154950400d07805c2001c05c000031302550860b5090000c20340010b00302640c3c2c0051301e10340140f45406503070000e211018440d050603c2e8412a01410711420000d01d40300a201081c0c46c5601c096141900c02822519100d00315941c10030b15003462042c508000881e0304182c01c10000a01c103400f03045010600341d0850581480b8205c10b1442260380644a00ca4841d14540f83e0030050000201074800e5034410902140050799a203140700e400360f0280b20351031101c6d810351044c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 180555683 1250 180554433 180554453
    0x909050907090b15030115090e130b06010f0c0b04020303130f03020a0905060604060c0609080a08070e0406050303040614190908060702011401150c02030d0e0102120a140c03130e04 79
    0x40503003c0c0c40f84c0444c0074030303101c4480c080780c0c111144641110441a060f0500b200c1c168507a0300300807480200306092006c02d411030f02034000018000c520100f400d4403442c00644c2d41214125811022070200340d074000201d0003480c5269030140c0090309882c50304182003880c14102c2c405401c94441c102c045141482941422084074001d0b01d0080d40404c031034101540007a405000d1485910300b041074585800d001c03c0000c0e04480030342036014130310f5030f15082c81d00000744c400c52007140d2000001e102c11088641920f401d0180804550026001c1c520b041c1c240002101c02d50b80000401002e10000c020403102412103509000c028141c50703403040700c0c240c1419901c03401d00801810040441e810204070340d010301618100d841c11129120520009000c01c00001d03540d040304044080e51501400364085105600300061400010090342a40d0401c1900d402954460040404070b4000548640c040701b01c25002c60000d2481d80720361000c90b424600342e8000403000d0398058000182010300c0031b00780030811000c0700d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 180556933 1250 180555683 180555701
    0xf0305060a050c12040510020301030b01181109190819020a06020105010503190302010905010c03240308090118030f050102040e180c01082d150607050307020f01090905090709 77
    0x10003803101e803c1c00c04802d003260190801e0a80855054004141004401c10a2624014550809540701d43c0c0d04d00304581c0ea00c10900c01c405e1041001d4041e0018245107119083c042ca5400c2150790801041009000300481035503030b130f5a07850790100c13404202420b081041200401d01d09490488241441c414041c07004516404034013035a040100500181d503001ca09203078402d04071281c0c2002b013260b0b410202e0141c4021071000c3c04552030009580842641a08051200700303d20464036900508010103080210f1184400f421040d400d0008524940c0b18590580304040c203203000c450304d00c0e22034a400d6216600302004441d81c3c1e60000d8100615000f600303550341d019940c00030060103a0448a161a261200e040700c2c18100320050000901d1000c0001110a49401c0d84499520100324a0035451b901c000c261a00713840000c0036080310209107400300860b0f0030b0551040145003441101d5083c41845000c00301464180036589802003200c2e203282c86401c1c46104075100820310585030114080884800300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 180558183 1250 180556933 180556951
    0x3012303060f0118240611030a0203030406110c1504031d0f090a0f02040b130b0918071e0203030a05060303030105010c0b0604090f030206041502070c06031e060f030506 74
    0x8401c11407481002c6406074111680d0502d000781c400402200305000b072054807050781c6030304900394054186107001c02c00130040c0d0b4241e031181840e100403512075a40e60300a0300d0115005900c10000940021000c4d003100c8004140248014140f200300b003215400c28141c40008109070001c0010030080c95482074a42d070710b0703009203051080d1800191000c03403480718024241c20301440f554008101d1040b40d541c4415207180e84207604540341e0f070700c0d20181041680015280d84180c88400c001290041fa104100c0300600c2c002804000b01034850700755801d0a031340080842c010701502c088a1840a031000050b82422a8254007555481c50541440e13012110050201c5005c0d5101b0f000500c41c40e604024580102900308081102650315440000c0150505840040c520b80d0344107803c0e802c15400051142c001c81c0b160703502c030841e00c4d86850410304034080d00c031000c0d02c004c60141081000600a511410b540540101c910f51490b038001c3d0400241c910342c1c0e0000b03905852849040007031120611107150865078a0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 180559433 1250 180558183 180558193
    0x5100c030e0f0f190302030105090d020111090913050705060f030609100b0a05070c0b0f1b03091c0f02041d0c010e030705040c0903050105040605340807090b03012303 73
    0x1041c08510303030f04881c0b1199406104840e03000d00c01503104644200c011980100217224503c1c0840c06507482d410b940300301c0c80241d82070031042c44562074240d054800020001e0b1503400301d03503a1600881e00d08001c4020a903010301410a000c038540d110b040040244515049545035241843c20034090a0761005020700d403100300d4040240111900234003121940645807902075114451810205c40100c001d0744681070225002484803860b0b914040a000800e9100c0c00925140e00200c403116124465652903a074000c2d01c046580541d8400c600d522442180520f201c021408900d5000c101100d031403d80500e2070882807810070030741c214100a4200b41c070740c0a02c0c002b5a4013589101280e45d610326405881e100308c2d10707807052800451045010000031500180284810b0501e401c00c1c50007070906442030250702c05000c4d4048401d4864182440c0c01c41c0390558400c0741018401d508507040340c0d0207015001085151100050326a4800c07020318003a020225581101c45046031841043e0701703030700036054066001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 180560683 1250 180559433 180559459
    0x1030207050705041d06010305010b03010509060114010c2f101403060f0114031f0e071d0307090c020105061003200309010f06080d12052e05100c030e 66
    0x8900e4a080320021340d00418032200c0e0710006501c9416021040080380304120001043c014150428124141d00750001c1003141c90f000d90154031041c09005120841d40c8143e2001d9007544180d51200a0600a0500002c07040d03090301c1851030005505030603200c5109403180d0102c05d01e410703810100b00b41c19600b03040d102440415500b121a020041c440d621400c5c58405100990740505111210070030522030440d0360b80b601c00f220704c100d02a00500e04600001c44400031a04a00345410240604404c2d240c0c4516050241308c0008803003900c000b8142c06001c0d0b04d100242c00c0d00c0307a01070311054501d1034001286c00d181000a2040c60b0024080a0040504240400d22402100d071121000f1001181c4001d07500c0c3e0310a00c400d40985101059a41e050b840d1075400104400702094030b00340c1d015035503100c040030b0001c603084a0a48000341d40780150350400d85902414210722030a409840461700072541c0c2280e541d07200042803600700071350310800f0130800200c81c0700701580260200d20340c4004950203010899 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 180561933 1250 180560683 180560693
    0x10806011e150e2d0d080705070b0403050d05120c0c010e03041203081302010f0503150d06020a030b041a0123030106170c1206040504140d0905040e01020315010e0d06150f0501030207 80
    0x1300c1401c90703006424840140c828404420304803421103070450100d45203142d0b901100c8210381d110344400d68190080000c8444a540310f80d044031708007030030f000100b4001d488100300c40782160301c500e5031502d02d50740e80d0754100000076090002d00300409403c21182d020105904000c1e1112038018039108681d8045009400140c1c5c0048406590314a107240640d2070b543c980ca8008901c440880320a58424103070441c01c0300f00f00c459002031148d2a4595428018050000244000c0d0f440c00742d1410080490024100c90035481203400340088541d0381c00d05d00800345003900496060b0300a03080031001800008006418401e61312405070401c4009034024504030b600d00d83e101c1c1d4088003401d020311942d1200301140a001c11101e405480201001c00d46800c1c80d00080e01802c0b8900d10b200f064015800d2108200d1a200107200f038070303c590720044000a0a00a0350011a080b581408016600445000311040400e40a1146891004503804d0070b18000d410320340540301c00d40f400d512150415004020480020f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 180563183 1250 180561933 180562009
    0xa032007080307090803030405010f0c031401031205220918050303190f0c21060e06040e190b06011b030f0c0201110d08010906090203010806011e150e 66
    0x1500000c020b41c42c0e8440075411280118194049105440044144000d1210640c005141005812010008000d60b4102134042c0c034803c142408000c40c5010041001c0740b5043c005002c0c010852503c5481e00203502016800380105039424820410011000c0c056030303044d8411400c1510314a00710110005070384d0345072a600d00c03009105c480c410480340c0203070450100e03540040d00c500d540043d05200780b044601008244800d11000d5218076400003c0491220146200780810303103c8200050026903501424040a0032606c05421032512400f2100e00484292001100300a40f04000e1000c1d0742c1061300005065102001c2088000524082da5a00007500100592419a5130f4201420720a040e400103842c600d10348a80a02039000b840d111a5006074070030ba82905880f2214020031000780c480c0315120890100340a000c0c510ba114030010b11540510442d600c01d112072150104100e035855001e00380c11b1112000441e0003141002d0541966490134184452032403508000420a00c500c0e184045840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 180564433 1250 180563183 180563197
    0x306061c030528030207050601210201030e0a0f05100e0303160c050a0c2d08030403170409060e0402130b10050a1101320f010504020c210a0320 63
    0x100100040050f803118005105070300d850855282c000d01030383d010001401030340c03280b0f008075014000c8100104000d1803164108000005c10741140500031410350040d0003c000c0031445c03845500c5916040f10012301c048503224842c0788150060a20004801400300035103040311001e152941080c010090320040003a1400e030f410300c0070f1a00c41130500550511704e06103240b100340904050f10301e01000c11050100300508820031030f43c090300206602300d0120540d02101c01d000300c15141c0c20400080020948100240c101c0103401030f20035261660f82c1000750300b200d2a40d4414181002c00e4400c20080d440c3c4000b401140481807441407000b0402c21000450414100d08810107106000c148594070611070309c10340c120800060b00811000c5112a101c5034ac001d00700300d90851010455101d90461000c184042e40228141140b40c1805e90801d4108000381d0459000303803c0324807407244a014810038a20307008c43e010085001e10755507002c008400900b41d4500900609510481511188566104904460700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 180565683 1250 180564433 180564437
    0x40b0a08010f0e0604110c060f060f06090a062007090f110310180b0604090603020a05180a0506060c0a030306051c0201050d050414061006090f081c020c060403030503060306061c03 79
    0x51042407034480107e0040c85155405c1c0d224060800a08622035514140100030858462041810100801c0301c944260205c00741c100aa4210411546006808102c00383c2818449c0e103803003800b0602c9003490144261b10920046489102001182c0380ca4440c035141c0f40c5107148c000c0d01c1d5141001c0042e03001445486500c12a21034480c1e1285882d80e5a4003035900507800400c00ca90b550f41d03800100c0094030442c00264451280c08400040c1403800c0d650b585c2c044440c040d40100b0540d40d00c2003401c0141001800b4580000042041144842e0300340021114544241c8001540d10b00f01024001000002420059012091200200981e8200042d1603201c0490040800ca9558a18002444108104201c5180e00c102010b0018884020320803406980c107550703840105580e980941100325405201e014540d81009200c01c4c0d074200b410098004a054500465454010100120310a035105034004c3d00064008010f10030240340a01169811100c00c80d10492075058208850a01c0306500c03c00900f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 180566933 1250 180565683 180565691
    0x70e031506010516110405090a02011d031603030512070219060902060c010c2102030103021503100f08072103210b1c03031b0807050a05090402040b0a08010f0e0604 72
    0x849038800c40c1203402d08080c070700300030300211510300c4e00700e0040c1045c20b80144074506240015181c010001400009290161355030200500c42d20701d41d507580c441c058009a0980241001c4000700a010f00302207009510a5131100d58807504104804080320001e061101190800c4254071500e09a403130b800b041ca55001200042c8508152001039017038410b03090721104a50811103500b044582000e41440ea0842c1000544042070349141030030202d20090000a50004104550100300c02001e400f440e8890441010310781e103243c03180049440c4007201e500500352075000c000103120b98005c0034640d07000e0040c0606c015448c40c030660f80c080c20403130307080071034020044111201c89544000f0b82c200c212a5000030f0310b40b40b61814851035079011250782c5030080d001f007818000d50740700c01c2d1380404035291201e07029a40c402e029100c000045845038030540e6a1010003406105682055403188020002004010486d80e555a002900981940d105a003d0781c540305021504224080303000760003030f174407101c101e80000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 180568183 1250 180566933 180566941
    0x301090b1f0e0f0a06050909100b040314011503050c0f0102030309030405270109050103020114070c0522140405210306040c110a030c140712060b0f0303070501090b070e0315 76
    0x1a0f62082c0525140d0303482080c400380040c026800c10010315089206071442e0700f065a072511440f100d2202d6120b02d2240c0c5a00300030800c04a50107c4c4400000f0401b2000800d5074110041200c6030100b494005503080d410000d168519450521001c00c43c2007000e0024504510780629000d49031f000d42d10405000b42419113942c29626041503424420080c042d0465100d943c45164440c0100001d0100302c1c08100c811002e01c0a0350969000c1e54041680f05400541071410582800151200c8444008a0a80322020300490149c14041c1d14207041011000d036a0750310b403e0509034900424500384541007820711911070208201c40044a500c8003081e40c01081040c1c41c210111010008081007800d0390043d50804403c01d94000316100b8110f006213620054217a0b003c6201d80c880880b48194a180f076002c110342d2000441e140c00c13000180c44005c1c90509520703032100c040380c2194490728003200d09075507030110101003162a19a1541251003440e1500511020030042540c0b8a140071074412480040340c001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 180569433 1250 180568183 180568189
    0x80d050d0c0207081e0705060712030c0318050f1203010e010b1e04080c0111060c04091802100215090604030503010308071410020903070b18090a0e0607050301090b1f0e 74
    0x404010301c0c00404880801e405d5021400c0c0042083c240100036000765140007400d40341130300503034400c1600300d00041d001c440942000e90003800c800f0180c2e003d0548a410040601345a10844000305010310003800b180b86900c040103041214481740c9201c020402d00c0180302c006140e50440f41507506400c0304542c2ca0a0200590380d070400b5030200401c840d034000030045903441020415200c007030001e8980b0340142c0754403081103440e000d040f64210180941804100282031154000c10b10700aa031070800c00240003a0780200d03180f6611562030602503800325040c4001600c80800031540121382d00054241c504003070ba00200320780b0042c8800740100fa0080380181c01d014030340d0414001010408121040d000451541801035004045418468050540001990140380301160f00c1950700144009c014003442d0704001c60000702402c0c2c040032541d118a011003e82c030400000c2d001c2c214903142c0a0720b96140c003000f0400d49240c1c071003850181c02c2e011040660504505000ea103d40c2803424a5000c0c40760308408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 180570683 1250 180569433 180569443
    0xf01030b04170a1d0405040b0c13050a0e0717010503031b151501120506060304121b060b040b040c0215070c0203120406021606020d18030b040b0a06080d050d0c02 71
    0x111104201001030000c59458000700d031101d450b0220740c1e043e410300110030108002c89400707c402410030307101c44002076003640c0b14000600f1980102c0c1810072903d52200040b40e090341d1150404440e001030748051000c1d49402c804041e59680829089584941c18600420740320301449040d0ba114152038206148803400500030907007034402508001c00d081c9032030240f101e0005202d840d0180851a0200c2c8840c40031000d005d528411400503010701d1450300da0f90b440450007076100700c1c1407041060320690601031800a5034903d1889000e5800801e081074400100001c40c0d40d01050310f0b01c514503110049110540102e034041e0302c04c040307000f030071029600d5a1080e2001500281d0081d49070140740101010b451448010700b003920b615908441c42d0f241a5070400306000c2113401884e000d07910001852000c86d100d0307103100940c92085404066940e83e03a564040c41c050003503038100c0c0e1034580441040119081485903034010419580201119801d1035030190a5220310900301d04582e45403107850500f1802001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 180571933 1250 180570683 180570713
    0x4240905030f0a02040b030f0a020907020109050303010807230120100e16060801081e10060303020f0c01080c0d0b030703020d030908010501060e130c0c1b031a0f01030b04 75
    0x94418044490b41025202c000c154401c0744118901084400300d4280062204955003504006010103941d613002c02040d004000c242c44219901c600c007401c00610300748090760080120f50018070001c0c3c01c11203001840d01d08106c0488410700451b00c01090b983c1d000d1031810464010341d01000e0040c40760310910341010300540c1c02005035070070014052010ba00000303010140798054002d401c0c0541c5c507800200c41c501421700c5812019800070f640c3d4903040e0490304810941c044000c0840d501198846e800401350780c11a071040c0d0141c5c004c441c0c242d0b1404dc00344100c803140b02c801d19203a2000c1c40d002440c0ca016001d1801440351003035a400080d640780c0c90400c400702c05190000c245040584151070f008210851500411165500b010000155580101d00680001030b004041340400b0054000f500000d11100b600e1408104c8004035003008149440310102120078403d102600581c10341c1012200c1107200680351070309020440c2002142d0001845803815640e20080c081607644131400c10768141781d1285 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 180573183 1250 180571933 180571939
    0x150414010b040608100602070b0f1905070303140c0301060c06020c010207061b09180504050a140f0c0105040f060302091503010f090b0f0906101211030601020705030304240905 77
    0x200010681030606030240c0700300c3c0c945a0381e07580310b50f0751280c940200044610030240964400c0600303104141001000d040c600c202401f0103402c0240040321080350f54070400c8010040f6800103000018186d160050380e19008602d40c1b0215141000d0030720b440d5600c014420f00041007240e8001d071040000c0c81d0100c56004260310700039034454a82d402c00d2402003105d02c9010754004140e401e00c071603440c05600003900300c45103a0b03408810301000c0103810707001d09801001200d55001e00b520700d100082c0c14000745220085d075900103100d6001280c551601c2e0034083c0e03a4450500c107091104010303600c4203030828402e88200c1d00d0050303299041074000c1801000f543d015028030420200010441182002c00f05044955100b4180700e80f548000603c00b06800d010041030300001100001001410300d42c81d031800040c07480c0340106044940c000f0600450300700e0354640020000001c207010066904025100c05414101c02441c9001c0c0b8041d002d0381301c40341e0a6848204140140e09405895000e241841c00411011b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 180574433 1250 180573183 180573221
    0xc030e0c0f060c1b0a050904170f0906030a0509011d0a020d030207080f0123070e1915080a271707142d0d08042d0c05030a0305031504 59
    0x12910b407900c2c50701440c4c801c9018a41460303000030280340000140b401a030300510084901706c03003101c00760003e81c0a01800d030b12048003084a15031907120107004500c11000d00300c0019145c18812526070030340f00094203c0b01002c1d0100900300402d14040346680340c2aa0480700303000e058009d458244c3c01c104c035541c0301c80054010b030844400300040c103400c42d50115010030010203a02c440c804400d44050340a8840c030000076000b0008591900b410f050000300090702d0b28803010003650b03a45440480c4200d920014001400e001c040c0304042d200c4c1e02400341e0103901031840614643c0c00702002484441089400781c4002c513101103080203500304204841c3c1305a00070405070507001d0094945a520011164102c0c20188102c26001116200b041e08030b0441980030007500302d02d1064142110450700c0500191000b13409440401c149420401c013000a03403040ca03201c0c421588590414810740c0145a100f0340c000c1c1c02148240b030029034490202e030b900a01600e051541000c1c45400704000b03110000d08a200b40c582 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 180575539 1106 180574433 180574453
    0xf1803030507260c010b100206060d030c0807060c1716110c1804030909050c03010303081806070e03010c14090d0213140a0c030e0c0f060c 61
    0x3580e6600107103d00004041410001c4210703c00c241c200000e518441603028065100034440440343e1010001d60701c2d401035210b10b001001c451060448103245420103003d140070b86e00164100960a488101501c0c004008040c980820000324103200301741c4049201441d4018810b5414482070740d040040c84400766071424420040943d00e000303444c0092859210780c402d03d4490b00b1085d40d914020b061a0074081c4c40d904440d002401d0352810076082140145a04049a045035407500d0169070a5403982c0c0499050024400320b040360340212001d120075198005200c0b04d200804800130050360306602e0068840d079140f80984401c600e018425280b0b0791034001d20300c60000d40081c01108961078070b5034645088610440188006424090078042c44100034840c6682c0d1a01c182410817810701482105a614008410214496110fa40094181d501c1d00b07400d940c29100349800710780300010 = true := by decide +kernel

theorem cover : BRFrame.Cov 180395683 180575539 := by
  have h0 := BRFrame.cov_init 180395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 180395683 ≤ n) (h2 : n < 180575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
