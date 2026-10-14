-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1818
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:47:20.988265+00:00
-- url     : https://prove2.me/submissions/17a9a215-6cf5-4589-83e9-f53fab225e13

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 326798561 ≤ n < 326978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 326799811 1250 326798561 326798603
    0x303030c09050d0c0905010b0a1b1103031902060c0a1e09030f0c0608070302090609090621061f0303080a0b0105090a06020a0308151818030a0801080f0a 67
    0x1400358010811a510030003060a071194030300718482c0d43c410154002c6581c0380040c0c290441e50180c0108851030000c11002c25082d83c4241040d2030f01411440000c0044014a002d070344109d00c8110403509800013040c1e8200580d0005009400501c0a4080d1001680c4d554100c0c0c074144100c0c441000851441340344a54045d00035544214000001d040040540e9180c0d21800034460b03958408503229410b004081c403500f070b03204031400d400c40110304080d410203a042c00001d540740143d9220300e0280010300005059a0754100c80355116400784400d518400d9134204038162100070403070750312038583c0c0d00300d286000c3c03a04094039150443c2d070035030341d4200241c884004c0d00010f019040211410050180040c0e012039480c00500c1008262640080800010f1881d01401c500030051030255041d03040c0c5040f07002e545605440344d28030a0b44040345903480c0d0311013501c100d2045562030081e40030301c80402d1040f9001e0308209010b040e0b4240340100c5070004031a000380d6036940300102c1e004001c5081c1d1b884034400003403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 326801061 1250 326799811 326799821
    0x10f0e030f07051207050318010203130b0d0f020d0c020f060618191103070e010305010b0d110c07030f0b09070303050f0702060c0d0f110109020f0d050a0f0b010603060b13030303 78
    0x21241d01130f20300c0c049524646400c0703900261400e8807160030000719151400a002d0100030490000c1c0041c608040c05010200c00e84002c0d84980a507507500011014118021948a6402d0f60131190003191558000306000700140900f242c0a00980f00c2e0a62004c0780450005d0303114030031003004003540083e203014904000c649030082c0000546a4441c4000d11070803030580603080280501181c21622494403e0780108101380d801d4601c0d040c10b141800512500c02e01c80304582d1104000c0e03c0104c0c4a503806010012684500c1881450328040d0800100401c40072450745030640d4005c280c818841e464102030345845011030320005010540c00c000302c40450080f03a0180c006540000c10b00e60800c28001e944504041c28480a01c00003400d9032800c18076140c003d80300d1000241800000c000708021580455010403804980612890440c0074803000c11508001409031141d00c054181c00722a00c0703180c648036626081c040c10010908241000c600740f41c101082d5401c21384a0350400e10810700e10f803002e0340104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 326802311 1250 326801061 326801063
    0xd030c0201110f1f05040c0b0f04030c12061d060402150714010605030d03090305030f3112030e1b120102040608040501110307120509072303010f0e030f07 68
    0x1040e440e002c111030b00500444850f051110084c000201007241010840068082442c60852a100505c000b14011702e03540025601b20307288807a50354901d006a102d1a008a620040602c00d0560021984e140c040070040400c51046000b071001c044241415003042d00c15000104142d071100f00000d0140c601511881d032031240c5140120f14002e800d0301c42c980c0c8403070156516000c2d03a4581604009a09080280d0308496a50f484d04015045056400420501c0b02400c14541c2109600c0030412004131030100002040031261004621013240000c00e80c0444208015100c00e2104200850130700c0c0030f40135154a141081d80035000308086565040000320891844c20782101c4145128903030043c0900c01030000c4d0400e516141400d00c0c1c50703e081c42c01e540340e0030a604a000411b2007408551504081403079440e4600103404541d5585009200c2d2a02e070a40e0b03c080318072084044982414440c2c0791440388522400d40081c0304442c140495282524131385080c1580b950700402119030400012405400c01c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 326803561 1250 326802311 326802317
    0x3051b10110c0c03300d052d09030403080915041e0e0105060a03020d0e0609010b030601080d02030a14120f04021905060406050a030213030c0806010f06020d050702040e062d060d030c0201 82
    0x71210210034411110100c80045900b25231406401d05000103600300300b12119003100004461030b2030075076540c8a02451200402460002c51342d031001d6a5005800c8041e03c10706c40d0030035100c030b50703946072158810b00781629405494040341c00852044445415103042c1d410107070040c0c0c54581a04412002503200b2540400c01c16070303030440c8031700f0b00034288507548c09004030b94000325503040c8102c1010308080301030344956807540c00440310028264002c02502c2039803055042c1585140210303d03100c40140b007940c40f4180103002e020100700380e1039030500c0c12a003c1c500075120324088050554007001c0196240c02481d610500510007044100c0c8101c0c02028016164600981029840d0a1200e804401500300b244c0000404005000030281001102c0c01426101d51404889240802c081d4548000425050401034001a110f0039521541c124124a403c00c20443d915031034080502000b001c00400b00191402c02c0d140707100b41180400d034005000350030080c00128800d429690503600c10f0b00d070810407418 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 326804811 1250 326803561 326803567
    0x303070f080d062616060809120f190309020a09050c1b07050f0306011a03040c03080c06010f09061805041410052203051b10110c0c0330 60
    0x40c44041c3c022000200180300031454102d5040101c01918482295098003640c4100440c1c0c140300001c10b010412207086003400001e0303440e01ca04803402c000d00b0b8161903d10120006170342204180f1100100100707070400000e040110200d0104030140c805150b0040c0d44a207124205200074040c0327900142e0854041840c2138900402c098403440c041144040b4401c140c2c111500c10003660500707500c5240400421005401c441d03040c0701c0350324007440f81c50720710805a10010001404104205107100047c5401c81c0c12192100c0740c0b444460790f0345100f40200e0400c0040c03c07200003100c02e603d0007410f00b5110701900d1242454203040800b00140230003070003038403500401ea4540100c19801c2c03203100444440035002186604d044103d40c09030303c8060034000c96010409850b4004203078400103403000600c00081d81c10603e8000300075503180140500448040341e00c1d0217010a0201d41c0580100321003200042540c07019080a4101030b1180c00d8004034100d940c0381014010915001d0300c80001c44280c040496600b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 326806061 1250 326804811 326804827
    0x6060501050306182809060501051816020a0c090506013e030405090405100b0a0303081f15090905010801021e0c150703060e150303091003090212010501031a04020303070f08 76
    0xc0da08800f03816401610355441030303103041c1f110b03c2c000c80e03024050a40d84240310003001c042c0c0000e0f100005004920400c42c400b02c40c0304240c428049840c48540000b003044e91360303468103100001403000750341c01c50116100701c0100c04500f06085035001203400b80c96088003401040b90700c980c3e4100b00c0c0303007800240f40800c100106066451041d0f60b03006d9802a03008180c2d500e40240040d0856150075042d91041900003010030000390301440466109000e40e000841440d001d15402d10700200301c0c2c0041547c0070408101c5ca00302c941c0a0341c4102100c5200750b0078031152740e945508508070300c80e5881d50070004000c4c01e40b003038035903025070010460105c80a04036021400300c0e812110b400e0b40d0641b54040041d40b41c100821441c0e503c18102030308041601c3c0800d640024a800280d507c2c03158040045c024100e1080700c2000b64001e42c405055207401130302500d403038444100311034003c10f82400308585405142c904411080d01c44201c00303110f980c1c00341c015807410001d80c5441c804c0040c0c03600304803107841082010b54 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 326807311 1250 326806061 326806111
    0xc0b150112110c061e01091107140c1509091f0e07020a02010e030316030e0406050d051e0604050705152b050105030a0f0f05010b030a0b01030606050105030618 70
    0x914094000c65140d00c0d000328403c044c0c20144042c00303101c0301d0645002c0c4120308030703c6540154111040f1a1001034880700418000a49001c1c942c0c000e0644460b56811007011480499904440181111b40c4100c45803962040c0c00c42e8021400007a40240380c000c0007448074840100c40310039503880713041803600f241c0d80e42010b40325006080f100200140c010340c0e401c01c00c650300b002c01e002d00795600320095400c2504100c5140c00d042c0d051040541006154038600324282c980751b00c00d001800014052034818441828001d660b100c5d540b900551750f482d030103600d001e164000b00c0c440f402180c0c481c014141442c50401006650102c2c0c2008480e030140801c000320382e5845103d10100d01ca02c04105c4102e420070307240004002c50320141d01c510300a400683c4d044c000a100c02d80d10b1016643c0c02048040600c00c903003009130040451116154241c0b00c0c1080b40b0b000c0c030881c40340f600d040301d00c11902480390984410045035540401e960580c3c00c40007910f01e04c1e03a248107003441c040d4407800105034411308400400d445 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 326808561 1250 326807311 326807321
    0x90b0d0e0a05030309070513050403021510080a0c210206041202011803050f0f1b0d0c080111040807060201020a121a0303040b070b130203031e120f01150c0b150112 72
    0x5c1c0d03200d58050001000503090680122a5000502c4000c005030b00d00f0b0b4501030b449060003003160b00319030016000200f08403060a01400030303100c03000480d81468050716020080c4c0c10036014006040c908403014503000c40f403011500240d03990203455136081030718103035107080080e079212030807418440b8803180540c3c200449624000190301030802030018181c80c040280c01c19003070380d0182e405500301d8810030340c19010360b1351200035654040d07174280c1404486061400803071103e0b130030942130341d420104040d90340140b01c00904160365030341301600c44040c0d481600303038207c0c840c800012010414460024082d14400d42c40b490705c002c407071002c050328850705c0c07000281541d216400103881c0b0308000c0340003424400e20b4107030690b10400c0720042003129005074000980d24000e20f036408107180c40b141c04a0000c00740140c10f0380d92039103030301c080740050303007410010805903400074020202800c560300c00c0b15044900c03441103581c01c1c41c0c00092001040d00d65080416500066a004a052251300507100c00340480510030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 326809811 1250 326808561 326808571
    0x3050f0a1706090103030e0f1909090c0b03160509031c050d06060804080f0c1c031a04140606030a060b070803010609050a08150a0e030c060601020d090b0d0e0a050303 73
    0x20300381110341440c0c86452001c006400d0034041c010080040c00002e411408910b4a078604459180d8500e0b00d450000303003514000e01c05122290084200000c50036a550030035128a4403c140c034a0056440314141491800116049002d41d0b085071a20603c140c084c00003050820030203003c0d1842c0b1701c21104625112102591518000f45002801180019661045101038049840c0c004d025007050780307459019004980900307520f600005132851203140100310390100038805d028060a20302000401030001c0c2030300050700200048a104010301840c10344542400c50003034040002494944205101030758000400360716140b40c2d1703540049143c10490028000040c8100d0b109941c0790704103032000301002880c0e070180e80140c07040c14082c0540f0703401207100c21400301d85044059140d5030b0358030020013402c8003c0300c01d0b051740400a40c15040140c04258588122000c0c0c007110310400c150241100c60890301e01c590242766205000200c0010143e8001c0f1843c0c80700700e02114003034442d685509055500c00c1c0c074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 326811061 1250 326809811 326809817
    0x8090d0606051e1302070323040812070b07030c050a0f12090c0302190e040602090f0901080a050708060c0a11121c06091a01030c0207031502090103050105030a0c06050703050f0a 78
    0x162005140340c414214130980c1c0c1c42041c250b040a10b6a507002d0101c00420b40f5641c280c202c80c080b10300e0694a8107064800508440003203482c0e4807400040b4024980c050b030b00945110300c0080000d2492030090060705401c4d030a40d6100c0c2d14005051404842d40c501d500c0e240d00c00c020360000d0502c0643c80c18055450013038005e03203603400c041d480c0d4410002c4440d03c0100d026a00c65440c041000411a44105180d025400120159943d41c0030780009640c071661070a0154800c5841d00003103030881000401c40b51803881401140c850070780301d03075610b60b03501c40032900c0040f0b83d44104018907500e8401c800140e404c1c040101150144d001d5445044084c2d00115800a401e5080b498004501c40303c40c001e04005005000080000d000c202402040c00b960950302c0c20306250b02d07859143c0041d442007141c40004c5420070a030035510764488003010081e6214000e01d0b4006410000007160528010500f20700266000040082251620105860b01d4110000c1038050000c00e1060480c00b2141800800d003140e6240d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 326812311 1250 326811061 326811109
    0x11030115090f03020102030f160c0b0c060601030912030903090504050403111005010e01030f0510142406030103060b1201090302340e0a0b030102040e09060106050708090d060605 78
    0x1801080d405056101c58600b0074003000400150341c002c400ca450120000f45050f5598079013070103460034174414200040c5504515840019201d2a04014088441d006400d030754580c1c60fa43c2c0110291540f400c806060500420305141c8581e009030311901e400340c401e06010005540da0b10001c0c0844508490a170045a10041d00f038115903000c0c815822080058042089a541080e03010b100031501400000c000d91802000307e070a001d4104116980c0c4d02e100c0d00117202d05e0481180d503540607641542c905070b81c0341c0e01d01c9002c1c907954a6039005c055103c0025102c0380c01c503880d58488101400c10711341c80c0c07a0003140300b10000c01d000ca020701815040c0c80c000e400914039903001e0481200c040060007080703088d4180c1d5a0004100324003000d4101e040b0340c07650380c039003c0c90f4035400c1d1100018640603110f80c1d80b561001600003004280103442521422142081d186960b80c2c0d581c0030356807440307a11002081110204400c0c002c52600e0700d5880c01c41030049000150301e548410214401c462807071401300109c0f50f10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 326813561 1250 326812311 326812349
    0x14060406060912170d020703030e0c010c0201120b0121140c03370603050f01050714070b070905040e0f0d021b0105090f060f07150c0903021201110301 66
    0x34064000280018a031200c80780340340800c2003000c807a8814004040003042c40c0382d101800070030000d542e058200700c5011076030f4a000386400b900400107014060310600076aa10600107600840901903200e4060b181c0e010040e0103076038050002c0641d003030003e041c041c4892041794254010494030710000b030b107000d0010b50803616440541202c00e00400544440d2410010401c8540ca402440c9060012421000d80301c2d000d030012076980381d480750440c901128038211001090000c0011905041400d413002045940c4a007482201c907240f0903043c104c00d83d003003040000300040e40a80d43c25030001c014548501000d44500c009400d036905004410b509138000500f001400c1801c0c030010320100000e000801d601336110000800c80d540a04203a4180304001c14888031580388c0700a4200090380c002e02c40e036591030300c084105046401541d030070743d108004841c01001940c0c003032203410b41c40041034481584041c03844e07003049031818403888485100d540701c00c80072102c2e4501038003a40c060a000030710444c0303880310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 326814811 1250 326813561 326813569
    0x10e070b03071101061a030405120c0a021e0d081b330f2a0a0207030327050423010303021c1e050f040b030f270c060903010f1406 57
    0x3c1c030200c036200c1d070340b412400304480c1e4051407000f00450b01d000300498407580d4500301142448100c94450124031000202c81d11442004214801180c1c822a0501116071006401c411500010081c003608400016411008180c05034080c0a404100090000c20344203200002401e001c01d0b218240e6a05810501c001e1300700d14030712120b80a40500140185a0f85040c150320421010040c0c050b10071101c03464420300411041c00c4078030392503480c051080382c3d880602c020000e6132927070701e4442036002038040003591100c0c1388032000704030650340090328200a031030411040000914040300032440c10680701908448030792004943d18004d5000c0e0300600b0410003c0058162030105007110740c0200401e800800c0c02071002011014081055454256110140f0f47c421388118403071500110a003000100420583c7d121444e85c09105140030002c04100781d5200702c50311050311121b0035040302e5401c2148140800e0a11340042d21110380001c0012a0715030303c1ca200c02c404c54081148078030101f00040208441824 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 326816061 1250 326814811 326814827
    0x12060f050606090108071b050a0b012105120a0905040e0a020405060415030f08131401030c030c0804031d10020606030105070c0b010b0d0f0e0f1e0304060809010e070b0307 75
    0x1c0546602e450000784400003000700c0002800d010510005414400c1c480303078510f040948190341b000c201d900c0101181401460403109200d03241c0310000310300c441d164807000200100070361980301d4000d242445400000d404160469075a080030000b900800281503030380c40c0140c00781e90700c020000d407030010b50380e0040c0015240010916070207241042d280344a1010214100070403a42c02c140803e0244104d440d1840317039441010032030050758040c00000308004180601e021140c01003624200896280001d090f4140c41c48598008041008080028080382c000c0000541e5101040d0744160021181c00c0026040200d000b01400168050b4003001b0440c1401d10680703400107040d0918103c6111503948440b840d180c1402250034508000c5150041c00f8030a80200d21209107010b81408041d44090096607a54422030841d00a4800c03103000b212250b440c0c00e958800781c00003e01a5180a040c007400307441a040203420341203559620300d42800d2104040c003482c2e0150012400e0140c0d41e050110f401440c2c41c2e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 326817311 1250 326816061 326816071
    0x20f0108190b0d211704020a030b06030f0706022103040b16050702130b01180f050f0a05040c02161a041203120e030903100203010e06041512060f05 65
    0x300032003400301101e1a8582958041c04402000c94491199004602502c100780c00040a40c00b402410100300004202130521a50b426921501e40d0200c0b69442d0401c900c0a95010390040c04400042c008030304280d65a82d48aa000350803100c051221140039454521aa8002001604401032031201460f0707581499011040c01481e00d411410b00340c55410b002100a003011b440c1c2d0340036414440340940034000303030340f11150020a206c0d52030546400041c00740c1011110f050005080158104050041c900c44a0581d84c4026007a9411400c000a00030f6072624001c8260380456503d2000503036680b1405032110740241c5901400e10b4407040b440304074a5401d0b90300705060404881004070340b0f401542d4203450881c1d0749030000241d80031103170034240c41142020030917085c039a00f0007a02010902c0004014800c2d4401076040358042c4c01007107596801c0340801c0c000d400604c440100400c0591800f030300040780c0d440142c5400c506141d518000e0048003400d07044d00b122a907031220641e200200007441015400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 326818561 1250 326817311 326817317
    0x80102190302030603370804140102030c0606150c01050c19211503020310060311060702031b0a0803280e0306061306180e0106050a0803030705181309020f01 69
    0x18101100000c4d102e9206206d000251041e005c07a124515041003621407410301100c441e10421982d03410050002d500501420b040c805840001042952000040b80c040f10300200150419840701030070440c111944000f8400702a2051085801000082c4111800b4a0418405503030301c8064001c0b0403088901c0c1302c41c200c00d002e2000032003c426096541480c42c108002540016141c044861984009565400294244c45520070f40300d18402e4541c004400d4070301030050541000414001c01800344904038000b5010b4002d030030102e00310502c40e0b032811144503001b04582c280c142c0f80c11b2820318540210b10441c1d0054450352005107031164410441c05510300c00c3c68040121030116011035a600c0001e00b02d18010344000b0000607150380c1ca50b00440240420003000b000303d04059040e98003030200c58141e5081940381041c001418505403041d002240e0b031113006076044d5602d4600c00ea9058001c25541440307011600e107404c029680e1085150702035040240005044245d6005000003058464012414 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 326819811 1250 326818561 326818567
    0x1802010906030e100204060201051f0b0d1d0d0914181303271a0306030c06030c09030604120315061409031501090b09090d050d05040219080102190302 66
    0x540d0344090180195074582c20080340c43c0101e100350a103400d5540395240d04140c40400c01003440ca0b8190055401060b8840702190703044102400c10301100c3c04c91040e10078058042020108103041500404c1c20b448202034250310741590f01000b41d0a2440100da088006601a1414019220307085000505c2040640b02407141d602e413004030302c600000140222030050700c000c125004042c0b00700350443c0c0c604480d10501d0000007045071510101c8100b8040d200711082e0483c500b504615803031080c2d82c41801e00800505070190a039040c09101c0d88094041e40505404010302401a00e080204501461141c6410564180724500080c120303410120b8444900c000003108008056001d200f075840380703036141102c9a860b1200b000003460498040e02100c05003020b8400060501c40e290300180250f2002d0300c5208099940e15034a50701d80c246030301102c0205105000a030032007078040d48031030790241c40030b09007456244516104c8000c0c40d4003a403149100307a40000301900c020703001d0508403424000d1420190b003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 326821061 1250 326819811 326819813
    0x30f03090303071106071209060f050708090103050403050408160311010e0f060306031516030c05040305151e1503070909020d0204050903130b090f010c0f0605040809031e0118 77
    0x1860344200200030703003120040e001d0304590b91744401c11039104aa101880c201984000a00540180c100c1e10495010907840440614228091800c545029074040c907290301d407460403c0190300074807002e08203900304201840b0104494400308441c003241000c10100d80841c1e460352604150840d1100101d40c104100c00004451503281c0140c065517141c0120341c60b40d00c994446011a20b01800060340e5460404c0e40710512044044c100e1011b42c5460761a9800d1008002d00341042da0f991260344070040044d03205603808001d894202d40e5850b0002040301503d10040401c500d030081c031910550b42003060a507545240c044c0ca10707003001141c00902c200842840860040c1c0c0001d900032240040c00780c022615080082c44280f000e05c00c440307002aa40080800b015101c101c00799140e00300741c90042c0a014101d04e07102c81036029403c2c20006541c09000340500c00c1c0382d40e8500c0c0203020060401c8900d08410301644c01595001c1c416000780d007101d0342603031144405840c0190700751507040154402034004d50503490 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 326822311 1250 326821061 326821063
    0xf05030c0c0a2114070320030312071107171b0a0b0f0706091a0109050702060f06010e01020a1509060b0607050c100c1203050a2901030f150f0302030f030903 69
    0x140b0309208003c1008040086003004035480d201c401c0001d0320307030003203410200070031102c002c491201d101074141c040d4201000d001416500e1151404844e8a00301d41d100150300740f0f200c0c021031000703514280306940607599900c1c03106918900c003a00601d01e03500a140005030603076521a00080200048580b441d0842c90b20800101038824540e40c4c038102c0d0b80c00103040c0180009608000415540f0195860845a4180c0305100e1503e0030300075580140e0900c00802c02d00b40c40003655500982d40d01c1ca03006010703100c007001503400d980d04030100c0d030550080700a5080030032a1404441076440110801089525507445c12104035404515039030f1103501d00b800190049200024035200002003a03c1c5030320803a0071506c081d90305403a54400244032280b6884600d046c0380d0b06810040c010b408041e02170252090070440c2094600422640259140b508105106d9035032081d00400314800c9006d0000854914550a40a1044140c1c002c9000c85400d15410030841c1001c10413160101c148102441c01c241000e8006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 326823561 1250 326822311 326822339
    0x3020c030a080301090b030a1203020f090d060228350a0618020c0601031704030602030405031803010b1503071b08361003060b03040303050702060c04121e0f05030c0c0a 74
    0x807204240d404104188006032a00803600c04010052030ec26004200d4034207c0003030341c8410082c1501c0184100b8101c046103140040751220801500c074406400b126041101e003090100c181c0000070528007018040c2c0e9920800c2c068040d054141d008115903081200c007041c800820289180c0c0540f040201d1818a40041540740c1581d6004003181c0840310038a040705070074020341e0006440c01c0d1000090104100d0000300411a080381c0000b142400c284c0d4200301400c0703860001210b904003800c076101c1850050403000850b4415240d04207601d1401031040c8a0030100c030b100c00221440c520009081c5c0f000c10584d00a903100300600c5050060700400c031180c0e080102800e9140700d002d03403100012004614003030342082010340380e40001240c03240f900c0d040040140c241550410094080c2e42c01180d5911134450031601902e4456081214051032a82d540b020700c0341140942400c0d0800411040006c1c0b1403980c0046d4080c01100210303115802d10b12000d00b40401c020069124901104003007080318004108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 326824811 1250 326823561 326823593
    0xe0c030f06010506130e010b041d09030d1d0a03020f060a0b01270b03070519050a0c020d02041d030a0e0d020a0b09040b0a181802011b03020c030a080301090b030a 71
    0x1480d916400b0742c02c1c0317400d01c4501e07503003203052011903010000c08c610308110050011203003a18074520f1840b01c21500403000ba0340a0f10074250641080200302c0901031142c000c03401d0b0f00c04805442c0140c84025920b941031111403101100142c0001d4100c03607070001c0800550f81c0140702207104010b03900640c800a0000100700c0c1c418100c089800820384000b690105196004040c0c900c880d13696071800900c02440ea603c41c807c1c0807464125807000380310940c807031402e840c40d85d1302e944c84007864207841c0c0d001c01451644902c0100d074440d0315440c00c00654049000d4032614081d00400460700e030500000040c003506030400446006030184140240540d031007881c0e050880e46a03006940c1e81c0c4019402040180c000200069001668520005242000c1c1e02e0118500a031410381000301c01652010650240a84d24000c3e00190303098030410700a45c8060344861019100380101c805030030030301c1c000c00e090109c000030035100245e001c03004000300e101c98002d044111000320044c295854903581e07400a541882e0700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 326826061 1250 326824811 326824819
    0x50103050907120f0f05100f1808030105130b130b10021f02032e0609052707090801050405010203010927060b040f06080a05010c18060305070e0907030e0c030f060105 73
    0x40c060150114014504c5c642240545007107440c0f072140100542424008040318a1070002d00380c001f508062034100020703501404462443c0d281c1010412040c00342400350741c1b560b680d40c41808855984100340344a200b645a00820800c0c0c0c00410068110708810402081d50043e1403400c08412135120310000303400300f000006880340c6810a20260300c0c40074415030034080341d030b07010001c40b40d203840c1c0c00540841d040381d40d84a4082c3d031030320103114076049a0841c90320714021400341441881003201c0f00d142d1012075450140e6100396100c200ea42980e00640b02070318503940c008018020070230b0b14002d012411900c1c1800404410000000c400c00401d0800007400c2141d031030310341002517a2103801c401c00c1c0c5000d6032402d00030a40c68620321503d542011104950940c0b903c030605035418040c038100301c00301007000b48201c4980c0c645802078028007401020001044002c1c2605003442d980c82c0003c50003421a80d0340000e20345260b408080c0360010a68029101e90701002201d00132190000c0c8190644074195 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 326827311 1250 326826061 326826083
    0xb180913021002100f020418090203030717091c08090103270305031801230613050a140f090304030f0c0306020703120f020909060d0f05010606030605010305090712 72
    0x8101080240c0c003510000e40c840d8a8210041d02c06600041c1003e071816808800c00119044d444810100d2240d48504a100315549049103100388059002074985030011f810740340780c00b0746c9646441e01c1d41c90350000040f200a01040c60800c1e800d006c1c0303910355442d82d094005110326041d602e8400700d900070480302c10304040d122520107044000c6100700307026101300c000b03010789444e000d8034000d001c0740c0040703407814030b24a8810100b62081c0414020341c00c40b881044040289008906100d21000000408081e006600d8180910820a0501c101031042da480c460008a4100520302c135003075001e01510007400300000300123100200c00044110f07400c507944440c858a01da40366144c0500c040d030090f8400b4201510105a50b0203141c0c00c010b14448041c00081d0811034503000c515104128001e2003581e98001e0065400100c280c01c0c9910041c005502510846e16042c3c45641d5031400d564140e000a000243c03183c0c0c0800180d40c15024081d0440c0c40707240a070100a05004144904808031000a05414025 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 326828561 1250 326827311 326827321
    0x120609020f060d0e06100f0302060a031404030903210504090903020c0d0317010e1b1602151c020705030f0f13140a1706013011010305010b1809 63
    0x1203440701024018100c1601c4422005103074000f808240c003408414040c1e6070002e020100b4030a42102a00c0b40e68200ea180c1909580070b1020a0b0030548a0006240c4d594080706038003001004614800e500c81d030307644050720f820351034102c04d039266608030680ca104284281d4a5080d40000c01c0e03030300707803074040c200010f089880d0f040481c98076184008090f013145502d0710302030a155100f00c01c41aa030410303c94900d416680c4418002c142d00c0c048401101c05040d03140ca28408240400007081c1c0c03062000d0701a042c400c4540c000850340c038103246211040d81400181d2421000c0c044e103e80e402801151400c5080c4415a01c1e0151a0f115a0307901e0240c3c43c80004584107041d404005071980080820300c0c4c49481526503072010700e8485c08802551042218040015625070340080c0030418448050203826075910741544020b003030303090001d00718003403074102c5103280341c43c0d83c0b00c210b8064540a81040c0d00c1402000d0009800c0310b1042e00810801c81c410071004070f2180120050142035482620050207540c3c40d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 326829811 1250 326828561 326828569
    0x301060e0a02030f010806010b0702010e04090b090d20150403050f030a02040f05100f031a0414150402091e060403080c0124050f06071a01060804150612060902 70
    0x3500300c0d1030018018400d10400c084503602a41c81000024800815079072143c070b203242d4504003441000b400000401402005500c50740070f032000c180303010b080421010306641d2214000307141240c07142c005038032542c1c20082842d88a80e0184020214128011041154006060710340038110441c0c56045164008541018817a208551008201c40600d0742c580c2803050078400654024403c007030000b00e4030320011415117051108070103c1e03d441d1300c48a003942c040700f02c1940644840021084071107030780c2442c4003603502e42d4003039640442c8100100000b01c0c0b03404440510054030545106001d2441403041c19007503118210b9500400c0503001c400c0c0d214100f0103000904521840e000103000c000081000e58400764150403401e20321585111040015200b568081d0030202c20b403241e5070744600c0c0d1080c0803042d42401c81c02400c110780105403458800103030309054803901100307900001c000340000042009100c0b41004a04112071382c41c0d01444000c1c44d00c0d5015050b80c0189401408141d03035600340c4800c5541d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 326831061 1250 326829811 326829821
    0x6120412171005040e0c0901081f06050108011809140d0908070b03041b08010f020405010e0111060109020d0b1c031202071110170a020417011407030e160803130918020f0301 76
    0x14005103520108d41c0c40702c0300c40751580300104500d111685083da11164008150048030142c2b40181e4820100381c0c038141c0c4055100c000c8851080200e0b5841d19044081039456108004482054000b054540026500200a0025640074002c41c0d000100107218a04800007141c1e000f94210074100511562b88061412400c0e035680030900e0341d0319110309880386855540203441120b41c240c1311840034280010054480e0801840000c90075000386c401407260b209103901609160140c08c0d40010304c41500004969002e8401d0011170f8010042c501e0542010b0340f14040e2111440d801c0029410308010b9507a5001c0901d21415040c403941065034a000c1e610301c42e854540c08004401d40007201410507000d603100a603c507018030140003c0724500c070780c5c060005004502c0d04807100d640c00346040d070351094100d00034036000600d0010303400b400c06500c003840f0b01c40406102609585c4081d550701c010000c00c00260040035400564010305000308803030100d8485000c0001d440d01503c410915041e80000280104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 326832311 1250 326831061 326831083
    0x91e1704080d030e010b0a03060f0207021201020c070506070b0105220f0c0905010e0d060207020f03031305010e0907020c191a040305071e0308070206120412171005040e 74
    0x10001180000703440000246040480d000d9031030400074a840310f0074a50076217950025150f0401100b110130030025039107a0100c030780740002c4200181080030b41d900007041001c960100313041e60380d004160703490ba0744001d0200038000c0a08540440ca8450107503900039401d60b05101e46841054442c000ea481080d1480070301d81000942c075420010318084650710402080341551800009200c4d01c0e01140d1540141e0904030b480a0082030f00309520389a42e1303440040e51050b20101d8000842e03001801c00c0c0c0d101040544035040c0b50780c440401e80303414000010720298170902024410398488040c44245d603004103500072a000f082d41e4401c002c00c500321182e5540319190b070009180e0860b2070801072800c0344403009000cd481c410410740e20742c80c0d135402203050354025107100401c503002110b81c1003001607040c03401040d51a1025000703905040c0c980c24030b10032154040310183c84080c54502000b52841c0d02100c082d0354011920408661030510300481d590018160107100d001d16a6030310414441c40040103c1c03c122 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 326833561 1250 326832311 326832353
    0x70509090406020309010b011103180a030501110d0f050606040308030618090d17041703040c0e04060c1b03020c0d05030c0a2102010507080402011b021305061003091e 73
    0x281c201031038590020350084070282859407030f118546142e5032090304007007078920b209401103003091020f8280b0712004800803480750f44900c4041300007001841c00e004044082c03614043e22a203850440ca00d10041e00c030769880c50f40c0c01074a01810000141e9501c41910300380c94000090546980e2003201042c40c521409201080c0e0744406c1d4200701e000c04001500100080d0156039010f52400300d0001c6c400b080c001030340c00400c0024074070105040041120055680103002d078403949100d070741d100c50340101c0080c1610152010354803891044030300c40e00302c0030700011504c23041c3d402e0b10300c40c5140e14003c0d1655207004120340301d040c820407507002b80701e020015100d00400301401d07200100941e20b03054071020440b4200001c0b032402c440041356051f00611070140302e2a41c41d1180d0286950b03590044445600040309110002600b641c840c015880d040c1c0340a0031034005400c002110f042080030800100000c07480003082604110001d0009541c042000a110040f940d501e0390f101c2c014a0020341034201030f01503400c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 326834811 1250 326833561 326833579
    0x309051b040b18060f0303160b19060b0a090b120402040f090503040b0d0c0203030f040201080403050c0d0305012d090f0603120509040b040905030724060906030b0105010206011d070509 81
    0x32071640d102c480d80580b04c00c551807012050680203042e160702511010300320021400c0e000f10701146140c0c2c841940088403409000c02d4485500800701200c0168100c01b40004000c078041207541e0704422844c010f002e000d10340300d0a250240e000e100903064000e000038000c0e61501c400c0405122107030031003c0b105901c54107885e15280c0311340301d5501d241c1290945191460404d001201580e0001c41140e0117018641e24910304c0b50b4903a0019200644c002d081101080000c01c1661410b040c14041c64080c105181c1d00030a00b5490021040100c90010800d11181c40c1c010038500ca03803850505039a070444601e4003020522000103851b0708024503450384080c0002c24034a50100300c06510200501030414202d03003c00c4942004801e00c0111040080018620303401009070001040101a4990048048000c5810381e01d41c6842000260742e81d50784250f00c01c6031292002d02c2000120329445000d03000070f10042416624001101500e40258500c0750008007250f004101114488d10480b01e0a940240044070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 326836061 1250 326834811 326834839
    0x6240301021804061e06110a1e030f02030307090e09100203040804090510260c04110405010314390301120506090d0509040e01090c0b04060f0309051b040b 68
    0x400020010103a10503440d004010444c07000550754a40041e40c030a014000b40350601da1b0981d5085d0403005008464820125500002542c48402c81500b066401e03402d0056502881c02400c000042c444080554205108000d211a40002d1500445507808182c8042d515440c02c00c1e03092240c411860141d15000008010a00c680e12008208580a00404002a6a0b0452014810314481c0110410b8101c0440440380f00c100030110b20300d006032410103850006a4850000b000c0365080c2c0c429001c403180c041010031040d0707094460403c0c0401614060800c0780b9100114a0180c4501c00c1c5800e0012090b10501c200d012040c9041c1e010240b44240e520782d2940c440c2620611114500004c032482d2180f00c001414102001c625003004a52075100c49007401041c0080001415070060102035039940d0350380d04030102e17000c0a0140000c2c00c480c1d400c1039841381480001088070303140c10072080134142802c11840004030300140105059001090019100d40040b000070702818014a205070f010320802c1c2c1d03541d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 326837311 1250 326836061 326836087
    0xf061f0f030311160501050f18091503010b0a030b161e02031306020a0b0c0306030a05010501090525080f070318050f011b0e040c0302070b04030207080705120624030102 74
    0x26860f030f0041000c40321307400818030240325101ca4901030307540050310510003007881403113120107042510303c0c801078007803d44484400314031a504116906507142c0202403020340d00741400c0c4143e100810303040e900c003101c480c1162203c1c403814501522508018100c1c14810301000e1251240c50b0140620890754a40042030f41d20095581d0040501030b0300b811000302000a07403a00000d0010540b0354400c0c08540745c0e50347d100301e40c600fa4100400240c1c040c060b41c4400700000e40288280b90180c00d41c640000f425040104c1c00c0c0e081d00da031200202c00840c0c2101c2209040d10f42107481c06a0120b500521000e8071340e40c4031421006003074400c440d00da200a4120401c401c2060115085400c6004039008105142c25004140640214841d000020440d212802151070400360804c08480300302e400c01500c0c0480613030b6005045a005c86050b40140c000b4a41881104000e1000b40001c04003120030b000f00c034881416498807030030082e1608580740051004281c18140c810a06001c6c010300a008540703458041c003070701c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 326838561 1250 326837311 326837327
    0x30901111902062409090f010903021513030206040f050a0204050103030507170a0909020c030405060a0804110a150806010c0c0603020c06090a0f08070c090f0b030d020f061f0f0303 79
    0x80c1000d8000d1000180394804c1c030700020415504440075001321940204144041000040c100c091903001d003548448102e1000d00810b81d0307c505c20707802407101c00c140b075007070311480c5002a180f108102181e0068030046076001594941180d0018160890a5500e00c0c0c1145800d100c048029003041c2840b000000741a00300c40079040e01400348900524014500c1c801c10b14601c075031b15115001c214600d0060280e0304065003d0000007400000b200d15081e214000506075422130024000060b20201c02c2208200070030403500045601524070045a6003459401700c81580903084130f80c01c2140c0100002c685a20401144a8007504001e040b0459521908001c0280d40f040d086000c4c103110700c1005c0343c0084030000d0610541c64001c850180103180c140d035a001c1079446142d0644541020a03008100340301d1601c5944590090040001104402c04003072500300b4021000340c40c10354100c540310402c81040460940ea010200342c2540204404000748034000c1c000c25002411a900321100c00310030140c00c04d080e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 326839811 1250 326838561 326838607
    0xf05010c090807090e071a190e130e120a0513092004050a05060906121f050d080304060c1e0e010f0201090f110102070e18010b10091505070f060506010801120c03020603090111 77
    0x102b18121000c10b009402c0d105851954900b80d440322190084000754031002d4004d14649103440d5180801c0340491000740b1503141c11102807182d803258038181c0a26550b814049041b0a4040c690406c1c0c40d03c80027030000b984034131815010b41400100b103002a9502c4040300c1142d84a010f61203080d09085a1f40c03c0c030003a42114070950f03007034400382c081928038080b041707070304829844211140f85503255985d05000c5c14500c110401849010032400405240302e4600002d449166503603100340380399074000140301000d07005000c0c1c1564548440e6202090400d8041010300c0c0d0030000c11100c00c031054004030f1400415604c02d040c0040500c041c850a05451641812100030b928000c6c0304020340c038004c11240142c1f40d410710000c18030601d01080546610441c803103400c02c00f400c045041180715181d6030b44a0100d5042201c1007070b6500104602da6810404040c05003003000311180c41e021f46540c179032400e0200c0f808040e103d00400f000086200000750007520200341a004000d859003e00d2261480b40140541 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 326841061 1250 326839811 326839819
    0x3130201030e011103010923010608161d0d0203030c0d08060a140303030f2a0d0c05040503250f120605010b180d0f05010c090807090e071a190e 63
    0x2d810980c10005005943d011103d6900040c550303464032514900601d444400040144a8080302c4042211082c644c18001c1015441c1c10030701d890b03e40d0054010101e0174508400707104402001c15070b242c101e050790041094041c3ea51800001403400040c2c030b180a40d0707240d00d41c2da201d40c070940507807036600c071401901988054600c06011500d038189000c0c2021038510701c07501a48103100107807144101d003081300c3d04180201a41100c550b1035440c0842c0ca0714401c07440700d030781400018548100d40d6440c424243d4004452410320305241c2450b00103612290315600044c50313a0510113a0310031403200c004c08d0400402e181e20ba50184656191200074504406e0002600c94500e00b0307000041d150a280c0880d0240410039008811041e611020405440c61204d0151001102d040f03200000880074420440142a42e80b60749029900d40f00d0300c50320f05a01c9400011801e400c100d20003d03040b070001001c2064955515407901d03180f040d9502c01d40315000745036594a03085c103010b0b001054103801c1308820900d50700944d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 326842311 1250 326841061 326841071
    0x1140a0b19020708060f13061404031d15040b0c030f03040501061a040317030c0d05070207080106120b07050309030d020a031a06070b0f152106070206070e0906060706020313020103 79
    0x11050b1901c0c2c071700c103d42201d9070001a07400220005d4040d2146c02845100300c100203240d20144040901c10340046804034086038410fa0031500307030780301d410070048401011100d06403107850001a0007802c0c090381c418011014004220b400d15030f03105009403140f070b40108040e26200e03e8282031035400380400e40304040350301132000e8103450718034041c030102c85c20340b030300721207032a074040281e19030a900c6603c007c1caa0b4641c11418054403032a40c80a00401c0d004210795801041840d04110455003100c1003a485550300c50703d04000c080c0091000014107600020700e0401e10340707079074400c0c400c0c038103521400b0341094060b44001401c800442d00f41c1d000c46090707103454048801c60300085042c005580b1424001920319031110700058036040000c41482e9115400107402d1500e4011302000c0398065011842402004a00c28041c104081d02003200c00d902c040741e48010400c47c02e0202e0058000504254818014045100010702c0c540310102100c00391540b01c1c108640d05d2822000d44030142e0000481240000c0c10a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 326843561 1250 326842311 326842319
    0x60103020126070507080d09030c020f100e061602030a08040608010608090a110105040b1201150203190c05030714010b0406050604150302091903140c060a0801140a0b190207 76
    0x940300100c196001c909038406103859101e4140c0f15904540c0003210301090030030512122034014008c482141d4483d8403404403405076841001142480c0c0d218243c010840f20220000302507009000f0241c0600179240750360b4030001c80b0030380a1030f4090140d02035054461101190100301e8454010130841d80240c3d40d00340035980f41c8030101c941190030348085000d5070103524500e006c45d00e4080da486c0c0305441410594a40341e960007103c181904948120094200071030300400070303128196801c1d44202c4183c40694a005102c81000c1480d0104816510070000d81d41c04440c1042001c000310344079550801d4450a0082100f58200d000c1d00c0031014031409503040801c0040e203824000192819105c08446100806043c07803000c078003c2d042a4061980045a00c1c4042001c2c100ca20358600551300504c030300a45216945000c616000320054541d01a072001c2100c24481984480b005043d03440203800b4201401c40e44001500e02002d94200d04c3d110007000607103407a45060008400b118491030f80a842245030380f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 326844811 1250 326843561 326843597
    0x170907030f0209090c090a0204030c050f09190e03120106180506040b16060903081006090e0606070303020c070602160e090706200a030c02010908030702010c0615030605090601030201 80
    0x1003444010486511a40389000500d0b08480d080c1d4068130240464034900c00301390005511003002da43c81c00300303103a002a00f0700c28015915440005000240e4010310840000030201328521301c01003540a44c55031450244010100d690405403040c81c41c141101e8a404040071410b55048081c030443d4003194180d10710024040458580100316000102200c1c106450224441642c1e4440600400c584403da026800010280e10031800150b000f0703911809189011001040030740955008038091280d1190100705c0f44d1407039410307550700100903282c0b280c0f181603c1c501a006030252404500c42401180c001050107940000c2041c170300d07100c180720512160358940c0d401020300e209845502d125000008180106070042644117004034140150b80101240c4100003030a000b048002180000d000c140362109540c2c2c000c20315070151040b40d0282d071600c90700d07500207801500c036050001c00803520783c0390000c41c1c94080d000342c500464118405020510302074100540320a4240000c80c08281c51a50307611042c65 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 326846061 1250 326844811 326844823
    0x6050a0f05071707261006170c0a0c081c1a0f030c0906012c030c0a120f140a06200a2a14100b0103020a2003090405071709 54
    0x400300e1070144c1d00d03908801c40320074400303a11000e11707282d44541d01e4413a1040c0184151280c12582241304d055414075000030040e10406402d6011140c4220038000658100000c07509210b0341c500b06203100d040c26241c40c2c0e0403401a06071140c500c0300c1141e090540340105401000080d18a180c100100c40c1d80b0004000710300b141c81914030b07050740c40f060b120708007801e21801c000c2e0440c03030504103189100241e405845078004509a51600c4442c160759110440c14200021040c203101140c4a001d410b0912000c2550b450580d1805030446030840e03d0441070020391310300c04044203c290143c13240301010741401c6000d88107006404840d00d2003081160201c151001c00d8540b154a2903880d20800030103900e55081d040300d490f02c614040c0c00c1380078441c0001813080001900c0e0010000150000d601c40c030565504890140b040a030502d401000505411540316290b611800e1002c10345c5c1c0c601c0584800c140380345029161107076401078500b00601c001c160f0081503000751a04920b644000740e07900e0ba120f6544a0b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 326847311 1250 326846061 326846087
    0x106030507090e0a20040305070803090108070f1413051302070809130b030a0b0402090f011401051b01050a05040b01170a0213090f0c08010609020c0705120a06050a0f0507 75
    0xe26501040c807400c0e00741075009811900414000c50ba4001e124920f116071741d0302605096814100040410400000348110401026070f00051030a00035203000180212800500c81010480342ca80095150f41c00752503010241e200520780c440d15200074182030701207813006014080c85089401d41c0010007240c00e000f202c0c2610761005940d410900d441c0b090003042c0c2c500a56400301d06440301d84003500c0ba2010002d0818060103514181404e04040c01802100302014018075880c07203a84005000c000314180c0c090201e0300080c07807c00e0340d03844460035251030000d0310701c0d804490307509190130f210f84062182c0010f4080d5000f982c2403c004e913031b0b4400500030081c44400005c0c03550000190b850140c0303021000011440300e03458000c1582c000c0d969030407040100088048440c03850100050160071024130031040a0320b10305e40c046280c0706202e00041d954411a00c100d038411f000c0741500a451060601000389103a5000c101031005080001c20000545601c4900c20b030528030b420002507044e4882c100e506940 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 326848561 1250 326847311 326847317
    0x2040f09110d152408060d030e27192913020d0c020d120b0f0f0a0b030106080402030c1f030509070506040b0c06090f030a0c060b090109020702090106030507 69
    0x2210811201402600082d018402c03d40c0100c440050b403100e00102107031081580c00c40030703c080d010501e4007a00b0003d0280c800f50142c040e03880702c0c0700001e400241c02c9c4881d01049070346400140340c1d0482c015107059209914041402400e05108000c968140c40380c1da8044100310034416105506003040140d082509840605000d0911f010480d040004410406540d40340004d0301e0000c2c0305400c0f006581d06ca00d00d0b9001030f4407080e105080f5583c40080901d03050444a000d0200c603c40c0c00000300300140021003171b807040090000c40a520b5a4090311030006202d20789075242c8135a0344c1c1d1000341140b80c0460b4281d000340a0300f103010180d468603042c507111440151042504120048000300e0003404001c0c00078850b03205022010490350303a900003030300085c100480100d50b5041120801d03406e00e00c01074081c24403984030780099107503088003200352283c5e203071701d490810728241c01400d010020f002c0c1d640364642c010300d0f40340000c0b070181c0058004012660080c1c4800e0381c02e0f40e0301c410031411644101c0e07a0b0000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 326849811 1250 326848561 326848567
    0x30303060901030b100b0a0c030201050f13030525050a03020d0203033102061303110f0a06080c09180601032f09040213060504031a04080a0507020d050f0102040f0911 73
    0x4c1c03840a040742d001664400700d102e0540d02e40480242c3c59102d01c081c003000c1240062214205a03090080d0341d03001036400341d2400e07a030602e41030500740c0f00c40c011401400d200004c034440340314600c4011294404000d038900012007050505165482d80fa00c11420380040c00341d07a100741d070f64a0000007142e01440c1a10a0340e40f910034800000e03007130f04403110403501ca0561f5125600d0056914400a46024098545008845451441c1803000240d550f00c2490154a40d00f101d144c803540d9000c1401c08440389070800c07811555440c5514907146c032441c904164416107041b55100d15200c9010340c0c0e1b125031405e89080003a03010690815031070b40020792803501d004052000a070901d1311010007400c000c40001c2c00140c103040d4000d40207840341d16a82c12240006101003010001c0c02014440b4086c1b5405150344110203041c50307110040188140d0342c260085c070500058200842d00e07543c8400c00c50f16080303800d485000f5a076104030b9020f58010300c170340389401d140c3e01008181048144078021045403241e8140b89 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 326851061 1250 326849811 326849813
    0x5090304050d020112060e0a0f0b1c08120a0902040b032d0a0c08030306010905060309060705090f06160308060a05010504030f060b0310140703020f2a1b09010503030306090103 77
    0x282c0100003501c200d04002d0040c4d00428007440a01526000d4401208070b50854946001000e00b2594450111348560307040ca07038642c01c1611030700043e841414803110151440880c0e824000e00c544560103450250342191000c02601c01c5440d030005100c130b80f007110240803407032040041554503c04244000815102c929002d00101d604420501c200016101520708075121a2629080c2c0c2c1f04683c04840540c00000800c400ca691009142e0007411007102c8050540c10000a00c5582e080000c2101c002c0c08000541c105060351402c1a480040310001c10080d82c0b05024100d00800e04080301c42203010941c80302c00b1491318034225000301d0a40c1c0040c2d580034142403841e140d400340d1084a15090714910390310103259240344c81c2844400031700b00c0340c0c100c041a000380203c0203400b03900000708020300b01807061107202004115002211000c8202100403c456500e55038150504840840940807500c5400822400340d4511a81034503900400c5940c0c084580e0703035809150b160300c000c840340741c1d0100c81200148 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 326852311 1250 326851061 326851069
    0x10021609091a060415260f06010e0421020102091201020306100c0f0b0c0715060e0403030c090e0106090e010f0305061303090b0a0504151d04020703030f09080c100509030405 76
    0x140c1c0300c1c2000708003050740c03581303640d0340075080303031103070000700c1d4a03842d41c1c60641041004c040314a00502c0307014010503c51f50b10020345511800180038041c2c0300301000380032905216407400308212040c03420340c11240040403ca400307030003075110344500b07401004200782c500d00c40c00040c07003078a221760000341c080300800e10444000c548200301d48104852042c80c1c02c081030089002003100c2d6100b8070030141c211b076460029041030f4000c002c0f2080d40520b41c0f810802d09008240714100c0d80e40d00141d0600700859802a608410384140200d03803c2008040c6105000243d0705030f1100c904011244030342e94684e03507642c03100700e000a450000e02010700b00c3d40c4000003090034940d1000900c2c01e00ea009141c05250b1a440d0206540264001500d1100040007c2010f01401100320307840c00800596041c108100c40c0c0641000401d083e06100d82841543e0110f51201410700035081406201d1038228100b00f8110b0916081601c0e4004640000c0c4038414214040308980180c4039460040d0104002541003524180c104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 326853561 1250 326852311 326852363
    0x3d150c030e0114040905070203090114190807020307140c1503010b1209030c070602010504061d0703030513080a0f03080906010617040201090806040c051005090d08181002160909 78
    0x2e0050f0010400020400f1103845690b01480881d809550f55042940004140300d400703011180c0b00c1d03802004480490094900340035000001030a061b4150f5031100c205a0a501960307201070201c0080c0c2c0781e114040030000c00c4904d000c10b0101d0b080f4030300000018403c402c50200b40164002c4880800682402e031120b1103580d42d0011a1800b107900e000060560030381050482d51080b40580e440c1c00501040182500410300c680f0610140340719580482c07120a5500c1c50313035100281c140400042c04021500503201d404003d04103030000c4400d201030302c1c60804509103507803605030005511540403460104010035014100d4039195581c0c5c2d40394500c810f0780706501202400803410b000c288040003c4101003030008900c6580916190740e103c501d40b400380103192141900400030800300300240001951603007074846a03103070080b455a0702c2d50103224a050703074401880d0015502051700080c51080d1980020074201003180c041c001800aa0741710b0202d0701395000150010100b803039240710490780020101c02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 326854811 1250 326853561 326853587
    0x60306031a180708150a050f040f060e0a050a020a06050307140d060e040807050c0406080d08040f0519031e1e02010b1f030509153d150c030e01 63
    0x2080d03482280354481140341c040303264488102070b04130030a0314031a0036a0a45e280c2c1e0082e50b100c0280410702e014a814805280c1c0240300800c100a4440d4038814401598007090030090f45008443c5080c62034200700b5625913038054103d103c2c403044030000c500c203413054058034020103058071403980101c17a521003800d4541211702c036a43c0703031580c0780ca00240025007103003200d0045008500050b5611b000b070a049081c1481c407801d00e4040c03414080100180e104c0011402d141d032487d07140507200740e100e40c030340210030040c4402c000d0010b1040312801d00c007018030410290141440790700d44080800c0444484481d0316081c03106034010075005c80300655040844000c009d0807140a2000003241c1c024000050140f02344103895001d82400704070103440540e010310400350400e003060000c100100640601c41c0101c4001016a120074410313020741d01c11210405000c2080f01c8041464036072610803440040410013a920860f022840f40c140d8541c0c46c107014003192040d050301a51804224542034005551080c06404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 326856061 1250 326854811 326854831
    0xb090a0b18031e0a031803080c0903010f020406030b1314131e06060503011a21150c071101170720030705010203010e01210f02040b18060a060306031a 66
    0x407802011060b003800b8043d90085036211140c40c3d60b5850701c0141120344d1142003030355403e0300e00802c40c040307500144900e030300040d0441c2d816a1250203038042400f600d10020342940701030000c10003041d01601904800c0b0b0f8900b050351000008500c40d590340044e0f50345c01114a90b00071803900410030b80b040c0c0980b40e07003025001c6c00105024408440841841e8072102c1000e6070f8080c0d0701e17081400246400e0060b49006a6075400c19403034004204001000d0300026400f0040c0104c001d0b0000d07481900510000c501c0100640b079440310f501d0101c02d9400183c2c4614001ca681c440440c80141c1158080c07400c0440d40740c24100d1440090343c441801b55464036202415051440744003000d8614150304000030030140303105000240c0c69500d404000100c0080603081005000e000801001c403940201c40c596685580002e05106008030318000700f002014103e1109804c662510340801d810001c007a100c600547d010b840182845681d030307404400b20f41650000800d55200d01000c00c0741d44140b00801034100710301d05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 326857311 1250 326856061 326856067
    0x150a0c060902191e060519020c18090c0d211404030312061a070308040614090d0f0806060403030e03070b031806060a0b0403020103021b190b090a0b1803 67
    0x1d000107950169100f8220b00c0c8100300101400100349206a01481c24036440c000482c06041076009440b0b4002c076040030342e42ca25680152082c1620802545428540103003c078010341c0804558071001802c12282c0c4d1074944a0b44038440010b08100070386100b1981c11034041100284050034098162500c5c071020700400241004450b51000c001000304011440703503d07084c403421403140924040e40d010340d02c603c1142d480f15103c00b403480c004000300d902c00f961510f040d00c9160740d686042c00042c8580244210046158001c0010340a00091b0700100120551a01400c402401e081241c0441c400c480c1d0039040b00051004000180c092045103400180040c2920700312a1124003040241d013044076030803003101081160494914042c40120f81111040c3d03041c048460030240e1b064100c1c400d174440203042640c00103004014541181c1d2a2088009503800d40d9000005c0c140b24011034691900700765071100414001c12031440c40000d524407650792003c12061295224500075600507403009010485000070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 326858561 1250 326857311 326857313
    0x203010b0301060602011a09040302150c0c03040f0815101502120304050c090c0403020d150e120a0905040b0307050d1505010f030b090a0302060a0b0a0f090c0806150a0c0609 76
    0xe000707a4021301015400011001400384d0103a43d20710501c1482c9000755542d074280800701f903000c5480c40981f07951100c00d034407035100c2e008950410705c40c004100744580004107001c13441c0c1c0052035501007201c05c1d21080700e06561003c00c042074200c005640c0307a0210f0346162820040240c51040c610340071040b500640314421801c0c1e00c0d07000203900488080b40c0fa90402c218551461402c02d144541189000f184039040600b0340d404203844205152018002a02105203650345035030070b412140d030b9850200188e135061081e44403058003a81203011100f02250034000049410b00b082e2103600820300005008100d25854201844000b940b010003e55a0025104450803548030a02440b0700034801c02d20300b020000d1440c1080c1c0f82c030b10300140c0800c10542001e8120800320f0b0340050240d8026005080c00035000b140e039000640040d031130340d0108200030600c110010f94036541d40e01c08c81c0c07103614a86031440c0a50310391003084031440042c1c200c0c044442c2d0501040084c903201e076502403030240c4079203000194400c80d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 326859811 1250 326858561 326858563
    0xe1e01051c0203011502060108101d03070b2a1801030b0a0f0504060603020a0503040b0c09130501090f02070308010303030209060d060909060b0f1005090a0f06020307110108041505040203010b03 85
    0x600d2100d1801c03a0000010014900764070301141c8242103a1016000b1541041443c5440700b1546440d500048c1d2a00315022020003c15410300595100350100c0350b68500524000410001c11254003940041486541d104482e1044a90000c8560800d00c00d282003104a0b203c1d10305610708070000e0416542d424244a1902c48285000c090050b80380c0f506009880c200401064070302c0b47c0c22000815005002064420b0740200035660025400907900130035640d00c691141726401002e004c10341c004e5242c08103418030762055202a06940c45840240034100200006406070320034280002d001a40020042001c41d101c3d6015250820b402000549484102c441402c103413002c9400080201e41c1d100310440170400309110b2002d10031000d45899220484010010b94525013104001d018407000250031403103992140c840c8000781910b80e40844910346c8610000b596038001c01421034200740390380da95064643c020a40c0c02d21441d800b603508107002c1a00800f040240001034001c1ba015906c611a03185503941c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 326861061 1250 326859811 326859847
    0x120d060807032d0b010b070212190303050f04030801060f0207150908010c031a130e01020304030c0203070e0108280c03052404020310050c0c0115060f0e1e0105 70
    0x4014100c41008810410603080f0451422110070859408441d280b0002514028500d0456000d054115203a100f64000319594011103400d00c210340c0601c0c4100001078105105203030a6a002c2d0360200019a5590700481000000b56000380205841c1c500420030740744580760f95800441c0d644141c0d01d2803035890f0039003400e042800072140081504d401e414003403440300b4403400300340c4103883c035050020144580796442070540b403840070ba00407921845081d50107003144e00444d00720a001c034002c564a1400e8107000749500040c5500300d00c6401040030005400f07030810b41d82d9058504d000d0107814006c01803504003044403074111000c285100f000503044c003c16150001d040055014901a051549441100f4401c40e042003455515141c0b040e4140405620005100000e070b4680da24000342588901d40b15204500079003022500642c00e0810400000381e00d03c0003178085669540f2840c0c00c181000c00155038000c03024442c1e036005651000d80c80d0400041c01a07154070311806041040c5440742100c1900c440354 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 326862311 1250 326861061 326861063
    0x27200139120c0b06010305060f041a090a050109110c030d2705010b0102070602070b070206090d0c06020c0f0904110d03031134080f030912040303021c0f02120d06080703 74
    0xd092020b0420a1025091419900c2042480c04100c1403405400140074800d2405c08503002d40ea0341d9403080c20900303000c070b0300500c840c4000b4004200c41c9044003181028020074040c05101609051622070a000d00800751982036001201641c182449034035180b00400303072110b0203010b6039803840e5102c010075141c0c00c91441103030150f40082140000c050001e4a85880c3d0351005046511440302000340345070490640308401e40c122666581c8055074400622084440b03500503216005401001840300d40008000e05047c5054032a144151801c03400c1128101c0115000b0302100c1c902020007442d440c004914800302c0d4441d050000c0c020450745040001038110143c0700301d80990341188003d480001810480e5a040c440c0440c0b0980307100365980b8402c5000701e00306415016000300105866a50a004418603038901d0104d8035115030756406e00035500d4401401107842c07111010645103442d481040808648200c036001440c0368900100c0f51895540301c1010a2402c550321400400d0b4400180441c00c025 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 326863561 1250 326862311 326862317
    0x712030b010201060f05060d1509020a0c031b1e14010509010603050708070605040b030c0403020d0b01030b100e130302030409050c120a05070f032720013912 69
    0x203000280002e400c540d416040100e494400160401c800d0361401c1c1202c44444640001143d1480c0e10381041c80c00c941580c200d0074445002041e000c101d10744c014480001c850103562500769040440da02001911040c40c00070300480802403030942d240c0030404228425130310a1642c00c025070400d24171a401c60394140d80088941e515504100f050001c00c010310b6000c0d0103004041d1110b2440c00d40044c0c0b02e482076204001544c413020001034495006501507034021a005007041c0c01c028002c2c60081403100090208a5504400c40080707440003828500c01402e888940301580700756200c00301c0fa150440b140782c0c012801c5200030803001c64840c1440c02081e0148110094047d00d9010f0b110b503e6141100040c281000c8603d41020080c029501ca4a04c0c1400d0080741070028401002c42451400341c08441070001800c00f8600c200403c004000c5c1030300c991801d2079030242c0c541020340703001103c0d0b460002d004141d0f00d03480c40540d03651210082c09028010401600c818856680d655902c48001c0c50640b000804 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 326864811 1250 326863561 326863571
    0x315040617151515070515100b12070e0d05030d02040303270e060d06020a0c0611040506180d02031e0705180f07030b03030706090c140d080a05071203 66
    0x50410400030001c0e82d9800419003800d41c6003805203181c000626501052160b03885000c14403010311258100c1700410f07002400d072030040354401c031440c072103400507103030001c84650441c00001c0720102502a00c90744c02000040c602503894607002214035005464803594403002e03800d194000544d040004101864040c4005611584ae50070003400c0017042030300212024194403110710101c0502c28103002500c900440c03800e15600c03090301084440001c8100140300602c00280c112102c2d401ca9240780c2c0140c403421050042014010300e1211a0203103109040d00080d041c4a141521000e10200041800000e07140b02c4054007503400007880c015241149258694540144026a10b402c2c001800545410307614001c080600d00100f1807580782c020440c00140d00c4a802007074840c2d00c250004140080001e00300d07911408542811070040062901c01c8070500000031000607550724928850104581c01051480c0181d4152101009607110b1a07222007007290401601000984040000c03014104a5500240c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 326866061 1250 326864811 326864849
    0x80706051512062202150c0102070b07020c03070602070f05150d05011d01050a0b0909040302071e050301052202061309140603010b090603030d0b0a080a0b070212030106050d0203150406 81
    0x4d914010b07503901075640448104a140983ca503030900740c840462100c0019511400c464032107009000e20040101300f5200041482001ea034002010030b20440100c0c156032034a640c0d940f0a0380c0e5200d0300e12031141e40242c094810800c0b03107019400201c007001000d400a01c2d02585444900c100d40c4240c016042c03120990b21104400d100041e40b06000d400107444141c0030b941011081c2660780a866159441422003100241c101442882940018808044070004100c0500e0925200803100d001e910b009610308000a0f4640145030110140034a00c1580a003c061854003072000581c00903880b4800704042980001d800440d41c4200700e03030381008220480301804d04004050039903d510840380e20810400042c0485030360088106c03110181c02c1e1900050340680c0901081d05062203900c50581c42c0a910051010b00c0000c02d182841100c0300d50a0354080792104c004c0080c180401c4c003030100002e400340204440015254010341d004500c44003180d517030070701c40d000250940325540c1014424142e40081c4d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 326867311 1250 326866061 326866081
    0x153309090d1b030c0602030a0b0a0303030e0d021605060c12040b0a030b062703010e010e0114091609020a1e0903150204030317060d15060812030408070605151206 71
    0xc42909445050040500940f0020301010090b0780c00307400d5580c00400f045c030544e4594400e08603814050104040c40d503883c01c01900070422000d5401041c000c0d2016640224400302d1803480d1001c40200e00c03840385090806015590f00040202d49207480b030301e8035025046810740080c00080060284c0380e0390b0350303890701c8005083c0c0b0070050000c0d000c0d1a080c800da0b20b00092446055030b490100071a000070324060000003902400c1000c50700081e5518001d02d150300745406400820790390340078000034005601e030000090b43c1c60b10200c4003c0f0f40c10728545010b1041c102d45800510900886240035062506092903840b0001040d00042002c2040d0380001c20070003140741c0282000c0e050521046041600d1501c018000c180d9081250080300c12900000762240d445150081c4210b4201d000c1540c0011025000310051031a805107690034070607a81c580300303030341400811203100701d07480341c42079041010360760f6400040c01e009417103002030310f81d5108110381e55200c8080c284c0a0306120f070010207490408013005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 326868561 1250 326867311 326867327
    0x150507082205041b03051b120103111203070f032a020406080607050d0e030f120f0606090f090402010201060b030a0c110a05070e09030403060501090e153309090d 71
    0x2e500407410400d516206030904907869519003200c0c1000324007959079440194000c22461002402084040b0301c20b40040722003002603051324812207040c520a20044100442500c58171505203a80d40208031702e0000809151108614900c43d041101082410440c504010800005e5a00100c10000034203420b40c500f90061500070958070b000780c503850070007280080152080c440d07040c1429488805454003001c0c2003085a544c1032036004802d0302d80c42c080302412410706c1f040c2e9584440000c1500412841e141002c102c07036001d00020030403044000c6030424411110f60040c0141e0540d565104000b03802e0b8a050001c5105a580040004085407181000382c0303000144a07888102c2c0d031005d138410b03000900004c2c200f0103907000d00c51009001e50781c20003500d1451003281c0000b4215410900002803048481d000301c08850b0260099400315a0f01400201a556044900f146468045400d070300c0c09098269180c47c1c42d2401d4000306404494150118001d202d054921000552201c0250002c0c00d900c1044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 326869811 1250 326868561 326868569
    0x11d070c0804050a03080c010518060106110312090304060f0f0f0318140c12070b1e1b0a021e010e0609030705040509060601021612080a090513050f011d011505070822 73
    0x1c9101d0305011081c0740d9070f032f0710f03030500a010509c149400101c500c820108142d403404800766520040d1403912407451a01c0ea04584075600204446c083c00c5122180210ba0282d200f824564905040d5660008114054841d01808030303804050b80c180d03800031841c54140401400c00b440c0040018000020078170144183e4034540c0740340c43d0055134007480041d880c802121900e50360804401034143e03c0a101c1e840d00d11551091592102d040e002501b503621000c610054070900885514212070181c070208420039800ca01c90328001218100000682e1601d83d02030700354820003804880102307407100b0108040315004e444000c1c4903440001084201d6a0400202c503800c031080a542d5009440d02c80b8102c40d090b0510b00c010421040440c0307a03841c10381b00d6003511004042c000c0c00041c004070810440d00007007000766030bc5000006418000b2603c40110b1860407070300c0c1e1040850981d16071a00741d02440c0003100c503000780108002003001c10003017124140034203800500c0031505030070400c500055040314a0107900c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 326871061 1250 326869811 326869831
    0x2010909020c0a060b0a050a0e0708070f050d0e0102130e0a150312030b0f0603180d0e030d030b0315040c06020f0a021008090a06150509011d070c0804050a03080c0105 73
    0x480c2c21030414010602e00d600a80c40030012405000b1400000c804003015040282c011199400015240c0f0b00c020030320b805401a51100b48840d11481011030790a4510369081001c41c90400100c401c5910540c011544c0000c0c03070000600300217850100c0c0c1000c004917030080390030030003c40c00c1c0681d41201340f103540b03468910301541c1d041a5142d0340da5120071050f62051841031554070508070140751511528034040000060005580e8500012205900118405c02105a114203244941902c0c0034000550110340024000c1c200f281e00c4100850150129012540c0c1602a00500c400d421000507803a5010301d10031700c21380e03c00c41c0c2800002460b004181513520020307401144500302585541c108895011618030700095140e4a200c211890f004480c1402840750345040c2c03021000d040329084007001d448040b90b58401607680c03610006a0f030b110580e40122410502004164000d008244004071107115210302400c0070b50328000155600d95a600541d85170360009030740080d161003071046590200c1102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 326872311 1250 326871061 326871067
    0x1050309212a0601051302040909030f110a051c090807080f061302090406090305160c06110604150b031230100512010209030a050c030607050c0d080c0403050d0201090201090902 78
    0x141c089a4a610605c1210300800405200615460041e01224042c055007207044c0b0000302d4a00c0c00401003500340e550700300002ca420407010300300840032503c0c95650f0303040801030a01040e041402428003034040c40c4003003800781503140040c001000b80000340040c05250b0192410702c3c55011482c1c18000c0040484c4100190190a0310050b5100441c50b500960810b400148458072407a0941309442602a04405001c016032120300300b140040d42c40060b25510707038486401a240b080c1403030307507a581610001e0010009c640940d00700002076103d040320b2200101240c3c1958030003248810550700c100c1240b000700c6600c01107c90041810b0441c040400c0c035200c0c00900030b261441d2807101202e154003d1902c2205403100c2d51140d224250140c885441005003500d0700d500d030502d8081e540304c4003140307014080e000395000038a910b40030704180c03900702490300060502c03402008000ca64552000700300c841600805d10010000c218100542c000c1490190000101d0410b2400090a8051164481a1200c0c010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 326873561 1250 326872311 326872387
    0x3050708070f0e0d020904260c0a02060904090f060f06150f030b06041d0108100c02030415091a030f0105121506040905060903031f050f0105030921 65
    0x704124444080ba2911910224400303000800c002503070b90000e54010581000d00c801d00c05842074004400d4100d103140007480146101e51080760144019440964001290403000740c1401d1006000c0070a004100280380009a545c07055000c44004c8240d503003d40d101c4181c2030035585803140c0c20142084100300c901452042400900d1a10b100c040ba008040d01d0b0101c0e04465103a22090301c3c042c01e0a50900000d480c5040c100500e003102c04d104241962158010310200c1c0c0261388280351400550f030703024516103810080101d110a1400154104010080e40001036220203200700000100500001c940d8900340038501790038070310041e00300030f104140ca1103c1c000c80050001c0d00030005d0340002c004610a640d801300041c002d01030845d016100e40070700c0c400c00c0880138002c401180711b00c9240740c0700011440c0601408060141c540074143e00982140c00c3c1110542c011b00c0a10761080000048481580950302e40d407060070002010046c0344031002c03e078440618100582010003240740783d01c1030700710781c28 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 326874811 1250 326873561 326873567
    0x80f03090d21230108010b040b040606080103140a0209070e09060108090304060e0a08071706010e010f0e06030f0f06011d15011b050607080609060306131101030204091b0305070807 79
    0x52900c0e4142d20380d61406041002804440c02c10f10703201c9807010080a56070740740d05140c040e0941d01c1312144614034103505a081446c0510482c000d89410740c1d64038000b0b03070840c0d41c5d42e00b94101c0035030b405042d03110340d007295001640d035010082d208d81c18a94072003500c82c1840d014058000701c0505040d060100e620308210010100009039003c41d0524a0f0070035545a503a40468040062038216160f00c1c00703002000f040d94200c0c5003000c46083c544104a80709683d84290f40d414042d42802140b03000d40340408200500303101c1d0b55480741c0001000341502c024170100341c0001c1c0350011104205480e40c1101004003c5030700781940845040384429100b001c0e600c0d0070004045034540c0800c2d2a418000d000d81c0b101c0031002000425202161712034111150340c100202c01800610741100c0452180c55074000003281030401251250041c81c000c040440050380720b80c0c454041d00000134101c0d04066092000040f0f90748a40225441590f02a01001c3c4441d29480002c0a80e6002860307101400120010300c246103138 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 326876061 1250 326874811 326874857
    0x15060f0e1537090203070e0a03150c052b0b010e1818030f0d0f060b030a0c03020f04120b090f0a1b09060b0a03061e170109080f03090d 59
    0x448a5031151003110070801010140e0b240c8400841089400c0c04102c200640d801940100e21a4880f103896105103000c00442c80210b000c01060140011001c011205440c0c01a900791b000606101d4240040460300c0482081107040c0c00c086046020202071007504980708030558403000386844030b440101350012610001c408850301e03146441c00c0d030005000b8404140c002d220035109a080d40e130b07650540480b140894012801070252103107813144400d4840114410081110941340f00b841c1555101981c1c0802058803940c440103143d02084052034846800300148003814031301c44054440c0c04182031035412884024562005903020062a0b44001000681c0e0304695512900e005d1181c6032407000c08009190710b83c00090038074141800442c10030103c00c050150700302d40303903020050140c1d51808421031441e047e02c1300101c0c10024905000b0150582100f5841144440010a2010899940e03806550202c1e000401c0e988010040c8010104140b08045034488645441241014800c0c00e0a02c5a8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 326877311 1250 326876061 326876089
    0x110a052d0f0d06030501141008071a0901020a05010c2c030c0904050a0204060f14010f05091903050d02010c120c0e040b010c0506150406170703030c15060f0e15 70
    0x42000c110040703051240d4204030f000d103038800700a2056500b0406111701402e07046d505054010403500300400da89800150010441d484500501c00b1456084412242c1c2d5210054443c1180211103004001c140709000703003030580307040f582e80b50428012001d150307659900d003d22042c0320780c0c07105e1a07110195600048d45525130b07804684905e00ba444034030301145440c00d4080c0081d002400c0500c002500f0103400c0c4003604844551981c00700c0c207050300e001103810040d10011200450814805000b480c20445403460151034180a081011a240d031549485d0500c60030340e00300181c0d1607080384100340d544840340012140141c3d4081c0484080003002608503002142001e010f03e0303031100c8044080e84260301500910303030050165200b43c1002400d030103007061054481c174080d03401c168000903114105403d42d51051134102c098003616085590444400100103000d80e518030820810502819441c0314040003080704e50305e15064649001c0310a10440300040007502d400346606100c44480d101c1c410081200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 326878561 1250 326877311 326877337
    0x1b060216091e0b01170a060f050102030c1506190306020c0f0f060708040204090f11120a02090f0702030c101a0901051e06040b12180604020d080d110a052d 68
    0x50b6103610040f58103404004940c2e22100303c1c0c205210051b039587c2c3c00407060322200002c60403019290001640d81340b048a25810856104002e900c82c1c021500030750039001407006024140038807030188040f19400681c0c0040d0707075150380003a400b607101d80d040012002c0d20025101400140403124401516142d00030b1400d818000741d000042c1c110f64a590010b0f20590740140c6564070b0501c5420400001d4402800342c0703000702d0b06220341c2610b41400050380c15030540d004041691540d2441c40c000190100542490b0962205100100c080030701482482d18440303190000141580e40d02034040d0b00c950000c5411400b401c1c403c1d0044c400c3c1e448183d6450045a41130b603e0500c208240320110307140d8403440d80170300040e500c00303d403070542c10748916441400344146404031a120500038500d01e84803d0b094400130760020080920f140010b038060040e2140508410000440204e6480700351500d902c240b180c0d400044000402e00d010886460103004451078886145030140340b240d5002006110b215801410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 326879811 1250 326878561 326878571
    0x706030509070f060302031603150b070f0203030301230a06052a0105010906050a0503010203071e1e050403051509031815040b070b0a020c06060d1b060216091e 70
    0x40030002c000d110014500c40d5024460740356180c100500079002501c200760740949000d11412550702c24000c6000c00141142c054403194503050301040c581d44421000c58400803045030300340c00369800740081c50007018801c0e154112800000e1001c1c3c91017075055402845482c40e04020302289174048269100f06000000c881c042040302008070103a03000d550030109442d801d00c400481c140f22560401400c42c0c1e0145d65000c00ca64032001014280d01044401900281d5909414103040e140344115003005081c0b404e00c60088000fa03812165a800c6481d00704010800c00902081086010800d1160300d0151741520300460801040e42522440f42407090210a101e4100d03050503651809800c0303c410103030642c0141d580da83c07040441c0b05900a0582620032041341c00010f1480e08403802100d0b29210b10502401c1039540306000c0100031007a0300f40c25a45404041001c01c2c41060121100e40500003540003489106a10b64801c4854002500444441402c0c00f620714090003040702090f14105200e000800c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 326881061 1250 326879811 326879821
    0x150e0609091f1802040509011a0607020d03030203190f0504120f08060622080106090b09070503010605031e04060e010b0d08030a11160c0302090f13060b060913021908060307060305 79
    0x10341100f2200203540945450188005d0b2903055000c0c1036a4907a02180e41145101003042200c0b034010104040e401c0300c00d1020280c00a4401d90055070700c0501c0c00c000c15601c6121301480d804a40c06c0079203124a95680d40103100c02d00c000c601445140150f9031a0a0b00094800e1400030a1144090140c0d4040d54001c51300002400e851100004a02c0d4404040c82c2070b10ba44218041c080c2003240304010b042e03403610034440c20a081c103c2d4954814000d40c0c548a00c0c59190149c01c941031b40c0010f020b000d904d000d201c001c0729108071108503240218001d210101e41040303494503a500b180c40c028001c9104002031400c0d440003d0751041034035448903c10200085080c06140003003100d124904075010181015421041000807000075041600d000b03031110715071a0b60342c070004042d4001c1560580311100380d012036907000071a42d80000c0246800541428200241c030740c00718030409816441409030640100300002c0508201c2c204055800031890400118140030003c80c0e2a9030480c0074081c101034507400014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 326882311 1250 326881061 326881091
    0x301150309081c1a030105010303090e04020d020603040303020304060b0604081207060b0904050d020f070b0d090c0302131d0d0804141203011205150403020c060d150e0609091f 77
    0x70300030b1128845001c407400c01c109480310092441910b04001304030144803200c1581414400e050682e0b90544070520140d0920f0a0b03401020002842203074080261031945006071030b2040a980203a03ca91000341e00ca003070070b00c3c1440070303640881c80280c00f4910600041004000011f4411210505003403800da0343c00590030304401030035511801030f4100d081041840100100020944001c0a02d1350a445203000c030ba920a0703444010601c80c072901e909091000c0021004a9800006ca441c0710f01c920000481c2d40c0d602040340c107554136100303c0c0e20a070f03100f11030080c408415510303441c03c0d409000645194084c400340581414000f40c005080b200c2180390008840500f000320b0020324928546540d160740e500c039106100148120b100f11201e0103180c0ba00d0000c90301d4100680d000b41e900d034001c3c00f0010710900c00d200b220782040400c4e0200c1c1d43c488680c22180030920f03214801400f0244841c03101854000144449088094941b5405600124003a080f00701000644180302851040215401702408142 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 326883561 1250 326882311 326882317
    0x281e050913020a02060f1302090402060c031306200606060421061103040c0e04020a032405010305010b0f1509090c070605070e120c091605160f02010e06030115030908 73
    0x10501030344006983c11146800003665441000c10400011860fa00e040103100005d07103109000f5000b4040201150042c60703c0e002400c0c2d005444401c60f800d1a030300140c4145903000070352090300407407070964182c0b0aa00490714000c1258002c1c100a001e20f06181000c41c1c81d42c821071081d182c50405d20120307000b00d42052030012501c2504907109010f8854040401c1c0141d1f8806c2d1802c65003040003000c005400030844643c640300d650020000b80b6114070715100d2aa45a003051210302d4201d501e120020b202100d94814540a1409030000048440b40c3c04140440015284080780c812210003058994080d8000d00312400b0030400c0e160310900d61600400301455000c0c0050040099060030b0401070155480560054003c000315140c0c00341c01c0300c0c000da080c1c40c2c0c040c43ca40c55803c415103100146071049030847e00143d0358600d291051910001c1210b20031200303c40d00e42182c5004500c00010190b60740040c250070243c0c2c0c2100c0213490355241c654682003540c2004000c00c18503403070300c210b4810300c82e04200ba = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 326884811 1250 326883561 326883589
    0x40503040812041e030b06092a031f050d120e040218030c0406350604050303010618050a030204241e080312060111070803281e0509 58
    0x4440d040940d10140c2c40e5960440d00980100c60085425002041c0744480c10000b102d8203c6280300d1703141c980c0020700c240e0840003085400c00c02c03071015448008044641604d8000c502c1c07021a81d8490500442805601c035041001d081c0b200e504403010300095680c20081d02106034004010120301519070f0040e240703030781e0040240e40c1c0b0070320120340003071545d03070b20204190722582c100c0555070031750703000c0c400c002c11542507008403100b2010401180690720a441c1509040301c0e944c0d01d2400e40501c40080c854a48803088404607890340000c80104140d682100000d4140010958480e02c040d0500000c00c405009601c0042e208903102c4d4180305440c40c0b10700320031480341c20940c01d24190710f4483d070301c49040d0103014070750940c4583c0000d0b001035900f0002c000e540c10040204004111521070000440e15a586540e03024924007441c00000b03143e0200b00010a0700d422000c00c8030706203016992000c1d510366490344d0103005201060765480400d5078240341d046500041030400d5501d841501e00440c070212032140c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 326886061 1250 326884811 326884813
    0x901021c11150703150f09090c0503060903071202070b0d110c0d0509180105331903050108030c070b03090102040305030c0601090b1905060d09080703080114030d02070e0405030408 79
    0x1180b06081c155a12024400c0c103041d00c09200090700c0f08940654031606104200d5410b144070000c0c0406947c54114001141c011541e2110380303a15100003a050850940e80c20075039034000162a400c000c0a480d030003a41d90168005040c0781490b103031705054a80f0a03850013100261340c600303554901c3c01519058507009444503085902521002e14054190b47c0b1001002d84a00244050b04200a8450380554180e5002030030503020380c4180603040d1201e20b4403005400d100e541d406198000307801e4000180c4610b00205c1c1d00d480326140849030103004c480c2c042e001540107400030841c5000c080700c00206c0008a90050701c0c0c0359560358030914928024005c50300001c2c89030100040000d01c0c4940042d50506071541800108000c41c080c4042003510b4861200c1c0c110f400440b0741e41004a454005e0141c850300444210100d284039140e6164900c3d9404080d0460102d0b44040041c0030107040ba1140c0c000c9800e041d0010a041c0c84010310183d03076060544070380004401e100300003c0810506100b5a03006006901c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 326887311 1250 326886061 326886073
    0x90b0a1d1f0f0801091a04150806070504091b0f0804031407150f0e15090705040504080a02010e0313210203030406091802040e010e041a07020c040506060901021c11 72
    0x64010b05003040b11914000140d00b03c80086007604061140700000541000e01081c0c001900c8148800703031940d029040034000507a240000e100c1c0e0148000c1e4411080341c3e035042e0740c3d01c0c202840c02080303507802400b04041ca400c80c440c8241803a08641c6108a000c02810140ca05540700d107002c40355100c0e403d204941032480072601c6010044121700480d0340c202184004e01c10140c45501200c02c4600400009141d98010240f141c483c54540c02230a4200364018141c0f8600354907000464141c1d801500c003220150350018100c807c80da4284514010140010081c40c80d08940d2507548500800c0c030300901351495040c4107c034051440c103104d5402000e0740901500e031101d80d0765001070034190082c8958498007450001c2c0d5038460710070744220b4050301c07012a80c00d5171a9090001c842c42d51030001784201d44801d90840141507940e180440030f0310548841d4020128902d442007404107035400981418004e400521429034540e1700452505c1c0040c541c1c04690500d2101e207441260305021015907200300f40510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 326888561 1250 326887311 326887369
    0xd060609020705070503010b15070618080a1e0801090f0e060c040501080907030b041101180306020301080d0c0f03030e19030c140f0d0e0604180903090b0a1d 69
    0xe074014203003983c042e006441042d6665030515080c1c6016100311503014420030900900c098149000e01201401140d0000e44141c80241d10002c4071410b14082c0c90146022aa880c90070f6807010521050009000c40002c070400c0b54100070b01010018003810340c0007a1241000ca0907800940d00401a01840c00c046500740c1c20141c0016500e54400e02070907002840200c00150680c40c00280081101e5100410301010380da0750301ca03c055020407800300343c104a901c884541c1e04a02040c03109016600a102c0140e41b03500d040b5801d4540800d01c400401402942c90032440031441c04800c5480e01505800d003c07a851000c0004c950520104040342030409504441400c00e040c1e01210400400d031144070700080061980780c0702585d90003100b0700c0f6513059006030701989030503210f50a105041000078007498102501e8100079844403003040741408807130303a5a5403401c080c903500404500040c00d10100c000d14000900a00506200003c40120000703940100725940c1e42d00e400d0a2401001c00148805d02c40701c00d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 326889811 1250 326888561 326888579
    0x20303180306010602030c03070308040c08100f0507030e03070f0f08120405060106030203090a0201110f01020a020c0405101208030c0405041e0e030310120c0803030f0a0c08060609010503060d0606 86
    0x650600e403400303880303810000300714580000700700c404840c2c405000314209400f641e41204c503448014011142405084d000192414007004000c0d940031a10601281480c0c8410054040301c10042000080504080300f000e011200801110000340d00000301282c01e51807401c0042c1d0400e500000202080c00018250701c40c15441c505083c0a68400c1e010b5035041d036a2244101c2c00c1c0c0c041900e20f9005078001558500c01580140814003000b86000162240140b113185950b08a0f0044000c1c070b800341c0c1044001c1000c52400c0d200c0c01c3d5100390000c1a54844a0400003910030034408958001c02c01b40c00080480c04044070070007510300400004105124041004c05000d0b03004407036a0b11450350300e00300728412041100100580f4840c408210110420b246090704a8a61202c1800300782c3e11269550170119a80d030007880114854610a151840d09082c0f0660481c1110401c03034441c41009218010305c90140d907000c04490403401e00b4a4080e480780c95400000d038030b081205a004103280e141400002d0b107429 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 326891061 1250 326889811 326889847
    0xc05071b0b0a18290d09060218011b03050a080702010b030d110d0c12030c0c05010219110a03020c0d1b090f0605030718050408070c030813061805010f02010207020303 73
    0x82c6542c2074541d9155140240c0100500244c00c420f041c101d540c101306034401e0100c0c042d0048141405010503079000d90346480c030881e48442029014503089509120707495820040511701400c08991240c044116902e0040990240b0750400d0700b0000e0400c00300351800e100350007040780c0305401016503910303081c0600090005a910200d50100e400b640e90408038560081b29031208440e000281d140b9110003454044000b00b60205069062000c0d9500140210710248003400b03202109035441c1004e914110805850f6840c0c416401680b030344207010080000758081444a448041583d042203002e50b5450004034001a040108407021080c000000340354005410a19050b201707100108a956218030525403582c0f141c2c0112500085171b00302d148000713080c3d9444240d219000da52954140000f0713551305c0503221a19441580c060700d0104031100c00c01c00da035455000520442c20a03419030030480c444019407070594490030341070084181c1150b5009000b034040300c0d00242e004090302e5882c0c0c2031100b5140c00741 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 326892311 1250 326891061 326891087
    0x1c0305010603050604051015050708120a050603032814070b061e030a230d08010303030b2b020604090e0106081009031202070c09060b0304150c05071b0b0a 68
    0x7400d00001c40c1071418181b081320702403205600f034203040c0c900303090802c0d60300e6000b50b00c0402049810089800400c0e52038010709540000e02c48400d52605001c0404000d0b90400b9041c50310a4100300b009550444803000e46414502c0d101070307203c640058880080d0f5200100424240c04148005501d60801405100c1c5612400d81254460070007642c0c01008205d1a0030810310b43d0701070b40042c0104000c2440e0f0340554824440201139a01001c5094a1603800c01c142c51420b003000c5540381d03005000701901409407075400d420650f0008480c0300a83d05104900ad0710040c24008014012000e0080d0f4440401311000317010f0201050011040f4100d8040c000c000324454203102e4010304884c60b07506000f40c090040d0f2190190307203600418000100800c000d40c4030b01400c0b146041e28500001e203100c1c40d800703030300000d00080181c3c039100c2c6018102503004c101600d41c1d500c0d025152141440c0d8558200060310791098008000f03155145c0d901041078200c0f4130705e4010114000c400718684800c60ba20402d01c0ea44d007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 326893561 1250 326892311 326892317
    0x504020609060315210d050f2208070e0f0720010e070e06060f04051c0b1311030703051c031d16060212040b070312050103080919050607141c03050106 66
    0x8030500f410905c1001e42c50840040540c1c0040f44500c1c2241e02c62405400c0c1c00c401030148518040d1400c036080d44040700001c140944480c007910401400d02d041c42003000070030103a66014190324060b201040c80d5100141042c090001d12003c019103806004007010354501060005c02907010103145690382c45100384281007210400c040010042e0a0040030744090403040e440311800c00d400c14080080750203548100300c6100c0c040d48041800308882d20085801440c3c0556840c46107100c0e17052844601c61480c00c114001e500c00d21041001590024542201004580c0340c0d44100c4064a0100c0c0a0000801490702064041000c044101e50108a4402ca041da1014111403286c0da104c042c1d032075000ca5510190500801c1c07208005441c03030500104000c034070a2905030b034041d052404400072213034207800a540180c00800d03003e605081c40ca01030446100d2804252401034a00000210a0700c60303114024000e031003580e0600000b420401c0040c26000c1c3c0c0c2c3c40603c7d20003140450050003000b0920802e400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 326894811 1250 326893561 326893579
    0x8090a170306150f0405010c0f0b0c0901091e140a0e0103050105070e0a03030f2001020307030b0316080303011a190215010905010e0420060703020a0c090204180504020609060315 78
    0x1403443c89100311441d403075100d09020304151501005648440c44000300351102e60175054a003000034907c0e988144a6440c00c1e0141e510340850000060040066400c000042d414141a40b502c0104540c8242c0407038800c2010140c0b41000c00c0e01013400d1003079642c410218010844008000c000341900f05034070139001540c551000c868294104202d00d400c03888054007040a01507981100d500c1030110418945c00100103030810030461101e00c0c22079204459490000340e0b1a5420101c515041c040c514408800c860034000300c5007055080c903180e12040c403175142500c41c6510740521004d8460191000804d03050038800d2480c5030010041d40750004200390841c111960300000c6411800352003500e042e110400c0c980c4502c1c0c0e40388d50b94070710403900070612450510b0300882c41100f2680d5500c01800200d110394068900e60070249014000d5082170f4004006003401031105000c00303050032409551003400c000021800741c42e94008242e00c0d1141401260f0003a03000420003000340000d0b24440021801640c104036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 326896061 1250 326894811 326894839
    0xb09030d1a03151306050601020307081b0601080d0905091504051f05060f04090506010915020a0b0903090907051e030f2a0306100e06130f080a110108090a170306 71
    0x340f103038125000f040c03a02c2c000240901003071040c2e0086074080e02c1801142c0ca0610661603401140c2c200c41402c801c20714003c07806030106401404414018181400186500000c03801c1c05070068040d07010721800380982a0024020141c2020343d00f0140c04003070070800284c24500004c40c80da20401da11021740c1140c0000014060802000311090342181580d9107042c01e051456050150030040c10b40d134100a0b1154010a00304140080040b010002e1b40052003803401c1031030500e5005100908030240d581003400348840316120750850301d61020b4649882c56481d2003803808010941203225503001154400700170065906d059070740795400348204040c0c401c00c100404c03400700304060192410003558241400802c4090409200c40310040b8400c2c18180030000310000071030b400d500105820082076a480d0000c1103662589214030000d451180080c189900203600d80b480c211245424144c100900e540c00140302034824408000c90580c00401c900c04000308503940c9500d5041510810300c80c0c0d440c0000e8803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 326897311 1250 326896061 326896093
    0x90f14070f0203041401051210050f0d170a0512130201200c1e0d06020a030507080403050a0f200a05010b06040509040209090a0803040c08120702030a0b09030d1a03 72
    0x10034041d02a500452800d0b042010040007042d60207100c03814844140640054a0b200c1c0400500c5824140a65840589014100055810320002c168010f031188950000420007804e202c1820b5200c00c00042d13503e0190366003c483e030380b050340e00741d0880e12a403070203101c2c1e495000243d02c51054001d83e903026481c00c2c0000c0300d4001c030f1415020802242d100c4440d510240c10203145202181801403060441107088501045250350340c14003c844c400e900181400c0301035054802c80d90400ca06290800443c503059802520502c0b4a808040030f0003014a005401740b4411180e00010003500c2060600c0c140c64590480d13590b009084d01103c0c2c03542488803224003030a01d00290340450300020301d81081a100c40c0c00303119421401420f034010074000c00b80c001d80410940e000541c011407281222200300340c901000b160800351203c09409004030100910310159400084c110f54041d00848102016202c4e000d0903840d61107a944a10f194905181d40c904848201344005030101505406442c4000c0c0a10f40d41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 326898561 1250 326897311 326897327
    0x5060423030a061e0c05090f010203040906030605011706060102030d0e07210b07021b01031107080a09031101030605010c020603131b030b1807180204050603180d080f1f090f1407 78
    0x502c0000c006010600300c910300354020088c03005042c010f0303a203459122010081550b92907001550100e031283c00401100c1c0620000b038200b80f0b050b01c05032006050420001b502c030b104012060304010340350b410035425070748140503030300c014420511031140e101c0402050000d000100001501c81240070000030b0722050002c0350303070314090003640d1001a030307811030030015030003445002c5403c070030414184081c0c0001502103004009601c00758944500301e525600d803907040c43c0c211400c2c6a04040c1803405c200300507604002d102e1400c035412039103d6200e40d602060500d03491050b0784040c1030313030181813205410072444c505404140e900420741c3c03500c580c0d11001041c4800b0f544d01440603541d4060301003009640840c400103510105001c40140c9030541d680001003458000380c440c1200d0f0841c044511440c044104800c0381d107060242001e078520f141c20030030489841e07001011000c1c080407031002c042650700b031089403002508820404104080721030007a50010140c91440c42079402c40c082c00b003070203203015a0740c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 326899811 1250 326898561 326898581
    0xe030a0209010501120e1e1b0d030c051c031e11040501030c02070801060b18010e01120507030e0303040506040210110a03030c0309050f0a110a05060423030a061e 71
    0x40d141c650b46000011907151080507122000f05590b200b18015200090000c01d139110215000707000c03450030085010742803451a05154542d001c1d45092407080c1c0e1910205280102c1e0541401001c0d4143c1c1e04100e8103047d10711000d070040c0645420406a40e6806030311044e1034120302ea00714096200b02c0344050080300d0f5a1100300d03190301d03010f010401043d0b10a802c605580720003031041c0c1d0f00c5190f80340401d9094aa19401c440040a00410101845030451150708510303002443d05610030f1104c4070000e0030026548400e40c14450711180082c521a011780c00640300d007000e400444c1e035207180605155840f0541514224032801401e4a0300b0b80c0148500c041050f402c9044018050f0b00e542a0390640060940e550080245600e400f004804907809110382c1044200d500d016090603102850802d03290750382c50301664810701c224070051060b030700c49400b510103907a403010005846107101c100c1d02c103140c048860b66039414802c0c80e0084003001506e0300000c015494410016510500c1e00d117201d0251209590 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 326901061 1250 326899811 326899819
    0x906180106120210030603230d090b0313110312070c0506032203093b01080a0204020d1107051b0405040f031b140f06100807050904030306150e010e030a02 68
    0x802d16001d0318011481e500c2d0b01005060002d01156669100c0b100329400c00c581260045d110f010001d4094001e000f0703811040b03000d1500945d5142000c000740306600000e0424a00c030728480c03142d03408003c0301d030340c5000e4801c40060842c1c1005c800b40c50795a060364820081181e080f180e10400142d80d041c10820f49019288142c00d500c880d24412106502c80601c040342542080100d410000345c1244041c05400104507424220b8006880c00303045454002a200340e5071030100807540100b0541c10301240c030020180d41190056698505a00228080c0c0000036640440c0e2a00150800400000088462240014040700c8540c00040410401100c03021a0050300004440243e00e000034400e000303015207080d0040001c41034070840d4464081030001100404043c1d0300ca82158095800200203140d80504c43c1000c0d80800b5007031520f01500c500c200c2c400d07140903115150103d41090300a0700b1160140c01e05445015401c03000101c01003402d0114a0314501055114204204a0034007080462006030068 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 326902311 1250 326901061 326901089
    0x1605090f0f04080403120e10020a080a11460f2d0305090406050a150e1f030c1d0d020f0301113001061b0215030906180106 54
    0x950301c0d01c0740400a0046540390010800400050998080c82e41c0c1d640840d9501c64401c42900c0510013440000b113410019035011000ea280010004000c540c0340747d407a440d0901407104c4e600405450002c407500c4a9100740c080e90b4900041a003985001700d40365100c0c0709540001e086002e282441140f400a020344204c90039441040801d120300c446002d420000d40c0c1d2565420244842038100c81c5144d40120009280010741c0d04541c078060080c0400b5002c1207e01c81c0481d4039121511005c0c0501034941400e0104104483e2481c3c1d650095100c01e0340c00c0b2003503424801da0071140c01001040a6283d11010410400c0c0c5c8403600741841045000d080d0020704940c50070f0949400700701011903074180c00c56040d925494591030145983c000360610180411443c1041e20f03800200f0981d042000380750b00314003604400100503044d8800000e41c9103030840b000844507084c160001c15450000003c501000c03040c000240101000d00080321440f901545d851840705100d0701c0145800d9a006105c0e01040240c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 326903561 1250 326902311 326902321
    0x7080f0112020607050610050301060801180f060b06030702010608010f02030919060b06040e0a060b07020d0b0c04050901030b07030b01050c030913060906030302060906070509150304020102010f06081605090f 91
    0x11118001d141c80c00186014144059503030707982d16240c81201c40c2000201140010840d60800340a141c002d403503404028404040c03c1e880d0141e410700c1200b0003a2443c0c0520207240b0a100b00c551041400d00000b6003003603a680b40122019000e084144112000c6600e448102894000030b8820b89014150441c042c0c42c4520042e0395030441001f200700300742c8034155a00c00c0039105075500300081c002800f102022401e40d1418500c11002c40c0e0f0360394421302031580104110401070381c8804000709225401903147d49640c40d05503048c00d0500071600701307940216a900010090064981c4013a01c501069a02445140740b001d00441d040e00400e0030711105680248401c1da00ca2900349031204501c5010030740095801c0d56100e00c08184c0b94980d0050300581c2051091203110042031000d80c0d40000b5905006280450350030100f01038460000074401441404400b046c2160310030740004c64280300b499024084980c48242168440300c60f0b000d00c2c800e50504120000307041c00e140501034402c409003103a00c021540d40c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 326904811 1250 326903561 326903579
    0x10f0302060a12060f062601030b10030b07080411010f080a0b0d02130e150417070302100510050a060309080d09030c0f1104050105060705060105060919120b07080f01 73
    0x3081e0b030000180a0307200c11081c01c408541c07066100805001c00c43e011554944007014000e01c5030300c80411000140207150340501d50080f00c11a044a0b4800129000e82d41c41c4420015450a140c10040c03a20359407005110403940c1c45959280568001c000000e07e031b1030000010b40d4160a50040580801d200200081c122032031603010341c0034910050040107920031386500260882c0c0c542803146603410380c8c2c1c084170341c404801003242078100c0e106000d002442d805c0a44889062040c0140c800107102000079000c400c2620910005081c140c6a44051000d401c1200c1c1d0001c03499954080c09016808044000921911902840e2038450f00988030900c0c141b00107030001d01a01c841e91040d424000190040d1000459001e103200c100f90085111000f8001d508003003005882c4180d210a00c91a02445094041080403e8080c1190011240f959a42c0450408680c2e16403d171030b01d0b5012607004040000356061010380c4852600d00c1458a5202599560350658000c60207417000888a04d40000500100395 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 326906061 1250 326904811 326904817
    0x604030e0301090506040803010614030408040506070314070507030b0a1104140105070218060108060406150c0c0522050603031908070203120c13080d02211b1c08010f030206 76
    0xc8040c001180d140c106854181c5810340a90b01116400000001001095070003580e66907840c082a1500b40365040c00d45a850450003140282d40c461900007910f07071b04050168480d03419031160005001c0e1640d81074103106444e010288400c0e10284071600001c1c0c51200740744595682c12608605d041d0404e400d0814a8480c00c00105401d41805404c20800015907038521052840740004450b00e10980b404070001007004401a080714051410b000341841640c20800901901e0452485e00400141c681d0501c02925a429132086412544041e0411590b150403803d0301c08082401c03106212a4840d00180341c0d0b00c1c801d100c01c014084c00c0c201c035001402c0b4415485940c014400d441264209100e5801c6a04031040645540702c2d20704d0005000415030427032014203001040300c0800b5221f04000b41c0c1c0041d45a05284560500480301c0f183c40080886020381582d20762910024944540e817000800560b44038803519070791404140460100345a94410300d00c282c1a907540400302200315141d40e0a00403950 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 326907311 1250 326906061 326906087
    0xe030304120f05121b010e1515010c12030b0a0e090705060309030c0304150e0a0b0d090f0b01120c09020703140d0f150512030c19021504030615060c0203060403 70
    0x200a040740c1840d6104040e015009140d05c0c5180d91000300c18889015003195013140c030314007c2d41c004000c800125121400c0c2c9a5000180300000a4040c13139a40c012514001c8150000b481301040c1c800d00c03102c1a901d580704000340b02e41034038281103403915a420860002c208590103200c82c2c0c0305c99014401414484051608100720304100c1e410540c010000a04580094011110f0083c03400d6a0200c07150b8072034805c8800340422f40d000c10710726087c21010b01c2188900080045a5500d0311141380c00c0202c0c80d60465a220f4000ca000c100c0355854034608800e0180580e02030741c070240d45090118610882d40700b180c07501f03541612000e80c0a0915201c800d81504041d02c41c50701c6a507548401c54600716180a81c010000040360340501c0c031410a410021444516206800c250303000740840d0340340030300000e100390010b002e540c10807500240d81d00c009003110605000c2c007860004041000020008a900a0070305a075454444a03d016200d000840340246c4840d4065815804000801c0109026aa104140c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 326908561 1250 326907311 326907313
    0x6030a060e03040b04030f20010f231305010801060f1d010c0b160f030209010e0d0c1a030601030b010302090310110906040b03040213090f1202101b0e030304120f05 72
    0x201c0c3e5134480c0d0a400e508654400d6a076145524150340030403e2078a107251801007107442843c580c04400000904a1504600b900141700c89541d030460894a0310011314624480322520740d0351250307500c400703e480e01c00c2481a140421080d40002c25003a000d0303501c02c0380600040ea900001e0004583d001c040144080954506020441c03204501048191440078440c000b02c00401e070340c154240000400001680c0c0b02c40013051720500490715160307882011400e0381d0707408072001e25580000d418490489021540082d503840d0820b00c00e42c055601c1040074501c50b8000b62820010b040080c8015000c2e8420010520b91540255003c4501d40d40e1542c40640c0c0c003421458047e08092640b03020841036405900b104250007004000c02c030071490441402241d1a0400300301b400802e03041d03991403107000440c042c001c01c10007614144801e034600c20484011210f00e408400d000c8001032040c0c040b00a501074500b1400541100804807107800c001089400311340d58100809a0f940711600d5201d1007983c060780031501c0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 326909811 1250 326908561 326908567
    0xf12070b010506040302010c0318051305040b010e16051810020609071d060d060605040609090212070f03020603071106040b0f07030c020d0e04090204051e070903030f03020c0f070807081506030a060e03 88
    0x35844450cc58010365402610018240c01c0034100719850f650140e03c004003030000c2c0070401465207071240030b015151f001400c006484001502d4078078448a03041342544d070401500c5464010710780d07000a5403030203000200c003565055038882015503503a1021842401020f05803034007140f1070f401d00b19a0a0f0000e0b000303a0b000250380e6241c40c0000e041e1051903005007405912082d0351029032030a18a41c0f44030183e10742c01081980c0c0340102c0007045440c58440070f845120088002484136001d4410600e082019009456081c9000d29085007101e9060b03413000359030101400096084c038000d100b10003802d04180c008140090844500700d48045800004030703045500d908203c1c006890701c0c0900b0b400350700c6840441d07066651401c1c034a440304000502e501c2c20003204e507070304101294018800080d18070041c03901503910000d6080d02031510441c1d8200352410701c40e620300001d5000012840034265401501078920404080c00b9038050390b00240e6a0f66899041720340a000050781c5035004d900c080740310001b1340f42 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 326911061 1250 326909811 326909819
    0xc0203162303160b070c2a0902040302090105040c11010f060911090307140102030c120307020c0613060818100b01181a0c010b0603070c0303050604091509050f12070b010506040302010c0318 83
    0x96404c0c80c1380101136a0074520041d1400c1f02c60840f03004060803a0460442c00d20340744d500007030300d00041031251a020780d0f0f890004040d01c9100d90640e041342c001503070080c000c0c82c0c80c00082000030010f82c07180650300380c0380555142c1c1d2920940202c4029a10083c014140700d13040009000300180100d4000c0c0c198071007040064039180062007540c4200040f440f07240c0d141d00c2c08100107805e042d0b948940500c110f204000c144043c070400c408a40590300d291401c0380030b0341d0b20107c0c4004560186e040a88081c801c1e41c00c801d0f90395400740c101901201c401c4e07869a469a500c2014a81103008a000303c0d00002410b03070080c0040031068000c3c0100000c1b0702d0010032003000d00d2010030070a52068641700001030a00001c0d009164141c050144c1000382518100501341203501c41d0340381e0b2516040c001c0c1c8841c3d1540625000d0080c1080703100b140004000030744490a041c0502c540300c80e8006401224000c04610000443e8542001514201c07034060b101d0440c28034890764200c405401c4403100c0c121440d660301000c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 326912311 1250 326911061 326911073
    0xa240305071e032f0d0504020418050a020a151b020a0f08100e03160f15050a02120f0c0f0a0c1203090303140105030c040c0203162303160b070c 63
    0x100042e68030000b522008480316443d08003603c0c3e4840400365120382c1c00b500a4000c1404a481801c0c95040018454903144005006040b111800c0e04644a500c0a954203000d0003143d000c11050ac212a1020300b00d41e6910481302c0380400322462804184641d013008503807100c800b103100000d44018040030806856181409142100d600442607950040f4604001420b05104034155150024002c40c1402c6091031458100284140e0040007001c0f100040d0042040c14040e1440c80301e501c102c01d000c18600b10054800030340102c0060700d2b28a030101c006c0f440c007048181c1c405000d000d80140032840d10103070b1121492a41e208075481002c000d103c40b1000042040c02c0103001c510011658003007469036082c20000c00b03039030040e9148186669000c004000e203607000140900b044000f5103000c1001d0a10401c2a410b501551080080140f0480c803840100304c07805000c0064403180364860401440e00c640440d9a03409491002e03050a010f4007104030214082180c540d601c81d07118074080307071240343e2540d0b24 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 326913561 1250 326912311 326912357
    0x301140f04020f0c0d0801050d0206070203030d06060e0414040f031407081c2a0f020c040906090b09150103020411040819120203120a05100b04030b04020a24030507 72
    0x5850f041c04089007580100100703004000b0342130041c2c505145a035042c0800240030b80c03c140e100910820b00092030004540381807041d2000496080b4007041480da8513480a0501c40c041000320b4440e5103002c821149000190340b40902681e04215621035140440d6410341d100f680030314020745021814042c040002d0240c00041c042c2c40d01ca18500042d110b2400320349026030726060881c450300018003c000e0024446500c1714640c028051624600110124806a00302201000815006170901c00c0c800c00344000ca0300440019880741c40910815035034000100c0c6c9503000c82a2031400200e104004001514003500482141810380044034a03250342e0300c44d00b80c5001134100d41e07444500e050040c80c40c2031200030200c0c0010300f2081d0003e10f14080c0350101000c2c02d10f400808050015507101d010400050103506201d0280200d880720951711602d9050140400100300c42c103d10440000a001c160b802403050400306896140c4c403114808030508609501400c0010b160350304104803200c402100107071035010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 326914811 1250 326913561 326913577
    0x3050708210f040e19180305190306090e0a0c0e06210102040510081e0601050706090611210c0913050a1401120311060618070c02030703030f02010b01140301140f0402 73
    0x20b0001403010340003003c170070f5070a0080114682140c055071400465081000c130b58003042150f00004024501c500c003900208010303081028541d1500e8043c125000000486209031070207141e4581c1c0040d81e0b06691107d000303040f91050381100c0200c0300540e4040c209140c90b15a600c421001504040c0c540d0301040102810a44034000110400113100010b8168001e81c08414a41c00b4041c00501e441000138109200b5030744002c1040c0d940f01c805030140202d9501c6800d2500c20955115aa035901002460401400c1038000c200a014600401c99400e200c07030440d10b101c48041c2200d00302d00510fa580100400000f8101a80c6a0f220303140080c2d61040b42c4035030342c003030b0141c00400b00d854080c03800d0091950080380b1031842c056100c04140400c55852080072181500091001c1516540f258422200a00c0c00c8500030340510403004040b041507004184510300030002c1d4000c00890221400454952038800440404d60800700b0050080200d880e80c60030240c180500b90345098501000803400f00d0f403180b0340e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 326916061 1250 326914811 326914831
    0x4051f1113090e0714060d06031203020c0610030506010608041a0c0c01111201150504030501020a051b030304031e0905060c0c0a17030324030f010603050708210f040e 73
    0x702408500d2203441190301024003c40109001800c001c0810b81c200d103441c014910a80f00414103056210b250b40042010f0b40d8040d0301003604130038400014003c4c2d0400b18442c0402d001d9400003543d8482d1800d0804201d0b5003010048c00c8a92801c481551260f0001d0302c1039851500c00c2d111400c0480c001c1e0600c600445112001036643c5070700c1119282100e6000e40c41d9403a5840c2000000c0010079484c0003181521000c541c0e02d0301d81d0144100698481c4240e600003000c2e5400480e4038082c3c0ea0300400070f0600e030740c00480c00006441c03048040948030304c0111001404126000713001ba048280300242001484001e081a0824035194130000385160811460495254400d080b0b282950030714040715401048010664490187d81ea40302ca601c90000412101c00c640300748045d0500c1007010401d44072400c1c0d01506582d5640c8422000502030030140c00107650382c2c071455800058111000411140034205510706113009010740006220b80d0780400092100c51105100200c2e040304003a81d106c2c02950010303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 326917311 1250 326916061 326916097
    0xa08070e0d03021e01330f030b01050906040207020315070207050a09060305010c02060106020709020309010216060515062a0709060f170304060e061c050c0c01050a0504051f11 77
    0x19100c00040c0d0414400d03c1c02c0c1c2d061078032000280a5901c1e1007044000400103403000540c1c2c22030b5080a6946e9980800095034101e00d000050082007050070341a9030095604141d0742d60789209000591168a100030740690200c1084d0b80c2d45045101360700d80101883c0305998009036507034002856912990000d08055035500001c008016092092020403910f90001e441590b14200029441d0320241c880c40c01c0450700000010310001c030a604944403c40e964014444424440c14241c1c010710084440e80c14680c40107480300d0b22450244280c030008016000348000300414070044e044840310086075807a4038130454002043d28403141c003030500a0324044901203202441c08500d001024040501c00d0125002004140000c41d403000132202d12240035240d947d6994440320308041000d0302c145000b800f85141138240310410709948014081c401ca508020f1000d0b444108042c403c449080e90b00030520307030080c01c00903405881a50701842c581703c2c0c414000341741c00e12140c54039480c0d4451b001c0728100c09958 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 326918561 1250 326917311 326917333
    0xa0e011d070503010603030906120b10050406080601030b06090d02040f09080a090f050618031e01050a06060503101505160b061c12030e030c10090b010e07050a08070e0d0302 76
    0x4101c61001018220001d00109145490240400341c0500490003001070141d080c0300b10b10174a030000d6499080252030074a0000c0c00d100010203030b4010b0701030040010307100c1010a000358407a01800b10940c8000340268540308005c0204140c40800040803030700107840f220207000100483c80f402c10403034000c0c140190f850a005030000d14003001034204800e2201040c030244030341d854090a4613882544440c0c501e02003900040028039052980310300c42c0302414214800c286034001900801c1c0281c40c5005c1c1030003016154a0203541d81e0104680007601c031080345100300880740d80351130096035412460804c03070728040c09141034810140015200b07a03007001c081c001303102040c14110310420f801c00c8005000c4001c0e62065482c507911825440c1c4003010113403200d0944019138018030448600d00c0f8407000b101c0c49004904400f00107401204420307142d200c10740c00002204200c1c150031902c0b54500c0e03a60585031a82c0e00b1001da42c3d141c4003400d03500c10052164508a99034441c0001d44800758000d40041000b0290 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 326919811 1250 326918561 326918563
    0x7031401050702061509060a031203060e10080312220503030603150405190212010c02011401060f0c080304110402030a0212220b090a050601230303041406030a0e011d 73
    0x241120046511001c208034914520380611030b05d130039040751200620784420000414054480c2c2010701784c00610030403207065a415a022404880701c0941290302682d130381484a100503414822400310303070800c00800040d01c03450300800380d0043c0d00e841e500c0060940c3d90042d0030751805c401070403a0f40c1c1e071000007071120910f410881a01a03584400780c210442c6000e560b0181c85034440c95002d1401c034a85000c3d94115038450b000402c0c030044a4000308408995050001d001e04824070300e40103280782443c00070a00f103102d01d000100c2d050030750b2110f007800341440e50b03100c6d4246d1008205440049459100e1412a07440b0f00045000e162400d2001d61180080d60313070100b14036400383c00e28441440076440500300c44058607907100c41c980c008641c880d03150f68071811682408c0801200404a0190100125151554850f40142d4070203d4414400745500c0e201450b80d01c2c42240030f508a00412648100310740d281c00320045038001461100854201501e4004a003901c410350001c0e1003a035407a65011001d0302c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 326921061 1250 326919811 326919821
    0xc090608010c05222102040e0c0303071709040c05030f1003051c03110a08100617010e04020102010f090c090f05040f020f01050c0a15241401020f07031401 68
    0x50400800668290002c05011840f54100100da070062070b44181c100002003601410040c88508041003c1200c0500c1410f180b142c0d8402c22880b85142c110041082e62000031080040368003d001945800016200da10a030703400150981030781641084002d090b6225400381000c50251500c8450700c0c1c0c10301544825000f400184001184501018100049180080c80220412000c2600000c21003050000c402138840f02c0d030140503015002130910840341d4002d45451040c031031001042c82d000d8487d41300f00c404000c012450090050300b440184507542001002d2900f01e481400001800d81b114142c25040d5801c1d00c0d01a2890000c0180411009695001e10454960704440c1003041d4541036032415550001000b0280c02038190015000031079003d5001c60f000780d00340000b1103607001154504103800c583c6c51004c03208240d0414a13150a003142803108201b420b0420115604840c0c00c02c03507016410317450a10014110311610000171410581401010051801031200451006003010650b007592 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 326922311 1250 326921061 326921069
    0x3190305190f0c021512040c06030b180a051e040b060a0807030206120c040e0112030323070e060f0c0102190801030218090a120206060301050a052701180c0906 70
    0x21941040e4406042d07407043d40707010159811100340c43c1d02c045440e1100b03054011600c900000b8a1000d0500041c0000000d022086801035601800041e002409019400344d070a1022800b204100d00070856003d61504250750220002d040724580344054081002c0000003918103442900080d01800002d04251640402034180e0f6401402030743e10b19400f00700c40c1e02c80c540040324007070007280105a0040c00034003100c00822441c2c401b0340c1c2035615800a032117410110001140402d14002180356a50b241c4041c0b070b200c2c2c4010312080045903695041c1564107240480d40982d010034104115a40f101c0c40c84302400d1300b00743c1d0500058480071440c44c1d4011301c440380601c010a104e5518010030050741da901c00a01c5c051101c1c0c1400e50381d138954650040c88c1005800000f001c0b40620018141000e60001d011441703044120000c0c80261030745044031044504c1590f0725182c8101804124002c0e1020880301070064214000000300714a24221009203c0d1103513008503104000503400b00070700601c5004110141c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 326923561 1250 326922311 326922317
    0xf14070503061b0c160803030702010f060b09040207110a08150105030102180616050a062a050f070c08010e061b0f0a03091a07031b03090f02010e0319030519 69
    0x26040c04203403012200c082c00e40c840c41c0b0040000c3c0d000c1910405004c02040202209080382c58192244c20321b68480d0021520100190300e05020440004158011802182e007170015840c40d1a81020900c8042c1d400782034207030380091103191450705c01d85a40d0054401458180c1c050110039140003051510200183c2c000d5101c1d03070042c08041c40c034400d00d0743c910540788002c84120343c2e1440c0e10b107041c20b0102c0600070080d2042c05400090710a129481d000040105079218101c40740e8456a0301c498002c0602c00c0c5583c001031410310510016403142c0c00100f010300c0c0201009140300e40d071000110f094941c81c241088117a046070050200b654000e03c09909e1616040c2e826505007a42540350020b140241d2041c4002c040d21403009d207040c08100420040c001d20840c01c20307485840d280038050003810410400061b503900f000c09001525200b0711420301065400030001000b000150011181d1710034604140ba49801114441c1814030203100b0b80a80ca0f511940b40c02c0e4980704110240034900120b03260744018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 326924811 1250 326923561 326923573
    0xc030c0503041505060135090f060403080604060503031315020312060f0406092405010903030c080309070b040305152d04030e040e0c15090d080a020a0f14070503 71
    0x141c0a0b1010308403400f1400d00000d15603181c000403564124225104008920132101d070360344000c2004100c20040b40703450f64415858641d6031540b591440156500c00c000c0d000600401e0019210707226540d0071440041c00464519200c0001a081da88862003511810a040340d0401070000c00e40b58201a11440740080d5003410007140c4484500e19000708036034458030700c0940a050b582da85501c00809881601d50401112801100c1084110450685030711f00021200c00095a50b10a600035000d8030f50640e51601d0301c001660700c1281d0741d0030141414000c6d00940c035012072050080707000b0700b00650180005100d4202032000c841080200913100180b40e0f2840108503d04d8802180c2d003071003400002644d120199994141110045509548264054200404103042641c00608100e040c40103e80800c2044400c0c100b80803140714840c0c400390013140483c080c0c00800c510b800905809106d80c01901d01c0b2240a03600c80045c03040710601201c1d00461401000c01820040100345c024001c190001c0031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 326926061 1250 326924811 326924813
    0x30105010609030c140d0609050c0111010203070504050d060b0909030406030b090f060105070609120207030605180c0607062003040b070903170a0311030c0c1203010f1503020912010c030c050304 85
    0x4d08460180101c02481c1c0c003a0034180b440380c4440e80c02030b40c480d030005410401c0c2089407801d10348800038250803600252505510014040044c42141d000741d90b20b0b03e640d450240340c801071045000040d04140d64250780e88070448190349800c1840382c85000020041c503611410810094111a81c2e0348582d40900c038140304100114081e6a012074122400b400c01c1601c07454141762000180240c900018200d4891405504040d500010701d0b000352071244d0014401d60b500c00c0c2c42d226044e9190f0281482c5603024590380966410003500800d00c541c05164045804031364012011100400154441030721000007081205100b4000076103a0820308034944008800d1842c0c40d0040b41e0b4070001d00c03132030350400001075007001140654800c3c14840c0c40c44042c0ea840785840084c0000e01d8010100614050041c542c0d0703508880001000c0b681603c0c400a2031150303107410100c1d034040c000f100c2900c40c0149542000710303041d41c2e55a1200061680c0c0031000205aa80c16071100909452800b10080e00788202481480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 326927311 1250 326926061 326926073
    0x19060501090b0714070e090c040e1209010c120c12020a0b0a02090d0f0b06120a050601262a010905060f03090102250c0b0c0d030e0705030d03020903010501060903 71
    0x1400ca41c94605600d858603801c4c01c0410b8101000c406030f01c683d00c10100b00155100141081c60f1003201280e00352a40d542c00398043c4802c0e18100c0a214045800c14030702560380d00040d1014014060042c03400c442040c0717203076451031103128000d43c02c6000f00b100f188048040109074a040b003040352152000e07005100d019916172012043c0a8078504119401160003412a02c456a1b40d00100350080d285ea540c00100d41030825841000741c0d0907901964400c40c0c81c166084000401560f0707554420b005000c1a03203413520455140072190f281481081c1e85206c1c200320312104005422500000507102e014403e5203442240b0304120b03460280c1d043c0201010100900e680d1041030b03170000304507818420790f2076448141090092142041e00c5800344070640c005c1c1c2d00101d40c0b0418003e035074030038030050100540b5000c08a03554000e800c200c0c009c42c2d2103081c064940ea8401e03000b011055441d00e0490b1640c945402c006810a1050550343d00002c0d804100c4000c646000d02609004000d00c1c00c14540d82c0382140c55603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 326928561 1250 326927311 326927327
    0x60a03030f03091e060f0e060108030406080601030b09070e010f08010b0d0e07030c0f080705010201142202210705121c23210f0a0c0512010e19060501 66
    0x200040c5075583c1400014800d80300d0340311003040000c500020003c0d5891520400800280408070340c1d0034a882d03a12502e5040000e015416201108010b40c100341c82c1c04012100c204009100301c2c10107450f101c20b09020b451f800402400751304503842d4024001c030b00c840010483c03000500d80c9000c100ba28001000010580380445580141f2140b02140c3d00d084031115903d030401a610041010702c0c4010000b41d82c2c0c07802c003944815034015005071106955100c004a00f078412804075541160120001b040400700002d1842c0c920455072601070803c400540c0000d4010544400c8842043e0400714200c0e41c130840901400010345412511070603142180d141d010340e9400031540f003085200e0b41c3d0781d07852065401045280c00d02034041c243d041c6074420407003141d18980c00c0113100c0d04100b1070f1800f90801c811510381c0d006200da1a2500b46001a559040c0a4001340040758410300c14080104a02070600d000308030558060148480ba902e03560030601e40c50541c410b40c2c0034090100d41d18012080c00942e86c02684 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 326929811 1250 326928561 326928587
    0x4150b0906092d0108071802070512090f040c020606010e0d0503030417040b16060b0303030f0c0307050408060c03010f1a07121202070f021e0f040903180914060a0303 73
    0x2541540494608951680101002c900f800c03004004000141110000407141d0a03103000c1081d09a010011410000c02e0703000d41034000f4010380104007181a070b0110702000d84046100100450030a1100c44003107012a8154100100141c11402c00c000e00f84d604035082c80180081550004104500c1d610b5403522800090002442c603020141c000c01194130913026980503220400190b0303503500051492081c0808030b09003c903601405c0c0842200749d854044142d81c41401181d000d42015640c41c0c50f00030381a0f00080810045c01020f21001c10b0b400b104002c1d440c451104243c00560382e50400d40100d180d00b07851b52100c0b001c0d0120100208918150805890354141e01400c141440e0500010279580c001104504044561002c94400b05002c2d0361a801501e4a00a135152204c1032801c10440d4002983c0410b400e400c0300c004075049540e41015441844201c0c041d24010034188403603000300907569515031006002c03070344650031300e291107215041d2107030040c80c01c503180403285203140e401608491002c16 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 326931061 1250 326929811 326929831
    0x209060f0105070210020601050103110f03040213020c01021602120703030f030b010e090f0a0507020105010501090e0a060306020f18010c0c140a080f0d080907030b060904030c060504150b090609 85
    0x884500180d002d2000d5402c040c0d402000c0051400c5035150003966140c0901c10103001034103000d4080c84108100c4204d03900700342822a00391566446401380907038080b204506410346903007000f913001020420301c040c04c01e800491010b0f860f806401d004000803911203044400300b83e08000740802c006034104000d40401502c81c2404900d99080b4001030312041400c1304420380044050082290940d00c82104905c610741404080101382c440d0407040382240c2e802d008050201d200000300340303e10240c2c07081d495400304000c0f03400b042d16520f03542c440e401e80c0c100c10b50305407041e980400c400c051070031107580c56000000d0030b1910000060464076002036824035882408110103103040712106644400c84450702401280d4110359230b1135071340b0340c03900c3e561542048840e000070303080c00205102400126041046036000340c10141503444002c104081180080d208030140100004607000059490089a00c1a07000c0c0c00c001440c1016040071809403603100341c00b1885140c0446c20440e0b1940c2da4003801760000b001c44 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 326932311 1250 326931061 326931079
    0x50609011206081f1a030309013e070918020607150e1b030606090a020a0c120e0a060305040b0114030f1c0e06070512070204020f070c090b030307020906 67
    0x4180c0800502c1c0981209056020340400ca40802a030100700100d091442d01d0100044001000c483e00207021044282e94103030000c0002c04001e42c0b040c00001400d4006400c8041d00300c0c401d0190040742012500019151042c0340300d080f82030324092000b40010484d0f1441404042a9607484140280700407200034860744000c07032404140300f540f0201103800780d00640d0810400540d400c0c1d09a6a024482d0a007008601d0306495103414180800c0071402401e001e41100c12a84400e00884045e4001014000c104801e9403030010206101c2e0900f1301e002d9030a51180c4118072444001c0c01514052504503405040c20305c400d220000d4040800a4119240300340480c075139402c401e002905084440d910140103101d480c502c260008841c40c4008000001c40e06e42208110040381800b030940540e80707019119400c030030500c5140600d4400203000140c4010401031230141d190760740341c80307039040508180e6020034541c9050001101c10300c02e4410000d0110029402d218143d40008c9402c0d82c001d10046c0a0030710b035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 326933561 1250 326932311 326932337
    0x60906090c130902060a0c0209070c02150d0b090a020316142b0207050c04060501080702102a031a01020f07061206091d060708060f010809070b0c0706140405060901 72
    0x83e5100200c103a900904490b52040c41d00d000401045400000317a1203050b4902c089180c80d40141450000366a015000c0c1990318070740c040d400200e801902d030100649465842d02c06165035001e04262045020719401038690400121241d960409280e000e010300c0141c1c50791a01c00e4001c0320079140303100712101c1c01005030b08090551200f1902d0400b103014207203002080c42020070070701090070314603198159401c02245076144011101031409840400140e00881c404401c4420a500000c042d03501c012002d03419204500c1d05095880c013840c048000180da03030000e00c40c554106034600860b00c10244010030411500c1c41c0a5034489e85070348120414020700b020004030b101c40d02d8003d04020002e1550800404100c0b004801e070000350300d910b01c601402100c00095400b0b004048440c012034010b00841e1508440314010340382c009015100b01e45a102e0002e000070380701c01800c0103021104084005d0210140341503c003400c0c04d04060b0800384050824030047c0800c0d00c605c400c1d15400719003440c1c14460f100d15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 326934811 1250 326933561 326933599
    0x41a07020d12200c01060302280b0309010b0916031b0f18050d03020321010b070204020f090907020706020c0303030c090f0d0602040306060f09021306140c0618060906090c 75
    0x1030f9180d1a0850f001183c904e40191065201c1000c1740e0003503c240c05904c0b903840c2c124442c12495200046203050795001800444952000b40d5030054100000240c06441d1600252031101e0072a68a245000600340039000d540d41402160a0b00400041c0044030300301511001e005030030082c0942040101040281f4002584000404010300e00a494107064040908000b9166408a03441c80030300e00c1141c80702810b0b0b0a000420078101c40400051031301b03140a5500b000044d5111190400c205c0000b8803c20b034041c0c0d07420400398041c00c20b0360001c0c01041e10340f003806418698a508040c0c030030741042c400c03c4031840d083c208545030004200c80d801042c480c5640065070ba0180c00c038000d000c00c2c4c4040b070080100301d010340c003440030381d441880c00c0518107a0340c101200c1070344294042400748802c2d10400b04001801a0050391201c003154800a042a0030312280d50703d0031300308072420006402d00031075074401d811080c0101c070b030440c0042c1701824803442c0c00004280d684108052050162085041071000511 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 326936061 1250 326934811 326934851
    0x6060111150910050601021b1005042d080c01120c0507120302030f01090902031b131505040b100206011419060c02040c030213050d020d0b041a07020d12 67
    0x1005141140d841c2490b2154695032905400380180591512000c07a80340e40c00043c5070416114560341c4500c1400e40c4405002c1680d24112007603052203c1807101142455502038060307034452080003a0b103618100100750811070b01d00c03a4003040305504000906446a41d00c0311900c4e4900600741c4e4040f03000e0b00581c004403880c1c030507403c0181640c8017070442081426071507002907014021103085120f00d66210340c0380c4011a003000e5402545640025001c1d903456004d86030112220744014807040300b4603a41049082614690100341c061100010340070300c81c034503240c440c6c0307100c00d04203540210745004c1c039a4020b5900c00040c010007011054040141d511643c405c035030403d00c03006000313a02071496510503000d0711b41401d004040b8810360500c0f0580b14100e02c81e00c20746004003103c044510601d8602020702442c000850310991b0806104600440441c251007410350295104e070542a002d481c604001c0002408042d20740021900449403208072681d121008003540f001d011800261100d0001030014018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 326937311 1250 326936061 326936083
    0x904050121020621040f03080601170f0a1d01060302090f1005091f030309060206160516030e033f070204050c0c060c0307030c0302040b030109092a0f05010c0506060111 74
    0x4d0424200010000140c50100c02140302c0d4442445d280ca51000660380da440c07107151084100c0b141e800080b00e0a20700b100454110b94040d000180030341c51080303100c400160180484000b03a440784003c00c1181080600c580d400010100c80304aa410840a0f030070460240d8030406d4440e142c1d560100d00d515050f0070148a0100703140413043c10b402c4e52454082d2013141c00d03200300400f42c000d060014582d4400301007013801c02c82c01c55980d54988580f40505036894070080005404002002c654410148c804008542c103e142201460b045400100b140992405680c039100b0341001204022800041d004400c1e540d44660488021850b03039a00c003250400760040506c492100e01c212814040031107800402140900d02c29502804001441e0b90203400340c0c4034510800b4000c16041004100b0341071640e005c0000e561041d0130010b0408903400c0c014a404c14445800c20601e09034280802014012038030950081c282800c001909492907100c6d541ca4220040035281440b048000003000c440080c82020144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 326938561 1250 326937311 326937367
    0x5040902060a0819090f030305010608040f061e0203040b0115020d09090b060c16051306050d0b0406110a0f0e0a030f03110f0703150c0c081c0b04060b09040501210206 73
    0x2007030317040c20541c20845420342e042c0c011230b1420002150140c42802900c0c402c64103c0300c00690540300d540d500340104480c8080b84040c14074170324580c2041149000075400756003d844940d1280d410140034102c0301c688443e015080d9403256076803840f540e800690381c0d0200c0715141400181e14400300080b174100c0c41951040c4109008010400b88a01952040b20099400a90f8a824200010303101001210800c4c0074503940505507980d188000740329000d80ba98018420030b03011515034161703d45100306400441e2500c020940034500c0e02a480e0348414000d0f2007070401c4550020300c61441d02c81c42070305070811101800300001e09000200404003080807055200305403003140c6180da503074108100c100050000c840d14450610380451841031007070750500340298000724550310300240c045a02421400003030500c03903441c2e1640c100b10101c1c4d559114410081c450403082e9551100c0b400c04110841e10160405400c445440013103524a039201401d200070140d0583e2420340c1c4811208402c69031040c240a98401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 326939811 1250 326938561 326938571
    0x30f0905030a0e010503060d021201141e0a02040303050a0323071718070501110f0d08040201080a0515010f0e04060303050702100f0c0b0402040e0f010c0905040902060a0819 76
    0x300000007006102d0a4002d640310030203842010b00440309403200f583e007660320208404028016140c00c58000084500717680001460102c00641d0f2034a9100c01c807101030a0040007001102400c620080395079002041c804210b00e0542569005040c17800f07a444d164040550321f5401805d00c050740e002041c021420300300100e200c0d01d40554014040d00540c40d00c112040540c20200b401c1d8400b03000740e00c44020002001d0444141803c00468240d91040648440d61040300c899a004035810300070428182d02c50f6542d0b02082c6428000580bc10101400103511b444c900000c20600120140c0100703500c8500b464040074504c00c2d660100c8500b61240742d03482d4410f25040300001019003103001050214400e13030390b1416644142c5001c0d94400640f1a400300491010f10818000401506520f60311038401440055000d0704501c183e460510308881840c1d01b0b079901c5250b0600113400c002030340001e10048805103d500360039400304041c0d0041040d0324041c403030500081200f10401c80301407000300c24001c0c42005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 326941061 1250 326939811 326939813
    0x50c032d01030b19060b0708031017070335030603011104180b0d03020c090c04270608160b0c1207030c1e021c020616030c02030f030703090b0a030f09 66
    0x303d6030b1042ea160918500a0b00082046141074020072046400c2c000c0da2078149603040d05c03940000da10043c8032145580b41000d001c07800748500c0894101c8101408000c00107270b811484c02c00e4083c160703000b480c1070300322041da012501c9102e20104420003074140d04030386890307403200700c08a809000c00c10aa04005032000c240441d07041080c00480b03000100700c06042c00160113000601c50318809450000c0c0058008460b000014103280c01416003010301e1483c214030305a580c0a480c40384042d0700200c201c4020040d400122501514002e00014203e00806064611491858800000c18522031740c4103610001c038903040d83e02418015140c48903265458169500d1440c50000c0601032200b1040fa4200300910b400802c0089012800701d6640d805020900300c2c5036140109600c80c0d01e6460300b240d1010f002c001e04124849800108400c151082c1c40f00e00d03202503207104045c14480ca000c0520748943c000e11a0304042684903481808965a011109503178a05030300d422405081c0d11008001014100307a0040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 326942311 1250 326941061 326941073
    0x31c030506090c03070203030f04080f27040e0307030c0503090301060612060609180e011e021b03070b180c0a0b07060e0a080a050a0509040f0c0f03050c032d0103 71
    0x284500d00442c0d0481c41a95600c001c00054001600c4a9006a00c00d0000440104011014a030000e000b050031604003d0310401486659100560707082540707100c0c16225400c1d030240716981012440403a02407004842d4074101c1c1d42e80e800f60342d80207800c2003000e556520a01806004071000784102030001e110980d2607160140c0410140c0c514005101d01c1c0040005a09200d5869032050302c00c1404042c0c42d044a400b2120050101624429815580c1e50b04040c48444a040c42d0070800941c80360150701c8940d080f00380c104030f0005121040c0160810408840020725021010f688200c40241400b120402503c83c0340c90304455a03032280e04407120780400300d040c604c031001130001036109000900c000c0c0310b410b4000c4c0e01c13146610320081041e80c092041c4044d0354015800350268454900e405400c084100000a00380c45002c0100c0549a0381e032140b960106a110580341c4044049040a02c2242408543c913076052000800c1c0c20f040a40c02d005108100040548400794058600c04001003961a82409 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 326943561 1250 326942311 326942321
    0x206040503190212030301050102070b07230c0414040209040201110304080703210c120f050f1309050f07170c0405090a0b0a0503150a020a030e0d020d02011a090a0b031c03 75
    0x6902c40c8121301c0f80705605000020032a8103907141a8042c1c108140b4040d0021041c0e001384034220f0340c5021811200b055400404071007410511840700820764182002c05004c121580f070307080341c0c2c00075844004010158440030503482d00182d0a103007000081d02c20303001075821802180c1100c0c1c024001c071800082482110408080e8034101c0030bd80c114911030452007038480c1c2c40f42c003c0c01803032032241c00c2e9a028920b00030a81c0b0001c0480500b0400e240620000b03014440d0343c001d41012040d000001010301001205200740c6a2048100700c110b286400c21100c003a0220b2103001c800703d07900b0203207000140340300c1005040e100280303009407000e0100e00701a0b00103005414564138143c041c1c131482c00002074070300e4000740101000c2c8100598040d90f807142e40035107010798018449482455103501004291380f50804c803920101c101c1394058015420042d60007400c0d034400e1459941000440d40754111140d1700d400100c1d0300501c07484c50006040c4501800f180c00c080309041c00b0301142c200071319504d44494040d005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 326944811 1250 326943561 326943563
    0xa0507140906090a09020a0504060806041416090b1318051b0d0f060905030a02030408070f0302061801090e0115090803070503030f13061a3a020604050319 68
    0x194041520465040c0720402504886a0b40e002d440c03031010039112080755000c0c40c80140040c00c5c86502e1902c500c04601a00c3c01a40310392200d5004901b003006001950103d1011110000042c04001800c401070a035140e416024035100d1541d01c0c507a040180d541d554507100307840901c07a4140a40061290304003248480d180003503415000d1a181315045080803c0443c00c070110003400200c0d82c0340c642c2c885502c1c11401000440303070301f0360343d080d03a201059080025010340405580155505d03414540a10f040010507031008054140e000703820b100507920301d400c8c3c500d24118240759981d80800100100c8803e12030750701054483c009180042000440303002030550102140c0c541885099484501039036a04c2040c40c060f10b81c0c0c1007440030680a2003140b04058001284603849212110280c43e85000c4845064000c070b601289a9031084043c1010300e0f14a00d514500044c10201c41c2e500358001041c11100a10140c03020040386500d0f0442da244001d03100640700107401c80b0285910046410822214018 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 326946061 1250 326944811 326944829
    0x150e01020f0c01230f16020112050f0105130209091504060501050918070908010f0603031106130b060316120203010621030c080d02120f0106020a030504260a0507 71
    0x40d0007203010400a48142c5465040e529030300400804400b00700107802e041c401050300c801c01c008010700007000b480500790126694015164204a910001d8940998200c500b28507900303000c10040480040c141d0981128010b9500c6550301d1001007404009200c0c0c15200791f40300010000f40b15114000341c080581540e82914208419a22071005440500866016079401441c0242c100c20826a9070000360300401c0b030703060004150b034850340040d094031041003101c003400c0d039510010403c2c541d0200c4807111005010f0082c0581d418090110395500300c803003402901108007000428076a4070308021031140418079482200740a501e49406410104025a00380c0c801e41c00c04c039000c600d90008150300c3c8070101864903030354000c03034603950141d0f01040000f00540d840c48040c41514010750700c90000301440602d40d0b200c0c0020b4030748200720030784180068100320219841090742c2d03000640c02104403010f403449055000c0da07032500842d1410308420036502d00c45843c00741c00c40b24000c0110018141d01500e01e100e07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 326947311 1250 326946061 326946073
    0x1509150c06151208090a0e0f09100c02060703090c150203190201230406200901201009050a0c2304090305070f06060302060c030702010216051513150e0102 68
    0x100d80c101c03065489003c0c0d404100800f100d900002083e950040110000150121034005e586100038a4102021035140c6102e04d070080c20460070030001c0c80b0413060400a00001c000381e140c0d4a600955440e4028206020305540d40d004009010ba4981500001c2c050000c40e03102050403114029102d42148503c515017100d900b01640455006000e007030528009444030023292441c0c0d038038074407810a020b030054600701d6603020903003410490599010400300079440c2c6942d84000281c0010f101151355018142c0000d20358841e9440e0450124203044405250180031400f84078608140b410700415280c000c0c040c003000d003000201c840705903010080107007021803040405c5c282001030100340e801400c801000204200b201100040e0282c6c1d0801d1014064007001030040e44035030102d40107074000c603140300466101046900440d80c0c10011030361020300740068400c64520f450003103088a10000354000750070502181201240800c03000b100c0c000d103404460721a40c004024030103425038070000841c50050050b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 326948561 1250 326947311 326947331
    0x30c0d0908070b07030c0c050a030c06020d09050f0d021c0605040b0709030213020d02070f0813090e0604060b0d120305160c0b070e040b0414010608010f030305041509150c06 76
    0x2054072030072950301503070452418225076800c4814906d21750080392500d8090001040c1c40e2074200c440e1015501c28411541310714200040a4507200c007003100ca508010700381c0e806105a448055001c83d000340181c07017901040c009840001d04504501200d1102800d80803440300034030100e074000038092406a01c0744900c5494032201110325144074013019401154009440801c00340300d50082510704406500107040a00c00c1c0d4408080c2e0344500c0c0706a46511010070200700300d040c41d9070030300c0041464080400c01201342a050b107488020050002e050b00c1d40d145807551260712020121000680d100d980d0395180300c0c0384680a03009180a8a44030b134140040c9499030091805001d11048440d04100030980b265074070002203510b400303070301d03541500161a120707050f80689540c040c8100c0012800100c42807503050610040050905900001d2103492507030040000c070340c001c0c0442c3d050320303814481c1512010a42000740c030b41b9105640555403000d20008a40310742e980c024441d9012910415043c02102e40e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 326949811 1250 326948561 326948563
    0x1104050405100b0a0c030309021f080105040b13020c1e072309060907020c0a03030e030c03190305030402190306090b1609260303091e030a0801060503041103030c0d0908 74
    0x9103014605820800300072100c84130340242001c0e280c1034071901d004986203c20394040782c02c0000c810b040c0c0d01140003501030082001d8001d0b0f41c4a02403c401e460030814212040002450345840ca81000d42c001c2c2c0c00201c2440c11001407016003200807144580004030100c0d40c24a555a41451003664005100851a418030b0f01e101e1111000f0307a41c00811040158554208029104101030141425441045070442c200d03155046000d000b1802603d031003180e0281c0c03800b030600f0540201620b0388250024040c011155540452000e00550145401601c9a0706d500c0400e00d201e24860058000200741c0c1e10010410400342c00401e005445446800314a49802c4903144194541c0c0e11803201040e1041c0c400e0140c0c00700c013441c203842486260000b100c82c0122034103050542e40280c0d140d103a581c001c0c4d4054120700c202c3c0e40400000310340700030003180340c894000001000007006014031400c000b80000801c003032141d01c102225000e0002403e99954518403140265100301c458a031401182042c280015a110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 326951061 1250 326949811 326949841
    0x30c0c0118081c0f050c090922170f070c051c08030612030912060702071d0f07030902040e03090a050f03060a0b1306150306080610061407061104050405 67
    0x141c09181c907420b020010160760910240b42e0110f2003600d9446420301040b04844c05414020038000640691b02d942200503c640ca40c07000b0510941c80400c940390f6905a03d120808201481e0490213a071503541400020000c94840c8215030f80d81e2801c0898450284441c0a180104079501210700c146040c1c11102a01c030380c0600312502801000050000909030b0400c9007242c00c0100a18080d00d2600807441c00040110580038612440c6a02050403c0551a010811100070b04210381040c0b10303084582e41d0584403e0001058540b0041c114400b0400c0d0324043c2d00f2803084d465000348180240e640060f03150340e481e0800c0c8003e52049140c0c40d4001020b050018200710480b0001d40030702496650301d40060040d1030140003454000c0740307821000c0040000352043c500501108004441d00f00b4000c4001000d2301c480e504104c1c0c064111205004404400044600413280c0906001c41001514201c3c80b0303180c0a43d40000e4821030500c103001d40002e145800078400d940382202d00708940d03200c103018042200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 326952311 1250 326951061 326951063
    0x602030307090e10061b0f06020901080601050304050309150c01050412031a0109030605061c200609030c010e0406090c09031e0b040602090d0807050f0106050f0105070224030c0c0118 80
    0x8089244c244400c0e4400e08007045030b0f40b0702000f06081640b8503581c0d40d001004102c420f890b01d50303020904c07440c15071b8030011494000000340303081c42c21030401e0745545460313110b10036490748100c0c42c9030345d0000400d4200d0191044402460020055440e06080c502c401c0c1ca645510540041c2c50540c6450041c401c40800205681c01039540c0303020103045965007070040401a207000d60100d19002e41d0f890226602420558891044000710a003007410911400d4042000c401070344194401c0c45001c046031070004648004030001d10b40302030144c4144011900915054100e0719000d400c01c1210890183c1101400003101c0c40303508621010311070070b100351640c295402030040c141c0d80c001c130204020401c83d4001c0c05c03100100403c16500e80c045541d600c00c076a802160300b2107058100400261240704d081c03103120020030701907598542001d10600001e080d8407481c036000380b280b10141e011010b0002003195004184416141c80345c1d03241016202c00c61a5044022410300a60030000031202503880c481040e01c1d01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 326953561 1250 326952311 326952331
    0xc0b0c0319050f180f04021903050604060b09040b01211e0c0206010b0a02070530060610050c0c0d0308090609010b1f020309030d1d090f0c0918010602030307090e 71
    0x8050400c4940c00e10344da4500700c07254449100343c5d40c40700c0c690b242e100428403400d0781d0485080407520040007034103403600104880d10403840c0410411080711510203e842c401d07401c4030009854551000140e0b0409440c1034200e000b000300760005103603014280e1000c3c91580000c1c001c080c000d80500510403e48201002c606e00580200004020500703591014200004c07041c01076910312a11080031465285828007454580c05004c1a03003860346110b0320003000c416400b0b5000d45554035042003c2118290300c4402402000350005180c800004140809074100100034a0004002e4a034200100703482c105030786500050180c1000714042050501c40e24a0303100010349070f60108003103170514403000034042065a003503010401a0781c0c0150b400b80000000443c1c1901c40c8403441030b0100b4503500301280780c040180654a8803060240b45411140c1003640400d07150300c0180d4801040001c107590600038282c50300c0501d541d40001c00c000d90040040d601c00c02c90303907555107410390b03503040c50034110402030741c4400f00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 326954811 1250 326953561 326953567
    0x131a060a170d030504020607050105151c030f050307030f0609050a0c08040b04020d020a09020c010603030207080c0622050a1502010510061e181805060109051c0c0b0c0319050f 77
    0x10b040c0c000d0f0803160b4024001400c0324140201500ca040c01d4600c11070b0240345401d103507807071081180351101440402e22264815044404000c8c1e40141c04411402c0c03100040c80004070025003514420f401c594503a031313000241481059500c105d4035015180946080b0441c600300644204030901c242400b502c00ca0300007040d081030303844603000d20421001d2030100f41e8008004240110b200c0301a8002804034001c2e14000140e0b551543c18000e080c8105a005680c483d040f0076400c031103640d10b078010780f01ea88041c0904050648586084a0042141c60303021300c0d000b0351108000030b4510184980c10362518240d030005e02556071344482e20b21180c02301e03014030f1011420070b0b1880441d245481d16003c0400b034150401c07290300d15551000c20074060302503000c0c0c0c22801700039203051780b5100e640c02500e800c0039080c01d00301020390601e170001f207007240408000304401005c64400028031541d4500480208480300c1c00c143e442044541d00c03512580554161419501c250503040200c921500440d48004e42240c42281 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 326956061 1250 326954811 326954833
    0x61312030c03020d050103051609110405060c0f0f0714060a0f110a390e3c01080c030d020c040f060f08060906090a05070b03131a060a17 60
    0x41948107038940c10981e00344640410381d10303140f1030036028502403c005c04000030186540401c184941d0862003569040018840325910b100702580c0030356400311415500c4001907640b4500e00035510800d00507904c15030941d62740d5410003040c10700a42c0c01000c0000704007200d0300e0a00c10340f4840e5849c5030300058040d010318503049100320f016108003407894040c0d400390012500e5020b0900b1161600c03001001ca070345002051680d0180b04d400303012030706c1c0390403402071450100b15813000c0700e00620940448180c039542e909c0e12401d1400d6440c2306411011409601e40e038058003044400380c2405001c625101d200b0180e40c00780350000301c0381907000b03056000740582c00c0d81009210241c60060416105142c480038089015021580440060004030008246500e05400d2803440c090b4058403031442504030350b80d4007000c2000403030400292240044020b9032611a92041041c9400c0481c0203400c0102495042060a4541c2402030181c0c400301c070814501621b41081e40c3c0120401154011294807944241c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 326957311 1250 326956061 326956067
    0x2030f07030c060c0306060e0405040506070e060417070f060206041113060806090d0f1110020325030f0614011b02030106030210050a030c050c100b03012903061312 72
    0x8200a032291401ca0010100b99403168142c540100304000817a403200c0c2c05101481d44051a455014000c907001d0159042070b445903901ea22000e0305810403c03904907400b041c035844440c2110014414281e0a40d014146100241d4641400c2d000742c0e01c001c0484400050810700c0010030a029903080b91540d111310198908000040d00503007a8442001c0c0c407140000b44403130b02030010320310944000018180351000c0c82c170000c00240118001905000600c0091200c4a10004454a0412140b40d0069694540b5600f1011040340300380c81a8881420f04210b810841c0d0680111224103e072030300600100344c9501034110b19800c44101c6600154000350740c10007440f1013028250800e40042d00005015480e500031510703d8004203e0f08012503000690540e066030315100301c1c106220245005400c01810212580d240e4807000c0098003c0c07910b41d0500c03100c03035400f035104002c24480c2d0400c2c203c0b4442d00049008030f180d241600d55109004007400148116554181d00c0c014680c071810781041c2540d588425 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 326958561 1250 326957311 326957317
    0x20a0f1511071208070209010e0f0a050601030b09041a0a02270a08010204031a070c0209061014040f030c05040207120c1a010b120a09080910110319081602030f 70
    0x41c0d0328a1140a1001429080d90900800194043c2507515980c05050040c01090070040c0d105008203004c01d0104000300c80300903100b075000000e04002080c0c507103e50004802a04240c01015030062075417040c8410441030354088214410400c110326200d80c0e0f1148104100d01403000b0403110a01c00c0030030b1340c24111038418165a28400281a43e8000d901c96250900b260003a41003200c1c2c141440c10000e015910030300100394402541d141000b1854020707404030300c0c40c15024041900981d007404062000c14041c2500f1440c244071154040d450769961342c0d0503070b40394075588025142076419083c00b2899061500841c0e0290350000c000b5034102c450410b0480e40e40e007049400383d80e03140220103480300c0507481a01d154020030898030000d40718100c0c11005608154082c208036805440c00c0d4000c00010300384000e031183d1fa202141c403941460300d100c0d825030f801c4c0013074140c02085010010b1030003a18005c000c11062040c140ea41e854007166a211a011300e0942491000000750f401486400e841c90507903401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 326959811 1250 326958561 326958587
    0x6040c02120904021e03071103031003030305190f02180901031a04150c02071703030708061009170601030302012007060b0f0d0b04052107080f12090109020a0f15 71
    0x10043c64005e44081c01d1007895420080da0340d503403c0001c20312140355408114161600c220078007071480d6003031022000c042d400c400d22006061646a00004001003282036904d031000d001050f0510a441d44115254002d501264243d000c1600401e4540c0890030980285030680b9404101f200404034910300303650400d0801401281c820030f0350004541e800405000751604010320360020002241069082442c520f0003400801c2c8940c410700c10442c01c0d5034482102c03500540181c0e45145060400c01c81124011903070307044628855550b410301200300a000030717582d0489010f68000c0148200c066003030304901c3e009200882c1c0c909014800c840104074960711842c00c40d0300042a061201050760003080303c8410380c02c0140c0d10040da43e02080b0500c4014442d6480c3c8544c50400d150108415921246e02400780301c1700540602c802150101502c10854111502000040c0c200307852860001100e9000e024543d03422400b91040c201b00291428401ca200c0c42511803614034000c500c04036040032241034583c104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 326961061 1250 326959811 326959819
    0x3030516020d170306100f05070204150b12011811030a0b0f100c12141b12031008010b040b060a081b0a02010608010b060708030c070311030301180506040c021209 71
    0x9080b00004500f451001c4007400340142e03050b128a404070030002138003070488610301408860115620300039800000c4800c1d41d80d045800140840701704852180180058000f03003032503840040d00d48418010101c0e05412281880440f5150b90020030345102034031120b00039404516010700c0458400440d42d0400704041001610800c00445040006140f0fa8550f4594102180548451405200f80410710344c1c42d00c2c0d002d0811201403a0350340b91052042c400d510020403220619074a452821001344880903000d5100601c003600c904080b09141084030031841103080c00d600c3d16000e0401c9050501401c698003900510075802e220031004103582c4140001d0000b601e040300c0c45141c510340b000090241c0821415035000050031802d155039a403c5905050085202d027a041c4006000612500200c0c0d41c0150032118aa8940c001450185d5055101c1802003659020200c00424055681c01000e19070610f1100140000d44034001440200d0380d0b100790a070016000700080d03070302301306a0000030159400090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 326962311 1250 326961061 326961079
    0x1a070c080307020105032e0b070b16020c040e0c04090503130f0b07060b031c02030306040c0c122f01090c05010318080a0c051006050a06082e0302040507020c190303051602 75
    0xc03440b0b03161fa4960f0401200c1b45400f05207001446200869298040708600c20702120000401f0040d581b0b041c2c40c0c02c064405c0e512a91725144004042c44480b96500300038009100a90325450419102c0d0440c2454480c1541c2d2031070001202d454509621046030b080c644800d2034044252103401c050425940165090300c030b80e44214841d01060900101d81c945541d02558690034241c0401c400e546800300703214208842149000042480e00d000d0880000190030724681880058806022582014080d85550402c070300304841d80b00303019001241c12610400000844d00d03158801075044402d0303045864211025018500d0019448800811508941d070410505601180e680c2d9840c0502000c0c40c981115240c0004200030b0901610b01b2006c0c0c0317070300d0400e04854034144100d801000f05280c0e2030700d00d01c1072902000c0419903440007448040d5030050401e0000e444d01c02c4001c0d548400800019005540304c1d07103680c5603a1155581c101c1520343c161784d06407601c0d11040401800d000b000c14181e038442494 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 326963561 1250 326962311 326962381
    0x103081608071406010f03080d02031b030c0a031103070c14010f0e0c030606030a080d0515040603051509070609090b1201090c090b01020318060d061a070c08030702010503 75
    0x20010b050700d01d100c0c044a580c4552540040350030940180e00030f0880403a003510a0000074043c8041d40d42480e1005001a102c0d41c64100c05104c42090019991000b0b9000042c81340f0000c0900003041070042503181889041c540b07621059440c441180c4280c001040e0503541070000382c10b1541448200c5544001080e81d4956064400c03c0380c5095034090410340c02440303088403c0c00c0500040742d00010840261000403100e0f01d5200032407051707401d154005a07407480002e0507004520758241000c0c102800401c0140d071603240c0203560350804040400030b0004040002d94012000070b92406a036255500c1d0b0569515100c00a0050284040e40c41d612050041c4540006035007441000c2400e401150030b003000c00d00c0c184088003120000c903507160454000304070345001c407001e010318440654416a4420782d00c4010442d0b090061400750401c0154a0700c1d01c190781c4080d40707248050044c090040c40b4021040c0d58030b419080e81d0b031180807002804603005200107a103007807191500b41d8540085c6140c3c134000e2140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 326964811 1250 326963561 326963573
    0x2010f05031506030114010e04050708040b0406063b060109060e0402070501241d13110301050907060905060301030c060c0f050106060c0b0c0c1002030a1503051c02031201030816 78
    0x7013600804465824400e00e0030311b543c1d21285414241005032010090350828850040030701000400180110b40644003140070001c15600002c0140000000c071043c44000d40c5001c0740000182c00c43d440c1c00000b40801d03050103204a0090340c0642d005840340c4151501d03115007030315601440d076090745d8000d5080c0003050102e98280241c6030008080748540700c070179031a0034400c0c40250300303034103c490b62a101105110399004e142c1841c1381c110b264203004001c00b401c00c1c1b615003004036041c18026055401c000501400f900b0000d1804141c403019100d0344481a181c2007030000c1404244030203024002100b50800c41c8500641d201a0407502134540308241c2d0106031101400d42d800782c0c2c00b11000411420305c00090000303004441d9082011035507442d180c00c4030445d030355039100e80950341c2d66641540007022824407a10340e842400d411100d5446140025600d0608a440d00070848142c0c0b21083c282c0c82d54184544048100c2d5000c1210500c221001d0f421502c400034650898900220440301d105200000f04107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 326966061 1250 326964811 326964817
    0xb04150b0f090603011d1507020a15051b12040309051804021014122202030a0b0a02271801080a080c010906020f0d11040b07020904080d02030414150402010f05031506 73
    0x411b40000c14880300c0c100d090f40c602c81d100410f08421500405c14501c001404d050313001e624480e80002c0400d0076110b4014000a500100d45080c803141c00000e0f251201e070080068442c4140c1c042e03200c203a00c141e610014040e4401c01c003d540c02c142c0e03c00c1c00c0048c0c010302e0403586102c21544589018650a507400c16041102d81c843c08884844440003410000c2d40000d020a03580000300c98a030700c02c140c000b6139000c00d590b6002044014000303400032000400d2060329506407656001c502e010b20003e0086c40305042025013507a014031380185850645655401018845a4101c40f00800201240c1d940d0b511000040c0d04900784140701552110341c0030000c01c2d4640054a8507441c00785075540e543c24401504400c50b00c07403441c88004050309010420101c07a1400a4545076a01907924400d10f585511b8801c0d9184103c03001c250319244003100f0311050000b490151480e070711816086680c6880c5001060b080b0306400c880c001c1c009210b10384202c444a10400155802c55416010750007400c0c90600041c00c0c80d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 326967311 1250 326966061 326966111
    0x1090e06220f082101031403070c15030b030102130e0a02090d0201050a0e06070b0106020f07060e010e01030216050105040201110102040e0601050d0f1a040c05030f0109020a05040807030b04150b0f09060301 90
    0x950900c0041c82405032058860500441e540c1c0210700d08400c9d5950b072a2100161711496a142c2146420100e09034006e81020340301c440c004008564a074102440901d141e1500e000c0c1e0100a4145400610b0300c0401740300b29000c2a42c01003202d000c0d0a120740c01100e0550240540000704001d030080b481403510f0300030260800d1481002901410340c10500000d1a000c1000f039224070030790010344208291500000c1c8140405001e1904040c1c01c2d0041d401070f0b01034412450b120039a6640c2a10050602030306501290090340300f40e90b40a1aa805880040d00340c0c001c0703001e40004031011102081556008100800e00c0c4034400002041c03850000d06580201c920400b6400034010480d91214100e260500c680c1c0c00c0d061080c10041c2c218182130b40b41801c1d40c8814059141d14075400a0003080e02e03802141a100100b00c507000b210507190b09c0b4549201c1c41101580d003294400d4001580030303140c0360715010f40d10031803c0c0a01142c2041040c2020400c0e540c0740900400e070155681c1c52600425008606000b43d06 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 326968561 1250 326967311 326967367
    0x33060a0522061d010e040c020f1501050a05121c12020d0f0f06030b06060c030708030c0406170f0a0b060d111210080a0b0a06050901090e06220f08 64
    0x41d4a000c401400941c036110034642c2c811110703080e20040d0782c0c1003000d1201198094030700044540924a007a40703009204030040203648a01d0452020640307501c07910b507058903003e9a4506810340c0d54802e2151210280d031020340980c004079100b141d02500c04403000106001807801101c6000c600e402c10080360304c2021400481500c40d4000300b0981010f00031003c030346a480c0070400c68245140c48070f40343c949016160611410001442c8081e5000c1003007038400380c0742c12070820b660341e09010b105071034130b90b100307100d0031021540030098084074206181c0c0c1c452040110545054165a07a4002c1030010651820003540c0540240042440308005115680100605004007683c1d5854101e2501840b00d00909418080b081050309020520001c030312a00000d80c86420807049884404414020f40041d8110a4118410400019001540c1e4010200b10030f0108141c0c0c07040d03140e8854800c4200d1461318104904c040281c01d080008401c20f44c6042160b0044810700e0800d0085401c5224001d91102ca003450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 326969811 1250 326968561 326968627
    0x31205072f06040f0314150106081006050f0f030603011e0b12120a0c03030b090c0316080c0307050705010e070e100605030105030c0609032433060a05 66
    0x85080040311501c00501c11580c00b428a0b1400b00c150b207054006000080000400000010a11004000714078a00c443c84c4481405507031241e00040c05a102140d28020010310890001056805035045415251000f00c0c06842c14485040c1c24038192300140003550159aa25090340310702c240c020155080d0301d02c00c040426003139610b10070060484040710a0f82000d070800b207040140a02101c00f00c07151105141069800e6100c14101940107000c10481290030040c041d08004085c604d203401503110301034030b2040384c1d28034003030a00844c0c0a0303808a80b480005402000460340e101c1c0503802070084248204004228100700b034130304508040c1c05602405c4542800002d00060441000218000c3c1c0458980701d07003158504000030f65524084100c15002d11000100e82003a03450030b010524400c40310908824942d00600c0c0070a08440d005c603028001074407c1c0c440d00100c402c508044022841290324400078440c0c0d500208582c0d03a00818551702480410803410007a002201003201d440340c001c1d058004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 326971061 1250 326969811 326969873
    0x12050c01050901020a0e120a030c08040b040e040b0703020c0a0b19060e091e07061206090507020c0a150e060a02011b0f0e0405060d060b0604050d0c1d040503030103120507 75
    0x101ba07148650216104084d540015540900005981020340b6007516009592118a0074402003912507508008031200c4005000f142288410038614002c511603101414240d6030038000f10124040e900070118140c200c21035840101384407032040c607006611109480401500b03580102d0403980194800c5800041c04030400c0015a41444035a003040f9500101c92031400e2080886915103199008100a004180303050f128840d0389503003c5ea010381901c0d142000b6604000c00080d5070b40001c14203051003032504000200d0710700d20440c0220030006051720f410000d021264100001034004c0c1102d80d00710f658071a05e03048201001d0144805990258a0380c3c903e10440d40350007000343c904066480c0c043d50810301485034603260300c0801a0005e4000c4000140101460b000420700c0c86594407080d4040c21903129002406851481d400841c2c4c20008500c40c4440148400c24074954100e5001e00680c0080c001000440c0752040420000600c40c40c000c2d10f494a590b89009151004054100010395074280380c0f1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 326972311 1250 326971061 326971067
    0x3111c03090c090c14180d030203030415020903070e041a010f090c0807080c09030c03030f18040605031905070b0d0501060e0a05100c080714010c1205090a12050c01050901020a 77
    0x20000d0f12500c4418444d079400c004029000c411108142c10940701c00141c90395036103082c01101741c03041d08000e1180c00d1484043c00c00950382e400946d0300f5212600d0343c09185011021600c221341030100c01401800485190146a80066400820507154844000101c4204070a01402c903400f0b080141000c0c01e115051144103411603900c0303074103141404205000d10070703100d81045255611007800c000d07013503490300742401007400d1009040d0001d401d8800440c0440d1000b00c464086d010040c1b03099114503451200000b000141c80143c07052a07010303002500e5400d1490156000e07050814066400c03600d400356a481d8181240d40589465007249a6690040c4071040d8001400e4000100c11140680200c0c2014006005100c2030040c09051020383c00300c80c2e0411520b041554052900081c000300010340304460140600751007601140040e54418401fa40e550b00f61046a02902540c4001c00c0c064190b541c5080002c60002c0d0a0000d00406110303e83c015007003402030501c0345889400140e21115a4040a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 326973561 1250 326972311 326972333
    0x120312070503100302360a20030c0c0a080403050309010e2e020106080f011a09100308030709051003061a0903251d0f0106050702090403111c0309 64
    0x190070410200148001406801c8030310080ea6011504901d1031411460884560760722100901508045c004481545651012074144290030344001445502900c10201c2c000c04001380740d001308600144041080000c0e00400340032750301c0c2c054003160004005512121203d4006a00c2210180d100141c0803815588c0f06002d42e86420342903441601144e07105900c0c0000c1481440c0c0c1c6000003801070419210076100350000f000800c984020f40354446c0c100d000d007502038101c070561072203d04070000135030982c1d0600c202840c1c8030302000701c036504d09942036644036040b0341e202401c4d007401c01640c0080422190346140c15030031304030510340f0300080382454a01d400b03003500040440c5815254050102c0111910b0115198842c403140400c846229a5648140303110014150070483c2c08880d40c082181c844001502c02a004a0100c820b880040c2c1c1e942000322003611441a000750010b07040350120300024060308a640d030140c10340f4260b542d0300103101c00c1124000368540c01701001070303111040304080c0b020030101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 326974811 1250 326973561 326973571
    0x1104051f03150503030307030f0209151207090b0a18050a14040615051c06082a03010519150e09030a03050c18100c12030209011e0801060302070c05120312 68
    0x109600e841c3c400040c0e00ea0000400340707018161901310402c2021001e40c12108002c40c01440c03041071034440c0300c0081d1070f034000c04005c43c1240d280b48049034a140c050180001100d5455018030b2400001c0309040b204455019001480c2201c0d145001c07809a4400e546100a02040b0308103040903039001d010041030f5026a4130081112051500003d5640e43c4a42143d0004001d40300300765141e449100d02c070f401008240d2081030a8043c2800c0110000c0120849020758a840b041c515500c5400c5010982210384c1900c07885640c8100318180060b0201582204040e00a0b4541c00898a40c0e64a400c04004c042145e040075250000540b8415030f9030140b0529402071300d2810403900b000f01c040c0104990140c8122160305c51100004424505440340b00e09c0c1d00704560011035114014201640a400b82d0030226003540407500120200080e2043e0040c1c2e07800641071551142c00e581d02c0c0440903802540b0044050b140030185000108041e15080700c0c01c0399079a03e803001166038043e80302d103c041072400501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 326976061 1250 326974811 326974841
    0xe03010c0314060f030a06091226010509070509100210060b0304110409050a08070b010905070c0201020a12020703020607050a02190312030221160f030e07091104051f03 74
    0x42001402c40b00c001c16900c4041580c0490554020741d0010b4038084101d00c00400250a02941700d08008030340382c000b50008120b4031404400d800380f40c8400c441c08007040710340e107100423140c00400c00c9203041061140c03c298142041440d003202c040103d401415400d6106000d42e0002e9440d031641c2c5220702c106c0d4000c00b049072a03d0305605240c0d4645400705044180188110f443e0000745003401024000450f0760341d0b1203644680d46c2d103000d01c0d00b6a80c0d26402d10407082002d14240020300041d0054005003030b403550590190614083d10750790368011100301d0a06000b10b20031454044010f80354000106822802040200625040c47c41040f4044504000c902603c01031040304000245811260100d100200c2c03c0141c2c0304e00c00e034400c4101e0404424100c0c126a2207210601c068141c0d031484403004005150390b65054680c40007000c1e010f440f20004895403e5104940800400700ea55200c60881051049103c2c074150341d5a0010f441c05110840d03007803111614920890310079425104d1840c4010300d00e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 326977311 1250 326976061 326976071
    0x10c051605120c010e0402070206190909151d071e05030f1302030a0809030a020618010807020d12180804080601061d0109030f0f0203100204091508061602010905030a0e03010c03 78
    0x100008041917620324000f4012074001c1160307003c540c1c42000380d5600c014050369050000383d0048000740682c10034860110b01c17514014030110f00140900180341501c95203003899461008100312415406001440d440800288003000c0c0c0e000f01819a00100c4000c05503a0390f5100e080950394050025400f820910944040d40313078080060b140801d81c041400d400484441e1540040f170040707810031100e030100039400000020745902c0c45000c146001c11144c000e030f80340407803036540c824140c3c2d0341d03101101c40e0b80100300c01041e90208003a9540146400d28210308031809a800a6516100d003900b06800070310a9070041c070018001c8650220801c04000124074030120800c141c48000381c241c807003c0c00044c10b280d984102400501051051401d000760340a812104c81c100c0e50300d0440d00940090280c04102424610704648039180200850150f4240d40c010780055140c0d01c0d01c1da041e0200b1a591441555224400a00854000d102400c44030119464210380b0b880700404142c212061441081d040c1480c00e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 326978417 1106 326977311 326977333
    0xf01111f1409011a0607021309060e060c04120b2203030b010e040b0f013b09070c03140309031c0c0818100b010c05160512 54
    0x1003074032154907144419420380c1d07100720089210103440b00f070428240ca4140001c1598178801069106085a40c800040c1a00c5180074203031030141d502c1e4001c60f88c540c000c0c05041c0c1d104a540001900e014100300340c01c10b50792100c940c054090034400000581440d002d1101c0070707000c2805820202806000d01e00180030f0314040e01207600180d98018000c0307482c1418003560606c20002400e59444038504d000468000d03200045002050f08810151400b000c15107030114600602d800004002403688000c0c0038032500040c10b090204100e107502c50010a43c004070b8101c00000c00c8078480e55035103445031707038038074502968024110a58550783c40e1000c0c00c1280c0d00c103985c2e10038551103140749070352035241802250742c0602403100d1130b07001442030224445071030b803107160021030506000603c01c1164589a24160075581181116402e01005002d039240449240d074500029400504078501c00f = true := by decide +kernel

theorem cover : BRFrame.Cov 326798561 326978417 := by
  have h0 := BRFrame.cov_init 326798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 326798561 ≤ n) (h2 : n < 326978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
