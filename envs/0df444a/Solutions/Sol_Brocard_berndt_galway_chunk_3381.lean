-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3381
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:30:02.595164+00:00
-- url     : https://prove2.me/submissions/8e2877a0-fc99-4a99-84fd-418c32688bff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 607913669 ≤ n < 608093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 607914919 1250 607913669 607913681
    0x1d0411191b0201081f0b0c03030703060f0602060703151214060a110d0908160602070209150a0b090301110c07030c0609030209040201052113021c081204081e030703 72
    0x8200803001004034001031380c0000a0035840802c0b000c040c07001c0d07410070100c0180b0030659803140340701900000308003408003004802141f14060603103040c48855550805500c0d0b03021240314030f1005070407040c04100d0b580e1194019a122060b01c8040030380c020f07282c2c1c81c50903240c144810f045a48190745030205007110401c0c060035500c0a20001e0030407005041500a661602c250b407054043c05030f03119200d20800c41110155641c00f000c2e540034800c142c007686400d03030080d0b2004000ba40324810074000074451851748400c0b5005080c001d41071071049441c2c900c0c2221560414062194195260ba01844080c0c0c000b030041d280108a120040c1082c0d803442c100901103d0f802d400140802415550510168031907401d565000303a030a00c2c24555842e640e28004240030116490114401510410700c02003511038800d01c030032310b4000c481c01c10401003551808070711842d01010050080e4801c0c0028100750181640d0300d540103002e24440c51814544800d41e10101d90100307103901d00075402006000304030307074035200b26 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 607916169 1250 607914919 607914947
    0xf03050f030406080610030f0207060203041506051f033b0706094b1d010306090f050102070c09050a0e0a06021b01050a0e0c090103031d041119 63
    0x3952802d818404000d28107600140124010307418aa00a008076100e42d0000495811685003152203c10f01c0c82d0460282d403080d034041c0c3c0c0720103103200340464001da188101004c440c0000c04501442e40c8081e2085e12140841404006269440f180f50400040c0d103400f0301602043d07400c0c0703200400e008060054a07500341c500059616482880cac14081c66400419160035604d01302d0011440d4070700400100c403009401c000186005100c0c040d0f60764001c8000203103540040e544141820080d880e2015007891407007a1408080400019004001068041d1300604905000e2070500d50144903030b445050990f84000000c07288240d07046030400001d201d41c400d076504282000c00501001d81c6d510f485a0703603010301e280c0103071109900140480d140a6029509100c50000c0c3c4000c2c030240c81c08200c04002071424507448a09401900f41c0c1c0d682030703d000d208242c1a60740c152602810306a0800100c0d00510000000d80c0d08250303260035240014104001503c58500189040300620703041c0d00d8000d01809491880d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 607917419 1250 607916169 607916173
    0x809041503110409060b19060914090f0a060302060a0f020c010503010b1c0b1908070605030606040b0c01180b180105090d08040501020403080408060a140609060402070c05030105010f03050f 83
    0xa1000500c80b040407481080e04450100d15007085041150041a21500041d4013039000000362203441120f0001b14211403854072041b140650780c8812001c10031f10320071a941d200c59860001080032103194041c64200080800019001e1380303950102d1401d80c410344802c4082174403481c16420681d1304000a0000000a10b0440d096515040941405000320394a0483c0d4800c501d80071296003c4940c0031881c400801007010603203d03001000c950103034805014843d0a13002e84200030076150b01038400c1328003881e03010f010546081e01d0f0090001098000950101c03d95417102d0305a06000c400140c0200c1007030154400700740b5402c20701c40304101d0520201442c0d07401e904000c200f05009601161511035103541d824042c11030350b510b143c030701d009101c3d940000305000004a03000c1448203000514a12030104050200070b801c00300840344014120849049520109480001d20300d418103401805a07940300340c10b49091203495000203429900242c11100840e409040d003001441020001640c04041d0540 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 607918669 1250 607917419 607917461
    0x130c080a170702010c051606021b1810030c032009161809050a0e060a020c030720090a0e0c0a0e06150d0c0914120606010809010204080a080904 63
    0x92800d11119800501d80d2210384081400b40c10f59018110076200c25610109070340c02102c0005c0b07080100c1015002e5940144181c10340c1c01241404072440441c1f0540c001c04031050b8290440740b410203008002d00541c40746a00034000400510805084d601462269044d4401e0040c0740d02c0c0888001c40d0890504c0c49805a841445a586039a080c0e0000419103844c01c0d45410164041c030240c0d0707800c81d074400c2d078410340b030a020000002c039694410003039000071100356041500ca9120764420383c024151145102d4104210140c0003c4800d503684044502d85043c800c90110010000340610f0021102110707116204c01d01c07191254014071190310101c1040351010348032420716000400341c04d4010211800b5050030700840b0000401a410769100c810b06003018482e210303001e100144840b009200748012404800201142da10341004d01003403880e001c5005120035640c5900441e00c40350050046401c955080001040e928410311180404500072442241d03540034500610003201c0c5240414640820030700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 607919919 1250 607918669 607918673
    0xc020606280b07080a1b030e04020a031d0703060b0a030b19090807060e060a02070f0b0402041103070e03070e220305040807080105010302120a0c060507020102030909042907050a03090c080105130c080a 88
    0x103201404441002c9e280103031034460001065004103c0b01c9240c84c182105503104810030070b000654101a0703486102c0c1403280324686001c1c070031502c80f140401050180d9480001c1d03044004840d03a840382d881c13805800300b098038840e2100c500990101d90150350705901c580b40c003000c503030382082055001040311604618004440d04d82c0546001c0003d0010043c1c183c0340302040940d500c58202e01c1d114485031010f80ea40b801d002ca000341c4034450760b80030789010740a0104001200900c0c603404900c900c103d0b80c9854000070703004043c1c0040740c0b2019030440500c2010300c40812001c808104040c080d0050000003d102d505500401045641c0310480d010207030300c4010101f00040394290b0180c1204e0171400c101d61259080e1005034198002d0421158020584030204014400381201080c10100d603810b201c2c5040e0000030314025248422600c00c030200f00c0402070311005038802c1e0301c00c200b52400f030220301000d240c03900b500c0e40c250785061f149106411406803060051100c059111b4004040c2c1000030300c4240010703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 607921169 1250 607919919 607919927
    0x20109121d150f0c39010305070804030f230912010603020d1b030803070f030e070609140103020d020c01021b0d140f070b18010c020606280b07080a1b03 67
    0x3070340c40c03071031440d000c1031070400d920040040d50840d5108020010402408000001d82c40c0005c503c4005079048242c812841540a13102e00c40c010580c960b10a0300c0795445031400e80f00014643c0d107940410801094580714000c00d103403000100c0303400001d11507807902290200b11640a41c2103000510764503181042005940d41d403614880164400410180380042407600f010b003e90b5a4406001040004100a000781d800b10340c2c0c007289d03031042d1820400300201d06881585d6507480e01546001c101d4442017407085099510b5400c80304401490003614114250a01d0303010b07a0801e41030b20469039008030300e922404a00b418030000d5851600e0040240040c150f200410040d103505400c45566000212140f4903280d410403200c40c59000006d42da46402d103014120308900a00408007055403038103810340c074581e2000c40c80c14000d5000a00c0c400420b800341c0b404103081d0949940d074400c005410007000880703440400c0034200d49030140e5006911489120b2016080180b000c18801c04100100403080000f600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 607922419 1250 607921169 607921177
    0x130c032406031d070608070305070e0907030506060912060f0136110a090906050d05070302270f0a1d03030a0e0102040f0b04051e030307030f020109121d15 68
    0x780386008145441c03550b84040d04151104000c0c069805200408030b109600702440502900035076504100c139944000007243d03040c2c0204850baa01500307000100e04002c0c480d8000c07903002030f00104a07a2405140400055018200407a40782a42c0c21440811000c407204160b070f03500600c04610749141d5031402c41e5a80c5840303404001d104441165202000c0c1d0610703102d601a07211902c1000ca03140e9150b600e07110180c1004400d104041001c1d08080d40820181041007452030780c954040000c0c41c005003541d080041100700040c030040b820300d17039a915010300b41030300c00c15900600301400c0d40c4440781069400001600c408051340740d100c010340c0760b2100046100008a0303500500e0400c00003a0502c0b03135031301980640305651100310703901041000456014544002002240d90486140203011540f600d260042044c030080194190018802c2001290040c58041d0b0071100074400020507921036030344c42c194451280c0110b000030b00074080280300c400d400d0101040d161411142c42001c0141e4420244c1c00d841 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 607923669 1250 607922419 607922429
    0x80a0809460b280f021e0a021009020d06181106030708071b0602031611070308041e080102030a0b040b0108060907050d0b09130201140703080103140c130c0324 70
    0x11001c100d4a03c01a0b00300300034010704032150180f00c03c900007180c1070061742042d110b0800204c0c01c804a0007814405104440b6030131456000b6085025941740c18a0040c83c00708016a00659503001c54400600c5c0d5100d600c0e641c200c41291b400c5050f8850404031002a8400c898500840040041c01616500214100d0307120502d89030880700c0007070b4514540381c40d401800c8001d00b168008420f01404c0018400e1200780c040643d6160840c14000040151ba1034400d840050150740007004140a50340b444080c040d00458040c5800c2030150713444000710300326441118503c802030b5664a911455152a01035403c1d41c00b000d18140c2e00c14244100000c24210001e442031060280000c2c00008144180c0c2101d80039400040441c003062404210004901c64100022400a41c440c11032421440e040016a9040c0350140d8400ca2281e0959840d041640c2010f003144a8501c90301c4c41c0c250642d03990030000c1c80d6420340382001049103405020040d041c2c411004c049012040c84442c403444807200480f08604942c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 607924919 1250 607923669 607923691
    0xe1b040510020f010c0206060310060f0e0603030f12061305040507150314010b0a03050c030106050a050a030e011d012f09040e060903041809080a0809460b 68
    0x24505100992400c3e0036038250000c1d40d401c02100744031032900496024443d08090f01079461a0820070107001c104c45060141c42601c42c0308090900c044102a002e09a021a02a08503454038441014070500ba4015100340486250b00d1703410044c803170800380d41c258590401c214080c00303241015903425842d00128001d000202c00d483d03d40720748e03540c8680c1046001c0c00b01400081403958452034150b8146c0d20802d03d0101281c180300205a61200326001c50381200c3c3e160342c03421305225040204443d1a070200c12402d08250b02c0e1080d08840500c20b10842e000c0318594602480b2041079480c1e11030a642c2d0342c0d8107a0441865515000c0707045142501c45030003441c11101602d035030346082000500280340c206810703007240c41a10104495140c0001c02001620540c80803640d00e9140c4c0a00c8109482c0700030801002200300740b05d81c0060728045c1c03221540015481040d10b011044080d005601a0303a05505411113041c190f0748003611490f2490a10b8400c0a00c406498080e80b03070780c807081c500d000051300601c010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 607926169 1250 607924919 607924939
    0x1021c120f060f0b0c0c0f010f080a110c01020c010b010203130e13050a0b0f06030a02010f231615060b121009290f10030e0102090d050102040e1b0405 66
    0x41e0704154003150150907039195501d152600e880103081c1da500001111322103407281c8541c4c260319241c140c0e510035001c41d05948010201000c008200d524403070140411070400e07100c14282c0c15501100e00603049141500c00010384130011158a5821340e50341460076415074000b0002d9260600607001d060b02690036000341c0c25490b449080b0045024400304101070058000d8105100412a0403040a400f03014a05660406601c40e4070030103860b02c80c1054001d003c2110b801280e0f08035401858450a0805207203606d589011a46a80b20300b20703840b00d0307640c8a1290b4140c1175582004503102e40c102c1d20840c11501001502d00b8020501c07040d12031441100e040d0b0700d1000001c1c407081060480301307000d0b0401c03040034061011a44106600e040d00d500816a105443e045580081c0c1030014001032006c80041803100048c030540b4040e40100000403092840f55000c200450240d08c5641e6510b034203071f204800040e66280741040c081e035400e1016050b0144117849521012500300b48005031025250101c40503d05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 607927419 1250 607926169 607926191
    0x30c1202070503090a0e0601140c0a120507050609033004110a1e0e0703020702011d0d0b040f03031103040c06050a030f05040f020405010605090a091a031b01021c12 72
    0x19501961300c035142d0009400402203109801c0250a50145000f80c0b40c1c0c10030b0740038103825618075000d4604c82c0318099105202d5100480ca01502240101441e420300300c5c41e2818585800d41003240403200c40741c451b4030000741c0f0140c0c8581d400d015403d8210040d0700f0440b1007144c0c0c004196081001c0e1010f4992000c801c09101565180704070b6000420240c1032008032010003504288501400d40314030010f90315440c00068200d402070080b40c2d901b0307505a54100300c0ca084624000c043c3e10400301c4040d04011078800c50710004414406442c0100d020b6550000240400d1500800341c2e034440210150003481170090200254141d00a00c069030f9540c01c01c40d848201d0010701318001d210400a20b0061400c0406001c103002640408540050080d5000d01c01b5a881d00e6040e10b0394070510340c01540142c01c00d5020008003071f1591201c10f1810703207407540d036004411400000340303899040c61100e030101d03003007006d8181c86607010451392a80ca000401114003d8a040c0d2014041420711501018034544892150300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 607928669 1250 607927419 607927423
    0x603090102040b0427140417040906061805030d09060c060f021b0c040213050603060a0510020325030f0e15191403041e151a010f030c12020705 63
    0x2018000900d501c0e615581c0da0a004451170150900c40303030106070a030025401d555140e0140d5000c5a4640015030f406c0d032a00c0d035400e401030800c103c1c03400c2614401d0101007104003990249400404095485036156401c4a000c40d03a05800e503413011703220f42d010b02003a500f40c0b07800c45000da003181c07114240b44803500f500d030400301c001d4440703014040b003007500c0010b01c903100007000ba8410000466420440b2082e00c9814203010032413140d8902009225800d00b41041203242590065a00ca000600300a80056503040443c0d00002244d0095001d600b0104018a60341d40070310091035400004003c2000b1481180c5000e880012102415400c018a10a00440c03603220400e040680b6035100d072900c0c0c0d0b02c03655a240007101d00801c204820000704058034401440480402f0703a80903542291814a661421002d0311140c0c60080c0740071100450f40310480c1c1c41c2c803401841142784a462003460640c0307410101c0c0005001854101180c07085c10729008110424507841080314007070410410005aa9480a090083c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 607929919 1250 607928669 607928677
    0x51605070812070c0308330d05010f02031b0304080d020706140901061406130603020715050c03060a050d110108090a060e010209031216080306011b111c0c050603090102 74
    0xc42c4500048042c41040c41d0311002d022011402641d0310091510344a00c0c20079480c4400359102141f80800c6450640c862a41074904520040204003003108035644da03845003034900d84161900c1596001c000c2052542210f410a4188034100c040ca03440d42c40c1c990340d226103d00640c0341c0c00d400c00c0e50104200003004416804014911070700211141940303000da4850f80030303010a00031510703181076421025a950504905840c01000060101488607043c008101c000790000303401a542c884002d14140c9040c150b62180394020002401480d0b03991522406000700d06025900080c050101d950280000c11201d0841d00c0b500c02d02460024803503181c6e03510282c0b0308029400060f09007890804581c2c0381901c158000e024004044c0d003550010009140890140d01442070ba1414022600c0408400510804002c55005405050030034002d080c1c49207030528940810000c45038001100148844c6151400020900e802c88081040f5030502e1503842c9800d41d105271003164000ea0000c030101e00d655500b034040e9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 607931169 1250 607929919 607929937
    0x2404140a0506070b0907090b060d09031403010f05010801270b121005010302100908030415021212070201060f0b0a0c050c0907081e04081605151302010806040516050708 74
    0x541e281c40c11030401c4010001d0039a4117080501c6400ca00081d0401c1da40184008298000d00041c03e0496120070300000e0040310408500b08261840243e0280031628003660113070120300c02c03c4414038103120014010981c10380009042c1c1150f050340e160040c036800420700b025002c0200102c2d46001600c0402e40d900c44c000700d8034180340202680b40d48080611b5118a04a038003c58075010340c107076800b03000d40b82c280c82d9025208150700104401e2280c988100b0340e04071003100c03e00c100d0307416410015580000d5044200b0b040d800c02e411400340321890f603090165501500e4002c03101c101a91800569034443d200d014184010300c16080c4002091140600c441c0c4440d400282204800d840d000310000c0c07000c04202d82016040d01501003a444a54070f040003d48907640c49413180b403400480304a40e4403000c4005000301c40c5407080881041000d4000d000860080b1100140c0300344046541c0b00160141d40000c0942e03010301d04d02000c2003100241c1640d07c4034112802e0400c00c0d51078907079040565191044035a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 607932419 1250 607931169 607931179
    0x402090d17070501050f0f07050c07030c150f0f201e0a030f0305040c0509061f050310090e06060f12070305030a0f02061e061306142404140a05 63
    0x1401022a20a0050414900c90740003007045e60b5a03407081601000c1c0642d0943c4148444800081c0001c0c0a44001c240c00c3c16685d08540b011075699549800d000000d0304800f40c0d080090902ca10995040854003180c1492428600001455031200a00140244084030b40d1180d00c0041a458100c00740841d9003190800491001050004844142d548103403510440016900c001200b800c14820706c184d83c02145d2202d43d00c000c00d03180c0800c100a40001601c003e03030103076203805040c00b40e000304405402821803540315a070b200c1c40e221384c03607017004036030350380540c0100341448009019018003185460740402c040301e94800d2000c4000100e41e003000b4020390031180d0300c1340b04030101c00c4c4080080a0880b02146070340728101615a41c4089840703280a8032450810381100d0386100c081c400c0341d40415032126000e0490034000024550b1203088c2c40c00b03684140804003242e9540740140c01c100041d0300508002c00c0350f600127101e0403145890148600e20403034001040b41c0301c8070351460341ca000d4510700416001380 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 607933669 1250 607932419 607932443
    0x140904150e06160801080712060504060608030d09030f0216090c1e05030411010309110f03010b131d03030907060815220506040b0a0b1b070321031404020402090d 71
    0x21003c204200340034a100402c6019000250320200000c0c0001070b02d01701c06400c54503035416a0752a01401c0090300071103540792204404100564204050480c0d9010401d0100f0507100e24103003d00316804031100c50781150802c121074840704590440800858030803640004030000c445101b147c00101e50340c134a050744460b40400424081d4020080d60045015100c1c0d04600e031a0307040150121140c4020003062240d00038013030042403400548a00703080401130004a5003000c100f00040204400c4039080c14115691401080308511014040c8140203000300114a141403c0140c990342c0c0304e4512400003080744002c00204804c0500c0042c0c00f540302d01810082102040d0410210704407000c6400704107040c541000120300786032a000f80200340c0030180c01542040d040140300401540800102d05401d0604050b101c000c510811941c0021070142c2c090780c003041410000d0100e122401e03141c200401d4240242d80c071400820486a940045d412180141d64121950100700c110581300c40240028440030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 607934919 1250 607933669 607933681
    0x8070c080f1b010f090b1309180507080105040b180f12040608090120090a0302150307110a030806060a122a180909051203041506140904150e06 63
    0x41c200b41c000742640c2c102c407001100c9001112a05441400360001980200c000c014468800005008010004074030f40d914071345032081d4400f610001c4200c040c0341f1810b00030307103c00e0041c02d0051340080e01200000344940d042c01d88842140c100094000b2240704001000301c60014000c10095506500704c0307080c0c40c03000101c50110703072564100e40302e84800b2460075000503107070050610520242c0c0e062074040070440c05010000c0303080c54010444542d040f540e00f14012015950b00e6031640010409204402e5583c40c00842c01401a6031180010480b40c2c083c45402c40000c1c1c100e40003607880f20043da101e075201d519001c4201d070f030100000b80f07080e00d40380780c400c01000c16107850004216480781503807180721000720f054048031102c0360003020176401e0700703008418480c200c42c503042500e04e28040c101300c03903146582552102c0303140e00c15101100c0d008404850b04900344024001c180040210041300e1144c110702d50042a4180c2000b080201003c10216905607451043d60010901c08561001c071070345840c1003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 607936169 1250 607934919 607934923
    0xf0106060915090e060102190602041d0c040504020304151503120203120f0c1c06050901091e0c0203130b0d0510050a0b0906040e070e041b050708070c080f 68
    0x40d00558000499034440403030310451448980240c08020f0307442540c8646010010340343d00360007406250450182c081110406803540c2c0510005a00503200140c0c0c461038480391014540c030700c2200c010070003c0c0f1400c00000c0b4100303c060f04c04681e0241c0d000f50742c0e80e58614226400343c541e800740041103854403c0500541210704448003c0e00d11a4080c3c580b603034442501640d407030150000303010b0800383d51400510140e0706400340a4019002e002c80318184400d04500b84003001d034840800900550300c020401c86403803e2010240108407003002000a90549085400b0000c003c040c440401511035030780e0400346100300300719045030528188844085480b010403001d01d9202200c030f40300040c1400c01040307411641800203000c5070b0f8010500f0901c145401030088603034024442059021406100004940b185961600d12513850303a135464071a4800002004211051784c08514800d00c402135100c0c50300b035044003c0f1070b0265080889651a088035180848041c095074000c12150300403940036030904000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 607937419 1250 607936169 607936181
    0x11030c0c070b0f1b070801110a0f090e0708071806030b01080a0c0e01110307150603120e10050c0c030d0c051b01020d05180307030503130e040b0114030f0f01 69
    0xd00c0c191407086948094a182c180202e04080c498500204a8440d14401080304104140d01050984202d240d40360341c03450858411042c101c0111100007104172031140e120107450001d450b1030500c0c1d0f0655003021014009810018502400d1012550218000c0740c0600080b4131018625010030007040c1c1c0f284001009411f20f048028041140c3c2030215426612900801c1480d444903070701e24041c50210801140d07c1c58451100c52000c0c0003c101040c0401c6140301c948007201d00d42100850304514628110400721b12481d81c0200300b04428072400c8407a03480290140c1c49603d81d140843e1a00b4a031b841d05420600100f04e8158135100e501c01070724441d9000010109004e00a800303690031007a078035100e00507030713240301e000e10340141c000840d480f19150003400548001d1523490070031b4603855185404280f4084039034106039441c0e130002c03483c1c4080d5000c520714040542940151210341d410030340d13107030148a00103004800a102002041e140c3e192000c00200c0070100d00d050860345038410354418603009004c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 607938669 1250 607937419 607937437
    0xc0904090c090606090e16050901110105150a1e23040623060301060806010f050702030d11100b06030402370302040501090207021c1b06020303101a1c11030c 69
    0x400d0300c1c1c000800c805001b00d014032408055201b41e1070001c000c0d5040303682c3c1d400032180b40d0502c042141d1010480109200d0300348a20106005000c2c0a480201080608005030b48410b4041404c0075010414a1203001c1d8801140c034044807000591000740c4081c001200303012482600b003442c185000400303071011450205a03c04d0b0101e00c803418000c180c1480541d210900515002c5040e10002c520154403c0180c00441030581c80e00f00d040558940c0000c0c02c041c1d4140f910800a108100d249641c400c0610090007104070f8600c2c108410036059021401c1408000e002038400c0c05140d58111500003046010380946510000c01c2090110303140c04100c4188540c00180d00541c601000410100080d1007120911600141103008000f62510700b202d00d40e850040403180070111a40403101c1801c804081005004c0a0300510b880b480c01040c0b201c00c1c8006035000c0a4440c1c00450030400c4495070800700c51059401e403c10409110703101001e08007030640c0701b0103000f20700800070400c140510400040c1403546 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 607939919 1250 607938669 607938677
    0x3030203010e010504060302240403060905100b0a08070e06060705161707060c0f061b11060603010605010f1103040e0a1406090408040902090a0806090a0512030f0c0904090c090606 79
    0x19884c1c0f000c2c0300440c1d01c40d02000750041c810650741d610f068014009030000c595144503243c80c090300c2e40d40b06800c0e55101d00040350745900c141a0000d6018450264070701d24402a5408241946086640c81e61034000e4802d48500c0c0000d00049520390b00c44400311106283c2080880b101c610007403059080c82141c5100d004a011007a0140b40030189000c102c0c8400c4603160b5a034036034900c0e0540c603007420919250704100d40c071a40e83c005540f910881c1001007207400100e0b84a164960700d0b014461410102c006040a00c03c0c5d00d0480284226a00400c102c0c009145502c0d081d1003d0ac80c041000d803452140b130700021349048043c0c0802c240380d18582c22205195600210107007041e1038610030300101242c180c400070600c1d40d042c8018855010a58058650a1002400841c00564480c0118200701059400352070307540004a100c0180a401c01001c00170f801c00c680806d19610b05040360141c40c87c0084d20002521100140d0034031641d490384c0064411a0b00441c00003099a994480c4d440200100d1054001007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 607941169 1250 607939919 607939921
    0xd210f090801060b0a0806010219151410030b04050a14210c1c090b07060e0c060307140702180f0703051006092c09060406062309040212030703030203010e 68
    0xe01e041c0a0101111001c42030342d824103a00031020fa0702c602c00180701d9411807103124180303802e00422602d40020a40106c1401c0341040d401c00d004801c1d240031540c00300d00d4800740c0c42030014000225090200b140d401001d030711300940722880c0060402041420140900440c03105000c542c80c40810601c0090480602140c20300c0c07883d4409581601034440f40d81d48a0300f001e101000c0c0306803824101c2d601e02c0480d142007034490b0745440e0110b80c41e4101c4881030b01c10a565444540a04400b0040006d04c0358084805504600e4186001050748151805841c03030980702140d11000c6441d00103140305110900c0f590304109240100c1d007110380b0b400895402001074200f00100e1a401d00b100380c0d100580300c8581d50041139500348040038120304c01607980c0e40c480c20000d078050003401b500d0312440b41c01810800003a00c194145030406e001a100d941d0880e01071380000402d20509170340310380c0603032144031005c0d84d070202140c0c0c0b035000252700002c08002c204510302000a88400309076140d4010341c180c40610f4036004607 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 607942419 1250 607941169 607941179
    0x8010b0d03020c090c0408070b09100302040b0403290a0e07050a0b090d1104092907090e1302060a0528080c0c07080a0803150103050c090d210f09 64
    0x440400500080e0242e04003d100d00c010742440500c9650241031422042d20700b5503030740552803038600603034041c0301604800304806426150488d035101100441e860b055040070b0400700d855003a031190744001000401000400d4440410079126990042c000e042c900302180ba0210192014080d001c001208078028028080f03104e203800701c0000e0a54080c040c4050034403401d442401030900810005481c41408184907012664542c0540c1d0b5005104000c00400d0b444480c40c0c505480d2070751220041460100130804c10ba60f0780c4100000219400d640221880d138644a250010014980304040e4010700002850840c0580000003410003200c040c50b0b50160032203031382c980c0d143d11544207850f00c0018682c10100b5407600c1c1c0500581030490003c8c00f034420b11950f4404052518207640c2084684480c080304000c41d140340040d106a00c0c1400b820244801e1400300c20444051041c03500709407060201003110b0092110b20107800d1708200100115094110821602034100c116140414001507820600495 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 607943669 1250 607942419 607942429
    0x5070605090a20060c010e0309090a0612022b060203010510141227060106080c09010c15060915030501050601050a0807030c0c0510050609070e0a0509100803030a0608010b 75
    0xb5038240c02c450f03881c0c0e8202c0d035000960420051890342e254009000d024000d40044e080c400c60300c94105040046680f03400ca00c051180c6030748014508400985090001c00c0388040e000f180d0307218103a04980e80e03403000c01103184200d003080d160440604050043c0580d0340c1003041560007541070b07400440b800200d01165100464520f420845031440032274061141074085041c00341c0700c0340c0050803201802a4441413102c100c800040ca403c6c01840b076446080100100d40d00f203820550421b482000031894940d21100280c9030707081c0c840c0010846000000d180c07115003259032150303018190030201405158048060148542801e005c142c0f100d511303000c00320301158004c2c003c48101d4091900c0d0f000c15a645d000f811340081c031003400d82030180107441d449000000c40a100301c2c0000c2d24055800243c0381480c2c4103101d03d845c1d00500100038060416005410380d41c9800400e021540c049a4440465507440090302c00001d09a010180d184030101c00e004100302e10b90000c03410389103050020441c111411007002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 607944919 1250 607943669 607943683
    0x1b2906120d0905060d09050d0c0c09110a0f030e010903020c090c0405090408030415110d060b1c05060301020403020a030f05101a091b0a110c0a140607051207030507060509 75
    0x2801103440b014082002d41490800740c6848404110700145009450b12134505000c46aa191030026400395000b000f0000c0c40c00004c0050004007404200d000c4482421480d240b1564080200348480d0420f00504c0d00d2103500710120942c040390091198406a15000e5036a00013440c2c00d510403500100003419011510080c1d070202c400c010500c990b9900c9030b0320703010029440900107950707640d5058682d00400d17449028038080022903828a941e1002c855031f4074030403a0690707003022044000400100319207501d0064240045e88500100241170b440f1440081d0081c492640000c2d0895030201c00001442021001135440d40d00075020386d0603086041c400c4c042142d20390401400d06084140080c2e5070307410b01718095503008960040032603c8050a5815075981d41203012000002642c0c038000c03121066080c055084242819507040c0d901c6800c0c81c9425000307608100100380600004503801c424404d00304000d00345801d008441680d41c3c1c0c1c8a00f0b00404c0d82d440004252506420030012404102c4001065 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 607946169 1250 607944919 607944943
    0xe0a050106120c081222120b010e060906130e0a15290612060301090b04080307031a0f0d031403070e10170a11040b04080309100f1b290612 61
    0x14a406d506501d4001d046016140d0b0601e1540003840101d000b441340040c034a0301034060034180c100c542c9051060102200e0043c0824003884500c000e002084e101c804000241080d00078010a404854480543c54030041d07140141501c80c000c0320004009907264091500d2841071041c1c0700502c0000c207a1071034815800940341d90408420000c81c20f03a1305d41c02c5001e680114005002042d040407544802d00b6841050310203680e40c0d0400410f00405903014812a120b400020f00b05200d8800804001421200211001800b59298000840070548900e000c02e0b461034020f22000c3d16030078401c00040ca410348510000b40648805880d010780540200d484841b1016611040c048039a2410b8100018103080070342d04d0080c0000b0301010604135152800340c006448100c0c006c540700c5451a0420091800304c19450b0f0a204018014141c05513018801d03c1078000b000d07010f0070580110380380152031220181080100e81c4407404c210541103d8420b600c5004290403101214500c140c813004a8a42d0166210 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 607947419 1250 607946169 607946203
    0x10e1b0d020a33020a0210030e16151704061d0a050105040302010501050f100f1407030509090a0207050706050a1209050f060c180f03030f030c07140c060406030e0a050106120c08 78
    0x405d000500e0308100001c814605480c01207548201c0a01451500003041c006c2009602542d006001c0c05441c1400345004401c50300e4490280b01c9601c002581d88807021f4006400c154403603142c10401013220110380c1040000350304603440d5504074241203000b0030054030110015420100005904c0c83c00030414040781c14024840020105010005d4a0034082e0080840a01c0240000c0910300c03d00ea00203087d00314043c0d200c05a03545040420030890010081c02085520302c18048240842c10004a400c02d40c0c00c0d40c03e01581e07801d1101000e491140390100d42154150900760940108200480c410700c500c255081111311644031200d00500b10300602d200703004c03560f5140f000441c2c07600e8840a41542350401800380c91a100c40040e010881e03500072a0050005040055400d0401004000780c0001c4051400908044a600000940c00740b007540b00f0f000401d038a4007072000c1245018840e0102c0103908c0802000140d6a42c1960804198004400d41e03031049070a40c001003090010807104401244440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 607948669 1250 607947419 607947433
    0x80304060c0518010e030a240b060c0a03050c0102091314060906030d0e01050c030703020717010b0603040210120903030c0f081e1b0a02070512010e1b0d020a3302 71
    0x441d185001c00c105c96600d4491081400d010684084941406c4102d8800d2185c00342088541442a95910b00e6140d000745070070440b40745229004145080c4069061509554030203014040b580a8001c2064050b0300c0042c020104902070203a50081030802038800c800407043d9981420407511040854100e81c15810100844c00e419100e600320544104050400c0760902ea0400d81061542c0c204034012000351780700e8081400406070a180010340120020b000307002a44400c004141360b400702a200074001d40c40c0c41030402c041409000b08030408460100c08020380506810024054480340404030003083d1980314150300302c0d10580080340314030300c0540394500e40b103060305a524031800002d02c030340407080402044401c61281c050003084010119401498160304000411090400054241a2980c9400c402840d0500042483e0041c00301030305940d590b5010302d00120705030303400e2610029444219001c02140647c100b00c21100b0103030304540190701381c000080d850305082d001c810055003d84d0100c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 607949919 1250 607948669 607948717
    0x20f01051602242122032f150109090b131a04060b0a121a060301060801060602010203190e060a020706091709190605040b180d080304060c05 62
    0x58002150784240031103e020800e820200911107802000545a0703401c100c6044044003183ca00b1000c0e008514415400d01c092080b140d18010035220540003000e1081c03900700340702c02c0010340030100c502c41400034500c24981e48070301c42c05884001e00241301100100c00030010030944024403032401840da1102c2c040d40d0342d0b110342040420011030324008840a0312180c0c4200b82c0c140030041841d0107284034420101d980e407000420805060710507001416002501c0c04030b4000300340078231042c046408184e4050140c544031400803901500d500d4014109642c284040042c01c00e605600440c0320703010b01543c0802c2d420828061a01741c449000c40c051195100c00042441c01d007250780108817440c802e0000003210910395817001c1103d420041e44400215000c00d544046092600f41c142034848914080380040e424900050810b0040c0d0140388490200030451101d031b0b0b00c200c4280d0548407002020032901c40c241c0d28005905600858048907010f050018501e0960b004d00255082c1000d543d00d41000c5070124 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 607951169 1250 607949919 607949929
    0x603020a0e0a0f111b03040504021908010902030606040603092303041a0c0a02130b0a03080703080a0c081302041104081f0c08070309021309060e0d08010b0d1119020307020f01051602 80
    0x4040000680d006c1080700161a0b62588014038100110f0584501d03a01c443c9074020f800c6c035034144e001020b541d00420402005903182000c860580f081424002001002424001c1c4650905044c180039102008050307141103d0000c080c00481f940640001003408030394000094a00404404501d585d0108d001500145018000c1c1c1c5181c12815100084102402d800074845a00e294016202c0b5500080c4103000e0583c0684440e038000c0761070000340310004004900600248000b04004541c55202c420a0115502c0b60066402054640c03440c1380c5a54440f0110b0307440e017441103070170f254052195030302c58241c000a005950118005032241e0706140e0b5905030a402a1001c0d00c1e04a03409058080ea00c00004040c2c41403003d00350046400095065074001982d14214101000310b0500c1040001000728114000c11681c508560b10b1002c143c0340b4000070a41158000d0410403154400c80e0303901d002c0c0f49039001025001c800e00131105101c0da00040001540c3c1032103041030341c0112491180585001d8106 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 607952419 1250 607951169 607951207
    0x203010f0b19243b010503090a030302090d02030a0b060a050102060702280b10060806060909160203070b040f03020114190b030c2e0807080f0a0603020a0e0a0f11 71
    0x2607042060b030344040070404a1907100104e0124251902140d40441440d03440301c01d280c071643c028282180b07103081070f0b100580e81d003e800c1d1004041580000e010080c540f40d0b0a01e4a400607030144c11600d5000c0c0620384503c040d54100c0700c1501400c2c2c032002c001520740c400a419030091510f900640007500002001a1105044100d031350000f895002480c000920303001c03100b910900c7c041440030800b83c1040001040300202810807031140b8004c0c0100c0700f483e919200041c1d001002404d00c082d002440c82e00580c118061820080c1040c1b150404020921074070f0a00c0e140711610aa00800158242e980000d0009005843d10101341000501540440503158800d20046100604a0300004840c200045584003883c0c8400180700000100214410380e030001601c07101c1140c1000c2e011403801c2807008001e100020040800620008041401441250300c954044e41d00940023800043d00c0b15040170b0b09150a41b0402c501d00d1901c030003412404090311400304024290b0b88211710b0480f10b05010300301109 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 607953669 1250 607952419 607952489
    0xe01020306060324150a09050307180f060e0f04050d09030c120201031407020a110a030503030c1c050708061002060c0306130e0706110607020a08041a070203010f0b19 73
    0x9071240b000320713a5540ca20014403d00e140d02c07082c13684d950111900030b06582c02688200c0c065030021304244040300c40450814103802d480c48001036407a42941c5c000c07021780f84039401410804030440901400310040c01040d0700c19030007541154106180c00314100e0311854148409003003030142280602c6908503140340710710418014500461031710707103100c111146140151a450302581c01102030307108000c00c4092444283d88100e801140302e92441c1c0f1000d07181c1c0300007000660030b00c000003a145859658001c00012031901c003d01080649007442e00038140c04400d8800e80e11460600c50b91110329480002c045115000c031a00c50f03800e517180c090a008240200e110310810564840d100b1540c01d5400f0420794001784025035130020f0240d101d031007031410243c01405110464202a010501240701042100c003147e103500460309416203040d061805034020081c0096265081c0050f180e010320044d0850140642c0445850041181070100310300c87c0c1d5014810042d119820b050004100c030142c1c0010440b50f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 607954919 1250 607953669 607953721
    0x610050a0303030c110708010e07080a0b06190b0d020706050f100b0a051b060709380d051905061c020603070309021002010603031806022a0d060605040e010203060603 73
    0x170384054510f4100340c4290415180c0d40e6450122540482007000300e800149010300c003816040100da110ba45908200401c228040c1e44100680c1c40300404000048000384207041030280c0303032030000410030065484901c1c00d031035507800c09011801081416040900801e81000001c60103490901c4100d00c907042000c03840c007400014042d0b01c0c01c64400c00d10707945007000d0b0600542034903d000000507004411542180038107424003440d0740c219034400460f201040061039010f0180c43d50029480c840d030301c100c4101410480c100b105101c0021100c2d08402908061a50207005a66401c4180b04c0000c5a14881842c0d4034842d000110141c144a4011600b140e118030700482c440780d1680102e10003080c039030010310040c0e640d000104145a0f00c0704884450f43c90030a091040d852030040000d40c0d49046441040c198a4403c16007130701c40007107400c4c0390560351000d46500020081401c102000304480c0c030038070740268104403045441d4a4107208503840366400400c034505540710b90308600340464020101e00d40131 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 607956169 1250 607954919 607954937
    0x606100e1e060708091305091f060b0a0c06062103080903040801021603080601080c040b0a021f1d01090308040f1e08040303110f060a11040f080c030610050a0303030c 73
    0x15182c04000f410a0340c000c10381d440e0344601032403d000882c19581840365144e445c01007071005290011902d9040c1c07210140c0c181a0769191818400000d0039240c0c802c0d007a00c00c0029103c0c00c6580c02c00304801030325024000810900b40e542e11118a1171304e001004007412029801da10b00083c0c080c540403900b00b44820101c0341056152600103089038480000200c02804c80c038a441c0405a02a07200340d032020080c13804c01da413420100050712640c0518007590b640d0796000718203032a515100704400d405006c130301d80540c01e04d40e246803807290013820081c1a41480c03550400740c00ba0503603030500407071090903810364609101e55500c0e298074180120030041114042120540406c2d03560300c08980d0301440c1c0c000d84295036200c0c82c62a028140c022554640000c90b0404070500c1020b06003c100c1c15405500711a021600898421138140140706540160803030800000001c59403030000118081103440c141c044504546030801c0f62440e91085200e110362000c10380c8002c1c40003e12917000a061a90141822004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 607957419 1250 607956169 607956229
    0x1602030403050a11090a1e0504050115060e01112a0d080a080f01060206240411030f041b0f06030b0105091e01021c0c1b030c03030305090606100e 64
    0x10181d0f086403c3d0740601c802a00c2e68440e142c114200e9410205a0500f04402288041016014240860f00003034030b50351100010f003030010a4110301c0d020002000400b1500f5145e110241a040c41030143c10b00046100c484001c10020004118080c0542e4a04070401c04089801c6929034003802003019800500410040f40098100d902903d80340420b038072600702c6440d000d02002c5000405921170803c6500c40001d01500b40002101c800306141c3e040c0c00f002071000683e001c034018124142d0607500b000d030000b08008039042140503e9000718072031450445409190141510820f00394016001480000c9001b00005802903020504100c01070420301d041c0007001c0001108011007415070040010b5440d0104010369061202000780c82d48901240500501408010000c011a1900501a52051000248103650309070303103500030356102070308921342502c0c2d10b0000c5c00303080143d0b500240f52094502003102454500000c041c81c1a080d580e406d1810960340c1080040d203146400c210380240501140301c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 607958669 1250 607957419 607957423
    0x180f040e07090b190605070b0a1d01050a0e0a0305030a1e06090e060105041e0e0f010c0c0309050f01080c0313020a0b090f04091110050f0d05010e1608160203040305 72
    0x140401280083e0562081c801e210302c1280b9001c00340d4504024030000d00c032540c0c20038290792506030000c902c25120766400e41040010a408a0340c1c84884048407a64281000150080340c42a2190304040c0000305c8603114050759541c0c2c960f8000d000c9030003400012400d00303240c1d1003141181d4220410390044907109d040e00c811115142c204445494031b440030540240400c000301e070f0050170203980400644400d401c04411511444024500003603e5408480c0f90440820015061500070802006041700004028280c800031140407404541c1800d40001c6924144600b4503401d8410f03107458806541d5442c3e42c01156000502c0802c0040c00061140f02685032010038402500e0350314800c6958420400c1048046644051114403450428500e880000c12400c180d50182c0d4040c1c615a10402007090300f41c0d16070140a8090081c00d802049444030f4604c1e6401a82c100d410109090f4595283c6840c0c00070054002890000420050008602481c071001090b00340250244140d038282a12540c03568 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 607959919 1250 607958669 607958683
    0x1231005070203061503190f0602030c041e080613061b120e030924040902070c14010507120f02070504050c040e061912030512041a060402180f040e 65
    0xa000210042500400c508003002215000200800d880f00c2007a490000643c1c0c3d10f2040046080755861606040100301c07503d11458405075000e00195100e190800800390749070811b10450306022501e040403c0c1d07115000c80c0da00c1c2138840c1203014040700e51703e004c044900014160400c85440b0707924444580700207078100700d8a81010107a694041186101045030098039140031000b816504200203079061681d0365035142d441811141300c40c61031402811034000079802141d000441d0fa50000920608100a80030706c2000e45d442020901c0c104113001c401180c4901582c400141020305444070500654002e120f40c4180c0b90382841286c80c05a02d410214058540649150520602c040b5060250401c00d5241d039600000c1a41c03503da00d002c0c01030359001e00300c86c14032a00c002210b07540e01010071301d4400c000300c03071180d112038071014030fa402c1c585011201c1c41e011208103070103140600081881c41c81e2600898906070701d8408100e4800380440108038a56003250304207607005682d4034281403901d400b48224 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 607961169 1250 607959919 607959949
    0xa020f091c03110706050304020405041a01080a0204050c030103030806220207030206040210180e0a0219020d0e040b0a0b090301020d05101a0a08130c03020306010801020406031a010203030123 84
    0x1aa00306001e500e000340c01c140101e030022030980c1240109014807135025040c2c0303500640444010507180c54030f00301140d4081d1001204a61061500c0001c56416000501d12400910030390b802c0002c2c1d0b40d09011082c0c940801e0200074001404580810800d1900103070204404401c002a0300c900c0120400d010104d0313000d15411009600b040c420803040d442c00d412710042d81080da0400050700942c1166841440c1000d000340c4107034161300740102e4401c4510b581910b42441442c400e28600c5010958044c0d550003062020740c000400b101101c0720300e410a4011030700030f0b10010b0281030b01c0d01c0c20001407116a4008650041e0550350034880458404228010180220042c00310f0640c418104240300c0341b084000780c2c054a0f0740e8010001e56400304e40c802030803617003d5445c98000d8181d81c2c4a15006602d0703c00d1f070340b0181d03051148200120390594190300810841c0c0c4c8d691000c000c0d254404080000041c2a555004d0150b00207000400507841400040492006008d14550f100a500d01c0000d98681c803000036 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 607962419 1250 607961169 607961209
    0x30f020709050a060305070909020f0105130f230a180c02030f0427020f0706180611271e060d05010f1502031602211002070203070b0f030a020f09 64
    0x820014801b050003101701900c8000380038862030700f83d030700803d203140f80c8d440d5103e0400a000038000d602d000c50b404090094075400b00000003040d0340c1e400075035554400c0204195112400c5856411924281101c0340840e60040d440d00311640c0d40c55804030041c080c803911304096002c208041c02e00c002198004101600451540d0382424a0030707200d0500c5a0310394000d5400e014810040c08051044203030603541150781c07060011890000c030691518103102c0740740c001012603003080182c07040240a140038005500e0f42d0b05030368440f410f22400340c0b005600c01c101040d401280301030100c0d1003008450746000d02e0104c05800782e4644609504290200ca009070712400000e4241c00c4144895070109905686449891008504000c02c50744661055400644000e00c03d00307110140300610041e80d158154000c071800b007580c01c203658004844d8041d52260398100c0c400e00401001045a02814080e50075060f01c00c5203d0f815540c0b81d402c2070000390320009402c2000002404014515901c81316a000c412240c210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 607963669 1250 607962419 607962431
    0x12030a060f1e08070b040b09010905101d03030901091802040312050a030b011403070305041e030801050307080f030f0d0609091b0905060f1302092710060c030f020709050a 75
    0x300c205140d500d5040403543d40c0000408020626420042c0d038141c800c42c074580c5030f5584000380141e9184880342d200030b41196200d06d80c03400e25070300070140041003075080c0d40645861041c001096182d05c242d859031804185034840501c40982035295136600008002c0006103000d80f01d0721141c0481c10ba18011100060000828007e0568140101d0810303081c20f0030b141c0c1140402180d44185c0707000040007e0704055541c00007400784042428407040751002040107240030f640ca400c004191000c00d0040c180288200c10700003030313088400104285140036400145040c6140d0041a8807107a00c9580f00c0f4601c1500d5480204a0f07121900ca84001c25204900165130400003615211302900e541d4003c0200e540b4000411080341c80c1c9259084004504507510500790003054503000080c0100035401e41c010180c0e140c0d1540200340300c9a0040c46d20711180409059a491580d0842007155500540001401003180000080e01074008000010050b0050755411a00c6900e01030495074115802014141ca9072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 607964919 1250 607963669 607963709
    0x90303010f151d21010209030106050d0320070504360302120702130203161d01020c060903030706110301140405060306060d0213020304050a02090f04020312030a060f 73
    0x418110010164581d00709091141e0510103811003018655240c88000311008081c0315070f486400003413042a90400c007a0b0066000c050445c000e4108540180c042d600e0a100418140707899042440c5213a030603130b250100041c0c0203010000f04402c20450950920440c200402c2c140c2d15405295005100b8a02001310032482c161190b0403400084820343e402507004900c0000b2a0740840c9076203101951043c6182d55010600c08160341c005a000d00e23003113407032004c810b006410480d020f035003100900c83e07503c0b03050480201b0b008107442e0710300206050150380203201c000c041d03003800d10140c465800002c1c2604c1c00d2400030780702c00342a6410b007085c81d4440e071000001407110300050b0001c0080c9a0040da402c03c498501000440c1c1e581ca809407000344a40c1f800d6100300c085503035503e03032034600f41c0b00113100790349a0a10303280069854280042c205e214031400000107503905d40c4c0300311161140f80c0040060801580440780d0f40100d602c09024909101d1b00d40e140072980c0c0242c2886c0314024050340003100b60b000000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 607966169 1250 607964919 607964939
    0x31e0a0605010b270d0510060303180e0a110f030916082409010e0d030f110306030a0b102102121917040e13060e06130303091a09030301 60
    0x1600f144030701020034040502070080041c82c8003001101070401810014200c00095075100003d0801021403003180c01548a00c1017030b41200003101d110344c4603d003241d048080c1c00030586010f40100100158a000016000c02042e00710740310400100304028684480302032000d185038412030b10420650700881c0614207200c194400c041c02460101c1c0a41a03603039590621219083c4811116041000c0100201d40a20401e50000c440100610205c4104081503580500544280b00807200661b1030032004001d10006541240e20611000703000d4241c0342415a24001d0244025085842c0c800602c0404690503501c2803a00d2280b808100300d540f0100150302c1001088201104181e040307810046520001052928400c400a64400d184940305562840b1844ac0e40c040c5034820120000c0701401d1050b4404041c00d1200654028102807190403003c40c45995500c02c2620209440d152040321440072a00c698480154607200352180341c0103c001e03890765020404181e8100d131881e003001004121352491 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 607967419 1250 607966169 607966171
    0x904111908060f010324060f0809070f120311030406050702120c010219080d020a030204080129061b060108160f06080c0a02010209030a051f06030c05040209031e0a0605 74
    0x40d03261200d02442c1050204000c8400340440d50f050544488401444000344088260400c60103014020200d60f5031030004c0c0800003007000507020585403070100d20303100d0000c540310090301e02d19500540c50526048098101e001248020b0301001580d81c850320400106100401c02000d0b141e4900d40c80e8480f070700402c210344880f20301040c900d03800095441c1d40350b40c000c140100408102c051003426100c1c20705000066100e6858074603500c900c001111031140e501039026005a0303000302d000300483d02c126442c1d0f44c50600c85605800c1081401d000f8500180340c1a0002c0c85000300100c040e10304d0010500d846840c01d2001c1e00540c1540d0401504103001c1c03442140c0b400014144100c000684500c0c0c090060710702da0b000341000e4140e56000504004e6107000f50122200b1800c0a02102c00c0b01e806424945c1d155561014404e2484000b40814a0002d50034003444003aa6007100d07220311040d144c0010007000f50b000919054160080b4401e9194624048000300c00c510711304000b4100728411441c0c01c40031140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 607968669 1250 607967419 607967467
    0x14010e101107050a18020f0d06030f0b0606130902090616080307031401030b04030804080702030a03020a02100e0a0933030506060a0b0d0507230c100908070609020105090411 76
    0xb40c90004004d4a20070340711800d6084545e400c016940c01c460f58010079144900c480e9512038a0810300000301300818034540d581c03650301604180219440e1078040008a206070140a521b140301244284124002c2d60f00a10001800411032890503003070f107044010042c0a41410b58990501008000ca19900741c012210410b4448491035215030641e56142040c0300094006002c0165000006041014240c112409035800400301c4028200340c0c070b40295600e10303e100c201c0c0203152a5a018240c14000c80860304070242c01440241c1040c1000c11040040411500035002551141c190b01107240100400304080840703000309020150550412610704200030300740a000d102d0441c001c0021400300000c3d00c3d001070042c040411582c494000031107a1002c90440300e05880603203c600d01e548646400144505400c10082d00c40c2240c100f00064200d600c8418040c1138890104035000006610350300516a41d841414940c2c1464640030101c0c0442d641101800000c000001c1e142d51401809038002c0c0c10b1342 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 607969919 1250 607968669 607968679
    0xf2a0604030206070618240b03010506030a030825020307030306080303010e0f091507020307110a1512020f0a0309060f092103141509070503070914010e10110705 71
    0xd461580424001e1254500c0507008603603c40700c0182e001901c41c2c58254058000f811811400101845105640c41c070380916111303280f900f0702040407800d0601403184103442c010046c103008040d68030140c800e52401000d03a034a00405a481c0c08400e4805613030101c010140e5030003543c031400a4507025045401c1c0c0e8000c400c8035442880104101d98000030305a9104640d010360101030303100d842403103150456a280800242c10b030001000541d80c1c1c000050705403140286c2031004224550028043c00d0f00300c9001c0d20111400018407ca4101c2c080c50a000040c00880300040c0b40c0070314440c00b5450b607007201030402d00003901ca00389901800120b005d0044002d41340c0d501005440c00998859071440b5008403c440d03002c00b203410078001d081c002d61101c1010400d181c181c50032807800b0307414010941803180e141845170100d035000c1000b8a10034000d4034031841d485c3e2101c03180c4c9820301120090042d10601118100880c209810710103844030011035001001a480f90b0050401c0e000b0f2a904210507600035034051 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 607971169 1250 607969919 607969927
    0xc0303030501030326070c05030c0604060515120d05091c0506190b010c1112030d1d06010b0d180819021b010504350a0c060509010c030305090f2a06 65
    0xc0f0a85c25031140c1c04c007030b480c10481549201c51070801e003540207001885840c0d0080364100030502c40365800507480364117584d030340d503038034024400400203a80c0190801d00b04540c801c2c4c0c080314000d0b004000510381a2802060f810706402510203d55900e4103e2004903043d810050500403890860b90881c0c1c902280a4024040802c0c07500c002080c0d06c8001c2c5020b018421904403031189034903101441c002d241c44450941c1d541d404010043d40151138210b8040440c04611540065a48000b1136040e060340c2a01f0407403840c5c04696207206002d00b4012100103000003403a8007003030000300054018080c1d030185028004141094500290501000c400030b1044541001c42000709070303901c07100300c4041e10a5070301e0b65030000c40c6420112102d404500e90300c4400b100146c00303038030301c03803000041c8843c419200d6030b134080940b9114034044400f40226010b08d40456650300c040c100280c041d80146a001c2100011a4038500c88581c0052900600050120307100499100555a40d142118543c1c281718040e6500c600e8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 607972419 1250 607971169 607971227
    0x301230607051b0109090f02071106070c030b06040209090703090204140105100c11042301050d0803010527070f02010b0a0602070e090a2f041b1101090c03030305010303 74
    0xa0b0300303c0c81401c14000c400c0c40303042021a07004009900c0a00300e850b8040041a5240204070000e40c003519042e9154100000b40d19594500102200d404035440b04c1801c0496296684e20221b400c000703040e4541c415020b01000f0001d441b13550f8210301c02d444503079004ca0300c42c5250040c07001321500e00c490000f245801c580103105580740e54000c600709164514022a0180c02d50400054a442d010710307140d4040d0030003461a481d01100410507400d50002d0b0318541c0141d0b0781d07004005840d00c01000007000010181300410041c80d0070518043d0300c6000c010f08000215402c110211700a201311010300100d01d1000b020b0782d500e40d0910a0941c035290a41d091030340d4a08014020350f80303161910801500003081c40014011300001d224000001c0e900004103081c038030b4403070424000715228204180c21741c07040058a560303d19180c054800030059141c07003c0c42400c640c820884007188001c13014051b40d074841030034800290504290740011806070360005034950661030000c00c060000940101d2800b110003074100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 607973669 1250 607972419 607972423
    0x51003050c0d03051b03040e180d0f0507050d090f090501120b09070b0309010204140d0f110103060b030c0403170c061f0305030a08090105090f030726030123060705 72
    0xc1d9841141d4050502c402c514040350f03240320300c054200e5044240c0035089101e0b400040a40141e42c04440160881e0744c1e005d08450a0321480c0c0c80c0080250302034405407c040707028400c40c0da0340381400d203000c0d40b0740b4a80e07031070705450900382d44000c600084201c4020002030392a02031100241984003400e211651400328101d4590344401405400e000145002c95400362041101e00d009085030032061b42c99150002d1030b02d000350800c0c031461b60b0404142c80210254603000c0980262951300c102c1d01903610403691204d44040d00542d070454149582c40c0300c00305aa080200240d8481e00000b50000e5132181145000040e003044000c01d0729031b03440280700c0b10100c02c00114186c0d91254200350010304880c0e48182d200c040c1045940b0241c0300d03000014039a2085603010911502c0b40031769100074403658071103504040d541c01110a0020355900140005000034428850219440d41c00a00c4085014441d4164004550081c1e000290300155101a0f8219071040d54a038081000c04540745414200951101c907 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 607974919 1250 607973669 607973683
    0xf0a08040c0902090a090b0a15082203051c02040f12060c0302040308040b0a03020909040b06090106050a0203120612150f0a02090a09090f1b1a03010308120c0d05041505100305 77
    0x840c030a92100390216560b05c541075a00c0c0105409d4041154110710840d0250409a064541180741030340d900040c186450012010302d5000d034565145850000d1035a031405401c8201d01980149a40030840000d01c3e400490100010b0f2040c4903003083c0ca151103141940444030b0f2115500145801032200b0000324810200b44c1d001c80e50b251074415076400400d041103000740704106519621107280fa0a21050000c8000c580388102c80c05c0d5501d00c007590700c40d002074400c2d0084621800050340300304010382c0c898800c00b624503081100580801ea030303010a0010541041c95003501e46201d140194104202c140c52403031a00e8110800e01000c528150004000c61200c08030b6000d4541d00c1912161041d0800c2110f036160018150400884440e08082d402901c0001c03c039403080c2603110074807004000c0110742e00800c03a4100c3c0e60045030103140980016100340c1044009081042120742400a0400480b507405032030700c00d034440d44503000701100c5010160101d6801412407c0343d580e034640140000b4200207905 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 607976169 1250 607974919 607974929
    0x160806090c0913061104030b01052e03020c0c1201020c06011202010e090c07140303010f1a0d050622060e0702030a02060a0b28080d110a0f080f0a08040c0902090a 71
    0x43d01800e400c030f051880c0981843c03c200002d0704000240002440b001c080c050341a603004803541c03c4039242c03050140d010880d012024010010380003052524040c000d034010301007030404c1000c0d41c000c0348035403002504611318184080746603500052401c40112003401050301502e039181f03480c00c01ea6100e8000820b441a0f02103490700519140022411829038142950714466004420342102c440f0800c01c0c0d52039800030b105500e60f40c3c103404804103550a107800025400503410342c1c00e030308004810303d580010308000381c0350b150440000550791504400856412009011031000805e600b440c14100089011f401000001150810321080c42583d90206480703070009854130020401d60b41403030000d861141040304404184002c0404507290031030f1104020210740502081d20414400076030700f0345001443c002d09103420340001001c0030010b50a0310941c5c248a005400e958140848211030382c405030b1003020000040703111a81048100203091481e20094180300301c040d41000d00e802e0108400001600803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 607977419 1250 607976169 607976191
    0x10c17090309060325020a060c020718050411030f0604110109050d03030b030c060d1e092301020909040506060a0f0803042709030f0e060f04120f05160806090c09 71
    0x4112203201e01c6402c945c65000250b41ca140b03520410101a641d240004421540307141460b07038400d0828000b08204e021504255401080d42d205280c03860002e02006004951190b0000b0b0868041e0701d0400420110225803001022941010304010503100500703003885040000c225801d021030340700c4003982c1074065410300740841e02c40e000c0c4000030304010700b142d03a50703401074004940c0b01c442042c186c10a10382d031080c6015a402c01c0b20110b00781c800f81c0301143c00240040d4a903811106131024000d0002101030114000141840d2002001840f40e12054600343d40079804002480100e181001d1404020040700c043c1030b00c1140f030400301c3d9881e802203105081c400c1c038042c8100d10078804844209224100821001c1080690600d400341017a03005185410018851801540c05030410a0480361652860506141000d01c1c29103404d409651aa0085417540022000440040c20070030118000c44c806480c5c11a9442c1003000c903030716200d40240a1030b87c40e40801c0c020f102ca6115035010f25000712041c85 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 607978669 1250 607977419 607977421
    0x80109050c1e0706141006110307020105040e0a02071b0302091e01050d1a0106050c07090b0105041802070b3c0103080310030b090109110301090308061e03030408010c170903090603 79
    0x800c00000c00e060407403c1001701000d0700f040b06011418148805690701601e0310303901100340103111a564042d041d0300a010607810401400414203405145502c001105400741c60301c140c0307a1365845410703107205910012100441e800d10462030180203103648008000762541e40d28115140780020044180326440c002c181c500307941c0050107081c1139103407544410056404019651568014455400701c00d2000e514040e40e10003080c0409140100307082540140e481d81c0c146414001c8400000f120200380030400c42c1c1c2006070100040c0e1203101c142c03241d0820b141c2d280e1520410001e212150103110715244500e010641550350305842c0c2c1122506494100310321989a507106207808006034110f41025003078195920400c41c00f02015080468418420004429040d801c20709040c2a90520324000b030104132203000041c1c0754140324801619100c581950b011054024a01003801c5071720640112401da5100c0303003500d0702c13160005010b40301103894801c13941c2d8600c0c0c807030001c4e600c034091004820b02c81c0c18004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 607979919 1250 607978669 607978673
    0x605181905070225051512190e19020f22020304060e0a050c190311130f020a0c0209150607060504020102070306060b070507080d0516020a090606080109050c1e07 71
    0x1002c0d042082800c41034030307422413981d001e407003d101c2e1040d070703100d90700071500d002c000654070302030301d0348540b09034180d981c41d4071800340c4814001c015134140c40f80c3c25170301c1301c824206c00420820015070000f2205d946200c0c2c0402e0041c06440c04140712898024014504010184d9210304010740c150041c201005807a9142c078075001e00501800101c880703d620030701d000b050a0150104030703030380c107200100c0f00b031221440fa100c05010520818800504900d039046101d07409070410564001e035282c40c01c040000e8800c4400c0d11141240c1007001d0003000101803100d80000c5041840f4510b400803542c20400c206041034000040152041c008010052500c50021400310b900800c8100003543d40604103002c2c00303803200050116600540403d039054498290001402e00c00842c070034104120696400e0720301000483d4541d404084a10101c0c2c1025403804005165003c81c4540e1000d803401c0d0b130300c070000c952500c0100402d50304007421741000801c0c00c1040c0c010003920b070100c20807520514083c0c161900068 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 607981169 1250 607979919 607979923
    0x605010503130609020d141c0806130e151501080105181b040e0c120f0720030705010c020d1106011d04230d031a0a030605190204030606051819050702 66
    0x10140050112502d1700b1003191449003c209509900d01c0c0506230105040245011101c056041d00ca60350041444075441d000350000e50002d220801d000c0088900391405042c560501c1001100d10120000d103903204241c1039a070211000d0b00400040f150361312401108084503004101c003801480c50325000c40d010001620941c0140c1c0d00400e030362031104903545000030603040f45500041d00890054680d4002400c2e4010b505074050042d0056540c0421041e01001161000c07441202103c6291000f44004400100c09015040070a0a15400361804a261242c00741040c00100c560501c2c40d0000001400880b22024003030100c0000140c0705101600e880c1808410945138420700a680703200c50002c00c51203980040c1e5622105080c0d5420410002d8041c40b00401840d0001030b03d6019221200c20008201103401c942d4000b090000c903140f98603405900182242c0c0a5442200c01c941c81e002c0800040c42c0c000780501e500c66441c80340c401d6511382180406540114408040c00040d0343d40c001ca154140f007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 607982419 1250 607981169 607981189
    0x61b090a0305010e0d0e180c0f1c140627100305030304030207031104090f11190303020c21030703200a15180302060708250c06060501050313060902 65
    0x2030b000b009440c0010107059101c80020030f0080c08501c20101510190500050601301e0b20385034100d141c505d464043c0c0745052036106041c0c1d588166001c0c00092042840381c0b04103601100c01c03003c00920f034504c4400703144d01004020542485620541c8115008006449500c07480001100010710b8990b10350b11790000d00c1c5200d41001d0190b12011040108150b000500101900e01817000d80442c2038050040105880d403269004003102400440c410004402d00b148980e00d500c002c080e803404d1040c52a2203200c0c020390754000c0d0016807044850800e2400d007001c003500c40d078518880d00501c05059841041e5684249800101002a03c041e1141c1d10034041415080b6291500c0039105e07084401e081000d607045456240c01c000c03030302d0001c0c00703d1110043d03202081d0f040d91603000740c401d65503680016600404018040a40024a440700c9508110360b481e03c0800d500054507423800b00582814100700f01c1c1c0307403600864140b000c20000d100d030510400e402501c0e442e5001d800854044c5503440480c2207414 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 607983669 1250 607982419 607982423
    0x16050402030c1e2b0e0106080a0f06060b0c06010e0c090a0302060c01110307030b0109090506031510050301020301230a1406071505040c0806160c0605220309090608061b090a03 77
    0x10b5049010b01e45200c151801e07130340c0b541d8802040c0078400842201a00f211391902c40c003500b1390701007420000020310804c100c1c680940100400254556541103507015540081001e600b0741c3c21160051040134001e40942d6005580004d00c5401d00c80300c0700100340108164000684145400b007000c034003a11094003d6044035080c0c641854890800d4400603020b4150341410902044007200d01044005852081ca44520002002885009a02c9501101e0400e01906003000c003100c140c4080b0760340c1c9007400110f00a000c01c0340c1d0407001001b42094070140f845542135a911400041404115051000d45080c0703591000326001c0c3c5c0d071413a0600d454100544803504004020381040b0400c007d00642d00d800c4000c403601c40d000d540c1269030780703080101c2600700325107004042980310014801258a03980596400350140c40725440c0c5d0200100d82c0300c1c4400d031022003140091103070003052001c0c0c001802064002c14401c801007555040c418444405480300e80c000c60307840e61002c182c90300103581d10102500150307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 607984919 1250 607983669 607983697
    0x1a090c1305060f01260612030c1e030a020c090c070203161d070503040609030e06030f100f05091f0302360601020a060f110c16050402030c1e 62
    0x3450001141000d003070100c488078451801021510003650155140b0610b80c0c0d08621207040c00a0651400b12100c01c0142c070013a00702d4010145a00850010801031030564010b100801007808000c40d444d0081003410081052a0010310041488540014541c2c0c0c4121088454a0681d43c46102c0c8101c0b0740161103001c2e52610981c00300000417440c40210000b9504404041e1038800c51500300340c0d1840c141a00e9030000038004100060100382d03150711112040e846494000c002110980005080d070b0010344403000d030914107109200304140c1004c52100100111082c0750081c42c81c10000454031b450043c1102840054813145903000402140c2c04005590b00600c854007000403604861643c0181074401044000c040f9001060035078120709080c45810b05034024040d0581555845c00504080010b10b01926155440c03c90140728200140c211210030030700038150044505030900c107a0010364019409030780b0400c1032246030300000301164145401480c02509102da211a240024469024055102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 607986169 1250 607984919 607984939
    0x9070e04111b03070f0f02012001050601110706090902030a0f0903020d0e0a0e06011116090b0f100813031e0801030b0709050a1703040b04090e07121a090c 68
    0x2500c4030000390101d03014030304035804202e034201032403030b075078404c4510140203040402c02d90300005031000d19109180b44185001e5140b00e0201c0c40c0683c0c40b11145a0441961b5100c00403c249075030300891082c0d2140003500140025494003901510f200742e240604154a5000000542e14491a421408103804080c100300100211410001d440e00c3e604c00100000a000720681d104920340500403030241c4050316040d00041e1243c070015110098200808401d9008010b0142c124a8407049502c4c0113211a40e000316a52038104201300d914450f80c00c02c18400c4082c0706000309080d40c0940c100e0b600c041202040c41c5240c2c010306058401001913221002040900321101d900340d640100340364103c900c2411141030b2504c4040d003d07a0454034a005041c0c008076800020000c01d4090142200c5411000098928003a250002d003481035006812100c001500c07000d1158820b101007140e0b0f40180a4128251400b616a0750348044050700c0100b0007410ba0030110100f0580d260074031a2100ba81c074010850546 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 607987419 1250 607986169 607986191
    0x50903100204051305090c043c0606030509100b0607050d1d040b030d031a09040b0103170f0f030705040923093c1b031603020f09070e04 60
    0x690b002c0e016042c010b104091302280a52900e000d030364020003401011b00032441c000c0381400014040400c41d903164030b134501140c006d200510782e014802d40e0900704200001200000b009005ea4005501c04010585040c08010303c42d000032411604050b600078001c512500c407007000600c24081d024001d8600e0017070810401c90242c00165228400c80310803a1144060221301c00c200031540b5440300c09170507420014030034001b948203500c411400c184002d503d4000402c07041c00b003444114102c504030b4000325900f005009000754412030840301d0105030720b0546000c4162201c2c14441c084c8401c58042401d01002182205005100f40c0e0060811000c00700030805501c80c10312500e0303028040c10a41003544030042030500a0105140031000611103030040500b8000401c8030b86183c007000703004c03d81103008409811104c0c0c207100d0003d49610b80c4840c49903140d2040105414407000701c1c2e06030040c48141c8010001a115a80d50983c070740022100340c1c07000c2d03545480c242e0f402c00842103403075801854003100c908 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 607988669 1250 607987419 607987421
    0x91707180204150305070c110a0909060f0b15040e0a0209040f020a1701060e1210090b010f080c010f084c08071205010906021b0613081905090310 64
    0x200710f80d203107014641c9a1001a60560440d40309850f000c0004005c0c1142c800425100c00054040e00c1000d4914000d60b40e407229400111402564200c8071591110711241c840e40a900898001000484001d40340f80701c400c11000f680c2c4070394440c0090054142c1c0c0014030704070071581a074001d040c2c05042400003003590300e03025000758860304160021641040942e6105084d010300241030340d5141d1211046060800100710707003480c030003104100500c44d1941401025000c3d0181040061185c0300801655042c00d114003400001c0e5005480a81e01840d95860142e902150000300b000c03850a04259945907540f5040f00e05040d2505441102030020203203e9018000c2d2901d40c0000ca14542e00c9444e88402401c104048058450122250b004850900540c1e00c00350003610402e10440001a106400e07503224400d0360800c0f02c06601501c3c480410700c441074402c2c481d00d64042d440603600c652442456454050031b00560050918154030420020384060040081394a00c181c01030807103052000e161102d00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 607989919 1250 607988669 607988677
    0x5060c030103051b0f040207020607020d0f0c08010c052517190c0c0515070b0a06170a020d060c02034b03060405040f0f030207080c010c030917071802 66
    0x12004d20030014600351240e5400320320000e4000003046105d000480305d007004083d400814099a101e4410004c010044e83c4035541d11899070310035000b103169003050342040c21001c102c96200344020390501c0c1a4242655002c0211040030448412080711880c0c41c412040d070640500c000100515a1088409011601a409003c1107542102c003a10042c8411104680300c03014408010311880c600d12052090340b40000f95540c4651485642034185a056152071000001c21303070326031190554541051080c266280003404500303a1920007025512001d07808a241c018400e00c02078030056480240d00d1580d80700b0b0084401900c2e846e80c0c540342c0c0340300c06500008000c0190004e040055100d6140301d00c2004201c900780c030041040c540b09815680d03039009102c09040c0042c0201d50007410013600000258500d400d40460f0b40c000e034010050103050103500c2d80740420040040e4103001d80c015012000039448400807040e0746986208121506c21190328900d0300000d0740004645c50340200138590800d1441e4090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 607991169 1250 607989919 607989923
    0x303020a380a0b0d0515041406070903060621060c050c0318030d0e1302091f121d1f0e070e041b0b0a05070c0906140414070806010c030c05060c030103 66
    0x1004030848000804c0328861030258001c2050f0420220f41002039010103140358840c0c010156101140400403199050680c225017420200b07507601003e1007404824802d0038007400d1404c082e100040c4101c035000100c40750170440280083e07290240c2c01d0300c091007403065944004284045940f980754500b8105031082600a080b802881400740a00c60144500c411003902400a806e442003022000d91540207980504100341e0170545c000090544500b80f4440c01310780000700ea5a54500075440300c0c1c03100642c3c00400d2950700c0445c0c103450740c800c1c01001180c8501074004910402c54003004007280c01001d04081c0d103001c081c0307020b1a4400107840b031919000c50b103d00c0c860340040f00385c1b46c0848008101d603603440c0134511402405014900c441400780d001019001d000300c00e03074080c640e560700910307003640c1182d0440d200000d500b905040300d40c1061b014800303841000141c1e80c0d0036483c005900a2059000802e594100054071454005060143c10300111954000c401d440a80c0750015440d80709a01c00e00c42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 607992419 1250 607991169 607991171
    0x819020906060a0806091807171903210f0203011509080624011b14010f020705030d0c051e040302010e030307050606060a360602070303020a380a 64
    0x1512858482d0407240d0514158071181c81d00c1c3c90b5030090100b4064018486091041113201e04144500100880c40040c44030200300040e604c0c80c0700c011410044c094516180549500d404600002d400c6044104d5024031605510381c00f03040300d8595005031040c0012900800d00c00400460764614400a04401000e80e0319503115040d6100e10060380c17003a003103400311424100c400c80b509140c00465070018a003c014074021242042c4601d00d005048001d18044442c012841401c2da1103c03030038000d1200740d0003080303011414402280c41702600e900c6000e0000801503940c860340e1010a00440035100100d804100f0a4070040402003a0f606691150009034040b40c081c01650005103000412140d01d03a90000c0900b03002c0d203c50040c01003d8011040400600c00256081120120728612128407143c070001030808034842025190004540c43c1c0080b000c5421007030003800403907000600650105e038002031844d00300b003214580881240e0b42c10f5000702c80c0298028050341c0721303074203282c190f0144840000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 607993669 1250 607992419 607992421
    0x10b120a050105011e051c080d0501060305090c0a0326070302390409080c01151503092019060f270608180106030b01170606010e0f010908190209 64
    0x1280011028045000500f80301d0030100c140554101042d01c1e60584550250144807887c1c1545e400c051034001480301565165100010411503506001e950340005c41080540045103505001c80d03500c90180c0001f030005036581d0700b041e01a180304150341d581700c00c2c03040c0002d0702c840c41440c2c025151031a22944207481c40402ca00701c0c041680f00000320541d00340d581c19882c0c212480c0e1090001a01d16a102030b00c0c042c506005030b0f11802402c0c0502803c400454421074100c6d420000802d0688058900c850101407030000c480001440c0c2074a221720710305045411803410340e4000005181e040700740c0000440a10f4814000854941241c0d142e1b07000060b41d140c42c20040c000d50382604020564031081401120111410042c03103000f600020f8100016110f407100052000f02c1617801d5890303541c0100d42c01d65035078004008108000c0c1c1c08010703034980318014103600c1c1000c0300000d01e20a841400705214809a903650307400c5a000e00c500310300404201d019521803a100c2d6604903a10880c0c0f54080c0d01500c0500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 607994919 1250 607993669 607993679
    0xb0d14070504230919050903030c0919090903030e01051f120201030204080a1212020406020d110a120e0a050d1703090a0803010909020a060206070c0311010b120a05010501 75
    0x10024480c0d089661810705040c50b00015500412074034007615401c88005400400d142c981002c050b00c215201e0030b000c00512460592841140c2d00102640d819410500912110750491021900e2000c2e0484050742c0034221150440e40740100c40e07204902c414582110703502050380603040100310700c1800000700981d90301c880c0c552040411104000e60300340006001030006441c83c99560401c5401072400606243d100c1c900c40e4540102c880050b03403812544000071003059440740d2408030080007031070250f09062508802943d50364516041d0014420000c500b0007801c84200302c8403070b4481d00039824041004442c0c4e00500041065201580109503e00e8040744d039092280403901420740c0701c81080c07068480c2041c110035a800180c038460f002d000749040c040118050401841c0600021a0009400c80607481000203070103050b40007900350f40000040141c3d85400c00210755801f0307010f08002d10100c10060105006040b141030b41c60b4091107040e54541000307400110044601e21030300c0200f007280d0700c0d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 607996169 1250 607994919 607994951
    0x70e01050111060f130807050a021908060a0209040e0d03060f090603080f03090114070e180f040209040c050a0602060108101b1215030305030a0f0c050a050306030f06010b0d 76
    0x4903000700c0d9010f440030440300d0010800d82c1c1e45c0038010051070401a07019a032040c030b00f540200c4007a604d50380300106a500350b01d01510400000a81c10800001c1d403458012016203540c0700501030740002e5400319180301c1a0300c03290040e0802c000b40c50140c0e03143c5009100d01900a007894082c12400b40c1d4841d401054180ea10311618040d40d400409181c10003c2c0c034125101190b20042c54000c641d501c42066a41c070880c400c0d0749a024051340d0701d815a89061070010704c00c060041c0d00c1032140c054000001d0102c00794210100541082d0160f0340c0050665030b41c2441220454581c1c001034000f503140000042040d070110f401816a02241c0c1940d000e00b0000381c81400742c800b401c0c89507500c414680b100e1900035020f01240500071303041c8000450200f6a51081c0302c8040c24651069002c18400000c01407501d4451048445002c4000c1040020175034015004102d03003ea140c50400340140080825070f00e650800c00f142c039001451040751302a40e103071100c000281c0c00045d04010002e040940ba10401108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 607997419 1250 607996169 607996187
    0x50105100c17160503040806060105070b01060c0201181706090c01201213030210090806070e060408121207090b120c1204030207051c170903100e070e010501 69
    0x40d540c503010030341c0041e2184003030142c41c1c05070a42104410400c2d02040740c2c0c1c080801c0c40080c040c0c00916101d61504041a0500000600803030401408200c0e20000500312644581569000c1c98144c14000c060b100503030340d02090b0581314080c0310030900001a000e010f10203084c1c1c011071410a0b19480d0f1140c28031160745801c480d00042c0800d405040d42544e98a0000f080b0000c10a15811641d038a902c1080f440c005520005100c095645440381c2481582005008015580d0007450811039491409507143c0d02d8420141000b8108007502c1d003444603940d40c403c25500a4801a0709445948105110703054195001110103a0401680000513030890b00a030b030018121203180da603841c6044104090034039101e100400a46c5581c009018006500394280c046a102b24403e070000e025a03410f00c401c00201c02d091804a110880d030511303941d00007610403110030442108186031035841c2e0500000203400c000403600c0c1421001e1900040e01c070f50000000d0602c1c22030b050030418061036600c400c011218018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 607998669 1250 607997419 607997449
    0xa0c181e09020705120a050708041e060216061412010b0a080c07080d0903050409051509011e12111c020f01050306010c03081015020a1e030c0f0f080d050a050105 71
    0x240a020b43d284170344c1001000e0703104181c81e00070b24145890b940e400d0182c0241d005504c800039402d4510082c021248102806441580024414040d17852460000d14046009490410001d9000849180300c2d84065890605c0b00361051201581c40703101c2101c540d005400c205000a01d29401320310081d800c4811103220300d0300240042c0c50720060309086005800c509030220100603041100140581282c440c0358040e42d071094000080401044c03c000c03030041e060b0440c140340d0950b00c8960408201698a07441107403202050216501072034181225000b44000c81316400ca240100e8100d4400049400300085520858951200f007034454011202c5000031203106000c104031102c0100440d0240d418246e10898020310000c0040d02d40d0345000760250440a803002680c40700c0d00c603000b04428001810541f41d08072850304040c44564030001c0460445800140c21403900703140c000d0901c58000c6a104466400400060340c4102e20584c00b0000c080464400d80014584000410f0924080020307070300b41c01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 607999919 1250 607998669 607998673
    0x605010206040b1009090f0b070f0906080c0705150406180209150a03050f0c0a080c030a081305030a08091309261603090812040e0a0c181e09020705 65
    0x780e140d680e69090f24030040c0003072201140149000600782c0e0f1a010b5401502d100d40e0800c04d07064080d1400d0141c01d0000b81c000424014010310060810368006440c0301103400d10319003c02c0e039071500039154005201b4060301400a0140304503042c42c043d00514814016449010104480c02406404100001010a00030b502a04a00104403a460070180402100300c00400c00080143e0b81e64940745440c5205a000e4a1608180c0b075840851900174901001030000310041c0c52021100c400281c0c0322210140020800070020034044113408030480d000e009008050100c07448043c0302d0921000e15004059181c0c0f150741c4c16030300c0c114480d40b14041d0300045540b20b211850309408c2c00c003030388a64080903056001d03124014000655801e5221041c903240700e02a8803611445410001030a044c4110701d442c010070b05208010420640d0036010481d5401039a0400003e00c541d40f8841c2220000b40360383d2601486c00c10684041002c41c0449180701707850480300c0183c01100d40d12007000d4140e00076030f94098256 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 608001169 1250 607999919 607999921
    0x10501030209061318181e29060a06110c151204060603050c03030406050a03020d0905031207080a1812020307150e06240d0203030405150310090605010206 68
    0x154001d401400704464010721050429182c83c060101d4002c1542c4005001c2110301030704100c03000304d80f2030300c1142e0390140c40c150081046500d031034003041001700000c400c2c0100c0540d0324080c45007864080c0d03c00c591403104011800e60900001554000c00d03580c42c3d10a50f014400015000d01600c0c42d0700e2245154405805040f0311a0308002c1c03c41500b0b01e00c2c9200c41e00c01c00c440e009850b0303a810518805d910a0000040c46070071400c2c01882c5c002e00d4603005000c2c0d0320810050006581140c181c640000e07062a0240e07031540b051103100040c26007d60014030307520021803040440d58490441034800c0d036a41d5a45078031076480441c0d03401599101450104168200050000455a1500744510340d2042e4011203141c1100ea5550640400c148248040c2a955130200c003155901c040c0005900528850032003103c00603080c0300e0300c20504024010300d10543c2800300c80400c5403820b000f40c42c000c1c6002411510100301c003400140195004568580e22800f0b1001c0c081024541ca00c00c2405031001a030041c141 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 608002419 1250 608001169 608001179
    0x5030301030b041703070f0c060e30040b030c0c100f02071a01120201030e12030916050103051509040501060509090304060305010f0b070b07050d06181d030a052a0609061e01 76
    0xf40202040180d9119403074035261184014204292a0800003030040d0013882f60f001c210034040c42040010110003030500b04000c01c0940080019a6000342c5c0280d140b0355580b85a0405520f0407030bc230901302c05001e04129001711b9011051b03000e08640c0340074019130407a2407003054200504000074018483c540f583c0c3c0c001c10004d54400d6010b031915508600403074051502c3c0d66482113040c3c10849105107a5131154114022040c05c1c0c25044005040a082c14030032401c05194014156a150143c00d000f415070700c00050601809400140050001403c0c4076418284440950780701d034070034028203000c0fa0038240001101c800301c0280300d0454181001090500d034243d130380c800c0400000b40246040000178404402c4400591080d100180144030380310810385032010f2050280c2e00704c0303041e0082d0038091205600100001000300c0305254100e107402655500d00c50081926060203140030504410751980c070a540013000110b81c0d00505904040720f1640c0c0e0340c0560310300866072240c4109080762416004100d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 608003669 1250 608002419 608002427
    0x90f010605160605040506012405040b16120518031b040203060d0c060306030b0601030c1d01120204030507080708033a1419020708030c030406060305030301030b041703070f 76
    0x21155401c4041c044480700036200c43c1c0a03190156010350300e0b03420441c010082440780300020480c141c2c01d000b880300000403403007000c0c0032030040748202404040002a00c02c602003208400f642107036444100350703c0d0040d2014000384150400344001c900703184640000c150519000544040e80e0114218170407003100d8840c1840040e40001d44807980108481494500150801100301c1c0903191640e0001502d030b02d181082d00807c2400740c0010f050500d06a03568224580c03180114000303541c8014100c2c140c280240c01240c4515603d60171400f56440482c0c003008010b40442d04608a941c6e100c2280d62032526821400c1c0c9074881c581403080d41e4216204001040940b907203010703428076842d81d0940400031026103c9400c1e2292040b08174040b001c02420040103410305818030029a240c003c0450800c651540c44051030311001e000140f00c004040009810841180c001001450303001d420350b5125690f925000c10b0b404000e55046495901e58081034040b8102d20b411380b03101300107641e9894000402c4d03810580e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 608004919 1250 608003669 608003677
    0x6090f0c0e2d040b060a03140a090f0b0403050c07061106090c0d150b0904030206070f0509010906110c0402221a070303020c0c0301020c07050f040c05031f030f030e040b090f010605 79
    0x1a0800c0e141d1941004559401000c0c1c004841b060301c0124800803502c2400081c404014055515903103003401d14000f203051100c040083c3d0b917002410024a445a00f01a5a103003e00c1c0510500c61041c640c000c98201ea0103215048100c1044085032440e840e4516010b03240c10091a042c4d812005114455011807070040390b080080f40b04600000302c45441030041a03820400715025005640070b0700c140000141e11242940c0c00703000f50301d0080d0800144d0701c0000c10404140c85a001040f01c1d003000025200e2041c030501406610062003103540b2920544400c00860391413400c010607015071500045c05180d8900d8185080f0040c040303071480c0104c1c59070194000d40042401c85214031500d0103c2c05103840910051241c001d2040090405a140000f044001c068055819010794105140e003030701260000c042c0c0b600b0040310b01c440320095000345402c440c0c03100158000307400561070001010030b1542124000d1103510040e47d00340702d1880301d541849210311042d18041c00701440c0000412000e8840d034050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 608006169 1250 608004919 608005009
    0x516080a0308091b10050403021008150f010f23120f070207060e12030d1a0406080c1c050312010902030703060504090209041704030209040503190c12080a06090f0c0e 73
    0xb06d401d282d160380128024081904681c00441c018000f0300c00b000c10700007100340315540700b291aa4070b0711511038002030004070250030711420f20400d19a1000c1030001c00d94030b49511030542488d0354486680b204c00c4c01c0608010303100b100d024040310011540062012602c1003c0c2d406a84466850001540034002e18040071400e124450200348814a45d0110038058203624a1040525221000400c0200412a6080c0e8804919540301c1040a803043e2500280700c0c102d11000f010710001003901e818001d04500c20640801d11280c00d1800100f20041598050f50060b039060b50104103403610743e401d010032205409800f139401881a0002400100309100c1d00c00b20014054405040640d2035001c1903401074180e9040b601500301084800ba14022070305040c080c485980b41c48003856481e5150300e688416401018420045035800041c101718060300b0039030041c00411000c10080960010074001402c201a242c0001210340e44110610316101015400148586100c6500c05c442c01020740030306500030800c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 608007419 1250 608006169 608006177
    0x5060d0308041704261213030b1b0d0f0c0507020310050601050c0d08010503060f06060f210f040209011a0904090204060e101802071a040516080a0308091b10 69
    0x4220064407505d02c00f610340d0103800000e0f4207882940303003a042129000c0741c2850100148009880f100c00c0c003041c0d00032a5045540e810541c0c8601d42003134010940c6400300703a41da400005859980017402e60110250001c080d07400c10062103003c1040324180305000000c1d6041d8080480312801340b0659014030b8000805041c0503140401c0b07103111a007403105140c1c030b04000c5104580100f1040c00e0511116501205880000f80b1a28110340020308074000d94124942905001c600e6000da84806103118500b100c00b4011a2050724114240012441c4201d804a0041c140c0100004140d1515801c2e00312450751507580c14104007000c0c0600000b04104207090740c0c42511180c1c006688001095603501a20442c004413054a083c02c9d40e04904400001c081400544100803410204143d90080704001c4103c84e20409603403541d0810602d082d2014149004411f0201c0700010602000115010818841d8440c540e045d945c901150b92500c106030402801c140156042c0d01c5185080c40020062944a0070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 608008669 1250 608007419 608007427
    0xf040803070e03120d0605100c0305030907030c2c04030807140d241401021507030e0d03060501020c031603030c03020a1718061918080a0b040605060d03080417 70
    0x9280072000d2888100c540e400040c11700400d0301a000c1d11020302419100c01c2481011104001d0070088154005001c010002c008908030401c01e010000c01550061858101d60340c917240f0400c4203240e038004003610000340121019041003550801885950581c0303c1c441103507905c10054a50140c0030380340041c0c2d00002c011000a0302303090b04c04e9030444041c10071519401c506100c0e086843d210307a42c00003020510720011458041c1e9000075a4100c3d240407000c00d0000303455008044d0064100c0c900072000a0051a400c02d14256241d84000300f101c909908132801d001d204024103031180e08000305200004126407040c00130030300a40c1c8800c42c16200748101e4070b0340c20300da495a2801c4046e43c00d03000a04680012888200c0004a030421f0103c441100d00603d052005910b40940200d00c80f5840c080c40030868250b0341c04940c00b40d080c2c0c0188903800549081d20300034548505d1032903048508640151070000840c00c00c1c100114020040d03649a1540d40b402c2c0c07100d4442c20344100c0c4080c241101300790200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 608009919 1250 608008669 608008697
    0x71403130503070501200309030d02091f02010b190e06040c0203070c0602060f010e16080403140c010207021e0603070509040b270f16030902180705040305010606080f04080307 77
    0xb005091450084000181d65611404148112000107003080d50501c828018452880c00100480307402e46070b07007600160b403911040c010a09009040600c102480d880c115100d08164041d08005140704080380c1410f0b0080110314110300860300703402140d86841d181e000084c0c0b1401c00d42e00103015500c06004480c00c110a641d1148800388003504000010f0700284103004e403000c003007888180940403d1000d940d80e45001d04807003100d52901d110301030800401001280070703d4000c03103030295111410314800b96200000e20303202e8041d512000040f8060118850521a40250050f550940e510001c04403072868940c1134003119a500504034241d4455034854a41d0101e5590010203000b44a0212245000a51070444421155401828801c01072400c5003005458a00d5003d1400794203514100000c14001d030b40042814682040b940300c0e915010781040c00544e50b001001780089901c104001d0014a4a03080d0850351150705644036003440b282e000114001644000145a10105a00d00707180c001c2400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 608011169 1250 608009919 608009923
    0x402090402131d010e040f06050618090f060c16031202090d06140603010905060115050d020c060603070609050d060b0f090a051603110904020319091101080a050714031305 75
    0x580c0c0f010110100c60000158081051481e403801481c02040300c4680303240584558040c40084500100615030703c40015007903640e03c100c172031000c5564101d0088286014010300383d4400c4400f400c0c080c01e114003400142d0501440044610314822070001c0c400e106c07002d84e410b54030440c100e40b00d01d40d2150203006a40d1141c0b40c00c41420b02d024000d0700d01041e40021000c01c21400040545858060f906086e0158042680015640e04440c0100b5914a40c9043c4480446250081040742d000d110300000c1d40d50300e1f101000a510340180c0040b0282c40d00a0342e85d810139142aa40e5100f00c580090444007224003149480d48244110003024102c0603100c0100c10020b0150b80c0f081751079001090b50740c0d080c4228110303000e100300c4404081c0c2c201000540304032044285580100071040384116000800981c207245201c20801000c0c1008206003c012001d00d0300786030301e20390540c144c4e00203581a40090008591809024003460706503c0b602c41d03414001d15010b03015403006000c1c2c0343c03001004010100003a81 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 608012419 1250 608011169 608011207
    0x50a060509032b0c0804050718090203030409060303090501020f072108030703092001120b010201062402010c031116290618010e0a0207230f011512020402090402 71
    0x19800700ca102543d040094441210702c1e481d6207408100c109030402000480002c1d000c410f686051040442d00000d8030340b100080c1c0320541000390540008540040c61a20540004055038466196a07501f0744e20780004907a501e00e10a54000e00cae0340032003810403410600c0c0350301c410003000145441c80d04041540703c109c2c55038001c0d9035110009507607640308014131506c0201070101d07542e10358000c3d118103540c000003092a00b2009425080d1941d402c03065400381c0c006d5005d03600403c8841909a07151411450054290323000950303080155003044508001288030b80326501d481510500b035103040c85103c0b041c1d654a40c1c075800d000c503150408042d9403d1143c60031000301ea4104004060401030f0b1401e00c2c04e0201c1c03500d2450380c05002c81000401408120b9503000300c941d011a100328016205c0c0341c40d04000c210f0101c0300d5240c1501c040002001c0e80c07100d00101d600607500395010002e220354441c12076920301c8140144a00254200420020401850709800812460800070405814410040200104068 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 608013669 1250 608012419 608012467
    0x3240405011d010603060501210e0a050319031812030603051605041103150915041a091305060a0f060b03151201110910020a060e030d0b030307050a06050903 69
    0x201d0482d41c01d15000650720041d0240516160074403171a4038100000e011004d20b00340d40f02c80700c0000f080740c08006480d60310104141d007400c0c0403207003116034506040c0e88a5020080e1104000020952480014000c0c0241d44ca9950780580c42800710b4020b88815540012004102c810561030301e2000020660401c07420600128208258100520b000e0411080304c80007a001100028240100180c841c1e03003000000042c0c0e03055512160a5590f0503045840e00207840d680c1d54840d1518041d0a1100d0f4407501411001da0141c0700c0c1d590944458802000d000000b00340100725501c4980000d4a10201e90401c0d043c0300240c003c085500c40e15180f0183e12a0000c4030740040b8124178035aa050036203448240c215056505100800c40000142a008447e1050503001801001904c454280b041e02c20047c0e0718020f40c1142040000c4488217054071380fa540034803101884581481c009a00703d1030048102c81010350321000410180810340c0e5a40b01601c0d0003401c0c10240c1c0000d10102d0154102014403c0c0d14403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 608014919 1250 608013669 608013689
    0x50a0308060f09010b040b07150c0e04050f040b0c090f0d11030d110a0305070c030609061a0f06030f06011707110714060a0c1e08030121080324040501 66
    0x841d00c642840b12101100306007a22819014004000c612044400c035410b4800d416151035540409050005001d03c001d41e14444070340c0780550316080f00307038052506a15044126010b00441e16202c003070200c511130503100502404096004a4080c084c50401000103d101134402070941102c00c0c000392141078191000d407080344102c0c00010305481c1c14450074101c03000c9410020440220782c091196113408030040241401400181c2c0828024100300e90002564010000d018007815883c2c08400341100700c01e10201e00b0881c26030320150b441c01c9221048003140180c40710741182d4403503200c000c0c10a03020380514140000a40803c0032881d4541e4214030510090300c50688161407046c11924020703650340103445203400328041d10b0b4580e440c90129040c5850510f4070a1046816003428a84e2074000c1d0410a03001c151660700da010440c50702d02850490318060002200c0100c2001c4400c0d1122407400300506070401040007a402080c0014030b00c00e074200f865a4000366804080209044480030703049180c3c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 608016169 1250 608014919 608014921
    0x40f2102060910270e0702060112030f03020706020a0302070501140105030c01031a040219091e030602071a07020c03010e16050d2405090c0d020109141c08040305060f01080d030513050a0308 83
    0x1104031708074072542200c80d510003401a50f24124594031003c501071002020030040d081001e0003544650181d8010315048541103651b0070380400045d0017540280000c5541d9420000311008a84000d8a00340c1258000340140020b199007500440040914410501c0a04509003204109846501c060140641500c149055011310b04a026090801c180d0203440507a04685425090b0365100350b0f000101c940c00403000d42c481e0b02ca80703042081a9180030341c080f00465070408001d00c43e68009566505e080741500200b0140900c840c4407138503142c410040c40b40f280c1c0c4030001003044d414202d600d8410580544013140242d0380c600700600002c0040b14a410b41c40b502c40052000801051190f8104958103c0c1c026480307182540c0042d00750f441c01d20500107d007400081030202d54580d0000c40c0200500c0c0c120124114106243c00040c60300a400143c9080c410000010b03808034203084a1416141707034200902e101c101d030300340441c0a170400a02a030040110700180390009031081003405100b03031080e2201203003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 608017419 1250 608016169 608016179
    0xa032003030c01060b310e04030c02090f180105010b0304110a08010f0b0901081f0f110d020301060306062a030e060711090a09030c0224040f210206091027 68
    0x5116001041101c1c043c0074107046c0c003035481820129004035442c54401c96041d0b5a83c0c00c0c01d45802e502e015000c0c0d0054090401c00003081da003007440e10b03c03c07452020980d054501c580101e038200c0d00c003401903024200c000c00c0480c020520a440c0f040711980003c160b130b080d80d0348070303068182900d00c4030700007a10898851040400c503280c544440d43c00f60180c40c004100b0714040d00750039000d0400903807800140c0340e41d406c2004e01c80c90b0503403c002c580c4854580344a5070b601c05a021031000750310034071521b00084d191107004200144910100e43c0c00d4007101c4401e59100c0c81c070a140e001a4110f4100440070310418408071400ca88501014141050203010520710341c442601c1804030050300241046e0066203000c010702c0c000b035044464002d000341c054548a030380c0c100b0301240c4101c0c402c00450301c80000c10046000107602c901a046c1105455001e00407500600c40100c45280ca80c0d05024000e40c030560512109080341010303151080c0c04001850482c003050300c44000310011403c2a004101d24030521042401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 608018669 1250 608017419 608017447
    0x1060305120c100923030705100b010909050903091509090109061d0414061303031401060807050c010902040612030e0d0b0106050f0c0102030703060608060a032003030c01060b 77
    0x30210541c61209441c1280c456041526001c01e007030300d00b40391070f6101e86141c00d1041d10702d1110045524900000d1500b101c00b040151740b900106c07802c0b92988215032200e201041140a800302c129010f85a8803203071401c00c543c1c1c60140500a0452056100511660410703a680c039075150b00b00d50018140311754404841c01404100441600224606400c00100700295080050010101c6040b91010350032600d5a14001102e20b044848a03e054031404003440f4110980c5210b04144a122351000c0160210800c5d40a807560b02c00d00c105800714100d0800658242c0c00f51000b00307601c000c004000907010010364000b908403802034001c0541c09030059003030700400d5004005a80c841c2d034106e80408609240f5903400b200740c1c01c140510000c10034042101005103a2140686003c50703941d40082d503c0e80b9001000a00400c03a0b8407034440000d0701c80000c20841d04051003070500f82c98014200c45d10141035141701c1d00c080c3c130180c036106400d072000300028500c0034000e204040140001048040ea9503200b906a01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 608019919 1250 608018669 608018683
    0x10b0d11040c03050c0a030e0c130509070e0601050306210f0303100807030c120305040906140103050a2c07030503040e0603120c07030f0c080a03030617210d150801060305 75
    0x1200f41460a005c0c8400c0904150684110f01c0451a0200301c0c0c8152a15030b50030a01c010030002c0c0c00804183c54075103404502d4015501c2582850204c6134140d6481c00401c00c03800c0280c0342c40f800300302c1c100049443c0d81031a000d84071104142c00405105080f00c07400040c40c2111840018a0f203403c08003d000000e010547c580006104600045c1003403401c586900c4014155442104c3c0c1c18401d100d03141003007501413030a44009103d142c0003040482d544003d03600182e00302a605a00080c0f80c80009042c45c02c03680724400e111504000d0341416048850a042c03035020804011520303500c5200780010000300308000510103003820300603000d482e05100d0180352620111944040008906102c00f8040c0320700080d0301c8007243c0d0020512820002a0f00b4006100c0015400c4014103014010005c4145078060304001c0480742401c516800620080340e10f1500d07442031620010300a414490800b00ca062698040c040084081c5000100d8000c40748416050211070b030300040301651256420824808140808 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 608021169 1250 608019919 608019941
    0x90c070f050a110a0503060c0a02010e060108030c01052d040204060504022101080304060f0e131103090c12030f0904140906090c180a09060f1e1a031509010b0d1104 72
    0x40c094545c00d201c00203445503801481c04064120125001021510035007107801404080030950300b0340c2d42c64400c22500c1e6400303510441000d600340342c0401c3c0440d01c555034000c401b81651545802c0c4182e0078005a6080f20080e1069170b010b034441c3d102064130354440c40142007c03160500000810340581c10f803001c034802c05901c084141d030000e00c000c02034070781c00910001100480f850011189190030000812580c1000f40e0303a0185841d01c0400040500d00700f0056001d4200d5074125188141341000300029150320100e6014150000c0c0004c5040a1010000e419103180090001c60790140c0701e44007884020b000c0f903041c44250b0021003802007400307040c0901d40142030143e60b0f400305480810a14901004042c144403040c81e038a07801c81d800d001c0c031588540c0414510f010280100c0804042403034003403594900d0001400d103461008210b1402c0d151f18201d03180e00140160880d1014840d02804030100104001c4155490700d08081c8182e60700364480540500c10060316190391603440900044520000c0c007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 608022419 1250 608021169 608021179
    0x6050a1e090c35010b0414032b0201090f06020702011b030801140d150b0a0501050c0a020919090f120c0c0e06040f02030a060303030c0f050306090c070f050a11 70
    0x40c442e031554019440c01416440001c01241d04000c59198030007034054a03d00b0f5a414841c0f00041401c0e01102c0081040326020034080303017034a46900405440e0f52140d0b800721400114845450710703889005000d14080001400002a8064980c48841016010302d004030f0395182e00041050456800c10201d414076079003d40c801d4004048c964000d0404103060103400e050040749880d52646d540e41d20ba10210480d408550704040c9003d0b04851006007580c040d00602c1443c0c002c0d80882d565100b942500c09184403c0014014081c0903000e11403000d8000e00406030306010201c41154070881809030218081c460f10f280c0c90070a80c141010b007084501c2110460800154100d0600855207505400d800c1d9540c0400c00303412616107400080c0200046d00586100d14004420844980450b912080407a402502d00340220101c250707080300c1e0b1000354a500e00c045001403010076142d04049131055071101c10007840501d482d5098403289140300c0b42032012035681d0b0080c0d00c0c2004120350741c4104018504181c0d2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 608023669 1250 608022419 608022431
    0xc214104080c060c03011d040206040b0c07060e15071e021f03050703140a05060616030e0a0909080d0b131a210307032d02070303090b090105071506050a1e09 69
    0x500b03500780056411f402460281108042008e640d07800c401c980081c441703121007582d664820700a01e611400781e4030400010480440581c41142800801403610403402c0703105c02c0c41d11800c1c0d0b842051000700150340d5642140202e00880043e05c0e00803140f400b05002d070902070008030103080b004040c0d030ba004205508050604144c500c0c0c2071b60021811f034000c0d0011001165130307030300c100100c1e019004040ea0f24070160100304c584800d041d003000f544454001d060b19541c1c7c178551114441d40c1500d002c010001c04808003000340000102503903219254039500141480306416100a5050544082c2c0340413801340384415030900b0303640c60060f01500254601500c0ea00c07040d00701000d02510b070301035000040d040c084454205141c09170300290015010b112440004007880c0d00d488002d5484031280421804904886400b007070301c24690040c1d03114070720141e41d01807074026960f44180c40c52840d2130f0090802c90b16440e000c211a91240302140141101c0b42d40725044101c01c02507440e894032164080c150701480c1017 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 608024919 1250 608023669 608023679
    0x1d10060f0f030f050a02090f03160312020f07060503060f0f0a0b0f0c0d03270b15040e122502060d020f0c010c214104080c060c0301 58
    0x104046a14181030030030020020401d8030542c050b200c40310011902900d0031003006560000355002c1c00c240e00c0c0503661003075281016024599510720070680306c400032110002c1000001d002040e840a550341a105aa08032071659a140d407900a1680080010403004401c01c02c0d0750a10040fa1100408212100e041ca20307204408544081251b008044012a0004000e5a980601001c43d01c201c94088111420282440001001040141d8030b65605405022400b800c7c000405514650303030b60800c0000c0507a07100d00c0032402c01c07090f01494044d0050303215180b01c4e00c00001841400f100c0032107810b1040e582d54031048048503461400c513a5034490000c42035400056111700c070546075142080300005903960a07001c9440c2072400751014494880d0300305080b1040320b6500108002d020000700b4100e0164024017220300042c1e45101d051540141040a44260280c040b0241340e4002c0303101007140300d5000340714071042c100407808440540785c20b00005480c0080c02d40c2009460744c04003200c1082c9056504003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 608026169 1250 608024919 608024927
    0xf0b0106080c071a150a030f020901050904080f1c0f0509300903120c0a0215090d02010f1e0203040519180207030509090103060b03010e031602090406090c1d1006 71
    0x1030700304006100b000030001d42e5252201c0b140d001440c1780140038603d0b45030340e80780480c1a140c50010883c0074500a100000745414540d000e503001d59800320b03c0380c0c00c104160a01c007070325400c000301d00301d07178440318209822003000c0e03e00c18916146000400400c5600d020840c9514094100380d68080c0b03091499040c1040014035505164804003620380c96079a64001c0c0002450941c2d0210030501a400029138002c45d901d00091420032540300f60b96403031252400c40741010190003034000880d00147c0781858080190f10948021080341e03050b05001d0b551401640c401108402e8103141c0030301507480020144103c0c83e140210501e04400e0001641c074203400c2c4220100c6015030400d2841c039140c0c0100d444e00426020f807069071414075019210125644c0c0d2070401d840a0020442a03501a510381010704082c02c401000721905519405807603442c808056080c010b500e107000b841a45ea0b00d1307544090b1000106054800e40083c1440442510030004650741802039010240072403484507080c0800300505504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 608027419 1250 608026169 608026193
    0x60207080309030a410d060803040e010902040311040213030c0902071407060c030c032d0318050d0c1401090b060901060219080711090702010204061206050901140303070f0b0106080c07 81
    0x544075444178201020200489076010b516602c5030400c2c1400700100300c0e000000042c2044800840c0245a541da0364000d80c402c0344034a01000e040034007448190000d60030903030010312448400100c5260801c0d50380c0c8500c440f2940c250854120284c0018070601484007200c02501044850800b804c002850983c2c09032070010b020400605000214880700241070082049003907800e030200e01000c00c0019404000c0410b048100408046850720b241018110b03140b0001c000c0d04c5038050020202d049540388251080d1900c1041110741c2907000d41c00c825000020700542c140d8a00c6140c9140301c604188042000040c016000a0210340c445c2c04030540100d441e5015003000c5030001850347d0b540c403c83c18160150340c1150007054110101c0800d0000140e0305500500032115503945404110035015900e00035280d503849402c1c6e010740c00400500514940d68400c0d25880d0000f8100c2e458040c842d40c2d0004043c1000005607160303034007200100721541d0840d0220f9445107100351250700d005c003a41d40707400300104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 608028669 1250 608027419 608027507
    0xb010f080c03131505091606030c020c060903011d07170a1101030f060503150a060b1317150a0509010c05191107120521040f030609060207080309030a 66
    0x1049001c0f0301c0502c02d04105400c5510032040061010740390100c0d8075690341c1d2804142507040ca505c0c00300015071620038400d42041d600702d6805000050f89500420105810985070250f01d5541c0e001d4045242c82d040568968402102c4090300026140241014101c2c04600d130f00066034004a00d81d000084c224541c0044050342400c0005041380c00c2c6203882d0040400d60409038152040340001e034400c0034139001c0d00340704680404083c0101529030600c4c41007805184601910101031150034021540111034070160300348588102c5043c0c040028041e1466407003a180c511a90340d0751f00a00c00100300070700840e4085401800c0492a004030404200807002c002c08a0100f00061202d10317034400003061007424001e011140041d00c03600214100076807034203c000340c0e194150044822100a854502c000e81742101c4031200a05c04241c80c507106c20000e002d10381c404841465080000400243c150300203140244001002181c42e04222a80a49407014028a150000c5c1c000058a00010860858591840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 608029919 1250 608028669 608028691
    0x90310140919080703030b060d05040b06040213031e0c060c050114010b04030b0a0e0102031f05090402031c14030408090103053409090f02030601020601170d0806010c0f060b010f080c03 81
    0x984241000c030300171f010300c07145194080c0f07000610025070030983d0001c0b03000e203001e6140c2d842c030740c2ca403030003040101e02c50a1074000e070b4602d003d8030400c08612422000b540d4001c1e4200e1020f042c3c2669aa003910340041a004003012481d404c0a50f424400f0921484500c07130955100105994188604240c0300d0285e40300c001d06c40d8845000066085510703800030301014800030300079500c90070300000c0c1e802d62001029100780603a170394181c00104d925015a03d90b014640280141401c05480c41a400d4024141e0b1000810710000354054054040c40d18000c511903030054109940b03d480c3c7d04001400e55201401141102285a0707140c411040c0c03154141100310b40d040800754004042c40019120300140b640110861860083c50b002041c0c1035400a42c0315000903130942c1c2090381c944583c0a000443c4240d0038945034403d1014122150096052940107801410406412a5251f8890035207045c0c0c510221905901c3d40324620980d43c0107a030b900302140b11801d19000d1480c00b5810300c0c2d0203008c0146901000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 608031169 1250 608029919 608029927
    0x50603040f050a111302190818060c0304150209031209040b0411070c0e070e010528021e0a0521071a150d02030c0405090309031014091908 61
    0x1590000c8000c01c0c59000b01510380741c0810341000102e001461100c1400741d5850214900701c031905100300c071800d5444145003440c41f000e00d5811642e40303000901040c1d018442d0000004603400800c004c03031040450003a6181e0320f290619000d100d4000f0380202219090040c0a2200e907540c020606540a040c00361f403007512141d44a002a02514440004a1304580703040c01d1101400070540040600344e00131039080004556980c1036101c1190304990010000300b0b00b9044907050742c801c0c0c008024400d07200460b00d4100d01e001503541d0442c0b1080b0b2211001d81e0007098408500148469850000350302c1c54094541a0855107900d51605801d03071502e030025a00044003009020094117841d07007a50000301400c103d0381d1040300d10b513001e01d00340d40e06071141809001c05001c40c504100000c808550250180401458000030300c0042c01c0081d01c0b034919400103124a401c076441c03c205031003000d40050800718a00d000504071400003d405801901030340c000904500c00d6500b1190440700040c3d2042000b551 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 608032419 1250 608031169 608031173
    0x51206040902060c0a150c0c1106040f0602060108010b060403030206040f020303041505030405250501050c10050106021f180210200c09060a05010801061206080319020d08010e01050d05100f0e0d031505060304 91
    0x102d4401c070780002680710514003005c030337a450780040c5090607a9a440020005c5d040035100300000d41c001d0380b20060059000f034000500151001014401461014007146d04040d107030040e01d44c0901c0c80d550a90000b41c804800c1100303120341005010a030703110b0621403040d41c00e00420800c440c00e6041c002d26040c0315000803005590b1408000782104a146914100010750315000001e40710141d04c2c001e80e07a044040136600c0d080c1c1c4424815480d107035a262441c45140a500c2c1d09000050030381c90140c0f001c4c0200034240b02800e070b001252510410031035034080c20200128000304031031007801038003142c040e074100345080c0001e980104001c2d055843d10f0501158005540100602400c13013a000750000d4080401c00394242c07609041100a0401d5079000d44010180c44041160307207050910444002c00107107801000b00c1d0230403c050701c001c24081c0043d541c0c3d40c026104a401a9102c0011408960307070340b00f00c000c03a000000d11050744040b007c0d1409001c006101c492045041e600c2d401001d12a060010114003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 608033669 1250 608032419 608032429
    0xc1809010f090e0708010c1110051311010309050a031e080c2a0a0b010f1215050a020d05010e07031404050604060b0619020708011506051206040902060c0a150c0c11 72
    0x200030445c130b030000d00c00180d145031700821a4080321440036140c4039164001921040d03500401d8410240c4c0b00e07046503200b0286c0c86002c0d81c6141501102d0625503240d4002011400c140148018580652a400b0181e4864041c02d0f8880c0184020101001408030501c0001c0503a802110504040050b00c0008244103000010500c0050074903c41c01d071040c2d2015204001100283e10304a030012090070442540c3c650a41041c110752000040845040e41000740e0007825503400f2a8120b041c0040060500c20038140d44003c95100ba002070301d801045000f040380c4d181d4140282da8001c14080400c0c0d9441c20280c0e6002e81d107a00c0035100420491b101c403100102c40d25050140d4000e14604a01c4800e250a81e202c040d4a4032450f004101c020750a090103011001903402e6898110343c156034806103014101c10400943c40307005406541d1207901d42c036441d000342c0d4850700905080c480700c401034a408e4246180004541c00d61103182602e450601401070740080d00880140e2884e60040000076082c00d10400140c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 608034919 1250 608033669 608033683
    0x10210804230904030f0e0409021c03200106081c080f0a02160b06010f0e2b1b0603051506040506090f040e0a0b09120915040b030c1809010f090e 63
    0x190300302c0c59002c1004281035002c8019010321809850304c0c1c0354480840305200c140d80c4a81c4020350003240042c0038442c087c010346c0458021500900d2b01000c0c0203914081603600c43e1200300c0b24a05a034403030317034184000c840910904101c490700942041c0302d0107103010094042c1500909038000c207042c0f8400241c13035100750b40466891a126003007034120448640303400200c80e4016079402d80002e080807146070000340111116008004001c21181c1c8000902041812035200b04a0316030150b0080e07105040050700030085c8402108224200c4203096042c8100107085510003030501c0c80540c03290820841d103454002c226000d60708103942c0d071070703a544515001c1411400462280783c0c0041c45c140d0b8107410300304080740c04034000d480b440c00e50305135031900040c5030344c0c690344038080040d1100b0410280c0302d1071034160180d40c40448070b2150a41001d541318150f200ca60001c03501e082d130a000000360218210a0500580c40281049441400550412000740c501d6003032030003694441562201010701c070210401c100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 608036169 1250 608034919 608034989
    0x1305030705070306020318121b0708060903190e0f120c150a0905010e060d0b03070305030307022b02060613020405041a0f09071e09080610210804 64
    0x1102c2143c0c0d00e181c007000a40c0101c85c64005030419540382c078007204002c03032880030301280c42c40a02c1c04d0070490549140a1403500113002d4103840360041c00a1075810501220344911b8281c405075844440c240391000c042e0139010004001c0040b6010304419035078503e00d00748070200d01035440346045035049103072915040c52811416480340c00d20650814184c24a0010b00d1402102d46c2c802903c3ca983d4001940c0000700300c12582c0c0e200c28140500200d0b0703501c9601c80a04000014100ca8090ba50394499500b141e000b5514000140c00c0fa00c407401880e1041c40205e8040c225a00da03610751382c50001c10080d100d400180c0039510079110ba89142e154520960161030240a00074000c00001c0e412090360362003411a0300100c1d02500780a075a00c215481d085180c140b03d0003483d140d50080390b40780c101301e60040034000d44103014400401c60200701041c0400200e44600041115010000d041030a0704c04a42d0a04149030b68400c0f07000c469a0000d41e014090303034200e612400341c13502d60250074001541102c040c0511 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 608037419 1250 608036169 608036173
    0x304060f1209120e01030b06030105040f020708130306060e0c03040b060105090a08010f050f0c0d09020303250302060105041a0d0507050603090a0b2d06030a0b1608090102121305030705 81
    0x50b106115110102920418441d290000c20000c6100150b0030303180f10400c5a58030080030f200411560400340c000c0043c2c0c910142005180c9070296546940a8204030240c6040e503010704011b2080080b18400c0304040c01000301081514540208481031520000b08010044c55070b150102d9496400340701550001080200108001602da806c543d0080181c0000703150040d044c90045040000c00c001124000e110b501c44680c50035601260072405029005400c070303094070040000d508681c00314100002c010076264031005d5005c850b414001d03e8a00c041c1c002e20f20492420000348404a44d4031a818080346050b1411660071410b8201682005850f50145800a4001040000c8000c0c042039000d003085c81075408034200e4031000c203a07140180c1050160003034403810b00030a4140160307000500ea0301400042c100d07130b801c00850761010051101501c0c0008400414084240c88a80100344564012900c0000b142000800c103241541a04090075042610004041c0b15040c45070503c211001d490700001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 608038669 1250 608037419 608037431
    0x2a05030319021203060a030305030403090e0423060c0421060501152303011a07020a0e07020d050304020d03050c1014040c0501020f070501050d0902090a0905010c0804050304060f12 79
    0x30009803907024054000c0041c000c01800341c0b0f540342c6920070350f80500c50113084048000d0842d0360658140c1d00c00b400035007d1107000140000e050419400381c91203a0301c9070750032104881d020203030021542d00048580040d83c00074020049410130b01c005440c225030041219004074403800380da03070780c0c81080220040c00c0c1500b0840082880c00c01c2c000030050001e0f00c0e58902c481c41c035a03207032017250450001d0480d101c1344a0400041001d17465054020103d240b05110080c90417050b0350014a80715003030380c8076555021400c02001000f0782c040c88038000310790312401d00c2da141d854181e00240c50045050001000d003c1c0104104100c010204850401250040010480c01c601041c0301c0444910445040703944044000e004500c40d407010588110002d004001846501e04040043d00c186c0c0246042c3d894490f516802680580ea0b001c0c070b5035006103040c010004940099042160940780010100c01c140184076050000040d0000304a9040350034902c0c0a40711001c014004981c03c40c0e86c0c422050312242810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 608039919 1250 608038669 608038687
    0x40314181815060307080a0c030b030f010501060305100b0702100c050708070305061602030d0f02160c05120304081018060c0806090a0c0f030b0a0306051905060a032a050303 76
    0x16074141d00404100c00e400100342e110700100b040d2840308844131400a401b0202044480c84280c10400c050310103070501260403412840401d00c2e14050a50803840c80c3e4403a401000800d4240c031550350013204461074223408905012141c605446400002400343e54003a2803040d189104865019940d80d01005440499540c1e851b80c1c1d41e01c0c0420300042c0d03018011140826403002c1080084850b6801c01d03005107041c00040000301008242c003103c2c00705840e0f001c0040026280300f050010040710703c81c04090010a003018140301c10042e44008442d095441004180005d400000342c294544510302400300d200017400760740240b1010071805c01852103003001001f050103504504c41030f12408040ea189041503031110160720945410100d81c4c4003160081c5521210907202c1d030845c0502101c05002c40000700c0c0d49640304d10498500312a14141000c0d243c2d4011740030381c49800b036607030807900444a1001f46401c54450712010803500e040d80132880c800603200d212540c0900c03000002400b0040540751204048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 608041169 1250 608039919 608039959
    0x3030a050901052d04080606010215070c021f0201290609060f040506070f060e0d090b0714250e04020109090209030a0f03030c1211040501080711071d070804031418 72
    0x350141c40702901a202c001440795100043d8198002a9511110b0f55a160710713405440c52081c64030b05036080208a11004180000000304003803604fd50313400002c3c650a08003886036216000042c3c403410905000d8600070329614030b4143d0300041422078042d50b90382c1c010f4103c02d060b0300c034a6110982026002c00d800b82070000c103289003c00d50307002d0182805010079051050b919554071003c0c1e00d01140c100e49007402624059400b401d80b07144034a0302c000f07441103c501c09614000510000381014881e10b26450740d1002c5407100800100032034030144001e82400d50001c1c00303148440c0a0740608560100300f0590581c0c1c204101c41040d904081007078816015410001c019002e20010400441c0b040c0007100c1f8059018890b0080b4489901030950800e4200340044030a0385000c0c0a103801c107c400071058103040014000c0100502c0a80d4014694052400a01002340300090159041c0300c002410840400c1c1c2104441810500107080e01760b42d441114808603200200e40c0032241c12184c40c00400c620f0000e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 608042419 1250 608041169 608041177
    0x51b070305010b1c20150c0c030f031918150833040207031812020310050f0a091407060909060b073c2003030a050901052d 54
    0x50f0b031800009010440305000c840c104c140018941c4141c0c02070702074a0f40d103684144a00040080c11300452800729801c4101542204126100507003295280c1d403402d107010003122454034404800f035400c10f580320301e14815075107455900c101802001c004440c00030500134148406002940d0b03c05002107014100209000800c40701d010a0b03410381c2c0c40f20b42501c0501c01440300711070907098150306114013490501029406c14201103040c41070031412804211580150310003d0180010152010305650042515040b82040009003d40c541824407420000048070540c0c40b03410110080b40301a610301d40b21102240c0c0c651080c10741e024203040031410396030001c090030845180113428030025071250340036401d1313220b4444000c284440700020924070140c0380c002d038030741a04040748601c0382e0683e516011901100d600002c44160305283c1004040034800c041164002d14150000c5041c00f000c918040d00600c2405082411701c84081840c18440c0721003801d400070a600342000c08400178420505a100781c00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 608043669 1250 608042419 608042441
    0x3040602090301051f0902071a01120510060e0103300f171611100f020903010c0c02010f0309151803091202010503040611120c03061e03030703051b07030501 69
    0x404e00010581400c074260303079946409000c0c60030f105242c1c64162404000d5221400450b00700c00c002d04019030815107a4202030080018452100f040d44013464150b08081c40c03607102e02646442c0c00002d2000d0400480401d040d2540b02e04174450801504032550301852a90550f03070314400c001c914882d030140e409480c010720f042d0103803120341c42d5080c250110701807094100c0f010007901130610000c01e980d500c900d007040320020015064403051861000440f040e11203044604c1e04150700082c41c40c0b918242403041c0141c1110a2401002d60b40065000030907241003000340708209921381080310300380841c41022072031100082600704003c09802803241070016035030720180e012645100d000a400e0714207005011480303505a440c1451580d40b50b50b248000d1400144000f050b08043c8982c40e0300710f850110710307030069000d01e29244d01c0386042c50411950309190f14011b422160a1003021640b61400419141c503c4e034542030507600e45128824035404041e42180d0390a0521403050700006204065100900c041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 608044919 1250 608043669 608043671
    0x906060f0206090303070309080738091b03010b030625020f070501050f070f0f0506100e0c0a03090209070801090501050609030d0c06061a03180f07060f0207050603040602090301 78
    0xd903012090b41c8031a000c032110301c0f080d00100005154030313220340c2c058280584243d95803410b140f416180c0c86c002c40805460200c601102c03100300d403220420351150034050401c1c20891070031440e00d03a61490700d650400310100c030710190603072801805a80030b4125240486000d0f04407040761400c031082000040c10b00c05038040590985003051140ca101003115400340881d0001400114035003001140c16920040040712802014065030300010ba03480c1945080b10f0060395140350101c5d0f68103065003007100203032400e00031408003203080100711a040d6090b40c0c0400034032070703054031018610782c103402a000d5000d0081d44803002501f0000403d8018103507505a840c030110800c4140c2e250700503c2010701c152a0000e074903030300142103600b52521031060640c21911452012905e25611304000c03601401c40242c4240c01c00d008010400c442c8112041da281800342c480003020f910f002c080d44c44d40c5a030101d0055208000c42c14800607280360081044000900e00945100d50b070340f0741820004000c3d0040300d0524440c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 608046169 1250 608044919 608044937
    0x60212090c011704230606030c0915012d020f1501050d200303030a020d050c091f0c0b070824060307030c031104030c06080c0408030d0f0b0307090606 66
    0x34400060511014078182c45100004120f140150001c1000410442d100f1242d00491102c000440b11241d10380b100040042c1400e084c244109400c3c20145400e95014412440802c4082042003403c089052001e003405030001861501c083c0e0240b40071b44960180302c26110f00b04881ca940002c41c13048845048040c1c500c01d803031100042d0700d04802841129401040c0c42c04260100c0d1607026061004807a1041101203850080e0100b81190002c0701c030200000d43c00f043d900070121b09409440d0344941051181803915000c400090101c55904081c510040b0b00401d0703a541175401172000702a01d5410800c030580500e00182c00030310650b011141c4604050380440b401542c5441055502181c0500078030b11820340d41d41c420100c000b400d508e4210300c205070301c07559904402004040200040c500034a451500941000300103045110080e0034141100e504102c10460000c0101c2035a504070708201002c00d0030080b203419480a0315285114a03414000c804002820003840e1380040220342c0e882e2144080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 608047419 1250 608046169 608046181
    0x219180e0402060f09060c07080d02070e190e0f0109060204050a051c030305090c0604080304080105010b0a0203040b0a20060402030609030f1617040602060a0f020f0910120207060212 80
    0xd8000e041d40d000350424401d0140e0320f61201d181001e00050a4040c00e03035410700302c1c60010346242c041260f0100110740c20500c080424981d040c4090009400240c0941d5114280703000300d170001c11070480c3d200c400a6990300c001190a030003400b840004000f5080280003801450808100950180c45064410030100000159a0814450400090321800d40300c59028100d520309601600d030041526070103000700074121f04280c0c2d441e000340002d090f07084001d54499060100349802c551040e00704e030750022400d02815001c0d07035001007250181d845020007542c568000c0b040954450042031480b140e007403090380c4121030000001914504c258021400c992084c1c8071404066264811404080c102d003908012181c02c407000c8d03500c2c0590342c078070030080380c1001c50b46400340038403d4100c5d4202c0c5005030441c40500194203604d000d02d400c803008021045207842c200c44401c1c8901d209150084d401400341c03004000384940590080880008010001c3d561980c8030b1820740d0007913000c1003008404000c0394001c985 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 608048669 1250 608047419 608047439
    0x4150e01090f06020309010815030f0102031906030503041a090a1205100b0a0302040e0c0603100303020d090f03031803060e0d020709060503030423060d0504030206060d08030a020904021918 83
    0x1c43e0840c0d0040e40c50310350110011200210010004200d51610000c0d860854404018990030704110400060f02da00304002001c1440d04225030140700c5134180481400441c40202c1214202d03503152105150008904081c10310318041c4000da9079021488078400100003d0001140d0101c1c1e200f8002c1c1c03140e0b24403022502040303a881c10340254010b610b500081c401030401c2d9129807800081c03d000c940300701c0d62200011f0203550003203400700007400400c00d0820406404001c40c0c80307002c1c00c1d424851b14003070500340c44c0d098140322407002504000035880d00900d50040c0c2c482c0ca40195030401d00a000301c0245092031692800800c0040380148901c28002544144030311601090b144014041c61070140307072401c40a80d8030340701c207840d003200050300000c004607691303200040c07054501c2c0312f4022520345401e080c0a401e20200901260060446504107000240080b0407661300c000000401601d4002c031101080c020b028a02ca111031900820b0b080b81c012940007a11410640c07840c40180c0f01d41c5840f000c140e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 608049919 1250 608048669 608048699
    0xc060c1401110904021e04092f0901050325051e0405033007050706080919020907021603060e06063a08120603010c0903052104150e0109 60
    0x70000b2002400542014582030700149500043d43c200302206900480c0078524550240e0f20070074001d5580c120313100040602039131100035013004164198681254000011162040f50b4400e0b04000c0c000001507076001e00f4400b522024200e582100010b0003400201610581c0011912840c192848074200c80149044007243c090f00c07400b40181510074032651103000c01c44044e244102c10385000d0060740040c0c0d809a0f01420a8500420040248514011000d0024003000d0150308a07500040c0d00d82549085003254034807015810ba0308081d1076940c1c1c0c0e008a0900b21600c41650407484001000010b11040e6041070b269044100c060700e095403500c40410840ca02914100b003101c2c0e507003c10b50b5201204003148082c010501400728003910703019549071592a0300070880d0100726031200060121604091065010401090510321412030958552a90720b0028120301d0441103040e8040e0019110444242d60080c0890101c41d407201c0340d44d0340e02404c1094000000d50010343d8945000500d51540c007100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 608051169 1250 608049919 608049941
    0x204170c09090d170702030408250f12110303190903020301110408060114031e0114010504270f060c08180616050a170c0a08060f060913090c060c1401 66
    0x881d030005a02131841040e450010100c01c2540024000012010018050264503071403013151895200c09005583c2c070100383d20341141d003a10440000500450403a11845030b0241e40054075403410100f080006460340c402d441d61072800003c0c8604d02e03688183c002d40d0440a40384210024017076114810000d544501580c0f14186040e4095001004601394103104148c00d440054141c948017206840d0101d450402c4082c0648d281c2e5403003049000600c42c007895280501002c0354280070481050031088048070080000c4840c1c1c10002c140001080035440d4402252a4030034000d010354040054082c0c0603000440786c0b03241804c108905501190404241240f14403e01841443c0c940c082d00030486564000b8074400301400060210041000c1c03c846556200e140e001d080d45903642032460000340008005004140034601500040410303554400569200c140c0980321001000c04009550004d404901d0010300004060072021070401c0c2e01408609900740908003074032038101418842d44c02c0320088002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 608052419 1250 608051169 608051177
    0x905061b030d41070309021f0201140106021213051305161404090e0a0204050a06170c06030f22030c020f0d050703170c01050c090103060506120f0a0204170c09090d 72
    0x2060301c00e2203c07200d0750048402d240003d941101a804680c80f400100d040c4150351000c02840c01e611a8240503d06024540403080000355252684c065030f20542c0251b5030200c84404180340e110720110034401001411300420050102079076010000040009590b50032003850541000d80c0c4d554001e80c2c80308044084d04003040d1800c0c1c5031034044802003101c0741c043e04460007100d658402580d510b0065601440610600003965032804000c40302241d503540a114103500020b808001a58600303042c1d950000c003200750020140e43e44401000b0320b21511010800420000359500b080c15071002d01c25031024400e40380c1c5244804a032080213607400c4943c80081076584a03510600c0092080050758803c00000c5866034100b006103040d25095602c00c50b00300c0382140d408180a0641d60307050280e0340c01014141c54452402c152a65100e82841e402081000309074841c402041a400040e412600104840f984542c003d100321200300740c49021030141c00380f02d100b28034040742d00300c100862669020012a2a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 608053669 1250 608052419 608052521
    0x30b06030d2304030b0a06050108011703071502191701050f091303030e030406030b030601050105130905060d02040e0d09170c01080405010605091905160905061b030d 73
    0x10401c0a01c840400c080c00164030602c40040003076405c40840b8001c81c44a40e0124809040c0400142070010582c040010002003140c0045c0811000c0b0884440703d0704072002440c04001912010080d1098404040c0644010b02018031040c0e84811207405003112000400d0381640e07107030204603450140002c5281e0054099001c04c2074402c49100c0600e005101e804d022884040e5000d2950841e00f141d408480400d460304011b01584c80d080c02000d02614003420413a041007030800e0b024002450501034503050a941e40c3c0031410595410406ca000d10b075000b407051102c0d0140700111922021102415008941d0490700400c9000d1021410000b1040990081002440020045034007240281058a095517180c0000c90f06445401e41a0320416842c0410700458006400351000c071500142212403164440d0604070703030107a01800000494000f281d0030b82e1502c7c03c8020402891981000700c81d0203200008540b1006001a0001144864100740c9003d8141d42842e04010003c140480a103603245916 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 608054919 1250 608053669 608053697
    0x303082d070e060c0106030c08060c03011e081e06060d110112021e030103030813020a0b0a03021b06061504030b18030c070308030a060909030e09091501030606030b06030d 75
    0x32441550040d103518080c00070503400c001040440d44100d40e2808aa511218140f0a005a02c5106001840440f00510941ca8440b4120355a400107005d8003040341070403248000081c85010307002c07014200c401d09a840320581030030001351011029620404901518000903503a141c83e07502401c03407035008805c10400e59441c000440d04000c8001082d0b40142e1309222401c284803000f0a003c2c40031040d401f40c0360340c0303504609016101c401c0081c66240300c186a207881c000182c507289501c000302e070741001c074035600c50401100603406405051003d020a51040d41c100101003400075150707002d00d0701541c880710a40d0180b07504884500c11800064400840003002c2541c1000140210001031780b9082035a0a003c1c02162071070600f44940e0090703d58200200c03d0000d007250700d1040300020200c28204002820841d500a800d00850040003440b62a2200004440781c109105030b60220000d0a449035803513850346020f40090849000607920140f00030001402c50400003022500c0e0000c41d268244002844 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 608056169 1250 608054919 608055001
    0x20f0907093b040f1104020c070b0703270e0a090605040f211713050a0602120a0506130c021606090f0e0c16020102030f0a0806030c0102061b0d150f030308 68
    0x60306184d00264204042340000c030060140f50702902e8900500395485209050040c18000c004000003000010513070150103954111950744101d0ba210a14003c180d9280c00b462002490200c42c0544000c2c24401000204a421081520301c1b034402c07041d84208005070190000100306503188280820814420001135447d2813008652000150101c4030120780c0c0340c7e44003070034118006401c950490f00850180d483e00890b01e0140d502c4000c0c0c000c10081454850300056440c3c08842003542000da6800003000414802d00500d10749031080d80007510354541c1c0d080b0007060020700344a4107100303440c03d400c0850350243c01c1c0d145a00840398030024900340b0b1700d40e030715900d1003ca04d46001c13810740c071040002020031036019015140380d8010341ca600d200381c41c184c0281801c1c103442300c071005d0441d00039904002c003d40c50844202001808448015103440030b0030301c03400003041582c003004c0303821038024000180140014004400e59109135249580340d107071550000d4000c4803403641c3c0190502c51200d101640c100b8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 608057419 1250 608056169 608056193
    0xf030c0d0804140d080a0b030a080403060f0b10020c040f060f06050d021210140102010608030313050a0c0909051908030c07030210060f050406080604020f0907093b040f 74
    0x3d0440c110324482c2e4140761034940095400400b002c9900c402c10006004141d205004c1300c0e01d005e8010303202c82022651092002d11650000410442d075501e620b40d6908040e91006946010107003d2048002c0c1e9040082d50741c2c0c1c084080302c0d10413404c04c0c100340440080d50040c0300c21100d461102188031810210240c980e600203520007042c00e9070030312500d01124400e00e030150261021880c150300880c01c0c0482e411a1301085461103040d6030400100b08084007001046075481a9200f00c0d10403010000d03c0c1103070900c404031030080d08044140c1c6010031002003c0d80300c681c01511800403603c0c01a031080454040c00c0480034040d00e011401d00c0002e20110703014000b080154400e2059594500d0041c1c400303002c41344140c004502509428505101701c1c1010311944001d41144030040040d8545640000e00700f0000c1d00b062802a001c03c008210030303d000e403a082c00540900703580e11050941c0c2c0c0c259440001c4502800403607a8aa25400140310020380002034040c6030426522030411805484280300284 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 608058669 1250 608057419 608057423
    0x1a0f030414030c0d0c0314030f010b13170705090123040f291207080c10030b03101a0904020d02210f010204081b010504171603050f0f030c0d0804 64
    0x1042010f02d01d480903c8090395440c05038032000d4400c1541d040080034040c08031800441c00d002001807003030010105010604585038014090303a914000c40d02241c0350300740d81d41310481c07107492600300703200d14040440d803902515016601c1800316030381c440344003a45032150070784043c1d41c0300f42d01543e2203941441d070810003a001c5c0c07039000441d02205a000001c8100da40040154400e0004151000207280c200f101400c1318001c10020b1496134103025100d500d03000568070703880c0700b01070440e050070b0300340d00940200e40d042c41c00a0a4076503c4401e07001d0000a8030010082e02d02000f007040d51006113140c400c2d20741d03020301c0e0042d10825240d01d0a50901c040041501c04514054880100031465000308200203400c03800c80c600050303240ca01e0310301d40e82d20b4a408910100700d1411020101d04a990380281030f1800c8907010425240c01e00031002c503843c00c0c000e10041104c00c10300039a41c007109201000038945200c0c3c80c01c4049400c1c8210304601c90745c8078081e46030580f00542001e0011180c1e40d100c1e04845402c14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 608059919 1250 608058669 608058673
    0x180c0e0607030806041812121a06030a14090304150c170d060f0602030702010e030105010b070f03121a09070801050a14010212160512120103030f1b0305041a0f030414 73
    0x107401b41d41801d41020110008541c00c40500181c20049503000720302ca4082500003100b0300c9000c6c041002d07078042c5006904600c2c000c0c0004400034050301680d03044015085003086204030941070204031161240d10a02411901043c000400700c0e07140d01c940b4544103206d40080b4608a0b1040048020100750f020b41d401d036800c1c40e29420081071342c601d0192400002e1026800855690060f44005048492006612446a45011300402580700e10a0846400039441181402c582c00c42e441c05039542054200150005d0b49040601d80c60b000342403c880030780c404200c580d881950b40d8034108640e01e001c2405090780004011104012105625141e24014681401504c801340d86003c1c0d00000e5030400d2600c14020002c141d0b034081813000a018131b001c40c4000b02d035024500201401a000c92a0041c400201000740051141c00306d18032a622820054100c9895040301e080c15050041040d0042d0040501c24041101c4907003c0c268503804498812004680150a503501c9449000860180da0741c0b44200d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 608061169 1250 608059919 608059931
    0x7080f04120c03230306040b19090c050c0d0801061106060d060b060d1a0f01020f0303061314040f0b01151d0105040b070f15091104090305040807180c0e060703080604 73
    0x8501841d500404041001e1301c0607101c4c0303490300410083e2104280b4480c010810301d80c0c04001d20a032002588162060100081a160016403040301c882c82100c642655500400c481c0c18561a1300040441c103d032959540c1100c08200c0d5056240c40c0c12007503594642c04414030300080c0020b401600440d42c6000014195402d00303403a40b945000780c9050340071600c0c50042019281c2000c0c9480c0340300b142404130030b200810f0103411001d801c40d41c2c1e00c000303032100c1c0c840d805860500300403182a4104640016400316408510706240c5080c544007242000c040358404202400803c210998529165801e0700c1c2d03941e42a6a1110036900407940c05083c028a41040f60412011481e16011401485203a201d211002c4485e102070801d00c40d00c52501403064240d03404d1565410202d41d41c514040050201201c00050b030f59403502d01612503210300da2002c881801680c2d0002032610301030220001c607042012040c401600000303011a00c4032090480254080010310400c404a442800415441080a0700c00508 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 608062419 1250 608061169 608061197
    0x210a06080f01090204140c1206060403020a030809090105030f031608040503061609050d03080a0b030a0b0a0e0f030c070b1b0313031b050901120f0204090b07080f04120c03 75
    0x4140c500a800c0c40d0680d12050f011046040500c1805122100555860000d0070207880b007000303511440c0003d40d103400c00300d00490140d80d40c00c000c560040d54020041d0801a641e443c01d644641c00c04844180f2807103130380000003503a00340428503036841910203002d0341c50b096515900504600d0000c0c01541c10300c40a01010844d0b44081000a0042c6510000d00d240d12030784a00091520b55103802043c02209880c00c002c0c0042d80054107030b500701190400108000340d03440d0200e490040c2000020349002c0c040001d100109281b50300c505102400341c1c1c1a60308660318100720340e9403441002d41e000718651169108104000001c0301400b010401102c440c009100305001e0180745030001404000d044140704000c00800c0140342100c0035242510244100c59494180040e00c030400500c43d80c0221007c8030701140400c0b002502b81d11403d0360040080000300c4280c2001c030080c1d0340444a00021981c0c41011803404032403424030a12580e0b01c001494402101444200c4111717008080c2117040c00019108445 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 608063669 1250 608062419 608062423
    0x260d09031704030801081b0306061017040311070e06060f0a09030c09020d0c0c032102090d0c05010e0102190f0309030812060a0f0506030c09190902070b0c210a0608 72
    0x4010b0707000f591654101e505214501d428085030710082600c000c3c5201d00040e07961400b050b0710b0351200044071440420000343d40d056413504482445a040c10f40e405041008044d00002c1c0b5000b062070601c00c488480341c6855041c0203096095860b507078050300074400c40c00d0704170401c070050924051900d491401e4540c0d07945e5035494119076401004495801159900c2c0440c441d1141440300b61444c680445005010b460181000c2e0181d01d142254401802d5104c400704261b40403a082420080e22404060709141440c03050030b03480d40203a50028842c507110b5119076100007480d0603447c20511582283c0c03002540c0c0da499542010360704409001410000002140514016020a10084819403103030702c0d05604110500495401c9000c5010345128140540d445400c2602d0b4406029007455a0310014003000441400b1040f1008452000088020030700403000e4028010861042103840c20b40d45420043e1602c0e8020030b130a1000307898518840c0c03615548036010381030b0002c451000000e5030540f0303100058 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 608064919 1250 608063669 608063671
    0x1103030a02010c02060a0b090f070504170a060b01081b180904050c0405060102061308160804030c031104091205030612030c0d0e09041e1502070609260d090317 70
    0x380141c0d640380034003503100d80c041c4100c0d54051484001004018100400928103241c080c00a00c03202035140005000e15008a046401510151003840e2191181240352030f5940203400003103680c1c60502c040345e0322075401141068040e55207040d0301200281e8130100c2c800395400441480301003015020f1038035510788600030b0382400b030350190001e01100081c41050105441d80507100724110b52009080004614103100c0c080e15503948455841d9a036078041810284004003140c2c003070a03050000030004200812802d210003140c0c03150b4007203495100d1034000c12080340d0500c40080d214003100400c01001d140700740011584020010031983c50030790103809803803450700001c4001c0c0c8168001d5450f80301d0245c0100d8840e4840c00d04442d4648289070035982c0c00218103400414628501a00250070100100d10307000f4032100341c55840454a5800c2070130945c018080d0070714107842075403200c543c080c681e03410020341100004070030880d10315211129103660300800202c00190f04000070b41c2c02403420b06a03d49801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 608066169 1250 608064919 608064937
    0xa123c1a13150b041e03050309010c03092c0a0203060d020907030f1109031e0d030b030a0813060f02030c0a1203141302010f230307031e060f0807050f0d110303 70
    0x26840700e0070700c210488807010342c40c5c15002c01007000d08100000b88000040300c000e40000c0c03070501c4907079003549001d8440110b5a00020055140302402040c0520b441c4410070b4090b1600e180400300b83c03109140001280f10a8400540250b00c141d1032101500301320540303903040159864001481c906c2d6080401c1201d41c208a140400d17400090031107002d2804006800d044084440a1509000e17502130b0299114403802200090540383c03900840150340502c84540d5082e007041020340d4480784e1743c05503402e18a0501401000c2141080040d00c07007440001661800700c1c0c800024481c0055503210406d500481040f17410070036888100080030b00e1010b0301d0781402403000700c2910340d03441041c1c4005003140840d45003150401420315441d9034400e44912400c81d0707640000400c155280c0300c03248102d018200c03164001d501c2103146c954580b0b60400079440201280e148005c0402c01507107030a070040e202c2c2c90034400d41e40e2240c54002044603514011442c0c5400520494040d101800000301090441e000401c1c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 608067419 1250 608066169 608066189
    0xc1202031003120302090f040504050c0d050c190608040308180d0305040c0518010b090f0405040320030f09040e0304050307060507260a123c1a1315 65
    0x104008105509482031580038a605040d41048505400300700c0030000047c08038070a41c0c5402c045001c0c800140104a011407000e04001110340039400c00640d5181403000103800b0f80e00310074200001048001d01c0400351841c2d5034a8004a446548040310040e10242941c540380e460031030080c49141e8200540b02c9044202c0e18082030320310b0141090f402000c0c00c2e500031742c011044110820640341081c00d03818150b98420035525103031041040800c005850384600300380c000e45008180400d0580204500b82240c11040319a40140c1182007903584034050140600c00c41c0d02c0500c400b8025140c10742024a40c414904200ca00305940e841c00685021034640c814408034000240e00f8003800111502c8101800752507070f1070100c58000c502c581007540300b005841003c1145500fa440d90201c2a17404c8030705849000103a0040700d046000c402000d03240b144594143c610300c001075804400340c56001d8003c801d4103110031498242d00b04010b02c42c181d50312428000d0055603a81600d5079180361100183c002d0203800c07074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 608068669 1250 608067419 608067451
    0xb04060c03030513050a200d0f1103011118130f0c0f0504080705060306011808030a020f070e0c090316150e01020c030703240f02030709150906030c120203 68
    0x6000c2c0442d500986980b084640f070b0b41c10b4202240000032440b0a03154804024500e40c2e01039141101c034170500c1c3d0546580300d4043d84e450030a20200602c1207100070300421007110301c56500740400d400c0b00ca00700024040900107110700c1500301d480004000701210094200d000c0b240f9080604022240400c8150b4140307507440c682044096807084100c0d000851a0900501e0300d402e013a003132030351400203210301ca2040780c0020000f08aa41320b030780a1f42c0d0300c5408c07122556026449500142d01d80e080017503200e00501c40ca030750541080500003610030484072082803004007138485180b2115030f41c1c00004443d81500c5a00c444014210b58024524000c2c941d03540080308030b824005005010403003400c2c21504561091a403070a2996000c41c54104480e44468a0100f0362111600381c9540801480280c4072a481c24044c07410113a21600150b21460f0280c3c0d0303c02c007203505d840b040080032041c943c400002410307001d000c1c0714807402035002c0000c400484c141404880c821081c2281a60b0040380e420b240010016 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 608069919 1250 608068669 608068673
    0x20a0b0405030d050c1201031101050415030917072d0f0609232d01090302030d060b03010803040603020c012910031116020a030606231507020603100b04060c 69
    0x4c0300d903503000040d4144a900d0b0030315007050328040c000180400b0340398100300d03203d10803680e01400803540108000003a10f40134036010b05000d8001c240318841502c0102c0002d005540024221003100c11240c0d2000152040e030810f0b034460300c201e148080d00e400a11444c400c0702e0010441c6000d018800d03d100b0b06022800000c10320701107a01460040050b20719500e403919040e600c207030200b02900802ea2821071070242075150f003e000c0c4084a4285404141c2d484d0150300c406056001c0010120800303a480c042c0091075603002039418a2109105040d155001400203100701407103600100102c043d9400080342c507100400390142c6079400280c90b0300303000300c3c80300d40207070581400800922502054241002500e906a143d20510b10940740040c89282c0c650549a04640d01d1441040195801c20000c0018540791020140c45c40703031100820440c10702104c88081c00d172070504c000c641140c106800c4941801100d43c240142c0790000303000c040c0320300440000400e0040c400800780005107010b5031042e510162078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 608071169 1250 608069919 608069921
    0x4030812090d031e09020f0604090e0c100801060c030c02130509060906060109050609011e0c0218060a0e0c0702030a0320120306090907090608030406030e011a0f01020a0b0405030d 79
    0xe006409041c18110304694035102c040d004c0b02c41c003c40610100d030190703941c4005080860202010381c5d1183c40450003080d400e502e0b500105843c542e481c03c4032895900c03c0100030006134004558800030701c1d901c0c01840a41d01c034200e100445072090400e1000032a260740024100144001258066603585040010450781080b545811403035a1001c1c2203207041035000200f000000c0c0c0074803401440d0000c0c40b0380d250303489000c645614004110490f407032004a0f040007403203451549010382c0f050b13143c0b103001c0e000000581101750140000516660034249007041521030450010302d0701b035248a0a00040740035880c240181e002c524400c1e80c03032113440c0e082c0044000c8a025400c1c03525200d40d02c180f5424002e00306442c00c0f00d410030b204854001413566081011031802c84039400c050495828100002141e07200000a8002e80f10b280d1000d01c020780c009010f4034200c845006081e03d03107049000d0048441d0601e80290003103980103206860383e10680c1d4841404902d8181c504880981c0001200041b034050303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 608072419 1250 608071169 608071183
    0x14130603030c06050109180b071206031a0601050307120c030b0603070201090b100b0909060a05030f030406121e1a0411030406050c0304080d050604090b0f0f0106030b21030403081209 80
    0xb5150080000740d0b100180005580c0200314008c19052140020400e01805613401000090102405220799038170b901d05400d4602c5000e007038001000000e00403070720960040040c0c03880b6800b146d8515817501001c0003010054103602011109044d52181c00042c642c43d004000c6120710301d40c0e000814003a5951800a40008004000d4030010815040601a0115480403134405810440307030910151188130004a0040b010b500076541071085c40412100998040042c0c01240c025031a640d01c12801c0b822141c090b1090b52400c02e50503617010807402c14000361036001140e204003081021060b21540d4000c5412240200500058646c0200800c001c11182c0d009a030703880f0984111031800e40c20203035101e81440c02044d1415154a49460000d10184c84070390006a003160040f84001407030414122103006202d0580310402070344814800412414041e00a02105010203030103812400022124800541003070041c044c4680002c01c00007011038071100250440080c1300800d0703543c0e0700f0300102c0140b800d10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 608073669 1250 608072419 608072429
    0x150b0703110f070803071119080d030f02070f020d05010e07081e010603020f0111010908070609030807020f0705060c0115090608070f05010516030c0b0403090504180b0114130603030c060501 83
    0x3010000901820b2800310555589987c441000740e20300385081c0005812140c015282e41d400100c5103400280004d0000d9880312801c41600c00f040f4400210030f441050703200f0300303030050205110f0400500050510101d0b810a1500940c000600c03901c854404500b06800e50703010680d01d500000b10b0780e070051104c0559140d0f0030018002040060310f0344e8045011005000c07516070602011603441684010f00b9081503000c690b00600195039070111349001ca00426554200340d00050310381c00018034070b6000281c0c0e030000c90b00040080100521b84020480c80e40d108402000c0c0301c1d500d80c00041d42840d20030003c04050640b055000c00c80c13506040e0000c0c82d001081c0d212170100600d448003081031783d070000121000c018034810302003e94215400c0c10740369000e4188004208410900c10031040c141d100d944a015079108a40c00d01c800782e0f4000604400c00340741000a8010070200004011000180101c0b809100000d007080303081845001450701240c0351680290b001c501c14918200400c0154480c1e1400f504e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 608074919 1250 608073669 608073673
    0xd0f050615121f030f03020d08060405060a05130605120604061b05040b090a05100e0a06030603051f0e06090a03030f0920011218110405040312150b0703110f 69
    0x2d0241001c0c0c00324102c0140414141e1003c200801d2080c0341c4101101c80a1500017001c03c421520601c0c00942d1040c0d0071023105c0014104401084241c074250044034083c3e040104810005410001001141401115943d80203545d030080010b080d103840c91080c0000343c0110240880303181c68105201501c9161a001d590b00e10100124114240c000c2c0694003950400f2013519120302c11000450000b20f0150005540502e0442210403199840040380700001ca080c0c1d4a401115507440d4268107603501400001c2180d008820075001490754041c0c3e4107030042d070000010500455070b0300010b00341141596005615002903240800b4142c03d0702510040e035072041001c11422242d40c9600042410403444640a000200e081c52003681c810400c0004600c010b2604100380b6421550050000ca5280c40484107808004190680c901d0f00307100d4035104581585071941070a0b102e511480003408120f0040141601491001c50550201c80242c413045100b038841c0280801070703c400a1820503140034880c455 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 608076169 1250 608074919 608074927
    0x3060b06070b1501030f060b1b0f030a0c050c0a0b0a020c01020706090e15060a02031210050105030c0a030f02120f280e0a02041a010f0c02030a0b0a020d0f050615 71
    0xd162035a00781d484000c031925603803042c05440048024007591300d0983c906c01d00b00782001c03071a2010100209452a440a222100c041c02c9666207920340d0508207801003141c0041c03003a0013605004a05042d1058400c4d8266415418220b0004000e003807186c102d001d420602040d03c038517180d0100054007100c44240000c20110b0310308000146801d02d20300600c01c249a04070045180c3c50a4500704050742d80004100c0b6858101240c0025a00d80003210001c0c0002803840c040b43d42d620525510304140c50303060751410302d10b946410800352980d00c04400c101c201680c4019640306201c551000e041c60565503a1100d00d14101003540124a030300c0070b402c0c603120b5810f0461580e10b4a80698035500c87d0043d031013010400c000c41440580c209100040c0207904203051847d006060202810b0b04010f02c03900341c030740d8010001c061a08540ca189007210094166200d1041c07800422080d4042560150010801516001140c010318040d2448960442105510b41040c429646000c40d040f40d41d254011078141d082c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 608077419 1250 608076169 608076173
    0x50309190b16050109050114160503010b030c0c0f061e06220e012d0615120b0a050441130212061e06011b030e121603060b0607 56
    0x290348621210202e42008a440810800200b9040b41c000355030003800800c091010301d001c0440419040ba1030340d055402c503110741c0b00041d0141c0103480c1a184040886421540c1f0810303803854646c040c0e00c0003001c41c49a00170f00f142003041000441d1094081601980141165003584110803c0182c0f01074424040407001b000c0c208800441507140c000600c1c004100306408010380f0340142541a44030401c0b4150280c2104c01c002a0784111303480202c046010000320f5680d07500601211515203101c0001180e141040950ba84140c00c10480220b000b010310303440c10354400000c0c044860a40600b40c100c0c20550701000707a405948180395851001120000c583c240598104410100040090361001511800b035810f42d215440320003540f01c4030314201c1d581410310114101c4207078590b01e40b1505948004000491551003a1408801200d044145400500d000e40c1c0030359500b00c850401a4100880b09e1a1300e84140082007000301e5142207418030100d4500754182003081c0c4004692042c010002007043c800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 608078669 1250 608077419 608077439
    0x626060607020d020609060f071e12030507171509010608010612050405070b0c0319050906270a140a0e010302090c0304060e0d0e101103041e030f05030919 68
    0x141d541101d800241089504c0000d010b40291600c0e19000030000c82c500b0003082d0070030300800b941703806803039189542007034000031003200b000408004221040c1c503e080080c4034080c2c3c2103280c10400c0c90503da44801141c3c82c0f40200108200d13080d240d51900c0b554030300200d08080c41018007512091030f10b003400790304299002d030501803252180382c41513603181d0006050010a11003000600924400b0f144c0c0c0da421060040d5481d041084100b1500c2c02c094031441d140c03400f880440307a07004d9025007110f00f4024903082d0448000088060020b00000c00da4190306143d07507100f01180545011001144c0111825003445a40c00342a002030440810700f10040c4056601d2496072940501213914030307aa00e07a110300c0c091014243c4c0c114260010b00c10244c0e98503100381c101142c0f0164000594180c03886d440403070422907140100244601c9070b600f04200600001311551000090441e010350759000d829034030760f030f800000e02120500382d4083c0c101041111540c80c100c68121000f546002c445401181800500c0d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 608079919 1250 608078669 608078677
    0x605070f0801181103100518190e010b220b01030b1809030d0203090705040e0d080f0c1c0b0f1909021303050102070b010509062704080408060106260606 67
    0x403e00070920000300e50484400e0f00500c101408005003181c030390420070419103008a031802810310030140c0c85941ea010b0788400e45400d00c00c401482416205138540307034441004101c0c1d440c8400140d501c40191010f40d1301d600d00c450104855464070b141d8020001c0d03809208803092100da2904050401c42420300d9903554100c006900d03412101c190505803200e00295181d17100e10325000d10101c2c008010030019802c0403680c0411201c0582c1c040c030007900448590390b00d0341c000e0580c9002081410380450080c5032669243d0f5030194404c1c40c20303482e00200200c0102c0522801709510045611200070703015a0a1605024200010a940c0d0200200310503280007114411401515030055010942002003540000c144004580100086503103407124100500070540034014280a03400e40c0c0041400da0400402c1d081c4e4400900c0d240f50918124181c4d440e12620003c1e1081d6506441030001180e0043c060040f01e00800035030710b0300c0181070449900d0f9000d088884c1c034051070000c000300c10010345881d107030111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 608081169 1250 608079919 608079929
    0x100e040f061202130b03060711190b0f042d050f060402060d0213031a0f240105070809040c020a1110050409050618160327030810050d08070605070f0801 67
    0x16295199003e1104c8020034012035920351500c50482441640ca411039110a60140c1e142c0503142000485040d0105400300b02d4001068000d1880001e07180e500d044161b5600a0701c96442400007000943c40700107007150104102003e4280703080c0c0303c0100f0004029030103890708608003400041c5002c0c3c0003d001800381450840c031160700025810a0034811089110103554041403c6c25602800f00341403c0302201116041c503408201c0c000315507600c402c80c0501da107035400c0540204c100d2000c04c0044a05800c42d9404551180040c0700000640c1e88130b00900311100429400ac100010490616103410b4110710f40050041078403a80c581d18480d80041140d040e10714100c0301095580390100411a0008a401d0462003c0d1101c4c0c14451088100344060b102c500762580d051101c9107400d407a04140c814803400c8203196103000040c43c40000e000d21012a40850080d1408640e107940b070340800c03030f003450118007122005800100141082000c0c030450b60003000c189000c42961a000d50043c1800ca8103020b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 608082419 1250 608081169 608081179
    0x106091a1c120f1106010902031e0402030c060904020702060c0a020102190b2805090f0d02300c0102161e0c030b0903131401200c090a0b100e040f061202 67
    0x110007095000f40e014032000c1004078115076003587c0d2800a4002500160b40d80000a0034040c3c00d00c0c00750142152003401680c0040140005500034010007440c0d078402808036800c42c9e003d1282a001d80c0d2008050500d42c6e240002138140482503100080c10401100c0801080c1c424141c0000041580c44004070f50000c260480c000c1501c00c000b2101482d140503000c2c6044c502c0c200810424000c102081c0345602c0b02d403d40880780024624102642c50303c101991003140324840f518401c10380e4202803403110503c1c40320f43c01c0794074029496003520b00b0380c0e10140f04d605000302c20004813030130881c4031020300010120751071100868046513900d11040481038070006e81040e8051001ca02010414001c48001d0741140c590900d52179a2002c0700240e060b4610201408207402c03040340703074110300c60b6540c4e4119500c484010700300d0210510101700100780f0140901c20401d55400c50455291903200341640c1c0f40310181c490dc050000007904000555140e248502030050400004021044600c0c00f641f59480c0c0c1114 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 608083669 1250 608082419 608082437
    0x7140d03031b03060302010e243103031d0d140102090604030623010303170417040b03312306101719020103090201020106091a1c12 58
    0x4040700a484185640115040440010300c000394042e80000c2c126071003030321108415020351081103001d00e40c40e00340310f500131142e0300c5280300c0800340401001143c80804d800c4000d1005d6880351880c820400d00c44600031a220002801815005a00c103148401c51112500c0c528842e02e001c110340910a04004100a50201c1111403041080d016140c044c01d010700b986031525038a04007034015020521103081001e13818400031310389500251000d41070741d40588544080030445501340c040c5e5900100b06444030124240c0ea03c3c5c4422200340140011b00f8855415512400c2115400712002c3c0455a4100c81812040000c54045156002c40c034850782c1003031421142080f40781044410001b0742d0213082d59400f0300c10400c208c4070003a03890030b0240d554101921040d40e102001c056550448034542032010301031400300c2c500640c0310760050801c4901c1031001154990b59566010140d071900c00e040c400ca1001004102d03031504220f110f90752008203446c002600d50101d80c60301c64800000000000420074492 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 608084919 1250 608083669 608083673
    0x5090405091501171605060a0806211e0c01021c0e0414070f03090c1a0c0304170d0c1110050c1006090b011409060c0a080408011d0c090f07020111280207140d 69
    0x481212f41c100c5801c2e000c418002805d110383c0b24880300215201c001c601490400101000091059107580e040e0020300c020065580800107080c0004a0941003140481e52524903445600400c180b8200740b9100c1415804e040700003500000c8020301c2003080501c0d0171685004103200f2825181200e55031a014500c40505c030943e510f01d40310300c26100001b4800040d001500d02120840c0084008400707050783c525440c0094220340c01803407140301070001009403036540b01629040742c8030852b900d01410407902e0325128040082c00c00c1240c0f800105210f5035108100075844842c0121400300c0e40c01d280c04140161440000495070040a120178040c1e440451349100b2044104400d501054012000700c0e00c9907580d02c18140a022240200c90300742030202d40d192004217002035040800c0308010b02c0c2030302903510750a40f00075005005190208541d200c6140c00a848030a0000f0515110404000c0c104002190300c00341c01c80e04000c0000c1c00310341c0640410001d84618011002101070304450084a2180d58 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 608086169 1250 608084919 608084929
    0x30402150a0c0501110a08010b070b0109020306120613260412081c1e0605100324081c0f120f15060c020a09060605090405091501171605060a0806 64
    0x340c02e0051813586040307018910f420840700682920546680c0c2c5218582c1c881d1810140b038024560020400360030003005010001c0035401456100f40c001c0d004400071926081e0951a02c2003d07108401c1d00046c1c24101400c0c86818001030440240c07001e0500c2500880910700c21607841944607142c1c01410b001c00c142c040141803011104c26081c01542045849000084c5070001c00b0b5200c159448241c0440180300c290302c040c0100000c0750001030030030080b50301c0c0e1a4150003070311000c04595040714607180120b00d001c1904403140044c154090003000200081e07942c0310f444800c0c25100f80b0502c10b503a03131708411495209800c00407071011803d0100742c0d00b08002589018004600065400c070b08614004545554406440c0840030f00072a00544025501c11002048814034001d080004004015181e0030307040a800050b00164076404681e043e080ca10400d0059510a81100007058228080c50130003810402c00f032180408011300c1c0c0d145052402000507040c2c416401102c081c001c44400090b11503035a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 608087419 1250 608086169 608086187
    0x1021b0d1a101d0109020a0c0516091a0d1209180e01180c061d0a0306020721020a0201030e1903180605120c07020d0501090f020411030402150a 63
    0x445041c00d221528011003104501d44102c88508540ca20200c00081e5000307500140c0c018220a0900801c0c50b0f400c0c90a208041d520805021003070004075000b1200240c0c040216840718600b010203420036074240365150007503030300000341c402401e40b1203040100d0541c1d40e9035094010351b0b03121030040c00184500c2e07425651481540e1102d02c1c0700459030042c045140981d04403035905d41400b0020000008400c410340e10000446c40040c0a012816205010140c00b540458219a03007106440903600181c0340040c1005215801c01c0360071a40124070b40702009801c1700c0010706214181c00c04599454541c400a680b05408000030781015100c00603000e03140014003212100c2c004440c03241800002c01d0901a0003c0b040c000e2858800c1208500050101e2040c0141d50141d6100d0604500c10340341d2a80304000c6800c030420a0303900038a400744480008400344546c1a400b07102c1c0031a82c0b24080786004000407215140b0105032040c42c10000c00005950705408104407107100c0c50b00c95152041e44400b2501000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 608088669 1250 608087419 608087423
    0xd080a02070e0f090d0815060c030d0605030613060c050d0c020d021c050412050c100c060605061c0c03060f08010518070515090112112701021b0d 64
    0x100015055040590215440054549400303248859407030303800311030382c1c500002c580044154100e0002401c566115184054006200050340e0030140781c0400014003a0340502400005940b00240707084400c0e00c035014400092004801601c440c0c0380180301c0060036101da4200410140e0307a10314860480b40110291071010701044001c018105041102a6550240e88135170381c0075202d4002188a10307040307211030b46140141075035041e09041c6810000054600d50f14000c4829005216403149291688680e4200303800d450b5a500c504201da90070680708031109500000d004110400c003004d0b20030315240300f800d024480b0700740004014207441411001002c07140c00c0b6080301190034a00050840054001500031030f25001d1003184541e084045c160380302124030a264100c1c0280d0f0040f0002800680a001d08100c103051180000761046001c1d01250030001000c65928004118500c0b1140558200c15907a034040440412101180001030740d5000b00003036131141c04c01504001c11040c1c9601c102107003000e03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 608089919 1250 608088669 608088683
    0xa0b180c03090c040216031103041502061b270321121f0611010f15090b180a0c020106081006080d0905061b010e0d021b0a08100b0d 58
    0x20404003031110306544155194500c5114180e41c8905130720700352080b112002e64880e0700c0d90300c014a940d01034607807800030700e10b01010340420702000a1107451180a017011428941c05801c4070701d0b1038140044104c02010840042d0981070001e01310389004c0040410b4164032007000741c2c0c144021a00082d1031304099010188504104090780300340740b586075001d0191103020782e0522109070303680c1429010404150503040c0d0500c048417403c00100d8090104c1e42c0868154100100d0410300711000b071020307544454414000c6206910080150035414442c101201e441105c801c6c40d030240e45034481c648940c0140108a0113130340c485440c0a5203000358040c07002007410380155100c92503520000320007048248150390290003580042c6956902c14003082c8240c0d030004000754101014011480e5005581041803580741d942c48406a40300c01d010000440558199802406620004601500c660340c52000d2a070240c4400b40c014080034401040160b1442c9601000103a444003200028485000b44c0c070000d8102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 608091169 1250 608089919 608089921
    0x608010501140612010e0603070806070801062006010303051c0617060603070e041506050d0510060512030706050c0412080a03060e06012007081f0b0d0302060a0b18 72
    0x15401908198100c40e054803446560314081014030296125810145880060010041c82200c40c0d1450103504030001400b1551040d880c0c203441407070001d00350380b24004244110010850741d40d0158809450043c0d140d0300003c4024201c40c119503401060000030203010010658542000b403561001900d03a858440030702615a884880c2091030b103000c2d2040e800f600800340001c0341070800103030700003c41e05203210401c85a07495440300c2155201c034842552500f40c40e031000003010380e61844064522801400a422858003142c6154103d5000d03500403801894040002d08072144040b044d1012a90001d50101d6280c1d9866108942881a40c200e80051440304019809011582c00030f4046915513840400c40c1e83d03110321004542c0141224100c1c00512210300c2d0b00c002c02c0482840300c032110aa03070129100d881d10303509044e0070081c05542890003c90001d4441c1c5065040c1d0107440d05000007603402c0f43c010031f0162402074668034000c08200b80551940150011500c484480c1081010041c1c101035607 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 608092419 1250 608091169 608091179
    0x60f0603010e0d030917040303020703030315030b0411040e0609070e040c210302070e06090604090609050102300907291308010b01080c0a0f020114040f1209030c0b1c06 74
    0x81805105c140e85812070400c60301d211044450407601030b6074240d001054900d10f1a54224003234244880310111075510381800000080081902501842c461000654180c2c0c800e8284000c0311801d0448400c65800701041c400c0030031012a07044e0654000205150050740c86091000407040c040d0f22185185940004c00b508031000070b0030250318107110b90300340d90040d5920200240b903510709030784c01c0343e100709110701084491501c4c1d4420342549214200124220b50b0320303181e5500b2a0002030a10000d10040e81c961139111000d03c103114640244124089580c0c10518015a61440349001c0c501803000f607460800344030720842e00003100f01401a816140e40340c5000c12502d078041c00d58440c01d01c5c00e42c01c01a07041071543c002c000c00d510a03601030030361a0030301c0da507198226141048400c445065550344d01c0040600d4010707404040c481c0d80502e210700c249d508a480e201400440c400540810005900350510010300c158a9004c200c07080c43c0d100986070411001003400c4d000e00b0350f00d0300450516000c0005030f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 608093525 1106 608092419 608092421
    0x601061b060b090403360521010515121b0d14160f0510020a03080c09090a0207020114030906010509040809091503010f06050f150708030108010b21060f0603010e0d03 73
    0x1031018001c602c414211a000c1e52f070f100e480102141c200d480d40c28203440c00c0000c022010014100743d601700071026000d010110405200344104540c140c140985c1d040b807140e0098224040e142c2030000030016a244500f940701d00300c04641c40b00b10015031490309a03900b100e0007420f50050524111143d84c200c54460000349060502c00041c445e981a5485d404d000c02e00c01d00180318011f90300c5001d0700001d00140d10381400820450301c20420840c0e0350300c0116401e4110768066034405010340704e51903c050700d40035900d500d0780c1044140e410442115041c500b031040d00c0400790004c2105d814901e06210644015019090300001100211050380c10401800c01c3d5683c440150242050742c0c0c0d58601c90103a100b079000f141d03a60b440c0c40402e42c42e860400040b803035081120300301c41504003c1c10b8401d80c5800000b48001d01a064002c0000d5960301c0a40050001e00d102d8019108030b003160b00d1000c2c3c = true := by decide +kernel

theorem cover : BRFrame.Cov 607913669 608093525 := by
  have h0 := BRFrame.cov_init 607913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 607913669 ≤ n) (h2 : n < 608093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
