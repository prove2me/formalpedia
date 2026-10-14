-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2087
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:37:34.23054+00:00
-- url     : https://prove2.me/submissions/8a057764-4b1f-44cf-89b2-2d6ceeabb978

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 375179856 ≤ n < 375359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 375181106 1250 375179856 375179867
    0x6101d01080c010e010c1704030c06090b0306040c0e090f090d0305040b070807141204030801050418030503070201020912010902030606060a0c11180403090503070510120b0d051b090a0c 81
    0x1080d400d1034004c181c0d030f5606004851140e240341019044140716121200200341d864020821288600340d151a80b980c3c402c41601c0700c0d1181d208407072100745c0400c001100c0385001d40c4a12926652400c1030200b011004004c01c90011003101c480344641d9402d0706008000c5c4080105410780e01483c41d050200d85815a00c0010f503001c060052010300420030041000c2a00403004507403012506a0403540314141501d1401c101d180695064020425032400405c0c1814140101c4200070141e40681c0d10103e0190740403070b02c03a840100408110755003402030080c15030741c0340000141d06e04410000300c0c0c18022401050300b485c0c0e014010910a060800040d100960000030308101c03980c100d50b410300300702d00030000328030b00c08030007a05220780c003150324200800c01d034001404c5001d03188160100ca01a41c4c03101d0500103400e958101542c007051a840304100344018580201045480150511a18403883c0c2e079058544448440210722681d1040c1408616081c0103201b95404603198070144103d5040c084054071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 375182356 1250 375181106 375181123
    0x203010b03030c10021e03091b0103050919110310020c1002040e1303030b0622080c220b0d080a0f03020412150b10020a03020f01050705090603100806101d0108 70
    0xd600418243e0302c11b025644403a08800115460542d245011007801c0c0c1c40300418000c0d981031030344001c039042e042d521910030b142c440c41c15500200b20000701a0b009170510031200c44219016048084034110544050049580144a4013070140e225020030b100316041c40803602c1c40c0d81203144140401c1040c07000940320f6070340191414020658008036418214050880e0380000ca03000742000420106140e81c0c504000d495900300c120b6203800c903450701802c0707440f1400c0300499684842d034812010300500ea02c4616100e50b10005c540058403502c44808030311400c0442d44140c2d40e43e640400c4441e01070781c20a500500c9006039280852a01d42028404000e00d00076034006010a51801c603802440d1502e0742c804072030158002e00000d4441c5651200a586240800c000c6005000f102000e24600c501402004d010307640300d449560403c81480c0c00e010140d0801001c40881180f4070f04002030320602800418028000112001c4280e802d201d418100c50760090000007410000d50010041117401248204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 375183606 1250 375182356 375182383
    0xa1e15051903060801060b0c1c021c020c090901020c070f060c060c031503080406021203042d060606050307030b100207050108060d0c0914160804171b01090203010b03030c 75
    0x488075100c0c0030450040034160010000c40d0710301306003ca00c00034601d000e821050a0380b02140c1550b0107911560480a4070705c0d4120005d40d0000300c0e1030b07024410300b0041504000c203500c100d64184403010000361000f402560b072911306940c001010406208107206650292010000f0312000a180480080a11040040213441c0e10760310b40c0d04580d420702c60b82100d03200041c0c0031211101c03181c6034203101390faa03032252140744094030440012055200c0311006403841980c218100c1121000c00d00e080300183c9504424107086017180e8080c031000108184a10303400341c8566680c00e40c0b685042d0001500303c0710324098003880742940c0300d0091545540000c0c1c0700d0a8034400e2030002d00a4940c200859028180340c640100b01200111020801d1a400d5004241c441c215400116064442070000c000c0c06a1054010000130224000940400d40222840004410112600d440d0a1112604050504132880c0405076a51110f20310000d61400f4081c3e0841c84400320090752521566030341c3e0540e0340034000b45a2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 375184856 1250 375183606 375183637
    0x1030605010c08160602362b050106031a060a0f030203061501030f0f0212060d120e0f0603040f0203060f09030d0e030706020c0717060c16110a1e1505 66
    0x4804006446d016904000741c21188030400c14002403403000000130b07840018200080300410716042d460000c6140c048544c8100c0c0005440c00400c1442e9000700d40ea00050740c043d900e80070004000341c000f820306480b480c0c07640440030207401d021081110401442d072100401018040e410304c007580c0c000c510a5040302d90181d0b014400f850000060700030341480320350450400d14003140c03070002d0315540c2c004001c150050360a185803aa141400c00440240101014060540854001c16881c1c09510461801040100014510300e00c4000181c0191700845048400300d02e400511811400c0400c00c030b50b049544184004218034042d5440da6403400f0313140b07081e55981e440f000905013074101030003103c0019070011815955041c4444071203545200511030350701181c0b4030319011400c035003011505500400b4500b0100d4a450038002c442c0003040f038140010750711240045188080e503540d03580408002c0035951045000c0201001036106094000c1c0d0042c210001101409400c00350720504483d800c20b050040c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 375186106 1250 375184856 375184897
    0x60603060f0d12090e0a11070b13290a09020303090114131e09110a03020a180303080612010203040c06110709020a120c1701230301060b030601030605010c08 69
    0x282240c2d960100c043c0c80b240f21000102d41d4558442150815a0003840c8030024503100c0a8001c0215042102c55285100d010305c03285001a40c080c0081e03400c820300c0321a86821300417988540150044a40008032014104603025801c0d141c0d4220044e030103c00d6840c2044015510707000701c1e8683c46882012030400400032044d12030192503406945440b89880000130100c0e49a103030420001d04104020146481201c2c0000f031041c000c1d01548217050045c0301c0342400c040c0c00341000d5011750054104601448250140800c50180065003007000754000ea8860907141803500030b005030700104145010269004108000c0404c03402c200102c1107402d03601d080201c141e0b519031410301704541c82e000190380e1400080d000300781541c822804d607090060b80e901008000c052200942e225072072100c0c15a903490700c5d000100300e0b00148480c20885400c1c1c0108016004448000007421500d2507041074421010220900006590610071840a0403007800d24a9001860341c0355482c003802089245454140d11540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 375187356 1250 375186106 375186109
    0x7090501090e06090a02160b0a0b010905090c070803220f0606050f0a030b0c28140304030f030c02010f090624030201171003020409030804210e040b06040e0708150603060603060f 78
    0x15001c44448c0c00420440081c1050b6130700c0006040003076555400161808004262482e00c501418051180581d1541c58003685e0359032480350350001060202c42d00c501881c80c27401202404114046c051007419868608000f074500801219401e400160142c008924110001d866148518086da0381140c0c00c0c56172940c600a141c022407003260403011031a540c0e02d080c2841180724a22603031410400da21004242e0034030366000a240d001c1103a001c1c0009000340d00400c0c0a900a91001040403c54400440c40d000c02c40c11070016200b181c0e204641ca11794a0305031800003000650b000700e80c04180c00450070114607680000302a1042c5c20380c06105400e0303403000325507400c12282c0c51100855025006110400759410082c05500c03007100c00390b0340c840d1580b1007070310182d41500101140b814942c844180782205001804024070b1120703040c681242d8200130104d02c0345040e005207072052003075607510030380c5141240c1c1204000020002e40c50140e030cc00d000f804111799451080c1ca60060b030940750f02a501c5101c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 375188606 1250 375187356 375187387
    0x203040c0504060807080d030b09220b16090801330e01030b0105040515030d1b05010203161206031208091509010e010e070b040312051207090501090e06090a02 70
    0x500c07041e485854164000f1308410045140000c0f1002ca02c20b480100d0180c080950690382100c40ca264051030007c0080d0303150380e00c060001a8101c14100750381a03031465558044044005550300740d07401d082c951106440d01d038090034050250114400910450801d06000141c0810300d47d180340c49d803120a0b4001c401042d4441c4054010400c10594104a580d00d0500c0701c203000080c025240a03600700400544206a170503410340540e40003600418071981d448004035a040c0f003540c61440d220850111800104800b40041c60080c020802083c00b07007001d07000082c101c500d00c01146142182001410800302d000f1603640d14a240050800181658072010902d00f0940303540200c4418110140601800c002e0560090b81001c2c41d0000030000700b1007485a0b01c0c7d9501c010f1180440783d0800700000c0c4006445201403100483e214200541000051103211210b00f030211407036000240e88440802c299a400a012401000c0d04030201820342090400f0910403140140315040458001601403001b5047c0c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 375189856 1250 375188606 375188609
    0x305070c05070b07020913020906090a020706060806100812030c0d1103090706110a0510020702040b1e030105010f060f0c020f040207030504090e060702030304030810030c090f050a020310090203040c 87
    0x103019142255201c0c1000f60082c1c0225405078001c500b500000341034030400c0d88402036480d13001406042d0a540d0368080004201c4000c1560071866020b0040b0400140c6600034030b00900301080290445180c9030484410b030708a15032081c0c90329071110f81076030410030b02502142c1e048004911440c0d92852000c07003441c098403610510302040c860010402c054040c012450302c0a940040d41c5a00b5003444049060342e41b204a0342c0064026000f0300b44801e09880140d001f041c40510241c401b00d122000b4800040102440b4203000082d003000d1022003c5602e028031519024192600344550f25a09121000300881050b215130014070200c50200d0040d543c80c14a043c82c00d8000603c103640e90040da18008000b0340007849075181d01c90a001c0007124112000c9100b91041855500943c00c43c0d0700c0d62003c4490300c0c0081d00001d10a06408004808500180c00c03040c084c0c02d00c40c1c2e000c2440100b00701d24500b110b0001f0111084948140144050301040c2c081103800c8032501880580c817034a403800d10700480c0c10380307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 375191106 1250 375189856 375189863
    0x51216051209090f250f0f020309012f030726130e04060906061205190203030a05031f09050906091c050a03020d0516020f03070213090f0210090503010608120a0305070c 74
    0x3801d60400c1701580c0b0403003550b040d1080340d03104015904000c45c160717074034000c1da10b01d90b0201700301d9a00340820b003518801d07540030741c1c0420303143d40340c1001000e004e6425a0300441c015202ca08081c0d4100c1d0483d81100302150a071004134106070b00d891040b08a4500b41c08031070143ca07050b100b0043c0490244004c42d0001c0d96080d81001e400c00400d503548410038250301d41d03500100c1e213501465881a26a03486407285110031034010300518903100043d18104e4881d0b200500155003203d8451500400141c148000e00180c01c290000040ba41084900a490721400a00c10101540070140300c441007500803500f030041c0d100500f42a6141c2c00d40000a901030700070018004800b40c038200801c5402200b000ca80645c0e94203d4003a20b04250200d550541c4030f125254010390803010f14820a0407a40c002e62107150058001c20180701d81040300da00040006010035032060003e00010014041d624080c460800204000802840c403100501c1c045421806000c0000040c1680d4a000900303090250b411720700c90320390 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 375192356 1250 375191106 375191161
    0x50a02150708060109050303131401091203030218100f030f090203151602030a02032d070c090506010e130c20030403060b0907020a020409051216051209090f 69
    0x140704100400a400844145001a5440344002400d08003c804c94001e040c000c0651020103041024015071896502a8603041100804c0c0c0010300d0b200e50821081c1e400c1c826030300035903203107002c1c00030f01000350020742c110344950720700341e600e81c681030700501c10301c403c07403107504020642c585110407100082c061420043c2d00f5026040c00c00c5801c40c284940b0720b2040051291036024080d600100b02e0352401424240c4016a00070041c801c031048143c0041c884450031100491507400e1385060a4203140c01682d811205008081014040d10407540543e50384402e0030f103895043d59041303800007079080e1445100d03400200e6451040e82c54680c031507401c0030003c01350812400015004a00c0d42c0d5601e620a1005940040c070300300c2c1039821031070400549409111168020001c0030000e40800c0010001034008482c644900400703084280005c001802d598401c0c1040c80d184110700781482418207001c2c0d055600c9015042142003420b641d054482600002d1401b400000d80d5120400c40203c5c1800101c420090030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 375193606 1250 375192356 375192361
    0x4020904110c10050403090b1c060603230606040e090705040e0d02060108011a010807020f10020403020a050904020d0f062904232202130c02062401050a0215 69
    0x81c41d04018007070164590101c1c0c0c03903140922a45800c80b031040d1401000911070300c0e02000000d81c40780c0600f0940b9001040307089188805010740044070704c16440803022903140c40750800741001090300f8046040c10900351404034941040050303402c2c4140d000b05064a64004040703550190200400c2c009040e0141040109000203140103680e0894142c5c18001442144004108981d041c003602c00c50f0341d50030100509060341e9200645070b0290050083e0111711a0303d6601c02505810000c010a400403290010ba07104d0440c014080c10b00c40d2604614002c2c0c180405200041c1c49001451905d1074000031040320b85d0703a1320302c6c0c4180035140b01a00001420109100540850710f05000d003119500210b40c10450030700c0004901d0100380b0544014844040c00c0000a01040b4074161101741d0850588603d1080740b90590005200e0a00000080c552a03030b601c03404d00881c2d8041184540201d04001c031402940120065406003120110b0f000341003000100e03030fa00d8664000c006480601909000318413051 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 375194856 1250 375193606 375193631
    0x3030905041808121008030c06040f06090605160f050c1207030c1523092d060c0406030501050102030309070501051804050f0a060b0c0703060902030f0a05070810110306040b04020904 80
    0x132042a40c0010805101030f20001d807142d0000200c0303003540300d00c1c00a004190307141d03107442500503c0d00700140d408030348403401c41c00004d24610419104600040e01300020a1901c0401811000346602c880c0a2080c10005c00418080c002410000c94021503600342c1d0b6802d261400310748038030132103500910642c0300485c40400a40147c000741d4200e409901000c0b2800403a00d00642d2100040d2003140d40381c2c001b80a94115501c59041c0201c110358000340000030080440d0031580b51880850700044a1000406c0a100c3d144d0f040c0a018010304091004500703500707090003020f0721031030144100da0500a0000381b583d50156102c1c600100f090000384100300c1480e0018a052074520101d42e04d001007490103401080b00407018080c0e607074034001c404c010a802c60565071031400901c441141603900d4420b4490003005403004000b40c41030030f4854409010321a00c1c000030b20303180403d4150250812420f02c00c10201c0241410b003525400481164041148800100482c00a12440410707540040c2000840d8405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 375196106 1250 375194856 375194887
    0xe060f190803040801110405011d270f10030201050d051e04060c1103032a0c030a0504080d08010509041104062c06040204050904080a03111204050c010903030905041808 74
    0x444d00a078000740484d421031945007201c0c1c403443c080d850200d00845511038120050070b5004100c0c040c0500b9080c0794911040725001c001c8400c3c1d2020030a50342c20f03c10018405104840035400c4001c0c040e0111049003540d0000c2c1a9015040c8250b8002d030b0784100052109e00980c220072403101e030711030361008541000e00b001c030b0152a4210a5502103502d4001003030041070004200c0384181c401d01012881d40240c03040b0b900c202080380301c1c1e0150304d200034071224888031000e10003842d1560440d190b45644624006229003885407480e082000d10510900400c001d0700c824064541c070030361100c108c0c1d580c0607007400045d00510003500004207091390720107800c40300000030848034001800420004d4081d03860004010591081d40100d03034000c40c101c0c002c5000160000c0192600d40040d040c0801d080c1c8040700d00118a811613000900107078501005d1206016042c008040a1300c0d003803030008a081d095407805060500148a500c1c01580d80d030300041c51962150312240002d542c040300240e07a8030401042280c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 375197356 1250 375196106 375196109
    0x31d0406030c031a150f060705011113060c0312230109021b0102071101050f07170406031d0703030e13050a0203090610120201050f070204020d06031106040e060f19080304 75
    0x500e00d0101010241d10002915203c1c0f04241c000b005d101442084003e03c0140d21000c15000e801035001d0000100040703084c011502c1c040d4a60301c00c2034039482094840307041121160700c000b0900c080740c490b21020a81c0035095000e00d00d491800412001c601c0c2d0441d10010210100e003003040302104c000401d501c3c040303400070018102d410205003440e6074094480c81c00c07031160040080400783d07000302083c129402170f0082c20116800f020f91504021103600da1b822001c410f4450881e0708200000c0c140141901880707903649221074403111391803502c080c1d0700e15580d61109002c05018083c2d0100030030782c207503601c1c010102c003502005010302c284d09148100c40b02030340042c0c807406150b000ba0700000c1d2514041139000c6e0100c80130048481c441c5034040e001501c155112035402000d04001300b0800016807240e00080400900100c800204140385007084007144003a2640184070302d804000400000402c040c1e03940d0081c4045407442082903c2000054904100d80002841502c0c1c2c0140090240b80c040007510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 375198606 1250 375197356 375197363
    0x9051518150d022d010f051b1507091d0f1b1c0228081506090a03050604030314130809030102090409140606150f0d060e010801022502010804031d0406030c03 69
    0x228220084c001134660580064443c800194144540450b52400b003801c0110011010141c41124002d80700444083c0304c2103840da804a40c180324104520040442c000704583d081300b03038003002c034103000c02c0403800724a015000032601070860703080108940b4480103c13880c5400c0400414510404268018081e401409058020003042145882d0805070303030080000380c1e134281e500c000299840d1400321151003500142c00d07030809428466040152a101110000345018200900e4507107454a80241640c54002c5da4580c2c4142400a201080c02c00070700c03a060081d40107280c2c0d84c8500300140170074028041c0366486540607007404081000c1c014144144c98107000350303805031800d80d500e40d81403103042004020200075030035042150781c90040300302c2e01501c10024003200101780740e680c0c0c1d91175040301d41d000e810100250b580040c10b010480e0f0480c0009910120150050b80c44501036000604200350041000e020b201800c48064550340360103418128a450081080090325202d04140138803080c0c500089 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 375199856 1250 375198606 375198679
    0x2090102072c15030303040807050c090f0a1505100e300d030509030403020f0f09040602220e0a09080706021204150e0a021009090609051518150d02 65
    0xea140450343d03500650404014008624544499842c01410750040a00362258003840c80080c030207950304948036014080f8100254a5420156644401c0f90303100b24482d40380c00441c038001c02c03041d00d503900c0e500e44e80005802e040d401e1110140c08160845e00034402d284440c642d00355550b100c0c001c424260401c01d0020b80c21a20032508070102541103070360564278501143e00500040005182c41c415401e00d9005c00f600601d50fa2034004082000e00c103040e03a049601d83d17004141080542c1c0b8000e4402c0e078001440041e00c5502c0d192010303520340000085c00110b078040c2c80d80304000621000304201d8025581c800b4013103550b60040004481d45444c103442c200c0d0100740c001e0041041c0d481900a24400d000410b01038103802c0f041b982005030000ca048a03110078400d0101000814550b030384103d00041101160102d92483c0c4004840c0403a003095154074465076001e0100340c0c90580c0d2030020b41e4045000040c1c016101c00c9807002940b00082500b0003076103e8080ca02144086040c41402c050311420000007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 375201106 1250 375199856 375199861
    0x90f060c020304290913090611040e1f0b0d050109050a0204140108190606030e06060a0b0a11160b18060f121035070609030602090102072c 61
    0x22620b81c812031080b1840c01050264106044111441c0b072030034105400c5141d07242180341008501e100400314004041c15a8034a20b48050008074041c0580c80c07020884000d10340f0f81414040a955075001c0c061040640c400c656010b504e040e81720240024099001c08140c1304e10f501c84a41d005018240200c2d000c050800c001f00d070142400f1b0003560190703550560440c00c809203410045030740c00340003446a80c0c21b200c020305822549100e4805e10010703040c0d40e03401003081d05811100c54905000585994090710305d07104100224036a03802030741d00d80001032814039a01030310a207401d442c001c0701079030700154000107241c00646a02c002000303092070650041d081e407145042c035081103550301461603817407910b0504010200000c418401c40950140b126000b50401c16221000d5202c040070a181070100f661440c00340800b22a034004210303c00c07800344401413035900e060140c002d080003000d100040031943c0119811905a0003804640c1c0030b044103103440c041040b000d101c9541102e10f920b043c1d00092526001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 375202356 1250 375201106 375201131
    0x60b031213030309120201050f090a24090803031003030f05041805011e0f0b0715050a2a09150201020c10151a040e060a03050a03030203070806010e0f061c090f06 71
    0x595881700e405071100d80c1004400b200104095008207841944199044004103149258100708103440b100140414400001c1040180245890f50044800c0781c0c001c2c800c01080c00c0602801905513649860705440080d140c2ca825282801650001c18856008800c488480360403540214100c800c1b1460107042148240c1c0c00008042c43c80c02808210000448140100c14110300285181441907000c5101200303100b540c40102c69040e00c044441a071507000082d00e40072010361403841c0d071044507060704403411217410190080405100c1c02e411000700070300e00c84109000303605551580744400203444c03410402c0001003009106030008842d808940070004501340500502414064a000400e0f034a042c0c200300700c1020a0600420051344090200d5001c0300080043c40f490600e180300e900d0168807428160782c060440400140704604020310344620f11046c1da50001a548095410f60369036596811801c012031100001d080d112420fa0300b440d140908000c0d0305d524100d80e55008034001c10008100b1072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 375203606 1250 375202356 375202379
    0x120305030708060f0a060e060c07121a010e0a0b040b060307090501020607050f160c030c0303080609060d02030c090c0c0a05100c112e05070503240d060b031213030309 73
    0x4401508010440c170300f880340e0380c001c000581a80e08028800c0e406d100d001a4101d141c00c202d5044406031b00300b007000140800c14002c40e0030b400b241182407034200d04e6043c41e0a000d1107840c0100251200ca484822030f12203038490398031038003c3c64005010030380e49103807051001d0000300a0f0b21402c0d005105000010355044e01c00c000b5a05004d8081295518220f103952132140b068109880170741d032022100e40d0020020700c809800000840c440e890355082c0f403911000300111400000d215134012400c40c19000b005a601103120101000104c1e0480019200c00d814a00d2034094842200d0403485140025402d10000080e0307050a01c014690a2002d540b00d89802c544903001032807a001035600200069902004103144080c02c0f086100c4600d25194a0003840b10695030140c0d002070114500005000d4018111b00040c110380c000d8000e241001021407010541d815589017020706107554954042846690074441140c544554602c1551a000d603040300e01c2072200140310442c081402d0780710000d0400c2a09 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 375204856 1250 375203606 375203629
    0x10c0f060b0120031e2b05010b1306050315030709020d05060301060e1902130605070201120e0303060f030a02090405151b07061a090108011a01210b060412030503070806 74
    0x1002860400804074074140c06034103840c3c11700c1107000307042c0300e004901d030300c403400e01d940c2c1c00890076000c00030310108219401210010713000b803142e109040003c00c03a00c440200c0c50100702c03010340c0f07071881d540c0e42e943c4a540141124107504c01d926000324900003514909a401920300c42d5449007040210b44c40d000e0806089524600c20f03003107141c0c10400026007510790a040c2c0c44601035911400340c50100c04070031070b00007601c46420180110304003040c0c040665a014080039400c51200c482042000c01c0002500d6803408004c2c00c4510800200600750130989061111000301c40c0d02a1800e0580c0c20180340054840c04400e21540c8a580c1c15400660380301500c186290000c074018141c00d2404103030741c0b9954058210b486c0b00741038030100102000107035107900300464000c000007030002a1404103400705400b0f65040c20000d50411600038240700b100c407150010030240c0008020000303900c41c68807021400c80c0c0101e901c8042050741c42c01c0844181070700305d8020340c454003081e521b28029030340c0c11040200d0390140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 375206106 1250 375204856 375204917
    0x90501021209100804140f0607120905070b0c10020d020301031719080a14040f0303060b04050906060705011503080903070e090303070305040c050604030c1410120b010c0f060b01 78
    0x940443c1103860095083c1600309003d80d000500c0a80e01018091600b006101a600268801010800d44039170062803403c1d109000c240501c00c070341c4592505a503c0c4801d00551150060000e01c0c03449058041200c00b42030414050b00307644400d03103011560000e400c24841030380c0c05280001c50016514010b01110f20100d0002602e0a052603040b60840300d5842c02803008041d40ea0303c01c0c503542005100d0074407034840c070f00c103032040c0d0040f00d11403a00400b500e005510105a0070030510007800b0990b44c12000c40c0d03000c20f00750b41c450344401003802d1542c05000214030804404400000110a00207440c0007003a41410540813218a181d40d85482000071408441c408080e40040c8086600f0501ca600b1860f04140100b80d60420f20780c030b0701d0028155a000c1e9104460181041c4810402c08514080080690404a602840031000c201000c2c080e480d05120164015075110b6040301560702400d403101a06401c00320f500380390b500c149080c800615502240c03d0124514011800215440d080340c4d0041c14038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 375207356 1250 375206106 375206119
    0x10f230a020306130504050a1124222903040308010e0411120d0306080105070c021216060e04150303050d09020a090c0201151401020304062706090501021209 69
    0x1518101a0300940015014540c001440c240c01c818015082c05400d01490217680940410b000750b00d00841210344036000c0f50b016042c80340c444007206543c81d05031000c40700c21810a546d2440c080c42043c540c142000d040080101e4508000706030b1114402c0019001402541441c0d44a50258807144250004032002000903640c0001408001e140b8001e075500f00384600f000c003041e0010940010104080203030b407802d01d40e110a10554580e03625004803801400300c40e0007000241481c400080c0f031038101c284041c1c0070b8404120140c2446004201c6142c00d402e4524983c0142522944010304040002180b180319500302010400300c2c41805a60b90201c035415280c1d18a000301c400d00103409011207400990b400b50701e00344005400ba42502650807407408079030002401441023106030a99585540002d02c00c9503080c01e0821151740c0000448042e80c0c0d081c2000d401402285904180342148002110701030f14600078005217450700070702002e0686000f6020f0791070021300000011903a010b030510f000d60080c0e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 375208606 1250 375207356 375207361
    0x4061106010e16201f0f050405031206030304170c011e0206071d03060c0408150c07150608150108060a020c1009110d0804060201050c0a0f08100512010f23 68
    0x60040c60103948203020700c0004e00c2e6041e03070051140d007015154410b01c420344042d40c80ba5403101c9241c0c8a803854600c00000300b0801810301e500c0d01d5580340a4041850f0241c03140a020400ea56002c2058034000c20400125050211445903d9a150906031040502261120204004004c1001940620689140e0052045640e030380c2c41100d03a0041d0140700d0500e6110140c100960303440038441e142c0708000c5400c6071580c81c0e2900c100c451910b0b201c08041800003139003d080c0314950b1000c4040322020760f0090168684442202c035050010031081d03001179068880c400780150310400c0c069880e812100c0c0c0c0016520380d580d032a80c1c142d003a2300c1400c0c3c1d04091608186210a1041400d601180d1114011074080c0c407030003401030210307200c803007180e43c141c0341030314003040402c04a80e09002d91980701c5162175425090004501e000707010800c1f240d64040034050703004001417500c0008100d030302c0201001008040c030500488a0907000f03003030f141c1d1030220342414182c08030140d402c1c60b00b1a007079644001110060a5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 375209856 1250 375208606 375208651
    0x1603030206161412040c0807081009080d0612060b100e0618031e0705010201020f030121081b011401050d0b070309080a090509060405160507031404061106010e 70
    0x14040b000400180080031040c400d007040028080c1400180910040a039070403e42850703082c1c1ca030307580d101c203205501c00034061140003008038200546580c4140e0215040c0d4807440c0c00c0c2103130700921080942861070810002070000340c080d1000040c5000d000200030008011042c40701c0c1d65424103010002c5080c100284c01d5a040c400e000704200450b01080c0043c1071242c8000032300700080c910310140303040b01aa0340240b080109010107802001c090000310714060541401a941340414810041c8a84599a500d040744c1803140702592070a5000d0042603030703003002441e5540356a291300a072500b5986840c482100f456800302209060300c3e801030a5907091001903442c0300c4aa0300c000d00c0401059102e40d134580c001031440d0050850100c0380d480740c0901c20b0070300081c002e151900601480c8258141710a210311030f4440c0f48151101c0b152490103a641710002d04095a10500b40408652802c50000c7c00090789c6911041800300400060207480382e03a42d840e40c001e94210425948000b021199540c6108407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 375211106 1250 375209856 375209881
    0x10050105030105120312130309060318020f1903031e0c1106130803030705030f15010c1403040314030d202a0a2607050a0f030c0b07030e1603030206 65
    0x980c4c1c601e04c01c403441c000403d05212581502511408950206440c1800030140c00110480250206240410401c054691540050842c0f000041c0c003c208140d900d00c17250300e400c0d111800320140481c102404907a03900d401090040c12807500040740e002000c0b405002445881340c0034101d030300950394600310300300d6004004d01e680c0460310700c3c1d030550a09500091000c1c030a00166100314226292680c40e442c0c407100c1c02000c0200182480c50919400d40700782805d80c3c00c0490010315940220221072240c404150542c40c41c89103400142c240b040c484003000c412a800401401d201840010a00c255131500424445101c070480c01e0b00b4240c4014000b004401d50540348801c102c84005101043c405c1451046500701440881d040e18404a40842074155141040d803284807441c00b0b800d200d180c0034a545485403950341b100e20051006500d4504041030500c10058000b07031a42081c0007500701c0c00c125a024004060400806280740249880040000801420707401201d4140d005840c241d0341e40d2011906 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 375212356 1250 375211106 375211129
    0xf0803030c130312020d12050405061812042c010501050414030304050d030806011106160806030a02120a110f0a0308030912040807140301051015020c040507030b010810050105030105 80
    0x10540e82c040c07000003c210802414424500c1d540c0140c1540003542e00001c146040c1d00c819800124101414170000800005031158491803824121010100c01445541803191400c400c05441c1c0d804240403403910044a03c8511040050211010695521200b004010400d02c18180490000e0004000c504584030070a04250300080945c0e1515032141c0000c1c5004284020582c0015200410481c01d942c103ca1000c0d802c00c0c400c402000d240c900140703807500203840d001d21041001002c5003c11400e8408120114450341d00415021441000c12505940d444a0314800d0305d40d0600a51a0b00d00c0342821110a0000c1201070700c015452415900d844045038000b4010840612a030f5107207180c0c04103000043c1c00544200000b61010034584100741640900c1446824841e901d02418402603a1171010b0350000c0b54581000032a1103001c2140c00d9041c50400e842054105060004100c4042c1c0d02da4404000540242c86060342500e644c1400e907000f407101d0268030301081040005000324a0f20054025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 375213606 1250 375212356 375212377
    0x1110c0106080c1f030207021302031608010308160606030507080604030f050408030702040e10060b2a0c0d03050714060115020f062217040312081312051207180f0803030c 75
    0x5160541f50b501041e5121a120044000d4aa005c41403050f00c0f04041101008100580f0b03124244c6c1d4115215a601c900c500d0b400d050107d09088520010802c154200c40015600101603401e101c0c4e840d41d00c5601c0d25003c480440001d01c01d15241d2002030302600543e402d680c103050086081103240c0d0b0a100051030000c0c4401c0c518410620300c02c0d01c5802034080c00000d0120f680c1e1850322507200d003000310010400041100041140c12007071101805000410b851410381c215000c0170000600e00301518039214413100030700745104401c111020814001078180c101c0320780c500270200e040c910b180107c2e220001d1002403207542d000740001c03031020740c0000f1000c0c02d840d04000c45d030354405ca10b23550740b031500b660a8148404411000f180070002e1100403416018045110308004203980741c82d01e0110400904128028a0303400c625034142c0c2400d100d0b00c00e0b2110110300241580b06030074800c0f4080d1652800100c03640780703016070f0740021806004452a0380101c0d881000154252b8440c8028159140c000d0082c62 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 375214856 1250 375213606 375213611
    0x20415090f060602010c03020a171506030c0a0207173403030215010915030f11040504050109052a04090204020f0724060b0a0809010e01110c0106080c1f03 68
    0x200e4000240e1103000c001c490084030014802d49419070282c25948400550030034148144080300b00c06801c1415081020303c40c0607400f80c150307683d801006083c6252890250040700120401000010040040c042c40300349400316610150b54190082104090b6002442c1c913070006c03e80c0862031045e44040360384009018804640841e0240940f59241c505e41d4820b80050740000c0701e036820b40541007191409429000001d0201c8120043c1d005941c824600c0010264680261488288204140100310420780240144003a0400d410418060005010280e400e80520a115084070b440100044410001c1401d08000d400621041100405084600ba80c00039001c0280c4c211510700c0c8402000c1d0030348110356261500061000d03d40d10400000c01420007180740000600c442a00d950030303585075407454600b0350fa456030ba800283e4090023840600050031b45c01d00c0b200403114411000900021038086000f04440b48e980c012156440d04541400313074010440d495950a602070040303c0d180092400d0a02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 375216106 1250 375214856 375214859
    0x1107020d020a1806140a12031202070b0a050103060e0109030e011809020d150605040302220b100302030a39020a0506090a030e04090c090b13110a2a020415 68
    0x1d04000c58200e80c0300c843c0c50340c0d883d0024845170008030445041c021741628100710641c2484070880c04244855000744c00d03c000044540801080780c1c04868070594802c541005604002d4125400b40c1400e010480b201810140307407200901052194140e0250541c3d0707444182842400103440c0d00fa65120721115441c9680c0d07022961641340e000512500203020000102d400c08103943d8800c6c00882d800000410a04010820250341ca4085010462011850668054001e8030403000204201e1480c650000700c1c110000030102d0701907003c1e61040510590a01c00140e0007828842a46920714519055015114101890000080040c5030980d10381c0100e94000c4d4071501c45515103e41150103402c1a07000c0f18032807007016440300446968446c203030340174031a00c84507540d80b602c203245030700807104d070386680c0c241052440d0b9580b510392804c072002e01e0040029401c4100c2025040e0322409440c004070303840c0c9403102d1714450342d081440c1080c0240b65400709420680d80c200030251002c0c0e180c5a54140c40242d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 375217356 1250 375216106 375216119
    0x170c130e0a140c0c0c010503040b04080d061203020c1003090510090303020c1c0e040203160c0c0f03061a030601261c0203070b070201270206040e190506041107020d020a 74
    0xd0383d0140080c0e0764425202c4405980c207a04c3c10001501d418100706043c0705201c0090400514a17070050340c051000c9881d0101c0040590050a2544c03101c600b203000c280d40d00301819004110030503243e00640d0258030103440c0800035001c3e1183c0c2440241503600442c400480014194029484a48a0f00c0e01500e04004c0e0017400740b810015201442e000740c031050407058016008804440d00e640d050340c0560a40c0341a007448444a144400b030074080c40410040070041009400a1001a1a000c080960300613103c2c1480da00526241400400c8921142c100d050f00e8580012801d0498415001c0c0c200081c280065014000c0c02c4440741c00c5403407007a1103d0760b401c101c4190544044d401c184d802517480c3c50039410310111441d409040d4005591402c0740040f00804016000c0c02c5010404201c282c000b03a0720302c080f40542c0304940c03004810412000600441d40045a050316039000039507024030440d10713440d04000803160750850345020700104000080042c01c041c80c20305802030000307092100711543c949 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 375218606 1250 375217356 375217391
    0xd290603060316030b07020601060212032d0c090306060604030203030708072402190c020102121c020c070503070806070503060f03030912010f1d0607050c100903170c130e0a 76
    0x40084405d204580f0400c548940d04103c040d005040c80c0c401071588031840420300341d40d40700c042c010342a000010304c20085403000e40c0d001200c0b090314505004040f890a070700d03030f00360035080388050610030300401000c1503a900e808001d41e415650001c020314a010034590310807046900c02a0200c49410840d0400c10005460400c104141c44c0d4024015a40e400c585c5002d880500c5404182400e000c40580c5520160768006801c01c44040e180700526a281e01358140100318048032410784840c28000241600f40e4880800c4103012a00194101d881da240c990040584443d0100e9110002a600b80000303902071420403001d0703501d03040c0a41070300e2801c5245400b04000e0b01c104003811241d030791280008400d5160328030858041401d405501c1ca0032080c0058107689540700900b0807070404c6408180d4081c44103084c8090622021001420442c50820b0301d80a0504110b41c5001d6080b82001c000040054029400b110a5440ba103082040340320b06050001c030000501a00d01403a0399a6540c020b82c5412085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 375219856 1250 375218606 375218609
    0x1c1110050105010305060d0b070305090a0203031603020d02120d09020f0627030d05040e04030e030a030903051204061b0503040801060f03051b090a0f1b03020d290603060316 76
    0x54041550741c1410000340a0782d1020745000d00840c0028130420210b032101a1054204c44c4510b0042900d4135403220700380c54080800e84c00303941400300003000d07080300f51414080346079148070780c081c0c80e00c4403030760041680c4a1491100301c9002d8401085100601540355200024261004140044510044000c1180c6410400903001c0900600300d00303c40c1440c0446070f07601840b40c2140142910031075160010a28080d500c1030b4076055031550301090805000f082400c1c013026000e01141c80f020003a04004055904510003034585004000400d1440b0a49074211002e440094036045a1090b004840c520360b009000800d590a00003848041842c000c07e0141c2c80080a00a0350801ca060950500c68200000b503201c8000100d045200e600c04c649561010940c0f010482400061050103d084240580410b403042030390860049500980b6070381540c0580400c1018100030071100404a00e50000a644040c418207408003081030200f07586030010045511500240542c0c24215892880c0851201030707 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 375221106 1250 375219856 375219883
    0xe01080f01050c040b0403020906040b030f030307080901090209041506030512180303070203280507060c031d09060d0c05060408031e0f0f07110312041d01081c11 71
    0x304280119005007401a01c0d04440d43d0030800d85468504003540140b4072903444001d0003541d0040004100782e4440d4880780184a000c2c080c1e524071020010200e480b0303801100d40c00046219080401d0f0490b03c140b107051143c6a02a240f8481c5480e41d48030410183d0401d1200a26162250301c08400240148402c889102400b44c24503129101c02c1c0701c0114842032440031a000e94401d01c007607005640c0000b0300e00d503041d4031040061403449000c50b000351200d120801c05007007840341140004406031300242c4030b10018006d503102d005507610fa60f008904040301c1c2c0c0b40c855000c0f82a801007200340ca05a40a410009e20411a030203100f5502c80119440d5006036020b00243d400c003003148015051440c03000742000d14403805039480c00025031110121805070102200c1d4070710001c6151010800e08440e13003940020004e0440b010407001414040303455002e80254807090a0174406900610103c030b0949040e190003a025005020303807112855220042c03074010804001b0a42c180030310021080c005180d00901 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 375222356 1250 375221106 375221113
    0x206071b0f08190305070e0d0c05060c24071704110906010e191e061b021c0b0901110f090910030f0807110904020d11220e07090516080405070e0108 65
    0x40000300a0903100005900c64041c0c2090641d0b2000527101a103038000b910000c845080e101c6040d21101d901d00102c40750380c00b064440000d083e01c150204d0b88a140d01c60203840d42e80c1d809481c08035000d41503072002900e00030800c0040100002032860074134001c0f9400344040c0340800309403040c840029002c00d01c4004445440e0a5a43c040c450000800103484c0c44203110601654940d14200000300310543d42250065030030541090002107503500541151014a824900c080003e007905095405140960301d21000e58640901d101a803800d910650f176a0131038418406041482e002c0c18003451810040011041e507540020110014140c00700a42c0700750f00a07040543c030ba464500d02500d2085541d041c0500c0340000c0c03070411005031744d4903020749102e651244218821414076804606540e801003000036001804801c1c840741d0b9442c0d68040459107200038210740b5101d5503001044e00b01c0c0d27016516240840303459600003441d1402150b195400511942c02c64507040d9841d003007440b0659003a0001400d86c0c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 375223606 1250 375222356 375222361
    0x9200f0a090906140f01030f030302040b030903090a0e1501030207020406080307030507030e0117010902220618140a030b100305010c091401022a01090b13060206071b0f08190305 78
    0x11144102a00045500700313642c40340c1005c80c0c8007030b0800c00521008140420300c4031314104041c42501030350700070b01b085030801b6101d0170601200d9860380c02248030755020700d807211000a0303541410801d1034010768855442d610012400d5004402030f52103082c050381c001d601e8903000246118204020601240240d1322907848031054580104a4560001064100100260f1404070b50148481d2581102c0700008010b03922b846407015014042002542c81c1664920351500042c0c058101d42149a001c1c1c800c01e0748803149484201c600300c2c1d0740e0420f030303d0317030b005240c040c8103000080f9108100d42c0c001c2c442c0108031419a907a503945500b036480d0701e403c0c4000903030408000c0107203219000740501581c02c24005003403042c0100214500c400070314411a02403400a01c4034031681e9014410f84c0010340f42e4205600c0d950314004d65442d080038800c0c898500180704840c00941010300c00c074250011841070703059075030301d1550940310105040030145c0f060754040000c204250341740c402c00002c4804c054807a100840c280c07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 375224856 1250 375223606 375223613
    0x90b04050a0b1315092619080108030711010c0c1404050901200a090e040501020c07080703031710270f09150e0a08120609060409200f0a0909 62
    0xc007400e008003051032426101c00096032200f41144449204d400010b80411a0510564842182510505d44c2da21018070800c910914401001941003604103000101d800d104100c5180009104030086034005000d00000550001201501610145081800f5000c0b50b110380395450303000e51120141e21280d00c103a5059041034096183d001980100800840c4000c00b5402180388000c590030146900000390403000e140216602c501510f4034150980882c038140c0340c024000e512004041c000ca204000340080d011030000b99080903070340c3c0344c1d8070a6481d014a4807458005440074110611417030314580c1c0070524440b000e002d1007181440c0c441003625a1084240181180e02c0054244042410a5080340c0403c0b0401203022441c140218001201c840e01c0c2115810110913802c000e0101c0703400500300e0440d4400c09500c0e402500700301c40520720b03922041708110484001c010001c018000c1803654040b58030014803a95641c1c100079150b24a04000e1800185000074183c000c4407a180d50f410489060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 375226106 1250 375224856 375224873
    0x300303130519260d0204060c021305060612270a0c0603020406090506130801050405030705010c09150e0310020f0c1e0303060631060e041116020301090b04050a 70
    0xc0341840c041242014241c8a040003c42c03842e04103001c04103101050038880c100e0380100c401c404540c0c01d045448646032040100500070422059124984445180d90858400d1043d0f40c02804020401d0f07142202c50a0311031103011004240201c3c403030b244002c41019600c0480b035800290031a00140401070020724200900004540110f820148103101c144040ca400491042c00d45904031115a1181d40700c0c04c1034481400c80d50444000c40d4200800c2c08200f29001003c0e0064038030840c000d008100c070102d400c0f103144c1c1c02c91289000080720211480c1c030050042c940d04104d40000380546092400000640091741d115460720102008006103410703000c0e5041c0040d140001c104c181c490203c007404042c169480c0030140500703202e00e2000a0008209491070940700105580c40d0000c8491104183d000b20440340c00d1041d07501042d50f4165030307103440c5040c5c410300c2e04100300a944507041907000c0310194800b2030099002c0ba055980d039941da801040d0502c100368071880c482c0c80200802601c1d807402109 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 375227356 1250 375226106 375226123
    0xf03060c02070e01061b123209010804050a1b0602120403051c091a0a0801060302120403030e0307020307140406050102030703050d0b0612070906081003023003031305 73
    0x219008a181409003640c0b4816090441e0f440e40b41031098101800d1a0181b943d2843e000100f1b040b043d01c012981007604411a0006450740c0c0c2c2019124484010148001d21000c0e6509141c1240810185142c1d41c05a0200e54000b4011740444421100a654000ca032810f500102002e180602c00d0412840d0741c1000035100044031449014281440c6a40f101d80e6803a9200f11401c908034454580c605540c4034110507001041c3c4120180a402c2003401d41c10502c0d07004420b0003000428044c000305140c0e020f402201c00e45480344410034165529914220010004698601c00c180410004040983d4040002c0405081c12414442c0340314120300400c012500c040c3e21072410354106000c034002080c0c000301550200c0c80340321004504108505d001680500c0790345210010581c1850600c030311560f0140d102c6003510b00b0368950a9207607c613100820b4129079903110082d40110750807200c40c548010316185006035005065504008000242000c0c11034001300c9003205994003c0e4040810b1150800c40da80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 375228606 1250 375227356 375227381
    0x20f0607090b041802130b090405070801030206070b0403020705040c02010501170f03030c090415030305120a110f0904140f070e04060b0a0320040f03110303180d0317010f0306 77
    0x948081c94482d502006000fa0300c42d00c0b403182d02200c004000c0c0992a01100c0840407041a0030001c0b68485d21500c070340760003001106001d145440f0001d48800d0080c9900c0e41038980040c6090b003031412070f59400b00040e0000700200c085000e91000000c0d10344460164070601d80703454001040365070624110b16403c0803101a4002da5030b1101c010b15a144501004032600422480d901c2a40d0705501d601050141079018010011441c2c100303c00001d25500202400700400c0c000c040d40d019407141400c6200b40c640f0880c000e01541010422400c0c1141208018008070502a1011500d4142c050b2140e036500e4089880e007086070b940d0b40c00c1104031544588803030301d0001e08880410596041c04440c0000707005154680e02415a00c0f5800c0c03c114070036403003000103010341d030340310f940ea941d19030140d02e60206080c44111014203800c40c41030748510b8040283c8600f2500e07840c0c000d40040b43e010401c085c0e202011425010f05c07000c01701d5145408006001103010b0080c0c000c5254441d455458042c08441443d44102d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 375229856 1250 375228606 375228617
    0x50901020315060a0201060509040f1101090f0504020723031c15050f010c0507080f070812180d050f030405011b0f11130f0c09061704021908030a020f0607 68
    0xc510060380b03984031640007a054420381e40b50100a81c003a8010070103504590f40c04892001008100700200c81900c120900c950380781440350b4102c800550350a01d4600555022070800030044c085810a0760240c04014094958106050344407400b001903621083e4055885401c00219032548212881040040259202e4204502d4030809201d40e11007507980030304c0307100b40c120651044041e0300c01c01040c2c44c226041000d0700d080b1583d440796103640b40340c0c8203203040702800f608000054070903010902d90342201508100c0361510004000400e0505045d00e04590302424428004000c10801c120b0b055031100c0000046030360b14113000c00074050004030404084502a0b10302038800080070100c20b406030a5000d64010b801008100016210310602291900c41901c0d040300302c40702c0302c0581c200345210322440e21210842d41c0c07a400c04a440d5a0102094189100c001001c01c0050030551030300c010358610711201c0e100241d25000d009007554070200d41e40c0010380c003a18450740c490360144a9283c002ca800d0500c1d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 375231106 1250 375229856 375229861
    0x5151908041104050612030c0703020405060a050d060b010203040312080718080c040507050c0102070f020f1228020a081b060405010912050102040e160207090506010801031b031211010509010203 85
    0x50a00528542c182c050003a41c4400103d0389980340d241292025009050940303441d0781024560540d100e400e88010313031159003810042103460401205000542d40060002d80c00e9000c3d90310380704050100507005a04500c4100000408101c403d03100d00f802c00318030340d5a0146401c1880000f0300d0301a04050481808440c01400c11910000240640114506850110340c0e5510078506440700d000e0b03102c0c002405c2d40001341c0234081107444404245403034401c80345a028649007506100821480a95940d100d50001b1210410114120240c03600c5d03d8600002544500d20395000c95901c450603031100035664480d00e10f00b201ca5082e9000d034841d2020980d031050030700d032910b000205545000c0c4902210600425052000c0c05020340489018142e14200c41190b410110244108012440d014000501802c000844c058029001d814090481650351071f075540d080d40c58944120095100c507101c402000040000082d0300c1c4130034001980702c01c0d00c03042c0c0c64040c0c28008a09641d40284208180d9104004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 375232356 1250 375231106 375231113
    0x106020d090f1d060d0b0109020703110a0c05150c070608010503010f0e0304050616020402040e190b0906100c06141f0b0301090b0a0803030a0203150907170901060515190804 76
    0x41e02680407011140426480b101d010030021640e45c0302c0030f06440b51050000c680214030360000c08555101347c2c0c1d816282071207034900300d0322580b81140007806410003420410040c5021040c4200c21580307502c2161a1250130034899103409266400b00c03000c121400c00401c1030b45820700c0f48101103080d49a0a20140e01880d0899031248124052540315500200d0720f1112140301c4542580303000c0e030151046545a071500740403103444c034044039050042420060035140b03c0c03045000b51030624002504000c42615100d08224003103102c68061410000c2480043d40030a80501400800400608104181d81403500a844485000130105540100b23840d40403c552002030046904441d064240010440401400508590074a62000700b5910010061042081c85030340158000e0080907030310101c0d503001c4001d100940c401141e8200116446181e6012031898240c96240d0140944000003055070725200011000d81008403212103a03500450001c2490b2010185540782040d03d007031501940c0750a68 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 375233606 1250 375232356 375232379
    0x60b10020d020d030f06030501060e060405131104020a050904090c0e010605120a0504081c0f05060d0308040311012d061d0c070309030b07030b100e03030714070506030106020d090f 79
    0x30706204250340c40302a45d840c11610351010016507404002408000d81d10710004142500644099100b1440d050108444528030914200f02c40e0b4040400300103115000c00b000000d410503408001482400c209000c46030341c940c451b440c01c0c0c521038091402d842d401c2000702d60010005801c45000e11404004420250510030909a0322080c0e1081c042080d640e140b0f85181c903800f800b2442141000f1071403117058041c54641007101314003140d52041201e40d0300d040420651328141100500401c0800717010802113481205920b601b84007083c0080741c204900241c0a0300403101c03040c40c840b0b08403c032082007020706090040c0c46c002e0010100811140482e0b80c411682000c000d08205501100010864201409803003980001d580029480c9224075060704082c0260481d0700100d4401c1102d44030000c0f0b40ca014004100341680c1c003400541c1440b650340d43c2d101c1950045640e0017a5482802c10004165503042d006601a05007603000c3c28400c401c1030f02c045c000b55801d4008202000840344207204001004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 375234856 1250 375233606 375233623
    0x121314160e04080706061805070306210627060b0904320319030e01060303050d0f060503030712120506060708071b14030f010b1804020111030304060b10020d02 70
    0x1401039441615140b6280903548a0650020640e90030145d00040583c01f10342241e4510040902c24003195aa0404c200c0c1287c03007a010310f198002c224140c420802240035180111144a0000020074000ba1141ca060000d41107404a1605002d10310200c10400240100440e00000380c92445443c103107a5100110010400d07503002152000404010401202c14402500054007405072580c0d50f200c036401001c8002c2c0076800340086800c1850b9594004414801c0d0030499806540c0c1c41d040c85005402c0d140500101518602c40300e454040104040e9001e00003040d03c1407080f07003644850304540750b000d0001d0072203100350940c040c0b61004019060300c401044408180d800191030382d0307441907403404910000c032030441d0340b0000455036004151a00050f2070034005940c01c07030840340003e0581c401d640c261401640b005802484402c204a070400210960380c2c1c0051050515418514804070b115142d038100711015a02c0c1034030b41511080d642804090700c10f1007892480588180a00d148010f583d88010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 375236106 1250 375234856 375234869
    0xc030501081504051c0e12030a02150a14010f290a080c120702060108010510050a0308160203030a03050a0f020f09010e010e061b0d03180b070512131416 67
    0x1c0000003010098203105c40041041c420300003103c4c14403c100010452120462a0303406100744484610070780c0c800106448603400d0750b0740106a02100e04071558508000504048141c84e2920440c5030407015126a60740079207100300c052610035103010854500b04600c0003150912203d54009250f180e101901150108061410407042c180c80c0c0045800c0a840380c130a800802c0c41150301804000baa001c60300318100d800d914000c0c0603136101e25507055060b402a00c603d81d4809001d0030104005804034024001a20f0310b05451000000a030700420b0950784645020800a03603a1020003d80e100c01d807040d0f04400b030820404505003142003400d00103a01c034540c509410700030000e02100d210707886440c0385081c100d0064603054441c221440c00640703480c0722010074000c6000c2c400002a4a0340301c0e01c5001d00d4001e0050b0500000415500d5481001ca000341011003001001c0102d002442803c0e004180686510710310a11100c0f12400e0413225485500000d02c000c0e00504208000004c103000c81c0e0050f90310 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 375237356 1250 375236106 375236143
    0x50a0e01090312080702330603030c0102040b07060e0105011401031d011a09160e091b03070908060a0b0618010203090415061b0510020903100905010f0c03050108 71
    0x4050068071081c4103648000c00c002403084141c099140c0c000019401040e03240c003101c0c1d0100d481d0300c01c02c02d0158252841a008014291a20800040003140e650840c40203826a441c0c50055145542a80d2240d040b030650210001182001c0150a102c1e078030034480d1000c020801541415200c03294000c0700301c100d0381055291100442050742d10300d01c0e1411002c070302000b0801128509071030b014242c510b1081c18441e4803120001001c0501036400a0411455a510007c446804c2400c0155004001c0c0110b1500b11a401d58002d46001c841e0045000360515144c2a0205103040310941c601000102102203150510207014032645a1070300b43e0380e03001e80030300d6241d01d01031201c80104c0c618041c1c3c1c05008d900c981013810041b02c0040000598040e00d103580c3c0d90034002d103000291140180e05e800001040c40c4c1c03012802000d601d01c250701404802800509440c0c43c9a8400d01c85d40c01c0e034668072000d5403540d42d6a0203c20104846d03110b0031101c513446060500666140081054480c80c2150b20031a0203e03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 375238606 1250 375237356 375237377
    0x3080604091a0f2a04060503071b0f061d0d0e030f03040b0306040b011b02100c240e0106030f02040e0106170106050f010509061602010917010b10030c050a 68
    0x1501c02c0034003145044250031814580a0702c034032840303034055424400c0c048070014880c12524541c0003042c40c41c5248150a13141c545008011a011780c0018119030400044a0319418196070f403000b5907400900842c40000441024101402201c4e00080a0200c50f2041c20400110080116004400e014641000e00c188202c85010074100045195400600c1c000090040703000e006400207940981d4007a1420072488038060015240290a0030b1103901241d5100c0511005103041040da24090f0303040e1901c040b50382c000b552030780f0703003a041803e20382c9642149298401c021510380c07094442c0401014000c1c0005072071512051400051800003030b01454950540021071002500f094005117040c18558003500c442c41d050074000c1815000c1d0740c0c440c2d010003910190940c80b03803007030391092540102694a844801d00f061052041d00e4a0120705104a003035001403414039012001c904201400c0011843d000722000300249103408801c00d1052504d0207205404007036001d030030f80e141124542000785c2c499 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 375239856 1250 375238606 375238613
    0x50d080702031908190908030103290a0905010506010f140f040e040302031930140c280807140403120509090a051b0702010e1f0801060305040308060409 67
    0x43c4900b8407042202000d03181c802070000d50000440c0d2060513042c081e01c0b890001000403600380d0707043d0303540900075200c14070060010403a03401c2545080b100c410700c952440c0010700c52811031280100d64280000750745020100c00c2c84402e010341c2d42e11100234a05040003001d46d0b54090011030070022280900100070541c80e0000c08404105c0d0b014292140610f40c0e280307801c0c94002d6a0360b00c01c148904180d1050b05030356503914000c0340c000360305000080201044602c000503041e21544801d00026803551100e80300302c0200d081c00d0000d8010149914121795032043c41c582400c0c0195103036186c0c001c000808007001140d5501c0700865410030118500354000340550070301c0e02d015004580000e4209940e18111440c0300350008001d050203034050b180d0000f00d07500c40210000b00c5804445070040118502069404074964500402d4224414145201c3c1c405400b00420790300d44c40c9403007424031a0100d411403420180c00080341401404c95140501442ca0f282c3c1d00100035150290610303000310b8a492061040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 375241106 1250 375239856 375239863
    0x1050103050706360303120c02072d03030815090915090a0516030308060609130c0201060e0a0b010e09041a06271008030708032707030503070b1003050d080702 70
    0x4040b590591204d04a4070300103c41090812840120045807808908040b000440d0154120188440e00504800392038003401c0c0c0b0400007403c406211030045010b114403840596100340000c0c0d4082d81c1d80c0409842c211007007044030390410201d0b600c00c06000b0108000f2500015141c2442e00b00c1075004609510b070200001d280480f000c0c0d004046009100c3c40418405a03503800030f040b6802075603405032940342d103024880c40340320b080c001d143c002d038454943c0744103800b080d005010340007941c0c400080c10950340c928580903410b040c0c512480281d101e282c0000d1560f0320080854175003004441c540c00341d0030b250741c03040240414180364002c03010b5018000380c00e554506241c000c500c00000d81da000310034150175044800c2d007000c41d05150503422000d00450f409400006543c801caa1040c40a0302e59101c03000070041d0811131011030131044a801003400c0000005000301382c0150700c2040110349900e03151400b41c080d00710040c50700c0180c2903100380c2000866000914080009240c3c148940740e9240c1e070341c0c201d00307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 375242356 1250 375241106 375241157
    0x6030608032a0303040305030423060417090a091505010f170c070f0302030309120f07061104080712060c030207080d0e01090b09151e010509070219030306031401050103050706 77
    0x90070f0001104100c18181c10100442c0b04900c54445403908200454a150300e07085000d03050000da178040350000c0c00080c9a01c0e52a0340011182c4105400c006802c0005280e12200d40c01c602c1c40240c07140c641c20b507241e2050603008013500003401d0603e0401100040144040c2c004031f0404c0450442d0004900c80302500401ca40007960051810301001c456420301a40d031340e00985038062103109481804040603000b1041d170b0484070301c42400b580342c0745a0740c852201400c8001c101c051202020000011044400c00548005020342c007a115820701d417905242084030b141815440c02d1600401c09100000ca0040441d00070a038009400260700010041a5004200521004152504480a01c0004c1074000b80c031904046841441c10744e40d558100d6440444560751004490410b100e100501281c9840609d01e031744200c10303104541340740f548a220901d400d8007051069010940e078441c2401801440d803010480c1040040080c050f551550383c07040e90341c40c2544100e608004003885134591030402800300c0003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 375243606 1250 375242356 375242437
    0x607080c0111040305190305090103022206091d0105030a02060c01090b0405010b0a05010e060304030e0102030d29030c0d06022d090415030f030e0604091401050a0603060803 76
    0x10840380108a402c5080c1c0c403a000503920740c455800d01c1c0c500720f84103511007070507958959146070078001040010340c080d4115441c04842888030b01c13280c1c038516005582c130030300400c91655220b540a140002c1d0f04030762468090344945660403400140600d8600184034020140d0586040d0354650000c2c0e40240100300c01003004010300096001e01c0180081500006da0300441200c0a04c0c5080e5a80d00640711a140c0f074032465003080061000030301083c01201a07403901c010600541c5e14003408071080c2011210780100100c52038101031581c0540c5040c0b030381d0104800b54123500500e000d550b0240050388401140740c009220310f07000100081f0303402d03c15410201c0304c04c0e90344191008000c03480540140790054822180101d103000c19103c0d00011003402442100e8000751800440d40103510100d61b19084220300030f030490720401000900c01450b200d8100301c0b07034141c40641050b5041408101c06000680c1c0039100305030410a080c007403044003004031880010210400c00a03024a000e0300e800340030201c240300703 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 375244856 1250 375243606 375243611
    0x1080403030b03030705010b0a0807031a0a06030b1602071a070b090322180b18040201030212010326130605090301060902270d0f02010f020109021e0415060c020607080c01 75
    0x2c170401005401500076202c0c1103581101207503c50740705641d6152144070240046183c0c500041030081e50654542e0000003400c008103c00d91641c9444000c5082504c4e0030811041c170325001000103038103000e480040e05001300314020300c079414000000b0a02440e0b20152121055001103034035040f08100329055182400140c98074803101d03103c80c4905000c60300c00d110a0586003c16552921172038856002d000750024105155002051944030fa003d2000300200d050581c20031159001c03403401c84032640214803a0b901151148440289490050402c09a03154088824010b1025a01c1d005445005942c41403a05c1500d0788414000a4094042540210340d150300c0003844a1040401d44803006005103510700140c44c15404106100b61004480d501400b000d8900b01020019071040d2103100c2100c43d20700c000b048841003078001070900101c0d60b81e880000c0b010603080303644d28201401032500d5410342426400f40103141c880c018000b440c01485c024030a03d80003401e14200b24460050310140c1c00d240c0004c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 375246106 1250 375244856 375244867
    0x702062107031508030307090b0d060e0f0402010f0e130c05090a290406020c09190509030d2703080403020703050709021b010527030f0c010f0e0d0c0201080403030b0303 74
    0x580140f40594900302c4282e65004081042c660004c01c6a008801c0303644c4d00841e80f890500050b03920b0300035000101e841ea459003000214050054002c5002d41000d40c01c110890609200251139244e190500800344011014003405565940b00590700a120f51000400c05d03040c071400c1290369226007a003069010f6145840490b00c5000810318200c03003d039200400d0311201020452041a0003588110401648000108001401c1180d44c06801c40004c4192208154102901c01d0507948200e518030700c05c1e440820b404c032241d0004d0185441900b050350082ca40c06034100f440520740300100d6809006d128841c0c000c101054401c0254000843d00102511111b603100daa803070010358480009002c0410795400300b03090100b01803040c01d0003120030401c1c00004e010302400b19800040e420007440e0f140d0000340050501800908020000f10507144000228a0105402c21044412002c7e501d0a80d90003510818245900710f180c2041c4207409003880c00031a41d49182c11405020765582a83e0140004101c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 375247356 1250 375246106 375246121
    0x1020d0e240d050603151b1806190e011407111903030f0f082a1e1b0703050d03020c19030809060a05190b0303040509010303090306110301050607020621 67
    0xf5405404110241c43c00104030504e11910303080203440c2c0c0700410180069210082c054900201382c980c01c103a0440c0c041103020b400148640c2c2104090800617100c50b54400c00440c2d0000e0700c4107150800342030070040000e075402c0c1291203000c0c000000380b0700990811031500c0c0340e131a0078502c01e88107400602c01454544a1a0080c0822440345021001c25444490814014001c0c04910300c00c0304005141c00500c80c0d228044000391542091f1141c20032002c010b0420b01c0b800000b4010200c4c5c031401c241680d903102500070040c0c048442100071140e500500400c1c40051404134021002150502c4c0140c1c564009003541030800340c51051300d084015584c5008020150490345031841a5181416601e840c3e071084500c9090303403c00c80350149920440849003541a2095024460005014048a042548940200e40045001e80064000c02c800c00b40810030032995001d285250a9038940190640d454807000c191a40111200284500b078003250010395168021038404c583c0d111000f15069a003030510 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 375248606 1250 375247356 375247361
    0xc0b130807050f0f01080421090501020f01090f080a0e0603040c0501030c17010b0c011b0915030207020d03030e010f0c0f110105090c060c0f0708150601020d0e240d 72
    0x108103001802420000941c0d40307403e0b41503011650000c1c1c0198010314401c0011030b04103900400c21070702c04d25444400d00740d08120848014020b9265200c8100850a0600180c58400c803810b14981e00d0307042c01e02800016844900445065500681c819241e2103000815910a41d0b0740703050741e070854000b0080001307006941c401102150400e1302e0070010300e0600c030b0042781d40b40f042c01c580c00119944480100240660038005102c401250400040ca214110304481407404003400c1c407000207000c1d040140203d0406000c0050031981605046103031103420742c00705030402c1c0c2d0024090141aa201c0e04034880d12000e4000205d10340300380004001c00b645840d0054000c04417074102100107983c03207240710f00035001407140f140134881140003013024000d84010001e06a00c1862040620301504125910000c0104000c00103014500040c241000761443d01021701103000380b401e4110344c8400c1d80d510256400c10b0b00c2054110342034548481c18030469541404004c954a08084084d600049480784c241c43c40c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 375249856 1250 375248606 375248609
    0x5030a03021905030412080a1d071e080c090406140703091401020a080402090705190c052a0d06180c03060b09011809030c1a070e0301050702030409090c0b13 69
    0x315034011001c01c01ca81100c440c001220300074000c03505803c00f10000c9020b410307c990f00184628003c1001d050090210509403d591610059540000001e20490260098040702c07031090803203042e509458500301550718100b03a40514010617441001c5801e11090382c008034072001203100d503419035081405005004003006d0b402511103442c2d00203010b003294018000c03078205214958a401143c0c07115002c02c010101d0141c071640621200f0808108000008201d0300c00b040140d48a040248610b03040260814510b80340b01c95155151070b00c50782d0401d80070100181200420340310940d44400c145000801480d190381d80c5014044c044002e401007102e01e41c90401500d204090070301a03440d55006101c1600409e0041c059490030b48440d02c3e60a610f00e078851090107002e8a0403001125503a140c001603100f00c54024071441c0d80c41c4d420001010340052142c5800f00d001e400070003039894a020029142d00031805030b290301d152141c4103a0144088101c1c0e20000d44400d003e80ca0b55490144058031019016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 375251106 1250 375249856 375249877
    0xc030a0501061d060d0e06070c0b09010501050117090a06020d02180301090c0501320705010510051c050705040c050c07080d0c150216080c0f0a0f1e05030a0302 70
    0x104400410b041d4407542014480021140141081c00700c080100041070704020108280269121414a0000c03020801140900059103489071980050f003045020000020310840290303041070010807813030768810700c502c039082c031344c007031060920744841d50120b081440e40364010f08614000b14403e00380601542c02400da110220000400d0f0f9060113080c1401c0e100c50307010141000b021180104159401811040c83c56000401e62071519503600c40144440c801e8807a0842c003003540881c40d0750420009105680c0c1040b242c1d40c0c104c074481d14100014142c00300691840035043d80f400000e608000c0104090800b80000601c02e1140c100a244000c00365003001003411028030079481c1c00960700c8008600340041d40031680e00c1010850b4980c272400188103016031000702d495801c2001d04228142c0741e10455070b203403041c0c0703a840d6030300da0340d86900e0328106925402e141c60750084a450380000d008100510002e55201c40c1403858020102c0980d8604040803202820744d0100082d106c40043c0d259000b001c1c168178 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 375252356 1250 375251106 375251111
    0x3120a0617010e0607031806020307082d06190e0f0604050f090a060c350a140a05040201180806090d0e010509040e070902070b010f0905070203180a05090c030a 70
    0x800c030320120b080c1d4150f106200880d0300041d0100305c449201e900882d014900306a2146085540c0b42d40d003c0c2260b10403580000003911010501054052549c440c030502c00a8510042c83c5200e0304131200e0520602a01e201e100761913000d0304905001080200c14010310b04140c11281d64030f4100101d10302c0010850325244194036050000310480c80c3c9650303035401501010000c2c83c0c8a0f490f0b685500043c00c420b030404013840b00280194054484aa50a0380b848070f02800e5080d9540310702151001641c405801d82006608113240749030014141c0010503031200d440b090204150b01c90740010780b1003503100000405081c119150215184400083c0d050003240301c00b040302c0c4000c45064085540820700030015001a000304000007480c0b801d60000815038030300c0801c0d02e841036940d042c44070880c0c1c082c04003110707501c0d0b003c00100a001e04c100540d0004000c210414840b03464040b80007501c1c2e108840c08030f254800c01000b03002483d2182c1d0780c1040685000740c400c15241c14890b07641d1800750012640100540e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 375253606 1250 375252356 375252389
    0x102100f0608010e0a112b05160605070614011206050619030803090706090e0f090f01020409090506010506030c030105090a0f1103011403070f0b18061303051e0604020f0303120a06 79
    0x10501a40c100c004072150084109840300c1048211f010315180040e11580f01c6e2224048201e861140c2e034000422244d01c40a90302d115a01c1d001d41030b200c04004000d02240031000410a28640c442103e030450b9010301c4c0041c1e2569481c0000b542c2155140140146100000000c400c1144002c011405a811070307044542c030a982e18422101000103008140c0c1c45c40300c0c2c4c800704206504944c0e826401541000c1506d0042010580c42422a000341c1c0c0120f4025480e070000000388041440300300d0161a040d46c0c0c0c1032440c5806116115680f0040c403e09000700e07082000260740b48029440070300a010301c0001800803000e0f00100b045036420a0040da42800ca03c0c180c0c40480c4d207000683c40044528419000c003041345000030354251500251201d64907040d90142c4440643c1d5a8002841381400500000d00395a0450a00c0d500e480100f0907060b22481c44403103114a04200002c800d644903504680104250a119000c6411402208140076aa01007501170006010183e0811403c1c0c4001001000c88417 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 375254856 1250 375253606 375253609
    0x3091a040803040b0c09030a060b06190e0a06080108120913052a03060907050901020c0303040306050a0b09240609120f01200d05130b0705030609150102100f0608010e0a11 75
    0x1b03103e44000b0070342c19130151840000203165500450f07000400240200c1c28484070340d600c00340e83c4003095600c5000800c42401c1d0000c624150004c0c3c00508007501e06040da035810601115500c00b044207502601400c00701c0c0045041c1d0b80c40b1401d8140749034014040c04503090400001c04c0038200104075408400481180d01010a44103064074401c040082c80c8030401e4940001c1542d8a502c0104540d04501408400c200e4985040000740010b612440002482d80b0f05003406504a0b2800d500c0544501989000d000a4030616010380f0590f90301e000e0a001d00400950000e496882007009264202807014280130074082c000c90244104d0190f80002c3c004112140e40e030710506280490000d664440034400b03004010119400a503105808081c0940d02803003e40340c1003038100045034203c00094002040042d241004408150014400c0441801c1892842d00203511003d500c002c882d0016030300d641c0040f2400007500460010104e40f0020010810704030040d540394446d841c400d4541080c00000d20206 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 375256106 1250 375254856 375254881
    0x160804061e0c0f14190503121308041703040e0a0e01050601080c0706050c070602030c0c070f0f0603020d15080a02042304121e170a090503090103091a040803040b 71
    0x32642c3c0a5210340c9828403941d5200a1400c3d003c4003010359200f41c101c3c000751105160b242e9403076203008a0045481d5650190041082c0310f004242c140c003e044040c0d0300c030001c0c0003070301540c0c169100000100078400841441502c0c60046900c03041c00c080c1d40b0024801000c00a40c001c1000200da01c2c028170060344c3d00d200542d22418192460307240681e0402001020801a602458100c0c00440d43d183c5032441c0f54596000383d80050300c1104000c42d0026041900e2503040007000c0040c0030203000720361036510b04107000700a44070900c5401c00385600005c0c101c0001c4060307446003100c142c0001611195588a42d8007640d00c05440508074081c600d004001814207004038801c240e03032441140e02900554640e0740d41c1000380040000a014441424004034a10171149079682d11045a40e58441700314021441c0c0e1761440b000034011002182c0b4250f442d0300802d04c003104841d0710354828200420f4041c0355140c1007081c5850050310300351410b1018107000c03c11901100440c019405131401c001180c4603035507103030705 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 375257356 1250 375256106 375256127
    0x20115060e0628081906030201050304080c0a0203100609060905010308090f18090d0f080f0610351f0e04020402040503030c0106031223160804061e 65
    0x3060744810840101c2c40c0c0840100650140351103951440000c0a40c07032842a00e000c03403000d021801250412840440e000d6080c411858007200a22815285800103011480050300141602c0400511070648400170080c00c214aa030140480f011500c0c000c1584008190381e002d051030050500b00000b405160f03c0c002c00341a0f80e00b00c210180b900d5040e10420010200303e0b14201d810610080880400c001340404152288201a0160a092400c610020084c03030b01d130900d035424400c0e0030b410b00140405002085502c00d60a030b50005001000c4541941d00b04550460101a10101c0d04c1c3c40c02c07440c19a0508510b5034860030712a038101e40b240c034658141c0d0071204a0404400341c850f039080189222800d09a0740250010700700600d400d48580c0071a042d41d11807040609103a4462204204204061900340100600d5240c46641720034680c030685104a0344102c10040b0750004105094101642898009880d0b03010711569502d5664400150451141381c0a85038850300c86c0a4040b41c0c81e004910010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 375258606 1250 375257356 375257369
    0x50a0b0d1505180c09040323120c0421050c10120501051f051c0c0302030709050906060423030a0f0c120308072105010b0702040b0a06020c0105070f021f020115 70
    0x4d076a40f0750006000004000810980c10011100d5240300c040c0d40c2c0044040c03903086100e502d01c0d40c50741e8a92290160050280005c0b81c504800c10040001d81417078503280303010101030340f0001030000f59810001d1034030080c1c821880e44018610401c6204507001a0111400030880e1010320040ea80d42d01003000040254001114041c004411140040e200b84001d02d6804490001c0510940e00c09080780101c555a03400840800e90000510008a800c04800001080c04494412803880d0030740104400340180d1058400003070303000c1401c65606042c500241800035000e0200c8082224074140703c1d400c85101d03141501c901c15203400115a43e015a0507500d07005405494601c65074884d22401c80700d00000f10020050980310300c40780c080056403801610b00a01112005680b20b142c0d13070041004032019180b0881c4a080d102d002040440c1d0045030314031241c002420090b45076001800d082c0054168054000d621904080300414568541162480241040d03802002060b6000080c05200744840c092107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 375259856 1250 375258606 375258613
    0xa050301020406020d180b160b06041e020c01090204050f041e0506070e0303130f0f060e0904111807080403030c080609041b09150914070c06050a0b0d150518 69
    0x290305070003002c1048145441814009665a40e0b1007c41d4182e00204848802055090384900612081ea80c080350810800c6400b082100e60b4140509035510120b8204851f040d008130304a10b02240079800308041da500035105000d28500703c0c0321681c4907802102c040350080c0b0010240c10300d503203004030000032480e40040104150b4460316415185030341c903500705070b9251000300144c000300c410348840036008001056404000302c3c1094119251715045400050810070444005200c664524030141e0b005508982d2410700d015a1401180f40c030612240d42c024545408002d00071700650018000b845940650f40c01c00040101c0c44003290184000e07121940d102c406100801e0100e1800354801815220132280c903001c40d81c0e581c2e801810340d070003651128000c000241080003a00441e024100e2820540401514186880700029124600e0140058166651003000880300c0c4c0c101d601001c01205d004281401d62101c91802e2404030395a49a04880c07141044046800805012840c3c07a0303010085024 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 375261106 1250 375259856 375259873
    0xc04061e050906070c03020d0c0e181005061914010f140703030509011b0c11090906070807050d140720120313061e0e0643030b0a05030102040602 64
    0x800800b50042c44094505c0a0034890000c0140d0b01d820340c00c130b40a4440c200e01c0380e12600d49010808818801040c1402c080c6500c1550003601d940461300318007030604040001410b8035040c0200d4034481c3e8003910003a030b4511206020500401692000d0756a0310300341c0ea8441001d14460701120010300c6180500c10382c0c44c0502c08000064002d402160b40024013000014502482d5103506113540201105907020440700810942800740e00c0240110070042510504d846040068100b03686100c0142894100300720a404502818442e404881504c00c1c0c401c0107010b034421821344a92120000d03101000070981140b560000d08001014880035039034030001910b03407001000700e0050a603000070015504040b0390219440020210300c164000c04400300a4101c0323410780d03d500b0400301c40c4140000081030b440f4004008402c0760021160081b400344000280c59600c1110030001c000d550f0031941c500d80b12480b403105640c1540760f0710100000208541e088000d82d5610245800c0788a1400b5000058015804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 375262356 1250 375261106 375261109
    0x14010c0318030c030e0618090a0507020705010f120501030311011a0609060d06080313030b0702060f04030c060f1b0306050402070c0b07051e01090201031b080a150e0c04061e0509 78
    0xa00154240203040c00d0703a0005190300042c5060f4043c4240d401507841d447e10400359030030b01402080d03100c15080401c000c10309003070350081d54914440c82601d0403c1921400b0240f0248a11010651044a05810700c03031540c6902d00a0b0110358480354440540d0301e003d140c0c000d0007142000c40c000100300030301100e2130f05103000203228165201e251241c80e01a20381c0700c0003c0058040004050502c1002c2c0041242421031408545410010707119200f10740c49201400860401c0300b000a41241d0305080c80c42188810380303000005029800940c41c051441c080350901428003011040217141525070301002126100c408203c12030041910290112103400d90510640e9646070003410120b00800440302001c0d0090b01050b40701c150500700b07402ca40d4440c142070003156054022840480700100e6400d810b681c94400c000c3c09494000d1022546c1502c841d580d07000c051803a0341d182c004e0322100e140b003101890b121914401319800742c865180060000001601c0303120352008050703403140b501c0c0e5a4130b203020400e10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 375263606 1250 375262356 375262367
    0xb06090f010b0a0903020d0606030c0b040308040b160519050f010e0c0904050c12010b180f062101180c06031104031202010209040f0e1e120d0e03030414010c031803 72
    0xf0000340101100c001c8096901c0e207008460680c07140602042007401c520340100c2107442503004000301c06040c0700500028103110141c805450001c03003141e8485c203802007070410703a8800100246c4240500043c4c0900511b0300654140c005018100310356841030340f22416400c03580d6800d24a00c8503000010001694908425001d0300540503078100d070014910980080c0b016021040780d0034050703640d04980105da051103005442c484034000040070030b030303c0c1101804042c58002000d0a02c19160f640c2030b070000c1071188404841d01c01004000b001007503100c1d41590800c0001c15000d841501d050000000c6142c442d0041c0004540d42012041c102072840da10440c0e076902508407402035540034041c440b00c43c0c8031446582a145107015010810200c810b061609003520000555802060305007034456180c0005020b507200308221400b540d41701d520101c12070041407210707100111404000184010312682e9100100303103007080ca00070400d901040c5015001c8414490a80d03100400a0a00c50042401003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 375264856 1250 375263606 375263617
    0x40b0d0b1903030305061306240c03080103020402130e1302040e0a05250905070903030e030a02090c13050d0302240708010b07060f0c21180809130c020a0b06090f010b 73
    0x9040c61f40e4941e001e905d07032019694560070800340001100c0041d500c40603603601c01810f155a9040024445016841c020a01681400042d004a400240900031819800f031084000d041c4003009825038180300380508a0402280710a0781300794180320340150503000220b101d4035000d900c0f40082925046000406480f49402c200e14020780280c8a030001d820748150103980e03c030311929031724040400d003035223409000e01030395a8400e402644400040001a10fa5054a6130006d141e0000715449801d070040314480080e03035401040d00803400c04100b0003015000221400340c04082d50101c0c020b521910384c0440508011202000015490750041120f0800784004004071030054601241003c17404003150306680120644100142180102094400141d000300c0b030744000100007401550702c054051118648441409001003600007049002ea56551064200c00124a0f20601030131246a201030b4480302d4404c002d5480e032440c003000512500c0d0040c41140705420000500d4810303401c0100700c1c15190007d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 375266106 1250 375264856 375264859
    0x70b0906040504091b0801060f0e07090e06061606050f1305070e0403030905060f0108120c030405041104080706030203090610060c11120307140c040605011b0f0602040b0d0b190303030506 82
    0x3111910981d4840170600c1c0000e0050400045401031070008180480352081d84120303201c2403020f05220381107900c900c0300c8042320b4002404c2207da4450b170000428030f1045203041c0d080d800751a4801000c01c441500503511540e1400429240ca9a401c01040941c00d42c2000c018116000880b090105000d0b03401c0c0c3c02c1d003080c002c5c9400511440707596112460f240041e68414102e0402c18010449a2710800c0080400c0c180d10a102c2d0174560104441036a90046000c0d0074420380e25408214008074601c400d07940140341040865480d10781d54030000e8020b62040d1400700c098090f40c0006000c4144009a00342141c0c440e81c0c40311a898040d441d008500305901d08807661000e140c61203603401c404100041c02c8139500854036507801e0121016498a0300110505150149092510410140e81c100303800524043d45e40d42a06a4042d039441c2207441900c144c5001030400e4404100402d00c440301038003402c40400058804c0141480c100d041118202d0f002e4101d00011170480001c0c000a07120b40c202a030420750 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 375267356 1250 375266106 375266123
    0x140312031302120109020f0103020a1407170f030114040b0a094208010e03030408030a06181d0c0a050402090102030705030a11060112030206010621140108070b090604050409 76
    0x40075800106110300f6030380640210703911190343c40c0961a04a82e090f02e540000d00f030031454800c9031400030301081255859040403403408580d0038140044401d89151030001f10390305036030300c0084000c4145076070401c1c011180c0700d52100502c80b0160030f00340f2407103030130020041c424031503d49048017000183c40510302000c40030368051409a044c01c1c005902240b000c6548103009480e005a0020f540744d50303c0c0c0c2d4440b90140c0c1c1410090703484014040122a04203800402407542d940d070b035500040c0034040541c000710300d4100d204c0c8241103041066001c40402003d131303040c136021100740d410401ea99165042c0001c0d03010080741d0041207645002c2e40208041c99060043c0c2c0c1c10f043c3d09489090443d045000ba6601080d91035050f88440c10701807002a0241070008840700060203c0e403402076030390a05000d500107014404400c0c9885105510000c021580c400702e01380402112441c0c5000034060a00c2240e1152080e01c5000c55880701c0e000640d052128045c00c140d041038a00820000134240500c4169103610 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 375268606 1250 375267356 375267391
    0xf1a0315150c150615040308040306111e0406030507030c120b0a030206160203060907061403071b05070e010501020d0203180a0b04082a0603040204111303150614031203 74
    0x11043c0304495400300f680f441e501d024a000c506100e04110700c104201c0141008200c00d100041d1402c05550642c0e4100900040d444628074250007548111220000c07803d0044405d0025110040c0052040d00e059031303402d20090303d1706d54060303003954101f19209012440f02104c41d00700314201e501161841c003000300a120304590302c1e0042600e80d409a0070310044504414007150960808115070383e00018844001d00c0c0c01e5203070000061503007500c0000284a481e0000115441c1e80c41070083e07854102c070143e52000c4c02c1c040b524000390341e189188680b580141e80361b40005240e6002054503400010190091454481d010441c0e100549200031000c1e0301c01c0983c0404521038050f01c010700003402e5000010031034840c0b04074a5490513036440801ea40c4407040104200616219013080e00e4100b5419200460250f00400d03c2c403145018030610000062924000002072040d4400b1800001c980c190b001c01040fa103a182d60041d540901e030516405a0004800c441300b003103030800560f845161402444110b030b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 375269856 1250 375268606 375268627
    0x4020d290103060c0c080f0c010b0a0b0c0105090106060215100e0412030b0906010507120210020d0603020906030610271811010c1e02031203010f1a031515 68
    0x40d03034031100c0444114065001441048200e10680000d145a824110350456451303603014400e00c0750095152012001003845206d1500035080160a8800241034aa00a80318014116183c120340701000b41c0d0341c00c0c00045007402c0818803801040d9091940540010300c09603010410f1058082d2403502ca91441c20070006075024404102802144a0f010303411420403800c8000742550000304100e0b100d5003200d42808407607a0090112400c40360700c031608070b4414803500416400d1682081242e440c46000084918a038002c5500c8401941d00c203c0e8060000c0e00c80b10281a075409040f40c65070045008614184031105070f415107034494650403c000012840090b2400d000c0e01c0c03200c4c4540c5010345081a6410030400c1c0003084101c0b1071000e20f0040c00342051906c0c0d2495020002c00107414500307140f4506d805544081c4403650418a20b40c04096903940c0d94070901c0b90300312051084404001144000588030700b502c0c411603002d106c10f6070034075200592110410040e1100041000d0402c0c0040000ca40c58 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 375271106 1250 375269856 375269903
    0x9060d0f060c0e01120506010905130f0c0e12010b0f0d14070305030406200d11010f051503010b030a050607030b0f13050f0610020a06020703170c1e09030604020d 71
    0x411400399a140301e84003283c0c1c0054200d6400c00152410749050100300119640d10510400403600100c8524020043d0507442000400401d00810602810700144400241d00820710660781c040a0740c4140143c0c4401b040c0701e0885402e00515940014040c1e03178820189010f840e541034083c0181c00841c00200d0707420000345014007540c0219038036080441c0c1004203540066070380d0501c1c1560f508688882c408002016190020107007030000740b201c0340b0342c0700c811164258002e080300324058000700628108080c40d0300d00000c0f40e41d1854407a600f001d0107140346040110300746010f01e42c084000c210b60f84807918150f0103804120f912942145141c0c6020420756114a907280e411f4024840014160400c0000c40701d5410004000c14025060f51812440c080da0000e0001600f0b43c0100c00180c9440851600b01ea9016034400780c55843c814580c18884184448402007860b150014102d1041e00518155aa820b000304151598550040c900043c00f40c200a12410401441803e0900f605001070600014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 375272356 1250 375271106 375271121
    0x601141504080f010f0501050906040c031806090b010506040b040312020c100302030402100908031804150315050615090103200d091a040819030f021606150509060d0f06 74
    0x10703da00c04075118407011001c1c070403411144500c041c1803101e90304182c0802c410380000791280f4080e50391381040d40e40c290300c00e5200030803100382034046002c48001ca003008000740241704410340381c0400b400c000183c3c40c80e01c00c04850448030b030741c8205070a192650321000c1c0c261400c00c03526425402500034503882d40d500c0184e0b19944501a440050326400c150050010752000c2d403c2c124140320f08200705102002e400804d640c131504044403588a144914070204001d000c1841140720344894984e07000c070800002400484c202011200100300310f80da503800b004400020441041c250500412140581d94420703041122560320008000f50328144a40c8040d01c00d51022400070401995030110004110603210446c5204510313100400c0e0b07508080d12609020f01c500d202d143c041409020103a010b01d0b0007900704924000d0026000c646650790303000b80d808141d160407403c58401d450020a60b5040782c0e00c140346025100f01410040186d51000244903103040d030307104255400950b040c0c906000130818001d004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 375273606 1250 375272356 375272369
    0x90204020f0c1b06180f0d210801030812040807140d0917060f061203032401020f070e070507050109060b012a03080a1d06041e050601141504 62
    0x780d0750000e02442c142025507500161164003485800282691399800a41d09004180e15145c0039000c035800000b003c0e007098010352070b081000f641000041c815130400a00c44140001c01030315070528024400c48241d9000d0000902d120018424080503030811904642d120b846a00303064500341c81381d240c0c04448080c809680c445c40d8000904e4503001588418070380c0082103982c0c01c030200994549403aa40f03440d001420103000300400741c0010341907600c0e03085000c42102058252540c0307017816010240c1e001982c0c00481c402c0083c03412080742c5540700041a203120800c560140c811a4140340d02e20900030740240041d42040000d00c91388012135170a2180e000031503c83cbc0070000c0c2010640d030014042100c03018107405c01c0a480c00307803041500ca41030014056107a042c85c0066250303440005807070044c450071480001d0741c4151a1100002d075000142c65004500078444c032805510060080701c1c02041d01341005007183c00074001003080c200c182600c18000100100801c80d00502d0045048080c1c01c0780e404070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 375274856 1250 375273606 375273637
    0x5010c3c050c0a1a090f03071701150b030402012129040f0b0306010918081602150c0723062d0313021c020301230903040807060c030309020402 63
    0x1084a03151145503030f0020410511010021880c00c0025902030145415071801800320007951011964140180303c0070708005181c11410b4846481ca250091085150302049040564800311300f41c0c01100a907071081e54169034420156000310340500301c1d44c0000b100d000e41d05844015000003e2b4040041c8814031b4078208a86200c46540c0d4104425076010303066010b544d81c600755400140b9200031501c1415a85904c1000c91351003c803003001100345034010005001140040348142c1109400802c0070078aa00884410724100504503100c50548104201e4926a50221404101c110041c0c45420200c042000e80040d440c814940070603210361203110708110480342c0c001c02d4018843d8055051561040c0200c0d800d0071450095030301d840b016041e1001030322510441d603940c182d500700900c0d090f8882d940038000703100001318504402e03031b0030135400c28848180b2107580c00112040070000650742200c0d0000c0040050b030745811415103113003119050550402d5200c404040140e10740340014500d110380440c0310b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 375276106 1250 375274856 375274873
    0x1017090a060b10020a17070807080c15070e1c0807031709030403050304030803130f03021c0503090d0513090e1b0f0102060708090114040b1005010c3c05 67
    0x200040340c1651808610406102840e1901c0f60340c0060380f00080c1d544400000800c0350784160003078441c06035000041c1128400181c0100300540302000e00300a051100c229040304001c021443d00c4084200e5030500007881c00b001001152810308010644208040640d0032180724544825100f0b500c8114254040f074541d000d0521098014280180d1240b284006142040e04658a4030f84a200d2480301a10001e00480440c030000d8148a40f01c2e98590b00201000e00c445541c50041d4541d68440050401e104d01c0f040c4958245002d0400c13240300d5800741000d40400f0032402015241600074404805001c0500940480c040c000c034455400040748403002040c04e80030410a042c5c140800d03092850090002c05500c0c200c90760000351854001ca030030304080f8010f944040055005014000c00e01c0c003403200e50070070312091080b004801801103910030280080c80ea240c0c0010b58158030b2401000300301c1c030320411503041540032003a031407600b8a4619203c0300300c1001803040c15a03003c189841c16281600200e15 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 375277356 1250 375276106 375276113
    0x1f0b01200105071106010e0a02090609030f0d0f0311070212011d0106050a1d0601080c0919030c050306060603010303030e01090f12081b09040b0402190c110d111017090a 74
    0x13071011048050301c011710075581082d40e1141c1d1340c0409003140c05601e40210b03030200308d96500704c1595007c60019044418001c20040c14955400000050102040000c07968001c040c1c0b081c007a5580d0816508401450314209600307101079000b491764910901d55840c0a034810340117041815995411084001003122814a130411602e80f186e5440008241310100b1880d0351200c8880b805a40000242071044107650b50302030014041c854040b0069002c4071001038440c00403501c1c00044143e90060043d411000d4690041c559070303080c29560103510110034001000041c0c425041728201200d500004594801d4680c0c07070060580107118212145040c0550252b503841d40559000e034400d494107420100406104860b8100d03200c0c201c00707180501c2e10307080e00d01840c1d2960b40407902c0541d00c6407950403030795118900061100b4062801103500381d2101c50641c4481c9002c5106100c0c5540180b0005c000c41c0075207082115109840c100074003800f031a240804800300040500c9845885034a001e005411014503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 375278606 1250 375277356 375277367
    0x14070207080c09061e09010b040f0b0717070f0501020f12150a1403010e030d05061002030c0709021b060f0a2406050c100204030c0f06021f0b0120010507 67
    0x401250300c0e9403080d40100207607503c40010940000003520000c80c01e07041c10200b10762150740311505640149809000045400c1c84000038401c0300c50003070b030ba03014241c0c9400151782e152241100180c8050b41c980084040e0940c1e280c01015541d1160130004004841c0e03650315070036078010700351742d031040d21011400c41102c54445128a5000410307040c408614a4800000740b6500e441e0f0085040c00e6001e00750000080d102540800d0b03a100c05401100e4a4a10311003401020f0802244c10a00803c060302d081e8009074000410780c1c0c0c80794000006880c0c01c81c10170900c040250804540e40880038a0001440c2d00804144600d6002d4a1031000c591058a8600c510000f0381d000701c18103120220500c980c0c0c4035002e0102e480b600a0700c50320701c0c1c41c2d85d4030302c440d00c2c41c0e0b454043e545103011078a904c0003034000308015000c1d20283c100c90b000c02c107241141d42e590788166181c40c2510001c00102404000341e450006150b03104a40c4420141442c9200310180303460001f1a6610718521029690340b0800c0c41013840e08030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 375279856 1250 375278606 375278609
    0x18050f0703090c2309040c0501020f03040303020d050d02120703051005030c0901090c090503120d0f020408031b101509110c100b031c081506040b0f0f0d14070207 71
    0x10700342480042016036071000000500e10903503920341c40c00c410070180c10035505040b00c41c034403000302410614141030914504045d2184681340c09881001c120100880000c019641180d406401501c00510554001d540c2540803d010a0510340d081207003111a41c00110f040f4040d4071140d4000400703140808103c80300a589400481c441e0f8045800c0400c0d40d514501c00c2c42c1503c804800200d0150505041500c60581a820030307903060141050344050002090041c01c01985120740a200080041140070224071070350185c141150030411200840000c14801030881c1d581c550b048900b022040950a8219040c1d0f94150039019914442001004040d000e0060307003010180c185d61400e004154172503900c0802010400c904ca031100e01212456030248003044425880d400007040d0301110309001402854101d4080d65a09000c0740700c05441e05240066805550380b50040c03a00d4072464144003075590300710040680e41c2040030420502120403034064150003011910030800b080c141000d000c1d01344041c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 375281106 1250 375279856 375279871
    0xa080102042106020d020c0a501c03061406040515070213020306180c031f08070909051b130207020301230a0e060f010b0901020718050f 60
    0x140401d00c040e0605002c0b2403410030442200c140a035003039140c5900a40241945862114808660398102c004c002c03aa0440c014442c0e44600704001000d5a410928985400008030207822036400169401c210800d03841c1600c403e40020180042c0750402518011080e0403544070740c400c6404070024a81c05004007805000202c82e80c034a41d0f9514400709216009038441c040c030441c400c04c0c0030585a10010220360300c0a40240500c80b4948103051a01c002e90320640d0900c4c084d5441d5820780d0284a242550940195a01860309165440da0b01107640c40200302d002c030554140d18414001081c0b4030030082e0000130508804d0203d00d4500904010f0304282880415803001c942803501640c42c2c0e520a61591a141490440181c4a0a0a0012038018141030811210015000c2c0e580c42c8000880d0401d54032801110b0400c1c400c003010b90666907103c0c4425038420380c800480c0001030254911500c050032240d501881200c880c241d50348003010b0200f4981100ca0342e541e03500d401384640d46003503840c00d0b94000c2c507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 375282356 1250 375281106 375281111
    0x910091101020d0c080a0e150a050304030801090506030c0103020a0905030a1a0c0f03040f030c080714070602070308070206031b04030b0a0c03020406020c040908090a0e090d0e1008040f0b01060206060a0801 90
    0x52a454105961240a008030104441f4405142d00c60f91401c11841100075078071029a02c8520101002d80f00d50700651701600400d002200003d1a41e043d4040c00e8490320000d809001c05c04203000c01074000e50030031003442d8240211710b40041202d8800300800c060b06c6008000070700420500b050b60001110014040150b00c4d401004204404403500d8200c076005503020100c40c030100300f1800e00301c410701c00310350009020080001c0e580d814002d003204c03d52801d140350340907036032000c1c0d4500d0142ea80d40e0b001d10000b0711111080c01804054a01500503551098070600390801d81040007401403941d5100b9002106d54100d14030501c0340340d54882c4111710700c04055040031485e00d81070080c040d43d19070385404043e1055484040150400429000781d07030389200c026080340c028586450304500c9002c002c44810010f07218401282c513881c1e106000c404881040503044c42e18403000554105c03202e0300014010b5480e426810104000540800f1403c5e000b4130b080e034040c24081c1400310400070410900c3c0d120500d260b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 375283606 1250 375282356 375282377
    0x6120c01091716150306081c030b03011b020f0d1d041e0e010605090a060501141315120e070305060c090a08010908030717041a0910091101020d 63
    0x260081d1000060302c0705907091904640c10304001c10714201d19010400c6060b0714603a4005482046004104070f60031141e181480b22a0315007003001d60b01c0d0b40c00c02e903440d20300e8422003040340c5881c002e0b8411f00781e4000140c0081085c0c0006192500340074103441a01c0010781c0a04000c0f05400c009000020401d04240b4041a4003032000c0d04003049100c00a403c0c500c1a991002c80a00395820111540b1107500952405e1001d01c09224041d802080c3e1f5201d51802440e02c5130000d01c07800380300e00c5580c050714416100c03030078440c021100c24000303900410684c40d00c0e0941c030180810400400310383c0c0c0180c101281d60315802130901c03800b8002580d1103003000500d103500000d4103000044001c150503a01c085200d10540d116107075000000c03140192907004101a503c8e04400c8030512403040d00851050019480f00355000041801e200721140c02110041c04102c1648070b20040c0d0000520215005959102204c1c01843e01a0700d04080b620050012142c98045c0ca2a200d0175580500100556450078117000d15000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 375284856 1250 375283606 375283609
    0x3110705090a0c170103050c0109060908030f0a0203040e01090b040f0e0a060f0b0a1509060c0f1113020c06070e0d0507050904020a0b03040303060816050303370806120c 74
    0x100c0003074040c2c4040c07922407000c41c070018803416207a401d41c00760200368001540c1d0303400c02e0703501c40140c0540140003484c0c036038001c03400301d020f402c400c411142c500000354030f05038088103010116041103040c1c4085010400000038400c0700300f05143c0c0a00145d0800065040304170003040100d4a884659068407400d150344070180000104d010050319422903c08542c0d0140401010014908418005e038480e03010307400407914103082c1100384040400381c0c490b4600e890300c640d01a03980d121003d20040c20010f03c4090140010180c4494410524000d4050152074500b421900280e0704803102044140d804001080300d03c0d5400004540680c0c0c095400311191070351925003a89815aa000d07041c00b5000a13000b090841d02d030041ca02c07000340800b60500d5102e00385032500070050301140c0701d0f02101c2c0c40f4a03440285c4100020803500100c034001001149000a1881c40c1016082060402503099190b0702465150383d64038062400090780a0f52400300318074280041240c000c2c120012100756602100400145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 375286106 1250 375284856 375284869
    0xb181603110d05120a1128260d0c0210060b0909090c150706110406120c030f0c02030a090b0304080418110406030507021c0509040b0604080f0a03110705 67
    0xc6082a10b44021078061810040c1c41d01c015002211074032280091203c207125480103541046800740320036a10043c1006014801d000124010440110307030000c50000003e00c00903000c2c001c15040788107011486403181c692031690f0403041c004082c450315a40001c2120b0741c10303c13022400d42c800c000304105060824044650a00032003165a000d0842c1c9000f28148150400100e4241d09005203001c40c02100703444860412313004510100e13012801c10035645808001c7c0c8060b03400369031540d682c41e00320002c100c40c00806402160341c030100345a6580da41c400e45213114018480080d83d650011030340c2d03603244d010080000045920551030480c0500a2000040040044804070380d00004035481d01c0020b042803000a2001604007080d2840c009400244a034141d000240b08a20300e07001d6800030b054281e0590702c2400d1a42042e400104100091103a0745010b9000a99055003e00700c14203003525040700c6da280204502d61842c00364086458101010f40c804102c134054061711340900203a6180801141d034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 375287356 1250 375286106 375286133
    0x60903030816021e03070203030307090f06081e0604420308160515010f0e061915200303090613030801211a09060619030803070207030b181603 63
    0x1c0d1101140124004d4801081500e031380ba90001c080c0c81c2d0701d00b049d8a000d0154402449031184850311180006181405002418070600c003141000c1c82c182010604007040712002080076900550710080903184640b4050f10000f882c1403210042020300b201e03c0300e841e020780c500c10000752a000e48038062000071a404140e8002491100401c9991651841c0240c1021950a054615013440740000940e48042c01d403004200d41e0592081c201d66183e6030b0602464091080105130410700e1030b40c0c100021603080c100350f00b8030000c030b103064203c1400860450013a014440c24108142e8404400e201040c801070005580128040304e41c20340c001e03040e07900546490b205101b14031142041c8c05018881d03c190075a912442640141c03030316560b0030180203240e45010156181400c500c01c0c507000440c83e0602c0304d055282c00e07004815402e03016103540d07140e0103681d00017040c0f1001c60141c10070010002e5154417600d070040ca801e09000030b0050f0b088154914090355203007941d1042c0b140e10300070800300385c80400302030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 375288606 1250 375287356 375287383
    0xa090c0212070c12030f0306120b13030302040b180f0d02030d030c020109081615051311060c030412050f011e1503050613031b121b0c06090303081602 66
    0x1601c5603090f00300b21800b440607a01c00025020f0064196040541c408030702040b001440e24104120307529884000800b040400c002001a00c000c00400c2c4c01c0746034450b4030006a0b210b46405894a500d03041440000c0d0004580840c1005061207041d800d4601603c04108080c4192562010001d1075000a90345031110b400750300c00d2542c0c070705070604145c0c401e40104040c2900402c14a0380c0e038000c10714000b00811030000940d5501e00250005035071107400d00440e030103181c100c006050414a252100c0c00c034103000743d0703c1340d6120f0350421034540405803d01c06800113280b002d01c41d0b5101405418024140040b10200d0a0264500a42d04100e2a4141401110680400b4001032120705c80114008001da1941000e8400c0c41407004111341080c4180c0101c51191281e075600025101407242d16410b06181c0300e00a041c0080840030018051140c12055483d070381c8100406031581e80c98581184c03008050708854005607810b80203105054205a100f90000c00301400d0244820720858002d403564003840341170 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 375289856 1250 375288606 375288643
    0xd11060a0c020c190509070507030215010828060504050102030105010207140604091e090501021b010b0a030204150e07031406010f02060712020714011b0504030b0f0a0e0d030b0a090c02 81
    0x1c50014107074a04e40009080c0143c280d000030b041c0b83d03401074a41c0e007000c0801c4005100d24020b6044056185448074101c95000008108840000c0302000340101844140c4850028424202c0041041405101c1c000c6000d4400141d40b541801c0009041860541001c824259515400480ca4641c0c10441d0102c902e030742e030b00042910503c00040c241c102c0103071401890300d040150910074480194000c20010303420880c1d10410b0406600700ba400c2e078000c103201550101c000705041015040c950820a240785040c403888240c0d0b5101c0b103812000d4681502c03480d00190740c5282c15098070030500c0380c4640015003420003800c84582000c0080d0b40380300051003002003041c81c1008205001850301a0b805203a80803d00d18502507481c03120031b00901d042a0000c116031100d603d02e889141c041d208580c00d507900001062450b82c0c3e4414140c00320701c4050584424107075142c1c0051009174003403000da55007400c242d8000c1041e902090400000307000720781088000074508996000810340010700c2d442e400300702c003031342 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 375291106 1250 375289856 375289879
    0x10092d0b09010f110a0f0932040f0e0d0e03030d0b0a0b0c06070306090522080f04030b0609060a0305100c090b0403080306011106190b0303160f03020f01020f07230d11060a0c020c 78
    0xc0301d408c50000f40400d0340190a1120b075501d0034011b03404c2400c6607c04082190aa80781212017150060741e07000165030107401c200104840d4400303070303088038082c00d0700541340600c02541d032103501e5410342c460018143e09070010024059060b034140190300080c2030a00040c052414620307891050317941ca201d14450b109000181e00405c01040d801a40d45007070841040d9a219507a81c2403110403408212140c520507002980080c40c1880c0c2510442c041e6600000180103141c41c6070100c000410304d25100c0014040e21072000100ea80681005101440c4921f1046d038a80c1000307000582215620008040150400070400c8030b100302200d001c91020b40c080202044041c20308003c40d04620981e608407100e049400c000034244034508110f426110b00c82c3c0d080f2400c9565050440b0b01703c1c00b4415010100b8901085040049115524800004d2050102e00e50000034220b4100345452815a4a4070125102800301005a18284003040c0d1007040c2c03007000d1044502c0300030025128a0300c4021103228402903000b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 375292356 1250 375291106 375291179
    0xe07141801050711040204090b0f182a0409020a030c140a05070f050703050715020703050c091e0a0b010f080408030705130810092d0b09010f110a0f09 66
    0x2d00403422800940210756842e12201c8c1900a0b11900c0300040c000c40311011808401c0c10042d0394081d001e880d9001064403612200401c801c1034081440440810040c42c20f400300d20065600100000c00c3c85c00390042e034448500c1c00240903914954503c0050000101c0c49280300d400c010212500b0b9a40741c40c04c0741d80c842c0723a40f07800c2c1d00319001204003078003601c6090340101c10040c0015211050390504448050001c0303820000300d94500050100a0031504010f003001c82c68140300004540083c02c4402202c0005c00e41810108a0b0301c04803054501346441341400110355800c803c00000c2441035143c80c4001c0d140035110301c0024070000d000c3d030b81000303800504110b0a0340e1040c2000c01905112041d103444018241c1510007910783e00380d00f5240309007404080113202005594101102003419581c42064096840750480383c07200030462007841d501c40780180d60082452040c00002840e146001307840b4109480000e0904542c114100140b01d007080007802100c410014070041c03000c1f103000315000007c4550 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 375293606 1250 375292356 375292373
    0x5060604030602040807091107150902060912010b0f0d0c0509151201020405090a0b0f011416030216080c060d09031214040b0c030106050a050705010e03040e071418010507 75
    0x500142c4000c1c80414081044400440e211003100ea0030102800300d513100105020192042d0100141780381401642171950344011b4014013190350000b03000d54105a008030116805c40000d6150200c1c136550784000300d0440c90804c4854000601c00e07121407860b10340350ba66040c900c01680c026144500341e800001240c3e000d074907010361100580940140c0650080340f0b000f50107500240600341c1b14800850005640641da84100491410b008084a101005950056891040b00b00d000c2d040002c08022001944d2071034001e18800500c0780c0d0040035401d0303ca03142c0004030b001d160840c00c4a80c00c031401c00401030ba5800d041e101001c17890702d40040c41845c1d51030300b515010014000e15a01e036050150041c420030b4004121886203000d43c100380310a981e1000c00c0680c520003401981d02080b010300015040f5440b0b08050200c282c42040001100000550501e156400c141c1c03000301460113803000c009e0f170180e0242c1c0c0d05014020706071295082c8001a41d4908440c0c100c5040c5038100000824850300303016515 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 375294856 1250 375293606 375293609
    0xc080d0207050d0305070203120a09030909060815090628060f12060b0108070f200304030f03021b100c080d110a090e1b0901140c030706180b0a05060604 67
    0x891045503203821a02e081034072100841d260b4004a031070100010300d00d6001104403003152100c07103113818160740d5480f812002840482c0c010f40410501980100e2141014401ca4001c0c000720001440607d2040070002001e10004118601030707000042400310170007032241107000768402c3c5d2201d000380700e4880038040d0003014035a00800502400380740000d40080070f4020030000030b00480c4217005404000b001541d80e030f038041d1521070001c0c1465007025201031244400c00c0c210708419464807022482a198540786070407540040e01c03102c6030b4584400402d5010070103664011088203200c902c00c000f520010741588250040f8100303210540c1003070f200700586001180c2c4150000081001012072aa00d038004542000c0700e014042040c4800200d0266240860f0901c03800302d0404051144a440d0905a801e81140d04045e0600281c20000c0401d414031001800c210004500250744072041da040c0b01d000e03514403c08550a01147c00591004a4a01c510071176000c09904000f2520f03451358008654184103a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 375296106 1250 375294856 375294877
    0x2031b0403110901080d080106110a081206040513080409020a03140f09010e07080705130209030a030c0b0c0313030807110a05160608010b0409093003061a09010c08 72
    0x1000710070000c04241d00340001205440e04505030380c903054100e40e0783c0c01c01020760011503007802c0108062403203607941c1c000c09103041040d101c107080d09a640c041d5903001049040d98404c010170412125040512481c2c0c2c0c0000c4064010300d0110705c07916004070038843e5002d114405900040d0341d03e5440e0294120b075240400c94408164203180031070980815100039950300c00c00c2d50902e2080c2c0c040e014001030314410307200503601421503d86048200951b242ca6808440c8130190280b2940c0c0742a42c042c0320103010a4020340310446107000a10306070818040040c0601ca021500340188900403215564070a00168581821039064864100640c0e48054031103120340316104002c84481000b0001c1042c102d21019121702c0001c9640f5841d041c5d42c3d0760000d010b016500003043c48200000070964000d034401e1130103030a000c2509403801442c803000a01034001000080750700e80001c00440e51611a507070003008400e441c40d400d81c176039100c156120310503005d00604102d8901014801c0c0481d01d01112020501c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 375297356 1250 375296106 375296161
    0x1602090a0f0e010203010f060c170f0406090f14040203040f02040509010b0118060f140d062303070f051215090706090807051809101d160302090403030203 68
    0x2000d050800103032416202001d0102d0400341c044140d18814000d8a0584d003192800b44101d508000c1d00300e421281d00c60050380c0b10704560017104030f0107040b840100b45980c01c0b564070b50784c1c0e141401d07006040021242c0c00340c842824003030003c00c00d10134444000c1d90108021075001d40c0e0381e100e500f4201204120b007030019602504d08801c2c0a09200154451135070711900713803541504403a48851086a440452003000c0c0440c00031001d17144118031881c2c280080e078400801190409043c0100001158090380050001c810500103801050000c8450b1103401c4008600505060742000294900c1c411a80308090040c21303010403a804801e8140030b0410030801c85c456a60031741c980444074039910001e921403032021810102d80810b000401107003041c141c9601419400060f01c45501c8041010790003811600075009003401c400000c01c16025051072246e1405400c50900011000e660400155440b00341c81c55140000410068030b40c481c0c1c1d10747c0650507040c0107849681d400c040c1c00c0110201c01820f18070b00c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 375298606 1250 375297356 375297361
    0x409060e0615091006140d0507050715180816051002070c051002030f1b100e0f160b03040206040f0b070302010516020a020907180e180c01090902160209 67
    0x1810303a106800ba0080c00c10005007107814407000b807206640a03901003048401c02c1c09802e009100d100e154002c0400047e2070603114040800c211038007614400c0008100080c44c0080c81030030408044d0001d01c0000810008603080d004600075900c10600606880020560841c2c8100d1075031003000d9540c01106075400180c00d078150f40002d502111013140c00c216002c1380480c3e01d0600310030400c072044807600110310b095403400030000c2d41e40041c071850340011042101c17a130401c00140302410138000d1018020032503180b1503090340d0a00c88160311419a60340400984043e05443d0410b0b07a0898840752105541ca44460001c240c1c5441547c0201c00110070240000510782c580f00000c2c8030660007680200304a40718180d401459900200c1c0d64001030344540d00300ea01510746001c2064009285040000712041c40030108001460154422022915548104004180d100079006400c40d141000740c40c582d49030710000380002c559030107a143d039142d0104014000c482c00000324080190014000b560700e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 375299856 1250 375298606 375298631
    0xc21070e1009020a140d15030605091b2107050a06050a080705040b0304060c030b1201060305071a041e0812040501030f05040b1527070906020d1b02040906 68
    0xa99041c1d4078254200303000e010002c0c18040034030a03145a00c0042e5689020070380c0d412101d140b00e8100d01008518a81c0e11040040003103080340c8180010f5100340340120705850400d0049040c28110072200844d940305000c0104103a40d01922041c1003071214901751081315580014614005064110301d41140c61100d01148280c0c010000d880541d0069442c0055582c603218125481c2c041c1d44501c5c9190079050021800048554101c1c010200407890b00241e0b500301000000c2c1c885084000541c0e069540d641d0a01c184031060000401409a6818040082d207284900450707600c594810f001d1240d44603008040b4032120300c035030400103282e581d0481e100f802483c5034015240e840307032141d0740c04603160140700c0100740a00e002d1548100e80188280040e503603040d1042c6451984246a070b51b07c03620a481054a11107500c8249016074114200c4d400320780750035080075080086a400c04001d640c091140780d03295546c8400c096003540f0401e0444100a0b801e0310200300540350408005004a090840c0c60800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 375301106 1250 375299856 375299879
    0xe0708060901060e0906010e040209030105040305090a0e04110d030c0f081908091c1b14121c11041710051302031507090e010303030624020c2107 64
    0x188811640400d05076680c4800784d616055110b45030340c005103100006840c41d805842440400c0c0805440945001c214000013030840b00111012004a100031502403c24140745810300007529a124120216040039103900c0780f218803d0002c580f2504003503402c0010184116144001e0f907900040304d51103803110707150000145d004001c01170b403016a5002d400850f1445a542c060181404a02800d20841008a900ca0083ca0020b0850602c5001005a8990b004030400ca02c1070b180160f18001d030f032441c00c0891500b0401c502c895000075071014003480c0004403800544082c50111100005113059801610040c14010307907001e894080c800c0000d0a94450000c00c042d00508d0807850200030340c0e5600f200144a032158100b001e50190300850343c854035000c1c042c1c182600441030f401c14100c03280da5110240328506090300300b20f0009443d0102041340101d02c1c0e8440c2000c0710031501440140c080d00380000e64494500850a01c10b4441c40002902e401700207015040301e00c130001c00c0d280f0750354031018010007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 375302356 1250 375301106 375301111
    0x40302031507081513110f0c0106090b0d200315070c0b0c0c03041e03080a02161a03040b040609020307080d020c060c12031012030f17040323040e0708 66
    0x200740da83d800190b6040c01514401083e0800030030003408216001c041c1c000802419900e2202080d00308182c444080a40c0d000c0c00c6c0203450000081441400c10841d0380560714121501c0d40940030041c484000102c4013000ca080850403084807180b0340c00828006858110055448d440d5603041105118405502c0380e034058641c1c6c00f49180c0c4645444a000c0c100481c030a4118a526541040c0014481041d806138044403040644107560850747e103e032600c01080c2e00c40480d00c40960700406101d15281900700d06007008100d482030080003408800001150b6110080c00140030211a02c002000c020096000880d815005012919410b407210700742076603415200c1c1424003510440b89020218507041c82102e00c00d4003108040e01148002030010f170110303000980600d40710004c10740007144d00c0180b02c0c19461801d000b0343d035080d007000000d00c0113000140315214207940c80c2100310030070001c6034000200440000749a812002c1c001d130256480314040c01280c001c546008040414800341a41c008070301030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 375303606 1250 375302356 375302371
    0xd020a080618060114070215040602010203160906020a030e010201020d0e010501050301060b0903030a0f09080f0c01091202030a0b0a0f0204030b04020117090c13090501021315050909040809060403020315 89
    0x70b10500391480304086586080f07908900145550840071882e00e40200540720075440541043d90014036081c10002c2c5810503040a0010b03076000c41040403030170016030380340700203229070902054050600c48025110846080042d041c089030500b0034135140d1003581241c400951400040101c441521541406070034284181d9100b0342c01c0401c003240b04003481044900300c90703000f0f0045251a00c0350b082581d03190f403001c540800f44030100d01c001440640034020072000001c5040500f9460b801d03600050000b12143e0003482460841c07044000c016240001c00703509580d0031049039261540c60303400c00d5000c5c0070300c0002800d00030f0001c2800020000c07003140b070b0b40c0254403d032581500d082482944440c501011201c25003698004009581c95003072a521140000c08802804a4010b04644640b801e90b408061b40044103507600100f0086d8018003400c2580382e07440c91034820700c2c05a8940c002252140090030117040c1841c0012407440c00da4525003103400440e4058181d500e0f40c0c00210b400312010740111440c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 375304856 1250 375303606 375303619
    0x309050d082a06060105040f090506041e06030606060e03060f220501050a0609021303060e0307210801050102011b0815100518090408040e1512030904060b090f010f050d020a0806 78
    0x34100750f004805450a030349500723009400d007903d8100744501402028004540155480540b41e0f4a00d640e18007071050106400b6001c642c452039880c0280484803240d00c080d080060b02d41c1d00008648d40420004c0d00000c07002c0c2d0400c155103a170009401d128200f6446160004005103181041217019000540310f40030b040c008001c10b5640b90610810f9106600b00c846c2c0042c1180c209000180c4507a00a6140720030340e10840e401c2886c15aa03c0361166039290b0b01000c140c280d0a080118079a122142c907025280a200030b11a0b9400c1070b0113803040c41404403401d8203101d0104006880380600105840903200c000740580403095100c01c015000e68001d065810310240c1a02f00f00100782800ca25003400390350b00c0f0b07800d5442c092426440c0089404007402d049401354001c03140075959070710860303154800b203100d00242d659849910f0801c811110503a200404601051040b01c015aa50300a4002408000c0c2020500044000c000b29014441c43c1a45820703e4804141e1003500b030362148076544a4241503558 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 375306106 1250 375304856 375304861
    0x30726011a0a0e1c060e0307030c030f02030904090c17010e061303050708280c080a1b0f0606050f03160b0c0304030b0109020901110c0d0818130504030206010608040309050d082a06 79
    0x540c1e482e032023004406004188800740100000c0e01c6110040f00303080703051050700e0030424050001801c1d107210070b10560741c2040d02c041c00c3c00340030342e0360b44080c04403001c0c000200700c9028100391321754484000405807001800d25011000074180507404845010307601c840038964401c41d0300030134104c80b44415400c0d010301c502181011011802070650b01d0002d9088208242000b01c3d040044800b141950303038040c0c0da07080070b0514000081d8101495114248146000704020b810001807140031000b0b029098883d9010140040ca03030101a205001621903180256546000301034010345540701c0d540c4002c0c01500d41500000308003400354083c000b00d0030241d07541025110524080341d034540301905500d40c0803502c40108030000b181200281258049859141240000f203c0060720700200b50080d0110280c07610100420140d0521001c0d01404150034402c0703850915031402040444280101c03805100340703410a0042c010048292402503010045d80100748800505404102104240402c040d00c0381401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 375307356 1250 375306106 375306131
    0x6060702060f2a03030f07140703030b28030605040609050d0201050f1806180106090207050c0a08060705070f0c050a080d09092708070602030726011a0a0e1c06 70
    0x43c80d00f220b4044000031030968803000080030a035800a4080c00a0041c101003002e00001c0340d002234a0368a0294400154044100c07041c0419001e480c4440b0030700144680c081840c0b4148150b20341c1c15a42c0204002407540e1b41d174501500103221102e4007034110721429020040d09507054000358490244000900388586800720707a5005104c1c074a0040700140c100500207500d20403143c044101ca00110f40000c508140e8928000041380d000160a44883c1c02c409040a4641800e6074504014004d100c0148050703c0e05410040c078a020b9084020700d92080350345220f0070310900450344005007500510600410780e46040c0c2682d0740360074024a00104000450010300c00749076106c0c10240c48100050903c3e0701e1309182c0e10314560829035008560412092012102249503803001e144580c01d55111818020001c0e004009901280f05007584c80f1401e140c01400505800c40b1024030b2040300d039811036111862200c0540e9031400610701c01e5000407900d07000382507076074140e01084411800b070501006800044003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 375308606 1250 375307356 375307417
    0x19050408040e04051c0512060a03110613090f0603020102060f0103020f011b0c0f0305070e07090302120f0d050d0b0301060f05190f29070312020306060702060f 70
    0x2540034050900601c001c110002c0c0a4144940c05803150050350702c550503032007406220a0740f481c1ea9200080c0042120743d00802105130b031a0b00b00d03200b02d912128103807459549114034803000788550302a290101c0c40c1c1185a08901d03004000e41000d82c01031042c4c403400c1480300700800b460711040e8010321410b00420505024006464162600038000710310101000300151190000013103403080c00204041c040c40490308921161000d0700401c5507410101d8a103017841da1400d1080d4110160b890240c50a00503c544c01402d480300310b036410f840421540400311200c0b0304100030002c2c1488240580240748001c66405401000c0300000c0900400000f803488081c142251414050a094034910a00520031440e0101845a465480071802d070070590b1200e00c08424042d141e0304c803444588035003103c41d84640401034840c55031140148050b0400380795031001414410048a1044c0c526800008190252580e90490b00550f8010b02025680c8110300007284040e440422403040c1c245541502880c0c0c5600d01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 375309856 1250 375308606 375308611
    0x901030b0619050319050f04170307080f040c0513061a090901090209040603021513090c05030a0b0310090f0b09011103041e02150705070b2a0312010305061905 70
    0xb00303400d00c50400600c409958070341c40544010301c08410f2200466114896024251080740d001c880003100e820203281c2030303c01175585003441c0c420036014403c21a07020760118000f5400b2440c81200b2600e80c86505001c0014046900080e0300019111690104c1160a400c00c0c0700715544911003107044105031034251054051030000740d42c80510a001003011303030744940203010344c04801000042c40300d0b5680d0019aa02d0080400c06485080200319000304004035010030340209042c600074405071038611f0000708103103c01001c0500303441e6690300b555165201009a5042510200c90421030480070b030601200241030360008480700880600015143d41c41030080000b0f01400500300760640c4c5a640c0e40d0140000b0034040070701640c0b0000c40c0140540d403200040141c10115a2103036070340d003072103003404e90900403107400c8030302e4501d4208202c1c1256603880201034155904200c401c141d1200221142d4207600c1882085102c2c03507114800841070010102e41c0b1401405050500c0340a8101411000c0a4030f004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 375311106 1250 375309856 375309877
    0x50f1219142e03030e1f020f010507050703080105060d14090f0c1e06070503092d0907091502010209090106030225020a03080325110f0a08040b0a11120901030b06 71
    0xb1500100002400b0f0500031600305001002e0040c482c904c5c400310780f01c00030b002400b200141c0c00704144e000c01c03038400e103e4640c210266140c11443c1c0b009070384002d00f00403818406c082c00b8410000340c036a980803c907031252044510000b90045281003510383c2c00c1d61584c03c0944034105004580c3d9444503450105551007451500a038104041c0040307034204042a00882020b44441c003040151080681d5402c7c2c840c4910004c91000018115031440001c4103446070b120720303a00421444045c0000150041072000860311081d0340e1142d0290f41c8101207000e4000d040c00f003034121400700000300703034240c0540151851501c8004c0380b0340e0510703070070035106980d258080001c0e410927207076802400070441c0c600080da404042e00351a44d50020351400c40d04183d030700c0c8841c400000307114044d07440110481403006c0020030300c811000300781c80c103201d4903482414400c510851281d010002900000716000307081b50405043e61005a0f50700407d818450b4005501005003280040d01e0701e41001024a40b034800d90740c85061 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 375312356 1250 375311106 375311191
    0xb040c0f05090f0c0c0f0f0109060e0c0d120e150301090e0601140105071406190608030a0e10030e030403051f050114040e1011040f06050f121914 64
    0x907542a11104c90703201e4885166940200c42c09a0a840000c102012044229500008503040e0609005080700c0b200c0d0343c9001c0341e8002e540e1000b0130b640d6426450b015660042c05104202041d08001d42d502007001801c9070b0820000754040350314600c140b01550407913007040000d000c64007404039501d8541c0e1090059940c1c0e41d10a204001b16541f095000d480c10030f1146000380f000e4900004041c0c41c1c01c00803034080d0300019054205e1050076560780200c2c4003d00d1088002c504083c80e2480c040c04001650110700e0140e0410b001c0055914400d4000c0b107003484040c8103403559076880c0e003009901c030b0a82071500c21850b500041e8000400c8030341e215850403a5007596851008101840800014024000e007400c21072103038030400d01e22803019100d0124503060204045076118603000303044121299035070000080c00340600400090300d41180445651034501440154030f0341d10003410000400e00311942500c0c651074030806c2288034070b008145038041d85103100811081a52100c0c01b0b1010180e00203820b24400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 375313606 1250 375312356 375312361
    0x7120c030912031814040c0906090504020c07032103050f0408030a020c0f060a1a030106050918030c1905010506030d0f0f0c15051609051807020a0b040c0f05090f 71
    0x18400c008080009200b80b41207001c90003c1c00904188003020742211040d05c21070040211285864072030314481c1101410440c00e02490070710301818002c0039204a070300a070740018401690f0340041c04880003a650020800c41580001a007082c100c04c00641da4001092a1078045080c0c1c07031110f00000d00c5150b100c4006482e6070b50310451600030b074029039601441d0748106640c0001c8a60184a100d1040c81c0a42c000290780c0a05103450207032040b2483c5041c0280d00d003400c1804192501c07989254082445080080c1c0c41910b000342510310301c80c04454003564003408640c001140300e00051031001c1801107000341310325201c0804258403200108002c078041801c80c40050301041c0100000502c500c10350405555400d019202c050110303100c0d0300d201b40001e95500400c6000109403c4010b1031261610303100c1800f5080a0105131483c01e40b0380d911312013250400000e681c00d40708002c0c181c5002e074040e154001d903040924100310002c1c07090043e0300000b0760083d80880c55003001745120340b1603514001300c07480da41c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 375314856 1250 375313606 375313619
    0x61802030108030a0f11011a031b03060417070f03051e19260f090f070b0a210207110406140303070609082b05150d2d0807120c0309 58
    0x2c00000070741c400d00282c80b65041140000723104800c00c80b50414419403029665000b0141450300c440d0760980d0842d0250b40b03200b500c0e20001881c0c0d034407990100016100c070020f42005003060284240040000d0190088502016031280203440e21114441a0050985103207501080d1809810300c070103425003104803880d6549100d0301c5c69000c0d541c1260302070290304034082c59103418030b50b048643ca4196031205050281405041001e8000070b41e90b04058001c103030034955482c05a100e40507a0388204104c00e21110b001515003064078249100410701107568a0452600c10521794503001d01510961a002c00010b900c13600c000c00350303011031004020f14940002940e403503008102564055a170f121050119820400f5802014a18401c1e40f641c803640c1900303118410002d4890040c8454040d89200c1c0d842a03007074981c21200401c455100f05c101105080b9640d00c01d40a03000025070b8030401c4a00020321040c031640784000c0500c203004410005240c0c001c0c14040c0c0c0c0340c8075842c0005001805010080001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 375316106 1250 375314856 375314867
    0xd0303151203030e0c030f120d0212243708011d06090a020a03110f060f0a020c0604050f01050708090406060906111209121f061802030108030a 63
    0x100380410594410594403424030001e14256800e0441c040303a0f660403480003c02c0708100706511701000b24020034001d06016080e43d1641100002c1180381e410204d0b104585e640300781c06039211400001e04c03a0101d45000004803002d804849140080c8540300c4100d2030840c03c00003241c44140c882c00e00b0071305440c0e045100e11040203041c9111801041c480c00c1020400c200207029041c1c088085030100038101604860813410028040c2a000c1983c3c42038001d54010786403060240c0440b038110010804400f80480400c06d14418500c80075400b500008840b03403481c0d0540003030144143c0715801c844082e82c40200b0700c0014884d5009084e8082d00184018a9070343c491f5001b8280e6920544515040070071003400315003615400e4001101250800c40140311060340410700707030000603505004002000d4403411070301480c45521000e9020300085407144221071020049965145400004031503950070981305100248424014100746150000f10b800441029009480c16034a41c1c40285190078031400c410f445 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 375317356 1250 375316106 375316121
    0x906070302010605100e0307122409120906021009151e020309030909071b060506030c0d05010203180d0926100e010b0328080c0d020c0301060e060d0303 67
    0x719902c0301c80c0030416440d002c89a40120315183c4540c81c0c40002e88040504121181d0001e07060002d140084c503000c100c4203685060307aa010403002841165080c4080c401800c0641e01c040d140956840411054581c8200c8030012500c0ca54262044803241013005001d40340c2007007015000a183c02e005220042407680114840c4595540c1c0043e040d004002100580e041192007040540003c5504003180c1041881554854a1803901d82030fa40050044003208148c80c1030007030280b5686600042007900c0c100181500c1c2d82c40100066028041460614041d6100302e03001180701500034409500554001808031480c00e0036201c001e20f0f01e003418030031030980000100c03c0116150103950807041041c00d10800a20b1100c451b008508691040381039401e6607902c50180d8040c0e8400f00c1c0c209110811000041407a50420046080d10340c902d0920180300d0052034009101c902800080b0080c164001901e412108010303402440010383d515030300c40320490100d41480d04000c1c5c424100d000240309a00805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 375318606 1250 375317356 375317363
    0x109030c0206030a151806050a03031d0609030109210e030618030f0c0c0103050c0903100209040e010e0a030906020a080405010e0a0816030b010b03042301020c011a090714090607 78
    0x60301400d43d51041a03a018554041c03608203010300c110b40346d4000940a210f02816058491092040c070b9a0b40080000107081c001d09a406a00a03e0301c01035900c3d101220600d14004000748030b00d0480b400e101d80d03060410544142070a0307600300034405890007803c0b845400fa600030007402081d82d40705848a540720784420a00b040780030412002c0340c414100360152851255a074024448807403140c0016040b108003070404820004140070203080750390f000440802048000364090b0f2920501000b00d006401440b800280790b5003442d042c44a40c00740080e560a070103020b0341d80c090030290756000981e00c0f551105005440300c48104070920a6501400041d07424800c060082c110241c4c1d03903034116040020350742000390f54050914080040c00900c01507280505602080b66180d410300366948a06100d50208a0080226410445103020300c01c0d4196404429400003d01100d01c6640c901e22407400c2103408903210320f000340c001c80c0c801c622510703a09680702c09034070b9820700c0c2c440c0c0c000c10802d8a400404044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 375319856 1250 375318606 375318611
    0x5060306131b1505030103050f01050103150f020904020304050d1e05030f180a0b15150909040f05070b040513150e061203130515130b070609050609060403020105090109030c0206030a 80
    0x6010b07040f420800581541582d2069102d50440c03900c5403c100b040c146600d01e9a042c1001407000c1035034666030032184a203d0300001010341b108001900640940307081d09510910110130071050200104401103407200e56540d40c04951500500410b0a17060902d40e000003a4003800041e4108150081068100340c080f07c5072a8101c5000c01500d1424100c484111688092103003031001c00e00d4031044c001d1440c030003211141c00c400a4566000c546000f24007901e441032880a0108092202c801e601b10355454200050b60021910ac803c80400b80d445480b495015030112006401c07500174510030070000c0c00d400380c140b1030b54601d0500c0030708040401412080c0c0c0100070070245110b03418100028003020380c602182540c40d6140108004002d001d881f07080704bd00c0320800070303c1d0103198100c9441c13080d0b5001da49041c0e2581396500b8464000c005885000b8118400e004c14804003105c0002c00602c141d201c0c0c0e0003400035035a828955400d1f1148040c0c003c0101e0072842c0a0801407404001440c1e0108695800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 375321106 1250 375319856 375319859
    0x110402070807030e0328081308030a110c0d080306150f0403060b0a05010201021c020f1201080a02041d0c010305150406180c0207051c0215030a020c0105060306131b 72
    0xc030740407a84880400c8021500030200000c0d582018420b000c1d0380c50005516503003801850005441201003130b08003e0105100007940c0380c5080b401d00c45100600324410490b611403188160240012891540f400410b01c19605d181030341c5d240c00340b0284003840c1d0101100d82980c07541c009100103482268a500190002405507102d0303020543c010b040154082e600101d0780c42484800e1219000481c2c1240d411a4010000341d0703070403c8180400d114095100d680165a5203201c0c0c0d43d801036011301e01c698909a03000f44000195440d000a10100e00c074000c86d000c100c01c0d007024007000130440701955910b00a40004a0310803c943c002c0d804581d1010413070500d8002d0039070820002d000c0340c8040c1c0000c0d540c04620f0b145001120301d184280084941180002c184007802c100000704144d00c035a000c006e8400b85c1a110108640307401039035148a80050300125180d0030009801c0020390070401148440c0d61901001844510740050010701030420002c0c5540194160b480d03840d504843d00703036000c41c20310110380c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 375322356 1250 375321106 375321113
    0xf0201020a1502040e0c090603040308130c03150e0d02191104090308010e0903030714091306060302090114040b0d021317010c1d032a0307080a051c0c11040207 70
    0x256048600c2e215400181d5440c101803408000100c00303000b814144030148640c1c08540c84000489030030603014201030920381e0b180050841481da803400c00400c0131542c414008204100c5640d601040090b400c001d010443c0c0c401c6005650b40307050044000180c0c440b080745c400080c3c20b85840140380c0d004180800007111030901117026110040011000517041f00f0041004160101c0c1440d00710218201541c994104110010300c42c42c5664200709101c4d0300042d40604a90b58410017105d0141e032a001448029900e010160003500310060840c046244586126003c1c90b5420840701903c2010b90218203180d522100788000f5044500c1c3e060764841c0c0d00d2008a2030746000b103801440f00d80e01c0000440c40504000340200319042e030640e09400640c100104000950700070424041810252654000b0a0008007040d1500724038910000d4050080450200e58034a020802e81d0450f4021000c8814032046000b142c030700b42c0c0c3e80c4c4070100e000404015102c80040c400780c400303d003450340c010400740c01c0405589 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 375323606 1250 375322356 375322373
    0x906040b041503180812190f09031103120c0702010e030703050706090f0617070e100c020a0e090a0602070201090e07050d0b06030114041d03130e060a03030c0f0201020a 74
    0x1040340302d074a41c081e110035001507418001c11103440c6151074410680c140d1683c4082140c012030a03400c1d5980d940d000043c091801018039000300d0b6024100a008802c1d040310300b40004e000d00320003500010010507030f10106120010842c3d610000000260b5030a96500001c41c480341c0000408070b0411101e40034a284903501000441e01660142c00a09111450198050001c0603580e00c14404003490000810405411000c00004450081c1c518452039a4070181215a927544000c03050380003502902d0b070400300394404200442244281c40d82c5034445d445140003296500200c600700181d502c17800c004e0b40084d680b03801503c4000c4c4103040c8640960349030309400b030515000311921000181c002c5000c21210f02c1600910500010964a0f6440d65041c022201800c0341c0e2844444d0086440701805480346a401040d00510449142626150f085070a103080b8605118811300d016458a03d02160701c2e80fa05010075001c07640c0c540c0341d4a075108120390b54201e120b0720080003a4103501450340350340301003031918 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 375324856 1250 375323606 375323609
    0x40509010f0f05040903121a060a050406080c03100501050c0a08030c030a0b011805190f0608061e090601030908090a18180f11060c03070803160819020906040b04 71
    0x501c0d24144a040c241d070001008101c0d44100d1245040850f0007002c01d4200102e844c020042200204860b20030500c1c0448240482d00c501c0d4001d0800601d1240702a4000e02400c00d485039030350f9900c40f03529051107811040c04142c80b170785c66a9079400c004105944c0600001d024a03003146042d9110811070b500c0345403441e04102d4843c0790f21000041004540d00745803080d001c0211090030240c41c840703600da01e005001e054901606008410071510700034080740c00c9005400034400004002c01050b142c6034004c003c42802d40e1014002c054090070508070702441040700782d40c01e0002d80f210342c0d10707a02e2f1001100074240c500b6003690011402c11000d2069110b0305480005422140c40390301c0969100080d1104840740b16414003003080440c50001e000400b01554280c240b0341062261600d005014000b404502c00c201110101d40700010343c82080000d5017024600c01d4124504030b200e51307a488a4184c0b800c400490310915080f006004d07101e05040140c5c0980000c2c10040c0c556810141c958149000580c803e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 375326106 1250 375324856 375324869
    0x120702121c140c060114180a0c030509030315011805180103051c08060d0c050d0605010e06010e09180c12010515040c050406120216122a020d020604050901 68
    0x1a03901d44609540100c481155684003088032450549042c00300741d1100010b000c0c00d1800240ca0b8103911041c0d0350340c0c0e03140e00c0b0000c0404031244203040c0300468200401707100b8608008030f400c00000441c0d82d42d000c41968460f642946c80f00119410107001100c1c00046000c2c081c041740c0c1e6150b0081266101e00c91150118501c401c40380c901c07541182402894202e41a641c0001000c03440a4403100b10350214000380c0103e000d448001c3c40c0b1040b840c200e0448901504416040040928282c0c207104103030b000107040f0351445121184030b4854000440325a0100d1007071980200c100c60215000800408204180d48807000640d03000241481c00141035580da1601205669101e01c02d010281d05035401204004101700ca08004250b410728014040d40950b00c00c0c1d0060000c00541584c09240f90380485543c001c9014a1405c04c810380e16000030304a006501c07480000b45820b0080f14a18000d60b510413007100e540c0c800d90680da000313a0030010980e00311041280c00200a010004036515009685030103040b1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 375327356 1250 375326106 375326143
    0x6070503040312052a0a020c0616060507120608072d030b24040501030b040b0a0e01060b0711011404180b12010b03060708040336030b010503070605090312070212 71
    0x154504e03101c1c179401456200b0344012800c001e09140e00340c0000f210315665074103440701d030344490300581c16451044581c600504804d0604c8200141d0b83d50010700c0a40d00309070f901c02040020b88a000d51507844180b07010f441c074020040c10b40301d02d617081d14a07800002000304e41e28864405403a42c0d030310040c501003524140f041d1810480071040c0121115100034030300106543c10061580b540d21401b4000c2d43c0030b8000341407140c0440100300d00c200d03241c000d2030659000c000240b1005560300144000380d4032014042e00c86e525044c1a100c150340c8034940a802c264011486035007007505006415404285a0341307521422903640401410079102d0341c400a5910700e40d9000015004211020700d0b003000c3d0001d02140400c2135070700030040084d0b000f41c5103080d20031410034824000c0740c1059808121410740d2a14810000e505000042040f9845940d103041e50410303001d491a456032507805031518000c1000e2564981c00815619101641b00700140403141d00080a80030701c1d580f210344050a107007081c0030f020010311703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 375328606 1250 375327356 375327391
    0x10501060e180417070f0c030c0b120117010209031e0d0206040f0312090807060c09121716020a080102030a180503190509040c020705150c0607050304031205 69
    0x5410010a1041080075030b40c2244038503894070303280d80380c45004000034200c0c4404100d1030750301c5080b4816101110b5200a601940d02c6150410320400074882c8411100804001d00201c0e43e03140c044140d540840300c40c0c020072216420000543d0100f00390f072145810b6590309002254166904101500304140003d40003a8078044548440b800d00c01c03041024015540147c00b80300001d84142400714209070940740498901640d251018007415038100050305003d00130031004140503040d408484001110b445902000c4d60b41e8a0840020740c80a00150105a003000d4882480d0b003000c0080c00d01c00700e41200d00b502200d9950014181d01c0160b0003c03d0103a60200420440c85524401c034003680c141c03812181e03a0a08a591100d60b01d00c10b08407403108413451403e0485c3c0751030141054807260b44000303009214480d90700500a5583c1901e200d024031403110041100c2c500d01e01030007241c545403903140203850540c9e00c59406580340c0d40b024000305e0401061003101c0340a00c3c01c522a40b03010705c201d0200004110f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 375329856 1250 375328606 375328619
    0x30a030905071509032a0315050f07020706050d1103040507030606050f130207240209190609030b07020705030115061805210c060301120c08070e0a18050f010501 71
    0xd003030340e008030b07a44a4402860403807542d001100300044030751001802a800c006562590b64a441d11b0000c0d18440302a01000b000700150a82008075035200b4903010005540c0c1c1ca00984003941054a025025030803015040c004148650300a000721500304101040381c6400b003151401c50341c400c9805440e903801c800c4082c4200802402441c00802088500000541403000041c4034400c1000c00c455200d54000b0b040010042030b00002a4403c0c007034400c544c3c0d1031164010450207503001e444114030804102c81e100001c54031301c01e45c01050720403d54070300101504641c0d8011241030003500604c04c3d44078800001600d13076001d014500031030500324464000d080c64820058085400c90100a007400702000e0f042c1700e60388403030940d082ca101d50120144488c150341c41c2c0c0242440e00c00380000b5080172000001080211409180381e00d101d106841e081e965642e280d81b0103071103e04a00a41d04240305060214214400035001008040c00320000c03240f0304003081d5591483c0120030011a111039440b5801007011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 375331106 1250 375329856 375329863
    0xb0904080309120f030a020702010c05010906050a0f060e0403030b0312030705070c050609030a1b180c020607020f0705010e1f030b03060a062103090b1803060a02072003010e030a030905 81
    0xc070b4098250035800d100551019132843d010050480c0c803941d5010072520700b0341e84a48107807034075190001d0003002404198103109001c0c000440b06e80c58528240b4440d00502c0340301d842000b0441d0088002c1070394546071550201d024140075290a58140b1801d40d0703400c03a116210000303501908540d102d03550350b00b03450b14044030141d480d43d02103071244900b07110145d140d440102c0d04609940c0e11100c0b03001d8403101c0c0e0150341403d0103280c0020350340600944075072401910744c0e4496070303000e60b0729000c44485644040e42203a50f80280002d40e9080d4025080401140d4001c03c0c901e944814000c045403011680084100c00e0303e4070041442c0000fa440d25103048180c2001e20003660043c0341800309020b03160400034844a0a0046103c9444440f070031018207040c58401c0c00c080c0060400c100b4680d070b0710300040c54a4504080071001c103512a000e410081101c03000c0e144200d5a017141d000c00454246c9404180d5440c80601001010390195201e0852034aa020140000c1050003d20740b0300164030241414400d14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 375332356 1250 375331106 375331123
    0x110f0d0506030d1b020907050c16080f010506151305040903030f050601050301120b09030405030f071806050a03020628021f060311150403050601090501060e0a060e10030b0904080309 80
    0x140203041324921502000e81364640442ca0301556110002d46030080100c9072803048602c00b52079400780030360300d10034903071299188070444180b01e040f00d000b401e00c1c00e0740c51b013291003d913071407030340b05001c80d1a500382c510440001e05500110904d040000f076549001040079514007030030403000242d98905181c41d5090ba803151980099080c80c5c02401c660501c44c44600f50088100081d013011261400900e00e2901081160068180a8141e842002d0402409943d41f0501c1c0507048102a2160142c01401501d116090850740d009250300801481c40d02403044075480b403500c1c030803824203480c107030301d0101c482044031083d00d4802c0d0700410600030003d440c2d0724802d00d922111300100781031800402c0461249180350a10340002c4415421070503030910a6002c41c892a80010308a00030303400002071220b0f80d40c2c02a03048640c01c0d1078482c4c0e1068040104200a001c3e030059002245905d5801d412500704400011506140c5040c009800d040c510001402c3c0a0125411111034000008003c0070a0701031010f040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 375333606 1250 375332356 375332383
    0xe10020a0203030d0209270403020607020f03040608072303150d11210a0308071e0c20060403050a021f080f0403120f0507110c0310110f0d050603 64
    0x2502411581c000b035180d21496903098a015008540c041c0940e48400003540900c400f10726991035602021090000e01c9001c41e170640150041c0c90009185a0000c1980e801c200500c101861405041140641e0901e00280181081103a60b901c07071120703820090f0600300c817501000641900e91070108606200d19006004c868010b802121803080000c0e41410402024001111200f104800c0214440507542c0d8000000e0303228032941c1c070381509041e002001c3c1c3e030040403160349010b2000308042d55010515860b03100000011074070520600442c40b6004151520514000d6428142451100103521a0030030713001510070b500400d00c0d1030114600311101c00c031190b0485840a038030030b8048101901e1460000c05550905481e00005001c15109404c4903403c5a81c20070708100c0e201200c842200180811a00240030034008880351a600000181c03040e00a58001d00503d50b9000150301c18001c0d103120a0f00b206031000500c00b40c01d81c10340303500c080c2c5441c034450341c000146890300348209454041f85070250b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 375334856 1250 375333606 375333613
    0x7050a0204110a1b05120a0c0210080127020c0709020d14090d0c030201020706050703090308070230191d06030606190207050307140108011a03010303121404030e1002 73
    0x10f0070f6003504030302d0810104641c001c01c54048140c50401d282000320700c0d14500581003001a042d0f030329a401104040e0f000d0f00a072941000d40340007103c1030751600030a0180b91805c000082c40c10040b14441c1c000220381481c0c0f03880c00f600f4800713071100300d03464155190000c10045401044a40214080d403055441c444180304000b04103003000342c0b12030740741c40401101c5000c12040008176824103001350115803015034800d40400c03961801c04401402016181d4045002503074060214042a100062080340c10b8840b6504080402c416400500ca500b0b20086035140120240214081c10400810030f402c50081521141780c01d00d18504002215040811028131840c0d040c400d118030758940c2015950000381004000310404904007050745806000d500c8690725219400001c04e40c800c13421040d41c107803d001e8031960758903600c562074580303803002e81c1040c1443c08a081c00104080b900c603aa4181c4d5406440100180101c840101601e02c1c40080710244c0204070790b050040c000e401c0409590b42440d00d00e1014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 375336106 1250 375334856 375334867
    0x2c06030111070b040602131211030109230f030f04081c0504031712040c050315060306070c031e18060806090403050c0c0409110a0e09060c0d0f0207050a020411 70
    0x10750042d000300d40d005403800b607008000400700415541201c850104004001500c2c40c0d49841402840414032030484207290011076085540c1030500842889070390105012b00f45081c603c0045480000681a088840c0b00721007110291200510080043d42c213503d0300c0550312414421824504410f8049000005064600c0e181c81aa80442582c055075170054000724604095003a540e11401103041c01c80048d81804c0a100c02c001c1c040d01e4034400c5980c1a0252101480c0301000506512000c40d03416400d900918001060706d4481d0203000b0700248a414000c0e540310f11454590182c0010f254000086410b0384550000601080d0100000705414a881c110f43e103400300129100e244064002018004042030080381800c044c0f00c11030400d80090000c00600280d81070410b00c04117041243d9015041c09000404c4030100745030518895a0450014112070f10344107082c2260398015194104010f40d1a1011450018240000c00900340540000d1802c03448500402c006c55034855052100507404020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 375337356 1250 375336106 375336131
    0x50f0301140109180902090c070803040f0516150912031209020a051507020a0b0405030a0f0206091005071b050112151a04030501050603060c0d02132c060301 69
    0x4980c1900d450a4450041e40501c2005a8803000650064044184002040303130098465174401c141c0d9500072240c0c840c1c241c98075840340c0e206101d071800242520008100150128900b0212006418425412a40359006006841408244940102540324070002c0030f103402e01d500903c904064000c4c400804100401e07550040d002e031081d00c0c1c54884140d122203540301503680d0303444140000d22001e802d20801c000b01840400c255440703c038049208002c20f810101d139500040e015142a00c1014008200104030f0381c40c3c0d0048103210401c02c07030744601c04010051444d1107d4144100e200102e44035292103a82c01d1800b51b80524903520b0310030110034401e0701049a03a82c041c40440d940c60800c0b1340065840c8000850307084140086d004080402d4840c1401420400d02d000100205c9000310001c02c0b5944a400800d62104030079079040168040602c21055818201d50041445c0e601107500c01c0e04160b42d860b100380d24141c85414507402c48d064041140d50a074106a015540310b081140200040c445020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 375338606 1250 375337356 375337387
    0x9010503040605041104060b1c02070201020c1315030f05010e1c1803081911190602090f0a06200a050316031b0c0501031113090b0a09050c070302010b0105 68
    0xc1c00604103603190b50104013400030038460008041c8000d80148005515001003503040c1c0d00c01a1203212940190081d03d0843c02c152090300c0c3c1d102d90580c05094002e03224003c21103200c1181e201008290355460a185007140519428001948140e00340d01422210303041c810b084aa20040c104164ec2210000132134403c0441d00800c01c110550030256400c100452802d41c2d180820b800042035401c000070035818a0141c000e00c243c1c50032840d665014076034600d0ac840b90315102034004002141c2c8100c02501c0c0010b0072a0081d220003200601640400305400b8006034485017030342c6c0500041045a00f020075180d001c0c20f03000c10140708050080481c500a640e9083e40e920914040d1180200844030b0380c3c04061040524101050f180400446030355440c1c1044402c5c42c0880c40b030700740420716101c3c040741d450704001c040d50314850068400c050098603007000b100150040c1c2c0c0102d0f6200744103800c045190340180c42a80d0003144400026900c03846d881c60060b007103480710b4040750b040c40406c0c01402203c3c040f51 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 375339856 1250 375338606 375338611
    0x509090a1205160c170a03050d051b030f0a0b04110301030b06010314102606132d150209030a06020c01110c0105090d050406020a0f020a030c080f06070509010503 71
    0x207001e41d1102540d445040b54203014540b00c804020356004004814000ca014001302038554442114403040a11000f890fa2003080e00c400502084040c099190040c41c10350009500142e020760700c4400300c5400d4613051407030380101c58100001039010240241c2c0e80302481040503240b02034408000d51822400320303105502051000030b106901c4200000c0d03890f40f00341c0140e041c180350030103181a14106000320480181d414011141c1c043e001d40c503819000c1c0014840900c600600401902098a410612a512210514007519034003c0f010350707401c242a04034028401190040041e00104001d440d107a0004403040c946514041d005101410455070080380e80032846a011400503603801c4031010007805407449a1049140450215100d05501410b41069100f940a5401e80f07030a070500490507a142d00a50081c800103900c5000c4800009422404094240d80014200052565281d555600d030b103903942c011031055000002e40302d03280c42017000b400b608020b9504040e814031582c00d0000f0081d0100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 375341106 1250 375339856 375339863
    0x70e1507020d0f0204090c08060606030f070503040228030303060509040203030301210209070c0209071d0103090303060807080a120c110d080d050903040518040b070305190905060106090509090a 85
    0x101d08840381007241c1042c03c03a020b103501502c28800e003040c0341081714000d00c461244450502a40c00020b0191814100b1240704029114414406445001085550b60402030040740c0001c5a003604c9000c2d40100003c001d0303880c41c0f40c076880d0a0b0740d040d4a001030540302079520480c041d141c40f10500c03005039004401d807415610324001c525480c074800c81a54603411040940a034004042d5424898000c0d8014801b00e8128001e40342440c0548a80c80122841401c3e4800c0b11001d540102e0071034a2588203410003031203d4040d28010886a0300c40c031105003089200d5100441a034001c168000800030b02210a14444105041481c1c2083c8181c48241c000e18407070803400c0c40f6101d848400d008108014096070107010160400b0071043c5031105c4283d030759505c18012944a0031880380003120900307050552520855002c0c102c06850340305c503078041d000b40c00060901a500562441034011a070303164401c451205028100800c12035240100241c10761009401403401f45203c00208a196040000d42d005080e51 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 375342356 1250 375341106 375341119
    0x30f01061a090d0804031101111906150512160b0f0306061c050f10080f030d0203070e03030d020409051305030a18090f090b07021606080702070509040605070e150702 73
    0x840100203040702c0d03e08000140305035008a004814055010300e154648042a00e03080d81c8101c54100c1643d0340d00c0f000c40e070341c005603c0308031080002401720b400c205500c003030706a0ba00c0801e41e101c00000d0b0b81c80e000c4a6140896912110740a0361030381c0401c2403200180524915503280c0404a032415105d480010541070040000090000fa2040c0b1503030712200101d115901080355080690030403490401c1602c42d0319040d4078108011804020100740d03180d000c00914015494880c40c0000d1034003030b4000030074000902c11410071410280e1414402400390264020005035100c0c1000750407012a080a42101c05c10600c40e10500c0c0000c80010440b0b070660381600f003903c410980805052202c240c10f811841d009400d0100c1c8410501c9160402ca6030300e8480c000024081e5150101203030b40d001280c080f401c803a40001410041d40e4020340309160849210301c1603519081e20b840125100c0d10301038a040311203d0f560010019140d41c002c1014452500442d02d22b4078001c800105000e8a000d5200040d10548 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 375343606 1250 375342356 375342367
    0xf0609010f0509061b060621071707030204050c0c0114060108040204092a060210020a0c08130b07080901170708070302090a091121040206071707060f0b030f01061a 72
    0x1684ca0040c1c076465440004c503c07003844100b4045a490b01c2058440d58010381d00c401c032500894641242c8150001000b40042180782d182501803810b050300103038001c03110f024011007c00540c071175014a900c02c0300c5086170159a480d2141d00e072821249003800804804a061007444601e030380c000900340e003058044501207540c015504164041c60b45071011510f40700d4a80326013264401d0490068002c492081d02a03840039240744034414264807801c1540c100180705103655400080b010405401d48a041211005c0050f80b1382091507541d6000e01429202408080303808203041da0304c48076480032942d45c87e6582450f0708000c0700103000444094501000d058001c225550140c54600d0448000c0a18003014424407454007084040e59102c0d000030300244854031083d190042002c9503150007242c0c064034031407405520791110f919054510311b40e060742c183d0402415010036040e01500c10017031040100014500c121800301071400003c480b1084031039050400c101b241003d075103541c101d003550403101e80d981e50 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 375344856 1250 375343606 375343609
    0xc01060e0f0903090f1e0d0507090e01050105030309100c150615030e1002030a090c170c0154051309110f0a0e040303020a0f1b0f03031104060309020f0609010f0509 72
    0x34041c540841e80100411f40c41e035060010010310501190340b5039000300a002856104907080e00c509000d155019441003110026070304081c2c1d42c1c1c00d404040b911700042078036410754400710104c00b4001e460503025162078003807090041c00008040c29180b5820204058800c0001d1a40c48a8202d0000076040d54084005400c58100b5000041c0c116806600020f001d41c440d06006510344290034038400da4881ca1714138101c15406040036040984005011540300c8001c1c48004203145e846111098034440b1211f814426190301100d034100c114800c528a9141905180900a825100201c030070482030800903101d010820719004000e550700181c8002e0128900c11012502e840c0041d48007000040004040200307159260740a86010385c125607460306143c00c0e8440071103900304d18180742d05c0c00782084800c51001070121a82250305601c03c2c100414801001c107407030116a0896131144020036114160201180303049030304040361050458640341490001000200b82a00a4840000b40040028001c259 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 375346106 1250 375344856 375344899
    0xb1b1504151a0a032d030507080c070512010b030f010c051c02091c120203070201080106120f060f03050c04020c06070804060216061a010309110d080c01060e0f0903090f 74
    0x1400050040b10a49540e4a040326401302403c0002c0c1d00709043d2400740f801e103e2004005e0810503010fa079802c1c02c00e0031988406140c0d904c0f03e0000b2103a4440d01c100001c4a0b140c810300030350389203410f000008000c1c1024042c0350506070b0080340402c4a92601042001c6141c00100361000503d248440a01c00c501300c2c03041c0d400070320418110541c420110090f810008846400a9800320720604100308030620310802a40c0d61302515400a001c0b4026400500520b403060b409005104031120b07020442c400300d520303050221003244e00080319032030384c04100b4420301408116119828030b01b40d500314588020412482e464400141503a004c04c0b01b194041801e10542e60181d612000680305602075400403490948020318400d00d04041d41c41c259076a40b00d05600a00c9011810f175007042446001015540c00c21800c0b1b030b000031007150326000a100182903003130b091052402401d00300f0150f83c800e00300043c003c142030b40024820700440d401001821901d032690402d080e00c45c0c81c262840d010580003043d04802 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 375347356 1250 375346106 375346151
    0x81017010b0a0b07050f0d0807050304051f020c150903040b0705071e0501080c0307020703060e1e0c0f0a0b340b011503090c0315060b1b150415 63
    0x600c100d62402c08918101064000c0c071900717203c0e20031a21100404807900351180710840d43c0c04046240700b030010742440c0c0520000c6920500c2a0192680340003086a034034108a82178940090761580420550340f806002c204100c0301d80f206d4100c0c0c48a5251550340c044e90b0303100700d0203142c00e03001012404108105007045110058030407070303210481c5a00501e5008002030001d00c22280020a08008100f03000000402c0780d024120030740c050b0507030340c3c1161a06405802041c440c0b102034807504061008188a00900b07041040b03196024001e20000141004030100007240550f11600c13001c24100104480e803402c80d4807081505207005032020040004140129411000b03903240c2407222050740400940c0d4801074103940d42c200080c100c600c82070004800721104140014140207a01c0000d0003c100740c800c00004c821600c06000c203801e03840e41091300a0740c008206000d0032660b041403400c1818400c1c006516410741040c610b400034642501d4049082824070080c0900e103585d4a600a003c1117414416030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 375348606 1250 375347356 375347359
    0x30501081518010e07060f080a02090105161712100519060e0d12020f06360a1406041707030504050d050705030d0e0a0e0702070317130e010e07081017010b 68
    0x804540d0744600280c0729000d00031f120b20003d030303019001030b640345260320a9886100040c3c0d5403c0c1441c3c44001269801c40c074444007a0340d4501850304032800e01103094024400300c250200784010300d09151006040e07440941e00554418048500802002181420a9001c8580900c1c01c00c050030842d00200d6440350486c0da0107400000c80c0035100034001d1300020101c401107200c0080b0ba80d90780d40c81e2141c9135020030f54111340420280800c444d41c0d004c004008000045020b03103082d9503600d8000d646088680552040b040a07c3e00700c03108002c1400011290440842e4081c00440d203000c604e40d80c000c06a06c100c0c0039061003088516036940c2402020845040035090207000c450504240c00c46c088c008041c401d81041c410001c0c2e00000c584802c02900c0d02c0e0003105e1131780040505d241140d0769813041c0c04404001041900c01440b0300e06556505601900043ca00c40e0710880d89541044240d0700c1c82d5100400080c20301c90820b09020807241e00c501d0601c11140c40c50000c030100d181e01da901a0141810400c1103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 375349856 1250 375348606 375348613
    0x105010305250f1d0604111c060f17060f250e0904060b0310152601050c18030a0b0105120102130f0f060c0503070305030c1b0d030501081518010e 64
    0x200d075070116030205408032913030945000101d07038614040000b980c46c400540c06c0e4000c01880b40c141003401640b803806485008802c0481c0464981005c624081901ea00c140c850466014001c24140c81c1480000c0d048058040b580a0318508a4202100c00440115080604440c02c0800c0122842401e01d546200310003480505c081c105818200090b00305d4800c03083c07081c0034041d00072181600750304c41c030240b92180107001c1d0381e01c03894000101c2d26030410000001c51044090a5040a4a0b080c86424890307100c83c114241c030340721645100409451210341c11402580040c5103000414a582c00d040c0c1190400c44441600e0060f80908501a0041e5924130301000e030003d07008501c441d114080e800c25941c200c0e01d0b0054491341c6aa04a0b0b145100c14005465504100001d9011070702c154000d590102c000d02040d03107001e9010aa40108164102c9040500d400c5400b80c4014a541401000d0040170340390002c1008020188001c44184406801c10140d60840b800c3c4442c600000c2d08102d844400c2102138 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 375351106 1250 375349856 375349859
    0x9141326030a05100503070608150d12020102030108060a1a0904020111010c170901110d020a0c0c0902031e1605071b0f031b0605191806030e07080105010305250f 71
    0x120183c20103a03044000081c01090114841c1000140c100407180240c0d14020103441e4202c03007041c0d4184c1ca20340e05400240d410946000700364903000d150300707244440e03000694940c9405030440c1000c002802c100309040c1800001d4444008040900030035080c110f4080401c1d0f2031382e10050f64900f0380c10b98070b8826542400c01040c0056003000c6100242c0c014000984141e80d190b610326404c03121003001004190b01d007440a0315003000941c0c0581002c216a0400140100785916404205d44c01039000903905030700042000b1001041c1600b40c40044c500048100e460b00b044402186e07030b11100c017003140401401080741e4040c054880c1c0c807800301404880c03031030b0703109601c82a081d07401140c40d0100707450003c0031003881c00b0101c03107400484080f140c0540c0c44509102c0220305050503200d001001c442000348190700d800309a820300203c3d000502e05501e000038110503c0e4030641c100007441c6e00c0360203d1703494403004002288020071501c0520540842414519091741c03140c80040f500343c1c1014a800052400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 375352356 1250 375351106 375351121
    0x9240402013513021314130305280e010e0121090b15100912080a110d030b03010c05090a0317070c030302010b0f030a11011d0402030a02040914132603 66
    0x12109505001340c514031405c1c10003400707410a4a5212000300d82c445a9400042c0f88100d036280d010712654401c2c07a0042ca003810805840c40181d83d00309841801e107015940310340c0800c2c0c10006100d0a0b000a00b4440d08051079040040c3c452a00d401d1200000c481c07000311030b1000e0b00355038852410a40d012400c0180c40c14007401c260540b100d121078050064140c140651004d500510f00700c070840740254040442694180c0e150711050300040c6141d4280401101401c20302501030100000d0701e0322a030350015244c0400c80c101030965009003003040a00c00c0030040144186c8aa418810030740e07800c02c0c0c0d81d014000c80c2c0300305d49000740b00e501d5002d400144014004020550b06400c01c0d01c500ca4115000c0b002c001c41e18003010345501c14800002c00c0d15048030311501055000e10b001340400c88200b540c0309003100992000c1016680222000c85403c0d50000301801244054420781310b900400540c0c0000515091a10007000d045088000d000060f00070310071150340c030001f07202c500d00100d50350503d5100e081005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 375353606 1250 375352356 375352381
    0x60a0f0f0e0f0613050c1e03010207052107050c091f0612050c040b030f0a0b10020307020a0b040621090215090406080102091318020306092404020135 66
    0xc0c003180320f00807503011400c480102629900025040400381a0f504029010028040106800c10310750745401060040c05503003e1002d00001030246010700341000031000d00741c28201e00605808500f20042c0308000200d20002070030706001c00165130307210301c079254042c0c40c0113101140c10f800d00340301c0031043c40854110360280d031400021003440c0b014440d83c3c4540ba0140c520340114003920890308010b000050310003028000c0180c102c0e840c40030026007606000080380300f000b501d1003c540507a000080c880c0c00c5007400c029100c000c0c841c145000e414a81450401015040c125032448400c03508480400c01d22141c560203100c4995005010702582a0202c407a401c15410114034075126034946540020303110018000c540c04118002c108000c0c5e501e0310100b0030024040004e007400300c01071100e885030040c0c8041001d1800741586000810785852001c411840224040718201c880074854418400140d0700005109401610041100387c6201c1c0c0c0d5103080300c0a4003201c0040302e803021041c1840300d14840e00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 375354856 1250 375353606 375353623
    0xd0f060c110c010507030518130e0705010e090603120c010f15060e030616032703030e0d090e04060e0f1c140403020616080d090605160f02060a0f0f0e 66
    0x744241c1d40700365035840040d11280200d10002e000304004100d4030003542126004620f8214000f0a5800c003003d0340301c003c00840d0318491010403240d000f00011b201944e00304642d1000f603282240c40142e140f41c00e10209454445c2644980c00071200805c42c40d03001d00c02074001080320161128100003c000056819001d09140d2180c0c8011840403e104a131500300443d6003131060200325a030107140c031480705040b4002e0410448884c0140f6401c40e81c90740340c4d040c620100f80058000d0354040b401801c03c2903100c0c02d03c40812030040910016039020441160700c041c04503403194000900003144c40b4030988080c200f202580142c00d160150140c04500c1d81d041100030714030401c0650b030305513240100702085080c1d0300c01d03400040c0d4007ca00f40400198555002d03414001c40e0b01c69801642044080300080c3d041d556912401c0304c0c0c06407120100b21007180b815200481c1c40c10a860010890f114040002c2d46a030f8002c0c02c0c500d4060344030b0b034a1004c1d0010700c0c0c03c20003165000c82410000700d80a07a000c5515004607 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 375356106 1250 375354856 375354887
    0x91605010f0f080a0603020a080102030f01050315040206131d01260705120102040506070f05010b0f090402100905030703080c0c063c030906040c051e0d0f060c 70
    0x1001142951041000394505a040c1d1030780103050712299000d0f14500801844100207540740d0f0700c0803005840d2404400d0060000d200003584a003002003a98241f50f034144c110034000d0f848038030305c0342c1480041c00760260010340540c2c50694940100404880c4200180c010f0f14600d00410a61794844009404090403602c040c101038194040d0a6020038440005040da5401d0364080f400a00c8146004100301c90000c0000c4001450075664001094554006000694440d0194049801408000e01680302908011501e4a40d00304010b000158254000343c00030b03000d55810701508400d41c3c000ca0340c110142600604443d5800e40e24036101100d036119001110540c01900505102414500165080e14400e0040f01007812828038070011160a12500c0c04409803010a074084800741c02d03001140640030034006850030b4a030505288000511a40c0024028050100405540400c11440c403010b40c9088811220500082c1421004401c2001c409080742e40b800d0040030310690000040b0110f0042d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 375357356 1250 375356106 375356143
    0x60309170705100b01020706210204082b030b130e0a060608030c07051206040f08040506030412031a01050301050d060e061614030108072105070603021e0c030912120309 74
    0x1d910300480c0ca40381c8234819003010a900344081099121080c01c007489500507104c6c010b041544c0c03144000d2902c0c0031000e403010b80c0d003030302c0300b41200290b22041a0451507102d4102800040d000c0c3e404601d40f41c0000300190010399481c90200305044051106c03a914640102c1c003400850b842d01005a201c0e800090751170a48d1240203400191400d202c403035000d10034080c0026000e0741e9140d0700e80d1200300000c003000302c0380440204008030340d5a54550242d4080c81c085c4064807010301c0120006412541c50040300b91100709180c1c00d03100e00f0fa900c5400c680c195001a42d64000041141c508232010345032401c000c0d404c900450080150038100700080e440340341602c0e9510901c280308000d030024148028060340b03c66401240c0d05200d2005001d580c5a20303c1140010a82e01c00220786416080000c03a8002070002038001a2060382581e841990a00c0c01620f030b01003a241c0149190a00da0b60f01c2040d00b903d0103031030360445a00004005208039038280783c040004035aa49070076083c403619450034206640d40d207030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 375358606 1250 375357356 375357371
    0x30f04060227121b1005070f0308010501030e01020306030d140409060308030a150e040f0f02030d0810080d051b0304230411070b15061309060e09010207020a06030917070510 76
    0x1100082c0c032600703d03207013421404400c2401d1000d00011100d03400d200c0050003020440d890000d08022600000e090090350303511800c3d4101400141900c0707078550b100c00e0350f0380180144407141d0f5001c00d0840c4014001c0c00c0c208107040800240070a240556846105050700c0c1007030001c1405512801984101241c8008000303807078403000d2000d4200d100f8059409074210880014000580800c00300501502031410036094000680c002441c2c00c0707a1004141c000342d144018003505680d460180800b903e01100a04954038488070020540d004142016141c0312050440076010b0405204482c054110b4841200b60311203103c45100d5010520b140d028061894500c012103140c4810043d0340100b58044c940160a4849034401200000160b9404d50710502c10400c4407402421307403110b50010b2401c0d52011079214134144c9032031040034000701054200d03401041001e006903124400d00003074a4450a002030040d409003030440210b43d80c0074000d6020a00005d45400f40031001660040a04001d0405d11250 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 375359712 1106 375358606 375358639
    0x11a0f07050c03100b030a0b340807020607050313060e0d021e0303041211030c030a0306090b0f060301090b03010f05070c02030d050f030f04060227 65
    0x7584030314034400150030244018400240c042c0003c00081245c0d6011039162080000024040385504000440ca90840310b0391203485100d002808060038505106896504020039212011400075000240002c7c40002c0c4d8510518a654038076085854031054401110f251030f900b12022500e070382d0070b0001d15008000381d90890215134000c04000c5130003100b4064041c81c0042406080c2c00410070000850a50304030b4034a5811545450712240030070165140c190302030390400108900002071194480c03540368124030242c811007502085820301d00d100300140d540401c060141c000f08140b00402c0036401c0d551105c1c1081c032014002246c801d140c03105800071518100c610601043d5011403034415824200110202c3c02010b007420307071501c201811200300750301004091200420074880010104000c9805840c400da00c0a41d8411036052601da0340f02c3c0d8044c4443c00c3c5401140840c1403222017 = true := by decide +kernel

theorem cover : BRFrame.Cov 375179856 375359712 := by
  have h0 := BRFrame.cov_init 375179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 375179856 ≤ n) (h2 : n < 375359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
