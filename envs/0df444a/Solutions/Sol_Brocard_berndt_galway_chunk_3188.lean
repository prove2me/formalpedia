-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3188
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:55:49.263277+00:00
-- url     : https://prove2.me/submissions/2fd5925d-e8ee-413f-b715-970a9f05d65b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 573201438 ≤ n < 573381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 573202688 1250 573201438 573201449
    0xf050c36041515090e010603020406270b031305010b010905031b0a091415190b0a0201020d0504053009010309020d05060108060f010815130606030b09030a020609010e030301 76
    0x11a41c44450016042c90a82a9101e5031a0384001218280c030958030410346025104403074000d2001d66290360301281280070742d01540740410340ca040c40c0019090010390540b0514402058031072960744031842403100360020b0310108401a045031001081040078001c555038081c0c00e00c1c1c0115040d01d0080025501d5a500031804840390402c6c2d40180d890725038000c10400340501120030b010b03072041761960080c85902140e02800c900140781007003105140125200355940e40300502d150409003000300700600741d807190340d5010039990308116800354003605005851103240034501401c8000403030900d0710004003416020200d054080e9014000603048003007504c03441e00f420320b80099040300520209491000d1000050814400e4500016010900141c442c1c40750980c240d810007140d81e6840c01660f1541465404081115020006030b1200d254503e003150042c09004007240d11a40d03a100c203d034002090b194420660000617087d28001e03010030400c1d8020400000802a00103034030a040d8a030f00060040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 573203938 1250 573202688 573202691
    0x250b1c050624030601031113090b090426090a031101031407050313020d14010c021605090403080411040911101106040803100803030c090a060e010c0b0603010f050c3604 74
    0x12640c1648031f40e0107855070071240078145a40b54200c22903550540e41030f110b018445402d024680d013040c1030008600d801503074010588503401241c860f9003440340c100c0a640421821003440303482c68503a200d00107440154050700c68040281d049000044c01c1e00d68410124512004410911400660200840c0e50101d92000c8020301c2850710f1000440002d6088405041001d14403401208580c040d442411000782e190210b880c0800c8420301c00d0400c080d0751240d03552080400c4000f5011a00919490380d01c6486003000c405c18903c10800a0210380c200c80c81940c81041040240c0d28038200303840e841c0d608005909020808511068126568400050008121a00100c04150209040d402c0007000c2c0c0100c80030380f074491030a08100d00d0107400c8014210700c82c070b03000c0500044181c0181d40c103907992001a556040c0c2e03049241c80300500d40b80041c24640d015980c80c42514800046841401d019039980c01442e80c0d54103901c2c2c40907914030000e1303411075044040350094a0089038502e13151120800141c90 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 573205188 1250 573203938 573203941
    0x12091804022101060306050c03100503070b0403150f18110105040509060d020409050307060903080c1903090503130f090f0203060a03030e0d170309060108070602250b1c05062403 78
    0x99070f405401c05030700040800342404144180e28006c00c0280d4410b600f120480161030b550b65041641c0c0c0c8200e0b120f80c6200c014204001c0c000300e4103010715100500d1007050003040501c81c50711154102d4084003240308a6a006c49504010024041030500010380f007440d01d203060504042c0007540300c09001d0501c51080511107004011912144c0150410300d0b0007800740e91f201d01190500401412405000314000f070603a000142000d90408103071902c048514010342c405021192059005161210090b94540300c01d03c0108417002101710014040e01d070b031803086004649880c81c42019034950206507907100d030041c001c011b42030302c079001d0a00072039806281401c008102e160220300f07503027040b05018000c12400e0801c58403144a580056025403d490304036640c581e80c89400da03840c1c4006004a1006801070361040191010320411101030b1000f06420594041e0b8403034903184140d200f9201c01085c000508002d400350482c610420764030013402e6602d00341201c0c0c81d1410110f00fa40d83d0320040c1c840c0c0310110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 573206438 1250 573205188 573205249
    0x1080d0c05150c03160302070807030c030210020d140c1e250f1208070207050f0103060b0307110d0203030402031f2904060501030e030901201209180402 67
    0x80b07100725498081103800a82050800d908030b0303030300c1141c1c4025038280350030348044c040344240b084400d120b400c0340541d402d002c0142d4003141c4400203010240d04500c24584000c0c1f00c016039100502e101a280e400000e401b007042079010148110040844000310414401460181c140341d0207403404900c8510001e5480454080c8801c000104010180c214100820803030104110388404494282c011f0313410407010151407500b10307200301e01101c0140040c0c01442082141c0e040182100d040c0b0f01d0b0504000c240c007038452080d10300507002201c04030001220148090000c81d0107004695060340180301640c51843e050300842d0303550444c481d10a268480100c0c6800d00c407174460380b01300410700c040c101c1081c800c1c801e0340400080c40c1c14000943c3c425440c0c1540024a903000384217641075919a00091400d180c1000015582114090600620341096a1440458860504c160b0310010f0515a065444240f96814051503803500c1e2140c0342c05444407400e120160352842d40460032121803a04080d000c82100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 573207688 1250 573206438 573206443
    0x60501083709151404051b030a020d06060611120f090103020706090c0303110f070b03040203070522200d09020310020f031b040303050d020d1e020c060601030501080d0c05 75
    0x9086925407402c075a98040240031030100030141c9440105100600900d001c1c0061100280e500501d164851524518608103008030783c041450005c0a03103102e0000d49d0007003201c7c01d140450844036a0754681052001c0c0d90000340e00400c00b400030008000342c0a140191812503c2000f00d5249000c0d004071360400142e1094040760070701136100d00103100d411a9032500582070286808101c001c9010300700f142440d000002040f9000e01d0882c00140342c00d80c030300500c0102603407000d841a81c040c040e6a0001c031342c0f52560501c00840303074041502130068084800400d802c81d15003145502e00f403c1420030700c4500e01c00c03020076560060140100001d0300100da01c0000d14dc1466400d2580ba142d0000c20145115180f28000d98402d09607410244289040010b040c1180e103d1400000c010803018040c8442e20780b16a40500158a012040042c006041911684054400e0741009002c2074001071036a52001081c460f0310b801110a00301440154140300c01c1a40b034070341c02c44940d4100b0010104240500204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 573208938 1250 573207688 573207781
    0x5030a030b060412150e010209060a2102030708010311010c0f300c0204061a0a080907030c180e120f070c0f1418040f170c060703050a06050108 63
    0x59103541c948070313182c52070001904030745400010442c0385081c00d03100454006008983c01c86000034041440e188450a00703840d91640c0d1414a101e905041c2e0022107600b100c0d100a5014494a8687c00925032461a00148609507000e4660401c0815880d0310002007004242810702e5030b01000b410308c2800d056070302899055109032403441141b0360259103069940c10030726000441c1c0c020742d8113000c00d070740383c00c154040074614028895a09004008190646208820540c0c00404060550303400035030b00e4071070744840400394010f00d041d10b515600c0c00c0c071100401c0c0710f0300e80954042c0c0060184090101c20b0300360207004a1008519204001600c14200466581c0100107040b00e1003065507000e80b22420021503a00e1010395078050a6034003000b1111411804001e8490742c4d10112000c0402e03419500c1d2500c0480c4500c000301400c030305200c41c0141a005100d501c0c45030344540c1d000146840c0014100040d200580d00240c140b012007024406510740654000182c125070340d94034130040c403854031001c010040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 573210188 1250 573208938 573208949
    0x70221060c13171906060501020f01090b0604021c11030a0b04050709060518091603061e05010509220e010c0302090906040518070303021c030c1b030302131d0a0905030a030b0604 78
    0x211301103900b080504d5000300d040d1102030b42211860016445d080342294100e05000c1c103034404410001d50245860340046ca024611040d42c80c20041a180c000340a4489000210b4100140401000120000d45c07103414032204044078140210b0820b010081d2481c007560007039404000c4001800c50b46401603007000c40c140305010b44200c5a80c40d01d40c0d40710803100400d000c003400113420020300050f425182000350000440c8e01020036441840d200064446512452480b0b4110085a040d01410104528900d211030f408003008a2414004100b5600f15401b040002d000c0c580705101007511500d074a0507840e441201950300244a4948107130594070307420400c01080e0b070f43c4a00c0002004059000c41e0000100c03240b400c106004000883d016015159016141c0740001e0110320900c800001c401d007501006402400d00605e8904c1c65081d0880201e001c0c0c100440c092942500270b08149003817103035582e1103080c1d10320030085080c1550b616602d03440303480d000e401019140c801e038400316520803007110000c06 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 573211438 1250 573210188 573210223
    0xb0a0605150409050705070309060819020315030c03070f03080304020f0306070c031e0509040c1107060203070506010b12062b06050a0510030203061b070221060c1317 73
    0x10000078540070594400c0c003840f08418200400b1804841c040d1045c0c4246a9054841840840c2031640440d64200c1c000c00b604101c074150f010304038030f1603003620055000da5055103c1251600011341032502e02aa4030b81e4590103548145010440701400309035a4003600d42c0f140100340d503600c1d02d000040b011a40c142126905000301e405000840b03401c05038420030f0b18801d407240f005000c01c03581c000f003c01e07445102410104408000c13043e1a840c1c0342c0e01c03440300101c50b0b05050014080450709070b0300d46401e50300a0000350f40700254500a1010810609006080c16040c50f0b1501001d0100d58030302c40000f9101c80d0256804034003182480c0300010001880e05492003180b0490341d01402c1c940090300c025505c4000c82031801000c90f00c1030450f000c0c0e01c4203880e000f50007041a902e81000c000d100c074401e18400156a08140607450059481c80c02c201d082c4201200111030360004221241e0a1440c09030180d0401d18013046420842c901c000036090482c4c400780300c0702051500a264890500b0010603100c821803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 573212688 1250 573211438 573211459
    0x130b03010c020a02120307080f03090f12030a060905090a0f0c08061017190311071809121803241508010c05090310050c040b0c010e21070b0a0605 64
    0x101d9000500c4408640200d89405405c0c2800d02000d84903c00c0c01c1002c2c0504c1410850781d03020f40e02100c000c40c0c0141c110310482e00035a402031040c0d030405c03c0b24200034901c1c02c0d00000344403201c0498000c83c0b02030308200c102042079042032001c45a6078054403100410101c0c480d51454188041c80c60301d40c00402c00c860541d03006240000240c01010005d004034107007444442001040c030240025440b402d04810311a40c1000d221a49041c3da0032030070b009410460340309900000c58207242032011348504207c01d000110300003040c0d10b4140882003a0300f40240c1002010301e0030041c0801005120340c2201e4100b0344055061b0034074071115214846140c1e000d10100d0800301040000f44000600104982441c0c0c020090980e00b01411a03d900c00c20704040e074550f0000010700c1c1d01e00d259038003080c0c0049042681c1803500b680c80d083c44045800100b02c64109940d601140110340c1e5081c05a0b001c040300e080c40c0c00c401d074000c10314202002d01034079002902c031950b81340004101c800707540c1c00540901001850071185 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 573213938 1250 573212688 573212711
    0x27010602030304031b020f01030b040e0102040b131a041503060b031504200405060c0a0f05030c0d020d08040b0703110f2d03010302060d02090405040f1e11130b0301 72
    0x80c1c2d4030540c0c04030300050304414074034880c0006076441e070f2aa41d4000e200702607a10805004402a04040b442160f00c141c3d5030015070300d15602403000300000c103450162544c941c3c40d0000c4040d4914056804280c0c00c0b098014941081201c2c4400c40703050743c045580e00c0c1141c02c041c4104400404c4075400c01448400000305000b04429014041c016140301100e080c8a00071040b200d03100404084445c55284860a100074000c502d8018080c2c100c0540c2041142e001d0070ad1500c1e104d801d00d00300041600d85d904001000e404040003405180440e100600040c070341041c0a4070000e108900090020f08400c0092004c240e8884c400e400025428641040b099140c482600c0081ea860380001610300f14520450280c003c40980028032005102e0701d01c03107140c1941e2171074003803051a0340040848640fa9500308a400303006d9a5900c05c0500503402400752045403181481c1030700c514402e001e107002000d60400071040015100380155620381d8029540325641048203d40d10014149001d040b42d0b0550804990004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 573215188 1250 573213938 573213943
    0x170108030f07140607121a010509040c03180c05090f090a060504050f1e07081b060a1202040905100b3901020d0b03060c0f040b09010c0b0403091e050f27010602 70
    0x120100c00010400c0500c1c808191407004940d800ea42e02240b1f05000d800110300c1c5c40d500c3300e28131242a08020480a0300c1814541c0041c448610840d840c1080400c248080e050460200380d212569a409190310b040c20139072030360b950b840f01e20700038200c80d1120006400c0042c10302c02103a107401008215524051440c0001610048940c0c400403203104058000440380400210241c44150340c40d4503003012038140c000d00c042c550280c54954140006460b514001d40c00910043c00201003900c1e001a0b1807c001c0749800380c02440b1390000c88000307402d01958091402c01c69850340400340008441a0398000130002daa01e8450685050506d9480030407400c0152401d60000c0c1040002101914940c1d525a0850b1700c840c001c0501349d010101c01803100380541d1403004002d1440039414181180c000c1403a503540552044102c4044000442d020b500b0400d00a242682c02c60712482c02c0b00b44074440d0300301004960301d044000b070a90301c9800f1044581038808101c07507401c5043c040c01d03010044650b859250295 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 573216438 1250 573215188 573215207
    0x1716060b010e0a031e0515010f0807060806010e0f031905030304020a060908070308090a051216050a0b0a080a09080309070810053601021603170108030f07140607 71
    0x1404030300d81d8180320060b860b10000880540350303c07829100017a4035a4a80301d0541442d0041101c0f103100d00300382c0b1a11004030001890003040c1241914074042d040c10811820412282d024030240412102805002d0f0380004000c4020803082da0380e080400d034144000b0345406001302d800181e2403800c40d07460042c0309001c00203503c924000d5421501c0180c0d903c0080f500b074640e074420850706030420001030000480400c0142140300e001010a00401d450b000040c051802c51404001d45502210a1181d80c02e0300324a06401040b0461b01c110f2036500e44600c00c50944207054100d410450354900044000c4180c0e4401c501c01034100b0380954980c030b42040719a40c5d84006001d80f8078603101d031403481d6080401d98041d80348600290b8455040e20f910000c54000902c0b51301d8160307011104000d080d168140c10034405004000200303c10042100b02e5030a001e419030501d100741d00001c00d4a80c0c01800884000401c40c1c040040c0c00707104c1540c85611381000c0c0c4080c641103850751a14024403082c020a59803001050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 573217688 1250 573216438 573216461
    0x120103030e220f1109012114160305180d0509180a0b0a0e04110909030d151a070503180d06020703031d0109020901030b06040f0609020d1512171606 65
    0x1040305035804c07035455910303000d03410415001a4103144690000c040f4408142c4001204203c08141800043c9121400138000c950f1001d000d030752a0a8016015850b0003141c0d004001c5801c0d050086001105e495101d103040103050052000000e44540a41c480c6042c03040d40c2c0008008481c0b086c240744100001405800d00c5151080100c513001040242840030386a010310740c842800004440385000348102282c000b400c2c001640000e114440004846004028681c000b111a00780c94900f05583c4904d141e003011090350040c001884040c00085001046621561024410020a5510350002200d072015410010400d43c00816458109601500411450007800c10804801007900d4001d5080700d017000e60195002204100400211b401c80d80b1031600004041d0000c100c040500f0f400394140e81071540041800381c0c0c0006d44003d080c0c501d203d000304000c07040c0c02d1290030b03500e0804039980702a000c50b400f0b0050a4030480d07025044110200326100c070004400041d855031803d0904000a2041c4244d2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 573218938 1250 573217688 573217691
    0x18030201050c0a0504030b060a030b040302070302011b230708074112030919030b1f173d0506010c061d0109051c0203120103030e220f 59
    0x820b061060746002c0c0c0707144003072654609042c07034916101d126541c540500340340d0b0080d908020201c0410362594070a80710358000d40043c80310070700d10300c00180340102004040400d03a00d20040c01d0002400380038441c2507880811007400c1000c581040d924103007082940001220703c542c51700040c1940c0c50303580d01824404078144810b8070020140000050b0b02d280308030040828109034000c040307072a01303c5139840d1004807002101e040000720300214144a002118041d4018105401001040505044592711400051340c02100344001151404880480c2c0201d4240070803000120403420f00400c44601e06525103d810605039140ba14480b80c4e41d1041070441c10ba0600020044055244901034540226010b030340c4c2c0c0001d44010f4660710300801e2800c480092800b00700b41030340070180c0300b400359071020790142c0060000c40410049640c5544008002203003950014888489207211101240c2d04503901410059000d00c50a80080c1ca29042030400c11000070707042000c540403c00c80d910014022644120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 573220188 1250 573218938 573218941
    0x80901050604050712020d1d03180d0b0106110c0d031106060114090609010306050a26010b010207050f0103091b08070503190f020307170d120513020603191803020105 73
    0x184810b4800858940d00415401e240c45501700e0740541c000c00910f4644640003d00c0c901d88800783c00032000c034031801609540301080e10203040314151858540c0c5081100e444604004075503808400100500c124014481510705020500c07400303100c880350100340103001852046031450064002c1d80a1001d000091186800040e4107500881003000d0310028040768904048489081000ba0340c40008501c0c101038948c5c02c0000c458444900b5103000e080e541d61140d116825604400e446800c0c01c40c04408160305100e40300f4540d036004190f0318117070340301075800316071121020005a0103088100802410400c8449065051010704e0041c2002c2d0f0b03084a003640d81e183c0d80c1c4c2d4201a900d07641c80380712020758402c12a003a40040d2228180c070b0004d91014003502ca10075921011000ea100c80751b0140101d50304461054000b540d44100e5150340b960405804100f2410302d0341900c0d0071103042c040d009000b1000040456180d80c60140d00f2680c030f83e00180c0c10300c0101c491030049404100c1e0404110095800c020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 573221438 1250 573220188 573220201
    0x503030703090e0709050a081b010c0803011211060c0a0510020c100b0d0503030a06061701030b04020f060c01060605190e060a0507060b0d030509030f0705030307020904060b1008090105 81
    0x1215a600d82540d141848a420442c0c0f240482102800c50000d000c00c503440020b05845420704034000300085009080800000c106450340c45ca00e0b04001410402c941c00d084c40000c0208007600e065580d0b030a00a4801c1c0e01c20714140303043c1c0c403c0c0054185c1c0200c02240b0080b8070030001074248102c903c10010354500310084125071085e805440000c40c403c0d00120b40114905444ea801200101d00050114030940104d48a881c15030344152134884080f51a0711061107800e4004035900180038204410001310341c0345440f008030302000944000d1003042c6804100308160303100815101c082c05c112000b0054295912800750280d40420000442da603e02c155840302d4034044d030608680c510303000c0e040514000400004540580c44150304407180c99031507070000704070340703e0300c0001039114429104d80b55600218800c16260900044844207503034031115080c40291004429030b0403071503042d20348050030303180c525150001d404c03005007023500a41341e000c070116030380d602c40b011602480c2143d00810490301c648 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 573222688 1250 573221438 573221443
    0x1236010b06030606090d0f08040807091b0807030221100602010506040209011b050f0102030703020408010b030c03070b18060a180e040210120f050a1d06060f040207030504030614040b010503 83
    0x840c0e103c1c1d402034090100d00000d09001c00d91941143c452512481410755a684008407500990040f00c0c00798000f03141480051440c1c80b580c0e09903208041c20081e00e21410000801c40345000700180101500401c1020b05102d01d0380700b41b04c1e5003950b002c03503107401d04d04051840e07061000703449180019070802c4040390362401c20b882180d014141c182c2d03c100e019485411801603101c4854001c803040c1c42140b9846204050a10207107008004607a07015075502d04e82802c0b1401e40d0b2030022594401c3e004186003810703030360b400598002118500d400c40c0b81c4580355408669050301681c54090b0304610001507000080783e000e101101d0344600750103e01406600c950414011580c120360080d0800341608007850b40500807020a43c4000d03981c040803505141c210124000d40340c09554100206465048406420200080c400b4403010900001c3c000d5180500c00904030302c10001285000e9a0f000a090060520403011140a150080b80c00d10485003d100000d079045000c43c2c00f502c3c16043c5030008106480d02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 573223938 1250 573222688 573222691
    0xa0e130c1202032401021c20011e1e05010305010b01180815040606080a03020f011b02120c0c031915050105061b010e16090b04060302061236010b0603 66
    0x1200440c090311100340401441c66071050180303410340c46074060708488451f038190140d0260100340e44200b2072581c0e58040b80c00ca85800c01061205034140403d000202403840740a10032480c08600205402541d801c8110740400b5482020a1450804001009000341500810040d90303080e070700c4030140d10580c50303000541e4000340540e2a15070888912045010704000907030b81c00500078180043c440c0c1e95801001d180c460080400c50141c0c0146e502480c00c20002c1c0304200000e07001c1c490701403218101700e000075210404030079500b003170000c00b1590b1014a40b040104203500c51001d811540c0d006840448044104105001103840e041d0700c80e9460b401010034006c2d241211409031559080140400700304801e20740801c1079840c0d0f5941c90140f2061240b007040041c03500842d400344a06914101178031002130742d81c55040140107030b0510a0030001070301c490086441d0035004601a03100380d00d400d00740821507514403000c501b0310384003d40041d940707410803195140c0744e814180080000f040e500040c40b81d01d000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 573225188 1250 573223938 573223951
    0x3050903010606050c06010f180b1507060e060a0e0a03112104210209061c0605010612050603070b030712021e0a02060906040b011502010f1a0901060908120a0e130c120203 75
    0x10064110011004a0b0044600f54132b0007000040203000282865045c0d03045050240c0f0080c0e06c2e10840d604502d0b06000180d0003148203502400b0a80c0041e001aa40740121f580c01070070004111052618803100344186000002c0d203007008110340d070084524031645c0d0407c1c02003c4200086c0c1141001e20804811050b00391a40a4810101c0f90b544a0030408407081d04c1c4188244c0190014440b0006002032043d14082c1c04541c5030403081208443c03c81d0100d40d4000c1c0403a009601801c2c080c0566005502540d83c092680c0c90710b000110b5010005401034004c0c841c0c8040301d4038410340c5004e04685d400010300b0004002c2d82c01c40321903076141e00314517558880949015107420294801405506001d4682c40c0d1001d00e14000400c1c40700c0d1051040c400c880d246042045e4030118041d11480d10f00d440803040380184108d02d01020f0050520300d6054456a140000d0b1080c0c69000401e00402805014805d85c41d00004003072440c1442c00f48054006040040700b51800581243c1e00841d9012492098900400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 573226438 1250 573225188 573225209
    0x702040c021f38040c0801060e0307080a0b041b0b0702120d0f0e031504060b03010b060c060f0406060b030403210e0c060c031303060c020d050c06070c03050903010606050c06010f 78
    0x1020078842d0030b424205100f040800319600c18000c071207031503074054000c0091032650303140d01e55858080000d0060303107000c001a1080d0400c040c20061804009103407141d1580000e002c1e15292220328050244920500424150808405001800083c00400f0301480b034000c1d211500f65004002045466150105130040801d00d51101c0410300342c810000d948913a54003a040f500f02c046841b404400c101307000c4030212180754641c0001041c505003030050100301c000036580281000c03000032007540c80b80300003001a03400c03010102c00a42408040d0304428010051001000e40e00e01701810000c1c414413081c026040b02030006190104d00c08040d22841070000081c10150005080d410100031241c0e02c140d540c803032030744001d2045030310b00700b0000f2408008502c529800552b41c0c0558002070b00b00700000c0284003d2220501c01050062404514554000003510344859544611726068410740504540250158681000400c80b075400000400c140e0004100316000e5aa031040250301403a59806103020301f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 573227688 1250 573226438 573226481
    0xb09040f030810172802010203120a060308071209054002131502011401270203190b0603010b1909080a2f06090f04020702040c021f 58
    0x41d01c160b000390341120703108000102c010f0340e401c50301034003518658201c0c105801404203961a5803d90000c0e880c124011300c1e001454031001c0d00041c0d1203004004586c10f00f46500f0002841d48000c991100d4003440d8014000e6480e41c0140c00e00040f6502c882850201040210700c1c04655485c03c074880740c4640b0740f0300e88031616400c40000032200120180200e03680070f490308a100003511805001a0505654070100e5002e0580341c10910058858038205107420f40e454900508042c010300c1c681c1c141503030200c00400324103d42c144031012079141c0c50716070551403900c04130070300640c0140004014800c641448007070010744501e0302008580c0c0b100b8424440d85001c10401e074000340865a82d03000c0c104100307041041c0d910b80c0d10341016041801440c2d0442d407086041c0390000c0030300ca03041d10501d22420401010314050303d2040219a20380304503c1d4861003410868002d000c96501d03901112101ca5000c0c0081c003040d12030090103540c03060700a40e40d00304240c0c0e885001141c002940304544c190100ac01081e900e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 573228938 1250 573227688 573227693
    0x302120c0a1d100e2412250e0d060c0302130f15031d060a0615020313030201030509031c0207060615020d0e06040e070f020c01020f07210b01080c03010b09040f 70
    0x20b4051008090b01709003881001500548044154460561300840c1c59540301c6801521120290008049001e40f0003803403a03001c0f02c80c241210030840c11100d4144060007850303400c0024401900954010324031410509007a01a0b545500509103147d10120f100c408144c58407120304051300540214041c0742c1c1c44000b11903c83e4883d40002003e03800702a41031100141d41801d0b5410107004442e4541400d4484604100340b01508500740001061780c8042c42c10078030011205030349002d061202a0415845d0f001140417401c0c20700c2280c240030300840e00d402c6e81c400d802140c20701940025200759403141c80e003c4000340c6440003040d00c41c2110a140d018041018007000d0603a105074000f000c070f40e0000001d0202150f2140340b500b8160055489403100c1c40400c0751980c0c001d2600f0380c0031006030f045400c40c40304042c5101d07002490f44180e690359407602c0c2e20240d0103202490302010340c01000e0700e900d02c940300001b03009002184072200030106500070b100541401c428448450020342c0c1c002c0204006003045d801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 573230188 1250 573228938 573228947
    0x61f080109021c1a09011401090513031101061e03050706030203130b04170703030f0c020706050d050903070c0f080c15032e1e080105040309060f0302120c0a1d10 71
    0x10342900c500402e000b0001c4c49100f08510071412100c100ca141c0d9036105c0320710901d002100c160b0040840c803000703000c0c81c50a280b8140c192524810018144002c100701312440c00822b42100019000b48480d071076040015207440ed0b0960190300c4280c2e03150059403030110ba040d03c01e00803a4402c400c1c034110802003401030342d600b00c007a0750300034420703100360081107c58102c1892480c0100440b6010b56404500d021211540008072254000480203560020780d04100079600001035891258150700d0000b01961000c83c80c6003188901d0341e00604001c0004400300d100b0030300100b060b080d54641402c4450021608042c404403440862034031505c1c003010f10001c0d0340c0b50440a08100c42c090003a003807010361000c0c6c80502c142c4591580201d11081c0c00e0082007400488c19a413840c0050018800030303c024101030702d0103880040c80d401000c041110300c0c024050000c0c0a0780407900d14180074070038449145000e9840b40005c0e0002c040d00b5000039000301d98503192003204522400c03070351030003440e1540482e1804000e85 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 573231438 1250 573230188 573230239
    0xf04020d140102070b0f101809020103140127020a022a091501022a280807090b01020115090f09020d0c05010e0306160503070c05061f08010902 63
    0x10303020036070003495008000080c0090312201d84918010b00c0d0500303109032042e0102e040109480051074100004001e2000c000740280c01642c03201c0030006991001d800120064003584a003400050106000021894144090404410224665820b05216111807403090b445181e0f0110016480005071401e064585a1000d100109d080c1003a01c2c1a80520003055210f03a040718031101d1034002441c468460358041c01030116159840c80d00b07185159408032501003a14a03044010b0050002144000c04480307443c00742c51600d00c524004502e000e82d20880d170342d9034201d14017031220b2003030400e10714100c954014000d65010904400c8203003a03280c24500e0100040c802121414441034880d00040c0158445182840a480c01002510341d42403e12001500003d0784030b01b0240a50f01c4281049981102d5554915044d0110715103181d881e2603c1504580c810a0044003401d140110000d200e601e6150207030022521060300c050b0218940c3e00c500c01802c9500c1108065049a0a010326004400c03003400c690 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 573232688 1250 573231438 573231443
    0x100f050403061a032a0d032309120105040203160b120a1e050a0b0a03080708030c0d05010611060609091e1903121113090c120e0a02180f04020d 63
    0x15000380c02004002840d0028001500c102e00d0320b007551001c4407104035050150b00c08070030344072400041c060740d40c004e1041e9821008e40041210344001141d06d0305c80a0100d0740c00803001014014001e49040c0341714002d00341030780c08902c02e108101d48894401c1040d01c45000320382c20518035a00701106e4207906404014018400e205065445014200745294029003a0103014490300000e443c0c54480040e50454086030075040c0304440d01078040000034199812100d11991120700c8503108d446420b071030b403414041c2109403c1c0481c01c04c1c00200c5c04981c00a664000b91401c0c40494405884c0c2030f060144108003a0303001c00060b0044045525001080c040b0880d149800c00100e030000d070b481c2d55212072030035034620003200040c1d40c0180340610385040b801141010802c0300c41092800c0002c0c0400801130400c2c2c4a484611074440201d02d1000d801280c1d650304a4680302018441d41d00200d02080d100d44580340201c0c4200c403032250140405201d0002907101e410204a00402c1f620b8039020131045040f2400d08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 573233938 1250 573232688 573232721
    0x6041701180b04030f140409090b06060304020616030c0209010e040b0a1401050114070203030f1309060506031501170108010209190f030b131505070e03010209031f060e15100f05040306 81
    0x1c0c032082c80ca11b42c000700010b000c0d00400294828261401c0510140041d11051181c1414024003016130356050482d00140411100c2003c00d039120b282c161100900c40034065440341c0b80c0320001aa4030f070705061040c4500e12421081c2801c0d610030710940c04803907118156848205c604001407043d5400b03400040d20b44048000305604101c62a80020f145038051100d03201d00c050046625840740788039400704409440c20391024843c450400d404903000d070000400550f20a40030341515010769000b541180500d0f0b106c0140320040d036031586c1c100c5002c1d50208010700d0194181c0e00044404038050072010b82680c242c0c1c07000500051464030340d01c041d01d02c080c0040b45120081210382d4001103c3e000d00e000070014840000c58680f070b000d200a8280c00245448600a9004004c035913103554001c900c022654a100c09590b0388181d032070342c0d03007002041660000002c492907001840200c01e920407200a118030101c07804c90040c0c03a42402110960700c022a440c0100e10300384824000a14680c10681900c40314000703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 573235188 1250 573233938 573233957
    0x2030601030f090f050c0102070e070e01030f0906060305100209090103021027050118081e011506020c04050108032d120705070c060206100b070503070206041701180b04030f 76
    0x1400c03c940c80848111081c50760740e0401800c000b820f119805d5441c10900207006103611703040f0301c040207201c01040701c01004002c001c0240790768020b510040d41c690140c2001c1140061a283c6100106a0303800300340c4a80c461810910307110b41d030900840e900684040c090101592869090003074041119160005001100ca0007400c415420000703540640744c2c402d20110880d24050026208242d50403140c0c40c0c5a400301800d00040740006600c05981c0ba01118902c49212004241c600408140307682d040c6900c40c198001072000d900082c018084030081300c0400c120f0360307203101c46039581c400d00202c902505002c0c030941640303516110650008480004402c0c4c0780c044c1c660110801194200c1e0204081400802c0701014040482c0b241030107401180001c0c00c090406240c51008400c40e8810404a030000150a204211007401901c404d00e1b80500a5619241c66226030304000c5103000e801e0030150702e49001404100001d22050750b13420303044400c01542c1c0e2241e8500300d8460207101075a4050104884 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 573236438 1250 573235188 573235211
    0x70b0c070b040b010e07020a02100e0a05100201141503060613090c060314090604030e060d110d2715020c031911010b0102060f0f100b0309030a03051f0302040203060103 74
    0x1120716209512544010034550b052000c11840040d0140c150b8046500c005111700043c0c54074405410725081d54100007090b04269000641c951038150041d68000d0540e02c40e40046a4054000803421120002d0218003562030000d4400c04908032542d4a9040c0c0c40240810102c3c22301607822000c011a0030004a01040e09403034180600d800c1303074403c10009694055400c030105082c0f680c2c94001c026080604014105900c1c0208049220300c006031041c8000907107188258019403252200c400e050445544481c042080b250080010401081500e5402c00309644100904081442034990207210380b941108421004402504801c441805a100c00c00ad4410020003007242c1c40a25092652030b080c00c22001d8200e0790944489445481c15035000702c00b4043d000310420a01036001075944170b04892540d0b1011810050354040e03000e403175202000014000b401c58080700805e0310030384948080c400e5803500580c00310048001c034035140f0144410714044c4014900b94005541002d81403402188202c0c981 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 573237688 1250 573236438 573236453
    0x30f1912060806010312030207050604080a050d06080703170f220905090d03060b0405060403021c0209090d080c040e1504060f060e0307080c060315010315260d05070b0c07 75
    0x94004000b40d0b40584010010410742d020310350466211b515065003080d103da540c0d5582d07800041c10003408040c3c04200e80381d00742e1162050b511000c42550060110716179807412303591a6001070000392240c04240c14038190035990b10080307580c0e0001e40000546040e14120001c001c42d001c038030b18045021450320000800700c00c60301445024000c0c20b405032140c01898100070b012980c0e1503000cbc03880800c05000c100074696402c1c040d1011290161031074000c52025080307292682c0401000298002002024402031500000380407044c14140c1d04e459070707103803540c20047e42c05004070b2240c0004002c4035000180d81e1103d400b81000c21000140000c00c41903122290034000d070405400900c00030b45402a481d50710700d0104004030040c50140007800700c1458102c0440c0031440003c1101e0148092007420310000e074400c1d0311048115112002c40c1c0d400070303140d00252112035004580c0e1388103081218043e142c80080800ca041440403592200b501d8190b0650b40d100b000b02000b008800308a40910156000c00e04c0e1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 573238938 1250 573237688 573237701
    0x207061a0d1b09050f150a050f040b27092a0f03010f3306020d14091e041b020607110f070306090203070b1305130e0d0305090f030f1912 60
    0x2d81240c110701d11b0001e0030907002641110303070588100e46030f0008100f243ca0740400d92040f05c01c10356020944842c104042483c2030f019400001c00c038900c2c4090090740c069221021030203040d054058440d642c00981d51410741c110030303104a4903030030a001201c0a513842c02080e403011100019001050407161002d0807001c49071703805028185607010140d0781c40300c08006207134681030f001c3c1d0083c2d81c903c0b0341c00c0140c020b54400344014107105001e04100401c40040464065038040b20004024201146681808850408114103540e000d1070402c3c00c91070f07074440304e03d13140c41680354154000c0011b40d0300c000c1c0842e80b44c907a11100541ca409190210a01d051042c80401e0281d40100d40c081004049072041c1440c2c95a640e01c1884141028012545060688075005007241c80c2102d446403092000c5122400804000068900c54825040c00099486c0c058100c01d00c070b0829042078515a1102000f10381d124803954a24940c0d948080003a504c424404d400e50060444441c17600c6034090142d62034540c2101c20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 573240188 1250 573238938 573238951
    0x70c150605011b0803070c02190b07030314090c1e04060e01080f03030112030e01050c0d030e010e010218090901110409090b010609030503092b060207061a0d1b0905 72
    0xc84840600c4103580008411401e402500c1c0d00c0c080c60300c000c0c1c407030703440304d000181c0140c081254549a100c150343d1030482004c0036480380b0318001580c1d9586c02100f07050350b05c0810214086410203080039480007080c40511303c1144040b0180c04032049002c01c005480024941e0702111442014954216498601c5200040c20001010103040c4d41048105480c00c002e00385d600500e98810401402117000c40280c507010590305080814031021900b0050322940540030044a4512842104003501a0f25810000d00c40d040e94000300105941800000c6c2070b84100a086c00701000d14512900352810700a400701d80c01190340307000040c4580494010340069001da03000c0580706032240c11003003c1c07140b24600d0301c3c01000c06041020700b252955680913224080d0103100c0340321f4090000b2030640030445035611201032802440c50a404803c03403800e48029040140e0580d90103180032010300c0e1800c008803002e0320032800100f80c3c241c1082190344107490940c90b02c101344408a01468001a15901802018003030507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 573241438 1250 573240188 573240191
    0x908120c0f0102070c0e1306110702120c0105070807080d1410050405010e01030305071103060c0a0e15040e0411030d090518190c020a140304031a061503070c15 70
    0x2480340c40c40600c0c000310822000c503a644108a501c0c00208540e81100c1141d6405020740d40c680d64802c6a403600c000c0e040c40161007581003c03012900000000001c001280c4201d0b40ca28540c00107020321581c860411140700d0108100b00310701030124580030041c01001c0c0c0724230b9010f0301c2d15a4602441c0c00740e0700840346104020f0068014841441010800840606030030364082000750724043c1c5030000b001045c40041c0502000140b560280075010300000c1c51480c0250803215241400403035040d0503403203102404001189541c1c1d41c4194509410403038200c0c1590f00b0301e14142820300c0410000310501810131200350100c000010080c2d00d00b407120b540c1d100b026490b03550072589480c0900c200c15800d002d001c132030140400200b00b0400141540303c054500101e50000c0c0f071150341002685800c4050381c2c05481c001b2114181d20403648004001c0082e00e03c40d414500a0380702900343c0c84482c6c4800d4070301940c031461a503106d03006d254075400a960300c2013251900c45034411564445034401c032400d104100519 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 573242688 1250 573241438 573241447
    0x8010803091203300f04020f060304060906060e07030c110703020411040815040b13030206040318030f06060906171207030e091509150a030f29060406090c0e0d0201090812 75
    0xd800c1c2c00e1340343d21000e0044106103070301c3c0685c00100000d0518000c3c0e845500040085824418680c0c0000c0503582d00110422070540c41c2c800413100440101d03a03c40020b414403170b440c802d403403003940200c2c070301800c00004003119030440c0d082101800d440c0140c0d0040100070300001910340c1d0108805002c010680401c003045040c02e06020070403171402888908a0301442d0995800280e002810a40c0290586011500304418800480402c2000d510142041140041d110306105160380700c1e030100e070309011081041640c0d410080d15504944041600c1d550003581807401c0c7e5200c040006d214813440ba160000552003010700292104106885103540400300c0b00c0100a14103060f551641c210914008601d00f068640780003d128091a000c0102681c0c0380703c901c0d10400000010700c01d0a90854400c6e1800c1004260402d400608100e403030328800c13401c007480002c0b1000a4804c15034a0149542c0d03014981d0112020322000003650030b0100d041041d92540051050014440c2600040301505400e40d81c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 573243938 1250 573242688 573242767
    0x7020d0b100303093c0b070b0f090c13020a05131401080606030c0d0b060c0a2f090a240f060e0906180405010f0c030e0d08010803091203 60
    0x38080780340c0118008201c0b03402c0e003102140d0400c5410101003085d004002c03040300300c000310300441e1040f80d10490301c00c5030119241007045041403080d4401c0c0828501c014003aa5030002e0140d031101806001c0ea0004022440844090746580081001c2c11007805c096142c0494003815071011141a4050300301d00116080003901580d00541e00ca41143c1c080324150306504140e06070200c14450407505000b120ba1300c0301084c0040c2c071075a0a44000c40c81c81c100352480e061031030500329004c80171a43e1b00e1030b12103018041a6030700f08211145034000300f8050801000e5903110800580103090440e400e900106040d034103101c1020b1054200f2003d003041d6011901600c0c82c0c2140a820010038083c028482c20603141004044e841e408041e035019441c0b000d0b41c80c0541c4036810070500400d0411341480701d45050441041e91160543c1101c42c1c003c0200040313510810446104480405007030164940642041120000300c1c6465000741c1550800303d03003505c7c58009862250070340040c042400e042156241070a1440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 573245188 1250 573243938 573243947
    0x9080a0c050f0d0f020d0f08150a0b0a0302041805010b0319180c0920071e0803040f110f0a1e0b0c010f06050a03080901030f06080f25140607020d0b100303 68
    0x10a089047c10624890824005800c5860081c21f00300d0002d00070401031800c0d541c2c0804172000b44205104140da40d00100001006580603008107009800302e081c12401c003d2041c420300d812240300749056400c43e1101860200024841c001001e112510b414070300c0911a2008480d4046920800ca0110300300d240c0a10141562480084680703824412044000074001107001c46500b168001400d10356a607211007007810300305035018040c0c4801c0c4040100802c0040c540082028140901c03840b030a034050700000c0140b0703501100d030382c6a00b10f000140c0400c1500042d40040484202800340560340c55162038440b0180d400c5207517024031a070b45840c2c0007400c49186105038000303071105903480502c65055407600d2146100b8039150b20704055030303000c1681000368241d1254014080f56015a0010803082a403540d8031040b010082c00d14180590103500720121000320002200c074440c8080040110410400c02980c00c12078080c0d0b08154103080c2000002c000b05000ca105a0000707440b0b45406095090081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 573246438 1250 573245188 573245203
    0xf0c0105100815040b07020f070f140a121113090503040509090307050a121b03020604030824010302180402031305060c1e0a090302060f0d0e0109080a0c050f0d0f02 72
    0x401c94001a40f028079074180e0030080c590103504240b420b00d9035115100124544a00b035400c900e4103000320b1002060100c4900780383e408480194090010b50b988400030040c85100d2072141a44055000c1052000102c0310700240094003402422094546203c000b01c1041c1c0e03c60b9001243d898000180078405842c040c01056002010301e40190706001a590f40c0550f07039110190701814204201c1aa204074030703ca0300b00100b2540c0c02c2c2800000b18611303880e02940d5084244c40440100d8543c000133201604001c0b008002141920b4131030320407600c0b84005500a51000c03c600d41a10501c14080700581c40e240010342c0075050a0b001c41c1200c04003814800e080400c054a5a035002c1c0301007080000302400706504d00130000b209000b0b00d99403030708031400340d5982d0956171000f9044400441c00e8280c0e0100c603030280c10b5840c08800c090100c2031440381e24078200c4141d4031006007400424050011414481d0b212148402e100700e003160710090400746507500d40310302802e144c070000d94440000107003280e0502920 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 573247688 1250 573246438 573246449
    0x503270705061c0524060c010e10060e063c0603040f0308070206070f030c020f15090d090f060305041a0a0501140607170a12021201060e030d0914060f0c010510 70
    0x40188001d4480b030328603905c5000d91040c4106004100c4181d107681c01e504c880c40e072501c40021206034804810102010b0502d9120700a1a82c540400241c0d442c00d01328030608a070f0144480240d03002d404c2d0356000101104d0202500841000b41c1c00e5030010352140b6000754000c50154555000207280c0d40703001400c0c041d0042c01030045400c24400d108a154002950040c011420304020a400f003106c01c04134900000e1007052201803040c0c11201d40070305c1d40f508446008001d104141e4001d06503036501517450380707142e100b0071821403090542048114420380c006034005229640142c0d16014044ad0312840070001c0e15082c140a0b5102d0040102c1c800510301d240300c9803403c3e20103030700b40003050f183c410f24030144144521441c1e03400a220140c0c4c42c481c8058014940e2103240464660204006000942d0400d00034240401c0301d5811900d9189000900442003180641c0ca000c01c8504042c1d06124a0590700c00b0950403d00038446451051043c1014000118200000040c2440e10a91420400310968081d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 573248938 1250 573247688 573247711
    0x1902010b04390e0d0521181c080712090b04050904060507031806020301063c020115170705062502040204090e1506040606020309010c020f0a060207090c0503270705061c05 75
    0x7924062100031301861010700120352182000851020610231021400e000501541d4001401c40411011042d0401c00300d40a680d86902c19032180c0b24204244200e0061680c800359146c0001c000800a40180b0380c0840546408691700c00000d0018020b441c401c00f04407001f51300440107001159100e40c4201504400a0840c0d40a0001e00c40750100d0401e1050500404002d514204401600035045048039401d44201190300b103940300c11040c0d0390401c12404851502a03407400103280c1c070300304041ea4040c4510000e50219030440c10b87c210286001903200300d0700540c0900c8006503101c100d1042d0748550f11010040e290300ca030488039510301d0f00d800401c035074031481c5007030801d100040d03002003612001402030a1031788400c0301d40c0c0002800b44410304000d580c0001c007d0000309140758040b0750300b821116242c0f01800904034074042038a40f408125418981c04000d441902d10201c4034810504148101c0800c0d180507680b583d010407496400340d448510300300039a00703c2800210b00c5215403640540710740117 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 573250188 1250 573248938 573248947
    0xf08060f1503070e0a0807080609032a0f070b09120a0308060409080d0510060f0c0209150118150e03011104090e031902010b04390e0d0521 61
    0x1801a90100382079020309076002c8001001c2a009005079040c00c04010a92415241c2d1440340c9a6140d900340501d43c81405541c006c928501800030641c0c2800703490490000e5140301e07200c0044e8103c080e000e1030318014800d4610324044088180030080107001d8402c0c2c03c84c3c2d1290400203010b000c0c5000c1e14800820361154400601081d8003174002504441d0880d40410085135508220f00c00d4050707c0040c4170320610340000c7c0511504912808002c4505039280c0b80c85c440440d1006075850300040e07401a401103030a400003407030400b21850b001d40125050422081503014401e900d0035120071a01312025041851140f450495044481e051035820120001d00220a08100860030f03406a0f100301010320761602502e070390915040c025281c4007660301810441c4c040803404002d01030300031001018000c038035060314440c10004001685174401d01640e50502485443e00044900c0e00c00c0c209140100581e80c040c00c0000c0d80d0f41c2020b040424051002054056a1448424070700d088034155070b82c0c80042000f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 573251438 1250 573250188 573250219
    0x60c08090a0b0c070203010219020c1504050402070201030e030304060c021e070902030a090503070f03141602090703020d06180510080709110f0406050d1d0c131103070f0806 76
    0x50035100140d070141805280341c540b0314800d0800e0050f00130095155001050541c807040044812002d202000e900701c0d8001d030b4441041c000380b01d81801c0d121a03101010003060110382482d400800c2098810301d400962203160401050850700700399003c0b0f840940b10381c04c0ac204241d040010320145854242800e402403890410079036500312901c21508800d8000c80001d1015045034002e02c600c0ea000425641d48040b1450841c108441e2007000300c022441035900452031450950903030754904109030b51034030110307025000c004003624028100f004041d000c05c01c00d44a12110700562000741503400d40b07544050080c1c00c00000380c43d0000c3c469000003800c04000c005200001884000310741c1d01440008800c80a0740704600b5510840c074001618410018000444561000040aa042c6808810002603040d900e100c004010200c40b00c4000340c1c00300e0140d800c6441c2000b00c40401d6420b5202c0020601e402c3c4560300c103241c004507440404078101c00c80500c0000d4200d030350f107030f88000704443c030290b03511441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 573252688 1250 573251438 573251443
    0x301051501092303060403020d09080c060f0310050604060c02030f0c09010506031911040305010e0c10030e010219050c0d170403050d0b03010e011b0903080403021c060216060c0809 79
    0x1842040f1140c5410042210b14000d81c075109a200100078050316a14541405c010b550f07035440d90200800034610f40c2e4001003644012400c103a01d9080201164509a0075219450283c0c2014003a01e0703100c0001031001540ba641d4800410007440b0719210003c12810500425081600900710248075801000450410b50364829001c0d05507407044420507160340384d10034107a1803071540c9040c23980803601c2c0003030f03104003040c40c05c0190040303d11a200030303c90300034076003104c81c1c84a40c0411482d4206c0b404481000466000741c100c3c0c1c4000000a00050801081c0c46c41c81c1c0685082002d0000401e90000d01580941c0003071005190718042818a44000c0144111400350120000d00140c104040807480003048540ca8010a546001c01070007404040741e101030b454001c043d0070300b41c200400e8107451018001400390070420202c0340c000d4085400d01e403968082c090700200b21203c5081400301401002d00080d803034805492840844d42500c0d1003000e9614000048454010307a100501019508004040b00300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 573253938 1250 573252688 573252707
    0x60c1206090b1903051c02030f12041e0b0105040506010507021302070605010b0325110a050c0102010c020d1b0218040308060901060e1e041d0318090402212a0301051501 74
    0x914540c0d0900106c08041207080d409084d110120001002811540c000420b011460146014040f00307250721601c0018074120741c00112009005103142d4004001c0c900e4a544a10362002042c1041403034911a03900143d90003000807005a8525404204c00c0140f1845224407805040c0007145e0501c0c50501d480720391481c4080703e034014440c20700340e0501c401244c8201188152611200120383d07141c82e061900a880391a00c8400ca070040d0328020320000014070000d4000220006a1200840f00301048100400b06d4090318050360041d03485510070404a036440e40c01c503c144d000380d5a00c0a64148801003140050341a8040c60401208480703110306a070781c03540200c0c0b06451303801e5142d1100c403141021801a02c0c215031003942c2e400181e5649120b4210200003003001201e0358041351201d0018400304a1400c04c240c43c0650842141503104044090705501c1d2200e00c04000c00b124042c1a03007402030700c1d240c0c00e421403154810b003000545041b44d040c2401441d40002a17a0000c220b802420400204102e02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 573255188 1250 573253938 573253963
    0x703030203030a0c0302070c080607140301050109030b060a0308220b120708040204060b04080a03030e0105010812030c0c0a0606060e010e2202071506061b050a060c1206090b190305 79
    0x342c0d0441311006a0180c0c0c111061940c2c00300407c021641d0b04d4010b50b03126402107640c40b012850806004807414200404c0700c0c183e0304144c44080c4001d007152039020f4894001040c075500001c1505011000c2032020001d001002c1070441e683c104103070071540768080d4038a44c1c0d0011004050034803410005038803c1c02d0340d507401425481c0005c419070396400064090010781d4403c00301000e0000d404a208540410485079072030183e1414030108013480703a12400c0301c0007441588901d41000c010108521820401581c110f500b064000f07080806a55203070307081c50016102100d00342ea0f50101003102c20381060700b43c100f0f500c00742003004d0b103002058017140c540300040c264800a4004410114081c60640c2d05031a90940c01400180f101080204907030001c201340d0041d0404641da50030b01184160606031030303800656011014044c0c0c00d60998412014150380b030035610030f01207080c1400d05180490701c22030004061860001c2214aa103005101c0c00480c078031000d2000c01c1c0c0c046010300101d0f0b00058000c25864 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 573256438 1250 573255188 573255191
    0xe09100509031201030803060a17060a05100f06050d050702060f16030f0204090504110d11100e10121a0a17010b1824011707090b040905180703030203030a 68
    0x50750880c52508502ca40200718115500d104004000c0c0801200594403624045c2c4083d011340d0380b0381142c9640f10038075209440442d845030b0006114449141c0103150494040e12010840e02d84480b0046600107568008900003000481d6480600c501402820741150700e5001a06440c203180d480300004450042254403a882500d0b925a0301c140720b0ba1240c1e4204c0e000c60000c548a40c0c80750949005400c003134034191020b83c03000c1c084103450310b03100c800040b46540c03084c07100110204e60b01c203101c140c00da4400c840c0c040c8240ca40c02c402540d1a0f030540e2401d81a2103a0342c41107a100c5076502c0c1012640b400b9444080600710004c0034417642c848100280a8445000d052044009112111405001c000c903441d9001001c07002404503041110b91902e0044841402740740861505008071840316280c1c2800c640019409604084c892900c0a15560488000d150400f8119292080075419902a602c2f00007440d07a1041003010400b03006041100100000e00034004031403079500c000399070340000f03400f0f40d000301d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 573257688 1250 573256438 573256441
    0x6040225020a171606020610060309050a08040b0901020708010c141b070611010507080705090405150907020f0f07030c0e0901020d0c170604151502011d06040c0e091005 74
    0x19a51185200003c0081c003111207030741a03480c140b240c1c503a010700641203004158003070042441c0e4004140c0340d00c200000410354054502d040c004034007412249505031441d00500f0210300206501800420107808500581680e03400b030340340028680300550b44110520703450314951302034a561000108210301c034a080c92035140d4880c1416810000302006c02682e042c480c110000420907088040982211940b000800c0156034100c829078503038408031540340000d24100040801403a007035001d03d4110041d603249005081e041404903c00039420748004c8056408982851221201040554909615580500301c031500e0355440003c1c9044900406420305a88800202d00d408258143c4050024400c0207108401000c13001601c0440700803484880d514112000490f14207040c011111001d075250340c20145c0d0351515200c01e4941c4803414a010441d520f4600700c02020030b0750112440d104d414a805000d29003410314051082c0e680c164000c010b0040000d00300010788102040c00c400040d030f21440803d0b103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 573258938 1250 573257688 573257693
    0xf070e040b040905150a020c0601050d0326090c1c0f0f080a120506040207050c010f0302040b0f0d051e01060813021909051f0506090a0521010506040225 67
    0x192841406554115140a0f200c07018813030000f801c40452014494030103521784681d90346400768820101c02e0400c07680848010416800c01035000c08007503000389001d8042818000c1e000c00d411040d0030940100c601000c4c18040300c51001c5c800c64050040440d01c040441c0040c640c107440d80402050003400001c1284003085c14414410751440101d680300c9441640d030003202102502c02d00e401c0050114071450200001c106040c0f0b8800c440030550040020411900d46400456540d00440d5550341011b8080c40000f503003c441c01c0113010140d2002e81c00503103c00050840008070303a801440030307a001050102800061035840100c1e4195502ca00e0001d440da43d41c00c1c2090461310787c805c0000d40000034000003840b03016944001c50140d680d84a4240145d4903a1140d1600071481c141e0f40f0710000d0340744e003c00c04c40c1d89010402816002d1001d0140404541c1d2034000603904d295481181e94403e034074001900700080c00b80305160340100c00b101e08608102101d5030100210800f20440380b404841035661070103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 573260188 1250 573258938 573258941
    0x20310030c06030e1603030206040b0403090b0409090b0601051e07050a081803070e07051b1603141603150b010c02030601061d060f191214040312050f070e04 69
    0x610782140d4015890307030741c03410001d000303207682a4036000501502e040c611900a00e03401010441c0e8042e401042e00b5196919a07001052000c2c01c203c05002401100044080044006d8002000d144000040c0b0000c41c0c02d00d5429000010038040c10481300308001413601c00b04941010000ca9840c0c00151200302c1c503c0c049190070307513802014001b1100400c0c40c013108009100b01800580090302520320b01ca075140310030501620185c41c1c0c113000c0348c41444a1810601c14042d61a00303804c002041b83c4c000107503401c2207940401e880c0c0082d580c06402c8603c0d0b0404042c208038940d03500c0207001c048801da03851a00c07410110900b40c0002c5220a850384810b00b050380c410f0100c0148950003c3c292145540d64a80280480c64940e010b0401403c41158100152518805030b0311440341a400e0145803540900d007048010a1a003090748c00e0220100350070402a42a100300a42000c110810146504180c2000fa0881000035001c56481d403c00c800c120300b100c00005103d401c0651307030400300120710300000082c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 573261438 1250 573260188 573260221
    0x81002030f041e02060301030b01050f030a08160515040615080303070f120f051f12200a030f12141c0b01051e07060c020601080a080f0720010e03010207150203 70
    0x1e501c51801b00010061100c82050103040300c1c0102c86c4092a00c0070740302416140c20844401400b407130341c00c0c0f0600712034094a4080b040024840c034280e0f00368003c9816044038094098a06840b030664a2401502e00d48603055100080c10b22000203606610f0941030041c8883c0480705185c00704030707a48104111404560300420000080f484080c0708916040000b0402c00749481611481034900440c0040d454840c1c140d040c85180d00034656004ca41100c1c00003481e090300714403040d90030950307040000020409143d0724000301d52003880841a407100d00003005100040c5001d0210070b40d001000810300f50200c0f050144c1690b1948000441c5c04844000103a41c2805070300074aa04800c3d18100006c9121111801407405601c6100104000c20705400100d07510482409041e00d240d1000b018540820070100140c0510346a041441d4074000441c1d40c0c156820403032943c0608461400703a40c2c4100d40d030300300003a190010b20030350007181402c0b1a500c900c203000000d403440791200d035400004512401c1e03843c103514 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 573262688 1250 573261438 573261443
    0x60815060f0c1b01080604020a0c08070503090d1b0605030708190b060a0306080d030212040f020303161101090b0c07091a0406120308010e07091e031407081002030f041e 74
    0x1034020f160121440400542030107030044c00903903840c00151070fa1400e882510803030354050340e91030215243c0d90b035080c0e141d50002c502501c1318032060220110716501d4075840c0c2041071241d00c1d2005c0030542c0300d04100b2504c0048c1c011009200050003004000c0e03034812a02540005102410400e032181d03100050f0051403d55140e542040000407203651842e01500540d089440740002c89a80e505000d03402c408a02500c0c1000c851800d038440454003103030700c1c01401e911890000382501e14140c0310599240c001c8861000440741c1c2c070503c5401212070340c0c00560143c028181c1c00f201e180703881e109000407502c1e00303600d0099006c15503980e4945200d4240039148c405440d80302400c1080240c2c0c4403001e90b00d008209110482c0003514940010403811807498010f4020703140c0d40c64990740281456006600200301520048851424980000211b0101018031115a402101403c5541c1c203001c1c2c42c90034829170b0742ca07100841d80100140250740301d03605241036205400c000304500300e1200e00540c11803c0b8507030001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 573263938 1250 573262688 573262693
    0x260714090a0513200f07120203160f051b240904020403141c02030717070c090203011d010518130b190b030105100504020d0902060313030306060815060f0c 68
    0x800d40305240c2d001e02d111140111140030050420313030100381d07144249516038076030070010700614000071290b001440303c0c1180350040d241041c01003400b101003129182815180c00d00c000450005108003030001c800b6031130b9100d02c6050403c0001000c100740c0100b5104207182d0b00c02d0012011083c0080c64103844013007000070029503840b0303541d0130a00e038000c50b1803250315114040c0c240110407420280d1015078031280d864004d54200045900c504d100c0786002681310f148441e0130440300780040c1d13285180c00003612403a440140c507541840410814460000400a44241800014030640c0d9560441c00d55047d2030040b151441d5a036285802c01c1c8002c0008000c00403042107040c0b11094a103001c00885441c42104100044182c840426081c0d460036070304840b0102068a040c41181019002007241c0203c542012424843c03a9010070060361044400030440c40c914080c040805030b0602484004021914014215003800f4042074804d1441e055070a00c2503c3c0080c0d10b0504d08001011388081121072001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 573265188 1250 573263938 573263959
    0x5150f180f1005030f1005011203080720030a0906020717070b0304050f19021512070c06021b01050a0609270c050d050a0507230d05100606260714090a05 67
    0x100b0366992803207806da0420725401c4c403001203103004a07681c0c2c400103141c01d03554040d2161140401a200c20b00f04103444901d900e28024491481ca0b4100018580751100c4e44c0c41400403441c2040007424244103030068003082c01d1480032a0980b03540014100700f42c600d091111a0b485d250f902c2e055180111081c64041c1c940506450703c91505803440e4007541240c02551801036103c08001c00500f14802c0d6000076014124110120b01514031454090303c5203442141c006191050182d2403c000201e60751410206070f4585040054a02003401070034010042d48000380500414079403242c000e05121104a0513200c100c1894106102c00801440d000b01005040c61042d0320b00c60030410b466090321503056545105400340005c108680c02844c1903540682748001852151082c00c20243e101d100c40181c03094032504d100510408440e118210082c5040c2e02c0c0c64016650241c0e0078810034100f002d40100303d002c491704010401d60050000c1d40e8400030305800341c5e0360b00c83d054000f41308451540c2045800148103103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 573266438 1250 573265188 573265213
    0x4091704060e03010b130e0c03070f05041b17100e010e01140d050607050d0e011103100603050f01030314160516120203030703030207051005150f180f100503 69
    0x10080040d01c00c15a580c0d0381c22034510003450700342d850151005402c2581c6003041d41300e01e2980c3d405954000300701c0c0c080d106464030039800a4680142e03500808500d00c0184000c12840c9000e21402d02d060b008680c00d0311a041e1005000b034024481045110f90800000002400c41041f075500507000c0c11000500401550f115110180b43c2002402842d803002d044218502107480c041c4401c41d4101d6015009000590344c82100300c4a5800964091700300c0d9846017144a0700c88400e00079030841422601c2d249841b4680401d500c04440c0b010f80c000414185000d080c008450070600555054a40500700800002a502e5403010300c1d1040c07102003038094054900c0b90041010218445500000f203012103200f990716038000c2074021040d80300096041c1e00c10416540044d000742c01a0000c1030040050390340c00c005202d8881c059801c00c8819600708800c248641c00c0786c1ca0800310041e64030f841900c0c2c0114029085800f501c0542d40a06206c046035100e8001031451044241c0560141c600501611203582c0d041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 573267688 1250 573266438 573266483
    0x15050d1503060b040b2b0b0103060504050d050c060f0606040306291c0b04030504030506010303091505040605030424020f1c1103070c1703330d0803060409 68
    0x1408200c840d907041502180c03551500780100003850390014400c00d45002c203081051860180d408180403046d50b40100c18000c50640c5003154029400b07048042410700d0285001410700ca800070314141844030601a890a130f41c2c2c0090019404110a1808032060311a2800070308a4025944010040c07410000b003032404507441265a442000020381ca501589841e00401c034601d1101c0e40c10b403104198030746000c1e001c9903220811030307040385c002d003425450f007900ea880701400c00c41e00b600b0980205540580400650030002c004100304201868132908003410080f00524911001e0005401c451150040c0d040a07544842848040050880110768400660442640a4000c0100540b00071112059401c0d00d05c5207024412203100c040c02c056245540707c1030b09403101c820603e000d07200042c0b00d0055554040745800150300401001125002030172800b00f0040c124a204024480f5402d029000444551140400310340fa45500c20f250f240c583d65a240410000c0510300350107001603101c50080d40c08082d14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 573268938 1250 573267688 573267731
    0x1a070c060215010501020c010210050c0c33040c121704060f120507020c01120e073b0c0d020c0712020a0f0302011b02040902040905030d0b15030115050d 67
    0x2220b003220420b81c0e80d8401640ca80000d860b00314056000804d0a000b000183c0c2d11403030340280b145200f00e0401d04410302003072400d0302c1c0c0d55040341d80d84950340c03c1119101c000d03000710300102c010507000d10452a0550350584012414820108052020705104c010016551000d504154051a0a6840d01d41c0c40c1c000500f54400726110802148001019840020850240728454041900100502900840111031038220750074000401030741c1d0790700f1403104442404000d00a213104040d1440d0182217580a45000c16041c11a01d00c010025684c40c440001c07004030319a01c0380c07105802c5516141840354140291003540e80509143c05400004030b0084224140000003600a480d040249600c52041c0c039403c3e2802c2c007020f4013191440d04d111050101c00050300c2495407014201040702000d036404181652007a0301c088a07907400204612210001d58400c811022f8000c40305000070102e924105040713440107001d801054016603018071946401031080b42e44410025508010140c50542280742c4d0052 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 573270188 1250 573268938 573268963
    0x100e0702100f1a010c05061512030f07020a0b0702220612080310080d121d10090b0a060b091003230403140414040911150702040c020303101a070c0602 66
    0x5200c1c00e420895101707a030791544039a0300000800080e200c1310700460300709803c80e8030036034480a00d210f80f83c0039070024409441c0400109403800d8a95900d4410464055015003018003400028002070015a40c0d041800b03560800006810230154540e20300240030f00303d00d411420740e1041c050007910800c44058000c502c5181e968201c0320075203448003c403c0d2105070808030b401c001103181e0b0000101030101c0c0e100c0241a0000c8400321400c003d04040d0301c1c10203502402004000750b43c0c0c09850244010002c4440e0f2054040c0400c01ca02d41c1032918410f1580142201c0074003505c0c0f91300112001e88d0180c1d204004011350f0400c0b482d050b0b030b5001c41290103a00200ca040b0005502401402c800f003da0301c0070780d81560080341414220f1001c01082c000104031410007925001c03d8101601d0581e25800c444044c5100d100011a50ba42820300501080e5024003480740308541c41001000b40b0840a90720003c1924000b101103d03190f00f4400d00d10566000c1c950024040c40380c480e00020b012500003c4070020041c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 573271438 1250 573270188 573270221
    0x2b140607050703020616212a0203160c050409150f0c0f050a1202030a0902030c09070801030209040f06022107141b1e03130905100e0702100f 62
    0x3a0303800c50031501c41c040c4540060160307101c00082040310f01c4214080d001d90700e2a1034840201200783c060b0141003145405444500740e91031081c00c54502200048804181038500d0890201c015424001d660348503000e54006c0a5540002260801418111450003400014030500651541e82001280b00032215404c40c1020320700500c80c031a101140c05561184880b0303449151500448840139078845d030000003000c04102c0e101c0c4034502002324030f10186000d00120040040d40c01e20b503206140c42c04400d501094891440b203400c2010855010640034152035054905811a407a03e2604c0c1c40c803107400f1400205103d0000c1885200c03074852415000702086c1582d80d00c1c80c941c507040702c2601e070401d080c0130000f030219041000282e0404003c3c10032000081c117008807110701041c400000c2070f51000340018803a6810004a01111b1034801070041c01074910450200054100000080e03400b0700c03184641100c0f107600c0c0000604035070082c0803406803034101d80002c2c403100c00c1d030160040040998610225024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 573272688 1250 573271438 573271441
    0x30c04050a0806040203060f180a0507060f02060910090314030a09021e130209011403101403120a0305040804180507081617042102030915070f022b1406 67
    0x11400020518004d0782c014001c3d280a4036007146204048030f008001c00648144d610903400d4258040201008850180b800382c19007600f4071600070454810030110104550001c400c1c84415000400d00503c1c0740d68164000400d6006e520301603405220031044260491b0002c0200102800304d0f80200031414800c64910005200d0307100c521281102203420780c4d400c06003020b1501d08961312940105100801410a82d00042001c40005400c0c0d104032010544d0701a41c110401108400c00c011100400c422805040c1d60700200c5d480504034001c2c0751030101050b0b164000724060150140444014181251030010541c2d0403080303510203401306031862800a001080000e108126420122143d042c0c141d131041603c544039985003070825000b500a5840841c50300d101414000400c40c0140040e406030069501d0b00c01500070400c40901809644040c001d08019040c000303502116400001603040780e451040400002840c4819100302c1d0000c00c83c082d24140c400b0900c030790001400c000040000407960346 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 573273938 1250 573272688 573272699
    0x3010f09061d06010e13110705010605010c08070b070504090e010e07060e060f1b0316050d0c080a1101090204180b061516060b060d0903020607032c03040803030c04050a 74
    0x3a040c0710802d00d080180d1200100704a90301c00c3d203850000c00c0004011703840100122611341c0403101461006c0100c2c0d80c0c00207502c2d082140c00c1c044c860041409003400301c0701c1d5040d500c40a0151080c0e84008090015080002da1410702501c1503901a18110000f004440801d0000b50700a24001003070b0781551003401000a1800c1c45051014154a8041c0c050345c2007142c171080041107a00499420325640c50140c8080d05420300402c042c2440b0150310f440d0b0f450311507050812a044c0703035540800314100301d0100c05040116002000719410040f103031070811140700d402d502a500406642800035482400c01290302801807110701100c00c914040c03180d000d0140c840104104200340c02d03040504400c4018024400d0280b011810b1020301400b40b032010a0f5001c241c000101d581c0d12000c1c0e62000d0503614040e00003855030420450380c2c4500c4c1c6060800c211a655000ea4440300d0111101c050145100854802400c00a0040d50700525010301202d490b402d00781c14644132600301e03000b103074062051010300040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 573275188 1250 573273938 573273959
    0x150f060309012c2a1318112d0108090c090907060315051008060a1a0703090b0901120c090801090809010807021507050d090b131e050714120303010f0906 67
    0x30103818980100483d65414091005ea4155054002069950f480c5240070f500400f00c43d500da01441000c0c00800404072804022201c41d00e43d00220100119484954003215210000b070400c6400b401e01d44020741e5465981c038030300001d00514980049164091000189001680303000b41e03000c1c0d03103042c0540c074141d03c03075121004c5052003800e5002c00080004840d95024034402504000c000c2c04940c8019103807812482c1c049407176000180e080e00001074183c103165001030942e000d0285813030300d1440d0146001c002810408900c010b024626a500000507005001300d00500c0200340c3c0c1e00081c00a41c0c014200030041c4e40204c00180e0124020340002440135101003a40c40fa0200c40e100b40542c02e8a650000f03c403d40c002c03110600c078450f600d0441e0b002080e00d03900000d10800c20708641500031380d039919003c9034844501c40717521a000000710000c0300060000c541e810598006102005404a9400000c0d10b141414203900415000000001c981035042049010030303214510800d00c81c080c0c0d00c081920 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 573276438 1250 573275188 573275233
    0xa03081e01090f021902030702030c010302031311010e041a0a050f030a140c0a150909020c0a0f02060d0203130b07180506090111010c020a0b150f060309012c 69
    0x5800c1280c00e00601c1040d80d59030002489400b100801414040c0800c074040d00c3d10070f19560040541d201190300c200b10321381001090000d54080ca4154210708051800341e00700a500c080040603481c1f00001e00410380d1281d0b090242404008009001819120441c41c484e030740220f02450103440c8001010070b003420b01c01d201085510b8050018a049000c039110342c01000d200440c178840320b024040181e10140e4480e00385401501940205240c001d40f482000b621041c1c40da40884d901e1070045c421aa604200840d001d69515041009940ca68505100180c030600c00c2e01d2030301249510100038400304580305540e502c0035a1088030482c032580c071025001d5030b80a01c100070b03a405480382c42070305201c241230080c0600a00361040c1065600b04030044a02030940b11b00d0350781c60700140d0004100c02c090010281c0081d410028040c070b44c1214080040100307410398540c01d4030b113004084c00000b24204144c254415050031408503400300c0d418600d4a0780c85941034a800d01110315210b03131800403441d03456503140305 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 573277688 1250 573276438 573276481
    0x1e0a090c02061909050a080a0807030b01140a030b0604120309090e030d1d01060305010e07120209070c030c050307080306011205060d030e060c0106181104060912230a0308 75
    0x144083d580f000320503440001c0242c9403c044545a2800302c0010f43e0804c206403c181c86070300c1041d01c40c0c28040d00200300000c020019030416040140b014901d9821005404000405800403a5145515507098029041c1d64005075000310f1b000800192800034540e200aa1a110f540c981030141c0d59028035078140c5001d615914031a4104100c0c000083e41240c0c4004850b15040114a200c0d0024003881821038046500559140e51501010700d01c01005104a1001e8215164400c1e107902d40342e0042440920000d24072014082050740741c000303050103603c444660b103602800700c035510b96641c41d000002d90400d490280c0424104600c20300000f800340a07a030b1054001a00100b1a480e031740c3c50448075041c0301c401c0c00b034021000308002d0500c11403e0084c0350161810b26800e07840c110070003021004641c810345165a001c0c0d410b000503c082503000c8404000c5669402071140d403440309041000307080c0f8403c00001c03400350612080c484002c0c804503914503d240a5129582135a5030803014000307081103103208 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 573278938 1250 573277688 573277693
    0x1020f030406080f040311030a03050403031116060b03010e121305090c030f220c0503160f1e05130f0b03031918030b0f240616050c1e0a090c02 63
    0x1607802c3c8806032800c5c1c2c828001c0c5004c00c00381600000003410342d400f00d1454000252035130104010b050b014001c1086179804d50842600c1c118402c4c0404192400185001f4995503d40c4c040140c1c643c1d0035000301c1d00000340201500d0030039107480c00091255014003404410a0410b140000d80761420f24600e500c680c41484219286640b000117840b1202e000803d525034034044007841071590b084043d088003000e03121b080000c000310300740f404040c42e06107140c100081b4940c80305020f00049925070390100445e600c40112042400940c2c001c2600c3d0035503a001180c01080a154002e44080180c0007511ba00b0082441000041001d00c107154981c81008910040080e0f180c0e0441d4106106281407010306401c50904c076a100d850355629200c002c0d090710fa40c002c1c055104113210f50780000303030f6403042c05604140104401c41c040300701103401400303155030596045444003008010b210045c00301e2140b0309002030045240c10320f1500c101d070164006c040e0320380c00f40803034009c0441c40c28454802e19a01003c5d0b40c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 573280188 1250 573278938 573278941
    0x304020d02060d06090509150609070c030c0305040308031608091507051303060606050910020706021209120601060201050a140c03040b0c04080303130308070c0c06050307031103100501020f03040608 87
    0xb8004140d100c1a0541403103641c031140014990500c2c41458011354440700075050100c107079951080040c801402e2188203030405805c2c00785ca590001080256240d1500f81442c10707c0660034245c40c9400346a2025007801800006c1280ba100f5030408400408400e0b00e03200455150150119501c0340424485000c0b900d81f040070a60301406000601880c5010300c4805801c1503c030303070300e034810343e07110b507000c40c000c1680413507003a90340e01d0310343e49040390100c0314030040000340d103015002950b552910f00050010180014155001c0d240c6010a51103200300c0011035089503540c00009008000441c0d661907070625010454580540c050340450184007040c0c4901d055803903944884c0720400d4007404001c800c1c0001c000018102d0802e20182d071250216250903103041d00c950801414050300104130408102d8003d0a01c07001031034200f00c035030565100340741482d16a9640704042c0c00400704412800e86051020040041e0540442002c3e4151030007a402e80721080886400a56a0f000b14054000801e00120 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 573281438 1250 573280188 573280193
    0x10e090d050d0e0102070c03060b0607050318010309020904140706030c0905210d02010c08060d030203070f0602310803030f1914010303050d0e1b010c0501061e03060b01050304020d 79
    0x2006002900310b0480c0004880388401012422a03100b190102da00c03001200d020014402d851159041804043d07d01c00d1924545660b000e45074450080c50302c201c40113055401c10705074401e5012110445d030148c0503218a0400c1d041c12900e094014407445540d100300c0c000494464031034000c03001d28020030b45076020001d0800042109804c0c045040300e220704000030080e01c2d5400200500c005e16032003a0000030381499103500083c4400001840940221058112040002c2c0e0000c02c4511054010441000c4d290480c90300c40b0292042201000d443c2d03203500760808519103121000903070b95200308080040b481ea5516007940b203002c120b40b0070440e41c8107140050105541e080f00003254914010b40051181d4180d0013260883c0800c0e0415400510301003020707006581c40b80715140d450351040000708144059041055001806c2d40d115604214000002c0300400400350804009000e11100401c4030451a04044400305680d20090f036601e030414590311280c4d4040d00480740a239401400103c00ba00464 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 573282688 1250 573281438 573281447
    0x304050d0203031201061d190b3f130b0402120a20012003030a09050f060106030905060f01060503010b2203261206100908030a020114010e090d 63
    0x2104103030b0b01804104804050b210281901034081c118030303181e1101c55a66440079100a039260002d09001d500b0030074200e9564001c1c0780340c44044400d110036440d5031b862454415070461414600403e407250b40141e69a0083e0507901d0403025181404840b403505940d1420b81001150002ca00500104c2c1190042805400d0848195106c18440002c90f80200030343ea40705503215031074608000c02001380440c101c540d0342c0c0c04060703502c03041e400d0780a801c0440800f601081c3c0f24400903003606074903640c480c1160104081408a10800da4003442034a9a40d0fa582c5005809461100402c03146c500403100026642c1d42c144041d5070588000d952514116803e0108851466029245424010340494060035070805206c07048005507110344041c1c80302403115501c0d10707040389241802c01100c2806001d0018003c0e181ca0b2195803111049852072280289004113443c2000706401c0083c260000084020500340c0540140e0041c508508410840b03a9175800c50900803507042d80c84d071100d038028a005900300c0d88103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 573283938 1250 573282688 573282709
    0x1605100f0225050a0e1b09030106030b090307060e0607050403020108061309052d0318060c070b04150509010219020114130807050f012010050f060f060903030405 71
    0x5801140e00c450003003444011044144040c00011402c8044144954101303d100c840080848400700c5545c1c3c01c05d403240500c000e49110b002c000304180410320f03510b640c0c1d0035005000110303000082403d103410300d140060340342e51103035500341c91107030514006050003840052001c2c8a1041507a42e03034100303030456004652140025001e268041900101d0070700702c80c020720401090911800c0140342c80480420f15007a590150b0f44071090010043c3c14520a591001c42103c0c0050714002355110ba5a0051002520368004d40a400b81e40307115400b00400c003192a0802002507070001e1400e9030781c0505d00e103411121441070799009801a00101031008886980140c220b520310700c1414141d8004d58801450b00c0950000c07400340b541c000420004001030041403110001030b10040e6401000e24000000290050340d04541c101030303004802e03540e04a110300c10f005032003190750301d030310305200508090305521156281901c1127403084001e98810741140ca05501203402c00003000d00a90b060a19043c20082001742 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 573285188 1250 573283938 573283967
    0x2031903112104020102430b0a05070c0905010308070201050c1c031401150804121b0f110a061b060204050d29010e0a020d091b08160510 60
    0x1801d0003052807403200c20010b0000a941c03800210751618290000914001d001101018401c000b10843c1d01c2a0240030345101915072294402c0e582204800d5805d02810440e60201e041c500300071070042001c40c0c0c480020841540148090317101991100f03845011500288001400400d00304603102c01940148090300b402014441521180401482503000b43d6501196020003e5590000503000a55103588a805002800030100d4240c551140107004c00d03101410180500a0011510344420f100d01c4400300584039450440006444600e0240240c00300c03444219051004000000c04904182c078200080b1650b07070383d4440c0304045002101c8c50301d40d0b41e0700c0265000d030340801c0045150b441e115945482c0034814891410700028001c2901c0324040302070440c014518030f0314010001541c46192a6400650146006030341c1c007904e181c01c0c0300030005000000c0200c5c902035081c0204039440b549020840b00b4034404c0c1c2d80c60300e01c526282c000740315031800740f00d51058200d82c244141c144121070807a142d42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 573286438 1250 573285188 573285221
    0x1b0a050412020d0507060e0a0e1003060905330f06090103060222032604060522050315010e0105030d0507061814070303030f050c030f060307090f0209030d02031903 72
    0xe0f82e00c42500340310854001e500030940d030844004035410034001c0c0700010146403040314480d01300441844075000c540c0c800903240b25210652281441002d019500702909032518180b00d9607268030b0382583c08002c20303029080c20429807000540302d0b80509560b5210300c030000c1c451403143c0e0a5070341c2d5100a40080804088130f044124003d20b8055201080d0400b40d070050824106d8100c1e41418005c83c1c0e4424416410403000902c4100201e9070094103a0300203071150b003068082e0207402031281c8071100031030b0310460741071092009a542e2a98003601e054141c50306d90480c10f16583e21001032595078400c0201081c0010130070030028002c104607601c071504440308008800d0080c2200e071100c40362180f0900266480303170040103040007099054070030303050020100396082c4440e00e0500107003055404010103892017201c4100015016680501c0584090088003104100300300d1a42c141c0c000075084a86514000e00c01c0345440400c0d280000140e500c010382044004040f0840600210b01078440b03106c02e121400b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 573287688 1250 573286438 573286459
    0x50403022d03040f14121e100218040b01020111040501031a06040f0f0e01180507021f0c140909010b1c1b020606010e060a0507020120061b0a05041202 66
    0x202810b000400060507801001c0000d1030a00740003110350300719200130b1803245180c100c81d0824064046024406420261401c0200c2185020039a08200c0c1300a2036042107840080c601344001003510b9600d41142301a10200b00c3d0315410001a07080f81c2400c21000ca030a142800100320703039881303504100007401c00002d00c81420603070640824015080364005402d82d4078544007c0c4002c0e0300c900710840c001e01c01c1c0c00303802580e540b418090100c0c640e955a140070300103849100160740c590080294240f1850290140c8801c8101440b20b24010701310a0307131030000158000c90030180c40c1203450503111004002442c500d241d03481c3c07240952240d4001d0704142c00504018451300030010184c071550000d58044031a40c0c0390700303078020002414034100800e50340c14000702084180c81a210710f02540c210284c50b0402c907940740d03024001611800b00c407684190f140d04c10386034000d03c1804045140c4e030140030f50780d10b03c01c1d018400080c04000750089482c1c42d40080c1e0180010031105c030402856402c0d06d4005004003512 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 573288938 1250 573287688 573287773
    0xb0409020409050f0609070b040302061617091002011109012006010608010e011203090302040e0705060c03090103110c0607180b0315010206070309031407110d0b06040f05040302 78
    0x980b510610250741580121400c121340c0d0805019455101e2010000781c0a031030705002030f8a816000e140030280c014000401c0c400d80c0c2d581450421190030350048580d80900b00e108503007142d29401102024011084140b41c0840b42e4014010840e03840c41c19040c1509082494004460410704000303d0b4106d100400d1500081e01011700102c0d0180046a40d185400e40c100b0070903180d400010381c85245142401c2c102400426808072200c1c060380d50444010170300450344480d181c40c00916801c0140c1c00000007412001100001000701000710080e02c00340105400b0302d41d0b00499015070156070f14540c01000000d80694400c6800801110250b005609110f465950101c402c1e0021104010080c0700690720445c25a01082490351050341450b040c46590a280e900425240005503031362400140405c006080141c8000c0340050040c001e44840401205802c000400c8042522658011440d01c219001703208041d0080380d2003150540c0003404600f8040f5158508054446e21000b0728a4001c10f40514 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 573290188 1250 573288938 573288941
    0x503010c050406171f060c0501050708091c020f0304060504031401090c030f020307091404110603061008131403030f0a05100e0403030b1f0801050a140d030e1507062d0b04090204 78
    0x3d00b13050340d100c01f400c409600d409070031140c010301210f080c0400501040842040003d4280846c0382e02406249800756144069192180040c08846c06001c0480e0109100d980302015004680c065807001007041040c0074500d01300c4131004006005800e01e640d09001096150840104c1e5502c007900702c41e007803036484c00180101c42850f1800c421900c024820f200c280080316000d48201e034001c50341f07545541030800010341001c2511a0b50818000c0c040000b03107202c0c00100500c00d042e500b040302028102280907006849610413210003100d400204003003010740c00035116075032041e0303c005180c3d4011420451002400c0400610440405442e41d420f06929111140d00c8043d011441c2e8040219a040402c0a003021405800c80f50150300071071001c000b40d071030b0304034001c0140b07405840340d0504051504040781c4607005400f000d80c000040003500120701c20580000c0c10361900039035081200455903100441400700510000c0d107241d004070000e0407094507a40c40700080047c002c00018810078141c0c0030a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 573291438 1250 573290188 573290251
    0x40b071214070f050f0111030703090f081908090c011b2a090c031401060c150c050316110c132307031404051b010504090f060503010c05040617 63
    0x101c1180003d6622810480c00304071103100799820500078402e002d2512000741445c04003c2c08035003095111180c6a0502c100e84e02d0030303030106801c03014040da9000078041d86140d070b00340201c42000240c0840005006150301149001194405950b8020000040402c0c404011501101a41d440701c890600c100c14520300b00e080451f01300c08400391000380389031074141412206003a2402051506004c00300082500803089207066910600302007001d02e4050500c0121121685006e006840c07920310242c0005d070300103014510546c042c150030016643c444600704d0340162031101c594131960141200343c00c2490014071504850380440d00c001048a200803036070881a0305403011182d50b01c0b01000f889800d079414050f50075030341c071980c401c0503560915945203641d4185041103540c603c8803031012600980c0c07283d021503005010040c000d00002c03441d008148001d24003842918841d620700300c00000100e008509880072101251515020207020201c100d40e00d11740208840c0a4941541c10062580304c40030703540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 573292688 1250 573291438 573291443
    0x8010504020310080609011e09030504170a080f030a0c0912170c0706111501080a03140f0c06090c010306081e0304030602070b0a0e0102040e04110a0302030105010b1e040b07121407 79
    0x100d103604d05428a400d4423503020b400c4050a03814101c40c1070100390000121003c9441c889031403400c90f2170b64100c2a0504200400050007400e00240c40c800400d000307405940140c010400030850185c0141050364040418070400e102002007030200d9011880052001c5801d0203031040c0c25240149080d080350601c1481e070130490119106458219409004010707004401c0f04506800609505000a07640d03160030f01780d001070410000078040c8001100700800c0c0c07000e03400414011511014610b5509490742001c1319010070901c14003914041325071003805020100c500f12409030070a04200e4003009142003082500ca121840304010000001e2000d20042007024001c819290b843d0411a001c0815207500350b8000400740c0c010312041c010040c0003070510b50041e13401511100490310480c0415140d070056031010350f065182c01c00008008590b20001d10056003003529001c04030342a542010228010341c080c00050b214240410b1001518403500e4114590060234440c200d02045e80b03a404240d403188208 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 573293938 1250 573292688 573292691
    0xc060406170a020406020a17120f0103030f0215060d2103141311010c0201030b031e24010b03060121020901121a1903020d0501021b0d0801050402031008060901 70
    0x800076800000c0035054210108100543c40d092901c0e40007550f03500da111000c1c0c51492201c04041d80c5441c010122070f900c5a20810070119454807140b556030086092109070089642040008210383c130100700d504c429000403084440b07548440d02405080080d06070100d504d8105501940c40d4800707861903c42c10303e00f099401150303000000e504181c00541c0a043c034000d650034200420001a004a400e0031f03200002e20b07040000c50710600049000e0720100040340c1d0103018143c4092584441740b44080d000c01c0703500d8211003468803a40410000007440d46500c0b4142c4d2100401030046e200070000650b08003c1c145490160300d203600300d00220590802c102810841d40c0002d40c1d103060350300078549840070480e0160401100c425806044440b201c141c914030705c204440c448041d8002c0c044460031020710b03001351408100707030181e2405a000b54442420410083c9012101300b0502000190b55600c01c03205c0e82d14044280d1030f180c244006901301508150a031707081008046513011003000748922a4900c4d000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 573295188 1250 573293938 573293957
    0x120d030b06072001200d020c0609030601050907020a1a0118060b030a0509100207050606150406050706020705031e1e180f04020903030f0d060603021603030209030c060406 75
    0x140480e1103198409001d01814002c24000c924000d40100d80e07281400c88a5420030448001218103d00c40790785817801000300e099600c410403000405071052001502202c6c0d58080042c200070b1940503213500c0c542e2590110300140080e0070035059041d00f1a1280c01105d45003401a500c800c560f00d04210b11109030559400104461051000c0301c0803949a0361804002c82d50600400380035030b00c4000c0c12001490344030004241d040e4810040e03c1010307603011000310340750341e01481c10f00d031942d10907120b1f41d1182020000301c51712401070f0000c440c1142d00340c0d100c1514041450341d0384806500090380a9950707020a212642904801c0d4003120704080b242c0d10095900c40102d4250510000e600340c181e40d8220f000c0c040070180d01400d038480040007400b280c414042071076440024000e8485d60b22855054040880d64800d00c0071014080c02284804000a01481381c81d200c0071000c034001c105094100d15021324490340800c0c080d43c01444550310107802e68105038809000302d2510751180c1c3c00070000425208 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 573296438 1250 573295188 573295213
    0x120f022209090c030605180709021803030903150a0b0a0605250b1909120206010f0602061003030806060720044a060103210c021f09030212 61
    0xc0d140e80241401034010003182d50b00e03031202c140d01c2c01c41d40402020310340c0c0c80300072494451707805240c0451483c4400c02c503200d40d900c0b00c548001175000340403c031280c0f030303468050340d20301e8a40402a900e0091014006004500c6250307210504224064003060805a07902d4240c84207031501c58041c0080d08035600c1d0703507681c1e41d4424000b01d110f44564030305c00601d40281650000081184007210b812685590a950140c03100b014008000c100b00c002c02880d1404000d51642080e80108809040f254036142d018030f180d65808003680c480030219140309086e60641418000207005120743d541020000c0d1805013000d0b515a0744141c41d407040c10342001003003000c00000b10030b8035203406400c41c03604000c6110341201d0009030f0605119440601c0603288a000c4031502d50300c1d451910a41c2d58441d105a00f12042941c0d2070401030b44070f0340a55401e403007100038081580000c2c1d0051080b9200283e01a02c4603501d440c0c109640ea200da08000028420021f00c1c4c20700002698500781c400889210380c5000e8185c0e01104c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 573297688 1250 573296438 573296497
    0xb0a0203190309020f041a0306040632010603110912100509030a0909050a021912050f0c0a0c050102130f080607080108060408160b0103060207050606061306120f02 72
    0x41d01641d0806041102000042e1124201d01958070010b440c04036017204690651900b84408414403505031051000b084140400786c3c01250000e4000c000d0000a6806040c1c404000008020449404c0c64039400401c4800d100c0d03808404030310b284211013410f20749440001401310381080035060f09075001204c80c50607c6441d05c26140c019003180e00a45c90010048400751600b4180e1003030003d4980c2e2480081c1c4854205c0d0121002e00344103140000c10001c103060081c0c00e0f6600c4200c00e007020751070f00c2c00040036100064201d60083c0119102d040c1400340300f0308101c3e20601c8045d13003140c49540a10040e0075280320702051902804000c1100200d540c20041c41d546800001458030b4100158600100000d000105820360815009014a551460990036507400191202e200800c80280d6000020034000d0903806030002c54801c0c002e803035481e1104000c05c07070103000350760005004048000c02004540c4c010f0103403031021940700c180030502c1000c01c1c0c0000100c0c0c01c0b280015422501200803400484080c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 573298938 1250 573297688 573297727
    0xc030706030b0a140d1208041e030e060d0609050705090301150620070503150712051506130b041d090303010f171024050306090d0f090b0a0203 63
    0x6807074100650110780d03002a4194020303104041004110b4011101c1d00c1d10707001088410702d070304a602c0c968409403e0030003c011080031107040c1d401f4540511a0910004601100040590107944044420b1805000c00003140c0c00302501c48070403695000001080700301801003e200e0382c240d44038541c49007481d1043c1030079624020782c0041110107a20080c82600d41080307420280403050311400307880e8900300030840c2c601446074011a501d81700385140e107840f010800f40301604c0b5110642c2c0d440c4481204105d0300e02694400e95440c080f447c1454103046850514401078040c1c2c4051000b00c0c0c01172031b41c81c0c4c401e804a074000e07081a03010340b0042c0310826801450060040e000700c0840021455589401e00c604607803030f8680106900c0c0010380d4000344400c20200840d82e44941400c00410000001e101c8901140c1510f414103da020340e01040000c0c0c5107404240710b8451000340020380003003d00c540701110540d0042c00e6850074860f03d0100811144030a4010340b07100246a002542d842e500068425400580b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 573300188 1250 573298938 573298949
    0x608180a0b090f070e010605030405030c010f0903030b04230910141b041a1813060503010e03040612150b0c0d021908070f06022101031e02012c0406080c0307 69
    0x41090200142002d070040d01b41110030314038215450b40c40f075240c1356080d845200700142a66003440c402903200011940000c20140c03081e01c00b00700c4800a0403d000c150360121460030742d40150404d103c9001c003203000001c1c1c2c1c481c00540030b44118070b41e12202c03c0308071220301d11b1019991460301300f00051412031908001002506c90b04050605250138a20454409109111148401c0102e0360740007815000d00c0b02b21560000a003c03203c04205100482c000b003020f407040511135820240031159101020089909542807076841c0c19400e807003040ca02000d011460101515804440b0002507105003443c0501403640c0340c9005840d81d0075002000074504440991032000000d9082c001c1301c0041c1d100822a00155842a50383c00e00e240345040800090041c109900000c00300b180c1c88494548455242074141d070b1003105441e5409091802c039401c2000c1e1440002d01250150f01c82c002408802d0000a20340304101c0906c04900b1244c102107030a80701ba03030f48410410790000180510601d424003041001d042c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 573301438 1250 573300188 573300193
    0x30506040b130b060c071d0a0b0901060e04061809030e120c010539010c0207050a0e1b0c010b0109080a0804030b0408071b05122b14070803100f0503070608180a0b090f 73
    0x1441c9ca000403844a01845084144800040301160a0f02d464101c4001060340d4020300302ea11700f550140502a00319217004900041154000b112180b6180d0b200d100a5810130700141000341c2200d0054800d54000210141299495011640e0382c0b01551150f00907413201c0c107600740040364100c0030242500d910510f004150340101d0300030b00150300c643c0d07422401c9421750640d83c0b0b2151110701c006580e003090070310390344844640001d0000d404081500100d4030104207076107103545207a40b00940c541702d4001c440018442d21080104001146c1c544098641060099528074a8000740c0d0303440c28030170034003c0121542800040301c01c0280e031070034000703100c0c8031280880a00010041400041205480d04211400d400302030700740c401c00c00e4840c00f0300030340c40402c038011581e844425007402c091a03042220401510b0395415801310702c181d51003807103004171000900107213202810200290341103580100761000b010398862243e41c00400411501c0700085c06a02e41c48041c3c181810038506001c3d802c6201003495 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 573302688 1250 573301438 573301451
    0xf0b040b0a030513060c050c07082817040608061008060102100c030e100204031e080409110d09110306010902070209040f0c121101030506040b130b060c071d0a 70
    0x1119100d00701c480300c4880d8a00050b241c2d8520208125400d0312901c080c104d145003c4c481e800213600719005015042000c801c554209541e0582150b84520441103144100c402c6d000f01d28002500c0341c0e079184144d02c07909075034490003c002c1324245560415440240000c0550342485064140b049189a001c901407400c0d40c0039141c40360010395240190242e07102c80507a2a500d54940c0c5120742d20a0b14010f10000c20744203c020402c4800b806504180402e43d00885000e400114050b16407000500e40da501101c091f08080c5032603842001401149070b0b4580c1d16004200310205840b5511861075407130300c50301c1404c00078050541410701d40311058100021007807041001c0e20150790ba4504450b071055200c000c1a04210051405554000c1c140d0320002c0c5400700d50306010104070b001682d05072810300a907001c20844d50b61070204419038444224050b001081c1d51604410301000750404013551a0103440030349007035103d541092610320356a00401d0072010a01d403c807101f4402400058020600d500c007884413 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 573303938 1250 573302688 573302699
    0x3090e1608040510020a02031c090b0103030c050102190c05061b071728020f0703080d0f0b060f0406020c0f0a2d15021515040213080a05070f0b04 64
    0xa6403032094a903080c8400c1000040030442c081204c0c090f4078408035000d544a85048402030b540740c00c11745a4008000011080010b050040d10611600d01e1700f042d5035100a928544041d109026100016511550208071107020240350001510b14031200d03a13203010300704000d41041030610701d014007415408042c00140c0c806e440c69200950b88a03a811003600d0b00b605000000107030480c0701d60603d4100f07540c0000c4080320b8103c00d03038581120740c41c080d03000d0f616243c0348007201d03680761821400009d2404606100c0340e000c01070f090384402d22040900070f00182e0541d400e03000074070340d8105103800203815038001001d00000780e05201103140f59009807400d4000c2c10341d040005045600b94019101c403614000b200b520f01c48001a0b8280c1c046120b001c1070300d40e05d03440d036049055040c890802640988504044800185003a481d5039100c1c0003072412a8010690840070413002e980264180b44035400b420720003055180061105180750791207000100f50326441c00050340d1000b142c2c2d5000c0c1070b90b031500344800c015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 573305188 1250 573303938 573303961
    0x30819030b1003020d090203071e1418070201090506040b2403033a09020a0e06030601140d0b0f06100c0b0f04060e0a0b01030308240f03121603090e 65
    0x4002c1040c10056185d0208201c010020448148041d6061055000000d03030242c40b410b0a08241c0386060ba071541090b07c40816040d82c0c6031b084000760700051080f2a14460340010000c10f07812411b00c2c8004500203109841e194548502602d09503400002601440317407840c1c2c0148203080f000d9603520224030100317190000a031240103440c403640c4c2d500e22113007a0500b650343c0c0e03481110168000e6081c4850000c0e0a01440d0000e0003110700480c0209000000030800707241e40c20320203200c0c0030011300400c0c250b8201030341501c20140384c444036500081d04d0401a40001c449000b01c5114100e0b00188900c149800d004106074041e420b0119810300200c0085840071039036141265502001c0900424469255850700800820807035800c101c04c0e0182e101c3c100300f001030741a8198101e902035554480a911101099201d08888070b2403080200d109040c20203040c00c0000c002c204881303005090701c880b0380c041130020103540d0140c190115405491500c05c003c06800c10b8005010f0224100142d94a10f0059503244 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 573306438 1250 573305188 573305209
    0x10212030604020703090b0a1101110304021311040503100b03070f0e0c03100906060c02010806060f16080909010f0602120316080a090204020c03090405011d0c03090304050a030819030b 81
    0x5001c2c0350005800d43c02d060140d410302c0000c2451a20503a038860512100400e0b0a9a10502c0b490550915184040c1443c1d00b03000c3e68000d94008201381d80d15210b146003040105030040103031003003c205005c0000c40341d40c18458080e030b6610030789010845220705006c05040c80015000f400a401d0710030801c0c04160100228142c0c09031140070055501c0e107030368012180000305540005c506505290380401c00d60381c08441003040d0b42c401e0320307048000c0d11204104040c600404800c4601c80400f4400f501499201303410b10420940a0069149480c1c2a100424070400007608030fa0050385541c3c3c01003098503410804e031007079880b000310b2450850a01c2000a00c3c01c059820806007000f5500c0c01007040700e80039900c000305440d0b004001315038071408042440d4403a00800f0741e0710700c901c0c82c10700001003c05100c005d6070780f60101b201840203196520000688e00b60800b070301490542c8001e10021a5039103a0540040185020340c002a8852607208000c2c0c907185900114081018202002e00b0199102c000212 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 573307688 1250 573306438 573306451
    0x1050604110f130509010b0c010c0c030f03200705060106110109020d021011070906140a031e080403060504081806090f1c06051f0f08031206060f03040302150601021203 74
    0xd80c1c841d50f01260000358001a0001035101d140b0b50000100c0c0c01c140d20040030300e0001d040092024001c502c00c26142c8640400000d40480e20300000d001003c1d10079408a2018443d182100004050103064101e5981107424201c80a50000005014807500050200c5c8601380c1d1100a21a203062035010510386658520024025419103521074a480d0207101401c1400c00a64201d038505a520415030018140c684a0540da051903d03400031800c0c14100f902c00141c2e9000000001c80328079641c0c0381c041030aa11101a2131101c403e002c0440000d81742c0c0500c50080d8020710241d5120300541c51201c00c41403401a183c1e11681c810001103c03961681a01c84e040c4490072034080742ca002444140e211213030018040104014600410230144a14084ca00f02002080a960b0706140c0d80f00d12402c8a510280d0203419521b9205000c0d00f0000c900804001d68403d02c042c0495081c14031121030042d5076003050b5011000b507044070a2008100031090034890b8840230920003040d124000342c060f50b0840c840580315 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 573308938 1250 573307688 573307717
    0x3080108030a17040f1e0c0807030f080c010b0a0612050f0433020d090c060314010911160602270604030b0402060c0d020703050615012a0204150302030105060411 71
    0x9400d001035040f86501d001d03046106c400e00108040140d2205404070310044605c002511800705c2c0344900000e401003502d0384006694910304c417603250804260802d020321441592200410303146a1522082d90303004080c80c0c2c9850914100021120060ba038008145a001040c400104004a00750003007440c02000c26024160004190803d0b0400004690445a02d0345000140c508401d1100350311052046000e41000103c641d1580d5044060340c41c2d054224046283e21001030164913003640c0309040340c005100c981803410042d204a0700400b49100819a012035020640b00c1c4490a12210b802140300c0f100d40c141c43c54246c4200080003400b5500000d4054203000c80024115110310741240c0d008450311003101c0c0c0340d81010000070342d101c0441c0001c903402c0c0150750120328002004202500710500c142c5500805038203040c4019501000d89880c04d015910060310a80561543d03c6480b222410f00a2130000003410f50041c1070a550300649454026031501c00454a01d42c1248142c810000303a4a01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 573310188 1250 573308938 573308941
    0x13060302160b10140d080a20010f0f051501020316060e0304091e0213181508010c0201060e06060304110a0e15040f0c0206010504110409061203080108030a17 69
    0x700c103007840081e40101521210b00500c00c0c00070350701016100702d800c50320301d85030140084003d111080005040040c181c0409002c81444d0b140101000e5900c41003400b0021b02c0c00d20f01c44800ca0941d807010075000741441e0b48002c10b990048032030090540c001c114800b0300700c1c900300f4840000e40c2c1c2c0c40350a80001034030341c2c90b0703101c1c20070082541c220044a0382d200c4110f0b40c07601d072030f015502c00416900040b6400305500307000300b212140c054000c1e13807403200504170008002460301d018410326048e00d83c040c6100381d41d111711000c0c40107092250100a003412200009405440600213800c480c41030b0001d580c405141c0c1c0411020380d940300c04895000f503000d8181400b0204c80d070b000c2102c0c403000b0f03004510385030366213404c001d00070400c580c0c4182c40d040210b4003807010b0071a4002100032a0b00640c81480140c016000601803070401d900410700742d484801d09a890143e0350a45603048582ca80c100829000b14181440245503000c0b041c1c0d0301400c00d501c00345140c41e41014020740305d00c011595440d02500d9060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 573311438 1250 573310188 573310207
    0x60209030a0f06050f071805150f0a031d1b040e010902090c03040c05040c081602101409010f152112120f0606020312060a12030215060613060302 64
    0x111806109070302c008103544014003072400304007402c02150200d010002040004040c02d220b11100302a01120300100701181341444240150f00a503440c807640452410030985001c8003e0900400d1340314400d0b80d0000d01c800124500d0702c0030f010b407c8540e04440e40329150b0300740109491620340f5401c00c01180d00081564080d294103000d041a01400b0f035010700301c44100802c2c211071b0b2004521135442444103c41194840b020441183c07041100e51002484c0c0f003000407000e65103981039541005031801140c2040900c050300501713440c0c800785028a801603074030500c03c039100240035840360508405001d205010018850b401126000d01c40c1041201d40901c4c82c3c03150701303450814081100d8001810310139161402034047c249451210003002100c0c584020149000f415100c0c03241070f51003980c0a5440c003445082d94051041d0701030000f6502102c5000002524040c0c3ea100400c2c04d071091300588244981c0303000014091b03030000c6c803481c050102042848440500601c8840c141c1da42410011303119103088 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 573312688 1250 573311438 573311443
    0x6050307020d181a0d0501150e09070c02031002070201080f0609060d0c0e07090305100e061503011d010b13061809030203090d080405030f2b14160c06020a0201020a06020903 76
    0xa42c8103554850719880944c021580c103000404600400f45018402ca907643d106ca4072101811064130400100402405560741c13400300070a640181882c0751010321000ca40e00000d00b00201d5801c041c0c6032a83c006000c50455030032202d00c980c428803000781c4000902c0d2400101e090014004e02c40740c800c1c1031002c40c840400c01c8410b0340350003034500035450000601d080c3c3e0029100c0d6a00e13000540f6603102d540c807280d00b521070600420840f0303402784014101d15200c0031400c41500c0d500301c4245602d03540707500071400f000c02120b00404035210100f001043d00388011040c46104140e00d044030a40c00e00b008003e1010303200c50090120040e071503801c00503050489080490550184100e0070341d00910440004c1d00b4402e03050080c000388c0354102c054400003429506010341d20003038800603440400855030040700160000196640c880b015050106044000440c56100c81c2d11814221a1804030144403400348132044a051f400303400385000900c1309440720b0b00040c0d0789000c140750052a107a0005903929103030b00c0a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 573313938 1250 573312688 573312737
    0x6050f120412082505131d1509040f02010e04060e07090302130c080a09050a1b0e240f1c050102120601090b04120c030206030c07020a06050307020d 65
    0x4804840030903090519214048071030030b60402d000a5060800318800c440030055494032030802001d07491103503610306002d9078103401070014403152000202d000900c021b903160040850214885a80c0b810313141080c0010507514200c0700c80e0380105881410440050007070a456005940c090070b00d21000d8642000050282045400c600032602211050182c640d030083c060303000340e038402c035414003c1a5510100f9801c03101d055000c040080d1614011031102c0d80568018883e25004409854581070541c9490420811950704100b18041301c82040114044420b0126085814480612040c01290480e0001810b1602a01d84030310b0b07111520201c582d641b41a409988883c01c402c1d1440c0601604046000750000d40328410301c02d103460001015580716038241015681c3c41e40402e030405041003002d11a10690038001ca5240380c4080c4040090b9032000c1c0074500c924800b40ea00340e40d40760320f40705003c4094039540c0240f0a01c501441440300041d0041440014600c681c40c1600144002c48c0718071a0b806d68 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 573315188 1250 573313938 573313957
    0x60216080406020d020d02030a020a0209100f17071401050f0c0f06190b0a0312050d021213050f07210f1b1e0e270714040c09080706050f 60
    0xc00038000403219004100024082c10a409465080081d280c00342c1c2c90784107140c80d003070058111031030000c010b02e00700b540c558003d80c1c2070b542c05081d1601c0fa22441c1c40c5c6686034221400000a40111a41814080225401070044640c1c07800001e000d200c000307009070060203000c05401c1000701e09054503d0b020031810414403036403c00c40c0d90350700b00044102e14041c1c0045070500c45c141001c0040b922810101e0188044a0b807000011518108028048410f9000041d10f40086a0200101a1140d8050005034001c02070280840114225490032038034084041603181e010741c100c4d02c02080005007400010400c41c12520804007100d502c0c1c41c3c103094594a07400700070302d40c40104650814141178581c2c20f0040d20801080180a0707250141d2400b010310042c460700814101c01c1c00024104581640c43c10103641d070010814500001c0d442c0e1040c180407084c0c00821022624110041c3c451a25010340d03507090340c89040c6080482e05180d600ca4489502e4001d00b130178040c00254000c04501840101c55000b403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 573316438 1250 573315188 573315203
    0x1807060914210106030305030711070506040510021c0f03050f090a0809040609050f01090513120c02150307080405120a0c0227040f0204060e130308070e04020a03060510110307060216 80
    0x646070700d0f01410030303041500c690b030004207240350351000305034001003d10070f0312001031295007450300cfe0608001c0c04611400e45001103026242111096001120450090301000d403920104280d45420040c2110b20042c200708840b03a010007484050440032074400b4000d90001e5944d070317590344020701080245c81c0951280c9003062625003044511680b10b14081d050b66080082881141c4030718403034035054610100060b00082c0100c4a07049903500900a80443c1c501c00352206664821075818240107800c11108000801c01c0c1808200400c48140045006031559030321b41810f000c0d4040009100d1200203d000303002d10070a10107c03001400090603001caa96084013000359a10b0300349820800d2200e85201280120f08040707000caa645200070945200340e0038500800007910054504a40030000a070090b414400c4100d403a101c95150b500050054080f581c46c040303000d918000511a00c0000c800000c81000521401d50760f2429000c400c980c04940c00c00340141e2940456680d010346542c25000040010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 573317688 1250 573316438 573316451
    0x111071a09040b090601120218180414010c090521033f0c0a030605120a05120702010c03110f01060f0510031b120905010518070609142101 61
    0x200200340149001070342034a003444550403810600040c0030302a15001e02159031f14402081481055000d0030301ca0b441500861070600d021804160040c0c0c0c0c01ca0f640c0c2c1f01c4000d0004101c14002c800028070b444002c020003c000c000c2603004018207146450003000e04c140c4a02c114000602000c0c1403a44000e1210029207503910b44040001c01854903440c030014002c200441c90250442e0482d04c0d01185041749805010743c2d543c1d88100e29200d512841e004c0703041c55a585030105107511b40b64100c040c05201c0350028000d419141c02c0c000e01e80814074403000410303c000c02c600030060f607104801c5061180e02d070a204c000c201050359402e08000d02140036594a41c600f0000107100d400c1c40c03002000b155401c0e80d00050101400000300d01350b0310350102c03c20748920b02002240c8680d11400441c1d58074685824006284091903441c1821f40c0e10558411b44243e004032a0303e00c004105000c000c00818031424450180e502d000c059114480e0710903165885a08005014201c10000041110301e659041c1d0081019 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 573318938 1250 573317688 573317729
    0x20c04110901021e19051f0f0612120309030207080a0b0a050601021b0f030709090602090102060906090a061107051e1002041a09010903080403030206061504060e011107 74
    0xe4000415070360051241014064001c207114011450010a00003d84012a031807020880d90811000040702c03c0d20404151622400a00c130100040402000e400f094040c03080c42c40509a44664100c100500402e501c4070001034100704005500c040d040c02c0204480045080580c140780460703101d05180c1c05440c1216080110f01030400b8403a00e1a10b07402c1156445e0100120b98400558040c0548000034050f038808a26280040000d5500001c0803038080c140c95015404c1a211b03100320844103e40c0209801e40b596070107104003a4004644801810a417525011340d55030b9030403200c006028280ea9441e4481048100012102021f1b0081c00b240c124124203245c8800325a001e040c0d001c4e06000301c0c454440403e1541c000c0f24222214003c83c04e01524500d1000003480d031140c480d0b40d0610041306000000a44024050802113029401038213852400354244016a00e4816148110f40300801c018812240c10000000f141c0c03800303103415070b182400d4840c040d03d04403454010050180282000584 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 573320188 1250 573318938 573318971
    0x6040303050a0f060302030c0405100f0605131d0f0c04030b071d09280204030212061b0301030f060c27060225061b021503010e060312090d03020c04 65
    0x10ba08600c10800c800c200c1180c081085410700d000003585030b0000c80000c00c092616400654000000e1050f4400c0290745a01c0d010a14859074001c10100340b01058450220002010b001d0082840f0300350750034080d5501c641c4046c40c0b6001804480060300742e1002c1100305285109540180d540312402e00580c1c108401c010306400b80310500f00c1c106803180b00f40aa03040c141482400d0181c0040e500307000c981c1c1c01216841a901100e101d0940301c180d402e20002000d65101600383c2000b0502d94040c3ca04c03401e08160205009040c1d00217000011020801000000c08000782c080000f038208070b001946020707440045884000d0402000090324008882440c01c11720501e0744401c9441036021a6070b402d100d030141c403508142600151003001c42c0745808004040c0501c030240102985c400104420f0307a5550f00103140d520706003151200300e20000c0010b01c844d910000520390004411001440d000030780c440060407030b01ca000c10ba107004001c440d22020825008010a810300c180c001d10510018006c01c2141c3ea = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 573321438 1250 573320188 573320191
    0x210204051903031407030e0d060504030f031b0809010b0a081c022409030d020c0102031819150e0f0c031504051513080c0d0f1103040509180604030305 66
    0xd2040740c002840300d151a039203104141c00c8a500d911610301011034411044116004404264180030f819641c8562640e42d0303244c85c2c80700c82e00c64403002855003000d00f030042030240714180040a2502d840500060032690034034003a056031192900400359941c2d91b403c980503005d0034003110f07040030600300042620040070524910140c1d90009038040701e01c2d0184101c0e51038a41142688090000c2c0340c0c5038840e10b00034040141d0009002d03045030318200c1404008400c0364080512000c842c0d41c084140200180180c10707004030314000400911124036110025444c0720310400d001030898156034a02c0381805140d0f00700c26005904c07041990a40411807141548842b80075040a00c02d00035540b40e940d0724450600a41c0c080c0741c220b8020f1207101030f840000081560b000d0684000c14600750b01580015207444010420701205101514008400c1e14000d0201d01580702c8036401d20140c2c480c00b241d010710000a64044580071100c030301a503110a80004420b42400e40c24400d40e0054030108424550503070004d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 573322688 1250 573321438 573321449
    0x70219140f0c090a1406040e0a0506131101050306010215060103110d05060406090e060c0306041b18060305090d08100b0a170c04050f0402090414130203010609050c0403080a210204 79
    0x103d4655844088420031101c580d519840b40034406400b00781a41800e0b4094082141c0719011540c0041607a21003c9c41c09800319100c0780b80c8808240d041d401c01400034101900688203090050441c20204000307929056a101801103500c00360000480582c802c1e0441c541e8401601029a51000001c1110000d01021610180568248038001030411624801d0404c8414107101030040c6880f030304d1110f13030107030700c003502003030340039131548800314512440d06280e03a020600d86e221509502280700d0564511401507000c0c0081c1442c03c0e0070800c0b4a040442c85006032490741c03800c200c5690755034010004203441390308400400400401c501c5100307a00709496008010415020599603590300703201c1c40c842e200c3c6008854002c080c3c1c11250700070b420290050039203240020404680f085414030f0981e800c050031035083c04001c03a503241090550400307200740c01c050020004207114525010900a4171b920551000034214440040c17000e200d503203c1c4040e551020788240300c0513411080030626402a41050282 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 573323938 1250 573322688 573322699
    0x405090109141e0c030a0b090709060b09010f0305090705100512090105010f09091121010e0607030c092d0f090603110607171308060a0c0314070219140f0c 68
    0x1040d083c1003000860001600c001001032902c0921913076004111140174250200c1413142c00000b2440071898080e0b00081c0c0031003001141c49401d40000100700918400d00c20003898903040c1800325403000855424190b80c1c05444c207012100c1080310858403403254800019001c0c551a0078016650010341000e41210105800841c00340e441c1c881e800c1c00ca0f070340e20800070601c540507404000581880300c144078854030300b24468041126108101401d4813038090000103503400490800c07000e6a014480c4121031f0f03d40c0c1c80c0c8041c05504122050824407031300c0001031900405901c0d24041549103e010001a002c4d90010801701941c400c6840050300c214001141c0d09806400d6007001410040295001c0a801c0b08103030a07008200c0c3d0100d0010390246207588400c2080f417401003510f40c81000b00070300800c4582800261040211801422510300c0080803032108081c10501420650004104011048110825034804000e150280d00c5840d80304c801d02a0340220441d0400070f10300403901884826040e03d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 573325188 1250 573323938 573323983
    0xa0c03050603120a031a18100902040e1308090a03030e03210d09050316030207210206120601180e18120f0c0a0b10031505060906040509010914 63
    0xc05440710f14800020710411000d00010f2000c9119801c04602100c008030100da1a075001c0d004100b840000c0030300101c694030380c03805000c80c0c0b28040c403500b0002c2480f502e00310b0809080080c0d204010001806014102041040304800c4c09010021100c2e444e60040c05401003ea90389806001c035002524400e119005520703d4500407250401d0814a21100d05401e0b4900842260b4601c002c0810040645e201d01c400c2c004046010003100c4500b44041c020f400400c07a1516004bc42005200d2105541c010b02d80c0c08840100180c9804042e5035000c400c00c0b400015554404004030b60f24101b10382900740410880000060605003045083d001d009400400c5040c444807086541d0346c0ca44403440541e200c501001101c007a66080342c00341000b41c1280c8103032011002e86840340000042c00b80e80d0440b815162030303c03c00402c14110a84c0c4002d00b00c141c0700f80541e03d0000002140c200004080502403a240c03400500c044800b036121801560b4800154000301c016a4101c1d5030f56a801c1300003c03c4c00c00b120741d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 573326438 1250 573325188 573325201
    0x2210f010606030c0c02191509050a0f050a060c0f170c010506031c0f050f030a060f080c030303130213050c030712090c03020103020f0c031c140609041101050f030a0c0305 75
    0x107800404601c3e0b842e50f004541d0305600780301281d02d90541d25449540221400f24007401014100c41080c1442d55400030f89c241440c04100c640e680540c08040207601c4003208001da501e5161020045401d80c1c00c100000300b2003400c09502034000c00d04010540400c1c403040f60194445000644244078a1500070001e50352180306040c0d88990040240300015840300160200351b01c40c00b0003203062075040c41c121b4148490103200e080260400d490b10414107460f2003091141034600c1e0800c0004100300c0c001030850002100c0803075180c2c80054a1041c2ca80c0d141400c2009546501403a83d4410900b841d040100b4900004050b200e0380080e201c29000940844100242903c1801440ca009420000d6541c1031860750380150000d501c44034034050006024040c0503080c8500f400640a0841c8007110000d0003214662418101d454000820b402c0d0309002c014090b083d00e649130841c0d81b0640c0280030901c428562001a21140035a400000070720400000300300d4000010340181490b43c1254900380110784804 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 573327688 1250 573326438 573326441
    0x30f08130b0c070929090c09060d05010e070815060a0c120e040b030304050109050d0c05030d090f060807050d0c030209031f1b2718020703090b04080a060902210f01060603 75
    0x103c50b0b010718a11440064802071420041b090781050f101041c00d403800c50000e010a020740c21801d500c4900d00d5407500104040e0050707801c41e0758040d076145480c1c8442d14061070100c030240d003810b0b0100d00640000c074440043d80e00450550140d2900719001a0110440000c01003040175001401805582400742210050400005507001e4800507111003007220304142c24442c014200050903141a94407810005a644040c002e0070300c140c185555030f214040c00e004540410078141c1d44100c003000410020030066983c071105880301440740440109100c0014442100640a101c4000d0b5041c040c1d020522a074120a00c0c034a00150381e090801c0c003400000662010509500c0d0048101241504031032495182c19290112004005035661814240c0c031040141921040c0c40d40004070142e000400e4401d16411091a60040807120500c0e86031506024841e6100d04010400508454441100200b19a0b51010050415100c402ca00010b450307003100c102e40d90003400c031100c1c0c0e0329441c117030011a00c80d01c04e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 573328938 1250 573327688 573327731
    0x1031b05100c0201140d020f0403110a0f0b090406080708030c160f170a0c060305040b060a1404020c0c060a050403170906092101050a1b09030f08130b0c0709 69
    0x41d0320b42501901040c1c005580c2d042403420400e28020080090300244503591010b44102e00209100c251640c1c25860107510821009001c2c51207890649001c0020300521031340c1c0d50948200880090703d54050402190241000b40c1005015020740da0000c980228004060700c01c0c440c40408849540c2d9158200000c0402d107401a0040b1140e0140180408003c0c000d5003900901d4000448148880c2915000600e444c6504800d000a0300d42041c00148003503000b0180d005401103400e40c0801c1d1034891081d2122042202d0030780141d40128400c199110140080086403c015004690b200e502102c005c1990740680001c40b00030707a212002c00d030a5540c01c1c0030b54081001c05044140f41c0141d0008020005038825100c0b01580c0c1800340000d101c100030b000d000d0140d01c4140780440c136140c08000c08100154120364070410480c40c5101000030803e5400c10115a61b00005000c1c3d44441e00340c41c00954030902c0c1c0103038040fa03000140451114100203507540440d0001d90080022810f0010303915404c101c3d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 573330188 1250 573328938 573328969
    0x10302030f011a120708071106160e310e120901030213081b0906041116020a03020a080f0709110a030f060909060f1b0915021501031b05 60
    0xd00180a82d46510800060360740b80f08070f02500300710f20b0015100c51190122110000181c090052010b4a50030a2004151520312000352009281c210256800c10428103204001c22101410a96164603901e0348075007001090201d0304022124841390300003480c1034a5907a0000d501e89103060180c001d0208101c10f4412002004600d07203020200114081d4109000c0c664807043c0c641c00000c0c0c0180c041104000c2205040021004121b44008000e814040140500c2c015030038401c00313140c5041c0d40c41c00c50396007030550540c0901040b05030010804110840d00000e4011401c4080071800d00710025112811000000c01c6508d07094541c17010300c00f134440e420000d01d0618001c1c840b02407040e0090700100c0307250311084400500c0d95600c6500b03070f05442c2c010702c080d9a42e80d40d0308241400403215010398034510500c42207501000e0b60441d0f0040040d00d0500c5808104a0800c0c42d041c5243e00c284041200c07a0300040540b40c480d42c403800c142e8480b21985258603240c0d0400f050002d51814075807824480c011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 573331438 1250 573330188 573330211
    0xd0e0a150603020d170f0301060e040f060b0702090a0b03060f0a0615051c15180e030909010b0a0309060c080618010605042d060e030d09120f1e050c0f01030203 70
    0x2c4c460341d860100d022092101c5001a40600401c02840302d0000594002d0500303586151030300340900e05001c11201031200400e61300e41424028402201031a04462207541d043d902654155140e100f810020300415191961501440c0144480d203403c00244602441c0c904604000880d42c0d10a01c00035003d840580c0808100103124851070015400d012007541f92410f02c021038038100c0ba1004400c0062a5002001e61110a80c0921840c507506e11580507003994210086107002d10000000f031030038a05101d403503030313018002800070380c4948031b500541a116030280c030601c03014080007000390110340100c81c0b2501551104584014004104142c28102d038010b031680e46ca824203241d190448030003400d52505001c200c2168045860080c11869401014550307514507020014004150420368001900d60420501032410b12000610241c0301884030f602070101e452540c410f20305001801094000c03090010040320118050003800f04000c1407180d001c88040381c1c850810f4006404900007a9500c00000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 573332688 1250 573331438 573331459
    0x1506030509010f0603050708120309060112030c060c0e0913030f0f0c0507080714030601080319210b011e0210111902030903190f030e04020d0e0a15060302 68
    0x12402903201a400250a100204002224808001c243d03100c5500032500c0b540200420015844144100c2c000d041090000b41d207981003080c01541c0d0b810060207400300f020014aa00c1702018024078907010825400300d000d0220380c1048101400c44005c14440500610780c0c07100007452112260131103030003243e0644899500840c1003200300c0b0b668076070064210501c1000401100400c0341009424018140e0303100030021142000c0c0c1c00141400342002d404e0083d03000030018003600c0008426142c4d05d0741c000d2151601c10504003800c41d102d00e911502c140b034147c1c0c0115007010081c2590800c1c0d8403044e0a884404855503100000d1902c41485022200140c002800141c51400d268100011044200f5141400e01801d124100981c4910034030307007005a40000780d03142075410203020903103002c0c460500f5100500d100c2d846503608212602401402c2040341c510b0515180e0b074950550745c4000c9401004c00034000b1142c0c2d5240d0b55010010183c96040d10804c401b03403112501c1c0641416a503000c1c0040f0101c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 573333938 1250 573332688 573332699
    0x60801050f0604060804111908060a0e07080307080c070f0602010c020607020d23042606150d0b06010315140301050c19080c091c0213090c150908030d050f0a15 70
    0x20b43d1f2890100c0742c0e00000010080035042c07480c89034000900500805040c031820291017110403240e160400d82107580151204200c1d0034030100a440c3da5070b8001c3c001e941d0700c0c0d45644c416410300c01507400140070341845401c041030741581580221520849902110b00303036250040181c0c0e0782c5051649100000f0009201607041d552001e040b0110b14100004042c04c258440c160141041880b9200c001500c002510246002d4000c10400c0d030001c000800c144604a03006c00403904031441c2e41c4002d458001c028010981c40d9100b5404104980c40c1d001074450004d484208844040307840300d000900ca9800c11000c15000320f9160100c0304682c040203d082410700301d40c58203540036500200b42d07110340f40c024812540701d521070074454400c100e940c0d12a80d02405403441084040c0c1034207000406890319051044002624054100e81501e20320211885181c084190071100300f115900600c0440c08045001040201a50040d80c0074440f80e1840849a5a038982c0240c04c8400b8540d003000200d6803c80c04210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 573335188 1250 573333938 573333953
    0x309081e0c04020a03060e01030b10151e17071d15040302270c0d0615020601032618120a03080c090d0206130918051f15060801050f0604060804 63
    0x24118421304002c2001b40c0c2e00d19010070816802d900613a62100c03c0d00030411f10501511076440276105500c407403100340000460080c88200e03100d42c103261900681c0003040d0345900540c6450340c40740740804240010f1900d2400100007213084540b15589040780d0b0111080c1c1d00c0c0080c14150f24008030603203281040c2c6190200042e0a994921880b459095a90101c00090031f00004901c42ca40f8500c1150340c880c0f03000c200c4001c0301c06540c03008103030260b02122400581d81c0801c000b81100c1d00010560726074058101014962683c01804504500001450107011214001d040402038421507040000d0030045c140e0684a0008030303001800a2415070010381400500400780051820241030b4800300d25440c3d010802591000e8940820300c004260b040010300d48038001c0f100c010803194140d00642c1619030303a460b07840358003400340c540d038422401c0312181c1007c0b59405401c010411000c900e103900c0c0d5648014100c10750038052a4040c010111303083c007607800c206044404440c03095407005590340c1c45880d0140b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 573336438 1250 573335188 573335197
    0x21e060402040507170a14071b0b090c0d030305010e070504030c060815150702040f06050609010e0303072a1a09061809091005150a0b0f070b01030309081e0c0402 71
    0x202845040c80c00c000108400c05c250074401c07841c40c28000f400783d4826500c000303000c000a1100c0c0030400d610b00c00d4071002030300510000b0140c2c2d20030303200030494407020001ca0a2221140354660010100080102415810b070001812104031414000d5a9203505c181100c0030700c103900000d40360b815880410032010703104684883d48501300d481002d0a0080342c20008502c00f40d0b25550b0880988007082d100d0551034030b840b800004000310b203420440185400d0110700c150040003004c0e81413000400f01070110361002d004543c001c80d4803244517000d032a186190100c003103048400013017080d103c84134040b6040c4d280c90b1080480e166640f00719410300c10f000080101c9070344041102d1598022141c424401500c613890385500807001c0c2ca01034203034025803521000c116035004202c014400440287c0e0041c0e40c82c0e41c102a0240d641c0c82030416610780340c03814000d8440c4503004000301030f00c07030020002041c9540b0510306d10984214206807090b4071103241140c01180c2c0080b40d22440c641182e41079130103600d882c0c2c0c000c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 573337688 1250 573336438 573336451
    0x3905160c050306071d01082a1605070f17212a0c0607020f09062403070e01050909010605032a0403030207050907230702090412021e0604020405 63
    0x3180d61900d034000b082c00e00c1c5043d200340300810360700c00700c3c03483c0d0034003031110304249650030301c5c00800b1844d180e050000c0d250150303680b81803500452228803c1d12000b4000b102c0450248008201c550078003403400591b240c1041c4940c451100d000c0602151200b0b1100e054004806110024401000d900390000c42c14640100002d004502c02c100c0b020000c500c0c0704409803a44031752031001ca0004002c04036141444824500b551207944100031f0000140e98200c071002980e0005e4900c5102580d542000c280321061800c1401e0f003400320500750013642c102040055100c2e102c159101e415403e02c2d0300054900d0300403134298035404261f00740180189407245020b16071002c0341c1c0d154482b011f200100f26503411240300c4404485440005818024035404106036002840c056801c000c0030303d002c080040101d2011000000e042107440128001d0140d240c1c20766030041d4000b404403103941030501d0903850945a182c0400098003813400c00003810f1283c00628102c2c5c41e0910080c0c41940d80b0b96003003100810005211 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 573338938 1250 573337688 573337703
    0xf060b0d06150303020d090501140c1f060303020d0e06030f0c130e04021005030705030a09030905040608031e04350d08251d0a09390516 60
    0xc0401252880c052080d1042042c403241e054607045080003400d0450308081030b4284084a2010080c913684940e450100c69445450683c4030080c450b8103600b07100c0e410204142100700260b6000c446280d0b036021404a074400d80840b4a42d41e081002540c03000c07040201250b0002080c80017844101c03120140319405aa135201c040d203440384d5590a003501d038145402010003001400100030440c200182000c0c0020079a080545c2907241110000300688001000000c80c15211202a0101402464040041c110090060052a4441801a41e40c2d04400b2040340141204c0e556036800303d81d40d81c115000d8800c030490009282001c240d40416111420400399890690789640ba00d12840912050248499507541d1b201c00f0304203c104080305650403d0341942d0300b090b04402d142000e030884001c018000710200300e001410031440008000f05415070120340940e00302581001140040751508282c50562541640b52a00c6005500d220300c00d00480103010407000c129100d039040702c01c0c0d1a804603d109020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 573340188 1250 573338938 573338959
    0x110703030c020a14011a03030708092419031d0c0402090a170304031a01060905010c020102010905010c0e0307290306030a050706020c280e090709090c031a01030f060b 73
    0x58070305846420110425169540e1b0851007015036116100d5580740c3c400310700035410700740f081e01c4a8007030b40728071a0083d100e8627024624240c1407080c1c0520304c8080142c901119160860841070b00b03041c1c80b22001c0440041d190560b9201c0c0c140c0c0c2e00062a241681d4007000300800492101408002d61229600315032000303030f200c2d00182c3d40314140b10500300512040065525036107140351403030002c0c00000701040c0f444809401072003030a90180d8054100d41d001d1030101d5032840c40740010313401000c5040e4007404035420118445200e64000c450121320034000d60480d0080343c4d0741c00407051000034030084c42030032942a03c50b8540c03410051000e150005d03001020744411420654503149008541c0e0300180140c1c00c0380420340050700d0300e4804103038a22141101184140025175402007001c06a0123030050307a400d08404070b000200b040201002608c002d200070050304401d4100140300510303030321084582e44039a0080c000e5016000c80103174101ea40c80f040310072070030f5496500d00001e800046d0481c0d400102004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 573341438 1250 573340188 573340193
    0x1c050903070f05330706180c0e0a021e03092a13090f060c050409060b2a1e011e0f0c09051809010b032b0201110703030c020a 55
    0x48214000c10520351a905603d00d081c0500c0246408078107840000301c4004456001d03030b02d2000c03907201000c10f2614a10b40c0c0b01200c0c54548001c184442d500110892240c503201c0030003001c600c10a0a841e40c0380354503042d07562221620710a911400c41040c10702c104040d180900580e0460146801000007010b5a1409011499866500384106481e0f40d2652001d04080c0d098200144403c4525000e01014031803c0100e03140c00c000050420f1006050941d580d240d010100d11480c01e582c0540400c0c00c1c03d0140c155500090350244c1c00800d00c8100000440148201030311100c100d9850500c80480034003d00e00a002c60591000041110300c81c0d555240c680b00c41951105458000d0388202d005000201d406c480110542111148880202844070404062100e0b82e25003903a0300c0035010300c140c03202c030301da0f24040e9250140000d541e40a030140724140000600e0b601040e4259607000392039540b140a4440344504030300366598803105001c020320030032541004c6881780d00b000c1d480d480940101c1d400003502d40e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 573342688 1250 573341438 573341443
    0x4060605100f0809070806040818010309080f03061f0e03010b191503020d0219020c0f010e04090606030b040609050616090902030405190312150e010b070c0b07080306120d021c050903 80
    0x3220112270b920400101406d40c1243c1b001c000b4081082841d040000104d6940c40240310720440201281d903080110001e080f5544008c551464440c4081d00104c949004820150200c14541c215504c41e50030700084201d5401e10a0b4101441c90444504a105902d0304407205000707500ea0003400304154081080e000e8001d020300040c003040e400303d9890000e0031810f110003400c04400403070442c450300c40c40c180491203a0b071080c01c80310142e02c01c031000105000c1c84e01d0014000c1415900082041210608100500040b80d011403038081c000c00654210b5611a44070f0b41100d0a01c04c000c00114580500a02061034103030701556005116a04940d0716200c8120010150110414110001641c200a03046010b100d400f4a8032103011000000b0100c50400840709001501402111152a40811752909204080720560010010194500e03524101c600309041d00385d008440190042620800740c5040f640001080165240c039a406000e61031080480c24510010134500c9030f0802c0814000140c030b44c2e81c01e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 573343938 1250 573342688 573342691
    0x6030d050c1515010e03010c170604090f0605010302040e0a05070e04031b24060b0919050604030b01030506060604030b060f210f0712031202030a1e020304060605100f0809070806 78
    0x940441907003d1039a80010880d003043c41e1038034080d0341440b00600c00740d40c111411098a07855043d050040c0d907610030205004201c1182e007e00fa40c10641500b1060202a030301190507a4000e070313018000ca511480a01d07596840b6050010541d50082c1010030115400004142d0081c2c824600322030340821210542c1d069042070603013507403048000319038000f0301d040303030402e940355403100340814805d0b5417078843c1429080c050040094020000c0b400c00101c06240a60154050308000f412683c0740c0b6100e04014039401000d000884292059001017145031800700f069408030307540310030a01760565a900510a03007162801000d50001c3c9003400c2c0207480d107038101b146036200740c40c1001056281c01c440452454050203070b2084994811168170078000c80d038009140400b0f09256500540d0340d4852031081307070041c0b114001e40b0a800d006180702d0b4035400003e4000b18002c0e4081d000c00c0c0951a11039041203503100b46103001b4000300d0007070120040134a00469065074454547d4080d6a0f02c03980c0d850f1002d007051030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 573345188 1250 573343938 573343951
    0x601061b060f050612010e070e06120105010e0907060201060b030117120a0c0201021e030a050f040504050406020405041a0a090b130c020312012103080a02070f05100f0506030d050c15 80
    0x303c030030800085080c04000a000000480f00078060003500180503502c031640750061060380411800040c14640b1401a8100c044442038020083c0b9a90740d00f0b02424840103590003820303400740b0880001c14510500901c0c06a031008001c10346103902e00a030355104100820040410f501503c03076621459008403010f49015040380d01d40f0f0781441c43c98800203007130020007462251003a02130a0106c0300c1d03820010035101a000f203400e0103991084500d4131441280030f186d1006502038140001c110801065030050411954255824080c000c0c901e19060306154601c12240e0f00718202903002c03c840402c035085110b015102038001c1d00603560300c14800b03003540c851520a001592000a185050140c181f03130381401030410b00411b00c01103420824090340f12510480180411044d0700100f1482c1074a50b04686605a010002800c0c806091600c0c076110780d041c04550343d5061074034280810f208214019070f0302c25803004000d172086055061083e01e03d0b400c0b030034500840303100b1111200c0c51010754034038043c081c44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 573346438 1250 573345188 573345191
    0x60908040614040e15030304241202122d0a060e07020316080a140703081009060609120305040f170613020f0f0f1e10020703050601061b060f 62
    0x281084409882d40042081c01c0308041010041044003d680100b90f0360041501c40302111126543d100181c650f02443c2c1140694101c1c0740e0912165079020108100710924a40f02c0c94032002c0003200241c100c0c0581d00d40903200301c61000c001180390f05200c45aa015041d0a200c0f10410803407032601e90140c400031940024050380e204428010340c440002641d62042c51480210301d0113106030320041010161000090042c0d60214002444500a980d03d80510384014030454030b078051070500a11a400c20b46402c00c6030083d41202080240d194055070f800d60340c0907141e000005182802500082d4450f20094040020134080031400d98003180400c0c00070101c00419100d0b60103000605810100040d0401e81c04002c843c0c00500180c5844262034500d202c1165200c16845400000c40c0344100e5100201d036200304420010440500c070501d2602ca0110180e4615201c050443d005a980d15003a0001912a902000042003030304d00c10302c98021500a451644241d03031140b59220801c1c0c0d8659141c24000d0b6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 573347688 1250 573346438 573346447
    0x210c050c070506071a09070504091b08010b0307170114070f11010b0f100306030204020a090f050a0605040b0f04050d0b01060f0905090105040b040902030a030807090f06050d0513060908 81
    0x1400104118000b80408442c1c8a140641d2503481c842d50001802c41c1d0000000041c001a071001001e002035402401d0151061005800070700d4542c444c1455541d9202c1e08500721000441c0f405c00510900321100400b0340144a42414045043c509404100d60440d03a076484880c01e4902c03186203480c0a004000c203403141c400c04d007001e0744041d212001048203186240cdc58802c0317590341503942004048c0310f0501610032601c03942001e00110f0251000f500065049400012600c0c003482d80454081c0c00c5403a07100400c03259940f5401001550031581c03081d100050f206000c10701032074028000503da0b001c0f907030241c607107002da0b00c00c049a629a50440180d0f9080c6406004000e000d030041c040d0400d880c0a072a000d002a810300c000204102c6c01070240c0350280c3e58509520744141ca41c2c0c0d00a148903034004046940c84175141ca401410b0704001c075132a0b400a443c1060019001b80400316603403e031007441e154107080c441541001c0c0f000304401081501c001e40c0024000010a04600c5054001070250640e942e95 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 573348938 1250 573347688 573347707
    0x1303081b1603030f11121305030604050a02042301030309090b0306090d08070c0b0f1e070e010c11180121020303030103110a0b0c010603030e09010510210c05 69
    0x22804140105095400669030450101501c0c141e00c41980d03454185460712843d0450b0440d00840c070303030301a14954841c2d0705440854207054005000e400c080700807000b15154440c000c0c10b464060646005125034040d6841000500d802d4012a450300d00303145014a40240310000c0c040c0703e00007a070054000ca000000d040c811501d07030740180122450150001c0841c0d0900000c6141d48016880d00e28080109010100d00900d2080da110101c03182c02410b0b008190400489181d580017040c1d6031040d0550740c1c0b0025511094442c0d00051090059407101c2c0200000e50006440541003810102c5043e4528100240990b45403456000c4846008500508542c1003401c85081c085400c2c450b60444014a01c0c040c0040e80c0020132281525403059011008817428400308041c14500c3c0c11215000c500855040d110311015481901200d009580d0441f08842d01820311155401c05e0041d190010080080104110b00031845000c410b400140240302400c0f213a4400c0d02252000700070f40c1d0004100040600e003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 573350188 1250 573348938 573348967
    0x303270102150103030c060c03020904021803070608070c12260603120408031c020d09030c0605130c05091806010f0611070b1204060902030601090504021c03021e0102130308 76
    0x1000d91221a0342e00c40c0754156100a00844600300d801046551140108128148a5015101c00d030402500664072180517240c3e00c900c002000e09000c0c0030348650721000454611851070705003c1c05054403008940c1076551500d1012540042c41101409480550f030b21048001c504408218604600c0b41502401d110703040509110b080448800111000e11091001070401300494600c0c0c1c903118503902074a400c19006d84040e00544410440c039610f4043c010040c56005a04991a10b1141504020694a0580148450804440142425102d244180b00cad80c10303d0203c2e82d401030b40c0c07414290410401e038a103652802c0801d8011160446400340c041284540011620580090190140403003e08100300358010b4011801003124800d1080046000c0c0810350303202ca050b4076009801d5494640c0c4410450f00900001c1e242280906124020151207840442498100680c190b010f0018851703061402c0d401242082c02024072550b01b00300385008014450a80e400840c07041003a04d49400100f949202e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 573351438 1250 573350188 573350203
    0x803030c03090f0d050a0e0a0819051002030c0d0c030902090a15081906050c0705071e1d010303030f0f091101030b100c02010f14120612160b07020303270102 69
    0x19550b07407144c10348903126500300c4240c0e50b03840c940b0325011010240c8140040c030250036a50040d8224010010490907595403040301600b0030b4040d03c2101c41e4071030994850000ca11089948550325413080c4806c500340015038000101c24102403402254901c842d40020700b01076802c0d607000802c83c0d82c500c4020610686460820010040c0c400905001c2035420f44d0045116050072000300101e41da0750010f51031081c0d110030b0b203020710340040449d070350036848212070340c040040c001c40c80c1c802c2800181e0000b404544400d0102010b0441680c40c075041c0d203155004e9000c0d104405108a40c540c940011110800940c4078801c0e500340512001011701204d04005012201c3c070114071401400d2107002410020f412a1102c2d054075420b1904040b0a004072004407220350906000d11718140c40003031509070380d0b407254240701e00402003100d1040002071003000c0c1940d13840c0c4032003d040841091000c01c00060b044080503102d0580041d00313491174130308002c0c022841d4400e002856200b0b40540020300d556540c0c10000c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 573352688 1250 573351438 573351463
    0x100e07031505060a0c0f06061e050a0f051e03010b1503040b01060302121902070f050a050f0708070501080a02040b030c21010b03040b2703070303050a110306190803030c0309 76
    0x14a416001000100a60350790f682c0641b403403071400c10783c40c10004e042d4040d0004255900c4030b40c542d01001443c0c420101218814548948010a00442c001008120301c0741102c1c002080c070100c5501100e030314271305401c01c0070030b0350392556035074441e0100343e01c400f060b00000e03208a4185681c0c07443c2c18981900100e9042e0001c81c101881800349005404e0100c2d4520340044031520804010b201c1019000046d1084082c0204004070389030040081040c000354000043e40b143c1e0540303504080039001541d0710645442440c010f54801302c42007083d540100c1c0d542e50000e00c8044054501510340b100c541103030b40180c0740040d4003c0002402c2c140c29440040015600e0180740c50380755039502d856038000c0d5900014201803c82d00340c1402081c0b103407200b40c84d5144201600703140d1249079032f0740fa210680c607504a040c050740824142000075440c1700030380c81840804880c0b280c01c64299180d4105000c406090a000d04004c5081958080ba018a00304095072042c1c03040d01c94180c0d80c0c030f07250f110386080c400d410b4480c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 573353938 1250 573352688 573352699
    0x9130b01080d090320040f0603030806040b0a060c0302100212070908010e0309010e1c030e0310060e01030311030d02121b07023111030405060106080c12100e07031505 73
    0xc4442d1550000e60401101c0d0031070380c03848003000f101e0b024a5001421246050340f00746404000e000284080d0024411a4040d403102c003203c0d074a40c0d0a01003601c1c60701110960105080340d0500404d030081d40c201e05454024411102c0003280041c000d8100e90184c4050a080d0f40b01508002599612081c8240504a0107000303000307000c13807032107030030754a000d0881c50038140080e600c111001d07038603005a01104805da8002801e210101d904015050400440e4518040d0061072141c40190004d03018080841d0b001001c41d826680c07031500c080380c552120003c0d04040380820400c180112510b80040d000e1500b0310b000000c000c0c1040c0c6000000501801c0443c044844140020300c0507940c0c039181c9400140030102d612101c46900b4200c120350000c040700007090b0314541a00d1016842000300598819480f81d03007241c2860b45c03221402d95079820111500c0c00c080078104524120386003981d01d103d41200c80c2920004200da140c0c1d0b011038401a08a4810000a0341c4004c00d4034001c032a510100b0040400782c17503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 573355188 1250 573353938 573353953
    0x910050705190f05090613260c040c020a05150108070e01080318011101091b0f0f060e0d0c0e0906070806010e060f070204020a110c010305071205100509130b0108 71
    0x100003071210b00098400d400d01180d008559035032400703a000c0b901d403010000e021907034800e042a03120800b01c007180071301c030b592000c020501245c04003040c83c0c60003030890300c0d0700405080391000f0030031000d0448101c11004500413040c076400021001c0160715031080010b0305820f019810000c555150007200e9207d8894035040750010040740c0804000c0384c1e210f214034440100c8100c0c40c100182c8540000154080c0a58a0b0500076428001301074103c2e042c090318584d042c141540d0b40d035000000d481c100d000d5268403402803a800c10105000e0300d402c02c020030003e41224404111501e400300150030543c40746155560b4207040040001c01402415800038450070500c040e4100340000a0900040c2104103020705400180341042d1300c44c80e004d41c1c0310294010025540c424401c60300418610488440140f544280c8c03012840c60360003401464400c614070b646100c0031849585801002e000083c1c225001c00054000208903034580c0702800303210309071582920242c500305190000a640b0143d1108005030031180d13 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 573356438 1250 573355188 573355207
    0x204081b090c0406030e0a05030c07180b0604052403070f2c060a140c0d02070602010c0503040f020d060603120e0406031106030403090e0108071d040f06050703060e0910050705 77
    0x400b9203003a03890600e00014a0342c8141c6c011403600d20340e424080c00781d1002041d5009030600003e41c01c0180c807143c08084045044003415030059a90301c4280385d030b100100740801c1c0800e00303103072044000d5541c904070441c04c0c01010034100070750369000341c50110015011003021140b035900060002c030b08007401c1c40c20350340ca1850804d81c200c46441105150388141000509410414400c4110a41c00a49c0da0212aa500311918282d5500e00002810390054000d001001400f24018810302103680803d48455140d40e6540d070320b0501c206107079901244d2004100c04004085802071281c3e40186104602c03052115000710bc000c4c01158207824514442c41c01c013501030000600700c100c0c13820100303000e03902a038a98546180603a01a01181c0000040c0445003000044841340041c1031421240081090300f80102d00c0340e1b421492041c01c44d006007554045084810002d04194456a800070241c940090015122080d500708188191039406103a03001c1121001460320512600d500081d29040c2549040b841a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 573357688 1250 573356438 573356461
    0x1d04020a120c0303030b01030b090109060f0519090c050d0c02100f0c090902030603210a030c050a0503060d14100212060102011b1b0b040501090308090d020a1b03060204081b09 77
    0x5020084c00c00d41c8074004081564081d4000b07002d100070003011b000041d07031640704034002844039200e0f1445d8582c1180000402e400e00b100c11100000d0901028000241405e44810140501004410801404204020aa00d854821070000034800d070701510100c8100901c1c2c0c400e0700d00e60b40900201601d0422125030042e08a140081200e1141001517201d0740c91000182c2880b0b00d85400c0102c1d404920780402800041500402001030f0300d403001c1021070031382403040301c19005465203c00071a41c10408640e007460314090f8849050b2094130070340884061242da242c184070040380080c41031038002c02d15505425000030250b134001c03c203100800c00190f0519806803c02131035452001481a450b031030f40c034406246540b51341c24a40040380400d50782400d03e8540d00078141244142c00141d400320102d2048200800e9580701c18100d81d004105602241c0c0302d0b6845902c0300c6103071022001c12401c0c00400651580080d200034543d40c00270b0821a81c1c0505200c0a0140d401c0302248070b86220400c228003c8034a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 573358938 1250 573357688 573357713
    0xa0509040b0f04140106031139010e011505060c0a0b04080f07030c030224270106091401080d08040f0305120f070207050904020619091d04020a12 64
    0x1120041401c0c03100c2400304010340440c0303032829040741c1031611a0401d43d1009280318100c601e1541d00b042070407101e4904819a02400d45514007000954850140010503910070040307800340c09200c003201020a1101c0d40c02c6400f60303002e0b03021607515000008503881e0310b5000a8004c100580d215490042d03c03601c6652142070a120003000804440c001c2000d106801058540e1003c015140700d5a0b02c1352303818050581095140124018480c0d004100956200614002561015034010003c26101c65205520854800c20034106c1da00c5622200c0c0e401c000b0900905004003410500015088000c0d844c0080a100580001000740d2060740081f991583c042c002c10b50090b042035500440180c0c51404907100d100f640e00c10700d0704094640901611070103a513002e50181285800300e8000039510810301c03101c00030846000c1c3d8400c0b410700030340e0003003c4034090210880900d4a4101886629003c40d8041902070f0b000c00f0084078121820271003181440540000580401e8000a1000f031066541d207002e0080c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 573360188 1250 573358938 573358957
    0x15060207081203250914040e060117010b1e030607090b0306040902010302070f150522020d14030408010f050709181505061b0c01110624090702060a0c050a05 69
    0x10004030701d690740910742850313150b100700825481142214018105034081c0a602508a0801c04080040c5003622513a542201303600702400260b864501c00c10912012207000921304c1d502d820503050655109010220304412220711200030b49200c5050524180d401000070f428807944a200380b00318020710040d01d40c0310200b1a0041800b480ea8801200a40100d17280140101d0b00c400040007009090305902c58010300301c0703504100f5035641400342c0c2003810041618a1250b00220424400340c10320481008400c1e0140c8603040e40390b00d0050a071440c55000b503000c00441e95486072101c00703600c010b000d100e821100a25088800030f0400c800c1040e80f094103104200e0f103655030707842d031280c41014072410001440010724203520740c40c0010050712001d071162581e850500420b85c56103003c1d07000d0300c0c118507400002001445607540d5080503051240b80d8040c94170100303442c08410821550342006203881340070340b41e014104509103840c0c10000d0b1480c03040560140701080c0800500598400300307039503d920 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 573361438 1250 573360188 573360223
    0x9061204110301051b0d0207200316120305030c090612070207050a05011e0e040606050d0510141203270108100b03070e060705011802011205040c170102090a08011506020708 76
    0x135814800407000b486400b20081c0680c62010341827460b0440c2c17070a1118100c1d02901900c0b401c4d526811b03400750001c0385010322185288441d00c5c110100b0320420196500507583d001b802c4c904000c00c070028050f500081814208a04a10200704440f64103101e00d01c002d103000d60350300c1182410140040c06041c90034001040c020310a030300000300c0e40d01c50140038648042c0034204110464594100078402e80c4000c4211040c507040074040b034026007070a03c2c1001100d02d901540c2c50412113103400c1103144542d0752410326140c4401d2110101c1c10071203162815454043d000c104016200d00e100242244500034030342d114034010b0b100200001003030b0780f040700e42c44140ea26100e001000103e000a40500946102500319032800041c1d80c2c10301d250b1001d0740403440c000d8880c0c0032400e0055004505680003210004e008616017401003140203140324648106c5441040058144014440859100702c603c0d4420040d60f0744800c2c100c3e0481c000803480f5009016a071001d001990b08100c119a5500422020700001c0c0c0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 573362688 1250 573361438 573361447
    0x130806070e131803020606180c0a030b0a0b030f100506030f04140f0f0708070506070f15020405090f060f04020705071205030f0307030f051e130809061204110301051b 73
    0x22000c9601040040c1140a0040f0700c0c4100da0070020360b20b040c02c0700c0c0d6600400904203100302c035540408009108040d044099840c000c9101d01c1200a0120f08411a0300082a0a40840e400c8c2101000e940b040b4907040d0389403603d14268020340000880d0394091400354008100344950500c1c03d0b02125405a000000b001030b035200c80c000b030352a10300390718600e030101c3c0910b00c070f480842d000c0440c441e0300b140c840c070040355216a100c0d030400131039200ba014004c1006d150b540f500c80000340700312140d02c4010ac101400604040d41c5901140211504980d08035034005100200705442c685404002c0c40f01e0310986003181000f00c0c1e9568141e807a50701d401703029070b54420070021004000c0b0401c1110641f00c2080d2801d85c0380d040000c0094080c0807903946440e10701e4202170010341e40c2014041704503090b114004d84800e00c3e40b1803180c007001c0491840402d5840002c01c006038102900c94000070816400c8007030320181d0030b00c1c007802c00400b06004007954600c26410304050008c0034440d1422600c0c2035020707010320b0740e44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 573363938 1250 573362688 573362719
    0x2090d03230c0c030601150f0f030f050c09100206010b120a1b050403060b151812011b2703021c0204050a0e1501081c030b03010e03130806070e 63
    0x2001d08a081c621451a000603403003031180e400f00d00c600c94004290215826030741c80e820802c4d110050b881a0a0016424a108050452256801e148070b6081c0c1e0800182d500c94040039542a50f008aa499458080c0026500e000341048504451319100c90300c054919541070001c86d003c98420748070500c00c0c0001080200d10a403400d0391081204951500303044d00301924114000c1d10903040340c4021b59940385806902141d80c148400c1e0b0308040500064481e26001402603000b2680a01c1a4207079002800f1510201ca254000d1146840300131410f0b500514164901030300403c440040607890191010315604844100e50741c500082c02e40794110382e40143d07034411480c8000600120140070394010b08180c00c0c0a00c0c00e03102c1d801030040003178000c00e88180e0040b09010717402a001c01c1c40350341c07031552000011828140182c4a050200e400d149800f10f000b040758000607080d5181c06180440ca40c1000650442c4c8000003030f0300d400104007120141c09645440c8901400043c000910305026070819040880c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 573365188 1250 573363938 573363977
    0xa17010f260d05071704030c181407030f150303030515150703030203190609020a1b0b0411030307020d051e070b0a031109041509050a090c171606081902090d03 70
    0x7017011600c1d0b542c48640e40e0914403141350080c402c0b1007110341658403241003201c0500901c2c107254040d51861343c2c503840d82c1104500810081e200c002070503903070f0014801e6401c2c0d103c1a42008600942d0301181600300486030000c10190801a03c2c0304500b40c0c0740f4003c0c24103400c41505c030301035011b0034016229034500501f0100e10384925521542c0303d140c03400c00f01c3c0215140d170281403203009031713a600300109401c602c4c001203c0b03800782c0000e45811840f000042c0060701c1c11080f81540c55014050302c1c00d2002c2c99001ca8000d0b1540c400480e015000102002e402c04086400c070320b110540103000f05072080c50b08814a00510804143c40101620350300c1c20950081804100d6414080107801003110700041c43c40f45540408900a003085142810301255403403800d07010b0400c0d02d030341090015401902d0200307a620380ea60035030001c05040c0500d81c003144440f0740b003504410081c8041d45401d000342c46c040c41c0348c0300301040203000341d90710030700c18004c01031923444800c0804000c69140c02e24440c904036008a040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 573366438 1250 573365188 573365213
    0x2010e0d3908030c010c030926040b070305181014031b07080a030506010302030603030d0b0f030607080f06041515020f010e010902090c0903120a17010f260d0507 71
    0x2080540601e00041416000000b0209502c50304020055200d00220031010785503045030140146404075102c80076a40c1d6080481d60711086000010b2505070f03602c039848081c2e0402030301903010400100311001070100d0307100380701940030080782c82c0b0341c0808440071b020304071102e10744078030003c070002100051494044c2c1c807040c900030010001440d200c01203490814240c4e841040704000003070401001c1000c1e94040d0027542c1c01540d005000d141400030807a5800d0082c458132400541c0500454080c82481c0c6003401032078081c030034a036a102081c0c900350382041e107000c0025082e40d010318645124074182440e450020001e8502c01807001c50380110b03000d0100e28104030341d2802440ba5180c18034100030301805601036444244213403610750440d911700c90400c0703040c007030002803a40640050b0485210511454010031a42a89040140010040070f0207a0b0705030009810081c03286515070800e0000c1c1032031914002c2c0c0c141340000303002d452100a81519450341c864140c1c2d04140000400d8000800c2507482102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 573367688 1250 573366438 573366533
    0x50904050316111c140f0318030102120c07050d020f0a0308060d0605010f080d030b0f01081806130b0c070c1806030602030f070f0504120f020a0801090f02010e0d 71
    0x38204010160703088001c040e42081c1140c0a4000c40300384d4640b80c0002c0361403e84001d51b14095401d00e40081c52a810210007498130700e90655080100c01e0341141008550750144440c003d856440308203d10307180382b40010b04142c15095502084841d014400d000441d98401c40c3d01d03203420070803900d07100007181d4001348c1040014801801c1800110b4102c0351100120100c40340c0208030350118204800690841d49000046034000e681c0301581c01042d4050140550000410080e000880403280c5080d802c0060589070710005102c1440244280704070940f8840c0c012154148440c41c200d21603071102c420ba180c41c46a242c54144103481e50030f500c81c0b91752100d4000c60300450300790360702c0c600501118082e50b030448820011446d4103200c803d03510321400c00e68040e100d024640720324005150b102d2901d00070b8480f4040360300c10301d002c6d0040f402c0c00b02030180071000c0b4400c0c0c14402d400d0f6020703c000740c2038600501443e4025442080780b00e01056602e03481c40c1c40072a2040c5401d80d80007207a60014142082440b80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 573368938 1250 573367688 573367699
    0x504020904021c0b0a0515070602090f0a090603020f0f03060411030f010f1506020a051506061b2103092a090f010905010812070212070f14090105090405031611 70
    0xa954020030f1604900000c8404490030b64201c0e031a2420403040015544582e00350b2602880524000380680d070007003101041c0200728250240b0a0000a01402e4031a0049a0901c1e01c5001c20070840c10000030701580190129100042c550f52440800d60b118801030018154021800b00c00748152400d0003858440d02112000380004000c40450b4406040c03031601880403d95000070020b2858408a100132180c1d522001604182a080c8032480307080340094092507111404020f034400900b140041801079500785005014107180c07003164510340500e400c641c3e081e4002c04004001c542c6401040582000c0d4a60304034a51101078085640c44c14000604100e0b0401a68030512145801d8400298100c1e507129805000517a02d07440301540742c1c80700c0c0002444a0f48180200340042c075104030170b05039003840a82101c01080e40c5031001141c402b00e55110a0720017210445820990614080c61405400e042d5840040e50809580e810f6691181001030005118030034000d10400801e05900121840f00a00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 573370188 1250 573368938 573368977
    0x2091504020d0c021513020d030e1e01120b0102190f0203031602090907050108070c05211c0504080a0318050102040902130608040510110c0105190c18050402090402 72
    0x10034002440c586205002510400700b05280c0c24642d40e00071071040c1d01202c0029403800701a030038486107901f410011414442b000c890301d0110b4a410300581c5400100030180d10850b028000050300810031020310b01d03203080c10310080800c1642c0000d600c101802002007034140d112424241010500035002000303505000000d4009580190f01029110a134000c6850000c20303166001016541c084500c5150301180e11407000404160091002a00c40c03401101501c0521803013400d00010f000403258011503406000c80d82d44510945d07009503c40602d40c5090401660800d0b2b00c0e21030132801954050740415486041d850702a03440c44003594129503102c0002d540702c60303c8110300d00c0a034004c0d02c1a030f40c0124032508001051031240c003105d4090740d0002e01400c00d42c07005c402d030b90000d1700f60700d041803020150400c007000f00b000091140d2407040c81681000350f00070042125120984298003010303800c000e001494410500711000c603140484508440047e07990113800701081c0a802a07024082c8031114a52 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 573371438 1250 573370188 573370207
    0x9050303070b09070e090709021c05100e0912031801020f0409051b07200303043b01060503070e0f060a0815012c030a0503340206070209150402 63
    0xc1c821402420000240c0303a407651126040403032000b0840f01007086901000c010071060807180e00402b40b40700c92203080d078507100301c0d041c04a060b56001d980055443c5d00040041081070211400c194209003590080c204101074864004028000503180e2540d000341d4050325400307164254126036019400a280c592a966101075070320003000c0803100140240b490a440c0a4030b609000204c61240354008241d82c00e400d58203152803100c1d180d041c0701c290144002c20000c42c40400c407030b03100c1c00ca680c421031000015907807400012848130240c0d03040e240c108403d0401031114035000300c280d0745c0c0410760b4541031816021001c0018442401c01c640307a41c105070000380003c2881c2d4000000c0b0f11a441d8010b00000702407404004452104281801604021f1175448a250380e40c0c4425545000500c014102d0b01034403410b884007411a4400e0080701025040d01c241d8152801440c1c0910800310b071940034030711341000942c001c107040c0e101e00040240701c0c05003080090b010302c880782d020107001000a0421900d80a444 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 573372688 1250 573371438 573371453
    0x30703140d020d0e0d0b1008030d020a020c04050105031c03090b0115030b010c021c081c02030f01090e0c1215160914150c030d0203040b011d0f0106050306010905030307 74
    0x21032800050140c0303003d40340c489004400665030a030003c2c00c020300c0913619031a071151108002d4a0500d06050715100003a08035010000b902e2101d04003080140c2d90344c2400c401903d0000c4480c1c82c68015800d0a004004541d0b01003141c0900a030f0045a001c419010740340100e0061056150091980d00100004604011100b004611040454a0800a0b05001c2006440505249400a45c8005040c0e65100d100045581080c552032185e07504608140382c102c100b400121512003a810825408410002d001180341c2000d80100b89503035040244040410000b80c949001c88405c0e03001d43c8101e1402c08228808002d181e4039040d03917120f807141a09004040304030b010a001213030000507941d00e102060350703444000d501500f4a0000c040d181c0c404003482404d103c5030802664034030103000611110301500520300065120300d111350900c009a60404810355415005d4100040c241c00d505810001a00f9040100d941980c9540c10000c0d103d540f1200102e900705019081150540001b00740708082007000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 573373938 1250 573372688 573372703
    0x6020406030507080c0712200a080717130b1b0a0b09120c030d0f0908130f060806030c01030e0708070f09060b07020112021309110705060a05190b03070314 68
    0xf83e50b40e01d006442d003104218003400f6403070740600201401d04800101c540580f842c00031986a40c1c06518903542c0c41c500b000d007000e40850098900410000e03d44042045040c46112480d008031440b50911242007c215a514914010701c4503024000a59410060310f00e81d0820705a080c03042158a0000e0340d00d0700d070803418002c0d81d581c8030303502ca034541d010b15080d0303007600b0365040403504001103041101d258145c20107441010082d0700e4050303491004c4e00100c6c0c02d40f401045001441c0200024461829010740028036299008a04006000e814131000740d4000c80d035102240f1092802180d07500c0610304140c1488007079441b840c0e6512440c1c5e4001200d2001c0d01c1003208803414a5410059265101c820400d10710035280c2c001d000030b01c000700818007a203603a03020b818140420409580865207401d001e40840308105001d10030008080340c400e0070400100701c11581310f55402d100f8010f90030943d504e800c0c1810001000406149c80305542e02286c0c4003007020400a5402c1440d94000c2041d01ca46152a08034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 573375188 1250 573373938 573373951
    0x1c03152903061318051614010c21020f0c01020304060f030203060a0e13050c042310090f0f0b0103140c0c030c030a09080d0c0305040b22080c1306120308040f060204060305 75
    0x106c075003145507904000007100c11143ca0014041c0da0707041403001180c1540b890350007266031201540480f07130b10126000711020580c05980040012190360a091840c0003101c2c4c1d42c250455104120038000c1ca60f00c40c0490300307584681d080c05626032315071500040f2a210280c20080300c0d817543c01c0411121107451404440464041d00c141e50072604844288001d45891740c1d2860400d00401445e00c10050310880d09561110316821442001d030b0300c400701003081d5840c00240390441610340f5040d100f00201441040303410042420200408445051903000041004162003144c81000c9a5006245801d00880300c000c1004429240e49111004028000054034000c4400798411140034828081c0035624102c401501901d0f00c50900b85030007004500ca50155042d079002019500d030f102801118030000b031014141e0310300902280b02c1150280000c0c414860310700b403102418550100310120480c5000e14a45401d49024411070780c85003011004a002102d0040c01144002000500c140e0725902180c02142c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 573376438 1250 573375188 573375193
    0xd0b090a150b090a14120f10050916050112181b06050f0f070204110c07090c0f05090d0c030213020c1207051e1c0315290306131805 58
    0x3500d509004140380100f032140342c1c101241c094180550740210f0403610465100a10794200c4c2d03141e0500c00c60905180418460301588400c8040c07023010b88500840d54002060300040c00d00060b071a00604030a8007900c18a03060104d440d4a6040450790b41c0c210759803480e9640086145407950303203031041541c500b04d05801c100780404100810007d05c10f008441d24840c66900403814515082030b980c2240d808001c08a07403040d0b07150306c0240090303c4031b8054a032300c03007a0b03402070261a80b521052000b540e1988080c54104039190f20f2441c03059030060159012140700b40c90914102955140811203010107800207540054144109841046075400500c0030b9201507060300d0030700561007100d1025000c2c0700401005074008540901084202c0c8030400104100d40b4101c8201c408804c0303081081042036044140004d44603002202030f5051214080010b09119103400200940d51070083c884032082c0180300d8040b480000420340035030780c20f4211544000c2e120005c03c01d190304035440760814841c142003182c050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 573377688 1250 573376438 573376481
    0xe03100c05031b0301060906030b030c0406030b10060e03070303050d0e0319020106080c09010e070306090510090605060a080c0c03090a060e0102011a09161206030f0c08030a050904020d0b090a 84
    0x40f81c0e5419070f412540c10340c90703103941603050000070f030090a0581d1206415200e004001c444a80d0745010302c000944c0522000502401c1c1445034101c40c0705146c01078001c2c80803143c1e01d001251000928032080701e03014945242ca8002c442d0000003d00307050403240e2035070320001c915500300070410b219461140c5402d070001c001e2580ea0741e15207074849c1500d42485034440341d114010402109014091340e8462900c0c070f00010f07078a13124598102158015242c05101c59440d03041841404181c5c454400603040841740c0504044e0340000040c4040d41c014204e04004c000400c0641903414100142e400240700100b204d003140b030f15140010520460412114015800c1c1205a40e010301c0703a0300310300b0120f003003d0010f06042d45d400a40101484580d280c6404100d407414201c442c400c0d1900c40c1c50040e6101e03a410a40440c0d090901954104541d0001845030708100003c80c960350300801201c1450b00185c2d07001d071300c0342c000130000e4000708641d240154015030703008201300c0d10340c9259011038008503603c0a44800c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 573378938 1250 573377688 573377731
    0x90213170319020712060e0f0d03020301050f030631050f030a03051305070e100f0e04030e27060a0518010906120b06150c031803060708040209070e03100c0503 70
    0x4549036032141c0d0f00c518601000030408140190842c00d03103c1d07c41c0c0b041702c200311010060140b500703500d030003080c0000754084018007051804a6680c0880d0300110000c0c82070f810460701c0c1c650700c0c0948141c81d86501010140482051006003039208005400406035880c88060491003502d076841300b0381c1d00f03001900c1e00000400080070060300c2d45441e40c00200500142d400d02841c11030085000d0581c0d90400886240040c0c0943e8948092024140710452008542060301c0e000c0e00c0c110b40d02000f10321a0454044004101c01c100324817010a00740d000582009440d00400300d040e200d81e9800c46500242d4642035610b41013180d0070164100c601d41c80302084965502c00c61140c05000c455002840e000042002c0781c12450803c8062036540c1140001d02d15040d95030706070354a03550056506000c0e075003080300485110303e010710820ba0f0001050030420b03070034580b81e4002403884400034091414800c81244c02c13920307038808120103071249070143e07004c12070b0026811001d07107660070442d00700e83c2000c06d08044a01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 573380188 1250 573378938 573378943
    0x6040e0412030507020a120933020304031a0403050405040f0b0108010e090307140c12100b010314010b1803030a030b1f050a08070c08071505090a03050409021317031902 74
    0x460705459006d0035600e0095655004a44018404a410007401c03c1c0c000c941c4045600e0320002c3d10244600c044090001d08120f401210721040500c2e040d1f4009010401c0401c642d024040c0d6580c410040354099a911440c0c02d981c00d004a810041d0454605440581055850340c04502480400d0321604401d0b03a030341d03601e0381d00000d0440b2580402c7e0028002c0000066501c2183e0246540c450155101d6031422000714142c146004e120010541c80b0004140c4203625030700c11000800303001c0c43d00340300740e40b80f81070381804260341845600c410b0300d000582c1c0d114100410560796031204004003640d9481c801028001c01914880600d07d1140051600c9a041b804056003482c2c418121501c1c2c160074580b080d4001d4801c480e00400d14401e01258a001e00e000521540081106511402039500e51000c400b6100c41203d000501c03001d4141c0c401241c0c040409d4108c81a82c00700d07080c0200241c3e40324a14120403046031815405046601003030400c422030454040050030000c0301c02018504800058102280d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 573381294 1106 573380188 573380191
    0x60907140702150c1513020a0320120106090e16050f0d0f0501050a0506061c050a0b0315160801060f1b2307080a0201210b06040e04120305 61
    0x1240d030a0031020242c2002216606c03401060307440d17000c00d5416005010280c00c1c01c000f0480c40c0790714000c6005a20722200041c08881c00300c411142c2c0540608203a000704480c2e2403c0c1000c0311155003001948983c10100369841d0860a440c2c4428030400e1590540c1c1c10713030000c5048080401044032008c22240f180c0c070403000040c451404500d43ca040b139101800d4144950300c1000245071500801c44041310b6440800000140c45d114458100d00030031f50055134641602600a054011f4801103400e94850304140c00309850350030340c6540480c0d01a109004080216401c1a003502800344125410700f10314004090003254604180c4800b12a0410308403000d280304401003007500d40714814444a001000e10f10000d00c0b401c020b40d80040c0203d14580c4040d8409030711b848040e42c2030361043c2c02444a01e14060f01d05a912030300e40b42c000002140c100c5003581c02d041c4030b94412807041e1081c410103 = true := by decide +kernel

theorem cover : BRFrame.Cov 573201438 573381294 := by
  have h0 := BRFrame.cov_init 573201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 573201438 ≤ n) (h2 : n < 573381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
