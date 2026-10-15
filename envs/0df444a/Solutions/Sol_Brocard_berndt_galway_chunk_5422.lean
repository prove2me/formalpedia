-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5422
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:48:59.664305+00:00
-- url     : https://prove2.me/submissions/e2303731-714f-4250-8704-ee0cfdb82445

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 975000000 ≤ n < 975179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 975001250 1250 975000000 975000023
    0x102070614190b0102120c0a0314040602070e0603030c0a0b0a0515060a030c021005161101020403030e060d02090a030b25020606010507030c0f0308040312051302100c0609 75
    0x800c18148110101105a0303400d40105181000c4041c60354a10b80325408491a1101c201903081e0f4002c1040121250100318030a450b8070400030395a80e1504804000d230f0019015000031406400300700c080b50140c3d1a60f40c0a03142940c01c09010200c810405820030350180f004014100c0180d07400e100d542d004510820312100b19003020311072075098400280c40c46100d000c50480814050760f9440c2282da00401c0780c240420a080454016400c280c2561106c480300d5080508004074814445148211002030341c0390412800e140310052401c0f80200e0000078045000c2180c040a6440c00f103000c0c0846c03034890030b0301524185401e00400d01c54059540b00300c401c1c2e00f02d042070225103007010410201c008a0360400c58030340483c683c8020f50310000648401d040c020300080500906101b90080c02c0b0071900008510359161441c0307002400f200d01102c4c140c5c006050007030f24020f551210301170b0074050040e10044040407400d5408020a82d03a1040c8208148103c0444002c00201035014441c015402540d40c44030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 975002500 1250 975001250 975001253
    0x80303010e24031905100504050c13151e0807080d141c0f0212010b0c06070801150f031d06010302040c05162003030301090f060e1e0720010207 63
    0x75408a0800d10110400d00b4086001aa100090402c0d19103001510399a528125030600b83c0c1098001d4802d201c0780e604000c1080103000002440c07000f049410740b502c0c006203d2500008040301c0741c091400c40b506155460400102c0c24042c0510b0955081404030307040669180c0040f8580103482d80100a290000208078004540004090780c1c121145c85906240540100000c810038000f041c24151140d9a010f42824209450b410b036015071744040e075608610f503101c2c07004134600c0e080700001026038860f4000103183d491060007864101d800408003000d4441a0f40000c4c1c98146d000e4054004165807080d04d40740030100481c0705414554140301130210f650550042c4029591102c0c0d81c582401801c00403150100310b0b000c01e80c01711035033119400040c40900700710400582c501122103a07152002000204851015034840755140300d04078010010a6598135400d42182000c90300046c08140103010f00610341c0084280035440201440c002003814020b0414582c001c40a64102d08aa940401e00c0d20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 975003750 1250 975002500 975002521
    0x140901080c072316140d1202010b040c1112070c0320040606081b0310170304120305040e010f0f05060d0e06070c031d030a150902041a091302010203030606090a080303010e 75
    0x1018207061000c1800045d0440041071070f61540c00030041640400340380d040100c078401c0d8401e42400f4001002448050062880180385841c4c1043e0085a4014030041605030391000e0206c3d8000c03540512100c64092450b203031007011300101c0300340300c0198110340c0030340180f542d462044001400098a40e03206d00c1c01c1c040f071801d040741a0071071290f00340a010424010f210204581034421924046040450051407011040c1540240d41c08091540c82070b10140081680000141065a601034140400ea03030303071240300703503000101486400f0485104040a226500f0254002c01c01c1170f600c04000b082e00d91080c3c030b0191404030104c40000028003403603281410194080059110341c1c4050a554622a0741e0304c0000380c9400c000318008041484014104070b441d5000d40003c0c40e040d40040080000d100c14501c4080a0303072045a21a201d034007000700044801c1c003146003d940603601a030045003035079256018440540d02c1004c04075032007416000c0004444c2c004000450181002d21050b00340c078200003040c031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 975005000 1250 975003750 975003793
    0x30f0d11070e2401080403050405150f03151c0c03020f0f1306080c0909060c160c1e06020319083105070e0c161e12140901080c0723 58
    0x3da040180400074080880e602005640958004443c451126440769101d02c405201740a150b042c502e40100030015101c0b4080c5104500a0044d2021003901b0040c6181c40c0301035081800003407002c12242024405818851a0402041000303051580c02d80640000650382d01e04c040640c405043e02c511091181d10340922074164038000c02e44014415003000d089003030300d9a40062880d030ba4040003142c414054904244150f0719150001040f91105031120180e0300ca0405240d540416595007400010780315200000702c0304611101890388400c040b07412000c40b4651030203000042c1d80020b83c480c9800381c00f001c440c010013180703a051058640c000310b0310700941084d819038421840d92402c01d00b0030110021507401c913000303480f6000000905c84424035210008103501555805007400c4080310104000000481d4a285041e68895015040c240482c280301481807000320350004228002007481360003403c014240b041e109440311000c03c1c1807500615014401c4140c0c1e0000d42e40100000c051844248c400c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 975006250 1250 975005000 975005071
    0x50325061a03121c0b0402070210080f1b0a0e0a1a12010f06230d050f061513060302281e03090b04030c06110f040e0105030f0d11070e 59
    0x1420218144240a0f00c030300764104c0c001140d0384a5414607042d0b500c550440354142d5004200064076404c5800003411030200322203810103200b4100204901854403a150620038400e20800c3e0f15181c0440002c480071905241006d40000058001107615144030b80404d4104041074440303a140c83c408640500d0010042c1d00c243c0d10302150100a000c3c950344120201101c402d06105000001c2000013502410f104008001f0070b00da1804003804060841100c001d4040c0008440e0003907080314105062441e441161502000460710380000c00110f40280c015040c0d10f456608001442290054070564130b12000d4143c0d00050781210644025420740c805255400c041803804004c1c1404683d0740d000c1d41070025001800b408200807982040054541103000740480407038005403105444142440d16400030f0040200544001c2c1c00400da9042c00155031656920540041c0b0310f04134200000e4480d800003074446501402106800b08845942040c510302030041d07000c001e07140c01091420001c12200e280d80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 975007500 1250 975006250 975006283
    0x204080f1b090615070c060503150306160c05100e06071404080709110c1c0e0103090b010b0f040b0309100e0102070f060b030a060908070c12050325061a03 68
    0x55060745445448141d030b80010199181080040c9811448240f80200480248082090500480c040b9407000c003031402181c000c0d00d8141003290580400d6280d5804071a2120381540b2985890b904501c5501c0002510f80030328296294111100380c1d1710291050854114040d5006030300b0300c8038266003d10403a442c0360030b0a0302a41450700b17010725a81c07034424034415103161988602c3c0122200140707500301c550180000c0b00700e0310203540d500764400080e0041052340000c11820036840c0c105500030300840100d917a01041c094440d03803c0910041198101c0406030800c2d4805100210750107410a0046001d54141401084112403c082072001d41d03100c148860072907401800304800042e400d041918086030300050225403040103002282c907003202904017422450400500009000c0300e14020a4000c1c010079440003002d07100c032045411007454003001007043d07008108420403664020b070344001c040d1219900c1012002207480740303030179102551259580e00c8046582c003481450304110001040744120f1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 975008750 1250 975007500 975007543
    0x180a09020c1c030914010603231c17071d0d02060313031106071106010b0f0711031603140c030102030712051509091005071d0609180c0d0b040b0a090b0307090204080f 73
    0x40d4803500c07812b07000c1900221901802c095420340303005410001071000404180307141441c0c09038006002c000c1c0c1001000d800000c030f0008821904180407103007070654002c2e24140c99a03d0b01c40c6906c2e2400840308083d03040050b0704c900384d440d0311801d001c0d0501840151b9100d1440300b1642a40c14102001a40043c0800303004100d5418644081010398800f281c1040188000001c0722001c2030030560714004860f003441805602000300842301454242c4400e01204907061b0402c100c3c203240c09c0744030960306c1e1400300d042c103508181440c0140e04002d511a680b0720784400ea200c0a00c002c00d164060690f10f0002d0b5403c10215141d401400c4e10401d544220740e0301e00100002001d01d500d25503400c921400f540120000540d03591203445000081c0c0c01c01a0300703240400103182045440d00d0a800620400342e45509010510a0134a05400360b04038a0600910f100c3e40b840c83d040c0385a000f44181c002040e0140030360940050031b02020710140001f02699005041c1450140765120f007400300c01c4003240e07840c9044d070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 975010000 1250 975008750 975008813
    0x315010903020a1403100509160f06020a1e02061903140c1c060b07030203070311011a0d03170c0d0605220c020a08180a09020c1c030914010603 63
    0x600702108031020341011364028640311000c0b07030034058190b03940303a00d03a4188000d01c04600d00019144404041184008034140d4075201c040c80864024072507070340140c3c00f100400002c99100300345509032031440480180480e03016030102e1400d4001000b41c00b40d22030404112131034190503004400000e40c1c58003461a03107103082c242206450003a03400c0d04100340f0690704d114900004962040d005004032624682d114144d83c03900959a80c04044200c0005020010f81c01e00140140941e10b101e2079510412020f00401500344281c00100d40e00c143c0c1000690a5410308003040303010094013503d16810f00540d120948030040c415650700c2e0f8070442c05600720b84020b45111401c44550070354400d2503000443d503240c3c407500c00c1b858070100b084050050080056040300643c5d0b003419100c0100415201d080104c1d560348011401c80c003078518040b001d50040d540c481c20b6100c030310030203100403059030034005440d14090300c0303400d0888201c5603030091581d07480f0410b00600c058181c5121000d0050400701d8a080b0f0034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 975011250 1250 975010000 975010009
    0x30218040f12020c0409300e10031103070905031c080402060a30060b0a0f0e13090501020301030506090102071509111203030a05010807120321020708031501090302 72
    0x10364000e00500382c50264040c11038400d211400d00580c0003003007072141c13103100e04141280c81080101100b00e8404030f52440b106100d20714686000c003100380c50b040c13a5040048217109048000c02a04802c140c1c5c0c92044000900300e40014500408942d5910b0f0b250310705000900d4070b801d290a12089902070844008015282d2102c20540d010340e041e11040d45503118002d0030340e02000b030440c080d141d02a013900d02040c1d403401400500141d0400340018010349a641d10144000c1c46030b031600000255400d109603503468000c0301003884200c409400405044080f000520031604900401c5039142d40004c010810302c242000400e4000003404021450400144c1e81c8040c0240000181c00c00f1a44070741c0503405100420400b1030081d400901200e909801d602604c1d603c03603008903400410280350400209441030f00241d04c100361500d00d43d80d0130004449440a85104034507045800340448a02c4111403212042e001900f40a880341441544900303101640780001481d1501407410000d1244040000da0745 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 975012500 1250 975011250 975011273
    0x1020c10030b0402040b03041208010e040807141e01020a0e150301030b0901060b0d02070201032003150a0801061d0a052202030a140c030706020115171906050103021804 74
    0x40d41d003000510710070390201141c043e02a95000401994002c0104414003150601d4050328016a65603d54a82e888611856007403000b03507400342c400e5000f408407000041024094240d860001801c8481311060780003094052100080690b20594002c074034142460b4002c03000c030318001e0040b24000700d00541c40400601c54001440082c10108034000070452a500c29441a000741010603481c9a482e1490001c03100654032105003240040e103410505180030344400000400d555090080c2e620790b4685d09581c810721400c004181354400c0480ba800540c0300000d10403031004200f00b154142c40b80241c80600c00910038010483e040150420007000140d2101035071485070a04221641121078134a030021a140c0380c911070006060304188001400f12a0000900d40c14010080381147c2c2142c0e201c1c00c08074280c0b002802804035036290200113014110815400c00414205401214016607110180c40c00070071340c115090301e0313107030303a400c014000d43c2003644082c20401d0402e402c880003402d0a507600d005500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 975013750 1250 975012500 975012529
    0x150903061b0717030f0f09150a0e070801141807030305070c0b131502190b0402010215010b03070305011205150711030403050615040c211104061d01020c 67
    0x40d00300c000c007000708400c1564403803600241c0810401007140c1e4002180ea2081c0c4000000100d074000141030036060240d420311903051000901004c0c2e02000b0b03880540c031800350550045d592654180d81c049601000210000c0c0106800460100e050098400f003444002e488880344c10000c07480b160050200081e841d0840c0c2d03151501c15960307136060520103078404180d04601c203414000a040f44458040481b03200136203554400d24103c0700b01030135050f80d0310340f0141080c070220202c580d0b244000c1602441c40c5a40300d8010700540d00318021100400940314002d030010091483d021040c0581c482d4184141400f420280c0d46c0003181c0c0010751200c65403029890b481040003d040760000c2c0c0d045104151280040f4088400c0366200c82d120b1602540381d10080740c49102d10010100c401074907203840d010f2116500090f031900368102d4061074060f075441d0980c642192000d5111481103504d5035030343c401003004102c1c0c0d5807520001d403441c041d28009810301e41c01d82411548900c0314280e0a176102d004004601 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 975015000 1250 975013750 975013771
    0xf0601060c030e0d03050a0206010e0601120207080c0105130501140717191a01140f030f07051306170702070f060f020f01060609030b0a050702150a02070f0c0515090306 74
    0x2801442d0444620100b031515941203036004905a041580044c05003125002d0b503000d50310a40e0701c415603410441c0c3d00311421400180181440f40050f0040c0e13005100b030398041c2c1e821340c0ca46114604040d080d5031054448008948090b01484c083c08004c3c4034443c0040b14441071044076040c0040020442030070362a12501d07010000010608010749072400c0e80c0e94501000007072000300c40042039400030150780388020f4042213820074100749841c24001110965070414000c14110303100d15900112103c00280b00d102401010028034480c4c90341d101d0020003c00503030b511107040f500135000c070f1000700c18090000e50075075002c2c0b041841168980e0303440b1421741d00c144c9041c10300c0d81c10a01049103003071840e1111000c1540780400c0420100c1e400030f1a03e060700d000d00b10480703a58403918440c0c012101c003200d8810043c5c0011021a425001c292080c0d504aa4108009400c20070746440b0510340103031000381110380c60340c548010003603070030041c1c01d103145110f00d004980d061124000c0800d44828000b000d06140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 975016250 1250 975015000 975015017
    0x1c02040209060708041724130c060810061407081e030f0703111c0c05070803090f0d0c03020a11010c023003040302090402060f040b0f0c10050705390a02120f060106 72
    0x2084d03048c240200041d810040f001450395a44c0c102803e4600c0c191214017600c0350204021070800e00500407011484000c040039407400710315444180803900a991007010b007060b04207510001c0d4000710083c4d406500e85a0251400d400c1100c00a0111000344202410300c000c00c1c0010300315404054940090f01c1d880300d04c00b0a1009641008513480c4c411110024595617004c001e101c0c042d80002210303003400000c0c004036042e4441d244420f0b10510b12003900180180c2c01000400d00040c0c1030ba40c0b21015150605110700f440815600183d24520000741c9080d510900a90400820010380030481c494400640610300d003d066801140718101d000744041d000360000524004544100d108440040624500240c3c4990b0644654040c9500810624845201c2d0180e0a042c50341944601030044a0310f0300c8072032800c0d495049103409140e0100410040c0d1048802107510321601c2000b014003046081c018100c0c00d441c602c104100d400110034009804d601600310100c0e4940c0000750541911040d0900c4e268 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 975017500 1250 975016250 975016261
    0x5805061309060b1306171f0c0201150608040b01051219020310050f0411090f07210c030b0406080309030c01201506010305151c02040209060708041724 66
    0x3074a03d4003101a0040801da018001c2c13059a50b010b401614002ca2071400d0318104480d00310380d0b41e10a41ca000200c2082910103040e50758656002001d40040c5000118010311900c1d03200c07112100c2c0d0f500401c0410051000c110400664034925409407404039980740709440306048956407583c00f20a03085a040100c04540159034042107802e50f801c0311010f0070b208a01d0701c0c000340040c0316000d44e0100c540400c40118000c3c21b1a0201426109004060849081d503641100496591201061030f148001286c1e0105000300005d000c1da034062501034601040c689a00000d02c01103034040d9004101e0307500f06100c1021103650129050903607078002d203082c80d861340c00a1000224400240000b40040c85403030b080c900902c2c482254a4800c96007620100215590907000c0c0031150840c41c0f0096001c0d43e502e840104410000156400c00b50015000604000450000c02d0347c940c8080ca0a44002c000801c0400c0001180101d000d0301f01ca40801402402000000d0880a034488070b1288100c0c510b0a00004d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 975018750 1250 975017500 975017513
    0xd060c0221180109260601090c022a0409060c020c03030903070509060a0f0602011d1c12110c011d070311010305040215270301060b5805061309 63
    0x9840104c550f084010000e03c40181405c0611401c030710103008400000526a41030f00c21100b4405054001e4134001041144560310400303800b0241030340da42101106000d0361911321940441c203114510000b01500e40e1580a407802c01c221030702510940c4100141101900c1c0418040c08503030301a01d0b04260364840000007450f0903c10b801081d5210000301000840c183c0c1500040d07007040d11000f55507002c0c0c1008203100d8680315160703c115050140b425256000c580301d01502600a4904200011401c840001c200c6903544003050200041c0e442c1c03c40030321459000070303400d070f800300030b0720018070707240e481c56942501d0302000c0403000f410f06580700700150a54584540b00100d03002a0400303241d54040b030002c000c909800c00e6001c0c140b641059060140c09003014400c000031b03a802e4a075400d082c1280c0ca000c800d00d682050051041c98a0100400811961001840300d820b142921024003c0c1004541d8620092040700d0715031011410700052104070b0300c0d0000042c0c040b602c03903100410303001d44505140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 975020000 1250 975018750 975018767
    0xa091802031005010303090b03010b031b0f0a11100501030b160e13020a1e0c060905010b040c2c2d060a11060c040e1906050d060c02211801 61
    0x40e4241c02a81e1400d00b2a03980340e8051816039110362521b414030758a441e03030400d05001c03d01581c82c4c800010030125500006c940302c0e1407404d80441d60344038a40351081220082c5a00701d501d400780460048450012241000d1101403210900c0b00410809036166480701c0b80e00c581c0240000803494580c1392001c03601440340c01c007aa60208003404030400c040c0804a4003000b58000880c15001606490b00c0d0f5080142442e10603d4000c101c2c0c0e561001c480d030780d0311900010301c0008002c039055075803a0342e00e84044d1514002c0b4084000240c58225500e0034654182d0400c031140e00310b032146480c50071599415682c5e00200844400f2811203003e80d00150458201c0c40701690308c00c0d03503a020b20301051600c44140c1c042095509901d80d0400c2da816170711341030381c0400c01e40218003480741000340c0c0742c0015458070f03a05c810b100f002c0d12040307001207109a038a0012031034181c0440000c0c0d541c140c554001c0144d1940401100041200c03910300024201500e01d18040140a00d030070500c0841f1031203081030050b80c81028003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 975021250 1250 975020000 975020003
    0x13030b0c072910030b1b04030b09030a0f020106030c0312020f15100e01030221100203070305160f0e0103050c0c122d160303290a050a050a0918 63
    0x30420716041c1401c1c82079000350011804a00380714880001542d104451240c2004c44e0750041040007030741c40c0c140c5650b000828000100511420a000001c0810380703980704c840c046c42031a0090b642d500f8007468020710702c518642c0d003030040d681051010400601c0c1c2005c038104698000c400040c1041481d10202d0038501c22080110880c401c807000080e00328020076800e409482d510303890741c10b050341d50500c90b0080c100920010b54062105000d00340c5855a000710761032503030240030503030380300000c0c104058040360000d03103002000030703591420441c2c0c800d05000b02070150101c81c1040740080c40d0383c04004098040c401c00082c1050748503c0403a20b142032100a03602c41c0940c16040d120b40c0c100e0742003a2982c40c2c0141c1030950810940000100158600c03048042c07002042100c3c01c0c1c07070800590f42e152400c10020004404050b9140d900401e840c1d00480c510000d101c010504200314410314003000701d40805a00420300c203582d10342c0c08100b15542d0b090507204454080e100803031075541620402100360745a150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 975022500 1250 975021250 975021263
    0xa0e13021e06071a0117060f07020c0a08100f0216060f02090315100603021e0702061603030b040c0e100e04090209010803071403040308040501080a0b1906080105040213030b0c07 78
    0x865804200c072090599101c0d404113500585a6a40c40208028900c00301801c212180c00c0900800d80100f902d50341d460307000b01c241c0101c1d40140000c038003280116005030700c41d030126080580c00303100e4085a805005401044da00d000d600301051060f4914515100c10700083c070590b501c1051080ea844550103550814034020305071080c2c900040c9448407a28011206d000311244c3c2c8050106190303000b44259030f900d0000c45c0c00049046000841c4071016031010f14140e85c442c0c2c060102841c00c8000c132a444138418881e56000c100b80c8890000d10080d16030340040d5400340941c8114070001502d6010f810000b009052801c510105c0c9140085001442e000f480a074104c90080004075550310000010681a8446c0d40c0c2030044503500c4201c0b6443c0d003e1808010048a8204000c20140d8850f9410300d801c041e0b0607000207071001c90800060320201a00500d4041400f9078502000030703d4008003842e006017030603102980b502c03400c06001241142c4a00009149103410700118600c68150717002d80d00c00590100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 975023750 1250 975022500 975022507
    0x615050306210c1318151e02091008040b070c0f0503030c03040b070201060b0f07141b01031104142112040e09150106030b0607020d0602090a0e13021e06 67
    0x100c01c591140320f1640440d00a8601d02c0f0290001d82052240c124505840403c10500b1030361075442c0040c542818450021058841c20b6403000400307041c00c6c40101211080c00165104480c1c01800340e050720703108119041c444d2140801000c960b414140c0d03640807501c0c1c68001250309403840c01500c00011140041c0c8248808410040040b941c007006501550040c4030754922696442412070a0720254011000e0520050091100ca000650040c0c0313001440f504081030300304503280f040c2c0d192410441680c400c8075400110076140396018401d022184850901041c60103040001411187c0c018050140c007034501b4081896100d0a424400c540503200c1c0030507036003c1b90640e581200c803a040303070140c034400c406000d01280e500c0d00d001846909411404121422a03803070a00180e0040660120139030300108100810b80040c3c0d580d10608595030b1280c50300585030160441802980d000715000700203281046018450408121482a0710055045817061800361041615002d00c1c1c1941450384c0c1c0010703010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 975025000 1250 975023750 975023809
    0x20d3f150801090b060d0c03080a0905100903023f011b0c02040b0a0510080603071502070e0601080105011209080d06030b0a0f0b010507020906120d020607020d030615050306 76
    0x190072129140313000e42500a5251919000c0000c0c2c6208100010015806000708100207640c15000e06a00d85141c2010100c4950300c00100c0e145003407260701c540c00180b000c9003c0c0b045140c40084609000d606003c000512070940e09640c8180468030f084011070382c0c03a0103069440b0f120035040380c0c440c00f15003070043c027601d2191000640584480e030300880c410750810341c0c501550b0800e003d4200450b10010038203401050403c009403a21340c40075000907090b00038000c2c00301c0e1094210141c0c0400b03144a600401c070707507031a1040201c082036011340514100903070036004000580e41300390542c81f15020350034005115121494900001d10690b04038042c118100f0b20000300b8000003a0b080e80c03207007205203801c1c014400500908012154000500b5020440a101142c00360506645603070340000e000d4040010b01075040182807401050f03640750700050b8809001c0250641e41404a50445512d2f400d09009090a00048032000c4607141c000e002001004030014015986a05001c10018890b000329041c44410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 975026250 1250 975025000 975025003
    0xd08090106032a270509010603081809060f030d052503170702010c120b060f07060203040c0b0903030d020a0e0a0e060a230d0f0b0106020d3f1508 64
    0x441d914800c1c07440c0c0c0c3d5103001825040708508a4286148000d80341683c0b08402c0b10107000b004058907a110940d43c5102c04070000796400010468030001c2c8020341e80c8555880104110810300824282c0604444c040c030204989000441c58000d41403030400d291543c3d5403030b2480301c42180c4088800303055442400c03072800780b5400c241d01c600409600f90b840c103800c4e641c01605a081c2d8000c9540b00300010850800e400080c1401d41c00340d45101001800d552401c0320701040030401e6007000340f040e01c03040e1f40041403008001401081400410040102c0d82c103200140c00080c0c3c5074005c1034503800c0465000a840d24081c0d21030070001c200324900508041006440700d204211030712048407980d0296155010121300c00c0d80030b01041a10f60518010445505414814000101d40c9640201d40c0c15260031080d400103403c0e80b650307501801580d0700404003d25420307801480705000c042d00314601525100e110103100f4040e10060991620070741c1480f000f80385c0d1088440200604459107044590804000c03441040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 975027500 1250 975026250 975026303
    0x1c0e07291912060f06030c0215010512070b180f1c08180d051b190b070c0b18100e03060a0510080f0c0406090c050403060c091d0f0c0c0d0809010603 65
    0x170142d40810925a00080603a07507000d12042207000314031044010040782c42d00044c440e08010380710703081c2d0b508e1ba03946000c03c8149400607021000d04103d42c0124840314104084c245000c02c0d01140e03440700c0c040710000280030040454001a0400e030001408030340c0700d4120b2101000c00d0300e01030103c0ba909840b600b04213880300950a0341e040d16580010201c81c0a140c0b102421036150301e80c02c1c809c20300703601d0b0424200807a844800d040718100b01c001070000d0051010805085540701c480030104a440314502000680c0320b070030380d8030410700ca2a10b030303854055280080c926901c1103c0400014041c1c56145c4003d10b80318a9038088a424402c40503d1800c1c50700c0880e20303269803007007958180680b5480c4c0422034103492000a51070000380d030a0004002041f81c80d00f240c0c20b00c400c3c0b41031442c01c03d51115140c648112000f0315829070004440b051103020030011b0380c00ba600c40250070722681803012a000d000c1c0c5170b4091421681c104900c2c0000300e60003c10a42c003035801158040011016240b00d0618005184d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 975028750 1250 975027500 975027509
    0x807081e0c0903071a271f02060a050403200f010c021b0a05030a150621030e01090f0501111903030c020d0914061c0e07291912060f 58
    0x140c81c0300000d141707144031203040b9031040ba011603d0601042c55410030b24181c660400015950100ba071030010780e254455886070b24000c840c004103070f00c44543c1e4080d28022000d045d15414030320300001c020100c0da00c020506104502c503060034950303103014000300c2d2038a05034414824040d40b03000300f000011500040d006820b0310039280d10580840251080010421541c407078550140c00c01d95401c000a00d001c003403640322202003e000070300340780c4540e91a428000407000341c190140f0407001c8007041c503800030f0301030300185024644140040d040c0031820a41c240ea91207258144102c10078516104d01080c03194510340d00740b803481440ba1b4251400c000380070308940100040580504215204094400d4000c0010340b420003812009894419007030040760f501c60402c02220b5144214000100426030242d03001806005008012041c2002d1b4100c405060780c6084006042c56103d042008038a0903050768028420300481c50840600448107642f903100522080364014508500032520002c000f0180c0c1c20744 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 975030000 1250 975028750 975028753
    0x201050904290301060806040b1321080105060922090b09070923070807050f130e01061d0f0a03080a0c0308060a08150a0f0c0504031209060807081e0c0903 68
    0x5040d200280350807107174a40a0301285411032000600410805241190041c2d80810800c0204401d034841c04140c404040041c1041c145820040c007030568481440d901601d0101c903d1882c1c14198800034070b440d80e440000c0c1034613442ca0840e010020b080c991182403819041040710780c447c90134000c4d06803100098081d0f05c5d1082c0c905081085031050303c482126171811180f01c601d200341c4802c64155000c2e035004080c0020000704022006c3d074103c90001400061054400c034406041c1801c040c0282108160080000c2081302018103114214501280300d00c48000d81c6e00d220ba1240150100f0855100e540000d00340f000005a10b5101681c0520306496190190399420303900d45a003401c00441d94800d20401c0c00c0c03980403003002403d503ca103072005030f000407401c00006401c080c5ca08400d030542c5d1a100000380403401c04941042030001c0c100c0b210200210524041c203405003041400340111710047c000d503080107d00e030005081029030840c003140c0203a889840c0c10140c5804110040320f5884031107000e00a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 975031250 1250 975030000 975030071
    0x50f10031118040c0314010b07020303160302060a1b1d12070602150a0911090601030b0301050703060314010c021504050a050303010e010302013209010210060311010801240c0201050904 81
    0x100e201b8451a4085c0000e24003d540381d074a0002005401d401424007a80e00d03010412a001d000c58800d20482c0f1824840c0d0040c01c0507107409280441200c0100d0350000c02891411b401200389540701254007014034070b400307420805c08002004208006c0120704640d680c0d2141a00c00b086150700007985842207400d20101c401c2a5885a41c000144d444130b9030300800c6503518a01c0c80242d840c040c901c2c0c603072006041c90b000446e84501c00000c1d080d103a040d00c0c44808281e80c0e800601c00e11029811140903807000c0070091055104000c40250380c0c80c0c807940d0f01c07814244100041010801300f8480018029001421680c90b035848003003450300300e0000c0c801207000c118900900d01d4540703018041106c021a1a1820800182c0e05d8603044105a0100d46424114043c0ca40e404c3c1044446104846c00340d1b0003202280c91000400002405040c07041c1c105c0e8001404150203028000b09550340b107258042103140840c0030f030200d440140d500e4001d10f001d00d0760250402c900050603401c0744483d00244207200c0c1d1400e06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 975032500 1250 975031250 975031271
    0x60801170a21020a02090103060e011406100305060102070f0f06090918030e0d05060f061801081b04060e09280213181a0f060901050f1003111804 64
    0x1500c11000000400c20504650040d4001420111500d1121103e0040d24243c0160340d001030740c0c02c45c0036041191442d80d5505100030301d51b02403140604190401c500300340541010f0f030005040d0700e003400c0003008040e164000100380e030744240708090007080c2c10503a400d0403640b10103051400c0b03241405040e00066041c040082e803030341c0310300072009049031900320440125501c0c0c400700c0e0512a0361124030b030014204088080040d0042041621030b0145482d030403058200182080342109007681c428030604508801400b500e50080b407000c002c000c8007002c0e0139403c0340308800315001c1c0c05030754030219601d60004204150040d000ca200c4040c9150b0b004184081c001080754881c80c5c134482c42d40650800d0700d032000d200c5a58220791007904074941c0d00901401c200301d603a46262050b00e04132107070001c00c40007109105410031075a00c00d070b0300010100c682403015818900845c03030001909400a128070b0100c5c0002c0c059a020794014000c1c00030001d034241c0d4800c100110540c00b0800d5540290040d071030b0001d4a01d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 975033750 1250 975032500 975032503
    0x70515071b1203031a220501091413050c0d0303050411061804020706110a020d0305090705060307050310050a170f0d0203031602010e0d090905073b0a06080117 70
    0x1603902c441c24940c61054251811001006050031402da00001c003980103100765550f141e0742c030b0944011900c0029101c00146054240c4206034041c2da416810324a90300108003034118081c3d0300c10488002104400c1090034070070301d007106645c0c840c0d40008041c07100c00c050550541000d881140260101c8a00c00111010b2026074456060000e44e0548a812003099514054004140c03081c010440400e842940c07841d808200e6200d5441c801c0582d025031415029250140581c0394405810800391507407501d4a400301f65a48401401d08081180000025201c040642c3c100d0001d03001c00351004581986501201081c190b0320755191145100f050b10041120b04000f520300240c0c5e100d580618119190520660082c0591840d8031040d03540714011408075000410200d6040005a902c4540952801c050300003110800b5219408010001d0b0500c2243e09410800103c1040072600c4407900c15481d10001001e488003a854a9024002210009820354000d00c40d9040e0f03101903a85081403600300d400e26 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 975035000 1250 975033750 975033803
    0x12020d0b031b0319031101140609150f09040303021303050c01120e1b030a20040e030703020c0618090a020d140f07080c12040c0623030402060c07051507 67
    0xc0b40d159002c0c0b0262458038060702d901d80403042c840d00b419561a001c46d401d0074203442d207038030f0582e07605520362080100c10b141103e003481c1c203c1000306101d0340d489110400b05001160031342a1501511a05003c5820076100b40c1c100e500603d4840c0c8848225a00ca14041d80c8405d00d0000544c00141000e060b411440114406d10b0840c141720300c000c02e100b054607001c0350a1801e6540c20700e613141c0a141d048401003041c0310f10070301141d0800419090824100d004100072580401c1c8600c1095000340080703000203400242800d0040c1c0121803840e211f06c810551251070540c00c4102c0740c3c100600f10248000d07001250054010030350300240900400400542e480201c0008450480f85440d000b00030860080c040e0102a41100c1800070342407070050f04d00000d103609041580c0c12940e240380348004100d01a402918108400845901104440d0700341d0040000d0f404068000781c846e00b0001005204054104401030051a0141484070388440d10302070168990040b913016911006405034040f04248610400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 975036250 1250 975035000 975035053
    0x31e1b0a03060b060c030c1c1d040e1c020703170703050708090a26160f052101110d050703180303150e0c13120203070605030712020d0b03 61
    0xc0280362454803800083e2980c42c0c290398100c40d080003178450b84002440100300d0f0340c40301030091550410214420034201c4900509204004203d111400d40c10080c0140700c107815001c41d0081002c0152594450900320024044001c5543c0c056555000c00c0e00401e00034200c2e40a4100c031380c03214896588600282c0709000c4003e002420801c007040000c1d03619406440c8021015000da01c0090b22071108540055510f40b400116514240c1c040c5a00781c41001007000c040f2569a40b01803a6140c200c0d1209800c00b98042c6903c02d0010094141c0c034006a501130782030a49001d0028001ca4105040d40000c3c1e030300c10b040300c241d114100030006e401c442c001e028600300020310294268080c282900e04031300500d03c0e03081a88035002c880711b002800e0036840c00c40f540150881c101e01a91a40c8250905d0f19141407680585100d8003041c1507280940d0307010803403000700c0d10741d0b05025640340d440d001c2c210741a0300c003000101c610720700c007041d030741043d110f80c1e80030301142c8000b07500310345406a0000986911020a142 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 975037500 1250 975036250 975036259
    0x16030b0307050d030503040309050303120105130605032806050c13090b0f15070b090d0314010b0a141e120a1e0e1f0509060c120a02090f031e1b 63
    0x3c1e040005c0c454001540c4c45070107441d18114132a15840042e045070321031800300c074525044000507c0f40345421003441d145545120001c1011900d00000b094840789204603526000001c4145500416032880c580142c955125108000078504590024442d800442c01032031002402000030414505a00c02d159260b540100800400e005020030030a810310103900c0103c001c0c505010303140014030350703c1c8400c1c0124020b8000c6c2118450111008003200c090103c421480ba18440040100141090454a0b01c610305c2c5440e001138109a25070b100c4922401031400c0c1c0b49030f50f2030b04181c424603c201c0641000c80e201582c4c4807a68132451502015254240a006108810010450b0500e0003590010b030300100e29000781d41d03100c1e078007220081c030181891a4045c003440c0c40340c0401519100500a0940c804003491f0041e0614603110180d11000708000d00f10001f056000030702c0081a5100c85605034140350085c01c80b10b603281381d02460100200d1500940d40c0602c143c1030f40c0d44c6440107003c1c070b1840b200320160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 975038750 1250 975037500 975037519
    0x1104080609120f0f0d1803020717010b1309050f1203060406060f0806011107082d0303010b0a1209021c1703071218080f0a02101401091d0616030b030705 67
    0xc9440700c658031180c02e0081c51940e494000b40506c42c440f8104004078026005011074038035145102c83d0300300c4841c9007103000303074035103109441c1c50343d9055441d505944141c040051000e0700c0d8540310f4904040b1400428580c4280c04060132107161840c0158800c44090320f0030b00009980d25410f80b044040140480c1c0400d101100043d074651103256003500680d03148088504103981c5000550a12403c140180e085801d105004040d00c0c616000b0010500407000c0214610340c90700c4ca40ca01d00d80144803c980c100401810400c4a41980350810050f1a4008050034020b46102036000c400c9001c96004031640030280003802540c200b00b40641c1d10031020783e00e40c819000e42c0c111400c0001c01800c4010704840950011440105860701c024105881c370f10000360381e03206032002000c0d14201c3c800d00c10030251800c03c10f40411680e525075040341110789020740407503082d10603c0c020072034150340244c00300342c2d1041a04100498a000c0d2841c2950003058a08108044160341407680f200c00d1400f030142c0080084 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 975040000 1250 975038750 975038767
    0xd0c08030601022109042403030507150501060503060f0901030203060141090129090d120806010f020601080607080612010c0f1209050a151104080609120f 68
    0x14000e6a00410510540d01c81080b401030b100c0590b4014103500d4900c681c0890344480c41e00f01841921404041081550700003401e07078040c1100403000307000003000c001001c10341d07200700b000c400310425510b80203240c1804190303110100104141c00c11110310780326240c0c0607100d001ea810002c05141c1a2030300500074242580c2000d0f41001c51001c855000040b190524404c20040003c0c2c080603009410440d01500320142c4803001c00118101c1a00b0000301c49510540300301807604800c501d80144240f0601c40e07602c400d02c1000152a07003a004c0702c090318010702070200c40c0c1c0035a1b000d88004d11582007621100d520365003108007280e0307442d400d002e0004264400008508468060000c003940944010412105200c1c150350481c259458040d085012846221940d2a445d400400c801d4182292071010450035980c0c1e100c0c9940c03005c03c1c2c3d50152203050300f40d450201ca10032542000104e101c034004802e03907603030b80c50741d00320759602d03048641e10910301411680441090480044070056847c18032100d081031800c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 975041250 1250 975040000 975040013
    0x172a09090703050712110702120613110d02130b09161407060b03030d06030b0a1b0807030f09050c1206090303150a0929030c01050d0b04020c060f0a0e0d0c 68
    0x3500b25400d2100820a00031000154021b092115010042c01d40e20b4020380d01c1480f44139800e0311f204075026000981045900c840e9209410800b682010140c1078001401c4017207241410f81440203900300100e03005180813881140c20825171800292084210b40d5200318820640c00305c01e003513203c0003608a00c28545400c8031100544406400f503a80090800f039035600091444d4400440003011581f03400d0704000384640500c00c552b10840611041c4843e4841110007140081c11124220038803020f00c01007886103100f6400141e04203001c2c402081602e034241000c998400300c4944242c800e180302000c1d000c00308030109106005546e000015421903d50303401c10041602c00c1070850390041c2c4e6081001074140f4090180c0c8140d0074485140165110041e100c1061a0403024049802075000e510444c0c078a0342c0c0401141c800d030300445400550404400c000030042c0c46a203181c012903100d41c20912155924410f0b840b40684a0301004000780f5507a40a06a00c032482806a00d000c5107a51500b480400d40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 975042500 1250 975041250 975041261
    0x6061206150408060405061b0a030e011b03020c0709060e270114040b0f06030304090f0e01152903011202031e06160201050408040510172a09090703 65
    0x4010104828440c4101c040103641d0400c2d4400c1c11503600030800e1200b8040c00788403058000e025654010046101440c9000701442144c142904255907039940103c0c4010039800640170030903000b160103d00194810003000b940040c4918034803402800c40c00622045184100f10444200d50228031565496400c04a0000c43c020000030000c4c40318040081c042c9400e00c039141c0c0000d510961008282054148044080c4006103071000550b1088148629682d0000696040b0f504003003000c600d2040201e036180c00f81c020000c81408175800d0240401c11b040f140c102c0042544c0203100e0740816900d500017040300221003445000c0140d40c0800042c400503503a42080210030340043c08441320a5980a480303220803046400504007504402c081c0f007a00300301302e0745012520346507100902c000e0501c0c2c0c44400c041d01c5940308aa00c140f00d800307124901103024042411f118580c44500c0c9401313160140741c41600b90b0645040c180c0286062051030b000d0000a0142c660001717001e0100440f680d5450011b07802001b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 975043750 1250 975042500 975042511
    0x1f14090403050705150f1009050712020903010b18010929060d14040f05060c0a2016080102040f05040c0c0303200703030b040506181b12150315060612 66
    0x10365804100c40302d401004172809151440600c09644c5002c40300904012459000100b10354102010300c079401d03610000c9441d251001d1480141c4c0c88050b00002030043c0310030814203401c40e54400d02e0034040303010046098101c0c0d0254000340014403410510040d00d402007a03202003810032a10403150a1305002010707000c44800b601d00014018000b01040d030b00301c00d080358100c460a080720325000801505002c0c0942119144000c9030504030415030203060300e805001081828076201011b2600c15404001801c61030301c12000c4800d00302e03200d5607054041d6015001d001c1c0c4402c0c0c606000203c0303007000d00c511035441e00c895035034008103071040e82e0031805000f26000d005107542641c8042c00c1400301910040106910948000520b0592031050105a401c018442ca200b0321100b41040c041505101155900c010744481a011305440c00f8a6078516004070188051140c8a00c402c220450364004410114010220101c131a2110041e6100405030001c1301c0380c58200030180800e0785ca92810101c80d0382c004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 975045000 1250 975043750 975043753
    0x15071b032613150e01080c270907020a0501050f1b0c01151202131107080f0c0303070903110306012105030408101d15150f091f14090403050705 63
    0x1030001d001158214094120f01007220001c03004105241c0c01200b000f052079001e007400160307881c100c4401c041074042c07035102c4550841104150340000031402840c04030741c50000d00a6143d17080036200255110100701003140d01c0d42c604004200ca0815a0392590712a004c005414131290348000720f101d0b526041501c22460320340d00c421041d100250642041805444074000380001994140108070094841c0a40207a40f1440c01001c85031500001c0e045925050700088180e90321041103e065405e4403601a10f10701c2408007006001084d64401c0648045074024003c81404e080c0103020151510028030070009803c00c100c1040c1e10503000d8104c1100f01d18040e03c20f407800c084c2c0e2003003002c0c10705a041000d032159942d194240383d84000d00389104284241a0340040510010403803140d861a000540421820070000c113501c240e9503694040444600d0340130300f5000b100e0500d11200c0785203502498050000c83c4241d003002c207643c07491046028580c08010032046841d11a601d06591030b80c414001503030079 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 975046250 1250 975045000 975045007
    0x1a07050c04092103051f120305031003140601030b0106020c030a0b0907261e0c0114090607050109112e0201020408030406050a090608240a0515071b0326 67
    0x3c1c0320b4508580002120b140c9010400d0714008103100b003510403160040c1c2c1c4821013580c0603c40c600d01105000e01150380340c18256540d03200d201185207102041d83c0300801254286850307402c008800300e0401c1c104c9105880d8420140d881e0f803030907a1078980c1050f01c560154007030801c20b40401c80e202460740d00000f02c00142e800b019102c3d03a2042a610ba88081006802d2000400f0a4070810800003084035a0499158542040318140d25075210740c01d250007a4104034000380b0039030003940fa01003103e251140081a00b03030755003058941240a401c03a0342081e00c9070b0004610048150801d06803441c08031500c0042c104680400c103c5076140350029600b02c204640d4244004030701d0241c03c1004001030052500c45a8507210210002401c071710035500042d003000085e1003446102202c13034100c082088208004a0030104044000c12030f007403810f07442903a01c50081d140d07000c3c410100e1802811541d000369002040741c181c4002c808100300e01d0303100c01458180d5030f4184443c20700c2482c0320fa82c01c450300d10042d60314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 975047500 1250 975046250 975046283
    0xa0603050c07150f29060415080a3e090604090e0c182a19030b0a060c03091d070c0311072705240102030c01020d061a07050c0409 57
    0x12161411406500624145a070382d0b1605e1000c42d002110036401c4a01c01d10f0b06041c11aa000300c006d01c01000028007003000081000c003a26a0042d45001c61144232248039800d1027485550008207640f207030814a807040300801180f000e24011220110009400303146441d00d4810307110010024400d4107845402003a400a400341d450620380210a68880305180b07460400b66101d03c0027214052001d01c0071515008a0441340f0940b030240c6d48a0b100740c1c0302290110402d60010381c040d0035155541a4170100c880e03008191707680c2101c01e09290038000e6035001d84c229260360710305c2d48080080417140c0741c0104080015030b015103d2402e01401c0c84c4a450801c0141104420b40d41c94000160010820308204c6881100102c60000400b5160322252030140405e04102090102e510700129031420320391241034950207664000c01c00c54180c05100c02c001c6596245070070b13000c030091059000e54000544c0020403550040c0d071840544442c40e4200340030b002103240d41c804200042101329022603043c0d020703800701d42 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 975048750 1250 975047500 975047531
    0xe010e0c0f0d022107090b2b0f0c080f0f0c09100e0108070303030b180601140f19030c170105042c060901060f061209060e0d0e0a0603050c0715 63
    0x701031461042d062042c1c084120121810b10017907801c00d0b41e182d072822110002c16690000d40e4143c45800200030070070720302d461000c0b40080ca8080c3d00500000340040300c7d0030820508100b40d404452036034003a11800f2000390540e68031000c003840d00703441d00e0b40201c41614607460000115030b0440e04200282c4e14142d07880314080e02074003007640314405541200c4c13800c106140c0c043c011510701680c1168240340340c1e108070303004011800001e402c2030f040080101c4220018040202140c034001c82e003901c01900e0742c4905625031111340d145031016000a0a0a01810b8114080d00b41d16001500d482c207103a005a007800c051000602018400f590703000c81ea4100100c40005c80000520080500b038050a15442c01049003800d50751b1542c020724041ca0400801c0081a6200201005e07980401d030001c286c0d010107043c024003809285000440c1c5005004440c0c49083d00f068110841c100c095644100080d40d4800c25001ca83c0201d5240340c0c000c50400c40300d00020442ca0454945401003c40040e000201d00d1011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 975050000 1250 975048750 975048769
    0x12031c0b1207060306050f120d0c021c050703112b051603050c01080c13030308131208041401060e0a020903072106050f090a0b0406060b0d020d0e010e0c0f0d02 70
    0x603c0440c5d5520b04c2800707281040380304160644401d8402101c0e91164074441c0d651030360982d00900410030031051540440d40d442d01c480c085880c60112100743c1d12600c0c10001c2d207408040c44201c81e01681012030b401d55051005141480811151952443c01200444c10985a1182d402200d00d070080c010044141c000e0340e00041c000e1f6006400804445812400140034003c001d4400003d5080a0140c01000b8400e80520303c10740c0c0e810725101c007030341d111032041601c00d81c14174400600442645060204071688250007922450107031880d01010790400444600301c030303c03d01400c0c0e484601000010680c0c11150001c0c071100c035001d0119481e15580d040c50b92801c00c0f0007100c1e41c000704101880d4105202c514090a81c00c5480038100d8070260400400181e80c0341c4544100411161841340006c0a1250b240e0254005010886080d50341d0303590680031070025031210358991411841d144108110410511501c550725512130020b003000c80740313002006600f401f40c40141e50302070340744215100141c0358107881 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 975051250 1250 975050000 975050009
    0x6130311060f010e0a110d0b220209030618070b071b0807170105060303220923070c020109032303040b0414010c0c0506030c090d030e12031c0b1207 65
    0xd1880c2e9410012200803500d00540b000d1003c80c200300c1030003414605402240d1b6000c49811001683c50b1001c40411014040c07160f40d18400400e034003003048144403a030010300050600301c05440c1203541d0100381068980c100700701100c0c80e900411040c409a100c51008010260083d00b4031520344000300d4540c503182c60700c0d8001a1180c1c00c4060104500402074441090b1b01148100a0040b480d005c00407e13500c0c01280b948003000a11080c0e0401c105008110032005800c1450041c86800c0c03500e8500740c0035000002c00000249006400207845030310511510042036416521381420520307689900340403520384012030310100140d20245008050400c018002401341e80032150700c840c589652400c90343c3c10707420807606100713402000e5800944000040700650700110307241500d07625541c20280460003000c5140750044450806002815040b860121621804071540740080055400ba81d4403030044400c402d44064a0144076483e0b06030a4100010610018084400703001c82c003103c0c0c034030300480390b8030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 975052500 1250 975051250 975051271
    0x3110d0605101d130e06070807140a0c0209150d03020f0f010e06220f0f0501050703061406071a01031b0909020a05040f090c0914060306090613031106 66
    0x30800407410300303102e5046007403240d0800301c121800d109403000c9800c48488001c1d204002c1207180d500e103141c00381c0c0300500195001c42140c0091410982c09000b41c44292001d10102d140c00f1501001403c058045a1101c0d02d641e07201c11101901d0380c00c1c0042d41d10003410310324100002c446520081d484e0300401e50460b9000f40c2c01000104005140c0311708200360f1414041982e4140030b18225036041c0000d0707882c0c000d144a06210040e40510300b48120b04604400c00070440081c0d20400002d0001d09403620300380034044c00c0200700320340f2040400d400320b480034440c0300c05c29040c2c41005e8101d071411102408000d07024000d8090886400102491288403d800813280301c40c284d0422500c03810384000c1c005c050f001c07180701003024443c00d4001850528146c41054400c0707866251000052480d50800000280d20021030340802d07440b1407002c000380900c964a42c0301c0301c81c440005041807400040f150300030500540900700c1c0b51a04040c400103000302d14007e07810f03ca1410002c0d829040f04021161203214001d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 975053750 1250 975052500 975052511
    0x3051302090a09060b09010e1801020c12031905270c0a0801020712030b060904090602090a0807090c0e0f0f06040b0c0309120d08010605090a031410060e0408041503110d 74
    0x41d009003241c1c80490424080c40210005010296254090f09d8005001210f2110424034500b115806841244031904540c0246070b540c0144c04540c0014501a000c10003000d035480c024540380008450080f540d41c0520380d020404030f2465107059860805062582080d00c03520200d03880420008040c3e6801080181c0d800529030040c04a4076540c43d42c80311a904c0e050051086400c006601c501401b49154800d59172160a001040803d5049403140786016140344e0389182d840084c9511414103200b4256074606103544a114103210703440d2600d00a4008007189010040b0b2400d200b0440f00b500380054000070304010100e002c2e64020042c01c0c4050a540046595601c00b03400d121144180081000c410b0380f041444007a031680001003a07065401901d0f00b662941c400340001140c0015a03031029010788450300c140d50100a020440100e02130f400c41092043d180e443d020390345260b60441300640b01d018107000a01082c0034620520380708010528002c582ca180300c4401d0300c040d034000a0084102075445 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 975055000 1250 975053750 975053753
    0x1d0324040303110c0705100905030118030908012a030207150b1e0303033607080d050c031806040914090d03050c04050d0c0909030503071404031203051302090a09 71
    0x180140f81085101940e40382c20700d10f100c03010355515900340c000d0b036209010740302c07a030110340b445242000020240140240510000700d00c4600380d007035140c04160300080110001040e0380070140510341c1c0f0804400540d111201007d5050701004c0290781100d0304041e001c00000001c240c1c05403c040c0c00391101580061140e82c080100510100c1c0c5030402a90710b40136900c0d215540c2c0e000720549911007200340d240f03494071180c0024a401c00010380d0422883c01d994644884000000044144c140c1c0c100e01d080302c440740801ea40a54544c082e61450700e05543c42040001c0490b9814a08081d43c180c2c080c10140c01d043d101c80340d940a80311a001500e0241024a04000520001b081994140c04c12410301700202e0404c2050100c540c8114007400d80500c140350224010032244000302d50040140f00c1c004c00c2124028078009155070310a40b4100d001500300183c0060342c26009084400712070303200002d0b020000540302c083c0c02800380282610a0001290540342c09078903017203005440341e5204100040c0d003c106 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 975056250 1250 975055000 975055007
    0xa1b0503011d04020603070302031009060602011d1203180c040207060b0f19090914010c08010f062d020f0d0504090f0516031d030d0b09060d031d03240403 68
    0x4580c0d50059615099083c070002d41c41d107000f1640c2160544c600580da81c1d0714110403481035072041c1d01480120b0310340301d400540c4179410351000c801c00c0d00410342c1c120450030300e5110035510705402c11020600002000807501d0501820210b04a40d100d0400f503e800d00d0341000094207c3c1c2100100f0744130b25072103401d01d025500c2c00200c00da00a803011102400c18000001d4094440101402205065566071400b04c0900481e8850075840210241c000c0c04100180b04006008810038403911500008003075001c0fa0040c042d0124141407401223480c1c42c514000906e410b40d12802084280d02036000301c0c11810311814042c085012281d1054441c255100d141051038001c41d84e4000851402928040a00550300c0140c042420f180c540c0c1e00c1c000c2415040c440d034040c802c0340321408000c0f692200140d002102401c03500030f5412081c040700c8010b180d54a41041c0581301110040c000c0000d030001401a080204d20000d40c091884080d003110380201010300000b10f030340400d0901c4003940407040704220400d5803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 975057500 1250 975056250 975056279
    0x305070201031b0f050f0705190204060f0b03150a0b0c0703030801080d0c1b0e0a05061f0e011416030206010807050d03050708090d0b1608160905090a1b050301 70
    0x201840300d504a20350103003000f042c656200c4c04030410041d001070300100300480741050312011030700501501c8036801d42000305400b8803801001240a9400c0000005510740b00c10884005c96002da032010f40b84d0b44d075210385540b810020085050b4003050780000801c640d8903100c007030221404c042e00200b130000d0079820050402c06050703104803031035031107188103075031a0341d211440c11072950f40540142c8000d9030f50400c21318045955004020120340d44003c0110780c8440d60003943c003c04083e03d40701041001d4503c2522890000c1d0740e03001c0858102c1c1c1e2545080c1d4843d00b02003441c01d43c1030342102c0c04e1101410050310b0b0a0060541600140d000d4401441000d4062142800518044901d601141032540e4017800900030540050101c40f0b022412001c0380c1c88290015818503400803030388483e80b0b40a01c41000700507240407264000b4042800060140920f404220019503480c0c40d0840f00070304d020200400c10000800c4101480d40380c8540030000d0180340c03421040c51034907490b040d84941c1400e549040341c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 975058750 1250 975057500 975057521
    0xa0b0306090d0c0809191e0303050304020d020a09020c0f010e0705100809010207170703172a0909041101081b0d0f0e070311040605030a05151909030507020103 70
    0x4111500340a201c070301c0029000381c0e418150620840460150408020074003e20261a400000031a02420030b90304a0000405503481e462a414080b901646418a8481039000042c0031900400219000d8540a0000907a881c4001c003100d0500c0d88035541d05060fa00304110601c8603900c90311400030002c3e002c2c0100100710780020010200c4130301d001c00294101c00000100c105120600004c900042c0c42034044500c41600441c11045c80e0340080c24080c620740c48100b003500003880950f0401111003504110b58090340e426515400d440c180c0b128540b14040711041403403465030f4200407000c071648070384032070304d2080303005601c078041c4e5541da84005000b015008244190580d814881c00007000d80c07a0f0705584510b07460388000540c5001c444007580c0180405a092541441030b0f4500004200030035480c030300c0c00ca00036602800031658a609040d078880700313480010031175004541040c4124131038443c466071180b80351107040f5240010700311074002c6485140c0242c0c002000000c6582c10b558042c02082446c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 975060000 1250 975058750 975058753
    0x81014310213062a05120a050403060506061602040e03070b0f160f090e0411041d010b0301060509130c0e100503011b1704080d0213080f06060904170f040306050a0b03 73
    0x40e80060240a96103500d136000c04480b00c44040c42e03100340f140400c90302070b16030070f20480340359038540008001e4410b81240c48201d03409402d15000401c103084c42d205503480e00008400e80502c48102c0d90810024100648050740b851105101000125403126441c0c0d010743e407074400c16205403d140b0514403c04220700012424130144150810500f64008a0803048581c8410103091980f0380b490403084030142d0b01401d940c8507080c100030200c428500344c1d0400d80c180414000708030300c0170042c05140c260307981d034483c59a00440340400500307440d8600703400b1400c80b0b00c00e84880c1d00d03564541d0101c402c501826100c441c01041102e0307060080d0f040074841c9440555402c07900d100b51042c0d41c1001041c403600e000b802c0c0d00f022040c0c00820304000121094407952901c0440540d100e01c0004059030b6400c2d80d5100390a920300c50113004203007001c4003080325400f81e0f0014010001641d90380d100d11044004101d00308140060412441d0200b442200180002c0d5101d07100109003401c054410106660040100320b12030f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 975061250 1250 975060000 975060017
    0x80d050606070f12020c130c021b10031e090b090c0d08042123070f0305031e130f05040f0b030d0c08070c060f08101431021306 56
    0x1180c03c962103a00d079a83c0c00414100d40900d100c3e000c0703052041040d4640d0704100b00041c901c0242007142c01c445100341c0390394222940050100c00680286002110382900320001105010040f842a00851a141c802c0381d424454500e2103222030044800224099405000010074032440e0b04c2c1c140500702030101d00301e42c0103400d0b201e01c0e19400001d00c600e104030f0301d0540c17503900051280a02c140324440410703048254808003c24000d44119080d0b03c035440104d80b40616100071402c00007042409042da0782100c0254140414041d454503a11100c40e924122040c080c0194030345107243d888408007038140d4034580407050f4030f8042404141c41541c2108407140d41130001621039520b000403c01a00c5280346040b00c80f012305810240840c0c40341d00000380c480300344d030175020591a40103c0c031403008c01c61550f14042a941c5001800185034168029100d480c00c0916242140d40340407031603401c1a0b81c00d00a23a000d0302c400c165107110441c1e14003410300d000d160041030790100080034070381090007004e960400038603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 975062500 1250 975061250 975061253
    0x302030703090603050403121a1f0311070507051002031b1f020702010c02010323040f021503010806040807150e100f0c0206010e0903091216060c0b04150b060403080d05060607 77
    0x48da08480c0c142049555510f40000b00380e4043c01c07501880c0d1001a103d10151990304075608140c04224100304042410103480c8c04204031880102e410700780e000303000760010754144010001c40360340781c1d82e01e8821440f00f44500700c400c0d0510800109500500c100030040d1802c407040702101042905a82c0c403210788184541800350342c004c652441d206d9824030b000038000e440503450760702a0308051000d44101c0c03500c0f010002009108607903880c0d00b0b8000c0b00e00d82e41004101d091103641c1e100034041c940c1c1607003000020600140342d060241c00b09621903941404034540344540001111741c08000540a035201c032488101c034a80038410210800c500384400e21225000c038101942c0c640045c41503480781c90304100003d07014541801641c100500003001140b840e0708504085a4400346052414007091030a05d00041036070148444503c2c899000102900c1a51070f6150080314a50810074600501c0d11101c640c0c01640d1031100500203140306640305038458542c113416000f00e4100810680c01940c0800a800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 975063750 1250 975062500 975062507
    0xc02071a0d0e030c0102040b040806130c09090f06140f01050406080c130e030403291e04020109080105090f1606020304121b06030f140c030a0f060506070302030703090603050403 78
    0x26052a4030307070800300c0da075800c404100e4a0761164085001d030b02c0d440400d000c240101c41a00820840380080100c0700b441d1905041e04200d20006a401000b0b150303600c0080240a02d180c000059403405045140840e40b0706850f100b003900c00d42890450300c0c480003010044008004001d02e4054182075408000080c20504104d41d074400c0c081603284902210f20040846020f5604180d41e0000710809490303e5aa50340340c41507045003880d4800444403c0c84074844056280c4188561044140418082040d440203680c10803850010b0004d0b810481800c4000c503981c00c3c24020180960105801850500500c89a25052071020342020800d64421003042104070350002c141d80c16a141340c000040145d00e01d240403982c2c883d090044852103501d1110001d803858065200d075405551228042c401c41031114103000c00701d07004551084013040107001003120182c80c4d0340502ca0b201c8511400050107915200050403a4110002c214010390001900200701a0710612010003081b281c01d0500803800d142d034015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 975065000 1250 975063750 975063757
    0x210a150905010602211b03041503050132011d100206150303071109090a060614040b0303030609150a0909061d0a0c1a040e0702010b030d02070e012102060307030c02071a 74
    0x40c46c1c03c00c1074445c0080010090041f40c0060074822600d0700c030700000b8200600a41400d00c2440726a01c00382c201500450a00440b580103145094900c0414204074001503c443c84500800807840d51014103080f41601c4106e08401010001c2d00107051502d03040c181c041c03030755101007503a5001e030b0420710071400000c8407010404400d80c002c640c000340a40d40c40d9802490104842c0000c0c0503503003401400201c810340c6020503028143d0540381440210000303414590f903848103a96290704842c42d03c0005041214008038145443c1c0020b04000c2035903034565800c010f9810300107050721701669840e1103181d01c4400c01050785c07850b003504d0007a0203102d50684030480560350600c1281a401111015030381005a0301c0e04640150079602c0502509040c000c034020b000745280d10041e0300912480d0b08500204e80000741200032501c0021300d500b01303a07081909485d000466207a106102d000f500880c0d10042c1d45180c05075104e5a01941d00184040c0d05500082c41c041071503125a40d80e5980744924225100301c94201c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 975066250 1250 975065000 975065017
    0x1f060e06060a1704030e0102060606030c0a080702010204231c0b0103061503020a0b0a0f0302040803090409060b030a150f0204050d060e07210c0902210a15090501060221 74
    0x107140c03500c01020b0151100c41032914003000c007618a5081004058000252581c0f42c18280e0072100d4030751b10541804800e1200f80d50910b100081070102080c190700c0358040c1e5501805a200142c101035880c490340404075041c200c00e07a0310070800c0d4510800c50424289440c1c4400b0003a40c03c440805260700c0e4410b140300103000240c02070b5211007280d02c4076030112402400031680034142200c1a0395800d220b481c1ca800c001c41e0700c40003c0e80880008034880c800e00948080d81e444101441c90034011038208001401c0c1e606c0304a40242e1603040101055800f0300242c0350140c01510303468500d10000d113440086500007103c1c0c130380c0707144140030601907602e03803031003d90240c1d5012a000882079842c20f00585844030660050740500c5c1e1032102c1d0f42c200452200c5105480744500e01c0f18a11a49070f0b401c40007a40a4008101c08400d0480c416655900b02b801e00584c00005c0740c040042e104d010902c048403e55002c2d001000e44540300e000420800d60304008a452002c00020003403146042c028003008588680e801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 975067500 1250 975066250 975066259
    0x1506080c13030c090203060906030703030806010e13060e0103123b2809180210050d1104050a09020304030914010e030a05060708070206190225051f060e06 68
    0x7407a444001d044401000035642040104102c955218012800b81d40129074244c003400d0140e000c02c6c0d2a00b00082e810003030b01d9140d2211340a0307540c0c0c2001182c3d590b440600740c4e940700807002042c0b00c81c54203030f108180181c28243d04903805581181821801428a400c1203002c00c40c0308044400140020b13042c0460400c0080801103500f0654411100c5031740500c5522540940b0441c0340303540300981103008001003112540c01e0300703800d0b41e41d036882d0045405079000e1904880c00584003c0062501d100c2c04030100415040440c01d12441c10410f174119900800c09003000d1400003400e000f1440c10406890040c6000c10307040d451890261307030050545080d4400d136407040c4285e182d0004503a024a290030502c00001d0103c07400040e0b64113103203903180002d4958401194036000450410740c40030030b615105100d06209580110a0f0214440007036110120022980d005020200810280c65010b40a580c1c001d034002d00290f10541c520101c060510f00e44c821500c1c0c40e04c4020820030125a0055600c18821913 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 975068750 1250 975067500 975067507
    0x618140703051516180b030703050a0506030c061e0c06040308060910081f0f0c05070b131e031e08100f060e04020904091b030b0106050a05030a051008011b031506080c 73
    0x6110011740c201680211051040c00f1040000e2103a260740258404c1c0c40d000002d100d1900c40000b0300d40c844070030036055038201c01e0404c00310300c44601040d100300518106019940c41c02010307030b501c6424000191402c800040340300040c030000d887c14a03112508007000102000d1041d140458565035038081046034403480030100405074039084258009181604060024010100001801031942e40081c1c1d08448110a641c0403900c209407107a2400605680010160003441e0311580034002588600011810080030600391a5000242c4800454801c16030300c41c0021401c007000b011030034a51542186400602c5040d0030084940d01281c0122805026140107a9440e00800071501410349800d0140202c080120008401c018040110f012640207403070201d01c0b6602c4070030848140c400c11888000180c1c042c400b0610401c440c1e4416030b001a10b000318282d901d0380c0d4405980c2583e51000750701003000c80743c8032807012039034050103852038400d18003d80c02c0205060200c090294800075111041c050b0020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 975070000 1250 975068750 975068777
    0x40c1e120609020714070f21081602040b0f0907030905160b04051002070513181407081605060a0e1318030f030b030a0618140703051516 60
    0x26160100302a8459805111550b180ca4041000c0e50200004440354110034115040b80720010610b8000e4070080f280c800740c61407a100240071600503c40706900c3c1010051142800100141c1c010112900c4180c442844d006035030042100301d0790f604006034040e00d00c0b130451551550b40e02000075880002403c0004015030a030038424079204189007083d005880c6880d01042c144040b5024108960044030000081c0303044c0340cfc080761070b02a148101d58002191203418081000c154205840c140315260003c10000402d884201c0c0f4103622610505403500103640a020f0b030442031090030056138402c201000c40502e420b02040880c1300b00e40c049030400c500510a06c040d683c1e11844101c0400907081c0510800410010440d0003400d401c0e000c402050039040e0105100c3e0003402035010a0030700801408a04145494a40191001c0302d00c04100d106040c0c1c03907400040314251041b00404a8100905c2e04608500d00b55180150142001000b01c10500400c1106049082c641c10080003134501083d0a1680 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 975071250 1250 975070000 975070007
    0x6060e0405072a0c0b0c0105100f270c08090705060a120f06080a0b090c0f0105070201032418050f060a1502100203011401030c031104060c1505010602060f06040c1e 72
    0x740c4000d190700511340002440558202c06440c400c407180008018949440002c8030b85101640304050300c0c804a1a01045080100074a03043d026412440c42800c21307090395000000c07696401c0c104004108801d003402608041008140c010b000165071980c903000300e401c0050403882c1c42c402c0800303042c0e45402c2c03075084020b400e402250040940e0822251904241c1c81c1c210300040d0215105402440345040b035407050b25055850055940341a180e075490070310b89800440207440716900b04990700031103001c050941c2c0282256040181160910710882d841544400340c00d40358054064404c0b403607007000380070681d503c1400c080100c4043c0c0074a2a140014454140c0c1005450aca60342120340c07010000050001000c041c190303072030609036030401c944030784001d0503000c0310742409100461100600050007601d01658110f00828010700b260407185035001a0981991303000d80080005801ca14244200c40c500e40440355006181102c0910050101c0c01006103070340d0400ca041d0072180c0701c5241d60345002c0d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 975072500 1250 975071250 975071327
    0x603090f0106121202010c0c080307021204170f0312010e09010603060f0209030d02070b04291803070e01080c1507060c0f022103060405060a08010e0106060e040507 72
    0x105100240320742d65950b0292442075002c1034064440e12282080f85110b0b5206100f426921082c1e034580703c5106000e9141c2d800d4036040201090158441c0d07183c0900a5a4070b103014100800c52044800b4070180181442400d01c075030700306403900d20790060001c4c42014034110401c1d410340303161040e00001030361a02c4440d40074050310b9001809082c94221104d8140c3c0300303900200045001602112910300c4c040204a03502d8949204411051000f808140701c00c80c1f080340d04051440800000710060002507010042603408020301d1000581e190a1725401c5003030030300c1100010007141011003542c2d07244c8180c075611130300324240042c820440a00c801510b1507203003080c0c075025a00184100074482074640058a18075009044d0780143c031a1040321100d00000c240d290703140c0b000c9490401d0071a194071007480042c0c10702030030361507000c2400003000c41c1150092290102c1c0c50300c002c0c008109286030a01c06895030580b1241103015509100c03c1000094120a01041410031002e090000c070031142d00140d031011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 975073750 1250 975072500 975072523
    0x5090712020a0306060618060503310c08060a1b0203093a0507080a05100b060912061f060813110414010e0c0a080f0903040e07020627030702060309 65
    0x17881e0000109445074005202c10354a808440070305c2d6065120f14003079485000c00c44000710100700802004a0700c140d40d60b500d8600c1d10800d01b084c0760036007003595450000c40132504842c00380c1e405001002610201d5004501a0103004c501c0d013008032860b40c100075244d00c5000440350042c000c8140c50002c1600d0313416860070f80e00400d81481d41c0102c0103980211170030301006098413548506440862150400b04105806c02e500a00a00700808104085000b030150030540a5020300c0078840e0060580340c2c40e00906841070341070081e000b40c1c82d140e05048026000a01911240d030103041040c028a80c000c4020340e0021b5402e040c90141301d2040c5000d034400311007100003e400906204100c0504400340d04120b0580e61001e0a0404a545500d0f2205060051100c00341c006034048002c1501d80009100e0250010b50650941e03241584500d080c00320743d202500d0042c016400b280801807000b40b04800706c0c0c5441120406044d011004072049680d07070003140b8000c2d00c034010006c00704035050003c01c044812030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 975075000 1250 975073750 975073763
    0xb07090b0406050703030b040501060c062c0d031a0108071805040c020a02091803030105130f05310b0601140d090803061504062f01050907150305090712020a03 70
    0x5a4840703500038081d410130b090440101e401c04088155510b440d0190394140d40065640e00312921840c0c44510150403183c50125401c1c18218030442c40c112585200301d000603804c2c2c02804882c0300402d001b400c903048803014400207011240d541c80ca03a070340081c881d9000965440c09900802031091400c4d01c20f01150702080d4010715002a00c600c42e80c010522111a074004c588809040c0d94548907602c1420072520303441c4440c0c01c01c0006000c289090900100342d030210420010ba0501d031001260102e6900707880d001045a0844441aa260100400c90000c0c40f050030307424007585102d558078007010b017010f081c071814454201e2010740301c03012002c165555031440030001d212241042c14903809941c0280c0314940298812401c144604002d04100c1341198442c0d41c4114120b030148008210046440000800204103a0070355420803609000d118051139841020b441036a01d001e0710854242129104a000d00d030401c400c06c5140318022884800301d42c4038080c0c4a0b00303d182d500c00500d5420181c0c2004000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 975076250 1250 975075000 975075007
    0x90302062a061021021c08070f0609020a050102030a08150f060310050102060615030708040c09090c17070518040204151404151809020301180303140f130b07090b 71
    0x10b440c1c0e4545143d085410303c01161000503a5040040000103181c40040d42109841c08008020032103030900040882c0101401d03414031100d9079070000c7c00c840c0d540c02520005e4072001080c043d072415905d030f580201001d000079440d050380b40001401d0003800070001030032030280b0410b000d52520b032019000c2c0c4e04203005001d030b90749280449031945145081d014403801841840005400c50900001c01764280081036201e50850740c1790b01007216240402072088035080400000012015000d01940720714510941100900d01d003403902c0e043c4860780c0444444119804104104101d403034401d10b00680801c101e03013060642d9540d0011030050b080c0442c3c01114460390301000651210000c47c0403a12400c1120144005181c1007048500c550290056090b800741c07508009050700b000398841c0c25421b101038008181c0c0301c0b401c1480206000150f4080e000b2a803144a4140f032200310b513104a500c000c160b00604003900306083c85115440080e240200000700c024041103500703015000c0c0b18001c1001a10107980d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 975077500 1250 975076250 975076261
    0x603010f0c03060e010608060603040816150506090f100e060409022107060f080c0304030201060e24150f0a09090911040c320d0f1b090302062a06 64
    0x83c94548104a6244501000070440c07501c01d1f01a03074003e0704014007150071a203503519084a0790344240442d40200201c1003480c0002280c00011030580c15a40d1070019061401c0410b0100d1850b0050a1101600c007000400c942a5100e8030f960041d100d56040c8628641d0b1140e002c01c0017010003200c060b40c00781311504900b50389900c1142e02c10319008160280c1e1041540c60030156400c2e600e010052000c078281e81c0003c2d0800082030043c651081c00ba1001007209562007140026161080e00d904403001003840c0400c0080b0784403201b140c07003140240d4072441c42c0e500406080340d032401180d0b840c01c80c86900140c1d0303903a45441281040045c00c00400c0421101004e0716019083c201c0308405240518146010210030702d000d600c074020001c03c9226004039900114886d200d126039150a6004940303003c0c441c00c0d0b103120241c860074002c107035240000901da0b52040e8590250034030090703542c01044520b5109100503201c0c24243d407100c104100040c848240c0c0c0c3c401c201e5041c0d0301d03540d1014841c40398004018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 975078750 1250 975077500 975077507
    0x130c1818050f1002030601080a090305090a0305250e130201260a0b030d020d080603101113050604180213081c090f08030306060c0309060d0e07060806090f0603010f0c 73
    0x4902120804841c241c440f04001030040c1d020488131280892910800100f0130072981c0c1000702c0543c440d280640c41c040103100001d03040c51380c82d082a80d50307074003100b1151005507810011003000c0718000c06042c03001d49424808070780d158004080d080703041e5602e8071000c21a40107014494100c683c0580c0030405040c2c481c40c00011280488900c1403140c2403504020042c01c001c5080000361031b00e9800b8000403582c035003041d03540b40d078040c180541500c6a50090b105001080c42042c26003c00c030f00620380d9490b450a4170005000d41a00524480c40c4204030800502c0c580720b00fa1000303007000e8080503072590403e447e034010444a44c0d00c214402e0089015907403010340760b243c0034031580c1c40603102c2004d85030711029805240e029500800314681d2082010800c00c0c0781001c0505a100700ca00c0450386025442000310b00e9540200611481803500d85000814211042c855003002c0c000915060440b0315050700040c0101d0000b0700107400b950203507400f0420986080d013103150380d0109594140201e41140c42d005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 975080000 1250 975078750 975078763
    0x20040803071209120209190213080d050c1b03010204030804151d03120c0712030f0306080607082e170606040501260c0a030c030506130c181805 63
    0x71500b0120160340401194041c070f8800003502c8003545110042045603007880b05108000e481d02490700c50b03002c00740a07000001d0004001652a00306880e030f00d6480c00c11023601d405280310100d018440c050000700e8600c0380c0018410100303080d144808100f0410240030034024400d80d040505038100025021860103030070710924101601b00d0303503441041c1c00d001c440708401e9030144100c241c0c5a00112103082000000d040a024403698410640b03c00550741c0b09011210700d0f050074210b0100d40a0701d2841c645c29010b00c900f40040c1001c2c0e001e091985800700c001040c08000900101404e01401c07808120b131000e1074801c0007049076a0854500540e203a0250303d4120075440d00e1070310f05200760302c00140702e400c20b07020b00c0e8100c58040e1040c0c1103000380b21422103010001c08481380c805215404400c0541e03510800f4050065010b008140c01c1c20f42503041c52418174100400001d070300e120404c8164009000040701d081107800700c0701d241c5044070760f110044015001201b1004010185850381d94280040401c40307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 975081250 1250 975080000 975080003
    0x70227010e093d0609020d050117010902090c0706090c091a060c03040e1815040c080d09051311030405070e090d121d010905060f130203102004080307 66
    0xf200d10f4a800300407902c2824486000151200d040460074004541200c1100d90b034460b01d1803804240701d9190b042a0b4200d03040012550b000c951940300400031410034148021240f19500000d10101e006038002c289420b90150010504403030004010307041c000240c2c40355184035070200700813210329078481c410303400f400343c46e403100740c105040e42406030030b6103423480440d51021010006123086c42e141a50303410740c1e401c00410400c0e0070b0383c0d401900260020300f0302294404103c0308418540c039080c281080c030824165a000071103503500c000d201342240d503005990070b01215000c0700e11241c5001c180300d100010b041c0d0508514030141d0084140300c100302003c11a0419260303500d58402c280d079510500d040d0744d0480700b40c200002c503003440010350b01d010458205200b07840c40001580a0b114542404500711803145000341c0d03003504140140501c0214400d005030300550380303031152680030a070f0703400103038a0780308180e0780d070708200e03551040348900d9a2000d0000721485241d5810a0315140d8441c44d0310b840381d100c03990 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 975082500 1250 975081250 975081253
    0xb04020108100810050a0e24060a03030e04090305040f0803071205160311071203051209060108031b1207030f02010b010c11240301090b1212070227010e09 68
    0x2500e01081442d0460844098070002d0207800c00c0d80128400808025045000541d1039001c0314146030000c100002e44d400d503801c04484d404011100039550420b000e0480b9100351a091030030000f10780e1002020010100440e00012421020324080d02c40d0300c2903601c03048507500c04000028070120f0200103442110b014640b101c64980c1c2c918803c607194845c20741200c481d04080048940440e102ea01c080e0080c00d031032012a82c4458950310f03150303401d800307151085000500006800711081049046c158124400100074201c81d4101410395880780102c00c40c81460061020760301e00580700400c0f2801258101e040b446030b4407000d50a00425454002032031102540c20b0150503049540315032554504a9002482c0c1192510f207081003042420032032412510500c3c0741440704000c411a203000318024005510b000482e82e45440c00d0050003160802c2d4819160080362000c030b03c00f003405d021266450340c11111030500d4200c0525a840d11000043c480030030ba40e9180021840c216801d015500460380c120 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 975083750 1250 975082500 975082517
    0x609071805040c06050a02010923010c0905011d0d0818010801080c131a040c03020903070806010f03060c170702010902040b030c030d0e13021303020a120f08090f09040b040201 77
    0xd04003080e11401e45008010000c064010030000d171142003e010959000c4c40003289402c81903c03140401c04070141c01502840240081c003101c50030920805903000344508001c0003c0d8a40000a0900c0f4050100d5032600045145902480ea803132104040c5c4256005061644900380701442040d8009504a2180402d90700c1c000440d14820008005500d50802014003078850301400342c0902400c00d901c10740351843d001e030488150701d984501a1006903581981e0040e11580b0020802d440c2440660210f05290407040050100100203054002603075045503003c2021480d80fa01127400341043d00d0300b8004210321406020f01940c1c10741101c0c10349402141e00b40600300c0180c0801d43c88003020a00c90350705610103880300c000301d4000d55680307150340c000a001000c0d00100301022010b03680704005849a5081d050700074021450100302001c0549200c00641902400c80d995002d04d1100d070740d00162030760001003a8109155151a20031012907009480b020f0716042a20300201c2502055404902203880d06 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 975085000 1250 975083750 975083789
    0x307120e03040f0806010b0a12021b060a061d01031419031707050c031c06211202120d0908040f030f060606021c03110904140a060f060e061803060907 66
    0x69268187c803180008a45802502c1c0e80903505e400e41401500000d075002d004002009914100c3c403101c41071443d000e01981c3ca80080460225003098024440d4500140802e00603411820382c1681583d9002c110741c01d50b940c560440354680080000c2029007003446503526000c050303000c400361648440f985030420090301c50742c5d8265558000c2c00890084c1e5402070085000307410900c1c6c488583d4403494000002d1740307500c541c114044000300c05400304102d90155007943c00c2103c41c00740b880080c220740c40600800303040698079000d02d201e64820f07072107a251519500014406800219001803c20710030b800c06a603500d1412440d140c0351203c05a402501d086c0300090898000715450761813a1045440c8040c0100186054005100c0e64015500c2407405024001040d211407041d1007021018403102a868030b040802441a50040d802100540c0d00b40d001c01c0240301d8200807410001074003141c0c02c60f00c611040510b80e4038141e01100d6140c1c54032840c030601191100200b000415506a40c2c1c0104080050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 975086250 1250 975085000 975085003
    0x1060303170a0e0105150a150806090a0b0a150e04050f061c0210020c10090b03040b15150301140d0203060106081b03040b160201150b0307120e03040f08 67
    0x11440003501003844501c10800c0c6001844007140e00c242d003150000b8030146100c0e4400d0841e4011103014020748510040e06245142c00803075130000b8941400e10100b041e04041c002000500d010700310500640c85007003c2803031155140c200f820610406040034070b80a5a4244d80c1813005a01800000401e0081c03000e07228906103802500e00c100c00f50b078504040b0f501c4c0c4000f8013140c0c0b950403c4481200003a6295071740142e0311061001000241540200040c1a40808001100000f00d82c0681400700d801000c00806c0003100c25a50b0054201c42039000c55a03803038076503203003003401500032941c01000d03448030706005071005c406181a04c1c9008940d099014882d401d2009002c001e43e0043d602d03910000040041d02d105542155224803150280e4422002000c110885604242c5045566030b5200c800c01600c84110f100b949168017845c8001e20a4100c00c280e01c0d04002810b014036500c0010000004281e603000300c004940310300c40d800c030801c580081418002d0f1250401d001d040c04410110b40002200f000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 975087500 1250 975086250 975086261
    0x41a09011106072a020604180e19060c0c1a010306050601031811012a02091311210a0c0f05040b1c0204140103030305060306091c11030c031b0f01 64
    0x8842c0c4440449419240d0076488113004c0c59040142540c0c2c40a1442c0140c0301d1402400003000110f4030001c82d8164480d030340041d6000d4107048091640101072140c2c25002c00161307100380980041000031000651982200c146200c8200904031340204036205014400b24240333241281e004140c100481d8480e40c0044040d15420f8200400201100e03010340f010a01c12420f50781085414103003a040408900290900c03007043c07040005804c04541d8540c0150304100300304a40c01060040010344000f016030b10010104081c035040d90007801400b140e070038030002250b80c4201100d5400200c0740c2c5c520940c80c0c8401c9000e100c1c0074081500c03540000020b60340c1020701800c4440b00d001841705052501402800100c0c0c4403703441030307a00c1a106c0643c80840b14031442d00c180618000d6038049490700d082001d161625902400525565006c0e000308140e914a41044600d0101c062410a1b10b0ba0105c00c001ca1441c010944900c216010001c0e4000c11603005e401c20314a58071041c015100d40b071016404107400ca44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 975088750 1250 975087500 975087511
    0xa060c081503011b140d0e0a0b01050d170a020a02060c010917040b0a0f030209060d02121003050723060a0e1011100915050c0901030b0603010f0b0708041a09011106 72
    0x98810039820307000c9009201107008041702c90702c45804d02074800c1c02001039901034220400750741c21a02804060107912100b05000d0042901c5103c040c013460750b248420b0801e08000000000b20114404503014400d208551406800400f00b94968806803107180c0200454881251500c284c0d645000b08100311405a9040390051003030f881c104018620242c640c9800c4142c1c120405a00300800000d644c3d4050103030442c0c10040c200140c481c00006840c01c11040040e1071118510000c180c10800140009500c109070b9075194041c0300d0320070b0040d0203400f1141c12140c11070342c400300c04164030140c10762010b0b15444841044400c09650a0078074000c4e910307010403030012041b41d000040d03000e150384441e03000071842900c5203504024514011841c0c00480703c060b601c85001160000300c43d2241e6905000c3c02c490b611007140d8041c955454284800700b20011445051207207003001c1690400c0c814048140ea0081925800c3e1407800c0700d0b051100450f640c1710442c21804070b1041300c62210035182c0010a01c0c4200c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 975090000 1250 975088750 975088781
    0xe100b1e0904080a0c05160f08010506030a14010204090609090606060c0b01150e040509010b1906050d05040f080406030b01020d05030f28290114030c0702030a060c08150301 76
    0x352183c0e203c070f4800d540b01c2021042440080846031000840030410001d26103035880e1102d03c214105130000c422160207900c158140e0b81044203011031a9000700e00d00311aa580020142135612007420000c2c00790090b03a00000c1d48034504240055810120b8000003880c2d441082d00f049540e441d901c090341e481082d00005050840000014001942030141c3e100c031804940c213154911408010001d41a01c0303046940349596515036000c02c406062000080040f0195041ca48003c2403c290005003540910b200901d02e840e02c0700081028000c60f624550085c60b000305d50b0a039a65191003000e00944540081a8010305c41c2d440c3d0b00c00a14815003d0300c1c045c040301010704c00c185d2120b0310f15000507511050b1401c6003159282514a101002d4410509028240000c011400300b1a04201070058450000181800309415003c008404408201d03075204412500c1c160b19105e0500100c0d1401c01c2020005010314605181c809038103800640451042d43c0b5a0900d00365503110704241801d0300c84035001c00d81388 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 975091250 1250 975090000 975090019
    0xc2b200405270c0409080a03050c040b0703080c0c01020403081e03010b092101060623070519030e09040b0a0518030a050d090f1110020f0304060c02040e100b1e 70
    0xb01c4101c54241c5096954003c580440d03e002c3c1c00202240ca441c9001c0311402000200c4405154142c0036050f8003007507040c0305506140c44c002e614001c61213600e50050820800e040001c40c1160660240c400b078480080085444a44174540aa26a8802c43c1c9112140c60010580204a03014404490698030003500709801c042c4c003401404900344210055042010300ca102980103900b00344070b050001c00e000e90740c040311035505401c0e14060300508250040356107030801503500881c1c8001002803400c51441c01542c1142194101110680c140c020101c1d8022440400d00003402400c080a50040d42035840402141d100c0f2080d07844482c07411140180305400c1400640044d600031000b900616110341000b0500d00d0305641e41c44651810b440f4101d41041032070302c15420500780420701070751000c01400102a0320a40741c0900d6928000c0b440344908000c5042485011511150481099403440c3d10450340781000c1ca000703941c0038010400c03090b40901c12424a0301040302020381c80101c1500041c3c0440c07031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 975092500 1250 975091250 975091291
    0x61803070309090f0f3b060f060105130f151716180306050a2f13030506090106150f051b070305122a0c2b200405 50
    0x9040014152500d942d034070103d10b041d001305402a0b1030500340c0403c05000b140d20050303030303800300c241c0000e0308030f0290004405c0801040d00004031140c01c8500c400f003d002d12741d10400121000c0c441c0b1f200301c0202c100da40e40006a014440c0000c0070a031400c00103005070b00103140c44211507496041089554800d141400f0420341044181201558111071802d02c1d03c1c0340d031015143e41906510b03481169180c1d41c4008000b1260b4503482851400103545003071412030038000701b90020003020100300c1d02640c9000075079000307072071400c00c1010015944001a07581c14500040d07424000c1c00544503c0880440f521003910703c140c455162885461010b072196400c0094805030b051081e100c010b41880301c0e02c200300000c07010a41c1001007900c0c1180440100d0b5803910b119100240300d241121100c54020f1350302c000c0313255900300400e015181010030b446001c0c0003001341040401d400300000d10822140ca0210b584002d00c9003030032510455050003400880400c1500d010300003101c40480310a50300850300f04650382e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 975093750 1250 975092500 975092519
    0x30702060f0c0c0a050708011a06030103060f1803080f0601030606050a0302030c12013b0f062b030305011505091210060905060f030703050c01200f061803070309 71
    0x10b0b00140744205240c03c212090803143e160181d49070003580c007540089010800b454003401906182c4202049103920410103101160aa0106002c0100440d031a0a80b0b02c00d00255a4002d41e01014102158211010344c1d040c046c06118083e110f9125445001d070025040c1d50081c0a400d0886421341e440314036203022a5030443c001c0d040609031f500d5210040116040c003150200c1554080c04402c40c000001e4a003901500136071009140c1d000c0761162007580c248800f801d41c000c0e060b500007080c01c40b000183e5900c60000307404203200c0d07400640b100d03000c148e40305600b606084400145803003a241000f41340d80702d0720300c0c8110446c0f0824460004a08010001b5682000e4070710801d96580502201d4003001e428041034283d80390354101140e080d6403003042180601d400c03110701c10020810307000b400d101c80c216100c60f602d0b40a07400340c0c2c0d07050244c12068043c2c9100c46a14168032903c0c4201039462048900d0342035500c030602992a81c402001080d585080943d012080343d02c26540b540320041028036203410903 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 975095000 1250 975093750 975093781
    0xf1b0a150b010c080a03050702100b100c081603110d03020306091b0c071503060e10060509030c1201020304030f0f0827060a0c11010b06030417190c02100503070206 72
    0x1e04200e88601a840091140313030152800861681340440c9a02d0f200d84001c1c03500b41d0300c080c9445c145040004140071511881c0b00c0070f81c078403c03a28006610584505182040f8132490070050b001c4c000056001092507442000c1c4c000d41003046081d00c0f401041c040703088003a03000645a0660041940011904600031030390460801000c0e4010a4107002d000c032090342c10107106a110640520640301c01b8241c0e01d82c5031060704080c0000741c590f2100d60505442540b4180401d0192000b03119002a204070316540401c240641002d00401c11400590030b004001d01030b410a86d0b04601148500d8482c481da070b40036092560100d0383e507030b442c201d207030b980c116095002d004400d040c422401401248040450018062544500b10f400070110b04d08142c050001c00c01110810038504a0345071422400650751040f0031250816000304041000c1032104075480003600c112a0011210f219000c041d0404980000b079106001e030085841160300b06032000309031510710044802c400140c00620002d14000c4104148 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 975096250 1250 975095000 975095021
    0x106140a08100203070e0307150806100f0c110a060509040e010b100806040603062d0c0c0609061112150a050607080c010902060c03040e131a15060f1b0a15 68
    0x8141d201b81304800301e42400d1041d000981200783c1010803041482d08040000d41222003600d00c84118400c1c101d004002d04450344140c41001203448910041c413645101c4207108940003403110402075034030400608181c0c040101c81d4021410550408810760061003440720811019000643c0c803850b044003180e4000004103101d03071140d554840400422000c0c80b84d024500303402c1d021600c64484641d07036004c00b45024081d030100942421504a102da034040a103000d403d5014202007825140b600c2c290f006000706c0a034880c07039008080f54185002c505581d4290107241d90a0105450588000034446c44d52100d0156542100c4100301c010005242e40d0001d14091001000000e06403030183d0000c0e00c160322521000100d684085000d01041d5441e07950300e50050281c2d2451288201660b4441c25100b408611070049062854005aa00e15100000542c0080f0080145640d1450007910000940111800c240d43d03e054030412984c614001400180d0385400858506182085030400d01c06400c1c0c1d890b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 975097500 1250 975096250 975096257
    0xf120303020d020d0b0906100906180b0c061008032506020c010524010806030a020d08040f12110603070806120f0102070803091204060c030509040b120106140a0810020307 75
    0x102c018014035101900a84a150340d0229001008000700244c510025007054802e024120007403000e6900000721b20f007258000e003880d07802d00c002403010000811031548a03460780700001945010424000c11018401e43c80023108005554076a45407503640c0c0280907458501010b041c04515000b546403044408041c414600586486040c1400c6400c3d02c43c01d44280600c3e0100148120036071b01c0b900310302d400b001020703c0c000d0038514201c0001fa070345000d2500302a010311a8281c2d03401c2807011000444010b401c501300c0c080d448540c0c6203500091a110448241d4041c0310308980b40350350b86401d00840f4001c10466032190003503101c07a801c101842400b0021a0058405c1480410b4280001c0c000341c00340d90f00401c0c2190310b0785441004142010310200d2440210f03001000240a40f94000100d09120307034040c6400c5440c3c1c0040004100100400c4d45020b6108035140b00e45001284c054200d00c0580e1000100f140300c0f070340d130300c0d041c014048002d0080e5409a0402e030341c926000340956000e1a480b444a15 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 975098750 1250 975097500 975097507
    0x303070507111e010306090e0c1003020903150601021614132003090120030a0504110a0305030319020a0504140d0b090313080d0f1b0503031503060603070f12030302 72
    0x40015505140c5602080c0965200038205640c9617050310400c0014464100b0500c0040c02c0224102d803200c4880590611801a0f000300d468440d01c29415201001805422103080c20055012204d1080040356014014401c5000c8828051520f6041030101c4100710040440e0f50814010020072004201140b45115078454880c00608e2000c4495109032080607030003641c03400d200f4881401e49410201c400d2b20464403035040c2002d0305450023240e80c00601c040d0300050311f880d1450300340104261441c88582c45144620003205101d0080000c50240507461310044a9020103c2583c0a0340103418013440400c2052000b0000c8000c0708009800302000103121446e6a0080c0d5034074048100706660980e01c5900c003003100040f41c2800031100020301011402803550100c0204d0040410300018031160820000d0362441c400d180d50031000900b219070050989881e0301d81523002c03d140e01c00c0700768000d10a01c04c1b00c2c0402e505003000300d4200305451340803190750740e10740c02c0c200070505591424404404255080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 975100000 1250 975098750 975098783
    0x30914190506092418030303010b040e04140a081909060e1207150903030809010b0f0609040e100b0f010c0203120924270a090e0a060905150112050303070507 69
    0xb501c8800f41380b40c91100c4e544594032000c0b0006003811680c0070a000741e100308010300268100f03200340c0d070450f0b47d14500840581c0d1145443e40c1000301d0345c1c407840310502c6890640c404210102020b002458000d01c070b070480d501c0d10a00304541340d000342e12030480441c820210381c0035a4108000401e07102a1141d04891400741e40307001080e070b1032201704441000940b00c90070a0003016801032603160024031f180d009101e00e40012000603124a61048814442c2d400010450305603100c90b005440c40c0a00c6a00340d40f61020b035600e0140251032441c22052080082440b480310560080031083c10894002c1c000301032100b030a0001d49042e501004003540d000a084070000038589502001400d4080d50341c5240e1f44812010801a07030b0440c8106400c8000c44281d082c02c07159407940c000620455000843c04105207200c5c40503503041070f20701c0700080c040508040c244014014001840d40d1000c4140050501d0342e0303079a4111090705040c084000b403050308208003089071184030750042d0a100740103000043c0ea09222 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 975101250 1250 975100000 975100039
    0x152830060c0c021203032d0106200d09140103060605071b030c0312090506030408161b0e040213111b03161101030b01050c0d080a0207050a03091419050609 68
    0x420300d0b06131588000304000c1400110030540400c0060206924034000b1140b0140784010710500402d070402800a6007200003488100d410800680700b001522421216210000c00d14580c60042c0d40c180900207410500551003880741c6030031134100769a101d080c142150f560311042c95180c1c002a40158502c0408008207910100b8000114801c80303484050328010080a8040303890b40c1d001520400b001e104000110f420041111183d58849200b03244554140c030305100054504200010a895114408101d004a203510305000790f000302d5203280c07000d111004a00954003210303071011001c41c0501210007600c51440c415030301c5a6154094904000d4410811100a00002003d0b0b0b0352503e05012800c03e56014421115a4202840c1c5180b810750511b2007140c0d03036401c00c0481020031121100242d144141541561003999102090317491304003160030018281d002a00030f04403240090506c100441c5001122007400000f1080d0048a5a142c00100a201d4020f4040f0b103402000d90301140b85a01007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 975102500 1250 975101250 975101269
    0x150f06071743030507030f03110c0c01030b0a0614030c0706180201180f061d0406030302031e04030231050a0c090504020c06152830060c0c02 62
    0x200d20011200001584803001d0034114200e8948038a103021180d20b011a80c00700c12680e07200d4043c28a4010008452011001400c160150701e01e101408070390200c0c3e8520104210302041c600b6602801100e082a041054070180b81c400c1e40c001c1441c01c6102c05140505e00040c1d540000e210411600f00100350f1164410f0300c101d0800000c0e80f10303022460008545e00400100401c01d6503141007002141415078040303c507409400340905100c6c00240500d001c401e03003c80f204020b130000d4014008150707a45400303540c98104a01880c0118581580c000001c0d0609041c0c508032500100b040e803903144a0340c480c1c4110b1280c1c01614400d07801c40442e40d120900a40255400b41000b4400003a800c41140030007031006c3d0f90364100a200305d00400820303401903000902c141d000403104103070001351080900003403803c240d0700661402c501043e8079614102c1425041c5581103918a0080c2400010441200c101c03902e01c410700b0002c89442401d40c140070410703036400000132a44a050a10080c503007500014400075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 975103750 1250 975102500 975102547
    0x2120706050a05011211040509070305030708040303090b030c090907091d010501030e0a020109030b0c090901170d050c031e25051c080103030e03010f020a0206150f060717 75
    0x29141c03810701074448103501c14280101300301e00703400410040c03582c1c829146040404c02e25200d0f0303807150b0219078180000d11142c8015980082200c0e0358884925010996410910080e40801e81000000803800c011300116846140c0801d0f241c2d18000d0210104000000054084010005500004036a40380d40204110f003862070030849071840d40c9460300044c03e440030444c01d4030081d000780b4407400050342c2112241c425258065200c0320075956840c03025a141c080e42d000d4079402407654000044584501e41c0d10350303094004d141501c540b102092402d690500c05c071042c2403040d40c400c200c0e8118240400c0c02e2202c1303c444410304140350400c2d035400d004100400028006001b1003e440c80790400408210010272151814102103640b5940c4a01a019550502c0701a05002c60000101480d603404e50208454400741c0d0f00c00c640314103016030300950301c0204441c2603a2510400420340e540d403402c080207010480c0c0092445103003080030b590741041c001c0400c1c20191144414070040c05450000c090201680 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 975105000 1250 975103750 975103763
    0x31d04020d0218041109040b041b050301080c0102060f22060f060905060901050a060f0c020303070c060e09040b0a090c09050a0920030a02120f0607020708010c050424021207 76
    0x106910100040010155100fa510030b501e0036a02a1002d0080c00550f0f407044822a0001810b074040c00114001e05110b18040440600f101107091180340c0100c042c5050321400801c031b07894080303e0b100599480318182c9005507003004160018680c0507540c090901081c010003861038940c40d441c0c1c7c420702950701843c0000d00d0703507450324024000c0d94000c2c8100340c2c1c0301c00c0c11200c040c070355450300303020614012103401038008100c140144507280c00d01848105052540c003804883c0d4a05060901d9841918503005090015140040d00700151501c80310881c040c5400c201031103d180c4800d90400001d1032241000c4500a803200f00006a84015100b803622451848001040072034891500100103a01c07000c484038041c0c03410b400208175440000709100d00c10350540300d000c1c1100641020038a01400210780c40903a20400d0700b00112141d000c141300e0201c6020314001d12130a03420300750945982c011400b07590a60343c0340704429403100031100c0704403c411503140103a50185400342c1c1ca04070385030311124066442 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 975106250 1250 975105000 975105007
    0xf210a030e06190b041e0b061e12010e100509060d0b0405030a0206060a06080a02090604030605040c180207110d08070b13110d02010c1b0b040905060f010306050d031d04020d02 77
    0x2c43c4101e0040c9030b9108000c403010400e00344c201051480002466a10f83c44c926a949a8161151910011540d0000722007407608400300710507010301c146500c003580c0d55003206421400058480c08002c8030324024202e11114610850500702401003010004009642c410918403102010500b4511514086c5005001440c1d445980c0c950191074080302030a5103006a44440041040681c801105600027090701d4000d03a5540c41140001c196008903000139107103d240109201c10001c6102c0380b4400c840101d0b000406046801c0c1c3e07803104900030b40c0d4000e06000b403000720070019458522404603103d0701c00c1d0442c50410303406072141e0000a80032580c54917240c03510341020b424002d809450a44540302101c0c40f126455555000801e42110994000c211044400150b480d4011104011002e0a402540c441d140c41e034401025018000075944180900c40c204010041c0c2e521070b0060341e003996009803850340c50000603601103a080c408038000411511009906410a95440c00100941c5041e1580541c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 975107500 1250 975106250 975106291
    0x204091103010e0907030f06050603011b03020c01060b190e150a09031a10060503060a05121b180103020d1505041109160806011202040f170f210a030e06 67
    0x480f1035000e4418038640d0b003c40000c0000940c5c102c01e10084c5070b0b01890118850f00d8650100740980455410403442d00414625400501d034158041c20108003054003c3c0565a913454021300141310794540c200300c50035000d000801403806001c0096202c4c2024201101500300018641c8164000703510031800260003c4040050005841c403c62540030303900303540703040d60400c0e950001e0b41600714030076003051100101c0001d120340c0d02d2a400c800240b1014021034502e030504c2000c5030300da50900446000c80d041c1358070100c03050308206004e4000a210406100060390840d02003107403144c604e91040707402d440684003a80c0310140314020680039510414010300001c040e0320400041c000000c040100c1d01082000b2292010f0780f2150054120a0a003820200704a403201c3da00d001e441150844218810503080c001080503005840d151001003050640b000798984130010740d00e0786943d101141c00ca0455826101410784a43c2c000c3c40039440909002814401480700c0300e0030118221695440c9a299441c40300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 975108750 1250 975107500 975107519
    0x901031b080d0c1403130e010f090608031218010e060402090c070b01030206090409080301170c030708030d0203180a03030902040b010e0105030a1a060d0e011401032004020409110301 80
    0x405007501001401c0c00b111944002040600b41c480c01412a4004e4080141d44c40f130248212000c01280540500c1074a03100c4010701c1c000142071107075664460214000041c00c451500c5218140c03071407000550f2403d0540d04400409c0d6401800f58450001511000510041f09108150070340e80117501400aa03d400e0042100b507403030040407980040c0003003001c0130024442001d22419294101d03076842c0c1350700350040030800030010454024540d203000000415401824a0714840b540001003c0300c0811142e60103254450a8a201c1d02c041d65009001c5031029048640103958405170726a41c40700d00d06c000d46007080c03a08507221402e40c00f281d07445000c0f0007582024050b46800c0035080c28100141302481000070498131006001040f003d60310000f40c01030103070009099500715402403559850b2601840c80100800c0c0c40000c844956203002031540b0901c003091002e41c1241d030000395142142d10400b0f2a001c0d54035501000c2070f80541d08110106810100d4469400440420b0400756203d40c107180610 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 975110000 1250 975108750 975108803
    0x11119050d0e0d12031d0a021f0504060e0d060908090108010906060c0b18070e0a06060f1e030b090114040e0a1218030c0b1801030e0c040e0c090103 65
    0x40146030030040190f03440c0c10807200c0302e09030300800c1942c028545001c110000c140c40307100d150026680c00c41d04070110704009504508180200c40f4110a1009520f100e9200000c054a00011032002d0204024030f07405010711006010011b007461b104404c20b80c0d00c0204440518108a503240d001150328170195900030840c0303002d40030792541000f01508004000d40102c4040340010081d80700c100000d503052955402c000800030451086804203500e800f0542c400b100104d500e04121440c1c43e0700080d00910800d580303c56169181c039001c103088003562100d0311a44030410039034107054541003403c0039a00c401c0c5a42e4000c164000c2c08526884004080006a6004410400b9a0303400b60101c02c001c90603802451929100fa4100745071705802c2901c5190303d103155a070024040743c88070440025103d03020f90003800c46c004c804040c210080442001541282d0b40081d281d03400d0b6101d00c101c6105410300e6071102221880000c21102c1010071440007882d0702d0006d0f003080f101c0b480340c4480260186280341d5803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 975111250 1250 975110000 975110023
    0x1a01020c011b1a0f0615030f010b1b06010603020d140f0c070c12080315030a03020a020613090501080a030f0504061d060904050a0615020c130b01111905 67
    0x14064030401080020030716003403560480d101645001c01e10003088280b004582c440b101c400c4901505141140200c41d0760181110300900580046c222598102c508404881c49124181c01d108001d900300522000e140d041141c0300c030b05001c100892411002020090b1078001c0038583e60140e90769408060440c02d41e15003000d460800c0e1034540921200620b410700d0b050703218000003011030b141c1072241803503400c04d035a603030113841440c401084504c140315600008500c9842e281050030b150308404000d141d0780d240044000750050b0800e40c074010040c5007400080101c07648180200c40f0440d118170310078084070030030703070042d10254410200602015003002c4035002141c0726090180c10b081c1780c0000178003002041e41c1c800403907412642c40805d96a6650013524552040540100002d251036078101d8020800c0c1d0041d4801d00c184103160a40c142e00c0001d00290b0300401800c1c11080f51103c05045c0d0241040f01c00f070505010152511400740682041035100e0f10b401b0b01152903610440b4207049003044210b104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 975112500 1250 975111250 975111253
    0x5070614180d0210020a031103010905010302042702040c050d1404050f03030609040f0204090f030c0c08061e0a0e0d1e080c070b13081602180f0610211a0102 69
    0x8a24883d00400c640f00e854101d01d0026991b194540e80840040400660102e0300d0400480045000401c41d40514185c034800d4500700491242145910044041d58441c2460071440b400203030010300303113500101640601420a1070a2022500e10309064548040c00c20b03100d80d048404100501c2001c12810300502001c0c4003651460501002095008800920252050240b405520215101c1e03030b004c8900340707810a00d030040e10b500c00c2c5001081c40040c0c001c01e44510196100c082400000442ca00340070301003c0c041c1e5070b0580812181c101860000400c0002150760f5581950607000c2c06008080156003155900450741000c400100e003c004d0b01c4281104102e401c0702008241800d4800700c0f095960003040d509216540c50101d200c0029035040000c1c50203a0204890b00c0380c0080325203c200c01d910071112480035801408016a038210200c90381e144000c6818046451405d00c940e10034840c00551620f8201601d10340350044141c014007001100d515617a240d000c00c41d0f8188241c50b90026800d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 975113750 1250 975112500 975112513
    0x80a021302090a0b0c1203010b09010e090c0405010c06020702040504030302091f09062a050c01030c0206040b01030b04030207030b1306050114090a020307090302040e061e090d0c030507061418 84
    0x40100f50300c1d074010f01640b504000c0000c0d03651002c4a0401030160703506140030416549603102c0c4c0d404500342e0011000039000c00c0320000001c19500d0815400f42c031444018a81a0400c1e00e00801120300940e600c030142c0d00a035081161001507100c5000f80f521841c00794601503a10380081c01404030b507800040803a600d0000c10f050740b036540d0364000e01171801c0714810b00d00b4604c441c0c2c9a241d605040743c042009600ca40202000001c100300001c070703640b071030920b01340ca0401400700d8003e01641c43d0071048400034003289481c401440014040c50046030424005d20440e1142c5440390740340d240481c8265406200900a01c802e40c080001e50302585015003038542c444031304000180c0100701851806004410310a40200028190522887c0f22000840c5c005000b030090b5600203904688421003903414001c1e10002101100b0751030b450082290103030321800b0090134442c9040004840000207410224100b010800000340400d401c2d005101540c450011745041609000c0e807400e20358001051411010b82042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 975115000 1250 975113750 975113767
    0x311180f01060302071a07090f0f0506040b0c0111030109060828020d02190608100f05010c080c1f0c02011d030a08040521030702010b0102160909020a05060301080a021302 75
    0x942074111000c1c0d00740541c9601c91440c0c0060000e04414074821042c4c9800300304800154024542e000302c074039400c2c0380003446da03c1d0010142000305900aa0b50030a200b00010402115100010045251400c1c000a0000d0b460310070001c580e4403c6c1d10a04071591150800d1101e01814400b0f40d82040807680086038800020220460141000d100a4802c4070858041000d40d1100d601e440600144071060b560f1a544aa001031304000c4241c400000403d00860003041c0303031505031131150035a8416142da261456880c2c0d40c2e0400741d40310303000105035402403820411aa40c07840e0403500003000c0442001c41e40e40c605500003800c48001c00791641d1104e202e50308041601c0e10200480380001517501d0400b04d01e44c1c0340d08005181501c811444001c2411403c00d03449401d500300099800b138135036a4000d101c0e4202c914012039851900c0c240c050851304154204201400701e40d1700111300d0500c050700000340203543d0350003d08103030001da025901a40015032120114580360102c48444c0e152680d00f103041401c034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 975116250 1250 975115000 975115021
    0xb01090e01091505150c0c030a05120309010204081c0e030c010915030608031b0601061817100e0d09120b010909050f0102192615040603050304031118 66
    0x6200e00c0b18500c1c0d840c400c88503018114015000980340250000c3c028528034544650306a000185248050185000002c01d9240101d0700100c15a04280145014a4203051040a90307102415800096608000000380104207000a1480b84c1941c070b41040e0100c0b241c140504079080a1103850f120750810f85051901e6171300056508281d0b900c4942071201480440c8087c0c0c0180b420341c1120750507200c042002d001610840d0405010380524070180d49040e41da40d076054030141c84c3c4091007040b0840401742444140780000202c05048043c0c42111301c030382a485400c00c00c841040300030700c5064214a0384080e40940040c2c3c0c000081842d140c41e01065009078485c0404508180100180c007a2100001c10034444204008142011034030000c40d5140d6030f443e20440c05009110402011580b003010302004000741d9540d16100c2d80000888691310366481900b10b000c102d4180d9040d90165940c080400491b03820000fa002840c03207804428001c0c141c141c00c000d9003840300414501110407040411000950 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 975117500 1250 975116250 975116279
    0x120507021b0f062208070e36060411031f150b0c0c03102a120e060f18070605091302030c030a050609060127080d080a0b0109 55
    0x607922071086200d88400107521854446006602c45030201e0b0131031410841000c20501d54441c41881401e480c0c0d501c550300d4035002d081c441c10481d5071010b00001c2c40890228915107603801d04841620784c1243c00c90300e0728480e00304a00d0094080e8406001c0104020034409410800d01e003c074020b0807a00856000491501d610240c1050030356211500007116411207203035500a08000c406441d1180c0c01010b03100d40d521251403c0c1032092003825500281c500c100d100701c03035110003080711030b0f40742c10003c40c540042c0281002c14201085100c40c141040c03110540300c0c00c4503504826000e03103000c1c107001d0150992540080e00503403003c404584180b622602c0001c4039400c40d030701d0b81441a11815824001900c2010b000e03104803030355000000b00942072080e02e000b58441c0031a1030003000192907030401d20105801c02c46281e80814181100c942820b1215000b401c1140e40d00e00e410445039440d051201e04000f9048849d00104449205024501104c1d0095200311070007842c041034041c0c94070303411819030700c0e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 975118750 1250 975117500 975117523
    0x216091815020c06041203180218060d05011b1701050a0e0c04090906060302031905060114120106060807020f01020315010c03050c010e1b040e0a080c07090608030a12050702 76
    0x18001d20320761600c0840d501581d09080341075007600c600e0f03e4582401990082e03034840c0c11000a1501c071241480750504409005030b03e80107481e41e203010562a0301c88041d070710058000781e07010b01200680d0000440900400b2000001520440140601101d010f4200b2240d803202400c646070441c018800da40301c420010044441000005a0740e898824001101d0321407a00005032003400c04149200344041e981005085a1003a402c0740e010210b07a40741c6402031440e8280041041d04010010084408000e8003003c40a00043c0000085c008008007142150303035952016011407444010420050b80601c5020b0551210310002d510318600056007103400030400300f0881c103101a01d041d0380d040c148940261b03810302410100821124150740f1030302d9a076500b020b0303000402860166014901b400d1900488107041400d8008003484000c0f980c8001d03072030b003180801c44a2481a1180010074424078000c200043c89180b001c1c0d0340e100500c480042840300211442c3c0c4146042c42e0034040440da0000360002c00c030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 975120000 1250 975118750 975118763
    0x30606031323070f050f01020d121d070801050708041e14030c0705120c01020604060245010509030d0c151113050d0215031b0a02160918 60
    0x101c1c860700d8241e51400c2101c030300005500601c50b2000000301c000030030105aa2481c0902c60800782c1c1c0e4800c00c000b00c680c1491160041c0c000c1c500214a5500400e00103444084580e000702c6c4c005801a00c2d8045200e54507644000360748001f804100281082c03148d0b0b41c010000e480e200f446e524040d1900920020103e16800d031801b049420081841003120300c10403d40c1d200001c1d0303540c40ba000c900c6640d03109803501a1900c00d081d10b0214107411000000c1c000702c00003040c0c0140c403160b600c80d15500000d4220000c0401e0b42c0740366449050302120a00c590807840da0840540c4109010003881c0300d116030088141003030602508101d084190340d4000380030541621a0700e05045004c52a160a0140341402c285c03004030036081010403651080305401610061089a04200549a403a81042100c00c00b03c10701a410903440402c0c4490004c0403030086034052803502c6950714075100c13842e1011095009a69a40c0182c02002031103a803024914807a00092194910a0240200300000060803c590600003085c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 975121250 1250 975120000 975120031
    0xc10020309090619231f020d0203041206021e040b0406030b0a03021f0309060c09050906180c031e0705030a050a050c0417100c170a060e0606180405240603060603 71
    0x11408202c0300e001e00170090301c0e690301841c9800c40d441400e640080054054003d4900c5103402510000684003140c1d141084070903121125128180254000c0004078400c1c0c06802c00b8a5034803070b030b64001740010005008400e55580c6040c80c01022224555003681c412240024100f0150b03030f400c2000d50a4036000c0c03904840260032800140c00070900700b58001c1c603050421201e004203542155100c0c0803590305641400e951b946003820400388681602d040707041a5085030108031000e1104010f558030544540c00580743e0082c5c4e20b102d4a403000111605000a14000108180344c803903800341725000b4088402c203000a040044030404036004500494419900341c02c0e520303041007010041080d0302c4400381010000c1e921002002440c0c4600d1030981340c0c004940001060024810344141c10840710341c40703508501e86e101c41041003810752011401d090340d00b200c16010130982d910b900c2890300916040155082d031401043c090b12160400d13000c1503104134000d000f008560b0b01d40710101c82d80a550b40001205 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 975122500 1250 975121250 975121289
    0xa0f0507021e041d030a0906030e06150d0b0901060f05010c1205181e010807020d210204090c030501060e010e09062107080c04060e25020c10020309090619 68
    0x1448801c0c01c0300c500c404c40401800000502100800754108651342c6c45640a4641e42e0a409032995603407201080e0f4444000103180d69650491940c80040041c044040380116440790401c01300250703031500a5075983e070010040b40140081800c014202800d0095100301035442d11528a800f50420340244080041c264080306002d00f041401501c0040c24100c11210102e4050840045421241e0219001d1004901864000203801950018a56a032030308a0f40911141008a1001d010b20740e0b1550207100102e1041c20078010031440313000b96036000842c2d41c500a4000c0c090810303814520705000780202c00740d080c3c1c1c84089041e5800003055030200d03030f0600d860020072031000b15032001e24450b0151201c0890b20303510104030040c000004440a2055644601c0c0c00c22213240b0603298120005182005803d08800c4036084119030407450042d6140c0c0708000010545902100310b286006270000210b008031494484034091b00094156406c5240400f0a5407800304080ea80c056001518580454010b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 975123750 1250 975122500 975122509
    0x5070228030e0a09090803060a0621020906070b160f030e0c040e030c2508071503050601183c03030c0507031209030b16120905010b030a080a0f0507021e 67
    0x4010500c108040148035178a040c070ba01c041d04142e038214400c01141c400080c14501c500c3d0140d001004e000ca02010305102c4480140095010504d9103030807040c244058408240c80c0b06056116022100c0f4510b005401aa002000042481c41002c1454941f409102d0b58500014181c800c0d080e05840006402c4200003406155010718506031529225000b04940c407008202942840307a00500c0d480740d501d5464910b105e4540c0794030f0240594401c00003203c2d50900c0e209802030307500444181400225416600185905541d442d0050800c030060552001c1000c0d1b03d081c060002c040141d04155040c550004c0d507400001c60070711010f41002601a040c2c014410180b0854005540c803c0004440c0d5003800070207005a607031840291510b0302d100000603800442c1d90000501c0b602c03182d99000198800410440044c64030f800b00740e96540d80c9400602e9982c80030000c1d071480a000b003400310344955030048002d10b1000c0c2e0352250410072070207010140c01a168509003868104661104d041d600d080f010104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 975125000 1250 975123750 975123769
    0x1090914010e0304050907020a08091e04060608070e010318030804080f0a0206190e070e0c0c070e061903050715050d05130b070e010507080c030702120105070228030e 73
    0x61240354030385003003918400000002003084945c159085602552030320400d98558407801c82c0503180d40e10402012200d4a40500400c408010b000c0c192000c01c41c10b00c011130200d03941504003c004c18800c1c02070054050704070032283c00c81202460240071428151000404142d01000004c00380040030010074104002c0c0826201c2c4001ca1800705500c60303298001c002c0d07a40c0010b564500c0354411060002d95a07480e20b024020313070f00f003c007001000400d00d480510201610f00130007071401e0f21420300c440c2074102010704c40100245841c03000004241041e504018082075411a00340c90704081d12010400130300f01145030310484010f07030030500220550b0306080d102486000500110035103840d04002c251284003a20171241c900482e81d2aa9a40d1030300f00030740319098408c4485000c03840c240200800034200318010416a0403003410360703040100c0382d0b011958510141d02040640e075102e508114100380d04001304045074015000c2c0c84280411078608034524510600003034100305141001a0440c3c0750404007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 975126250 1250 975125000 975125033
    0x209040201030b1201060509070c08030619120303140903030f040602090a0f080d1116090f020c0604031d0423070e09070306090b0f1f03091a0901051e010909 69
    0x1d644c180040002e0756000309804e002d4640b06c2e40e8007001251170588075841c120340703030380e40801603502c1c40e01c4560401c0b1800600d0165600440c2c8450300100e00007015400c9a03e0013403203610081030b5040200032024404c0d10080108003203901c240104444244880c00c800d81194210000503603500f1024041203209002c0e804c030740114290381d50005500240060050401140740d03880034464400f4030b03070640d01c80c0d542191031028885118428024203401d6031010031042c1036450b00603c0c24158250b014149501100c084d40400c98003110416003414140d40c0200d0000102d900b04444000140c1514120380c21100c0041e1081c100d60028100034007590910131782c03a5004010550354074062030000d02629440c010350700f2941c108404410706003885070300900c0340c3c50010444480d5140c2103441500c27032030101000004064403456104c0c0864103481908010384203141c600e2885140c4060f102d4203442018000030403800388421407101300800048120f0541c2c40304040490810400e08241c0400c9081050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 975127500 1250 975126250 975126259
    0xc130302061e03010312170907271a100512011814010e0702010b0306010b0301060c1704060e090c0a2c0301050c04090606210c050d0e100501090b06070209040201030b 73
    0x7109005110300303000b101494075034809003051f914000421010809542c000c2090340200c90601060161034505e000c00c200c42c01c940c1c01c1e082d40c0c509030041500c2d1203210546544580c81840c00d0710f03080c102421240d611301402c01c1071030001802284200d81c8414865070424860136031001e00640315942282c0000300401209005a584a401c0c90309440404c0e075036800558a448102d1350982404240181203c7c0c000c041c5d02d0650b031800230299021040d070742c021108101584070010b0311030358283c00351020b070060f5529a1041c8c40d022050002ca09000b400c40c80e203040c010301c458000700354400b83c06003a0503507100141d00c5080030002e03085001001482400c0d419402c003010407003403d840c180039104035921000c05004641d07440009075020640411028092803441c1069001d41245030880090800245005072820801681d401c0460390700b040d5a508642141030f0075488040c880c001e4902414040008005240302e980004107184120381c002806004d0003800038095a010790311071642c0c80000b82 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 975128750 1250 975127500 975127507
    0xc0a0509120c011b08070206030403020c2e2d0905030703030e1003020f0d05060a050d0605040c06020d09030213020d05040b190b0901060c1115120c130302061e 70
    0x768015100c90341c603084140064000320000003031200540c01c500c40d03070390407002482c07410700302c3d40074498070342d00082c0241c0940c40381a4050b541519035080440000c907012903654a00700140340343c200c0c21480b1268030b1041210840c46401181c4074034040c01c0392a00343d950700036026248003409035021606648460303414050b001c800820305400068040744d0b01c904803400f0700940c01280098040f402814040803185000744200f4408000c6079008030340040000380013010750382c5e4803030002c0c0f0f03403004c01c07441264040d46480030720003089584031490000d80306034005002802c0c2100307030003000c0a007548006449000d8041544165080c264100c403c1e0004c500d00902c12807900b4101188003650603185034240c0071403405108101c2d1000d108403209402e00600e0110700340d00e00042118a01506d0b8007c1d02c1c0010024450720080d5155428100f9101d540024183c440d250481452010f8800500d00003002104000c1400d0004894040034203490b030448003661500d840c41c0303086016891108001e494600c001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 975130000 1250 975128750 975128779
    0x905100c020c040903051204080c030712230901050708131401080c0301060c0f0812070207050a082d07080307062c070303050f0c030d050f07020f060c0a0509 69
    0x541003121419816002c68058a2045040c08100c514009000e00014810301000965039405c511254000d03000301d0b4501c0c10005280710301d5040d50f000c46000c540010411001d05006a0480c0181c40010314040b01c00a09046280340c64000d449140c451078100701000400404000c9200300341c0e40d9050062080022154540510000300d031802d0a03070301c2c0402c040ba00000d8000b803003101101d068600e1035580d83e801e542d407951010307444403d2840803221031000b070044001020000346004d10880c8181e000b000f90501c0c14050008848044c2c1110b44942c001d1041040700c2c0700341070102c00100c89416000c0a681400181080c1003615582102c0860f010004403042402115001a02c6034443c500d00c82d034071000500c8002c0d0301036452003624155600480b00030800720780100301504580141506e143d18124181031001c0c299400b041020621a54910605c00c0002c501c05640c0c1c0d01440c2e50008165500c03652040705c2d6100070080800c9004d080c00281c091106c1d111b074055507038a00c00070b0841000060700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 975131250 1250 975130000 975130033
    0x11403120d0204030c0e1e101e0b1317030c06130c080f0607020705040608191707050102070620030f071814041a0f0f240703030b01030204140d02040905 67
    0x81c0c8111f101e90020395150300410000e600158080c86202ca18454090704d040d0002c0324076994942c20064100c540003002540340b1800000b400584e0b110031514000d2070178110000c3c541500840d03107100540c000d000c0c062101c40006543c0d07403c00c1600180c51058480c520b0076078501c0c55140c110448034001c440030103408042c00642140510095002c4c4c402080e10b82c014802224500d100742300b81680810f00d034107462090111680920b030b0007601007001403400c801195a03154440002203886030341c0010070701c003448241e114002c5440d4207052010038110300301c03012080740d000180c80c0150000d0b41d10089104103000703007401d4001c20641e020250070305980f2803410b0820745100c0003c900480c10400241400401050a2031210030010801e01e01c50620030240010320100e000b0154105407082000000111900203449000c024408602c1d941c481a1800506403500601031034140341c014442030040300c3c4c1141303074010b0209003034a850000001d85d00005003c0c00b90a04051300d94056a802d500340c003401c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 975132500 1250 975131250 975131279
    0x80406020d090503070515060a030b071107060f030e0c010503221a010e060d030519020f0a0c0810020405090601030e0a1a092103060402031b0c070509011403120d0204030c 75
    0xa4419500c120041045540507c0030840d5440c1c0e00c9054910280300007070aa030070454002c4101c0c5411040c040c3d0101c91507181003019080200480c140d4040c1c0010a64180603002e084c0c8416409000d495150b000084d055003c003600760707000d509100d10352030b43c65401d8a0301d00a019400009d0008035100e440d00811624a003800783c460164081c0000404505041c4640f240c410380c56074030113181c158443c6000d5401583d400492046001d401e000c444c16000402014100c00d0040441c002128a03206250346805108070300c0c0413036980140701c200700d02c1d5218050340da8400c00a080208a400008190b103080c1a51004010300d0350140040021001440b8900140f0654092080729900001110010304000d000440400b4201d01040040e0590900d42c01031070700801807001c1c007900c604619148003401c2c0c108a1071340b080c40e0300c9928100000e00e01410628010404040700f100300c10004030102e174442107243c0602c3d110020009155001841c107504135401560001900e07000c040d15050011450b00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 975133750 1250 975132500 975132503
    0x70803040b0703050f04110a0b041e081c080a38010c020a1205160602010c140c03070303050606040b0406200f0a0f0c0306180c150e01080406020d09050307 68
    0x11000c1c0c0004110350700070f00c9203a000b44024043d044166456507200c10400d1104a02c1d030303421045050002861000c614007078400b510481c90240703201d56040341001580300301c0d40e01109072980012a54200c0441c003810300d04401c0c01c5442c0ca003a495486210400181440f11141010355411005003c10550f20301c01443c0c4e240309048011084c40310000044036122400704d000703548041101c00c200000e540c4120781e405000e10450684440384210b0700e0741c0c031249400da402200541d444905810380b003984130404101103001d2021150522822186407540d90146940040c00e06036a5000f01e00f10795103032026100103103511120380d950f4545911004016102413480d051502c414003000085c0603a0100d0040003080c139103401030195840750b840b80e421641400034180c40b0784141d0480880403804034065090071000031015030780d1141c500c0c581910f4001c401da100c120400c43c020051040c05910180d020220b0300d09103440c003c00e80716400c0c204024400d020721001050305d0190b144041041c084040d200c0710f03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 975135000 1250 975133750 975133763
    0x611040e04030314060121020c100e0a0c0b04030803070509010905031c1d0d021e0306010608061305070e060a05040e0906190c0f0807021005071110110d110d0207080304 74
    0x2a200d000040d02c490b2201f001084c0562440c1020055030a8183e006d0685544642c044410085180001e4003c440e64100005441d030801c803c403c0a1010554044004010034800245031600c0c0d40c44001950002502101c2049800100c0c0005c581c4100d00d0003024000003002d480154111509071101c0c180b0070706515001c604010800c03000080d4540b204c82d146403010340156604901a401c02030841000b21200e8211015580701300826101044414041e0075142c48020032401c210003004403840d40c071841c1400d01ca052100b0006e41e16403005205443d44d2050ba100b07034403502d001e10140d0300c40c01160803e4601d0011103040054050000400500600031141741000030313001081550250342d945240200401c0e9110035800ac418464885c142d0310900070320540e20041000e6582c88182c4400340d5001c030000d4412080001e0041f0180700d0805040b8031b0903400c02c0080f03541100c00c1424003841200358007031a80c8000c034100c242c2481007240c0386100c4462046648884902e810303034140e0000e8a080c1c401c0f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 975136250 1250 975135000 975135041
    0x20a0c0b2d060a030204020c100501090c0e03030910110c03060c040f0503190206030601140c01050a0f02070b040206031819030e04060302130905030904060305030d2301030611040e040303 82
    0x5a4501e6500804000d008204000e00307503002e200c045d44c0901d074180c3d824802c0e20b1600681100c144900740c040c181484001c100c00c004140001c3ca0600710000c400e101e41c0041004140d181d5400384128200720a034245414400c0444100b6410291907031800c03034050017510100f102c1c4048030070082082d83c6410094000702c2e916041419070700c510070503c08140c00d1140140002500d0000f000d035902c40014580049080c10340391081c1e07600e810428002d03007580c3d12a01400070002550040f06203202e45044d0450802e035085d00e41f00c629445c0640080e00900d00000810068103020110030070038001c4e04119075036050300b400d0000117545070f1113007503000424040340c41c08030386024040c107821240c000309103c0325416014404401091004411100da100803c50070710b035520781d801440001d41c001d0020f5903d1300030004801c403d841c0e0000c555910030f038548100c0405a040c1d0b95002c0e05590b082200021180d42911034091a44641c0e08140b680795014001c0004056042d00035607240703041a00803600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 975137500 1250 975136250 975136321
    0xc1208040503180d0212030910030506030703170918090d02010219122d0b030c0d08070507050409080702041b0203270612240f04020a0c0b 61
    0x2111041680d004200b50410040c50591a0030700c401c0714081d03074004044180c070615503800241c1d4226855450031041d00082041040d41c50b080062807400b50702410140040e1601e007000139201d8116000082400024007003038280400701f482515078190000e4402c081440c5410b0303a004c00700703008a4048a0b42d11032042588031061042c003d807070f034180b5255135404220700c2016090300e140d0107400d202806180e42d20440291444018202901011600b01d020751200c140d03070383c440c140c4004004250103684100101c81c02515a41c0351107024a42207820309484000500d4141d0800700b4a0784469441070402010138103100340f48006043c098400c940c2003005200705a428606c01507141580d2001d0381040c007141511040c040c003104182c103410403155083c9a0344200140050b00581200002807010004015040740d8402c41c2d00900401404506418031040e000583c0981c1e00c103804a000b40d4002c07501443d8503015449140803030f03074020035050403031911441c0309103840107407600740b0580c41940e0b69248 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 975138750 1250 975137500 975137507
    0x212030c100c1101050403110c12280b012408090c060a11011d240c0912010f0f06120c030b100b0304050a0512120a09210c12 55
    0x106030150250103010001028504400101203942818080c40100308080c00380071030a12540c0d10880c46925040040181a104203191844100c59a8028000b0818150500303074005420b142521902c100604041c104400aa01c0402400310041459455000114511030100c16154031081c109008141c100e202c0f04040b00d411109491410460b0021017042a545c00c00c4802001001c0e81402c24a95a444003002d05084803540015a002d038111100c0c08004600c041c0640c1301c00c03e002a06002464601200c484c183c8030010f00120300c40c0000007117803681501c075000405840ca05800003000266000ca40800150880d080d600045900e0101b02182032080406503485040e04815042100c0d411940e9000340c0510140c40d031149523240756000142080c03610300131442940b103100984140b1a0a151640c580f400020340b074085104180300340c030141803540300c8042c0d00002c144030200340e8455504012200404444110030240c100d8800001035542000c010b1210a01c00d100225030040300d0708048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 975140000 1250 975138750 975138757
    0x22109130509060f161413140a06030501081c02120c010209182202040f091a091b040209010306050406060512010b030108150717010f030506071103040603110904050c0403021203 78
    0xc010348020405070104a8031480e01c0d46c0441030b46074203c13883d14003440e1014801c40b00c2988990400c0d80404417402003401c0c40c00c0c00354000c00450074140469410910381507202c0000c4844a003082d034006100390011442001401140c0d040c82c001c440d0344142240724075001c2c0d4400c6102a00904180864180410091848070320405404803110055090012800454100c4400070782e80a51240288a40c1a02e02d1142500301489580c1d10744003440c400040c111008070090445502d500810070110050f542c07070720030101445040300e00680c0e80020310010b03802005190081390f00580b41210101c1e0300c4d80c000c401004404a48450440540c1c0e842e001038501d48804d000c2c105054101e0880c04d1880204208040c0d003103c1e0605028030004c102031003030320556200364401600a00110820018007130140491500a4120304d0107500020f5074100190b50fa1207544140d00c01c040c0e170307624409602d00160050b1008400020f20a120324180304010700d005030003500050b4403911001400458120000048 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 975141250 1250 975140000 975140011
    0xd0c110a020105030c0d20070201020d0206130b0405030d051501031406030d0309022232010e07030e030309070503120711190b0a0906020d0f022109130509060f 70
    0xc0f1899559080d40d40f5110360004800740d48030540700c0c400180290f000c100e80000d0490950929a15036100e4000245000341a042c2002950400c100b840101c148402c1440c0456420038000303c3c00362101c0c5072603031460ec210081420418980020300018a00c99640900c411500b660b040c0f2902d421004581a54401510041d41c540c7c0001e2159900c0c5010343c11078100c00b40001c01d40ea55400d20441e4440803007100c501c20403c503a41d9070000700030401000ca0610000c80c0b40d2451202201d0100e03500010400c03042c060040103200780400104498865080f10202102c881c054039168107000141741c0e82d40d161800345071310902914801900b0344d44007005079200d264005000003080c0c0c04036018441da62004002c01035070300f12405408500700711801c00402244119075504400c42d0700d000b0300282071070365003c2040101701e6454160440b06900140d03510a4103c9a0b8180380d1603a4049450105449040c1c2e00503080310704015144241d10141e40000e11404001050710260303603034501d0940003901c04680 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 975142500 1250 975141250 975141257
    0x50f09042301060206040314092116240e060f07031e0503041a010614031312020d0f0c0305270a090c110a0c1215020d0c110a0201 57
    0x20040526264212051446605262000c1009000003420100d0340980001004d07a0005081c0070805500241003c10958036110207070521801c00001485848102d0094651160950030740b074000030244000740440307010113803112019a60f508001000000c14444103102c0c007110386401c035000e000b85001245420010503641c9080c410302401ca40c641c021640550400014000260020350a070041ca0525440f40d05c030503451703140030300c0c2504090f8802d1840b42e0f051143c1c24010811143c11060980480300304210181e201e69445041641c410007141d0050b04a500d41c070907840306180c02003440c0d0784020711035403a03400c040b442c08410380700d14050810060004508110041a21808600f1490015010300c0e02c207141c6004140002c1c4071400580001c00c1480e0b5030580c581155800c4040c80302c12070300c0200a418090342c02c0c3ca844840c2c407000e10581400d000400201c40800c0054030003803006110b4000d00310340321f10080e104c100c0100700343d00c1c80001041e010341007080346040c00241c215140750305a5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 975143750 1250 975142500 975142507
    0x10b1e0a060813231009020123070c0303080402030f010501050a05090a0f091b0f050f09060619050702011b12030c020a0204140906100b271e0f01050f 66
    0x1c0c00b200c40d588010403154520700800d4004000580000040e1090701d00c100101e220201c000d1070180c01e00001a081d040d0003481c0904400060360000030380e001e051300f41064181407a011121800003807250007002403071107008001c04000c0541100c1d00c503000714000e90445640034094005507080781c0c001e0268552054031120104054035148103a10790003446198042071003a010b920840c181c82400204445d0160110010070b101c0609a143c20700800c40e41a2075180707145010301180200114038492030245031403200181072610380d00300710751515003140e0305c03041c0401c140c10004229820400e4100d0000f40b040144240d4512800076013081030ba0404040315079140052403e40003004140310031400c0d4000c2d840d100025035164860301c00150030301c58640440b03141c502c403058200a0000c1c1464080d0304048014020142d03008140c0350390f010440c214035a41400500c0c0c80f10650340f16a5003951206c0b01440e002c480c11603120024050407000d41d050080c800010005444600030f40409206002051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 975145000 1250 975143750 975143759
    0x10503060405330f0601020d030b060d0f240302090a0e1509010b0d080721050f0a0504090e01140a180b0c0417060f0912040b0a090512010b1e0a 63
    0x900e1441003a020a95642074060201001c1604050203d600404c00350002041092658041c004545513844601d420082c03410b50a0000d500c1c1d00030080c2d11070b50700d6981c0d941f40c41002002c1c0d000f5451403090242c0c090107100c040120104040c01d60000b01c0c01441201c0200c3d143c03800368010800311740202000381064180c00002000d40c0800184928019900d078812000d894503650107086240b8001d030a00f81c2c0c0ea16941c2062402e07600c4400403100507075404040044a00ea01609603200caa041c02c0440e40e651055120844440c000d94000060aa00d0402441d0324128154420b214800054090641d01d41c0e881c421441100d14100c080a03060310700d07050380000940c1c44940c1c26805440c0300401c42c1845d403038000c508012481100002081d41c00f41c402d1007099400a80c0030369000c411301008100c10903003082d030515240110f2003803960000c0e010510300840b5004d00c034600d002e0400600749801c0c0d840c1c6085054083d00090b80000e0240548a4444064000c03290b048440320002410040c0040e02c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 975146250 1250 975145000 975145033
    0x7090c0801062712021e0a1703090901090207060e12040506090402041d0103050712050304030b0a091202100c1814280f12110111010b030303041505010503060405 71
    0x2111543c400c1e00c1c110281d5540c8a618a03100c00c05000da00d00d0030541e5125500c144107031000c886013a440c44490408454103da90f80300040030a560001c100144109103046000c1d140d805601011a031000501c000801d0340703081d03940034040d060301a403000e00020980040d6662110b4418500251443d0200400d2207075040040c001e00d200000500018902a0b55000340310b2a1240f0011820082c12042e00403c03d201e07081007400041d10b100131010001d8102507550f070703031b8030f00c07903888002e00d2056040c0000d409900c0b65440f224070980c001d140c1e4039802e200381c4002512030408400c1102480d1404400444481c8203801100800940c00030400400d0300340341e02444441d40070514150701a8500c0b840103481c009004041c145180c3c0008480134440c10b1184005e4a201c42d9000b4034800e9801c92942e50109604200054401c042820141e608260700b05207103014003500d116040c0c16120020501c410020010f40c0d00741c3c07004010380c0401950740c03148100b544070041598090480d41c4118044c1010444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 975147500 1250 975146250 975146267
    0xe0603060c0a0c0c0308090909030a271203090e07030c1403150a0e0108010b0d0312112a0601150804111804050a0510020316050708040801140907090c080106 69
    0x8041c02e0405014440c1d0f070318020f51141a17081140d1161020640c854941842412385c0c1d08141014082c60402d01c0d5044020b0644160071070046504c102c010040400d0b1a6402c14170300030780143c1340c03007411074100d505018103c81c089201c0e00c034001c0300d05400529260300c0380c4580b62000d08030342d42d1000f26250b142000402c0b5007000e09400000305140c080340a003a920400000014120041c0d001104c0d890001c84608407520302c41120300502c11020b1a81c0040e90002c5017140c410041303c4000f44860142c7d0128429014000c00d04010001e0344004080c00f07901c001d400c2d220340f06108200c84841e070b01c1e5070805400f640345601d000b020a00d03500200d030002e04060114222520040d041003c0941e124049090541c0c050794140ea480c1c02019822003404001d024402080c802c0c120154654109000d51401101c58285102c0402c1f00103e0045c0400028004540003412100024003442c062510300c9400c0403010388862000b44542500021404801e00491514050f685c03241c104580ca0503909980500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 975148750 1250 975147500 975147517
    0x60320070c050a061809150323010f020706060f06210b041a01030f2a020f070e010e0112050d14070b0903030a0e010e0a03110f0f0a0209010e0603060c 66
    0x8a216020405440741c83e285401080241d89010100254903608000b03032805d5041001c12504103003e100d03031038141a402d2401c0382d5000746d0a144a84990f65901251140100482c4055080481d14140b032a000c2d0040c0030b003140110070400c151961146008030003401c03882190302003150b40c107500c1b00d012606d1141c0760701880d80c0c980216841e0701401c0068204c400c0303c0c0c40001e812562207030040e0300d540e00d44501c0c01b214045400400080c0010031540311403000c1c80240c6681007032400c02840c459482844980204414427003115881d42c0c4482451518250074001d03030f05441c90070000062403944103041d42d0140c40d0000054440800b80c0c101c1214120141e40010101030343c108400e20008101038801171040000d000903548a0900c6070022094070380031480e5100f03503030505114004910000c6115000780c0d0b1305040048582207100362150400c0d00340d01009842d806a92240c4207040c5002c131b20030125034400c0300c00c80744503038952143c080d6203a0300340c1342c0d43d4066001800103103421442200030300408 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 975150000 1250 975148750 975148763
    0xb0601050724050a0b0103050403171302090a09030f020a1a0c04050d05010b0111120909070c080c06040b060103050f04020907180605071704051518090f1006032007 72
    0x140242e081142ca89400301050400707070f80d4004004821000e481840164982440c0c14091824191801005c180e5004907608112045d40301049058007880300b858117095018092120740d20345001a6001080c80c07060540220700d8004050b40350502c04608402407903400803940c004075000402d0304869000c01420b03803900f203d003000003181640e200f10318a801c5620400010901c4a04030000600e200044d9100c00c031350b941305050062098066200b46c0d90b08203010703621003000b55030f002c0c0202d560010b103c0001d864010001615280507001145240c4901d0140816401070340355400114101c0b0030480748104803080280108006207003050700181c12584600e42a074180c0005001030b0b94001559000760041a800941c000400450152520a09200d018a90f00b01031400020448120030300b250101d1081d00010305040360014140410b080318005080e12001d0300c0c0502d83c140b850700040c0c56049504c0c81415002072030760303c0f0b40a031400500c403a80040f48003910f8985009034079040220100c440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 975151250 1250 975150000 975150023
    0xf041509270c1107030809060403021c0c0509060d06050711060a0603031716200a060605010806040506060d09080409050702070f0b0307091703070203100618090b06010507 75
    0x101c40104052044224004940e40403444000e561007080740d40d100030103018007143c140310b158040e001150b0841140c3e04880040c0c0e43e85a05000161b0a00c15030300001c0d80700a801d292190509480c0c0242d02c1d04a104101e01c5510a0301d03402040241802190312982c84170f82401c5c01000200f46400140d0014928249008100d01c82c15600d42010002c488180c07056503036450400915501c0204002c514419845c003400c01e00b8445030002c0c005d501da03500700007031140940c01801c20082d91036801946200396416200035202518110010f07080386d200d424002200c0c00085001c1d03141501c940340c0141c00c014205440c25032003010b8000984205103080ea0044270a1100240e214680e02803544aa00103038003501545062111742e0070300986a400c5040e0101081c0104007800b500488046e00b03540c181c0d540e074070344890190051455449868070094041c0030b500381d400783c0a20140c0100c8241c0f550700905d42e240440c801401412100400f03006814072011201040b0194001d0008100c510b01544e008400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 975152500 1250 975151250 975151259
    0x23090a080c0c0a080102130b030408040302210d031a0102032805070c09020d0c0c03080c030c0f2703030c061504110c060604050609070509040e0f010606090e09030f041509 75
    0x51203e1581d03c5101640d4000525079401110492500040c2441c50b03541400d50429480342c0d032840c0034078000240118813a410030803145c100d1512003c84000d00404444416103020740040107000594000849409100103051581d03002000390b07481c40d00c101c0c2c01c0f445042410189003a020841c4140601485820887e2101081d000c03481280a015560030150351000c5266240c002c5500395200f00d010010596000400640e022500541000b440c005003a01c83d22070908071010740c481c0141c4e06030070380400500c0d944038460030f0921304190300300105179244114102c3c0916840e442914400100d13070b044003000880700014801c00720403088024000003008582c4141d40007080d440440e400c1059031012003040800e00e000e00409500000c20758080d4100d0030016009052409079125644c032464645032608010038041001c1c404e8000024020f2101c90364808000e000c51089000300201c2121240c00074001c030200004641c1208000d40c00f407803805207042240d03e0301a080c240241b0420840180029 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 975153750 1250 975152500 975152509
    0x90703050c0906180f0901030b010b030916150207090c020705120a1406010e0915070309061506090317040b1c020d02032e140f04150923090a080c0c 65
    0x10780d020f10b000303004c240c1ca4010130090f04120341c0608a100c1c88415005000240c06000e809044a41d0696801c0d102d0320f5158100b407d0100088203003010400503c0005566603501c80124100c082d150260750300d60707407100116420355580640003000741c2d001d410f00304468242001c0c2c15510108201c01c0d610f4007451940c4504030402c0b00300c040134183e030141005100b00b058080d89541c0066400008108041c2c14141417000c0c0d04005080302d041c1940d5a40d00401c0c4a82508007454101115071b410603920b844d800c0262142c03040c0e00040e1465170140500c5403294040302c0881d000d60356001d402d1340c10860050340c10301c0601050813030102c510342c00740542000d40ca5035001a5001d81400d0213070b0740c1000464040d4550000c82c40781c8030904021500c200b0010600c515046140d0081c050710500640040440801c002c5d00c020104034200800080d000124400c203030f800f030305e05c05006240781c074201100d50191041d05201030f81c0b00b411b83c0c7c1002e6112000104050001d2041264500603116000603c1d00002e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 975155000 1250 975153750 975153757
    0x80316030b1e030304030510150b071208040206070b040804060e0d0b13081c0902010f0828020403050712060c02120d09030306090510090b0307060e04050a02040e0c090a0b0702090703050c0906 84
    0x170052300d8603800301d5442c2c00c070005040c170f01800c090703c40301c4d041c0f0702161101c918a10220402500340315003103011809640701c440440344196081006d048242c00c0030715280c2104d9000744030300f800042d0360100c00740561410344041c0003156084121010305844803185034520405c0e41c0412694a4010040031213002c7d10024100703100f2280803400245004280009400014155110020490388104215981506103401950ba212041c208504a174007400c6400007071203503400280c100e2042031300c000380c1000c003040d0701e0a41520403142405541e00096040e0303920909029901c88046052000351010301c080c0e80000c1c07050740249004030783d443e42c2d66030301e10885209a0300848000c0d44140f09015012712406103c0c03004100f41c004102c0c2da4600400101f410592184040c840ea46880100b1500019901510050503480030b294905040c14004002140c1c040790400303006040c081e0340000c5107a80e54040d1000d40d07030007030704081113a1796506048005100c014004020424280404070140c1c5444000c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 975156250 1250 975155000 975155023
    0x110f0d0605190c051c0e0f10110304080412030309020d030f0f020c030307020f0f10050c0d05040b0f031e0903040e010504020405060f0c01060909080316030b1e0303040305 75
    0x74080c10810740645001100007090405503003800e10908a8903401000c580030503405c204000b1100c3c1941000602030300c8141310f000820320a007207165120390008a000755040000d50f200700301502c00710320204d5443c0001c0360040c110344403e000400040f10200d103480b031400c0c800d1800040192207640015501201000c040d00024001d014031641950004030010580310380340001e200c9054000c0000703540c0c0c0310f6008002d00510302020254200c4d180c1c003907400e45002c802003a00f86001003040005046400034803410710684156021150124000c0d0210790503a114140400c3c5450b1040d0000c00c0230b60b001500000911807100d4202ca4003c8031410604c1c000c0794070001541d92189020b00401400c030301a001107200301d20400c800c04c0241e45d0502100c400c1c41301446043d4807440720364000ba005001d154020014541003103c44d03000c000b0178200840c4a4214941c1c500360844091204404840e0b0590f840c1e82c1040365440c9010300318a15940840c0300c02d00080c00c032881d040d1250384290a01c1d405180 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 975157500 1250 975156250 975156263
    0x1020a090306051008072714042105030601301a09100504091a011401081e04060f0f110a08010b0c07030b0a062616030f110f0d 56
    0x1018800c01c4110301440f42c0040d001050740c00300d0317410030802e543c035005c1520410400410800c0c0350388032000360b00041480141c2d0303130004102c200c801d0075000080301c408035406c880300310410b0202c040104007503041c19640449551014199501c1c000152402c00902c7c0e10782c030241e4110300d951b80788041021122801440b071800d000c81c1c031085a0309500701c0c5510080e800c41c880c000309002c000c51289030428003012144101e0b40410704121608101d0054241c0310b0840c2e00b0f40407400008540c0312000700c00d002850a080c3d98400c45940c0d440c24603d40c0d10f41c5c10065800740c0c41c0301400b00b404140c42c0c1d0090251702880074400244001c040b4144003c541c42d030141038003504800308801a02030340006000d0f004240c003001c8030f40f5050050940946840c4107010050040304c101c0c01055041845902c00d802400c1e200d00340084040d40c11b8000601202c0004208005200d420008003448240822a03012a50b00503200c0a101c0301030350343c2c0d4250300707030306000d00350407d104070600942603407100c40780600d507400b17001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 975158750 1250 975157500 975157517
    0x50f0d060306061202030a060207140d02061b0a050306040902040209061201080609150a0504060605060301080f061b04170309090f0a0e0a0f020913081b070f050105070f1401020a 78
    0x2510100391041c40d0300660b10f490785813180c040582c8000c10b02ca540d00b9030150340141c3e40c901c0c0e80b40c128960903150765140402e00c600038281c014640c0001c2d41038040e510400300b94644160301010700307041c1d204000e030b05000a50140040b0320b1504050b08803101503440108054141b035030307080102e684ca0304580f034045d00c1d404007400100060078013804450f030000120806003030350300100e1001d001030f030704017400300d80b0301c20b9540380054180403465002c64080d00c4010211030347c0c0e5a40705085d65a84a80c1c200e00781c039038022580800d00c03008411589011821310800464205441e00c0c9504100024498150740c250108108030380081d0381c2e2140c0c0034801c0481c20303281040c508094100c90115041c55410064540c0300d00e603100c012a80784058802a80d50488c1d40501969400c04160180c815a4a00130810440482d45003c0c000314401c81c0d08241c01c1c440e0854049665840301150b521043d88280c42c0820402c00c034060119007442c01e034a1219000391840e0f044468805003250032039000807000c100190a20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 975160000 1250 975158750 975158753
    0x40605010c08160830040506040f060612060905010f06210c05040c11070614070809031c02250509010b03250203031e0402090606031b04170d0819050601050f0d0603 72
    0xb041040010140790b4203200714500350b0380e1f25a565101400140036011000211804c0224940200340a0180c0250b400030b190b450b85402800b03443c01c0c032012101542481e0b0321072110081d031320680c0115130304410344406011283c1c031000c0c1000e030010030036103d030001084082540d031998000c0090001c041e54421205a501846150511002d504100708000613000b564803055101015100b9540d0000700b4940d88424820020385040310300d018001070001604001340680e0340103d19454045028480102882c45040101002da4410301070254400c000b10300600020340914041c40d406200341040c0e0140c80300201d4948418080325800c0801640f0002c1042011500760fa801c4100b8144254001d0050409500165400c0001050503000d03200200005644c40b844c03c2030308a1118520400b5a034540d1100003459084800e0580106c1d075104503c03625400c03d101c1c1d4116031084074007500e543d13142c0b503142c03030000c0107070001824090400c04d0030310490318203110000090000c00504040080d001c1d295 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 975161250 1250 975160000 975160057
    0xb03010908190f0c120e090f090106120506040602071412041805071d04021c0605040e030309060f15040e0c030f0705010e011b0804030f030e040605010c081608 70
    0x15210b140810400a001d40700c040c0c0c00009010340194030a01214101c00d00d0b80044803a2062000c251798000804030034048400e0383e0312001c9009201300c4000380902501d6114100f190381c0d004100408035840a00018003062150340540a554410a66003d02450b4803600c1ca1030440c2c12180c0d00d60322140098104001500c1c20344030f1815012050062015148ca0300001d03112191075400c5070344034011911030701d41d00e030b4903541103500d039030000c1c480b03000360fa07400074210b9000382000e020316405246820111062030000009803132145400c00c006041c02d0ba5800c011014400c00500903840300800e48078088050350b03c0740120000c4881c0c1800030900041383d242018500112207941c3c40050301b20407030910082c0d900c035003000791100c003e0809103c030007040501207028464985000c1c00b5030002050102c20007035506594030181d40246d617045160b40000d8200400c507612442081c0c0807440b1401420001802d0b200a0507030071040f03042c000740f240c0b180e0b19030030f00a9014240916044505c86044403840300c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 975162500 1250 975161250 975161287
    0xa031505010e070519030f020d020d0f050609040210020102040302134701020f0109050a0308150603070819050411191a0c03040b0c010f060503030909190b03010908 72
    0x1184500b6000c0c07418200400303001442003e110b0302e103000c0103482c40000305000350494103017001d000300115a980080c2031010025041749000d184620304214081d0980051401417a000340001402d920141e101c03039082004c0b0313031591186c407401d55409000c0000540d82d05c00302c0d9441c02080400c04207800c4a4511254000700d0140d070b1011400d0820ba5062100100450200100d444112000802c038517040005034a050386007c10300c5611b600308a614010000c010070a03040c001c0c400e0300e8810041d241ca50740483d00160719904250411802d00019800901c01c0c1c04c10381d0421482c0c65040280c400e4038510100b0303540102c4050728000d01c052451412810035031518141040c4201c007400209040100d060113000d00150301c1805154085484403c2c40401d00480e0300902a01d441c3c0341c0d54180c1b9998407406000c0401c002e203900b5140005c0020755060110072501a84030040400303203d55240c1c60041c500d175840d010182040c0b540e48820400c141c500741300c2c15001c81d000b88046515000e500c50b08441c1e060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 975163750 1250 975162500 975162509
    0xf0605040605120c0906010903050f0a0b10030515072c100c030801050d080f0c07081e150703110d0b0907030608060f13150b0301200f070602090a03150501 68
    0x480d03d100821062000310300d4041ea1801140d03060302d540c40d003c004136060503141e04041d0150150440c02c1c0c2c03111400040b088991b503c03407482c0116607074481d210b0606003041c0784030241c02500180c1100303c0603403060f04102d07481040c031708002d4800c0c103c821484080f0310803c144500d03142e03912240d1280078a46004854003001091800307180396406690000e15480d0706120b0341d0700828102040c1c2c0e080010303410685201010400c034254403160024a45942c1d44c006202d0104c0c0b0b4043c0c5862910843c6600c4410440340003080000d15131804c680680000305200244060205a0344804d03c82a8680190040c9034012842d8004980311a41c2c2040004e880009450300e4241458103208010314040400c10325400185600c00e04a281d40d007a001104000209600803c110310b55080281c6080240e403000c500d01300150001c02c841d80360940500c0d02d04c16407030008840e010007408850b85040d07003076000303081c05841071001505091000d00450b11200d20745d04101c415008000f01c40501039440e10039580140f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 975165000 1250 975163750 975163759
    0x3120612140f01152310051213030c140c041503030810030c06120b0306040c1403062e0321110304030309120203030c0604120320090d0f060f0605040605 67
    0x710100c4181400d1820a209885d0131075036107a500c4031000a00d814a1420780405007110b9080302105000420b1503010001c00090303101844041504864806103004010303515072910048407810346c80c2d1a10312036000d0812801e40c4201c1d5000c000d41e032120702880e15442410300c14000351909514010342074520003000c9100410880030100045901c1d88001c03404c407840760900710485ca48440000014084600e1180e03007611a030320a01003040b280b0030007902150224142450700b08104d10425403a644252083c00c0200d0340d40c0396480407003001441030304c0800000040a840155241d07100f003031a88400c5202551122450b16099281c3e802c80c80a640c49070740c800c040c3d0728150855501805010190040410481c034032149001152020000c40320080d12a0003241d0840c030b0140b1308503080d00c4416618400207812320380c0c0c1013035030072800d400101d90b000503002a50900d901d80007448404003d802c0103a40c9030b00000d1480b00452068403607154140080d039008141241880180001d42e2200e5002038000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 975166250 1250 975165000 975165011
    0x8010f05061809032206030e030c100b03070503010e03180d20010302040305032a01090b180304031502090f09060f12010e1207060f050f0403120612140f01 68
    0xc0e641e40070b650711024140504491540c0e00c0d40c00c00c261a50243d580110b529620341406032000445074000101150319540d001c0c008099034962564581c0288414000550f01c403d840303075030f0300c02a030b0401e440c0a01e0141c01c80715040d0b603640c0000c0c25240300201080ca603801c00904088403400c0781700645122503090795108900d000300c0d940c01c2c108901076a10710380d11a600704030364021a840f9030100c034021500602103c3c2c40701102541e41114020103058490004001c2000c20703d003e906015030714200c0d4000031000e5550350788070402c0101503078100401c1c400d0302081201200240c2000c0e40b40b40d0855128a0045e141c0009000b172100305541080e440b8480c5050030700300641d03030340c500d10000100d82c4183c50340003803003608600c0300c0d015014800c000c020034081c82100039000c01d5803c014146c5140a448180107080c07802d00c801045175800c5e2440ba04000e011030000d004a4055070441405803444440082d006940b22040700304000b070741e10120340030b04000440d1408568100510010b502c00701c4002c110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 975167500 1250 975166250 975166261
    0x8090906090603120d061706070216080a06240e010e0907141905030102041d0a0501050303070b04151104170d3207030509120604031202181908010f05 66
    0x7903404c00c4910742c040c184000101031075003045540043c0010040d100030150403510410101e0703151601104c001c0300611411045520b208011f54524048408010241105400544545020300400c80e40c420080316104000f901a10b106810080205894a402c020f9941000505028040c014060700742662000f1000d111a40308148020744800046508582d103000d000c000720b149019a9002c0c81e819407001c0bc002605100014821601c4c14904060340102d540d68501542120300170300038030b501541700340800d1001981030340300300ea04a4098901d50064182c881d9803c000d44034001400381c81c41202280c10020502400c194410181c0c4650250210a0800c500200710108905074031040c40d042106a14001401d5110454912410b12040f9a1210701d810003804641c0030110140c02020343c03500c8940407183c0481c001c0e00440e4190b4a440c6030042200e0300001a401201006450005a00e65102a95194030030a1441d8808204d0120310034a01402b49084490000d040150a800c0400300701 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 975168750 1250 975167500 975167503
    0x130507140303030a18020910210f110105070f03030219020102090117060103110d050411030f06010b07061e14090c1f1b0c050a091406220908090906090603 68
    0x4e60250100307200040124400320000c43ca48125100030b50400c1408081c818401240381c945e006075142c00da00d107069494a851281d003e40761042d406459102c11400c03070702c00580d408503043c01c00d400500d41181000c95035101e80940040d00442100401e60006a1134002e01003d8514428111180002c5007065030800019160070f038000100e2160707912030400500903a001ea40601c65240000040d252241c3d41c62621800600c0b06031000d43e40d40c0c00008000005180024030500c0141070180a0700080e441c05031800380640101c0e808403002c64651100002c4161485081d1904c541e0f440b40110710141030100034000003c02600d154410341181c42281505d403609608201010014006858184104002107601c01541d07140340c8802038013038a050050010303411004041c0e520803113046480d11f0b07580010100702c42c0180980400c40d0000b80014000389003010010451411303101c40245840c003402c01d0350049569404003140c8600010810029a0410f1701c00903501000640b022466802c0444c0043d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 975170000 1250 975168750 975168757
    0x9130209060315043c02040b0412030c0b0f1f080c0607020f030a08070c23010c03030e2415030a140c0603071d0409020f01030f14130507140303 63
    0x22190200c40b031000f0071068480c1d82c00080c5200820b1000e240035080c0d443d00b00c08410b0340d81c5455400b504442001c60050500c0c4c0b00300c60841e052460070a140502d030640403440302c442900c068041c40041e00032000860300c04190355129071000201084a45001070680c680c3d25401c452820220003000402c0c8045d81d400200c002034854200c41179503c3c3e40a600c0003032014214010103a0301405100300342c40c04c005c0014080c11010b40b29611036038900782c54009020500ca04a15040c4004001c0d0002e110700c0d5000e1001d045a030b9010b8500400e06840c909102031404800c841114000010400f186041160100c00c2035048104000500301e03400c4a0f900107542c98003694070142c03d03000841c0d0070485d1031504124080c0c40704400751465489141c0841d024140140c142203005001d043d00c9110845450a4400c1c218100c0d401082c04035035045080046000303103041000e10105940e0350794500c41440300f1080c82441243e040e14070602142c449d18015091408a03031101100412a0005c1800c60364084140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 975171250 1250 975170000 975170011
    0x503010504110403020409061407081303270b03090106090b09071b0f080703110d1215080604060b1f05030f040602040b070605090708070e012303070b091302090603 72
    0x100d442c08609400075524400d6501c0254482d00d80308140c800c1100036000000e41084003204a40c0703d0703a4180050b556200100d0321040780b000e0042103031000a0007042c5102108040412849010211080c0341c081c1291540004c0c00c1c4680100820003d14802d0040f030f400703003452800c01c0c4985408030010511852000d041c9009001c60380c0c08524070701c1d48540040b0202038010041168900d603034100560580d0000d20309900040741811041070041c0002680041401c00ea50342d44c43d150b000d91a0400200b240100701007081001d00c200003a8030104100740d50144c0d00840d400031380d421500042181c07070030300b00502100c600c4d01c4c1820b50309125000f0043e243e00a0400c609010140d030b40389003000c0280304542140c11030a0010031000c00744080c5502040c0720302c40c906c045920300e507295005185d84044910880c205003e00400601000d5210071140000000d0b4180e9020030954040006e420194030303400800850134003141c4400c003450700c541002c20301c69090200310310b4081040003054841c0300c000c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 975172500 1250 975171250 975171259
    0x1020408070e0903120c04091406060a0e0102030c0a1a07030c1b0602093327030c0603012c1021080c0307052a0910120804090f0c05030105 61
    0xc03c03202c0c1c18022140d00c0304012607441d06500c4e0100b40b440380b0f40c00c41c3c003071031280358600b441984041c00c1360780200d0300600c00104024201580d40320200c82000800351924114002800f042420040070451044011700c611002d840302c400c1242d5640005000031310b603108040c101b540001050303810560310400c0005090043c1082140d50034140041e2203101c41d46600282400b841050402e5842403210211a0180e821040d44601914150b09800380440c1702d40e0010f5a10780b118a180c0491003049002c400c05825101c0c0307034000703400042640e0000d91080c00e0f01d610f1401444140a200954401d24000001c40c1c0c6450741018841d441203960b980c080d0005180c05000003460400750440c08804244d80059503a981d920711840c4992260800381049075148120a03075800f1072660340c164010824655860f01c0329011002c02041b81200c0050011482440c000502141000c800840802514040c06007569503d03e0300c50f07004c048610001c086088186401c21038404141c2c00021079044441c201c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 975173750 1250 975172500 975172529
    0x206030a140703092307140d0213090c08010c0509040c050d060b0915040506030606030709030b1608010e1306020c07090e0d0f110c040c030f29030102040807 69
    0x182500028049200c0c0701c01d034005120700b0408259415084180710340d12600d100801e40d14203503145000044511070070a96600500d04c00c1c005886104130038110f00d40c00400b603254000300e50700440e00d12552011009a12502c45030040d05006074803d04030010b040b41d074003c0000325094a402001070041a40c00c0e4829500c450902e882c4074071503010303500c1d0441c1c0001c003000681e171348040303203002036001c1c40d440c034020051032030750342ea08140000c1580c044400140c50b00e861a42e43c507040000ea94001131800702403080414003c804144245011441814805682604400703000740141c40324005910003020a0303004000c00807810f14101e80c0d0036410750311200c0980c0300c012a4044508102268100b41022850520150140e010001e0401c84070151030315800f00e0089480710072035501110b03111840b100c1c2d001c04101101ca040a600c00e144280440c500010800c02c069016070959401d14110140300301d02042d90415004082108120400308070300851401c1d10304041103032141d00d5172040140140148 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 975175000 1250 975173750 975173761
    0x10050409020409021f02010507030c091e030b04081c0c2c150d0c031107110604120602270a090e0f03070b090d0c2406180e010f0216020603 61
    0x382c104040b1241d0041056003a0503a035a84172070542c40c2d081d0104d00543c200b402183e0524000c0c8a0140c801c01b09030313a6400594103043c0100041a50107004c0342070001c0302c4400001140c40c10f111580114030401038607969403e41005000d044141480f041500b07482c00401410305a000002c504440001101c4602107002440212242403c0d03460300da504280d0395982d014429242000602d0800300020303080003c6281039004400302c824015004180328800c011000104950303041c4c118000400500c0d003440c003601c505d03a0652a00e41104201e41b165004200520614540718004481c240700303005401140f40e07403070300160307500e4214490907a00b19624480c003d03019205000344011030400900312552070025190201d0801011a00d00e0380c140105884210003c0c0708181d40c1d0326564101c0c2c00c0085024520460304034070940082c0380740d11950384840000e442d0415050286030307420440000102c00120801c03050030f442c844424803800714410028516200030303500803070b6801da805543e05030312a81c55 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 975176250 1250 975175000 975175009
    0x42606011d090f0616080907030c030f060b03070b040611150a0c021930080f060d020310061401080103050319140301080d0f05120f0c070206071505010803031005040902 74
    0x10310346001c0680100702c02c111001031740d2800364100c1d0580380c6d1264075541d07078860480c0e111451404018128080140304202140300f011343d11b4003042c018400080c1001d54040003a19020080e80522860f0300042810410316800c90090740600d04050003410b9104c686581c5a44202002880000600e5a59120304c002a20800c400380c0f00200c000200008a8140d0904120003c1050f0003400b04e04000e03200a6451889910000e0001d00075444070100341e00d5501010103440001405036070041101075194025980410007400c0d80a1007100c0011404e042c100314451000304200302a0604c8980801000000c2c00001112112410560b0b0401c0080081604854100480c0102c0c45180408400442ca40f10040741044021200d5187c002600751804d038180e90a0092103400307516036038400001110403141c8458946c3c40218000040e191045950000d0314035080b556080c1da902000355200c0150900c1e40c458980509901e000550a40c6000d00280a000c4207030b001e89801a034461041a046448 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 975177500 1250 975176250 975176263
    0x6262a0d0510080607091d06011106070f031104061e03060b1201050a090504080910180f081902030a11040b04020c010515190b07020303040308042606011d09 69
    0x18040010322030340c100b128103000120030030301401045000f04004110954045c41e02202152001c5909030040b000c0c41b5040e0b070070028020002410f01ca8052500034010030140a018811100b42c1c440982c900e182003c01400c0b0350620301d4000307816004110611902f40c12880c60000703010b81041d400b0030084141c8045002d0700b225030200260031008618140e40003c0022464180c40c1c05482c0610301c26601c811000645000b034401030410041000042d800b17003485c0c20f001d00411024140f80d43c0c0081101680001c00380c0d02d80c4000a4182c511038140311561080c0242c80d1a40d03c94000d811500c04150002034880c0c030501d200505840b60355906415030384840c0c121005120000b00115100d00c031555403680078040c11201c241c2e00c65854080820030f882d0181c80b051000b8454900e42030080e044c918452229404a4820f0b82d040c44280700000005080c0340c0100058004481e4841e03141c0001d0100440c00510003500c00802c3d006030006002c43c1400150079001001e29028600d403503118800102d0400a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 975178750 1250 975177500 975177517
    0x70e0415060b04080111070c030807060e120a020c0d03390c09051f06031e230c0c03090907050c0d0f09080606060702010f0908010606262a 61
    0x107040000000d99018004060012600280b00a1021001a00000507180701d003c400400c01c0c00c22000c1440400e00c0d040c0580361042c442e080005180034866426481c0c0341ca00c840d015102000065028041c0780c4c140060000070000366490302d10440c180e035001d0001d024045040842402c2417103068001f070006051030000c070041d40c030404040c070050305100c80110f4641c090705428070704007004102d005e0030384034684000300000c1c1080c02440d07042c034070110081c24103644c0c1507001900200d51500c0548051180003145110000c1c01d41900c1d0400e426aa0800030080c11020304000501c44019040f2000c0200c0341654001ca81d41c0000d0b50b940c09043c0c655001da0f0000c10000e10a128041e14130b03a0b000401d00820031190340350540130a54a01105a40c2c00c02160000d800180c02d02c1490300650142c050800041c1c02800e0043d803450300d402c405070071140140d000c800083c80588520000154030310001c0c1c0030400680c003d04c0b9915021407440300511000031908000d20391203910300050405d21041d0392031078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 975179856 1106 975178750 975178793
    0x5180a03030f02070b0c031017030a0f121a01030f0c0504090902060f0310091a03060f06010203040b1206040b030d1202091302030a0504120908070e04 66
    0x4080008442c000d164082c0501d0300002c00c0d940c5141d02c01c0e43d42c10101900c030701e4000c181400100d41a44a80d000984600c3c8486c0340703a10120840326411745d80d007000e00c44620808400c03904600c0c01c00c03010072228a05000c540d15240d0070f2a0400e40550242d034148208458010307000100d82408501c10003080c0300308400c20450390250007600750103000038005401c01034403200c403141e10b510844100507000207051092040e00c00910440803180c0181e40c802c00d20302e0039440840e60b251800341000ca4048a01c10011322144c1c4204122000343c001c40c10515103a1000c141000e040c2c06060300d0307991107241020144031950900044100b40820707076581e021805124007200702c1c000c0d80007400e01c40e0011b0100641c8034200b141030000354003810310600006050b141600f00500744080380c04203a802c2210207141042a110009000710681e40040c0c040c14036900c603881c00d00307402d0140342102881c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 975000000 975179856 := by
  have h0 := BRFrame.cov_init 975000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 975000000 ≤ n) (h2 : n < 975179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
